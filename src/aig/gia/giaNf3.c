/**CFile****************************************************************

  FileName    [giaNf3.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Standard-cell mapping with area recovery.]

  Synopsis    [Area-oriented mapping using construction-proved choices.]

  Description [Reuses compact library matching while spending additional
  effort on structural alternatives and area recovery under a delay bound.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaNf3.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "giaEdit.h"
#include "base/main/main.h"
#include "map/mio/mio.h"
#include "map/mio/exp.h"
#include "map/scl/sclCon.h"
#include "misc/vec/vecMem.h"
#include "misc/util/utilTruth.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

enum { NF3_WINDOW_MAX = 8, NF3_LEAF_MAX = 6, NF3_CI = -1, NF3_ALIAS = -2 };
typedef struct Nf3_Obj_t_
{
    int Gate, nFans, Fans[6], Refs, Arrival, Required, Compl;
} Nf3_Obj_t;
typedef struct Nf3_Recipe_t_
{
    int Gate[2];
    unsigned char Pins[2][6];
    unsigned Mask;
    int Profile[12];
    word Area;
} Nf3_Recipe_t;
typedef struct Nf3_Cache_t_
{
    word Truth;
    Nf3_Recipe_t * Recipes;
    int nVars, nRecipes;
} Nf3_Cache_t;
enum { NF3_RECIPE_MAX = 32, NF3_CACHE_BINS = 8192, NF3_CACHE_LIMIT = 4096 };


typedef struct Nf3_Man_t_
{
    Gia_Man_t * Gia;
    Mio_Cell2_t * Cells;
    Vec_Mem_t * Truths;
    Vec_Wec_t * Matches;
    Nf3_Obj_t * Objs;
    Vec_Int_t * Inputs, * Outputs, * Stack;
    int nObjs, nCells, Target, fDecompose;
    word nTrials, nHits, Saved, nCacheHits, nTwo, nOdc, nCanonical, MinArea;
    Nf3_Cache_t * Cache;
    int nCached;
} Nf3_Man_t;
typedef struct Nf3_Plan_t_
{
    int Gate, nFans, Fans[6], Arrival;
    int Slot, ChildGate, ChildFans[6], ChildArrival;
    word Gain;
} Nf3_Plan_t;

/**Function*************************************************************

  Synopsis    [Finds a node in a bounded window.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Nf3_Find( int * Data, int Count, int Id )
{
    int i;
    for ( i = 0; i < Count; i++ ) if ( Data[i] == Id ) return i;
    return -1;
}
/**Function*************************************************************

  Synopsis    [Reads the physical cell area.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Nf3_Area( Nf3_Man_t * p, int Id )
{
    return p->Objs[Id].Gate < 0 ? 0 : p->Cells[p->Objs[Id].Gate].AreaW;
}
/**Function*************************************************************

  Synopsis    [Computes arrival from physical pin delays.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Nf3_Delay( Nf3_Man_t * p, int Gate, int * Fans, int nFans )
{
    int i, Delay = 0;
    for ( i = 0; i < nFans; i++ )
        Delay = Abc_MaxInt(Delay, p->Objs[Fans[i]].Arrival + (Gate < 0 ? 0 : p->Cells[Gate].iDelays[i]));
    return Delay;
}
/**Function*************************************************************

  Synopsis    [Evaluates a physical cell over six Boolean variables.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Nf3_Eval( Nf3_Man_t * p, int Gate, word * Inputs )
{
    Vec_Int_t * Expr;
    word Values[128];
    int i, nFans;
    if ( Gate == NF3_ALIAS ) return Inputs[0];
    Expr = p->Cells[Gate].vExpr;
    nFans = p->Cells[Gate].nFanins;
    assert(Exp_NodeNum(Expr) <= 128);
    for ( i = 0; i < Exp_NodeNum(Expr); i++ )
        Values[i] = Exp_Truth6Lit(nFans, Vec_IntEntry(Expr, 2*i), Inputs, Values) &
                    Exp_Truth6Lit(nFans, Vec_IntEntry(Expr, 2*i+1), Inputs, Values);
    return Exp_Truth6Lit(nFans, Vec_IntEntryLast(Expr), Inputs, Values);
}
/**Function*************************************************************

  Synopsis    [Imports one physical phase of a mapped GIA object.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Nf3_ImportCell( Nf3_Man_t * p, int * Map, int Lit )
{
    Nf3_Obj_t * Obj = p->Objs + p->nObjs;
    int i, Fan;
    assert(Map[Lit] < 0);
    if ( Gia_ObjIsCellInv(p->Gia, Lit) )
    {
        Obj->Gate = 3; Obj->nFans = 1;
        Obj->Fans[0] = Map[Lit ^ 1];
        assert(Obj->Fans[0] >= 0);
    }
    else
    {
        Obj->Gate = Gia_ObjCellId(p->Gia, Lit);
        Obj->nFans = Gia_ObjCellSize(p->Gia, Lit);
        assert(Obj->nFans == (int)p->Cells[Obj->Gate].nFanins);
        Gia_CellForEachFanin(p->Gia, Lit, Fan, i)
        {
            Obj->Fans[i] = Map[Fan];
            assert(Obj->Fans[i] >= 0);
        }
    }
    Obj->Compl = -1;
    // A spare earlier id allows a cheaper two-cell implementation even when
    // only this cell is removed. All original fanins precede the spare id.
    if ( p->fDecompose && p->Cells[Obj->Gate].AreaW > 2*p->MinArea )
    {
        p->Objs[p->nObjs+1] = *Obj;
        memset(Obj, 0, sizeof(*Obj)); Obj->Gate = NF3_ALIAS; Obj->Compl = -1;
        p->nObjs++;
    }
    return Map[Lit] = p->nObjs++;
}
/**Function*************************************************************

  Synopsis    [Builds a compact topological physical-cell network.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Nf3_Man_t * Nf3_Import( Gia_Man_t * Gia, Jf_Par_t * Pars, int fDecompose )
{
    Nf3_Man_t * p = ABC_CALLOC(Nf3_Man_t, 1);
    Gia_Obj_t * Obj;
    Nf3_Obj_t * Node;
    int * Map, i, k, Id, Lit, Count = Gia_ManCiNum(Gia) + 2;
    p->Gia = Gia; p->fDecompose = fDecompose;
    Mio_LibraryMatchesFetch((Mio_Library_t *)Abc_FrameReadLibGen(), &p->Truths,
        &p->Matches, &p->Cells, &p->nCells, Pars->fPinFilter, Pars->fPinPerm, Pars->fPinQuick);
    p->MinArea = ~(word)0;
    for ( i = 0; i < p->nCells; i++ )
    {
        if ( p->Cells[i].nFanins > 6 || Exp_NodeNum(p->Cells[i].vExpr) > 128 ) { ABC_FREE(p); return NULL; }
        if ( p->Cells[i].nFanins && p->MinArea > p->Cells[i].AreaW ) p->MinArea = p->Cells[i].AreaW;
    }
    Gia_ManForEachCell(Gia, Lit)
        Count += 1 + (fDecompose && p->Cells[Gia_ObjIsCellInv(Gia, Lit) ? 3 : Gia_ObjCellId(Gia, Lit)].AreaW > 2*p->MinArea);
    p->Objs = ABC_CALLOC(Nf3_Obj_t, Count);
    p->Inputs = Vec_IntAlloc(Gia_ManCiNum(Gia));
    p->Outputs = Vec_IntAlloc(Gia_ManCoNum(Gia));
    p->Stack = Vec_IntAlloc(128);
    p->Cache = ABC_CALLOC(Nf3_Cache_t, NF3_CACHE_BINS);
    Map = ABC_FALLOC(int, 2*Gia_ManObjNum(Gia));
    Map[0] = 0; Map[1] = 1;
    p->Objs[0].Gate = 0; p->Objs[1].Gate = 1;
    p->Objs[0].Compl = 1; p->Objs[1].Compl = 0;
    p->nObjs = 2;
    Gia_ManForEachCi(Gia, Obj, i)
    {
        Id = p->nObjs++; Node = p->Objs + Id;
        Node->Gate = NF3_CI; Node->Compl = -1;
        Map[2*Gia_ObjId(Gia, Obj)] = Id;
        Vec_IntPush(p->Inputs, Id);
    }
    Gia_ManForEachObj1(Gia, Obj, Id)
    {
        Lit = 2*Id;
        if ( Gia_ObjIsCo(Obj) ) continue;
        if ( Gia_ObjIsAnd(Obj) && Gia_ObjIsCellInv(Gia, Lit) )
        {
            Nf3_ImportCell(p, Map, Lit+1);
            Nf3_ImportCell(p, Map, Lit);
        }
        else
        {
            if ( Gia_ObjIsAnd(Obj) && Gia_ObjIsCell(Gia, Lit) ) Nf3_ImportCell(p, Map, Lit);
            if ( Gia_ObjIsCell(Gia, Lit+1) ) Nf3_ImportCell(p, Map, Lit+1);
        }
        if ( Map[Lit] >= 0 && Map[Lit+1] >= 0 )
        {
            p->Objs[Map[Lit]].Compl = Map[Lit+1];
            p->Objs[Map[Lit+1]].Compl = Map[Lit];
        }
    }
    Gia_ManForEachCo(Gia, Obj, i)
    {
        Id = Map[Gia_ObjFaninLit0p(Gia, Obj)];
        assert(Id >= 0);
        Vec_IntPush(p->Outputs, Id); p->Objs[Id].Refs++;
    }
    for ( i = p->nObjs-1; i >= 2; i-- )
        if ( p->Objs[i].Refs )
            for ( k = 0; k < p->Objs[i].nFans; k++ ) p->Objs[p->Objs[i].Fans[k]].Refs++;
    for ( i = 2; i < p->nObjs; i++ )
        if ( p->Objs[i].Refs && p->Objs[i].Gate != NF3_CI )
            p->Objs[i].Arrival = Nf3_Delay(p, p->Objs[i].Gate, p->Objs[i].Fans, p->Objs[i].nFans);
    Vec_IntForEachEntry(p->Outputs, Id, i) p->Target = Abc_MaxInt(p->Target, p->Objs[Id].Arrival);
    if ( Pars->fAreaOnly ) p->Target = SCL_INFINITY-1;
    else p->Target = Abc_MaxInt(p->Target, (int)Pars->MapDelayTarget);
    ABC_FREE(Map);
    return p;
}
/**Function*************************************************************

  Synopsis    [Propagates the fixed output delay bound.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf3_Required( Nf3_Man_t * p )
{
    Nf3_Obj_t * Obj;
    int i, k, Id, Req;
    for ( i = 0; i < p->nObjs; i++ ) p->Objs[i].Required = SCL_INFINITY;
    Vec_IntForEachEntry(p->Outputs, Id, i) p->Objs[Id].Required = p->Target;
    for ( i = p->nObjs-1; i >= 2; i-- )
    {
        Obj = p->Objs+i;
        if ( !Obj->Refs ) continue;
        for ( k = 0; k < Obj->nFans; k++ )
        {
            Req = Obj->Required - (Obj->Gate < 0 ? 0 : p->Cells[Obj->Gate].iDelays[k]);
            p->Objs[Obj->Fans[k]].Required = Abc_MinInt(p->Objs[Obj->Fans[k]].Required, Req);
        }
    }
}
/**Function*************************************************************

  Synopsis    [Evaluates a window with independent boundary signals.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Nf3_WindowTruth_rec( Nf3_Man_t * p, int Id, int * Nodes, int nNodes,
                               int * Leaves, int nLeaves, word * Values, unsigned * Seen )
{
    static const word Vars[6] = {
        ABC_CONST(0xAAAAAAAAAAAAAAAA), ABC_CONST(0xCCCCCCCCCCCCCCCC),
        ABC_CONST(0xF0F0F0F0F0F0F0F0), ABC_CONST(0xFF00FF00FF00FF00),
        ABC_CONST(0xFFFF0000FFFF0000), ABC_CONST(0xFFFFFFFF00000000) };
    Nf3_Obj_t * Obj = p->Objs+Id;
    word Inputs[6];
    int Pos, i;
    if ( Id < 2 ) return Id ? ~(word)0 : 0;
    Pos = Nf3_Find(Leaves, nLeaves, Id);
    if ( Pos >= 0 ) return Vars[Pos];
    Pos = Nf3_Find(Nodes, nNodes, Id);
    assert(Pos >= 0);
    if ( (*Seen >> Pos) & 1 ) return Values[Pos];
    for ( i = 0; i < Obj->nFans; i++ )
        Inputs[i] = Nf3_WindowTruth_rec(p, Obj->Fans[i], Nodes, nNodes, Leaves, nLeaves, Values, Seen);
    *Seen |= 1u << Pos;
    return Values[Pos] = Nf3_Eval(p, Obj->Gate, Inputs);
}
/**Function*************************************************************

  Synopsis    [Counts the complete released cone while protecting replacement pins.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Nf3_TrialArea( Nf3_Man_t * p, int Root, int * Fans, int nFans, int * Slot )
{
    word Saved = Nf3_Area(p, Root);
    int i, k, Id;
    if ( Slot ) *Slot = 0;
    // Protect the replacement pins and retain every decremented edge for undo.
    for ( i = 0; i < nFans; i++ ) p->Objs[Fans[i]].Refs++;
    Vec_IntClear(p->Stack);
    for ( i = 0; i < p->Objs[Root].nFans; i++ ) Vec_IntPush(p->Stack, p->Objs[Root].Fans[i]);
    for ( i = 0; i < Vec_IntSize(p->Stack); i++ )
    {
        Id = Vec_IntEntry(p->Stack, i);
        assert(p->Objs[Id].Refs > 0);
        if ( --p->Objs[Id].Refs ) continue;
        if ( Id >= 2 ) Saved += Nf3_Area(p, Id);
        if ( Slot && p->Objs[Id].Gate != NF3_CI && Id > *Slot ) *Slot = Id;
        for ( k = 0; k < p->Objs[Id].nFans; k++ ) Vec_IntPush(p->Stack, p->Objs[Id].Fans[k]);
    }
    Vec_IntForEachEntry(p->Stack, Id, i) p->Objs[Id].Refs++;
    for ( i = 0; i < nFans; i++ ) p->Objs[Fans[i]].Refs--;
    Vec_IntClear(p->Stack);
    return Saved;
}

/**Function*************************************************************

  Synopsis    [Subtracts the replacement area from the exact released area.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Nf3_WindowGain( Nf3_Man_t * p, int Root, int Gate, int * Fans, int nFans )
{
    word Saved = Nf3_TrialArea(p, Root, Fans, nFans, NULL);
    word Added = Gate < 0 ? 0 : p->Cells[Gate].AreaW;
    return Saved > Added ? Saved - Added : 0;
}
/**Function*************************************************************

  Synopsis    [Releases bounded two-cell decomposition recipes.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf3_CacheClear( Nf3_Man_t * p )
{
    int i;
    for ( i = 0; i < NF3_CACHE_BINS; i++ ) ABC_FREE(p->Cache[i].Recipes);
    memset(p->Cache, 0, sizeof(Nf3_Cache_t)*NF3_CACHE_BINS);
    p->nCached = 0;
}
/**Function*************************************************************

  Synopsis    [Compares area and phase-specific pin delay profiles.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Nf3_Dominates( Nf3_Recipe_t * A, Nf3_Recipe_t * B )
{
    int i;
    if ( A->Area > B->Area || A->Mask != B->Mask ) return 0;
    for ( i = 0; i < 12; i++ ) if ( A->Profile[i] > B->Profile[i] ) return 0;
    return 1;
}
/**Function*************************************************************

  Synopsis    [Retains a small nondominated set of physical implementations.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf3_RecipeAdd( Nf3_Man_t * p, Nf3_Recipe_t * Recipes, int * pnRecipes, Nf3_Recipe_t * R )
{
    int i, k, Pin, d, Worst;
    R->Area = p->Cells[R->Gate[0]].AreaW + p->Cells[R->Gate[1]].AreaW;
    R->Mask = 0; memset(R->Profile, 0, sizeof(R->Profile));
    for ( i = 0; i < (int)p->Cells[R->Gate[1]].nFanins; i++ )
    {
        Pin = R->Pins[1][i]; d = p->Cells[R->Gate[1]].iDelays[i];
        if ( Pin < 12 )
        { R->Mask |= 1u << Pin; R->Profile[Pin] = Abc_MaxInt(R->Profile[Pin], d); }
        else for ( k = 0; k < (int)p->Cells[R->Gate[0]].nFanins; k++ )
        {
            Pin = R->Pins[0][k]; R->Mask |= 1u << Pin;
            R->Profile[Pin] = Abc_MaxInt(R->Profile[Pin], d + p->Cells[R->Gate[0]].iDelays[k]);
        }
    }
    for ( i = 0; i < *pnRecipes; i++ ) if ( Nf3_Dominates(Recipes+i, R) ) return;
    for ( i = 0; i < *pnRecipes; )
        if ( Nf3_Dominates(R, Recipes+i) ) Recipes[i] = Recipes[--*pnRecipes]; else i++;
    if ( *pnRecipes < NF3_RECIPE_MAX ) { Recipes[(*pnRecipes)++] = *R; return; }
    Worst = 0;
    for ( i = 1; i < *pnRecipes; i++ ) if ( Recipes[i].Area > Recipes[Worst].Area ) Worst = i;
    if ( R->Area < Recipes[Worst].Area ) Recipes[Worst] = *R;
}
/**Function*************************************************************

  Synopsis    [Decomposes a six-input function and matches both cell functions.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Nf3_Cache_t * Nf3_Recipes( Nf3_Man_t * p, word Truth, int nVars )
{
    static const word Vars[6] = { ABC_CONST(0xAAAAAAAAAAAAAAAA), ABC_CONST(0xCCCCCCCCCCCCCCCC),
        ABC_CONST(0xF0F0F0F0F0F0F0F0), ABC_CONST(0xFF00FF00FF00FF00),
        ABC_CONST(0xFFFF0000FFFF0000), ABC_CONST(0xFFFFFFFF00000000) };
    Nf3_Cache_t * Entry;
    Nf3_Recipe_t Recipes[NF3_RECIPE_MAX], R;
    Vec_Int_t * GMatches, * HMatches;
    word Hash, Rows[64], First, Second, G, H, Key, Check, Inputs[6];
    unsigned CfgG, CfgH, Phase, Perm;
    int Bin, Mask, Bound[6], Free[6], nBound, nFree, b, f, m, i, j, k, nRecipes = 0;
    int GId, HId, GCfg, HCfg, GGate, HGate, HIndex, Valid;
    Hash = Truth ^ (Truth >> 31); Hash *= ABC_CONST(0xbf58476d1ce4e5b9); Hash ^= Hash >> 29;
    Bin = (int)(Hash & (NF3_CACHE_BINS-1));
    while ( p->Cache[Bin].nVars )
    {
        Entry = p->Cache+Bin;
        if ( Entry->Truth == Truth && Entry->nVars == nVars ) { p->nCacheHits++; return Entry; }
        Bin = (Bin+1) & (NF3_CACHE_BINS-1);
    }
    if ( p->nCached == NF3_CACHE_LIMIT ) { Nf3_CacheClear(p); Bin = (int)(Hash & (NF3_CACHE_BINS-1)); }
    Entry = p->Cache+Bin; Entry->Truth = Truth; Entry->nVars = nVars; p->nCached++;
    // Singleton and full bound sets can supply a missing input/output
    // inverter; direct matching requires those phases to exist already.
    for ( Mask = 1; Mask < (1 << nVars); Mask++ )
    {
        nBound = nFree = 0;
        for ( k = 0; k < nVars; k++ )
            if ( (Mask >> k) & 1 ) Bound[nBound++] = k; else Free[nFree++] = k;
        memset(Rows, 0, sizeof(word)*(1 << nBound));
        for ( m = 0; m < (1 << nVars); m++ )
        {
            if ( !((Truth >> m) & 1) ) continue;
            for ( b = 0, k = 0; k < nBound; k++ ) b |= ((m >> Bound[k]) & 1) << k;
            for ( f = 0, k = 0; k < nFree; k++ ) f |= ((m >> Free[k]) & 1) << k;
            Rows[b] |= (word)1 << f;
        }
        First = Rows[0]; Second = First;
        for ( b = 1; b < (1 << nBound); b++ ) if ( Rows[b] != First ) { Second = Rows[b]; break; }
        if ( Second == First ) continue;
        for ( ; b < (1 << nBound); b++ ) if ( Rows[b] != First && Rows[b] != Second ) break;
        if ( b < (1 << nBound) ) continue;
        G = H = 0;
        for ( m = 0; m < 64; m++ )
        {
            if ( Rows[m & ((1 << nBound)-1)] == Second ) G |= (word)1 << m;
            if ( (((m >> nFree) & 1) ? Second : First) & ((word)1 << (m & ((1 << nFree)-1))) ) H |= (word)1 << m;
        }
        // The zero bound assignment belongs to First, so G is normalized.
        assert(!(G & 1));
        GId = *Vec_MemHashLookup(p->Truths, &G);
        Key = H & 1 ? ~H : H; HId = *Vec_MemHashLookup(p->Truths, &Key);
        if ( GId < 0 || HId < 0 || GId >= Vec_WecSize(p->Matches) || HId >= Vec_WecSize(p->Matches) ) continue;
        GMatches = Vec_WecEntry(p->Matches, GId); HMatches = Vec_WecEntry(p->Matches, HId);
        Vec_IntForEachEntryDouble(GMatches, GGate, GCfg, i)
        {
            if ( (int)p->Cells[GGate].nFanins != nBound ) continue;
            CfgG = (unsigned)GCfg;
            memset(&R, 0, sizeof(R)); R.Gate[0] = GGate;
            Phase = (CfgG >> 1) & 127; Perm = CfgG >> 8;
            for ( k = 0; k < nBound; k++, Phase >>= 1, Perm >>= 4 )
                R.Pins[0][k] = (unsigned char)(2*Bound[Perm & 15] + (Phase & 1));
            Vec_IntForEachEntryDouble(HMatches, HGate, HCfg, j)
            {
                CfgH = (unsigned)HCfg;
                if ( (CfgH & 1) != (unsigned)(H & 1) || (int)p->Cells[HGate].nFanins != nFree+1 ) continue;
                Phase = (CfgH >> 1) & 127; Perm = CfgH >> 8;
                R.Gate[1] = HGate; Valid = 1;
                for ( k = 0; k <= nFree; k++, Phase >>= 1, Perm >>= 4 )
                {
                    HIndex = Perm & 15;
                    if ( HIndex == nFree )
                    {
                        if ( (Phase & 1) != (CfgG & 1) ) { Valid = 0; break; }
                        R.Pins[1][k] = 12;
                    }
                    else R.Pins[1][k] = (unsigned char)(2*Free[HIndex] + (Phase & 1));
                }
                if ( !Valid ) continue;
                // Prove the recipe once, independently of its decomposition.
                for ( k = 0; k < nBound; k++ ) Inputs[k] = (R.Pins[0][k] & 1) ? ~Vars[R.Pins[0][k] >> 1] : Vars[R.Pins[0][k] >> 1];
                Check = Nf3_Eval(p, GGate, Inputs);
                for ( k = 0; k <= nFree; k++ )
                    Inputs[k] = R.Pins[1][k] == 12 ? Check : (R.Pins[1][k] & 1) ? ~Vars[R.Pins[1][k] >> 1] : Vars[R.Pins[1][k] >> 1];
                assert(Nf3_Eval(p, HGate, Inputs) == Truth);
                Nf3_RecipeAdd(p, Recipes, &nRecipes, &R);
            }
        }
    }
    Entry->nRecipes = nRecipes;
    Entry->Recipes = ABC_ALLOC(Nf3_Recipe_t, nRecipes);
    if ( nRecipes ) memcpy(Entry->Recipes, Recipes, sizeof(Nf3_Recipe_t)*nRecipes);
    return Entry;
}
/**Function*************************************************************

  Synopsis    [Tries two-cell implementations in released or reserved earlier slots.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf3_TryTwo( Nf3_Man_t * p, int Root, int * Nodes, int nNodes,
                       int * Leaves, int nLeaves, word Truth, Nf3_Plan_t * Best )
{
    Nf3_Cache_t * Entry;
    Nf3_Recipe_t * R;
    int i, j, k, Fans[2][6], All[12], nAll, Phase, Pin, Id, Slot, MaxFan, Delay, ChildDelay;
    word Saved, Gain;
    if ( nLeaves < 2 ) return;
    Saved = Nf3_TrialArea(p, Root, NULL, 0, NULL);
    if ( Saved <= Best->Gain + 2*p->MinArea ) return;
    Entry = Nf3_Recipes(p, Truth, nLeaves);
    for ( i = 0; i < Entry->nRecipes; i++ )
    {
        R = Entry->Recipes+i;
        MaxFan = nAll = 0;
        for ( j = 0; j < 2; j++ )
        {
            for ( k = 0; k < (int)p->Cells[R->Gate[j]].nFanins; k++ )
            {
                Pin = R->Pins[j][k];
                if ( Pin == 12 ) { Fans[j][k] = -1; continue; }
                Phase = Pin & 1; Id = Leaves[Pin >> 1];
                if ( Phase ) Id = p->Objs[Id].Compl;
                if ( Id < 0 || Id >= Root || !p->Objs[Id].Refs || Nf3_Find(Nodes, nNodes, Id) >= 0 ) break;
                All[nAll++] = Fans[j][k] = Id;
                if ( j == 0 ) MaxFan = Abc_MaxInt(MaxFan, Id);
            }
            if ( k != (int)p->Cells[R->Gate[j]].nFanins ) break;
        }
        if ( j != 2 ) continue;
        Saved = Nf3_TrialArea(p, Root, All, nAll, &Slot);
        if ( R->Area >= Saved ) continue;
        Gain = Saved - R->Area;
        if ( Root-1 > Slot && !p->Objs[Root-1].Refs && p->Objs[Root-1].Gate != NF3_CI ) Slot = Root-1;
        if ( Gain < Best->Gain || Slot <= MaxFan ) continue;
        ChildDelay = Nf3_Delay(p, R->Gate[0], Fans[0], p->Cells[R->Gate[0]].nFanins);
        Delay = 0;
        for ( k = 0; k < (int)p->Cells[R->Gate[1]].nFanins; k++ )
            Delay = Abc_MaxInt(Delay, (Fans[1][k] == -1 ? ChildDelay : p->Objs[Fans[1][k]].Arrival) + p->Cells[R->Gate[1]].iDelays[k]);
        if ( Delay > p->Objs[Root].Required || (Gain == Best->Gain && Delay >= Best->Arrival) ) continue;
        Best->Gain = Gain; Best->Arrival = Delay; Best->Gate = R->Gate[1];
        Best->Slot = Slot; Best->ChildGate = R->Gate[0]; Best->ChildArrival = ChildDelay;
        Best->nFans = p->Cells[R->Gate[1]].nFanins;
        memcpy(Best->ChildFans, Fans[0], sizeof(int)*p->Cells[R->Gate[0]].nFanins);
        for ( k = 0; k < Best->nFans; k++ ) Best->Fans[k] = Fans[1][k] == -1 ? Slot : Fans[1][k];
    }
}

/**Function*************************************************************

  Synopsis    [Matches an exact window function against library cells.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf3_TryFunction( Nf3_Man_t * p, int Root, int * Nodes, int nNodes,
                     int * Leaves, int nLeaves, word Truth, Nf3_Plan_t * Best )
{
    word Key, Gain;
    unsigned Config, Perm, Phase;
    Vec_Int_t * Matches;
    int Fans[6], Keep[6], Gate, Entry, Index, Id, i, k, Delay;
    memcpy(Keep, Leaves, sizeof(int)*nLeaves);
    nLeaves = Abc_Tt6MinBase(&Truth, Keep, nLeaves);
    p->nTrials++;
    if ( nLeaves <= 1 )
    {
        Gate = NF3_ALIAS;
        Fans[0] = nLeaves == 0 ? (int)(Truth & 1) : Keep[0];
        if ( nLeaves == 1 && (Truth & 1) )
        {
            if ( p->Objs[Fans[0]].Compl >= 0 && p->Objs[p->Objs[Fans[0]].Compl].Refs ) Fans[0] = p->Objs[Fans[0]].Compl;
            else Gate = 3;
        }
        if ( Fans[0] >= Root ) return;
        Delay = Nf3_Delay(p, Gate, Fans, 1);
        Gain = Nf3_WindowGain(p, Root, Gate, Fans, 1);
        if ( Gain && Delay <= p->Objs[Root].Required &&
             (Gain > Best->Gain || (Gain == Best->Gain && Delay < Best->Arrival)) )
        {
            Best->Gain = Gain; Best->Arrival = Delay; Best->Gate = Gate;
            Best->Slot = 0; Best->nFans = 1; Best->Fans[0] = Fans[0];
        }
        return;
    }
    Key = Truth & 1 ? ~Truth : Truth;
    Index = *Vec_MemHashLookup(p->Truths, &Key);
    if ( Index < 0 || Index >= Vec_WecSize(p->Matches) ) goto two;
    Matches = Vec_WecEntry(p->Matches, Index);
    Vec_IntForEachEntryDouble(Matches, Gate, Entry, i)
    {
        Config = (unsigned)Entry;
        if ( (Config & 1) != (unsigned)(Truth & 1) || (int)p->Cells[Gate].nFanins != nLeaves ) continue;
        Perm = Config >> 8; Phase = (Config >> 1) & 127;
        for ( k = 0; k < nLeaves; k++, Perm >>= 4, Phase >>= 1 )
        {
            Id = Keep[Perm & 15];
            if ( Phase & 1 ) Id = p->Objs[Id].Compl;
            if ( Id < 0 || Id >= Root || !p->Objs[Id].Refs ) break;
            Fans[k] = Id;
        }
        if ( k < nLeaves ) continue;
        Delay = Nf3_Delay(p, Gate, Fans, nLeaves);
        if ( Delay > p->Objs[Root].Required ) continue;
        Gain = Nf3_WindowGain(p, Root, Gate, Fans, nLeaves);
        if ( !Gain || Gain < Best->Gain || (Gain == Best->Gain && Delay >= Best->Arrival) ) continue;
        Best->Gain = Gain; Best->Arrival = Delay; Best->Gate = Gate;
        Best->Slot = 0; Best->nFans = nLeaves; memcpy(Best->Fans, Fans, sizeof(int)*nLeaves);
    }
two:
    if ( p->fDecompose ) Nf3_TryTwo(p, Root, Nodes, nNodes, Keep, nLeaves, Truth, Best);
}
/**Function*************************************************************

  Synopsis    [Evaluates and matches an exact bounded physical-cell window.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf3_Try( Nf3_Man_t * p, int Root, int * Nodes, int nNodes,
                     int * Leaves, int nLeaves, Nf3_Plan_t * Best )
{
    word Values[NF3_WINDOW_MAX], Truth;
    unsigned Seen = 0;
    Truth = Nf3_WindowTruth_rec(p, Root, Nodes, nNodes, Leaves, nLeaves, Values, &Seen);
    Nf3_TryFunction(p, Root, Nodes, nNodes, Leaves, nLeaves, Truth, Best);
}

/**Function*************************************************************

  Synopsis    [Grows a bounded window directly in the physical cover.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Nf3_Expand( Nf3_Man_t * p, int * Nodes, int * pnNodes, int * Leaves, int * pnLeaves )
{
    Nf3_Obj_t * Obj;
    int i, k, j, Id, n, Best = -1, BestCount = 7;
    int Try[NF3_WINDOW_MAX*NF3_LEAF_MAX], BestLeaves[NF3_LEAF_MAX];
    word BestArea = 0, Area;
    if ( *pnNodes == NF3_WINDOW_MAX ) return 0;
    for ( i = 0; i < *pnLeaves; i++ )
    {
        Obj = p->Objs+Leaves[i];
        if ( Obj->Gate == NF3_CI || Obj->Refs > 16 ) continue;
        n = 0;
        // Keep the existing boundary order, then add only new fanins.
        for ( j = 0; j < *pnLeaves; j++ ) if ( j != i ) Try[n++] = Leaves[j];
        for ( k = 0; k < Obj->nFans; k++ )
        {
            Id = Obj->Fans[k];
            if ( Id < 2 || Nf3_Find(Nodes, *pnNodes, Id) >= 0 || Nf3_Find(Try, n, Id) >= 0 ) continue;
            Try[n++] = Id;
        }
        if ( n > NF3_LEAF_MAX ) continue;
        Area = Nf3_Area(p, Leaves[i]);
        if ( n < BestCount || (n == BestCount && Area > BestArea) )
        {
            Best = i; BestCount = n; BestArea = Area;
            memcpy(BestLeaves, Try, sizeof(int)*n);
        }
    }
    if ( Best < 0 ) return 0;
    Nodes[(*pnNodes)++] = Leaves[Best];
    memcpy(Leaves, BestLeaves, sizeof(int)*BestCount);
    *pnLeaves = BestCount;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Replaces a cell and releases its unused input cones.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf3_Apply( Nf3_Man_t * p, int Root, Nf3_Plan_t * Best )
{
    Nf3_Obj_t * Obj = p->Objs+Root;
    int i, Id;
    for ( i = 0; i < Best->nFans; i++ )
        if ( !Best->Slot || Best->Fans[i] != Best->Slot ) p->Objs[Best->Fans[i]].Refs++;
    if ( Best->Slot )
        for ( i = 0; i < (int)p->Cells[Best->ChildGate].nFanins; i++ ) p->Objs[Best->ChildFans[i]].Refs++;
    Vec_IntClear(p->Stack);
    for ( i = 0; i < Obj->nFans; i++ ) Vec_IntPush(p->Stack, Obj->Fans[i]);
    while ( Vec_IntSize(p->Stack) )
    {
        Id = Vec_IntPop(p->Stack);
        assert(p->Objs[Id].Refs > 0);
        if ( --p->Objs[Id].Refs ) continue;
        for ( i = 0; i < p->Objs[Id].nFans; i++ ) Vec_IntPush(p->Stack, p->Objs[Id].Fans[i]);
    }
    if ( Best->Slot )
    {
        Nf3_Obj_t * Child = p->Objs+Best->Slot;
        assert(Child->Refs == 0);
        if ( Child->Compl >= 0 ) p->Objs[Child->Compl].Compl = -1;
        Child->Compl = -1; Child->Gate = Best->ChildGate;
        Child->nFans = p->Cells[Best->ChildGate].nFanins;
        memcpy(Child->Fans, Best->ChildFans, sizeof(int)*Child->nFans);
        Child->Arrival = Best->ChildArrival; Child->Refs = 1;
        p->nTwo++;
    }
    Obj->Gate = Best->Gate; Obj->nFans = Best->nFans;
    memcpy(Obj->Fans, Best->Fans, sizeof(int)*Best->nFans);
    Obj->Arrival = Best->Arrival;
    p->nHits++; p->Saved += Best->Gain;
}
/**Function*************************************************************

  Synopsis    [Computes a sufficient care set at all immediate physical fanouts.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Nf3_Care( Nf3_Man_t * p, int Root, int * Nodes, int nNodes,
                     int * Leaves, int nLeaves, int * Edges, int nEdges )
{
    word Care = 0, Values[NF3_WINDOW_MAX], Inputs[6], Known[6], A, B;
    unsigned Seen = 0;
    int e, i, k, m, nUnknown, Unknown[6], Map[6], Id;
    Nf3_Obj_t * Obj;
    for ( e = 0; e < nEdges; e++ )
    {
        Obj = p->Objs+Edges[e];
        if ( !Obj->Refs || Nf3_Find(Obj->Fans, Obj->nFans, Root) < 0 ) continue;
        nUnknown = 0;
        for ( i = 0; i < Obj->nFans; i++ )
        {
            Id = Obj->Fans[i]; Map[i] = -1;
            if ( Id == Root ) { Map[i] = -2; continue; }
            if ( Id < 2 || Nf3_Find(Nodes, nNodes, Id) >= 0 || Nf3_Find(Leaves, nLeaves, Id) >= 0 )
                Known[i] = Nf3_WindowTruth_rec(p, Id, Nodes, nNodes, Leaves, nLeaves, Values, &Seen);
            else
            {
                k = Nf3_Find(Unknown, nUnknown, Id);
                if ( k < 0 ) { k = nUnknown; Unknown[nUnknown++] = Id; }
                Map[i] = k;
            }
        }
        for ( m = 0; m < (1 << nUnknown); m++ )
        {
            for ( i = 0; i < Obj->nFans; i++ )
                Inputs[i] = Map[i] == -2 ? 0 : Map[i] == -1 ? Known[i] : ((m >> Map[i]) & 1) ? ~(word)0 : 0;
            A = Nf3_Eval(p, Obj->Gate, Inputs);
            for ( i = 0; i < Obj->nFans; i++ ) if ( Map[i] == -2 ) Inputs[i] = ~(word)0;
            B = Nf3_Eval(p, Obj->Gate, Inputs);
            Care |= A ^ B;
            if ( Care == ~(word)0 ) return Care;
        }
    }
    return Care;
}
/**Function*************************************************************

  Synopsis    [Constrains boundary patterns by exact cell relations.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Nf3_Relations( Nf3_Man_t * p, int * Leaves, int nLeaves )
{
    static const word Vars[6] = { ABC_CONST(0xAAAAAAAAAAAAAAAA), ABC_CONST(0xCCCCCCCCCCCCCCCC),
        ABC_CONST(0xF0F0F0F0F0F0F0F0), ABC_CONST(0xFF00FF00FF00FF00),
        ABC_CONST(0xFFFF0000FFFF0000), ABC_CONST(0xFFFFFFFF00000000) };
    word Care = ~(word)0, Inputs[6];
    Nf3_Obj_t * Obj;
    int i, k, Pos;
    for ( i = 0; i < nLeaves; i++ )
    {
        Obj = p->Objs+Leaves[i];
        if ( Obj->Gate == NF3_CI ) continue;
        for ( k = 0; k < Obj->nFans; k++ )
        {
            if ( Obj->Fans[k] < 2 ) { Inputs[k] = Obj->Fans[k] ? ~(word)0 : 0; continue; }
            Pos = Nf3_Find(Leaves, nLeaves, Obj->Fans[k]);
            if ( Pos < 0 ) break;
            Inputs[k] = Vars[Pos];
        }
        if ( k == Obj->nFans ) Care &= ~(Vars[i] ^ Nf3_Eval(p, Obj->Gate, Inputs));
    }
    assert(Care);
    return Care;
}
/**Function*************************************************************

  Synopsis    [Matches two care-equivalent completions after variable projection.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf3_TryCare( Nf3_Man_t * p, int Root, int * Nodes, int nNodes,
                        int * Leaves, int nLeaves, word Truth, word Care, Nf3_Plan_t * Best )
{
    word On = Truth & Care, Off = ~Truth & Care, On0, On1, Off0, Off1;
    int i;
    if ( Care == ~(word)0 ) return;
    for ( i = nLeaves-1; i >= 0; i-- )
    {
        On0 = Abc_Tt6Cofactor0(On, i); On1 = Abc_Tt6Cofactor1(On, i);
        Off0 = Abc_Tt6Cofactor0(Off, i); Off1 = Abc_Tt6Cofactor1(Off, i);
        if ( (On0 & Off1) || (On1 & Off0) ) continue;
        On = On0 | On1; Off = Off0 | Off1;
    }
    assert(((On ^ Truth) & Care) == 0);
    assert(((~Off ^ Truth) & Care) == 0);
    if ( On != Truth ) Nf3_TryFunction(p, Root, Nodes, nNodes, Leaves, nLeaves, On, Best);
    if ( ~Off != Truth && ~Off != On ) Nf3_TryFunction(p, Root, Nodes, nNodes, Leaves, nLeaves, ~Off, Best);
}
/**Function*************************************************************

  Synopsis    [Recovers area using bounded local observability and boundary relations.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf3_Odc( Nf3_Man_t * p )
{
    Nf3_Obj_t * Obj;
    Nf3_Plan_t Best;
    int * Starts = ABC_CALLOC(int, p->nObjs+1), * Ends = ABC_ALLOC(int, p->nObjs), * Edges;
    int Id, i, k, nEdges, nNodes, nLeaves, Nodes[NF3_WINDOW_MAX], Leaves[NF3_LEAF_MAX];
    word Care, Truth, Values[NF3_WINDOW_MAX];
    unsigned Seen;
    // A forward pass only adds uses of already processed nodes. Thus a
    // static fanout index is complete for each still-unprocessed root.
    for ( Id = 2; Id < p->nObjs; Id++ )
        if ( p->Objs[Id].Refs )
            for ( k = 0; k < p->Objs[Id].nFans; k++ ) Starts[p->Objs[Id].Fans[k]+1]++;
    for ( Id = 1; Id <= p->nObjs; Id++ ) Starts[Id] += Starts[Id-1];
    nEdges = Starts[p->nObjs]; Edges = ABC_ALLOC(int, nEdges);
    memcpy(Ends, Starts, sizeof(int)*p->nObjs);
    for ( Id = 2; Id < p->nObjs; Id++ )
        if ( p->Objs[Id].Refs )
            for ( k = 0; k < p->Objs[Id].nFans; k++ ) Edges[Ends[p->Objs[Id].Fans[k]]++] = Id;
    Nf3_Required(p);
    for ( Id = 2; Id < p->nObjs; Id++ )
    {
        Obj = p->Objs+Id;
        if ( !Obj->Refs || Obj->Gate == NF3_CI ) continue;
        Obj->Arrival = Nf3_Delay(p, Obj->Gate, Obj->Fans, Obj->nFans);
        assert(Obj->Arrival <= Obj->Required);
        if ( Obj->Gate == NF3_ALIAS || Obj->Refs > 8 || Obj->Refs != Starts[Id+1]-Starts[Id] ) continue;
        memset(&Best, 0, sizeof(Best)); Best.Arrival = SCL_INFINITY;
        nNodes = 1; Nodes[0] = Id; nLeaves = 0;
        for ( k = 0; k < Obj->nFans; k++ )
            if ( Obj->Fans[k] >= 2 && Nf3_Find(Leaves, nLeaves, Obj->Fans[k]) < 0 ) Leaves[nLeaves++] = Obj->Fans[k];
        for ( i = 0; i < 3; i++ )
        {
            Seen = 0;
            Truth = Nf3_WindowTruth_rec(p, Id, Nodes, nNodes, Leaves, nLeaves, Values, &Seen);
            Care = Nf3_Care(p, Id, Nodes, nNodes, Leaves, nLeaves, Edges+Starts[Id], Starts[Id+1]-Starts[Id]);
            Care &= Nf3_Relations(p, Leaves, nLeaves);
            Nf3_TryCare(p, Id, Nodes, nNodes, Leaves, nLeaves, Truth, Care, &Best);
            if ( !Nf3_Expand(p, Nodes, &nNodes, Leaves, &nLeaves) ) break;
        }
        if ( Best.Gain )
        {
            if ( Obj->Compl >= 0 ) p->Objs[Obj->Compl].Compl = -1;
            Obj->Compl = -1;
            Nf3_Apply(p, Id, &Best); p->nOdc++;
        }
    }
    ABC_FREE(Starts); ABC_FREE(Ends); ABC_FREE(Edges);
}

typedef struct Nf3_Key_t_
{
    word Truth;
    int nFans, Fans[6], Phase;
} Nf3_Key_t;
/**Function*************************************************************

  Synopsis    [Normalizes a cell function over canonical physical input signals.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf3_Key( Nf3_Man_t * p, int Id, Nf3_Key_t * Key )
{
    static const word Vars[6] = { ABC_CONST(0xAAAAAAAAAAAAAAAA), ABC_CONST(0xCCCCCCCCCCCCCCCC),
        ABC_CONST(0xF0F0F0F0F0F0F0F0), ABC_CONST(0xFF00FF00FF00FF00),
        ABC_CONST(0xFFFF0000FFFF0000), ABC_CONST(0xFFFFFFFF00000000) };
    Nf3_Obj_t * Obj = p->Objs+Id;
    int i, j, Lit, Phase, Temp;
    memset(Key, 0, sizeof(*Key));
    if ( Obj->Gate == NF3_CI ) { Key->Truth = Vars[0]; Key->nFans = 1; Key->Fans[0] = Id; return; }
    Key->Truth = Obj->Gate == NF3_ALIAS ? Vars[0] : p->Cells[Obj->Gate].uTruth;
    Key->nFans = Obj->nFans;
    for ( i = 0; i < Obj->nFans; i++ )
    {
        Lit = Obj->Fans[i]; Phase = 0;
        while ( p->Objs[Lit].Gate == NF3_ALIAS || p->Objs[Lit].Gate == 2 || p->Objs[Lit].Gate == 3 )
        {
            Phase ^= p->Objs[Lit].Gate == 3;
            Lit = p->Objs[Lit].Fans[0];
        }
        if ( Lit < 2 ) Key->Truth = (Lit ^ Phase) ? Abc_Tt6Cofactor1(Key->Truth, i) : Abc_Tt6Cofactor0(Key->Truth, i);
        else if ( Phase ) Key->Truth = Abc_Tt6Flip(Key->Truth, i);
        Key->Fans[i] = Lit;
    }
    for ( i = 1; i < Key->nFans; i++ )
        for ( j = 0; j < i; j++ )
            if ( Key->Fans[j] == Key->Fans[i] )
            {
                Key->Truth = (Abc_Tt6Cofactor0(Key->Truth, i) & ~Vars[j]) |
                             (Abc_Tt6Cofactor1(Key->Truth, i) & Vars[j]);
                break;
            }
    Key->nFans = Abc_Tt6MinBase(&Key->Truth, Key->Fans, Key->nFans);
    for ( i = 1; i < Key->nFans; i++ )
        for ( j = i; j > 0 && Key->Fans[j-1] > Key->Fans[j]; j-- )
        {
            Temp = Key->Fans[j]; Key->Fans[j] = Key->Fans[j-1]; Key->Fans[j-1] = Temp;
            Key->Truth = Abc_Tt6SwapAdjacent(Key->Truth, j-1);
        }
    Key->Phase = (int)(Key->Truth & 1);
    if ( Key->Phase ) Key->Truth = ~Key->Truth;
}
/**Function*************************************************************

  Synopsis    [Hashes a normalized physical-cell function.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Nf3_KeyHash( Nf3_Key_t * Key )
{
    word Hash = Key->Truth;
    int i;
    for ( i = 0; i < Key->nFans; i++ ) Hash = (Hash ^ (unsigned)Key->Fans[i])*ABC_CONST(0x9e3779b97f4a7c15);
    Hash ^= Hash >> 32;
    return Hash;
}
/**Function*************************************************************

  Synopsis    [Shares functionally identical physical cells and inverter chains.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf3_Canonical( Nf3_Man_t * p )
{
    Nf3_Obj_t * Obj;
    Nf3_Key_t Key, Other;
    Nf3_Plan_t Best;
    int * Bins, * Next, nBins = 64, Id, Old, Bin, Gate, Delay, Fan, Compl;
    word Area, Hash, * Hashes;
    while ( nBins < p->nObjs && nBins < (1 << 22) ) nBins *= 2;
    Bins = ABC_FALLOC(int, nBins); Next = ABC_FALLOC(int, p->nObjs);
    Hashes = ABC_ALLOC(word, p->nObjs);
    Nf3_Required(p);
    for ( Id = 2; Id < p->nObjs; Id++ )
    {
        Obj = p->Objs+Id;
        if ( !Obj->Refs ) continue;
        if ( Obj->Gate != NF3_CI ) Obj->Arrival = Nf3_Delay(p, Obj->Gate, Obj->Fans, Obj->nFans);
        assert(Obj->Arrival <= Obj->Required);
        if ( Obj->Gate == NF3_ALIAS ) continue;
        Nf3_Key(p, Id, &Key); Hash = Nf3_KeyHash(&Key); Bin = (int)(Hash & (nBins-1));
        memset(&Best, 0, sizeof(Best)); Best.Arrival = SCL_INFINITY;
        if ( Obj->Gate != NF3_CI && Key.nFans == 0 )
        {
            Best.Gate = NF3_ALIAS; Best.nFans = 1; Best.Fans[0] = Key.Phase;
            Best.Gain = Nf3_Area(p, Id); Best.Arrival = 0;
        }
        else if ( Obj->Gate != NF3_CI )
        {
            for ( Old = Bins[Bin]; Old >= 0; Old = Next[Old] )
            {
                if ( !p->Objs[Old].Refs || Hashes[Old] != Hash ) continue;
                Nf3_Key(p, Old, &Other);
                if ( Other.Truth != Key.Truth || Other.nFans != Key.nFans || memcmp(Other.Fans, Key.Fans, sizeof(int)*Key.nFans) ) continue;
                Compl = Key.Phase ^ Other.Phase; Fan = Old;
                if ( Compl && p->Objs[Old].Compl >= 0 && p->Objs[Old].Compl < Id && p->Objs[p->Objs[Old].Compl].Refs )
                { Fan = p->Objs[Old].Compl; Compl = 0; }
                Gate = Compl ? 3 : NF3_ALIAS;
                Area = Gate < 0 ? 0 : p->Cells[Gate].AreaW;
                if ( Area >= Nf3_Area(p, Id) ) continue;
                Delay = Nf3_Delay(p, Gate, &Fan, 1);
                if ( Delay > Obj->Required ) continue;
                if ( Nf3_Area(p, Id)-Area < Best.Gain || (Nf3_Area(p, Id)-Area == Best.Gain && Delay >= Best.Arrival) ) continue;
                Best.Gate = Gate; Best.nFans = 1; Best.Fans[0] = Fan;
                Best.Gain = Nf3_Area(p, Id)-Area; Best.Arrival = Delay;
            }
        }
        if ( Best.Gain ) { Nf3_Apply(p, Id, &Best); p->nCanonical++; }
        else { Hashes[Id] = Hash; Next[Id] = Bins[Bin]; Bins[Bin] = Id; }
    }
    ABC_FREE(Hashes); ABC_FREE(Bins); ABC_FREE(Next);
}

/**Function*************************************************************

  Synopsis    [Reads a literal from a cell expression.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Nf3_ExprLit( int Lit, int nFans, int * Fans, int * Values )
{
    if ( Lit == EXP_CONST0 ) return 0;
    if ( Lit == EXP_CONST1 ) return 1;
    return (Lit < 2*nFans ? Fans[Lit >> 1] : Values[(Lit >> 1)-nFans]) ^ (Lit & 1);
}
/**Function*************************************************************

  Synopsis    [Realizes the recovered cell network with its GIA mapping.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Nf3_Export( Nf3_Man_t * p, Jf_Par_t * Pars )
{
    Gia_Man_t * q = Gia_ManStart(Gia_ManObjNum(p->Gia));
    Vec_Int_t * Offsets = Vec_IntAlloc(2*p->nObjs), * Data = Vec_IntStart(1);
    int * Copies = ABC_FALLOC(int, p->nObjs);
    Nf3_Obj_t * Obj;
    Vec_Int_t * Expr;
    int i, k, Id, Lit, Fans[6], Values[128], Start;
    word Area = 0;
    q->pName = Abc_UtilStrsav(p->Gia->pName); q->pSpec = Abc_UtilStrsav(p->Gia->pSpec);
    Copies[0] = 0; Copies[1] = 1;
    Vec_IntForEachEntry(p->Inputs, Id, i) Copies[Id] = Gia_ManAppendCi(q);
    Pars->Area = Pars->Edge = Pars->MapDelay = 0;
    for ( i = 2; i < p->nObjs; i++ )
    {
        Obj = p->Objs+i;
        if ( !Obj->Refs || Obj->Gate == NF3_CI ) continue;
        for ( k = 0; k < Obj->nFans; k++ ) { Fans[k] = Copies[Obj->Fans[k]]; assert(Fans[k] >= 0); }
        if ( Obj->Gate == NF3_ALIAS ) { Copies[i] = Fans[0]; continue; }
        if ( Obj->Gate == 3 && Fans[0] >= 2 && Vec_IntGetEntry(Offsets, Fans[0]) >= 0 &&
             Vec_IntGetEntry(Offsets, Fans[0]^1) == 0 &&
             ((Fans[0] & 1) == 0 || !Gia_ObjIsCi(Gia_ManObj(q, Abc_Lit2Var(Fans[0])))) )
        {
            // Use the standard opposite-phase inverter entry when its driver
            // is a cell or positive CI and this phase has no physical driver.
            Lit = Fans[0]^1;
            Vec_IntSetEntry(Offsets, Lit, -1);
        }
        else
        {
            Expr = p->Cells[Obj->Gate].vExpr;
            Start = Gia_ManObjNum(q);
            for ( k = 0; k < Exp_NodeNum(Expr); k++ )
                Values[k] = Gia_ManAppendAnd2(q, Nf3_ExprLit(Vec_IntEntry(Expr, 2*k), Obj->nFans, Fans, Values),
                                                Nf3_ExprLit(Vec_IntEntry(Expr, 2*k+1), Obj->nFans, Fans, Values));
            Lit = Nf3_ExprLit(Vec_IntEntryLast(Expr), Obj->nFans, Fans, Values);
            // Keep a distinct root if the physical cell simplifies to an
            // existing signal. Constants need only the shared constant driver.
            if ( Lit < 2 ) { Copies[i] = Lit; continue; }
            if ( Abc_Lit2Var(Lit) < Start ) Lit = Gia_ManAppendAnd(q, Lit, 1);
            Vec_IntSetEntry(Offsets, Lit, Vec_IntSize(Data));
            Vec_IntPush(Data, Obj->nFans);
            for ( k = 0; k < Obj->nFans; k++ ) Vec_IntPush(Data, Fans[k]);
            Vec_IntPush(Data, Obj->Gate);
        }
        Copies[i] = Lit;
        Area += p->Cells[Obj->Gate].AreaW;
        Pars->Area++; Pars->Edge += Obj->nFans;
    }
    Vec_IntForEachEntry(p->Outputs, Id, i)
    {
        assert(Copies[Id] >= 0);
        Gia_ManAppendCo(q, Copies[Id]);
        Pars->MapDelay = Abc_MaxInt(Pars->MapDelay, p->Objs[Id].Arrival);
    }
    Vec_IntFillExtra(Offsets, 2*Gia_ManObjNum(q), 0);
    Vec_IntForEachEntry(Offsets, Id, i) if ( Id > 0 ) Vec_IntAddToEntry(Offsets, i, 2*Gia_ManObjNum(q));
    Vec_IntAppend(Offsets, Data); q->vCellMapping = Offsets;
    Pars->MapAreaF = (float)((double)Area/SCL_NUM);
    Gie_ManDupMetadata(q, p->Gia);
    ABC_FREE(Copies); Vec_IntFree(Data);
    return q;
}
/**Function*************************************************************

  Synopsis    [Runs bounded cell-window recovery under the original delay bound.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Nf3_Recover( Gia_Man_t * Gia, Jf_Par_t * Pars, int nRounds )
{
    Nf3_Man_t * p;
    Nf3_Obj_t * Obj;
    Gia_Man_t * Result;
    Nf3_Plan_t Best;
    int Round, Id, k, nNodes, nLeaves, Nodes[NF3_WINDOW_MAX], Leaves[NF3_LEAF_MAX];
    word Hits;
    abctime Start = Abc_Clock();
    if ( Gia->pManTime || Gia_ManBufNum(Gia) || Gia->vInArrs || Gia->vOutReqs ||
         Gia->vCiArrs || Gia->vCoReqs || Scl_ConIsRunning() ) return Gia;
    p = Nf3_Import(Gia, Pars, nRounds > 1);
    if ( p == NULL ) return Gia;
    Nf3_Canonical(p);
    for ( Round = 0; Round < nRounds; Round++ )
    {
        Nf3_Required(p); Hits = p->nHits;
        for ( Id = 2; Id < p->nObjs; Id++ )
        {
            Obj = p->Objs+Id;
            if ( !Obj->Refs || Obj->Gate == NF3_CI ) continue;
            Obj->Arrival = Nf3_Delay(p, Obj->Gate, Obj->Fans, Obj->nFans);
            assert(Obj->Arrival <= Obj->Required);
            if ( Obj->Gate == NF3_ALIAS ) continue;
            memset(&Best, 0, sizeof(Best)); Best.Arrival = SCL_INFINITY;
            nNodes = 1; Nodes[0] = Id; nLeaves = 0;
            for ( k = 0; k < Obj->nFans; k++ )
                if ( Obj->Fans[k] >= 2 && Nf3_Find(Leaves, nLeaves, Obj->Fans[k]) < 0 ) Leaves[nLeaves++] = Obj->Fans[k];
            do { Nf3_Try(p, Id, Nodes, nNodes, Leaves, nLeaves, &Best); }
            while ( Nf3_Expand(p, Nodes, &nNodes, Leaves, &nLeaves) );
            if ( Best.Gain ) Nf3_Apply(p, Id, &Best);
        }
        if ( p->nHits == Hits ) break;
    }
    Nf3_Odc(p);
    Nf3_Canonical(p);
    Result = Nf3_Export(p, Pars);
    if ( Pars->fVerbose )
        Abc_Print(1, "&nf3 cell recovery: %lld trials, %lld changes, area saving >= %.3f, time %.3f sec\n",
            (long long)p->nTrials, (long long)p->nHits, (double)p->Saved/SCL_NUM,
            (double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
    if ( Pars->fVerbose ) Abc_Print(1, "&nf3 two-cell: %lld changes, %d cached functions, %lld hits\n", (long long)p->nTwo, p->nCached, (long long)p->nCacheHits);
    if ( Pars->fVerbose ) Abc_Print(1, "&nf3 observability: %lld changes\n", (long long)p->nOdc);
    if ( Pars->fVerbose ) Abc_Print(1, "&nf3 cell sharing: %lld changes\n", (long long)p->nCanonical);
    Nf3_CacheClear(p); ABC_FREE(p->Cache);
    ABC_FREE(p->Objs); Vec_IntFree(p->Inputs); Vec_IntFree(p->Outputs); Vec_IntFree(p->Stack); ABC_FREE(p);
    return Result;
}

/**Function*************************************************************

  Synopsis    [Initializes the area-recovery mapper.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nf3_ManSetDefaultPars( Jf_Par_t * pPars )
{
    Nf2_ManSetDefaultPars( pPars );
    pPars->nRounds = 8;
    pPars->nRoundsEla = 6;
}

/**Function*************************************************************

  Synopsis    [Maps alternative structures and recovers physical cell area.]

  Description [Construction choices require an ordinary untimed AIG.
  Other inputs retain their existing interface and use native NF2 mapping.
  The caller retains the input when a distinct manager is returned.]

  SideEffects [Uses the input scratch values and mapping fields.]

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Nf3_ManPerformMapping( Gia_Man_t * pGia, Jf_Par_t * pPars, int fSynthesis, int nRecover )
{
    Gia_Man_t * pWork = pGia, * pNew;
    if ( pGia == NULL || pPars == NULL || nRecover < 0 || nRecover > 1000 ) return NULL;
    if ( fSynthesis && !pGia->pManTime && !Gia_ManHasChoices(pGia) &&
         !Gia_ManXorNum(pGia) && !Gia_ManMuxNum(pGia) &&
         !Gia_ManBufNum(pGia) && !pGia->fGiaSimple &&
         !pGia->vCiArrs && !pGia->vInArrs && !pGia->vCoReqs && !pGia->vOutReqs )
    {
        pWork = Gia_ManDch2Construct( pGia, !pPars->fAreaOnly, pPars->fVerbose );
        if ( pWork == NULL ) return NULL;
    }
    pNew = Nf2_ManPerformMappingArea( pWork, pPars );
    if ( pWork != pGia && pWork != pNew ) Gia_ManStop( pWork );
    if ( pNew && nRecover > 0 )
    {
        pWork = Nf3_Recover(pNew, pPars, nRecover);
        if ( pNew != pGia && pNew != pWork ) Gia_ManStop(pNew);
        pNew = pWork;
    }
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
