/**CFile****************************************************************

  FileName    [giaScmapWindow.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [SCMap: shared-cell windows scored by the electrical model.]

  Description [A physical-cell copy of the mapped cover; bounded windows of
  it rematched as one cell or a two-cell decomposition, with exact reference
  accounting (as in the cell-window recovery of &nf3); and a search that
  scores the candidates with SCMap's electrical model (giaScmapInt.h) and
  keeps checkpoints measured after buffering. The cell windows are derived
  from &nf3 (giaNf3.c) by Alan Mishchenko.]

  Author      [Anqi Lu]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 2026.]

  Revision    [$Id: giaScmapWindow.c,v 1.00 2026/11/27 00:00:00 anqilu Exp $]

***********************************************************************/

// Preserve separately rounded timing costs. Fusing multiply-adds can change
// near-tied cover choices and their downstream sizing trajectories.
#if defined(__clang__)
#  pragma clang fp contract(off)
#elif defined(__GNUC__)
#  pragma GCC optimize ("fp-contract=off")
#elif defined(_MSC_VER)
#  pragma fp_contract(off)
#endif

#include "gia.h"
#include "giaEdit.h"
#include "giaScmapInt.h"
#include "base/main/main.h"
#include "map/mio/mio.h"
#include "map/mio/exp.h"
#include "map/scl/sclCon.h"
#include "misc/vec/vecMem.h"
#include "misc/util/utilTruth.h"
#include <float.h>
#include <limits.h>
#include <math.h>

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// Window size in cells and leaves; the objects that are not cells: inputs, and aliases (wires to Fans[0]).
enum { SCM_WIN_NODES = 8, SCM_WIN_LEAVES = 6, SCM_WIN_CI = -1, SCM_WIN_ALIAS = -2 };
// Two-cell recipes kept per function, and the cache of recipes by function.
enum { SCM_WIN_RECIPES = 128, SCM_WIN_CACHE_BINS = 8192, SCM_WIN_CACHE_LIMIT = 4096 };
// The work a window search may spend, in cells: a trial re-times the cells its edit reaches and makes
// a 1/64-cost pass over the cover, a commit re-measures the whole cover. Small covers use up their
// trials first; deep or large covers stop here.
#define SCM_WIN_WORK ((word)1 << 25)

// An object of the physical cover; Compl is the object of the opposite phase, -1 if none.
typedef struct Scm_WinObj_t_
{
    int Gate, nFans, Fans[6], Refs, Compl;
} Scm_WinObj_t;
// A two-cell implementation: Gate[0] drives pin 12 of Gate[1]; other pins are 2 x variable + phase.
typedef struct Scm_WinRecipe_t_
{
    int Gate[2];
    unsigned char Pins[2][6];
    unsigned Mask;
    int Profile[12];
    word Area;
} Scm_WinRecipe_t;
typedef struct Scm_WinCache_t_
{
    word Truth;
    Scm_WinRecipe_t * Recipes;
    int nVars, nRecipes;
} Scm_WinCache_t;
typedef struct Scm_WinMan_t_
{
    Gia_Man_t * Gia;
    Mio_Cell2_t * Cells;
    Vec_Mem_t * Truths;
    Vec_Wec_t * Matches;
    Scm_WinObj_t * Objs;
    Vec_Int_t * Inputs, * Outputs, * Stack;
    int nObjs, nCells;
    word MinArea;
    Scm_WinCache_t * Cache;
    int nCached;
} Scm_WinMan_t;
// A candidate for a root: one cell, or two cells whose child takes the free earlier object Slot.
typedef struct Scm_WinPlan_t_
{
    int Gate, nFans, Fans[6];
    int Slot, ChildGate, ChildFans[6];
    long long Gain;                 // exact logic area saved, in AreaW units
    double Score;
} Scm_WinPlan_t;
typedef struct Scm_WinState_t_
{
    Scm_RfPair_t Arrival, Slew, Load, Required;
    double Cost;
} Scm_WinState_t;
// The candidates of a window: the plans kept in order by Scm_WinPlanAdd, the signed area allowance
// (Extra), whether equal-area plans count (fEqual), and the timing that scores them.
typedef struct Scm_WinList_t_
{
    Scm_WinPlan_t * Plans;
    word Extra;
    int Count, Limit, fEqual;
    int Root;
    void * Model;
    Scm_WinState_t * State;
} Scm_WinList_t;
typedef struct Scm_WinMetric_t_
{
    word Area;                      // logic area in AreaW units
    double Electrical, Pressure;    // model delay; arrival beyond the threshold, summed over outputs and transitions
    double EstimatedArea;           // logic area plus modeled buffering and upsizing area
    double RealArea;                // measured after buffering (checkpoints)
    float RealDelay;
} Scm_WinMetric_t;
typedef struct Scm_WinRoot_t_ { int Id; word Area; double Path; } Scm_WinRoot_t;
typedef struct Scm_WinDelta_t_
{
    int * Starts, * Edges;          // fanouts of the committed cover per object, each 8 x sink + pin
    word * TimeBits;                // the objects to retime, as a bit set
    int TimeMin, TimeMax;           // its range of words
    unsigned char * DirtyLoad, * DirtyTime;
    Scm_RfPair_t * Caps;            // per cell pin: modeled input capacitance
    Vec_Int_t * Changed, * Loads, * Times, * Fans;   // a trial's changed objects, loads and retimed objects; scratch
} Scm_WinDelta_t;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Finds a node in a bounded window.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_WinFind( int * Data, int Count, int Id )
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
static word Scm_WinArea( Scm_WinMan_t * p, int Id )
{
    return p->Objs[Id].Gate < 0 ? 0 : p->Cells[p->Objs[Id].Gate].AreaW;
}

/**Function*************************************************************

  Synopsis    [Evaluates a physical cell over six Boolean variables.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Scm_WinEval( Scm_WinMan_t * p, int Gate, word * Inputs )
{
    Vec_Int_t * Expr;
    word Values[128];
    int i, nFans;
    if ( Gate == SCM_WIN_ALIAS ) return Inputs[0];
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
static int Scm_WinImportCell( Scm_WinMan_t * p, int * Map, int Lit )
{
    Scm_WinObj_t * Obj = p->Objs + p->nObjs;
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
    if ( p->Cells[Obj->Gate].AreaW > 2*p->MinArea )
    {
        p->Objs[p->nObjs+1] = *Obj;
        memset(Obj, 0, sizeof(*Obj)); Obj->Gate = SCM_WIN_ALIAS; Obj->Compl = -1;
        p->nObjs++;
    }
    return Map[Lit] = p->nObjs++;
}

/**Function*************************************************************

  Synopsis    [Builds a compact topological physical-cell network.]

  Description [Matches as &nf2 fetches them by default (no pin filtering,
  permutation or quick matching). Returns NULL if a cell has more than six
  inputs or a cell expression more than 128 nodes.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Scm_WinMan_t * Scm_WinImport( Gia_Man_t * Gia )
{
    Scm_WinMan_t * p = ABC_CALLOC(Scm_WinMan_t, 1);
    Gia_Obj_t * Obj;
    Scm_WinObj_t * Node;
    int * Map, i, k, Id, Lit, Count = Gia_ManCiNum(Gia) + 2;
    p->Gia = Gia;
    Mio_LibraryMatchesFetch((Mio_Library_t *)Abc_FrameReadLibGen(), &p->Truths, &p->Matches, &p->Cells, &p->nCells, 0, 0, 0);
    p->MinArea = ~(word)0;
    for ( i = 0; i < p->nCells; i++ )
    {
        if ( p->Cells[i].nFanins > 6 || Exp_NodeNum(p->Cells[i].vExpr) > 128 ) { ABC_FREE(p); return NULL; }
        if ( p->Cells[i].nFanins && p->MinArea > p->Cells[i].AreaW ) p->MinArea = p->Cells[i].AreaW;
    }
    Gia_ManForEachCell(Gia, Lit)
        Count += 1 + (p->Cells[Gia_ObjIsCellInv(Gia, Lit) ? 3 : Gia_ObjCellId(Gia, Lit)].AreaW > 2*p->MinArea);
    p->Objs = ABC_CALLOC(Scm_WinObj_t, Count);
    p->Inputs = Vec_IntAlloc(Gia_ManCiNum(Gia));
    p->Outputs = Vec_IntAlloc(Gia_ManCoNum(Gia));
    p->Stack = Vec_IntAlloc(128);
    p->Cache = ABC_CALLOC(Scm_WinCache_t, SCM_WIN_CACHE_BINS);
    Map = ABC_FALLOC(int, 2*Gia_ManObjNum(Gia));
    Map[0] = 0; Map[1] = 1;
    p->Objs[0].Gate = 0; p->Objs[1].Gate = 1;
    p->Objs[0].Compl = 1; p->Objs[1].Compl = 0;
    p->nObjs = 2;
    Gia_ManForEachCi(Gia, Obj, i)
    {
        Id = p->nObjs++; Node = p->Objs + Id;
        Node->Gate = SCM_WIN_CI; Node->Compl = -1;
        Map[2*Gia_ObjId(Gia, Obj)] = Id;
        Vec_IntPush(p->Inputs, Id);
    }
    Gia_ManForEachObj1(Gia, Obj, Id)
    {
        Lit = 2*Id;
        if ( Gia_ObjIsCo(Obj) ) continue;
        if ( Gia_ObjIsAnd(Obj) && Gia_ObjIsCellInv(Gia, Lit) )
        {
            Scm_WinImportCell(p, Map, Lit+1);
            Scm_WinImportCell(p, Map, Lit);
        }
        else
        {
            if ( Gia_ObjIsAnd(Obj) && Gia_ObjIsCell(Gia, Lit) ) Scm_WinImportCell(p, Map, Lit);
            if ( Gia_ObjIsCell(Gia, Lit+1) ) Scm_WinImportCell(p, Map, Lit+1);
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
    ABC_FREE(Map);
    return p;
}

/**Function*************************************************************

  Synopsis    [Releases the two-cell recipes.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_WinCacheClear( Scm_WinMan_t * p )
{
    int i;
    for ( i = 0; i < SCM_WIN_CACHE_BINS; i++ ) ABC_FREE(p->Cache[i].Recipes);
    memset(p->Cache, 0, sizeof(Scm_WinCache_t)*SCM_WIN_CACHE_BINS);
    p->nCached = 0;
}

/**Function*************************************************************

  Synopsis    [Releases the physical-cell network.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_WinManStop( Scm_WinMan_t * p )
{
    Scm_WinCacheClear(p); ABC_FREE(p->Cache); ABC_FREE(p->Objs);
    Vec_IntFree(p->Inputs); Vec_IntFree(p->Outputs); Vec_IntFree(p->Stack); ABC_FREE(p);
}

/**Function*************************************************************

  Synopsis    [Evaluates a window with independent boundary signals.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Scm_WinTruth_rec( Scm_WinMan_t * p, int Id, int * Nodes, int nNodes,
                              int * Leaves, int nLeaves, word * Values, unsigned * Seen )
{
    static const word Vars[6] = {
        ABC_CONST(0xAAAAAAAAAAAAAAAA), ABC_CONST(0xCCCCCCCCCCCCCCCC),
        ABC_CONST(0xF0F0F0F0F0F0F0F0), ABC_CONST(0xFF00FF00FF00FF00),
        ABC_CONST(0xFFFF0000FFFF0000), ABC_CONST(0xFFFFFFFF00000000) };
    Scm_WinObj_t * Obj = p->Objs+Id;
    word Inputs[6];
    int Pos, i;
    if ( Id < 2 ) return Id ? ~(word)0 : 0;
    Pos = Scm_WinFind(Leaves, nLeaves, Id);
    if ( Pos >= 0 ) return Vars[Pos];
    Pos = Scm_WinFind(Nodes, nNodes, Id);
    assert(Pos >= 0);
    if ( (*Seen >> Pos) & 1 ) return Values[Pos];
    for ( i = 0; i < Obj->nFans; i++ )
        Inputs[i] = Scm_WinTruth_rec(p, Obj->Fans[i], Nodes, nNodes, Leaves, nLeaves, Values, Seen);
    *Seen |= 1u << Pos;
    return Values[Pos] = Scm_WinEval(p, Obj->Gate, Inputs);
}

/**Function*************************************************************

  Synopsis    [Counts the complete released cone while protecting replacement pins.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Scm_WinTrialArea( Scm_WinMan_t * p, int Root, int * Fans, int nFans, int * Slot )
{
    word Saved = Scm_WinArea(p, Root);
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
        if ( Id >= 2 ) Saved += Scm_WinArea(p, Id);
        if ( Slot && p->Objs[Id].Gate != SCM_WIN_CI && Id > *Slot ) *Slot = Id;
        for ( k = 0; k < p->Objs[Id].nFans; k++ ) Vec_IntPush(p->Stack, p->Objs[Id].Fans[k]);
    }
    Vec_IntForEachEntry(p->Stack, Id, i) p->Objs[Id].Refs++;
    for ( i = 0; i < nFans; i++ ) p->Objs[Fans[i]].Refs--;
    Vec_IntClear(p->Stack);
    return Saved;
}

/**Function*************************************************************

  Synopsis    [Replaces a cell and releases its unused input cones.]

  Description [A non-NULL vChanged receives every object whose references
  or implementation change, so a trial can be undone.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_WinApply( Scm_WinMan_t * p, int Root, Scm_WinPlan_t * Plan, Vec_Int_t * vChanged )
{
    Scm_WinObj_t * Obj = p->Objs+Root;
    int i, Id;
    if ( vChanged ) Vec_IntPush(vChanged, Root);
    for ( i = 0; i < Plan->nFans; i++ )
        if ( !Plan->Slot || Plan->Fans[i] != Plan->Slot )
        {
            if ( vChanged ) Vec_IntPush(vChanged, Plan->Fans[i]);
            p->Objs[Plan->Fans[i]].Refs++;
        }
    if ( Plan->Slot )
        for ( i = 0; i < (int)p->Cells[Plan->ChildGate].nFanins; i++ )
        {
            if ( vChanged ) Vec_IntPush(vChanged, Plan->ChildFans[i]);
            p->Objs[Plan->ChildFans[i]].Refs++;
        }
    Vec_IntClear(p->Stack);
    for ( i = 0; i < Obj->nFans; i++ ) Vec_IntPush(p->Stack, Obj->Fans[i]);
    while ( Vec_IntSize(p->Stack) )
    {
        Id = Vec_IntPop(p->Stack);
        if ( vChanged ) Vec_IntPush(vChanged, Id);
        assert(p->Objs[Id].Refs > 0);
        if ( --p->Objs[Id].Refs ) continue;
        for ( i = 0; i < p->Objs[Id].nFans; i++ ) Vec_IntPush(p->Stack, p->Objs[Id].Fans[i]);
    }
    if ( Plan->Slot )
    {
        Scm_WinObj_t * Child = p->Objs+Plan->Slot;
        if ( vChanged ) Vec_IntPush(vChanged, Plan->Slot);
        assert(Child->Refs == 0);
        if ( Child->Compl >= 0 )
        {
            if ( vChanged ) Vec_IntPush(vChanged, Child->Compl);
            p->Objs[Child->Compl].Compl = -1;
        }
        Child->Compl = -1; Child->Gate = Plan->ChildGate;
        Child->nFans = p->Cells[Plan->ChildGate].nFanins;
        memcpy(Child->Fans, Plan->ChildFans, sizeof(int)*Child->nFans);
        Child->Refs = 1;
    }
    Obj->Gate = Plan->Gate; Obj->nFans = Plan->nFans;
    memcpy(Obj->Fans, Plan->Fans, sizeof(int)*Plan->nFans);
}

/**Function*************************************************************

  Synopsis    [Reads a literal from a cell expression.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_WinExprLit( int Lit, int nFans, int * Fans, int * Values )
{
    if ( Lit == EXP_CONST0 ) return 0;
    if ( Lit == EXP_CONST1 ) return 1;
    return (Lit < 2*nFans ? Fans[Lit >> 1] : Values[(Lit >> 1)-nFans]) ^ (Lit & 1);
}

/**Function*************************************************************

  Synopsis    [Realizes the physical-cell network with its GIA mapping.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Scm_WinExport( Scm_WinMan_t * p )
{
    Gia_Man_t * q = Gia_ManStart(Gia_ManObjNum(p->Gia));
    Vec_Int_t * Offsets = Vec_IntAlloc(2*p->nObjs), * Data = Vec_IntStart(1);
    int * Copies = ABC_FALLOC(int, p->nObjs);
    Scm_WinObj_t * Obj;
    Vec_Int_t * Expr;
    int i, k, Id, Lit, Fans[6], Values[128], Start;
    q->pName = Abc_UtilStrsav(p->Gia->pName); q->pSpec = Abc_UtilStrsav(p->Gia->pSpec);
    Copies[0] = 0; Copies[1] = 1;
    Vec_IntForEachEntry(p->Inputs, Id, i) Copies[Id] = Gia_ManAppendCi(q);
    for ( i = 2; i < p->nObjs; i++ )
    {
        Obj = p->Objs+i;
        if ( !Obj->Refs || Obj->Gate == SCM_WIN_CI ) continue;
        for ( k = 0; k < Obj->nFans; k++ ) { Fans[k] = Copies[Obj->Fans[k]]; assert(Fans[k] >= 0); }
        if ( Obj->Gate == SCM_WIN_ALIAS ) { Copies[i] = Fans[0]; continue; }
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
                Values[k] = Gia_ManAppendAnd2(q, Scm_WinExprLit(Vec_IntEntry(Expr, 2*k), Obj->nFans, Fans, Values),
                                                Scm_WinExprLit(Vec_IntEntry(Expr, 2*k+1), Obj->nFans, Fans, Values));
            Lit = Scm_WinExprLit(Vec_IntEntryLast(Expr), Obj->nFans, Fans, Values);
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
    }
    Vec_IntForEachEntry(p->Outputs, Id, i)
    {
        assert(Copies[Id] >= 0);
        Gia_ManAppendCo(q, Copies[Id]);
    }
    Vec_IntFillExtra(Offsets, 2*Gia_ManObjNum(q), 0);
    Vec_IntForEachEntry(Offsets, Id, i) if ( Id > 0 ) Vec_IntAddToEntry(Offsets, i, 2*Gia_ManObjNum(q));
    Vec_IntAppend(Offsets, Data); q->vCellMapping = Offsets;
    Gie_ManDupMetadata(q, p->Gia);
    ABC_FREE(Copies); Vec_IntFree(Data);
    return q;
}

/**Function*************************************************************

  Synopsis    [Compares area and phase-specific pin delay profiles.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_WinDominates( Scm_WinRecipe_t * A, Scm_WinRecipe_t * B )
{
    int i;
    if ( A->Area > B->Area || A->Mask != B->Mask ) return 0;
    for ( i = 0; i < 12; i++ ) if ( A->Profile[i] > B->Profile[i] ) return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Retains a bounded nondominated set of physical implementations.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_WinRecipeAdd( Scm_WinMan_t * p, Scm_WinRecipe_t * Recipes, int * pnRecipes, Scm_WinRecipe_t * R )
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
    for ( i = 0; i < *pnRecipes; i++ ) if ( Scm_WinDominates(Recipes+i, R) ) return;
    for ( i = 0; i < *pnRecipes; )
        if ( Scm_WinDominates(R, Recipes+i) ) Recipes[i] = Recipes[--*pnRecipes]; else i++;
    if ( *pnRecipes < SCM_WIN_RECIPES ) { Recipes[(*pnRecipes)++] = *R; return; }
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
static Scm_WinCache_t * Scm_WinRecipes( Scm_WinMan_t * p, word Truth, int nVars )
{
    static const word Vars[6] = { ABC_CONST(0xAAAAAAAAAAAAAAAA), ABC_CONST(0xCCCCCCCCCCCCCCCC),
        ABC_CONST(0xF0F0F0F0F0F0F0F0), ABC_CONST(0xFF00FF00FF00FF00),
        ABC_CONST(0xFFFF0000FFFF0000), ABC_CONST(0xFFFFFFFF00000000) };
    Scm_WinCache_t * Entry;
    Scm_WinRecipe_t Recipes[SCM_WIN_RECIPES], R;
    Vec_Int_t * GMatches, * HMatches;
    word Hash, Rows[64], First, Second, G, H, Key, Check, Inputs[6];
    unsigned CfgG, CfgH, Phase, Perm;
    int Bin, Mask, Bound[6], Free[6], nBound, nFree, b, f, m, i, j, k, nRecipes = 0;
    int GId, HId, GCfg, HCfg, GGate, HGate, HIndex, Valid;
    Hash = Truth ^ (Truth >> 31); Hash *= ABC_CONST(0xbf58476d1ce4e5b9); Hash ^= Hash >> 29;
    Bin = (int)(Hash & (SCM_WIN_CACHE_BINS-1));
    while ( p->Cache[Bin].nVars )
    {
        Entry = p->Cache+Bin;
        if ( Entry->Truth == Truth && Entry->nVars == nVars ) return Entry;
        Bin = (Bin+1) & (SCM_WIN_CACHE_BINS-1);
    }
    if ( p->nCached == SCM_WIN_CACHE_LIMIT ) { Scm_WinCacheClear(p); Bin = (int)(Hash & (SCM_WIN_CACHE_BINS-1)); }
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
                Check = Scm_WinEval(p, GGate, Inputs);
                for ( k = 0; k <= nFree; k++ )
                    Inputs[k] = R.Pins[1][k] == 12 ? Check : (R.Pins[1][k] & 1) ? ~Vars[R.Pins[1][k] >> 1] : Vars[R.Pins[1][k] >> 1];
                assert(Scm_WinEval(p, HGate, Inputs) == Truth);
                Scm_WinRecipeAdd(p, Recipes, &nRecipes, &R);
            }
        }
    }
    Entry->nRecipes = nRecipes;
    Entry->Recipes = ABC_ALLOC(Scm_WinRecipe_t, nRecipes);
    if ( nRecipes ) memcpy(Entry->Recipes, Recipes, sizeof(Scm_WinRecipe_t)*nRecipes);
    return Entry;
}

/**Function*************************************************************

  Synopsis    [Orders candidates by exact area gain and stable implementation keys.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_WinPlanCompare( const void * pA, const void * pB )
{
    const Scm_WinPlan_t * A = (const Scm_WinPlan_t *)pA;
    const Scm_WinPlan_t * B = (const Scm_WinPlan_t *)pB;
    int k;
    if ( A->Score != B->Score ) return A->Score < B->Score ? -1 : 1;
    if ( A->Gain != B->Gain ) return A->Gain > B->Gain ? -1 : 1;
    if ( A->Gate != B->Gate ) return A->Gate < B->Gate ? -1 : 1;
    if ( A->Slot != B->Slot ) return A->Slot < B->Slot ? -1 : 1;
    if ( A->ChildGate != B->ChildGate ) return A->ChildGate < B->ChildGate ? -1 : 1;
    if ( A->nFans != B->nFans ) return A->nFans < B->nFans ? -1 : 1;
    for ( k = 0; k < 6; k++ )
    {
        if ( A->Fans[k] != B->Fans[k] ) return A->Fans[k] < B->Fans[k] ? -1 : 1;
        if ( A->ChildFans[k] != B->ChildFans[k] ) return A->ChildFans[k] < B->ChildFans[k] ? -1 : 1;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Ranks a timing recipe at the root's load and required times.]

  Description [This local score shortlists plans; incremental cover timing
  and the measured cover still decide whether to keep one.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static double Scm_WinPlanScore( Scm_WinList_t * p, Scm_WinPlan_t * Plan )
{
    Scm_RfPair_t Arrs[6], Slews[6], Arr, Slew, ChildArr, ChildSlew;
    Scm_RfPair_t Load = {{0, 0}};
    int k, t;
    if ( Plan->Slot )
    {
        for ( k = 0; k < Plan->nFans; k++ ) if ( Plan->Fans[k] == Plan->Slot )
        {
            Scm_RfPair_t Cap = Scm_WinModelCap(p->Model, Plan->Gate, k);
            for ( t = 0; t < 2; t++ ) Load.Value[t] += Cap.Value[t];
        }
        for ( k = 0; k < 6; k++ )
        {
            Arrs[k] = p->State[Plan->ChildFans[k]].Arrival;
            Slews[k] = p->State[Plan->ChildFans[k]].Slew;
        }
        if ( !Scm_WinModelCell(p->Model, -1, Plan->ChildGate, Load, Arrs, Slews, &ChildArr, &ChildSlew) ) return DBL_MAX;
    }
    for ( k = 0; k < Plan->nFans; k++ )
    {
        int fChild = Plan->Slot && Plan->Fans[k] == Plan->Slot;
        Arrs[k] = fChild ? ChildArr : p->State[Plan->Fans[k]].Arrival;
        Slews[k] = fChild ? ChildSlew : p->State[Plan->Fans[k]].Slew;
    }
    if ( Plan->Gate < 0 ) Arr = Arrs[0];
    else if ( !Scm_WinModelCell(p->Model, -1, Plan->Gate, p->State[p->Root].Load, Arrs, Slews, &Arr, &Slew) ) return DBL_MAX;
    return fmax((double)Arr.Value[0]-p->State[p->Root].Required.Value[0],
                (double)Arr.Value[1]-p->State[p->Root].Required.Value[1]);
}

/**Function*************************************************************

  Synopsis    [Keeps a bounded deterministic list of candidate implementations.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_WinPlanAdd( Scm_WinList_t * p, Scm_WinPlan_t * Plan )
{
    int Lo = 0, Hi = p->Count, Mid, Order;
    if ( p->Model ) Plan->Score = Scm_WinPlanScore(p, Plan);
    // Reject below the retained frontier before searching for insertion.
    if ( p->Count == p->Limit && Scm_WinPlanCompare(Plan, p->Plans+p->Count-1) >= 0 ) return;
    while ( Lo < Hi )
    {
        Mid = Lo + (Hi-Lo)/2;
        Order = Scm_WinPlanCompare(Plan, p->Plans+Mid);
        if ( !Order ) return;
        if ( Order < 0 ) Hi = Mid;
        else Lo = Mid+1;
    }
    if ( p->Count < p->Limit ) p->Count++;
    memmove(p->Plans+Lo+1, p->Plans+Lo, sizeof(Scm_WinPlan_t)*(p->Count-Lo-1));
    p->Plans[Lo] = *Plan;
}

/**Function*************************************************************

  Synopsis    [Adds a one-cell candidate within the signed area allowance.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_WinEmit( Scm_WinMan_t * p, int Root, int Gate, int * Fans, int nFans, Scm_WinList_t * List )
{
    Scm_WinPlan_t Plan = {0};
    Scm_WinObj_t * Obj = p->Objs+Root;
    word Saved = Scm_WinTrialArea(p, Root, Fans, nFans, NULL);
    word Added = Gate < 0 ? 0 : p->Cells[Gate].AreaW;
    if ( (Added > Saved && Added-Saved > List->Extra) || (Added == Saved && !List->fEqual) ) return;
    if ( Gate == Obj->Gate && nFans == Obj->nFans && !memcmp(Fans, Obj->Fans, sizeof(int)*nFans) ) return;
    Plan.Gain = (long long)Saved-(long long)Added;
    Plan.Gate = Gate; Plan.nFans = nFans;
    memcpy(Plan.Fans, Fans, sizeof(int)*nFans);
    Scm_WinPlanAdd(List, &Plan);
}

/**Function*************************************************************

  Synopsis    [Adds two-cell candidates in released or reserved earlier slots.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_WinTryTwo( Scm_WinMan_t * p, int Root, int * Nodes, int nNodes,
                           int * Leaves, int nLeaves, word Truth, Scm_WinList_t * List )
{
    Scm_WinCache_t * Entry;
    Scm_WinRecipe_t * R;
    Scm_WinPlan_t Plan;
    int i, j, k, Fans[2][6], All[12], nAll, Phase, Pin, Id, Slot, MaxFan;
    word Saved;
    if ( nLeaves < 2 ) return;
    Saved = Scm_WinTrialArea(p, Root, NULL, 0, NULL);
    if ( Saved + List->Extra < 2*p->MinArea ) return;
    Entry = Scm_WinRecipes(p, Truth, nLeaves);
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
                if ( Id < 0 || Id >= Root || !p->Objs[Id].Refs || Scm_WinFind(Nodes, nNodes, Id) >= 0 ) break;
                All[nAll++] = Fans[j][k] = Id;
                if ( j == 0 ) MaxFan = Abc_MaxInt(MaxFan, Id);
            }
            if ( k != (int)p->Cells[R->Gate[j]].nFanins ) break;
        }
        if ( j != 2 ) continue;
        Saved = Scm_WinTrialArea(p, Root, All, nAll, &Slot);
        if ( (R->Area > Saved && R->Area-Saved > List->Extra) || (R->Area == Saved && !List->fEqual) ) continue;
        if ( Root-1 > Slot && !p->Objs[Root-1].Refs && p->Objs[Root-1].Gate != SCM_WIN_CI ) Slot = Root-1;
        if ( Slot <= MaxFan ) continue;
        memset(&Plan, 0, sizeof(Plan));
        Plan.Gain = (long long)Saved-(long long)R->Area;
        Plan.Gate = R->Gate[1]; Plan.Slot = Slot; Plan.ChildGate = R->Gate[0];
        Plan.nFans = p->Cells[R->Gate[1]].nFanins;
        memcpy(Plan.ChildFans, Fans[0], sizeof(int)*p->Cells[R->Gate[0]].nFanins);
        for ( k = 0; k < Plan.nFans; k++ ) Plan.Fans[k] = Fans[1][k] == -1 ? Slot : Fans[1][k];
        Scm_WinPlanAdd(List, &Plan);
    }
}

/**Function*************************************************************

  Synopsis    [Matches an exact window function against library cells.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_WinTryFunction( Scm_WinMan_t * p, int Root, int * Nodes, int nNodes,
                                int * Leaves, int nLeaves, word Truth, Scm_WinList_t * List )
{
    word Key;
    unsigned Config, Perm, Phase;
    Vec_Int_t * Matches;
    int Fans[6], Keep[6], Gate, Entry, Index, Id, i, k;
    memcpy(Keep, Leaves, sizeof(int)*nLeaves);
    nLeaves = Abc_Tt6MinBase(&Truth, Keep, nLeaves);
    if ( nLeaves <= 1 )
    {
        Gate = SCM_WIN_ALIAS;
        Fans[0] = nLeaves == 0 ? (int)(Truth & 1) : Keep[0];
        if ( nLeaves == 1 && (Truth & 1) )
        {
            if ( p->Objs[Fans[0]].Compl >= 0 && p->Objs[p->Objs[Fans[0]].Compl].Refs ) Fans[0] = p->Objs[Fans[0]].Compl;
            else Gate = 3;
        }
        if ( Fans[0] < Root ) Scm_WinEmit(p, Root, Gate, Fans, 1, List);
        return;
    }
    Key = Truth & 1 ? ~Truth : Truth;
    Index = *Vec_MemHashLookup(p->Truths, &Key);
    if ( Index >= 0 && Index < Vec_WecSize(p->Matches) )
    {
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
            if ( k == nLeaves ) Scm_WinEmit(p, Root, Gate, Fans, nLeaves, List);
        }
    }
    Scm_WinTryTwo(p, Root, Nodes, nNodes, Keep, nLeaves, Truth, List);
}

/**Function*************************************************************

  Synopsis    [Evaluates and matches an exact bounded physical-cell window.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_WinTry( Scm_WinMan_t * p, int Root, int * Nodes, int nNodes,
                        int * Leaves, int nLeaves, Scm_WinList_t * List )
{
    word Values[SCM_WIN_NODES], Truth;
    unsigned Seen = 0;
    Truth = Scm_WinTruth_rec(p, Root, Nodes, nNodes, Leaves, nLeaves, Values, &Seen);
    Scm_WinTryFunction(p, Root, Nodes, nNodes, Leaves, nLeaves, Truth, List);
}

/**Function*************************************************************

  Synopsis    [Grows a bounded window directly in the physical cover.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_WinExpand( Scm_WinMan_t * p, int * Nodes, int * pnNodes, int * Leaves, int * pnLeaves )
{
    Scm_WinObj_t * Obj;
    int i, k, j, Id, n, Best = -1, BestCount = SCM_WIN_LEAVES+1;
    int Try[SCM_WIN_NODES*SCM_WIN_LEAVES], BestLeaves[SCM_WIN_LEAVES];
    word BestArea = 0, Area;
    if ( *pnNodes == SCM_WIN_NODES ) return 0;
    for ( i = 0; i < *pnLeaves; i++ )
    {
        Obj = p->Objs+Leaves[i];
        if ( Obj->Gate == SCM_WIN_CI || Obj->Refs > 16 ) continue;
        n = 0;
        // Keep the existing boundary order, then add only new fanins.
        for ( j = 0; j < *pnLeaves; j++ ) if ( j != i ) Try[n++] = Leaves[j];
        for ( k = 0; k < Obj->nFans; k++ )
        {
            Id = Obj->Fans[k];
            if ( Id < 2 || Scm_WinFind(Nodes, *pnNodes, Id) >= 0 || Scm_WinFind(Try, n, Id) >= 0 ) continue;
            Try[n++] = Id;
        }
        if ( n > SCM_WIN_LEAVES ) continue;
        Area = Scm_WinArea(p, Leaves[i]);
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

  Synopsis    [Collects the candidates of the windows grown from a root.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_WinEnumerate( Scm_WinMan_t * p, int Root, Scm_WinList_t * List, word Extra, int fTiming )
{
    int Nodes[SCM_WIN_NODES] = {Root}, Leaves[SCM_WIN_LEAVES], nNodes = 1, nLeaves = 0, k;
    Scm_WinObj_t * Obj = p->Objs+Root;
    List->Extra = Extra; List->fEqual = fTiming;
    List->Count = 0;
    for ( k = 0; k < Obj->nFans; k++ )
        if ( Obj->Fans[k] >= 2 && Scm_WinFind(Leaves, nLeaves, Obj->Fans[k]) < 0 ) Leaves[nLeaves++] = Obj->Fans[k];
    do { Scm_WinTry(p, Root, Nodes, nNodes, Leaves, nLeaves, List); }
    while ( Scm_WinExpand(p, Nodes, &nNodes, Leaves, &nLeaves) );
}

/**Function*************************************************************

  Synopsis    [Builds ordered physical fanouts after a committed window edit.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_WinDeltaBuild( Scm_WinMan_t * p, Scm_WinDelta_t * d )
{
    int i, k;
    memset(d->Starts, 0, sizeof(int)*(p->nObjs+1));
    for ( i = 2; i < p->nObjs; i++ ) if ( p->Objs[i].Refs )
        for ( k = 0; k < p->Objs[i].nFans; k++ ) d->Starts[p->Objs[i].Fans[k]+1]++;
    for ( i = 1; i <= p->nObjs; i++ ) d->Starts[i] += d->Starts[i-1];
    // Fill backwards so each fanout list has increasing object and pin IDs.
    for ( i = p->nObjs-1; i >= 2; i-- ) if ( p->Objs[i].Refs )
        for ( k = p->Objs[i].nFans-1; k >= 0; k-- )
            d->Edges[--d->Starts[p->Objs[i].Fans[k]+1]] = 8*i+k;
    for ( i = 0; i < p->nObjs; i++ ) d->Starts[i] = d->Starts[i+1];
    d->Starts[p->nObjs] = 0;
    for ( i = 2; i < p->nObjs; i++ ) if ( p->Objs[i].Refs ) d->Starts[p->nObjs] += p->Objs[i].nFans;
}

/**Function*************************************************************

  Synopsis    [Allocates per-search incremental timing state.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Scm_WinDelta_t * Scm_WinDeltaStart( Scm_WinMan_t * p, void * Model )
{
    Scm_WinDelta_t * d;
    int i, k;
    if ( p->nObjs > INT_MAX/8 || p->nCells > INT_MAX/6 ) return NULL;
    for ( i = 0; i < p->nCells; i++ ) if ( p->Cells[i].nFanins > 6 ) return NULL;
    d = ABC_CALLOC(Scm_WinDelta_t, 1);
    d->Starts = ABC_ALLOC(int, p->nObjs+1);
    d->Edges = ABC_ALLOC(int, 6*p->nObjs);
    d->TimeBits = ABC_CALLOC(word, Abc_Bit6WordNum(p->nObjs));
    d->DirtyLoad = ABC_CALLOC(unsigned char, p->nObjs);
    d->DirtyTime = ABC_CALLOC(unsigned char, p->nObjs);
    d->Caps = ABC_CALLOC(Scm_RfPair_t, 6*p->nCells);
    d->Changed = Vec_IntAlloc(64); d->Loads = Vec_IntAlloc(64); d->Fans = Vec_IntAlloc(64);
    d->Times = Vec_IntAlloc(64);
    for ( i = 0; i < p->nCells; i++ )
        for ( k = 0; k < (int)p->Cells[i].nFanins; k++ ) d->Caps[6*i+k] = Scm_WinModelCap(Model, i, k);
    Scm_WinDeltaBuild(p, d);
    return d;
}

/**Function*************************************************************

  Synopsis    [Releases incremental timing state.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_WinDeltaStop( Scm_WinDelta_t * d )
{
    if ( d == NULL ) return;
    ABC_FREE(d->Starts); ABC_FREE(d->Edges); ABC_FREE(d->DirtyLoad); ABC_FREE(d->DirtyTime); ABC_FREE(d->Caps);
    ABC_FREE(d->TimeBits);
    Vec_IntFree(d->Changed); Vec_IntFree(d->Loads); Vec_IntFree(d->Times); Vec_IntFree(d->Fans); ABC_FREE(d);
}

/**Function*************************************************************

  Synopsis    [Marks an object whose sink load may have changed.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_WinDeltaLoad( Scm_WinDelta_t * d, int Id )
{
    if ( d->DirtyLoad[Id] ) return;
    d->DirtyLoad[Id] = 1;
    Vec_IntPush(d->Loads, Id);
}

/**Function*************************************************************

  Synopsis    [Marks forward timing and records the state to restore.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_WinDeltaTime( Scm_WinDelta_t * d, int Id )
{
    if ( d->DirtyTime[Id] ) return;
    d->DirtyTime[Id] = 1;
    d->TimeBits[Id >> 6] |= (word)1 << (Id & 63);
    d->TimeMin = Abc_MinInt(d->TimeMin, Id >> 6);
    d->TimeMax = Abc_MaxInt(d->TimeMax, Id >> 6);
    Vec_IntPush(d->Times, Id);
}

/**Function*************************************************************

  Synopsis    [Updates only affected loads and forward timing in a trial.]

  Description [Fanout sums retain the full evaluator's order. Integer logic
  area is exact; cached modeled overhead is summed in the full evaluator's
  order. Only the root and its optional child gain new edges.]

  SideEffects []

  SeeAlso     [Scm_WinMeasure]

***********************************************************************/
static int Scm_WinDeltaMeasure( Scm_WinMan_t * p, void * Model, Scm_WinDelta_t * d,
    Scm_WinObj_t * BaseObjs, Scm_WinState_t * BaseState, Scm_WinMetric_t * BaseMetric, Scm_WinState_t * State,
    int Root, int Slot, double Threshold, Scm_WinMetric_t * Metric )
{
    int i, k, t, w, Id, Edge, Fan, Extra[2] = { Root, Slot };
    memset(Metric, 0, sizeof(*Metric));
    Vec_IntForEachEntry(d->Loads, Id, i) d->DirtyLoad[Id] = 0;
    Vec_IntForEachEntry(d->Times, Id, i)
        { d->DirtyTime[Id] = 0; d->TimeBits[Id >> 6] = 0; }
    Vec_IntClear(d->Times);
    Vec_IntClear(d->Loads);
    d->TimeMin = INT_MAX; d->TimeMax = -1;
    Vec_IntForEachEntry(d->Changed, Id, i)
    {
        Scm_WinObj_t * Old = BaseObjs+Id, * Obj = p->Objs+Id;
        if ( Obj->Refs < 0 ) return 0;
        Scm_WinDeltaTime(d, Id);
        if ( !!Old->Refs == !!Obj->Refs && Old->Gate == Obj->Gate && Old->nFans == Obj->nFans &&
             !memcmp(Old->Fans, Obj->Fans, sizeof(int)*Obj->nFans) ) continue;
        if ( Old->Refs ) for ( k = 0; k < Old->nFans; k++ ) Scm_WinDeltaLoad(d, Old->Fans[k]);
        if ( Obj->Refs ) for ( k = 0; k < Obj->nFans; k++ )
        {
            if ( Obj->Fans[k] < 0 || Obj->Fans[k] >= Id ) return 0;
            Scm_WinDeltaLoad(d, Obj->Fans[k]);
        }
        if ( !Obj->Refs ) memset(State+Id, 0, sizeof(*State));
    }
    Vec_IntForEachEntry(d->Loads, Id, i)
    {
        if ( BaseObjs[Id].Refs && BaseObjs[Id].Gate == SCM_WIN_ALIAS ) Scm_WinDeltaLoad(d, BaseObjs[Id].Fans[0]);
        if ( p->Objs[Id].Refs && p->Objs[Id].Gate == SCM_WIN_ALIAS ) Scm_WinDeltaLoad(d, p->Objs[Id].Fans[0]);
    }
    Vec_IntSort(d->Loads, 1);
    Vec_IntForEachEntry(d->Loads, Id, w)
    {
        Scm_RfPair_t Load = {{0, 0}};
        Vec_IntClear(d->Fans);
        for ( i = d->Starts[Id]; i < d->Starts[Id+1]; i++ )
        {
            Edge = d->Edges[i]; Fan = Edge >> 3;
            if ( Fan != Root && Fan != Slot && p->Objs[Fan].Refs ) Vec_IntPush(d->Fans, Edge);
        }
        for ( t = 0; t < 2; t++ ) if ( Extra[t] )
            for ( k = 0; k < p->Objs[Extra[t]].nFans; k++ )
                if ( p->Objs[Extra[t]].Fans[k] == Id ) Vec_IntPush(d->Fans, 8*Extra[t]+k);
        Vec_IntSort(d->Fans, 0);
        Vec_IntForEachEntry(d->Fans, Edge, i) if ( p->Objs[Edge >> 3].Gate >= 0 )
            for ( t = 0; t < 2; t++ ) Load.Value[t] += d->Caps[6*p->Objs[Edge >> 3].Gate+(Edge & 7)].Value[t];
        Vec_IntForEachEntryReverse(d->Fans, Edge, i) if ( p->Objs[Edge >> 3].Gate == SCM_WIN_ALIAS )
            for ( t = 0; t < 2; t++ ) Load.Value[t] += State[Edge >> 3].Load.Value[t];
        State[Id].Load = Load;
        if ( memcmp(&Load, &BaseState[Id].Load, sizeof(Load)) ) Scm_WinDeltaTime(d, Id);
    }
    for ( w = d->TimeMin; w <= d->TimeMax; w++ ) while ( d->TimeBits[w] )
    {
        Scm_WinObj_t * Obj;
        Scm_RfPair_t Arrivals[6], Slews[6];
        Id = 64*w + Abc_Tt6FirstBit(d->TimeBits[w]);
        d->TimeBits[w] &= d->TimeBits[w]-1;
        if ( Id < 2 || !p->Objs[Id].Refs || p->Objs[Id].Gate == SCM_WIN_CI ) continue;
        Obj = p->Objs+Id;
        if ( Obj->Gate == SCM_WIN_ALIAS )
        {
            State[Id].Arrival = State[Obj->Fans[0]].Arrival;
            State[Id].Slew = State[Obj->Fans[0]].Slew;
            State[Id].Cost = 0;
        }
        else
        {
            if ( Obj->nFans != (int)p->Cells[Obj->Gate].nFanins ) return 0;
            for ( k = 0; k < Obj->nFans; k++ )
            {
                Arrivals[k] = State[Obj->Fans[k]].Arrival;
                Slews[k] = State[Obj->Fans[k]].Slew;
            }
            if ( !Scm_WinModelCell(Model, Id, Obj->Gate, State[Id].Load, Arrivals, Slews, &State[Id].Arrival, &State[Id].Slew) ) return 0;
            if ( BaseObjs[Id].Refs && Obj->Gate == BaseObjs[Id].Gate &&
                 !memcmp(&State[Id].Load, &BaseState[Id].Load, sizeof(Scm_RfPair_t)) ) State[Id].Cost = BaseState[Id].Cost;
            else
                State[Id].Cost = Scm_WinModelCost(Model, Obj->Gate, Abc_MaxFloat(State[Id].Load.Value[0], State[Id].Load.Value[1]));
        }
        if ( !memcmp(&State[Id].Arrival, &BaseState[Id].Arrival, sizeof(Scm_RfPair_t)) &&
             !memcmp(&State[Id].Slew, &BaseState[Id].Slew, sizeof(Scm_RfPair_t)) ) continue;
        for ( i = d->Starts[Id]; i < d->Starts[Id+1]; i++ )
        {
            Fan = d->Edges[i] >> 3;
            if ( Fan != Root && Fan != Slot && p->Objs[Fan].Refs ) Scm_WinDeltaTime(d, Fan);
        }
        for ( t = 0; t < 2; t++ ) if ( Extra[t] )
            for ( k = 0; k < p->Objs[Extra[t]].nFans; k++ )
                if ( p->Objs[Extra[t]].Fans[k] == Id ) Scm_WinDeltaTime(d, Extra[t]);
    }
    Metric->Area = BaseMetric->Area;
    Vec_IntForEachEntry(d->Times, Id, i) if ( Id >= 2 )
    {
        if ( p->Objs[Id].Refs && p->Objs[Id].Gate >= 0 ) Metric->Area += Scm_WinArea(p, Id);
        if ( BaseObjs[Id].Refs && BaseObjs[Id].Gate >= 0 ) Metric->Area -= p->Cells[BaseObjs[Id].Gate].AreaW;
    }
    Vec_IntForEachEntry(p->Outputs, Id, i) for ( t = 0; t < 2; t++ )
    {
        double Arrival = State[Id].Arrival.Value[t];
        if ( Metric->Electrical < Arrival ) Metric->Electrical = Arrival;
        Metric->Pressure += fmax(0, Arrival-Threshold);
    }
    // Stable ordering preserves the full evaluator's strict area tie breaks.
    for ( i = 2; i < p->nObjs; i++ )
        if ( p->Objs[i].Refs && p->Objs[i].Gate >= 0 ) Metric->EstimatedArea += State[i].Cost;
    Metric->EstimatedArea += (double)Metric->Area/SCL_NUM;
    return isfinite(Metric->EstimatedArea) && isfinite(Metric->Pressure);
}

/**Function*************************************************************

  Synopsis    [Checks loads and references, reusing unchanged cell evaluations.]

  Description [Optional baseline arrays describe the unmodified cover. Loads
  and area retain their original summation order. Pressure uses the round's
  fixed threshold, not the trial's delay.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_WinMeasure( Scm_WinMan_t * p, void * Model, Scm_WinState_t * State,
    int * Refs, double Threshold, Scm_WinMetric_t * Metric,
    Scm_WinObj_t * BaseObjs, Scm_WinState_t * BaseState )
{
    int i, k, t, Id, fReuse;
    memset(State, 0, sizeof(Scm_WinState_t)*p->nObjs);
    memset(Refs, 0, sizeof(int)*p->nObjs);
    memset(Metric, 0, sizeof(*Metric));
    Vec_IntForEachEntry(p->Outputs, Id, i) Refs[Id]++;
    for ( i = p->nObjs-1; i >= 2; i-- ) if ( Refs[i] )
        for ( k = 0; k < p->Objs[i].nFans; k++ )
        {
            Id = p->Objs[i].Fans[k];
            if ( Id < 0 || Id >= i ) return 0;
            Refs[Id]++;
        }
    for ( i = 0; i < p->nObjs; i++ )
        if ( Refs[i] != p->Objs[i].Refs ) return 0;
    for ( i = 2; i < p->nObjs; i++ ) if ( Refs[i] && p->Objs[i].Gate >= 0 )
    {
        Scm_WinObj_t * Obj = p->Objs+i;
        Metric->Area += Scm_WinArea(p, i);
        if ( Obj->nFans != (int)p->Cells[Obj->Gate].nFanins ) return 0;
        for ( k = 0; k < Obj->nFans; k++ )
        {
            Scm_RfPair_t Cap = Scm_WinModelCap(Model, Obj->Gate, k);
            for ( t = 0; t < 2; t++ ) State[Obj->Fans[k]].Load.Value[t] += Cap.Value[t];
        }
    }
    // Aliases are wires, not extra cells: transfer all of their sink load.
    for ( i = p->nObjs-1; i >= 2; i-- ) if ( Refs[i] && p->Objs[i].Gate == SCM_WIN_ALIAS )
        for ( t = 0; t < 2; t++ ) State[p->Objs[i].Fans[0]].Load.Value[t] += State[i].Load.Value[t];
    for ( i = 2; i < p->nObjs; i++ ) if ( Refs[i] && p->Objs[i].Gate != SCM_WIN_CI )
    {
        Scm_WinObj_t * Obj = p->Objs+i;
        Scm_RfPair_t Arrivals[6], Slews[6];
        if ( Obj->Gate == SCM_WIN_ALIAS )
        {
            State[i].Arrival = State[Obj->Fans[0]].Arrival;
            State[i].Slew = State[Obj->Fans[0]].Slew;
            continue;
        }
        fReuse = BaseState && BaseObjs[i].Refs && Obj->Gate == BaseObjs[i].Gate &&
            Obj->nFans == BaseObjs[i].nFans &&
            !memcmp(Obj->Fans, BaseObjs[i].Fans, sizeof(int)*Obj->nFans) &&
            !memcmp(&State[i].Load, &BaseState[i].Load, sizeof(Scm_RfPair_t));
        for ( k = 0; k < Obj->nFans; k++ )
        {
            Arrivals[k] = State[Obj->Fans[k]].Arrival;
            Slews[k] = State[Obj->Fans[k]].Slew;
            if ( fReuse && (memcmp(Arrivals+k, &BaseState[Obj->Fans[k]].Arrival, sizeof(Scm_RfPair_t)) ||
                            memcmp(Slews+k, &BaseState[Obj->Fans[k]].Slew, sizeof(Scm_RfPair_t))) ) fReuse = 0;
        }
        if ( fReuse )
        {
            State[i].Arrival = BaseState[i].Arrival;
            State[i].Slew = BaseState[i].Slew;
            State[i].Cost = BaseState[i].Cost;
        }
        else
        {
            if ( !Scm_WinModelCell(Model, i, Obj->Gate, State[i].Load, Arrivals, Slews, &State[i].Arrival, &State[i].Slew) ) return 0;
            State[i].Cost = Scm_WinModelCost(Model, Obj->Gate,
                Abc_MaxFloat(State[i].Load.Value[0], State[i].Load.Value[1]));
        }
        Metric->EstimatedArea += State[i].Cost;
    }
    Vec_IntForEachEntry(p->Outputs, Id, i)
    {
        for ( k = 0; k < 2; k++ )
        {
            double Arrival = State[Id].Arrival.Value[k];
            if ( Metric->Electrical < Arrival ) Metric->Electrical = Arrival;
            Metric->Pressure += fmax(0, Arrival-Threshold);
        }
    }
    Metric->EstimatedArea += (double)Metric->Area/SCL_NUM;
    return isfinite(Metric->EstimatedArea) && isfinite(Metric->Pressure);
}

/**Function*************************************************************

  Synopsis    [Computes transition-specific slack at the current electrical loads.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_WinRequired( Scm_WinMan_t * p, void * Model, Scm_WinState_t * State, float Delay )
{
    int i, k, t, Id;
    for ( i = 0; i < p->nObjs; i++ ) State[i].Required.Value[0] = State[i].Required.Value[1] = FLT_MAX;
    Vec_IntForEachEntry(p->Outputs, Id, i) State[Id].Required.Value[0] = State[Id].Required.Value[1] = Delay;
    for ( i = p->nObjs-1; i >= 2; i-- ) if ( p->Objs[i].Refs )
        for ( k = 0; k < p->Objs[i].nFans; k++ )
        {
            Id = p->Objs[i].Fans[k];
            if ( p->Objs[i].Gate == SCM_WIN_ALIAS )
            {
                for ( t = 0; t < 2; t++ ) State[Id].Required.Value[t] =
                    Abc_MinFloat(State[Id].Required.Value[t], State[i].Required.Value[t]);
            }
            else if ( !Scm_WinModelRequired(Model, i, p->Objs[i].Gate, k, State[i].Load,
                State[Id].Slew, State[i].Required, &State[Id].Required) ) return 0;
        }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Orders roots by slack, area and topological ID.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_WinRootCompare( const void * pA, const void * pB )
{
    const Scm_WinRoot_t * A = (const Scm_WinRoot_t *)pA, * B = (const Scm_WinRoot_t *)pB;
    if ( A->Path != B->Path ) return A->Path > B->Path ? -1 : 1;
    if ( A->Area != B->Area ) return A->Area > B->Area ? -1 : 1;
    return (A->Id > B->Id) - (A->Id < B->Id);
}

/**Function*************************************************************

  Synopsis    [Ranks electrical timing and pressure before modeled area.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_WinBetter( Scm_WinMetric_t * A, Scm_WinMetric_t * B, int fArea )
{
    if ( fArea && A->EstimatedArea != B->EstimatedArea ) return A->EstimatedArea < B->EstimatedArea;
    if ( fabs(A->Electrical-B->Electrical) > 1e-4 ) return A->Electrical < B->Electrical;
    if ( fabs(A->Pressure-B->Pressure) > 1e-4 ) return A->Pressure < B->Pressure;
    return A->EstimatedArea < B->EstimatedArea;
}

/**Function*************************************************************

  Synopsis    [Independent commit measurements allow only accumulated floating-point
  roundoff.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_WinAreaEqual( int nObjs, double A, double B )
{
    return fabs(A-B) <= 16*DBL_EPSILON*nObjs*(fabs(A)+fabs(B)+1);
}

/**Function*************************************************************

  Synopsis    [Evaluates a trial without changing the live cover.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_WinTrial( Scm_WinMan_t * p, Scm_WinObj_t * Backup, Scm_WinDelta_t * Delta, int Id, Scm_WinPlan_t * Plan,
    void * Model, Scm_WinState_t * BaseState, Scm_WinMetric_t * BaseMetric, Scm_WinState_t * State, int * Refs, double Threshold,
    Scm_WinMetric_t * Metric )
{
    Scm_WinObj_t * Original = p->Objs;
    int Ok, i, ObjId;
    p->Objs = Backup;
    Vec_IntClear(Delta->Changed);
    Scm_WinApply(p, Id, Plan, Delta->Changed);
    Ok = BaseState ? Scm_WinDeltaMeasure(p, Model, Delta, Original, BaseState, BaseMetric, State, Id, Plan->Slot, Threshold, Metric) :
        Scm_WinMeasure(p, Model, State, Refs, Threshold, Metric, NULL, NULL);
    Vec_IntForEachEntry(Delta->Changed, ObjId, i) Backup[ObjId] = Original[ObjId];
    if ( BaseState )
    {
        Vec_IntForEachEntry(Delta->Times, ObjId, i)
        {
            State[ObjId] = BaseState[ObjId];
            State[ObjId].Required.Value[0] = State[ObjId].Required.Value[1] = 0;
        }
        Vec_IntForEachEntry(Delta->Loads, ObjId, i) State[ObjId].Load = BaseState[ObjId].Load;
    }
    p->Objs = Original;
    return Ok;
}

/**Function*************************************************************

  Synopsis    [Measures a checkpoint and keeps it under the window guard.]

  Description [The search continues from its current cover, not the
  checkpoint.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_WinCheckpoint( Scm_WinMan_t * p, Scm_WinMetric_t * Current,
    Scm_WinMetric_t * Initial, Scm_WinMetric_t * Kept, Gia_Man_t ** ppKept, float DelayTarget )
{
    Gia_Man_t * Check = Scm_WinExport(p);
    Scm_WinMetric_t Trial = *Current;
    int Accept;
    if ( !Scm_WinModelLookahead(Check, &Trial.RealArea, &Trial.RealDelay) )
    {
        Abc_Print(0, "SCMap: optional window checkpoint could not be measured.\n");
        Gia_ManStop(Check);
        return;
    }
    Accept = DelayTarget > 0 ? Scm_QorTargetBetter(Trial.RealArea, Trial.RealDelay, Kept->RealArea, Kept->RealDelay, DelayTarget) :
             Trial.RealArea <= 1.02 * Initial->RealArea && Trial.RealDelay <= Initial->RealDelay &&
             Trial.RealArea * Trial.RealDelay < Kept->RealArea * Kept->RealDelay;
    if ( !Accept ) Gia_ManStop(Check);
    else
    {
        if ( *ppKept ) Gia_ManStop(*ppKept);
        *ppKept = Check; *Kept = Trial;
    }
}

/**Function*************************************************************

  Synopsis    [Searches windows by electrical pressure and keeps the best checkpoint.]

  Description [Timing may spend 2% mapped area; recovery holds the achieved
  delay. A checkpoint measured after buffering is kept with at most 2%
  measured area growth, nonincreasing delay and a better area-delay
  product, or by target rank under a delay target. Two rounds of timing and
  recovery phases share 32768 trials and SCM_WIN_WORK evenly.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Scm_ManWindowSearch( Gia_Man_t * Gia, Scm_Qor_t * pQor, float DelayTarget, int fVerbose )
{
    Scm_WinMan_t * p = NULL;
    Scm_WinObj_t * Backup = NULL;
    Scm_WinState_t * State = NULL, * TrialState = NULL;
    Scm_WinRoot_t * Roots = NULL;
    Scm_WinDelta_t * Delta = NULL;
    int * Refs = NULL;
    void * Model = NULL;
    Gia_Man_t * Result = NULL, * Checkpoint = NULL;
    Scm_WinMetric_t Initial, Current, Trial, BestMetric, KeptMetric;
    Scm_WinList_t List = {0};
    int nRounds = 2, nBudget = 32768, nTrials = 0;
    int Round, Phase, Limit, Id, i, k, t, Count, Best, nHits = 0, Before;
    int Kept = 0, LastCheck = 0, NextGrowth = 1, nLive;
    word Growth = 0, Work = 0, WorkLimit;
    double Threshold = 0, Bound, AreaLimit;
    abctime Start = Abc_Clock();
    if ( Gia == NULL || !Gia->vCellMapping || Gia->pManTime || Gia_ManBufNum(Gia) ||
         Gia->vInArrs || Gia->vOutReqs || Gia->vCiArrs || Gia->vCoReqs || Scl_ConIsRunning() ) return NULL;
    if ( !Gia_ManCiNum(Gia) || !Gia_ManAndNum(Gia) ) return Gia;
    Model = Scm_WinModelStart();
    if ( Model == NULL ) goto done;
    p = Scm_WinImport(Gia);
    if ( p == NULL ) goto done;
    Scm_WinModelNodes(Model, p->nObjs);   // optional: without it, every node uses its cell's responses
    Backup = ABC_ALLOC(Scm_WinObj_t, p->nObjs);
    State = ABC_ALLOC(Scm_WinState_t, p->nObjs);
    TrialState = ABC_ALLOC(Scm_WinState_t, p->nObjs);
    Refs = ABC_ALLOC(int, p->nObjs);
    Roots = ABC_ALLOC(Scm_WinRoot_t, p->nObjs);
    List.Plans = ABC_ALLOC(Scm_WinPlan_t, 128);
    if ( !Scm_WinMeasure(p, Model, State, Refs, Threshold, &Initial, NULL, NULL) ) goto done;
    memcpy(Backup, p->Objs, sizeof(Scm_WinObj_t)*p->nObjs);
    memcpy(TrialState, State, sizeof(Scm_WinState_t)*p->nObjs);
    Delta = Scm_WinDeltaStart(p, Model);
    if ( Delta == NULL ) goto done;
    if ( pQor && pQor->fValid ) { Initial.RealArea = pQor->Area; Initial.RealDelay = pQor->Delay; }
    else if ( !Scm_WinModelLookahead(Gia, &Initial.RealArea, &Initial.RealDelay) ) goto done;
    Current = KeptMetric = Initial;
    nLive = 0;
    for ( Id = 2; Id < p->nObjs; Id++ )
        nLive += p->Objs[Id].Refs && p->Objs[Id].Gate >= 0;
    AreaLimit = 1.02 * Initial.Area;
    for ( Round = 0; Round < nRounds && nTrials < nBudget && Work < SCM_WIN_WORK; Round++ )
    {
        Before = nHits;
        Threshold = 0.8 * Current.Electrical;
        Current.Pressure = 0;
        Vec_IntForEachEntry(p->Outputs, Id, i)
            for ( t = 0; t < 2; t++ ) Current.Pressure += fmax(0, State[Id].Arrival.Value[t]-Threshold);
        for ( Phase = 0; Phase < 2 && nTrials < nBudget && Work < SCM_WIN_WORK; Phase++ )
        {
            int fArea = Phase || (DelayTarget > 0 && KeptMetric.RealDelay <= DelayTarget);
            Bound = Current.Electrical;
            // Calibrate only the model screen; measured timing decides feasibility.
            if ( DelayTarget > 0 && Initial.RealDelay > 0 )
                Bound = fmax(Bound, Initial.Electrical * DelayTarget / Initial.RealDelay);
            Limit = nBudget*(2*Round+Phase+1)/(2*nRounds);
            WorkLimit = SCM_WIN_WORK*(2*Round+Phase+1)/(2*nRounds);
            List.Limit = Phase ? 32 : 128;
            if ( !fArea && !Scm_WinRequired(p, Model, State, (float)Current.Electrical) ) goto done;
            Count = 0;
            for ( Id = 2; Id < p->nObjs; Id++ ) if ( p->Objs[Id].Refs && p->Objs[Id].Gate >= 0 )
            {
                Roots[Count].Id = Id;
                Roots[Count].Path = fArea ? 0 : -fmin(
                    State[Id].Required.Value[0]-State[Id].Arrival.Value[0],
                    State[Id].Required.Value[1]-State[Id].Arrival.Value[1]);
                Roots[Count++].Area = Scm_WinArea(p, Id);
            }
            qsort(Roots, Count, sizeof(Scm_WinRoot_t), Scm_WinRootCompare);
            for ( i = 0; i < Count && nTrials < Limit && Work < WorkLimit; i++ )
            {
                word Extra = fArea || AreaLimit <= Current.Area ? 0 : (word)(AreaLimit-Current.Area);
                Id = Roots[i].Id;
                if ( !p->Objs[Id].Refs || p->Objs[Id].Gate < 0 ) continue;
                List.Model = !fArea ? Model : NULL;
                List.Root = Id; List.State = State;
                Scm_WinEnumerate(p, Id, &List, Extra, !fArea);
                Best = -1; BestMetric = Current;
                for ( k = 0; k < List.Count && nTrials < Limit && Work < WorkLimit; k++ )
                {
                    if ( !Scm_WinTrial(p, Backup, Delta, Id, List.Plans+k, Model, State, &Current, TrialState, Refs, Threshold, &Trial) ||
                         (long long)Trial.Area + List.Plans[k].Gain != (long long)Current.Area ) goto done;
                    nTrials++;
                    // a trial re-times the cells its edit reaches, then sums the modeled cost of every live cell
                    Work += Vec_IntSize(Delta->Times) + (nLive >> 6);
                    if ( !fArea )
                    {
                        if ( Trial.EstimatedArea <= 1.02 * Initial.EstimatedArea &&
                             Trial.Electrical <= Current.Electrical + 1e-4 &&
                             (Trial.Electrical < Current.Electrical-1e-4 || Trial.Pressure < Current.Pressure-1e-4) &&
                             Scm_WinBetter(&Trial, &BestMetric, 0) ) { Best = k; BestMetric = Trial; }
                    }
                    else if ( Trial.Electrical <= Bound + 1e-4 && Trial.Area < Current.Area &&
                              Trial.EstimatedArea < BestMetric.EstimatedArea ) { Best = k; BestMetric = Trial; }
                }
                if ( Best < 0 ) continue;
                Scm_WinApply(p, Id, List.Plans+Best, NULL);
                Work += nLive;   // a commit re-measures the whole cover, its required times and fanouts
                nHits++;
                if ( !Scm_WinMeasure(p, Model, State, Refs, Threshold, &Current, Backup, TrialState) ||
                     Current.Area != BestMetric.Area || Current.Electrical != BestMetric.Electrical ||
                     !Scm_WinAreaEqual(p->nObjs, Current.EstimatedArea, BestMetric.EstimatedArea) || Current.Pressure != BestMetric.Pressure ) goto done;
                Current.RealArea = BestMetric.RealArea; Current.RealDelay = BestMetric.RealDelay;
                memcpy(Backup, p->Objs, sizeof(Scm_WinObj_t)*p->nObjs);
                memcpy(TrialState, State, sizeof(Scm_WinState_t)*p->nObjs);
                Scm_WinDeltaBuild(p, Delta);
                // Forward measurement clears Required. The next shortlist
                // needs bounds for the newly committed cover and its loads.
                if ( !fArea && !Scm_WinRequired(p, Model, State, (float)Current.Electrical) ) goto done;
                if ( !fArea && List.Plans[Best].Gain < 0 ) Growth += (word)-List.Plans[Best].Gain;
                if ( DelayTarget > 0 && fArea ) Growth += (word)List.Plans[Best].Gain;
                if ( Initial.Area > 0 && (DelayTarget > 0 || NextGrowth <= 4) && Growth >= 0.005 * NextGrowth * Initial.Area )
                {
                    Scm_WinCheckpoint(p, &Current, &Initial, &KeptMetric, &Checkpoint, DelayTarget);
                    LastCheck = nHits;
                    do { NextGrowth++; } while ( (DelayTarget > 0 || NextGrowth <= 4) && Growth >= 0.005 * NextGrowth * Initial.Area );
                }
            }
            if ( nHits != LastCheck )
            {
                Scm_WinCheckpoint(p, &Current, &Initial, &KeptMetric, &Checkpoint, DelayTarget);
                LastCheck = nHits;
            }
        }
        if ( nHits == Before ) break;
    }
    Kept = Checkpoint != NULL; Result = Checkpoint ? Checkpoint : Gia;
    Checkpoint = NULL; Current = KeptMetric;
    if ( pQor )
    {
        pQor->Area = Kept ? Current.RealArea : Initial.RealArea;
        pQor->Delay = Kept ? Current.RealDelay : Initial.RealDelay;
        pQor->fValid = 1;
    }
    if ( fVerbose )
        Abc_Print(1, "SCMAP_WINDOWS trials=%d edits=%d kept=%d area=%.9g old_area=%.9g delay=%.9g old_delay=%.9g time=%.3f\n",
            nTrials, nHits, Kept, Current.RealArea, Initial.RealArea, Current.RealDelay, Initial.RealDelay,
            (double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
done:
    if ( Result == NULL ) Abc_Print(0, "SCMap: window topology, area, or timing check failed.\n");
    if ( Checkpoint ) Gia_ManStop(Checkpoint);
    ABC_FREE(Backup); ABC_FREE(State); ABC_FREE(TrialState); ABC_FREE(Refs); ABC_FREE(Roots); ABC_FREE(List.Plans);
    Scm_WinDeltaStop(Delta);
    if ( p ) Scm_WinManStop(p);
    Scm_WinModelStop(Model);
    return Result;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
