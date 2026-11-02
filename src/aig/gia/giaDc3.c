/**CFile****************************************************************

  FileName    [giaDc3.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Fast orchestration of balancing, rewriting, refactoring, and resubstitution.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaDc3.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "giaEdit.h"
#include "misc/util/utilTruth.h"
#include "opt/drw/drwInt.h"
#include "giaDrf.h"
#include <limits.h>

ABC_NAMESPACE_IMPL_START

// Rewriting and refactoring share one mutable graph, maintained structural
// hash, and required levels across passes. Recipes and neighborhood colors
// guide effort only; every replacement has its truth, gain and level checked.

enum
{
    DC3_CUT_LIMIT = 128,
    DC3_LIB_LIMIT = 256,
    DC3_MFFC_LIMIT = 32
};
enum
{
    DC3_FAILURE_LIMIT = 2,
    DC3_PASSES = 5,
    DC3_NEIGHBOR_BINS = 262144,
    DC3_RECIPE_LIMIT = 16384,
    DC3_RECIPES_PER_KEY = 4,
    DC3_BALANCE_LEAVES = 12
};
typedef struct Dcr_Cut_t_ Dcr_Cut_t;
struct Dcr_Cut_t_
{
    int Leaves[4];
    int nLeaves;
    int Saved;
    unsigned Truth;
    int fFullSupport;
};

typedef struct Dcr_Cuts_t_
{
    Dcr_Cut_t Cuts[DC3_CUT_LIMIT];
    unsigned Hash[DC3_CUT_LIMIT];
    int Links[DC3_CUT_LIMIT];
    int Table[64];
    int nCuts;
    int BestSaved;
    int fFull;
} Dcr_Cuts_t;

typedef struct
{
    word Paths[4];
    int Next, nLeaves, Gain, LibRoot;
    unsigned Truth;
} Dc3_Recipe_t;
typedef struct
{
    unsigned Hash;
    int Recipe;
    unsigned char nRecipes, Failed, Epoch;
} Dc3_Neighbor_t;
typedef struct Dc3_Man_t_ Dc3_Man_t;
struct Dc3_Man_t_
{
    Drf_Man_t F;
    unsigned * pNeighborhood;
    int nNeighborBins;
    Dc3_Neighbor_t * pNeighbors;
    Dc3_Recipe_t * pRecipes;
    int nSkipped, nRecipes, nRecipeHits;
    int fZeros, fZeroCap, fChoiceZeros;
    int PlanLit, PlanLevel, PlanRoot, PlanPhase, fFullMark;
    unsigned char LibOrder[222][DC3_LIB_LIMIT];
    unsigned short LibEnds[222][DC3_LIB_LIMIT];
    int LibLits[DC3_LIB_LIMIT], LibLevels[DC3_LIB_LIMIT], LibSeen[DC3_LIB_LIMIT];
    word LibCosts[DC3_LIB_LIMIT];
    const Drw_LibClass_t * pClass;
    int nLimited, nRewritten, nMerged;
};

static inline int Dcr_Mffc( Dc3_Man_t * p, int Root, Dcr_Cut_t * pCut, int fMark )
{
    return Gie_Mffc( &p->F.M, Root, pCut->Leaves, pCut->nLeaves, fMark );
}

/**Function*************************************************************

  Synopsis    [Evaluates a cut cone using stamped 16-bit truth tables.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static unsigned Dcr_Truth_rec( Dc3_Man_t * p, int Id )
{
    unsigned a, b;
    int Fan0, Fan1;
    if ( Id == 0 ) return 0;
    if ( p->F.M.pObjs[Id].TruthMark == p->F.M.TruthMark ) return p->F.M.pObjs[Id].Truth;
    assert( p->F.M.pObjs[Id].Type == GIE_AND );
    Fan0 = p->F.M.pObjs[Id].Fan[0];
    Fan1 = p->F.M.pObjs[Id].Fan[1];
    a = Dcr_Truth_rec( p, Fan0 >> 1 ) ^ ( ( Fan0 & 1 ) ? 65535u : 0 );
    b = Dcr_Truth_rec( p, Fan1 >> 1 ) ^ ( ( Fan1 & 1 ) ? 65535u : 0 );
    p->F.M.pObjs[Id].TruthMark = p->F.M.TruthMark;
    return p->F.M.pObjs[Id].Truth = (unsigned short) ( a & b );
}

/**Function*************************************************************

  Synopsis    [Assigns cut variables and evaluates the root truth table.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static unsigned Dcr_Truth( Dc3_Man_t * p, int Id, Dcr_Cut_t * pCut )
{
    static const unsigned short Truths[4] = { 0xAAAA, 0xCCCC, 0xF0F0, 0xFF00 };
    int i;
    Gie_TruthNext( &p->F.M );
    for ( i = 0; i < pCut->nLeaves; i++ )
    {
        p->F.M.pObjs[pCut->Leaves[i]].TruthMark = p->F.M.TruthMark;
        p->F.M.pObjs[pCut->Leaves[i]].Truth = Truths[i];
    }
    return Dcr_Truth_rec( p, Id );
}

/**Function*************************************************************

  Synopsis    [Removes functionally unused cut inputs.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Dcr_CutMinimize( Dcr_Cut_t * pCut )
{
    static const unsigned Masks[4] = { 0x5555, 0x3333, 0x0F0F, 0x00FF };
    int i, j;
    unsigned t = pCut->Truth;
    for ( i = 0; i < pCut->nLeaves; i++ )
    {
        if ( ( ( t >> ( 1 << i ) ) ^ t ) & Masks[i] ) continue;
        for ( j = i; j < pCut->nLeaves - 1; j++ )
        {
            if ( j == 0 )
                t = ( t & 0x9999u ) | ( ( t & 0x2222u ) << 1 ) | ( ( t & 0x4444u ) >> 1 );
            else if ( j == 1 )
                t = ( t & 0xC3C3u ) | ( ( t & 0x0C0Cu ) << 2 ) | ( ( t & 0x3030u ) >> 2 );
            else
                t = ( t & 0xF00Fu ) | ( ( t & 0x00F0u ) << 4 ) | ( ( t & 0x0F00u ) >> 4 );
            pCut->Leaves[j] = pCut->Leaves[j + 1];
        }
        pCut->nLeaves--;
        i--;
    }
    pCut->Truth = t;
}

/**Function*************************************************************

  Synopsis    [Finds a small complete MFFC and its boundary truth table.]

  Description [Local edge counters discover removable nodes without changing references.
  The discovery queue is reverse topological and doubles as a truth program.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Dcr_FullCut( Dc3_Man_t * p, int Id, Dcr_Cut_t * pCut )
{
    static const unsigned short Truths[4] = { 0xAAAA, 0xCCCC, 0xF0F0, 0xFF00 };
    int *pNodes = Vec_IntArray( p->F.M.vStack ), *pLeaves = pNodes + DC3_MFFC_LIMIT;
    int i, k, j, nNodes = 1, nCandidates = 0, nLeaves = 0, nCis = 0, Var;
    assert( Vec_IntCap( p->F.M.vStack ) >= 3 * DC3_MFFC_LIMIT );
    Gie_MarkNext( &p->F.M );
    Gie_TruthNext( &p->F.M );
    pNodes[0] = Id;
    p->F.M.pObjs[Id].Mark = p->F.M.Mark;
    // Local edge counts determine the removable region without changing
    // live references. A fanin enters the queue only after all its users.
    for ( i = 0; i < nNodes; i++ )
        for ( k = 0; k < 2; k++ )
        {
            Gie_Obj_t * pFan;
            Var = p->F.M.pObjs[pNodes[i]].Fan[k] >> 1;
            if ( !Var ) continue;
            pFan = p->F.M.pObjs + Var;
            if ( pFan->TruthMark != p->F.M.TruthMark )
            {
                pFan->TruthMark = p->F.M.TruthMark;
                pFan->Truth = 0;
                // CIs cannot leave the boundary during further MFFC expansion.
                if ( pFan->Type == GIE_CI && ++nCis > 4 ) return 0;
                pLeaves[nCandidates++] = Var;
                nLeaves++;
            }
            if ( pFan->Type != GIE_AND || ++pFan->Truth != pFan->Refs ) continue;
            if ( nNodes == DC3_MFFC_LIMIT ) return 0;
            pFan->Mark = p->F.M.Mark;
            pNodes[nNodes++] = Var;
            nLeaves--;
        }
    if ( nLeaves > 4 ) return 0;
    pCut->Saved = nNodes;
    pCut->nLeaves = 0;
    for ( i = 0; i < nCandidates; i++ )
        if ( p->F.M.pObjs[pLeaves[i]].Mark != p->F.M.Mark ) pCut->Leaves[pCut->nLeaves++] = pLeaves[i];
    assert( pCut->nLeaves == nLeaves );
    for ( i = 1; i < nLeaves; i++ )
        for ( j = i; j > 0 && pCut->Leaves[j] < pCut->Leaves[j - 1]; j-- )
            ABC_SWAP( int, pCut->Leaves[j], pCut->Leaves[j - 1] );
    // The same queue, reversed, is a topological truth-table program.
    p->F.M.pObjs[0].Truth = 0;
    for ( i = 0; i < nLeaves; i++ )
        p->F.M.pObjs[pCut->Leaves[i]].Truth = Truths[i];
    for ( i = nNodes - 1; i >= 0; i-- )
    {
        int Node = pNodes[i], a = p->F.M.pObjs[Node].Fan[0], b = p->F.M.pObjs[Node].Fan[1];
        p->F.M.pObjs[Node].Truth = (unsigned short) ( ( p->F.M.pObjs[a >> 1].Truth ^ ( ( a & 1 ) ? 65535u : 0 ) ) &
                                                      ( p->F.M.pObjs[b >> 1].Truth ^ ( ( b & 1 ) ? 65535u : 0 ) ) );
    }
    pCut->Truth = p->F.M.pObjs[Id].Truth;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Tests immediate overlap when breaking maximum-MFFC ties.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Dcr_LeavesOverlap( Dc3_Man_t * p, int a, int b )
{
    int FanA0 = -1, FanA1 = -1, FanB0, FanB1;
    if ( p->F.M.pObjs[a].Type == GIE_AND )
    {
        FanA0 = p->F.M.pObjs[a].Fan[0] >> 1;
        FanA1 = p->F.M.pObjs[a].Fan[1] >> 1;
        if ( FanA0 == b || FanA1 == b ) return 1;
    }
    if ( p->F.M.pObjs[b].Type == GIE_AND )
    {
        FanB0 = p->F.M.pObjs[b].Fan[0] >> 1;
        FanB1 = p->F.M.pObjs[b].Fan[1] >> 1;
        if ( FanB0 == a || FanB1 == a ) return 1;
        if ( p->F.M.pObjs[a].Type == GIE_AND &&
             ( FanA0 == FanB0 || FanA0 == FanB1 || FanA1 == FanB0 || FanA1 == FanB1 ) )
            return 1;
    }
    return 0;
}

static inline unsigned Dcr_CutHash( int Id )
{
    unsigned h = (unsigned) Id * 123456791u;
    return h ^ ( h >> 16 );
}

/**Function*************************************************************

  Synopsis    [Enumerates bounded frontier expansions with shared MFFC updates.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Dcr_CutsExplore_rec( Dc3_Man_t * p, Dcr_Cuts_t * pCuts, Dcr_Cut_t * pCut, unsigned Hash )
{
    Dcr_Cut_t New;
    int k, i, j, Var, Fan, n, Id, Added[2], nAdded, Saved;
    pCuts->BestSaved = Abc_MaxInt( pCuts->BestSaved, pCut->Saved );
    for ( k = 0; k < pCut->nLeaves && pCuts->nCuts < DC3_CUT_LIMIT; k++ )
    {
        unsigned NewHash = Hash;
        Var = pCut->Leaves[k];
        if ( p->F.M.pObjs[Var].Type != GIE_AND ) continue;
        for ( i = n = 0; i < pCut->nLeaves; i++ )
            if ( i != k ) New.Leaves[n++] = pCut->Leaves[i];
        NewHash ^= Dcr_CutHash( Var );
        nAdded = 0;
        for ( i = 0; i < 2; i++ )
        {
            Fan = p->F.M.pObjs[Var].Fan[i] >> 1;
            if ( Fan == 0 || p->F.M.pObjs[Fan].Inside ) continue;
            for ( j = 0; j < n; j++ )
                if ( New.Leaves[j] == Fan ) break;
            if ( j < n ) continue;
            if ( n == 4 ) break;
            New.Leaves[n++] = Fan;
            Added[nAdded++] = Fan;
            NewHash ^= Dcr_CutHash( Fan );
        }
        if ( i < 2 ) continue;
        for ( i = 1; i < n; i++ )
            for ( j = i; j > 0 && New.Leaves[j] < New.Leaves[j - 1]; j-- )
                ABC_SWAP( int, New.Leaves[j], New.Leaves[j - 1] );
        New.nLeaves = n;
        for ( i = pCuts->Table[NewHash & 63]; i; i = pCuts->Links[i] )
            if ( pCuts->Hash[i] == NewHash && pCuts->Cuts[i].nLeaves == n &&
                 !memcmp( pCuts->Cuts[i].Leaves, New.Leaves, n * sizeof( int ) ) )
                break;
        if ( i ) continue;
        Id = pCuts->nCuts++;
        pCuts->Links[Id] = pCuts->Table[NewHash & 63];
        pCuts->Table[NewHash & 63] = Id;
        pCuts->Hash[Id] = NewHash;
        Saved = 0;
        if ( !pCuts->fFull )
        {
            for ( i = 0; i < nAdded; i++ )
                if ( p->F.M.pObjs[Added[i]].Type == GIE_AND ) p->F.M.pObjs[Added[i]].Refs++;
            assert( p->F.M.pObjs[Var].Refs > 0 );
            Saved = --p->F.M.pObjs[Var].Refs == 0 ? Gie_Deref( &p->F.M, Var, 0 ) : 0;
        }
        New.Saved = pCut->Saved + Saved;
        New.fFullSupport = pCut->fFullSupport && nAdded == 2;
        pCuts->Cuts[Id] = New;
        p->F.M.pObjs[Var].Inside = 1;
        Dcr_CutsExplore_rec( p, pCuts, pCuts->Cuts + Id, NewHash );
        p->F.M.pObjs[Var].Inside = 0;
        if ( !pCuts->fFull )
        {
            if ( p->F.M.pObjs[Var].Refs++ == 0 ) Gie_Ref( &p->F.M, Var );
            for ( i = 0; i < nAdded; i++ )
                if ( p->F.M.pObjs[Added[i]].Type == GIE_AND ) p->F.M.pObjs[Added[i]].Refs--;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Selects one cut by removable MFFC size.]

  Description [A depth-first frontier walk shares virtual dereferencing
  between adjacent cuts. Truth tables are computed only for maximum-MFFC
  cuts. Library size, leaf count, and reference count break ties.
  Only one cut is resynthesized.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Dcr_SelectCut( Dc3_Man_t * p, int Id, Dcr_Cut_t * pBest )
{
    Dcr_Cuts_t Cuts;
    Dcr_Cut_t * pCut;
    unsigned Hash = 0;
    int i, Fan, fFull, BestSize = INT_MAX, BestRefs = -1;
    p->fFullMark = fFull = Dcr_FullCut( p, Id, pBest );
    if ( fFull )
    {
        static const unsigned Masks[4] = { 0x5555, 0x3333, 0x0F0F, 0x00FF };
        int fExpand = 0, fOverlap = pBest->nLeaves > 3, k, j;
        // A small complete boundary already maximizes the removable MFFC.
        // Keep boundaries of up to two leaves, including sharing-only XORs;
        // also keep any boundary with an improving standalone graph.
        if ( pBest->nLeaves <= 2 || Drw_MinSizes[pBest->Truth] < pBest->Saved )
        {
            Dcr_CutMinimize( pBest );
            return 1;
        }
        for ( i = 0; i < pBest->nLeaves && !fExpand; i++ )
        {
            int Leaf = pBest->Leaves[i];
            if ( p->F.M.pObjs[Leaf].Type != GIE_AND ) continue;
            if ( pBest->nLeaves < 4 )
            {
                fExpand = 1;
                break;
            }
            for ( k = 0; k < 2; k++ )
            {
                int FanId = p->F.M.pObjs[Leaf].Fan[k] >> 1;
                if ( !FanId ) fExpand = 1;
                for ( j = 0; j < pBest->nLeaves; j++ )
                    if ( pBest->Leaves[j] == FanId ) fExpand = 1;
            }
        }
        if ( fExpand && !fOverlap )
            for ( i = 0; i < pBest->nLeaves; i++ )
                for ( j = i + 1; j < pBest->nLeaves; j++ )
                    fOverlap |= Dcr_LeavesOverlap( p, pBest->Leaves[i], pBest->Leaves[j] );
        if ( !fExpand || !fOverlap )
        {
            Dcr_CutMinimize( pBest );
            return 1;
        }
        pBest->fFullSupport = 1;
        for ( i = 0; i < pBest->nLeaves; i++ )
            if ( !( ( ( pBest->Truth >> ( 1 << i ) ) ^ pBest->Truth ) & Masks[i] ) ) pBest->fFullSupport = 0;
    }
    memset( Cuts.Table, 0, sizeof( Cuts.Table ) );
    Cuts.nCuts = 2;
    Cuts.BestSaved = 0;
    Cuts.fFull = fFull;
    pCut = Cuts.Cuts + 1;
    if ( fFull )
        *pCut = *pBest;
    else
    {
        pCut->nLeaves = 0;
        pCut->fFullSupport = 1;
        for ( i = 0; i < 2; i++ )
        {
            Fan = p->F.M.pObjs[Id].Fan[i] >> 1;
            if ( !Fan || ( pCut->nLeaves && Fan == pCut->Leaves[0] ) ) continue;
            pCut->Leaves[pCut->nLeaves++] = Fan;
        }
        if ( pCut->nLeaves == 2 && pCut->Leaves[0] > pCut->Leaves[1] )
            ABC_SWAP( int, pCut->Leaves[0], pCut->Leaves[1] );
    }
    memset( pBest, 0, sizeof( Dcr_Cut_t ) );
    for ( i = 0; i < pCut->nLeaves; i++ )
    {
        Fan = pCut->Leaves[i];
        if ( !fFull && p->F.M.pObjs[Fan].Type == GIE_AND ) p->F.M.pObjs[Fan].Refs++;
        Hash ^= Dcr_CutHash( Fan );
    }
    if ( !fFull ) pCut->Saved = Gie_Deref( &p->F.M, Id, 0 );
    Cuts.Table[Hash & 63] = 1;
    Cuts.Hash[1] = Hash;
    Cuts.Links[1] = 0;
    p->F.M.pObjs[Id].Inside = 1;
    Dcr_CutsExplore_rec( p, &Cuts, pCut, Hash );
    p->F.M.pObjs[Id].Inside = 0;
    if ( !fFull )
    {
        Gie_Ref( &p->F.M, Id );
        for ( i = 0; i < pCut->nLeaves; i++ )
            if ( p->F.M.pObjs[pCut->Leaves[i]].Type == GIE_AND ) p->F.M.pObjs[pCut->Leaves[i]].Refs--;
    }
    for ( i = 1; i < Cuts.nCuts; i++ )
    {
        int Size, j, Refs = 0;
        pCut = Cuts.Cuts + i;
        if ( pCut->Saved != Cuts.BestSaved ) continue;
        for ( j = 0; j < pCut->nLeaves; j++ )
            Refs += p->F.M.pObjs[pCut->Leaves[j]].Refs;
        if ( pCut->fFullSupport &&
             ( pCut->nLeaves - 1 > BestSize ||
               ( pCut->nLeaves - 1 == BestSize &&
                 ( pCut->nLeaves > pBest->nLeaves || ( pCut->nLeaves == pBest->nLeaves && Refs <= BestRefs ) ) ) ) )
            continue;
        if ( !fFull || i != 1 ) pCut->Truth = Dcr_Truth( p, Id, pCut );
        Size = Drw_MinSizes[pCut->Truth];
        if ( Size < BestSize || ( Size == BestSize && ( pCut->nLeaves < pBest->nLeaves ||
                                                        ( pCut->nLeaves == pBest->nLeaves && Refs > BestRefs ) ) ) )
        {
            *pBest = *pCut;
            BestSize = Size;
            BestRefs = Refs;
        }
    }
    p->nLimited += Cuts.nCuts == DC3_CUT_LIMIT;
    i = pBest->nLeaves;
    Dcr_CutMinimize( pBest );
    if ( i != pBest->nLeaves )
    {
        // Keep the removal count and reuse marks tied to the final support.
        pBest->Saved = Dcr_Mffc( p, Id, pBest, 1 );
        p->fFullMark = 1;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Builds only the selected library graph.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Dcr_LibBuild_rec( Dc3_Man_t * p, int Id )
{
    int a, b, Lit0, Lit1;
    if ( p->LibLits[Id] >= 0 )
    {
        Gie_Finish( &p->F.M, p->LibLits[Id] >> 1 );
        return p->LibLits[Id];
    }
    assert( Id >= 4 && p->LibLits[Id] != -2 );
    a = Drw_LibNodes[p->pClass->iNodes + Id - 4][0];
    b = Drw_LibNodes[p->pClass->iNodes + Id - 4][1];
    Lit0 = Dcr_LibBuild_rec( p, a >> 1 );
    if ( Lit0 < 0 ) return -1;
    Lit1 = Dcr_LibBuild_rec( p, b >> 1 );
    if ( Lit1 < 0 ) return -1;
    return p->LibLits[Id] = Gie_And( &p->F.M, Lit0 ^ ( a & 1 ), Lit1 ^ ( b & 1 ) );
}

/**Function*************************************************************

  Synopsis    [Collects only the nodes needed by a selected library root.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Dcr_ProgramRec( Dc3_Man_t * p, int Class, int Id, unsigned char * Seen, int * Count )
{
    const Drw_LibClass_t * c = Drw_Classes + Class;
    if ( Id < 4 || Seen[Id] ) return;
    Dcr_ProgramRec( p, Class, Drw_LibNodes[c->iNodes + Id - 4][0] >> 1, Seen, Count );
    Dcr_ProgramRec( p, Class, Drw_LibNodes[c->iNodes + Id - 4][1] >> 1, Seen, Count );
    Seen[Id] = 1;
    p->LibOrder[Class][( *Count )++] = (unsigned char) Id;
}

/**Function*************************************************************

  Synopsis    [Compiles compact evaluation orders for the immutable rewriting library.]

  Description [Five roots per class, and all roots of the associative class, need at
  most 50 distinct internal nodes in the current library. Their exact area
  costs fit in one word.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Dcr_Programs( Dc3_Man_t * p )
{
    unsigned char Seen[DC3_LIB_LIMIT];
    int c, i, Count, nRoots;
    for ( c = 0; c < 222; c++ )
    {
        memset( Seen, 0, sizeof( Seen ) );
        Count = 0;
        nRoots = c == 1 ? Drw_Classes[c].nRoots : Abc_MinInt( 5, Drw_Classes[c].nRoots );
        for ( i = 0; i < nRoots; i++ )
        {
            Dcr_ProgramRec( p, c, Drw_LibRoots[Drw_Classes[c].iRoots + i] >> 1, Seen, &Count );
            assert( Count <= 64 );
            p->LibEnds[c][i] = (unsigned short) Count;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Chooses a feasible library structure for one cut.]

  Description [Counts new nodes after structural sharing and checks the replacement
  level against the fixed required level.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Dcr_Evaluate( Dc3_Man_t * p, int Id, Dcr_Cut_t * pCut )
{
    unsigned Transform;
    int i, k, nPrepared = 0, nRoots, fShared = 0, Best = -1, BestCost = pCut->Saved, BestLevel = ABC_INFINITY;
    int Required = p->F.M.fKeepLevel ? p->F.M.pFans[Id].Required : ABC_INFINITY;
    static const unsigned Truths[4] = { 0xAAAA, 0xCCCC, 0xF0F0, 0xFF00 };
    p->F.M.iRoot = Id;
    p->PlanLit = -1;
    p->PlanLevel = 0;
    if ( pCut->Truth == 0 || pCut->Truth == 65535 )
    {
        p->PlanLit = pCut->Truth != 0;
        return 0;
    }
    for ( i = 0; i < pCut->nLeaves; i++ )
        if ( pCut->Truth == Truths[i] || pCut->Truth == ( Truths[i] ^ 65535 ) )
        {
            p->PlanLit = 2 * pCut->Leaves[i] + ( pCut->Truth != Truths[i] );
            p->PlanLevel = p->F.M.pObjs[pCut->Leaves[i]].Level;
            return 0;
        }
    Transform = Drw_Transforms[pCut->Truth];
    p->pClass = Drw_Classes + ( Transform & 255 );
    if ( !p->pClass->nRoots ) return -1;

    assert( p->pClass->nNodes + 4 <= DC3_LIB_LIMIT );
    if ( !p->fFullMark )
    {
        if ( pCut->Saved == 1 )
        {
            Gie_MarkNext( &p->F.M );
            p->F.M.pObjs[Id].Mark = p->F.M.Mark;
        }
        else
        {
            i = Dcr_Mffc( p, Id, pCut, 1 );
            assert( i == pCut->Saved );
        }
    }
    nRoots = ( Transform & 255 ) == 1 ? p->pClass->nRoots : Abc_MinInt( 5, p->pClass->nRoots );
    for ( i = 0; i < 4; i++ )
    {
        int Pos = ( Transform >> ( 13 + 2 * i ) ) & 3;
        p->LibLits[i] = ( Pos < pCut->nLeaves ? 2 * pCut->Leaves[Pos] : 0 ) ^ ( ( Transform >> ( 8 + i ) ) & 1 );
        p->LibLevels[i] = p->F.M.pObjs[p->LibLits[i] >> 1].Level;
    }
    // Use a feasible standalone graph when the library already offers a
    // gain. Otherwise, sharing requires an external variable-pair gate:
    // an existing internal graph brings all its fanin gates with it.
    for ( i = 0; i < p->pClass->nPairs; i++ )
    {
        int Node = Drw_LibPairs[p->pClass->iPairs + i];
        int a, b, Lit;
        a = Drw_LibNodes[p->pClass->iNodes + Node - 4][0];
        b = Drw_LibNodes[p->pClass->iNodes + Node - 4][1];
        Lit = Gie_Lookup( &p->F.M, p->LibLits[a >> 1] ^ ( a & 1 ), p->LibLits[b >> 1] ^ ( b & 1 ), -1 );
        if ( Lit >= 0 && p->F.M.pObjs[Lit >> 1].Mark != p->F.M.Mark )
        {
            fShared = 1;
            break;
        }
    }
    if ( !fShared )
    {
        if ( p->pClass->MinSize > pCut->Saved - !p->fZeros ) return -1;
        for ( i = 0; i < nRoots; i++ )
        {
            int Cost = Drw_LibSizes[p->pClass->iRoots + i], Level = 0;
            const signed char * pDepths = Drw_LibDepths[p->pClass->iRoots + i];
            if ( Cost > pCut->Saved - !p->fZeros || Cost > BestCost ) continue;
            for ( k = 0; k < 4; k++ )
                if ( pDepths[k] >= 0 ) Level = Abc_MaxInt( Level, p->LibLevels[k] + pDepths[k] );
            if ( Level > Required ) continue;
            if ( !p->fChoiceZeros && Cost == pCut->Saved && Level >= p->F.M.pObjs[Id].Level ) continue;
            if ( Cost == BestCost && Level >= BestLevel ) continue;
            Best = i;
            BestCost = Cost;
            BestLevel = Level;
        }
        if ( Best < 0 ) return -1;
        i = Drw_LibRoots[p->pClass->iRoots + Best];
        memset( p->LibLits + 4, 0xFF, ( ( i >> 1 ) - 3 ) * sizeof( int ) );
        p->PlanRoot = i;
        p->PlanPhase = ( Transform >> 12 ) & 1;
        p->PlanLevel = BestLevel;
        return BestCost;
    }
    // Cost masks are needed only after finding an opportunity for sharing.
    memset( p->LibCosts, 0, 4 * sizeof( word ) );
    for ( i = 0; i < nRoots; i++ )
    {
        int Root = Drw_LibRoots[p->pClass->iRoots + i] >> 1;
        int Cost;
        for ( ; nPrepared < p->LibEnds[Transform & 255][i]; nPrepared++ )
        {
            int Index = p->LibOrder[Transform & 255][nPrepared];
            int j = Index - 4;
            int a = Drw_LibNodes[p->pClass->iNodes + j][0];
            int b = Drw_LibNodes[p->pClass->iNodes + j][1];
            int Lit0 = p->LibLits[a >> 1], Lit1 = p->LibLits[b >> 1], Lit = -1;
            p->LibLevels[Index] = 1 + Abc_MaxInt( p->LibLevels[a >> 1], p->LibLevels[b >> 1] );
            if ( Lit0 == -2 || Lit1 == -2 )
                Lit = -2;
            else if ( Lit0 >= 0 && Lit1 >= 0 )
            {
                Lit = Gie_Lookup( &p->F.M, Lit0 ^ ( a & 1 ), Lit1 ^ ( b & 1 ), -1 );
                if ( Lit >= 0 && ( Lit >> 1 ) == Id )
                    Lit = -2;
                else if ( Lit >= 0 )
                {
                    if ( Gie_Simplify( Lit0 ^ ( a & 1 ), Lit1 ^ ( b & 1 ) ) < 0 )
                        p->F.M.pObjs[Lit >> 1].Level = p->LibLevels[Index];
                    else
                        p->LibLevels[Index] = Gie_AndLevel( Lit0 ^ ( a & 1 ), Lit1 ^ ( b & 1 ), p->LibLevels[a >> 1],
                                                            p->LibLevels[b >> 1] );
                }
            }
            p->LibLits[Index] = Lit;
            p->LibCosts[Index] = ( Lit >= 0 && p->F.M.pObjs[Lit >> 1].Mark != p->F.M.Mark )
                                     ? 0
                                     : p->LibCosts[a >> 1] | p->LibCosts[b >> 1] | ( (word) 1 << nPrepared );
        }
        if ( p->LibLevels[Root] > Required || p->LibLits[Root] == -2 ) continue;
        Cost = Abc_TtCountOnes( p->LibCosts[Root] );
        if ( Cost == pCut->Saved && p->fZeroCap && p->LibLevels[Root] > p->F.M.pObjs[Id].Level ) continue;
        if ( !p->fChoiceZeros && Cost == pCut->Saved && p->LibLevels[Root] >= p->F.M.pObjs[Id].Level &&
             ( Drw_LibSizes[p->pClass->iRoots + i] <= Cost ) )
            continue;
        if ( Cost > pCut->Saved - !p->fZeros || Cost > BestCost ||
             ( Cost == BestCost && p->LibLevels[Root] >= BestLevel ) )
            continue;
        Best = i;
        BestCost = Cost;
        BestLevel = p->LibLevels[Root];
    }
    if ( Best < 0 ) return -1;
    i = Drw_LibRoots[p->pClass->iRoots + Best];
    p->PlanRoot = i;
    p->PlanPhase = ( Transform >> 12 ) & 1;
    p->PlanLevel = BestLevel;
    return BestCost;
}

/**Function*************************************************************

  Synopsis    [Selects the best rewrite among bounded four-input cuts.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Dcr_ExtraCuts( Dc3_Man_t * p, int Root, Dcr_Cut_t * BestCut )
{
    Dcr_Cuts_t Cuts;
    Dcr_Cut_t * c = Cuts.Cuts + 1;
    int i, j, Fan;
    unsigned Hash = 0;
    memset( &Cuts, 0, sizeof( Cuts ) );
    Cuts.nCuts = 2;
    for ( i = 0; i < 2; i++ )
    {
        Fan = p->F.M.pObjs[Root].Fan[i] >> 1;
        if ( !Fan || ( c->nLeaves && c->Leaves[0] == Fan ) ) continue;
        c->Leaves[c->nLeaves++] = Fan;
    }
    if ( c->nLeaves == 2 && c->Leaves[0] > c->Leaves[1] ) ABC_SWAP( int, c->Leaves[0], c->Leaves[1] );
    c->fFullSupport = 1;
    for ( i = 0; i < c->nLeaves; i++ )
    {
        Fan = c->Leaves[i];
        if ( p->F.M.pObjs[Fan].Type == GIE_AND ) p->F.M.pObjs[Fan].Refs++;
        Hash ^= Dcr_CutHash( Fan );
    }
    c->Saved = Gie_Deref( &p->F.M, Root, 0 );
    Cuts.Table[Hash & 63] = 1;
    Cuts.Hash[1] = Hash;
    p->F.M.pObjs[Root].Inside = 1;
    Dcr_CutsExplore_rec( p, &Cuts, c, Hash );
    p->F.M.pObjs[Root].Inside = 0;
    Gie_Ref( &p->F.M, Root );
    for ( i = 0; i < c->nLeaves; i++ )
        if ( p->F.M.pObjs[c->Leaves[i]].Type == GIE_AND ) p->F.M.pObjs[c->Leaves[i]].Refs--;

    {
        int BestGain = -1, BestLevel = INT_MAX, BestLits[DC3_LIB_LIMIT], BestRoot = -1, BestPhase = 0, BestLit = -1;
        const Drw_LibClass_t * BestClass = NULL;
        for ( i = 1; i < Cuts.nCuts; i++ )
        {
            int Cost, Gain;
            c = Cuts.Cuts + i;
            c->Truth = Dcr_Truth( p, Root, c );
            j = c->nLeaves;
            Dcr_CutMinimize( c );
            if ( j != c->nLeaves ) c->Saved = Dcr_Mffc( p, Root, c, 0 );
            p->fFullMark = 0;
            Cost = Dcr_Evaluate( p, Root, c );
            if ( Cost < 0 ) continue;
            Gain = c->Saved - Cost;
            if ( Gain < BestGain || ( Gain == BestGain && p->PlanLevel >= BestLevel ) ) continue;
            BestGain = Gain;
            BestLevel = p->PlanLevel;
            BestLit = p->PlanLit;
            *BestCut = *c;
            if ( BestLit < 0 )
            {
                BestClass = p->pClass;
                BestRoot = p->PlanRoot;
                BestPhase = p->PlanPhase;
                memcpy( BestLits, p->LibLits, sizeof( BestLits ) );
            }
        }
        if ( BestGain < 0 ) return -1;
        p->PlanLit = BestLit;
        p->PlanLevel = BestLevel;
        if ( BestLit < 0 )
        {
            p->pClass = BestClass;
            p->PlanRoot = BestRoot;
            p->PlanPhase = BestPhase;
            memcpy( p->LibLits, BestLits, sizeof( BestLits ) );
        }
        return BestGain;
    }
}

/**Function*************************************************************

  Synopsis    [Checks a cached cut by recomputing its current truth table.]

  Description [The bounded walk rejects a recipe that no longer covers the root.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Dcr_RecipeTruth( Dc3_Man_t * p, int Id, int * Budget )
{
    int a, b;
    if ( p->F.M.pObjs[Id].TruthMark == p->F.M.TruthMark ) return 1;
    if ( p->F.M.pObjs[Id].Type != GIE_AND || --*Budget < 0 ) return 0;
    a = p->F.M.pObjs[Id].Fan[0];
    b = p->F.M.pObjs[Id].Fan[1];
    if ( !Dcr_RecipeTruth( p, a >> 1, Budget ) || !Dcr_RecipeTruth( p, b >> 1, Budget ) ) return 0;
    p->F.M.pObjs[Id].Truth = (unsigned short) ( ( p->F.M.pObjs[a >> 1].Truth ^ ( ( a & 1 ) ? 65535 : 0 ) ) &
                                                ( p->F.M.pObjs[b >> 1].Truth ^ ( ( b & 1 ) ? 65535 : 0 ) ) );
    p->F.M.pObjs[Id].TruthMark = p->F.M.TruthMark;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Prepares only the nodes of a cached library root.]

  Description [Computes exact levels and sharing costs from the current cut leaves.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Dcr_OnePrepare( Dc3_Man_t * p, int Id, int Root, int * Count )
{
    int a, b, x, y, Lit;
    if ( Id < 4 || p->LibSeen[Id] ) return 1;
    a = Drw_LibNodes[p->pClass->iNodes + Id - 4][0];
    b = Drw_LibNodes[p->pClass->iNodes + Id - 4][1];
    if ( !Dcr_OnePrepare( p, a >> 1, Root, Count ) || !Dcr_OnePrepare( p, b >> 1, Root, Count ) ) return 0;
    p->LibSeen[Id] = 1;
    x = p->LibLits[a >> 1];
    y = p->LibLits[b >> 1];
    Lit = ( x >= 0 && y >= 0 ) ? Gie_Lookup( &p->F.M, x ^ ( a & 1 ), y ^ ( b & 1 ), -1 ) : -1;
    if ( Lit >= 0 && ( Lit >> 1 ) == Root ) return 0;
    p->LibLits[Id] = Lit;
    p->LibLevels[Id] = ( x >= 0 && y >= 0 )
                           ? Gie_AndLevel( x ^ ( a & 1 ), y ^ ( b & 1 ), p->LibLevels[a >> 1], p->LibLevels[b >> 1] )
                           : 1 + Abc_MaxInt( p->LibLevels[a >> 1], p->LibLevels[b >> 1] );
    if ( Lit >= 0 && Lit > 1 ) p->F.M.pObjs[Lit >> 1].Level = p->LibLevels[Id];
    assert( *Count < 64 );
    p->LibCosts[Id] = ( Lit >= 0 && p->F.M.pObjs[Lit >> 1].Mark != p->F.M.Mark )
                          ? 0
                          : p->LibCosts[a >> 1] | p->LibCosts[b >> 1] | ( (word) 1 << ( *Count ) );
    ( *Count )++;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Rechecks a cached library structure against the current graph.]

  Description [The saved recipe is a candidate, not a proof. Current truth, MFFC gain,
  sharing, and level determine whether it can be used.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Dcr_OnePlan( Dc3_Man_t * p, int Root, Dcr_Cut_t * c, int LibRoot )
{
    unsigned Transform = Drw_Transforms[c->Truth];
    int i, Pos, Count = 0, Cost;
    p->pClass = Drw_Classes + ( Transform & 255 );
    p->F.M.iRoot = Root;
    memset( p->LibSeen, 0, ( p->pClass->nNodes + 4 ) * sizeof( int ) );
    for ( i = 0; i < 4; i++ )
    {
        Pos = ( Transform >> ( 13 + 2 * i ) ) & 3;
        p->LibLits[i] = ( Pos < c->nLeaves ? 2 * c->Leaves[Pos] : 0 ) ^ ( ( Transform >> ( 8 + i ) ) & 1 );
        p->LibLevels[i] = p->F.M.pObjs[p->LibLits[i] >> 1].Level;
        p->LibCosts[i] = 0;
    }
    if ( !Dcr_OnePrepare( p, LibRoot >> 1, Root, &Count ) ) return -1;
    if ( p->F.M.fKeepLevel && p->LibLevels[LibRoot >> 1] > p->F.M.pFans[Root].Required ) return -1;
    Cost = Abc_TtCountOnes( p->LibCosts[LibRoot >> 1] );
    if ( Cost > c->Saved - !p->fZeros ) return -1;
    if ( Cost == c->Saved && p->fZeroCap && p->LibLevels[LibRoot >> 1] > p->F.M.pObjs[Root].Level ) return -1;
    if ( Cost == c->Saved && p->LibLevels[LibRoot >> 1] >= p->F.M.pObjs[Root].Level && ( Count <= Cost ) ) return -1;
    p->PlanRoot = LibRoot;
    p->PlanLit = -1;
    p->PlanPhase = ( Transform >> 12 ) & 1;
    p->PlanLevel = p->LibLevels[LibRoot >> 1];
    return Cost;
}

/**Function*************************************************************

  Synopsis    [Tries cached cut paths and library roots for a similar neighborhood.]

  Description [Each path is resolved in the current graph and its truth is recomputed.
  The neighborhood fingerprint affects search effort only.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Dcr_RecipeTry( Dc3_Man_t * p, int Root, Dc3_Neighbor_t * n, Dcr_Cut_t * c )
{
    static const unsigned short Vars[4] = { 0xAAAA, 0xCCCC, 0xF0F0, 0xFF00 };
    int r, i, j, Id, Cost, Budget;
    word Path;
    for ( r = n->Recipe; r; r = p->pRecipes[r].Next )
    {
        Dc3_Recipe_t * q = p->pRecipes + r;
        c->nLeaves = q->nLeaves;
        for ( i = 0; i < c->nLeaves; i++ )
        {
            Id = Root;
            Path = q->Paths[i];
            while ( Path > 1 )
            {
                if ( p->F.M.pObjs[Id].Type != GIE_AND ) break;
                Id = p->F.M.pObjs[Id].Fan[Path & 1] >> 1;
                Path >>= 1;
            }
            if ( Path > 1 || !Id ) break;
            for ( j = 0; j < i; j++ )
                if ( c->Leaves[j] == Id ) break;
            if ( j < i ) break;
            c->Leaves[i] = Id;
        }
        if ( i < c->nLeaves ) continue;
        Gie_TruthNext( &p->F.M );
        p->F.M.pObjs[0].Truth = 0;
        p->F.M.pObjs[0].TruthMark = p->F.M.TruthMark;
        for ( i = 0; i < c->nLeaves; i++ )
        {
            p->F.M.pObjs[c->Leaves[i]].Truth = Vars[i];
            p->F.M.pObjs[c->Leaves[i]].TruthMark = p->F.M.TruthMark;
        }
        Budget = 96;
        if ( !Dcr_RecipeTruth( p, Root, &Budget ) ||
             ( Drw_Transforms[p->F.M.pObjs[Root].Truth] & 255 ) != ( Drw_Transforms[q->Truth] & 255 ) )
            continue;
        c->Truth = p->F.M.pObjs[Root].Truth;
        c->Saved = Dcr_Mffc( p, Root, c, 1 );
        p->fFullMark = 1;
        Cost = q->LibRoot >= 0 ? Dcr_OnePlan( p, Root, c, q->LibRoot ) : Dcr_Evaluate( p, Root, c );
        if ( Cost < 0 || c->Saved - Cost < q->Gain ) continue;
        p->nRecipeHits++;
        return c->Saved - Cost;
    }
    return -1;
}

/**Function*************************************************************

  Synopsis    [Encodes cut leaves as bounded fanin paths from the root.]

  Description [The high bit terminates each path; lower bits select successive fanins.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Dcr_RecipePath( Dc3_Man_t * p, int Id, Dcr_Cut_t * c, word Path, int Depth, word * Paths, int * Budget )
{
    int i;
    for ( i = 0; i < c->nLeaves; i++ )
        if ( c->Leaves[i] == Id )
        {
            Paths[i] = ( (word) 1 << Depth ) | Path;
            return 1;
        }
    if ( !Id ) return 1;
    if ( p->F.M.pObjs[Id].Type != GIE_AND || Depth == 60 || --*Budget < 0 ) return 0;
    return Dcr_RecipePath( p, p->F.M.pObjs[Id].Fan[0] >> 1, c, Path, Depth + 1, Paths, Budget ) &&
           Dcr_RecipePath( p, p->F.M.pObjs[Id].Fan[1] >> 1, c, Path | ( (word) 1 << Depth ), Depth + 1, Paths, Budget );
}

/**Function*************************************************************

  Synopsis    [Records a successful cut and library structure as a search hint.]

  Description [Entries are bounded and cleared between passes. They contain no
  persistent graph-object IDs.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Dcr_RecipeSave( Dc3_Man_t * p, int Root, Dc3_Neighbor_t * n, Dcr_Cut_t * c, int Gain )
{
    Dc3_Recipe_t New;
    int i, Budget = 96;
    if ( n->nRecipes == DC3_RECIPES_PER_KEY || p->nRecipes == ( DC3_RECIPE_LIMIT - 1 ) || !c->nLeaves ) return;
    memset( &New, 0, sizeof( New ) );
    if ( !Dcr_RecipePath( p, Root, c, 0, 0, New.Paths, &Budget ) ) return;
    for ( i = 0; i < c->nLeaves; i++ )
        if ( !New.Paths[i] ) return;
    New.LibRoot = p->PlanLit < 0 ? p->PlanRoot : -1;
    New.nLeaves = c->nLeaves;
    New.Truth = c->Truth;
    New.Gain = Gain;
    New.Next = n->Recipe;
    p->pRecipes[++p->nRecipes] = New;
    n->Recipe = p->nRecipes;
    n->nRecipes++;
}

/**Function*************************************************************

  Synopsis    [Balances one bounded associative cone in the mutable graph.]

  Description [Searches a bounded set of low-level frontier pairs for external
  sharing. Pair level and reference count break ties. The replacement must
  not increase area or the root's current level in level-preserving mode.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Dc3_BalanceNode( Dc3_Man_t * p, int Root )
{
    int Todo[128], Leaves[64], Front[64], Lits[128], Levels[128], A[128], B[128];
    int nTodo = 1, nLeaves = 0, nSaved = 0, nNodes, nFront, i, j, Id, Lit, a, b, Level, Added = 0, Edge;
    if ( p->F.M.pObjs[Root].Refs == 1 )
    {
        for ( Edge = p->F.M.pFans[Root].Head; Edge; Edge = p->F.M.pFans[Edge >> 1].Next[Edge & 1] )
            if ( p->F.M.pObjs[Edge >> 1].Type != GIE_DEAD ) break;
        if ( Edge && p->F.M.pObjs[Edge >> 1].Type == GIE_AND && !( p->F.M.pObjs[Edge >> 1].Fan[Edge & 1] & 1 ) )
            return -1;
    }
    p->F.M.iRoot = Root;
    Gie_MarkNext( &p->F.M );
    Todo[0] = 2 * Root;
    while ( nTodo )
    {
        Lit = Todo[--nTodo];
        Id = Lit >> 1;
        if ( !( Lit & 1 ) && p->F.M.pObjs[Id].Type == GIE_AND && ( Id == Root || p->F.M.pObjs[Id].Refs == 1 ) )
        {
            if ( nSaved == 63 ) return -1;
            nSaved++;
            p->F.M.pObjs[Id].Mark = p->F.M.Mark;
            Todo[nTodo++] = p->F.M.pObjs[Id].Fan[1];
            Todo[nTodo++] = p->F.M.pObjs[Id].Fan[0];
        }
        else
        {
            if ( Lit == 0 ) return 0;
            if ( Lit == 1 ) continue;
            for ( i = 0; i < nLeaves; i++ )
                if ( ( Leaves[i] >> 1 ) == Id ) break;
            if ( i < nLeaves )
            {
                if ( Leaves[i] != Lit ) return 0;
                continue;
            }
            if ( nLeaves == 64 ) return -1;
            Leaves[nLeaves++] = Lit;
        }
    }
    if ( nSaved < 2 ) return -1;
    if ( !nLeaves ) return 1;
    if ( nLeaves == 1 ) return Leaves[0];
    nNodes = nFront = nLeaves;
    for ( i = 0; i < nLeaves; i++ )
    {
        Lits[i] = Leaves[i];
        Levels[i] = p->F.M.pObjs[Leaves[i] >> 1].Level;
        Front[i] = i;
        for ( j = i; j > 0 && ( Levels[Front[j]] > Levels[Front[j - 1]] ||
                                ( Levels[Front[j]] == Levels[Front[j - 1]] && Lits[Front[j]] > Lits[Front[j - 1]] ) );
              j-- )
            ABC_SWAP( int, Front[j], Front[j - 1] );
    }
    while ( nFront > 1 )
    {
        a = Front[nFront - 1];
        b = Front[nFront - 2];
        {
            int X, Y, BestX = -1, BestY = -1, BestLevel = ABC_INFINITY, BestRefs = -1;
            for ( X = nFront - 1; X >= 0 && X >= nFront - DC3_BALANCE_LEAVES; X-- )
                for ( Y = X - 1; Y >= 0 && Y >= nFront - DC3_BALANCE_LEAVES; Y-- )
                {
                    int Lev = 1 + Abc_MaxInt( Levels[Front[X]], Levels[Front[Y]] );
                    if ( Lits[Front[X]] < 0 || Lits[Front[Y]] < 0 || Lev > BestLevel ) continue;
                    Lit = Gie_Lookup( &p->F.M, Lits[Front[X]], Lits[Front[Y]], Root );
                    if ( Lit < 0 || p->F.M.pObjs[Lit >> 1].Mark == p->F.M.Mark ) continue;
                    if ( Lev == BestLevel && p->F.M.pObjs[Lit >> 1].Refs <= BestRefs ) continue;
                    BestX = X;
                    BestY = Y;
                    BestLevel = Lev;
                    BestRefs = p->F.M.pObjs[Lit >> 1].Refs;
                }
            if ( BestX >= 0 )
            {
                a = Front[BestX];
                b = Front[BestY];
                // BestX > BestY; remove both while keeping the remaining levels sorted.
                for ( i = BestX; i < nFront - 1; i++ ) Front[i] = Front[i + 1];
                for ( i = BestY; i < nFront - 2; i++ ) Front[i] = Front[i + 1];
            }
        }
        nFront -= 2;
        Lit = ( Lits[a] >= 0 && Lits[b] >= 0 ) ? Gie_Lookup( &p->F.M, Lits[a], Lits[b], -1 ) : -1;
        if ( Lit >= 0 && ( Lit >> 1 ) == Root ) return -1;
        Level = 1 + Abc_MaxInt( Levels[a], Levels[b] );
        if ( Lits[a] >= 0 && Lits[b] >= 0 ) Level = Gie_AndLevel( Lits[a], Lits[b], Levels[a], Levels[b] );
        if ( Lit < 0 || p->F.M.pObjs[Lit >> 1].Mark == p->F.M.Mark ) Added++;
        if ( Added > nSaved ) return -1;
        A[nNodes] = a;
        B[nNodes] = b;
        Lits[nNodes] = Lit;
        Levels[nNodes] = Level;
        Front[nFront++] = nNodes++;
        for ( j = nFront - 1; j > 0 && Levels[Front[j]] > Levels[Front[j - 1]]; j-- )
            ABC_SWAP( int, Front[j], Front[j - 1] );
    }
    if ( ( p->F.M.fKeepLevel || Added == nSaved ) && Levels[Front[0]] > p->F.M.pObjs[Root].Level ) return -1;
    for ( i = nLeaves; i < nNodes; i++ )
    {
        Lit = Gie_And( &p->F.M, Lits[A[i]], Lits[B[i]] );
        if ( Lit < 0 ) return -1;
        Lits[i] = Lit;
    }
    return Lits[Front[0]];
}

/**Function*************************************************************

  Synopsis    [Orders the first pass by level while preserving topology.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Dc3_LevelOrder( Dc3_Man_t * p, Vec_Int_t * v )
{
    int i, Id, Max = 0, n = 0, Sum = 0, Val, *Counts, *Order;
    Vec_IntForEachEntry ( v, Id, i )
        if ( p->F.M.pObjs[Id].Type == GIE_AND )
        {
            Max = Abc_MaxInt( Max, p->F.M.pObjs[Id].Level );
            n++;
        }
    if ( Max > 4 * Abc_MaxInt( n, 1 ) ) return;
    Counts = ABC_CALLOC( int, Max + 1 );
    Order = ABC_ALLOC( int, n );
    Vec_IntForEachEntry ( v, Id, i )
        if ( p->F.M.pObjs[Id].Type == GIE_AND ) Counts[p->F.M.pObjs[Id].Level]++;
    for ( i = 0; i <= Max; i++ )
    {
        Val = Counts[i];
        Counts[i] = Sum;
        Sum += Val;
    }
    Vec_IntForEachEntry ( v, Id, i )
        if ( p->F.M.pObjs[Id].Type == GIE_AND ) Order[Counts[p->F.M.pObjs[Id].Level]++] = Id;
    Vec_IntShrink( v, n );
    if ( n ) memcpy( Vec_IntArray( v ), Order, n * sizeof( int ) );
    ABC_FREE( Counts );
    ABC_FREE( Order );
}

/**Function*************************************************************

  Synopsis    [Labels an export with the corresponding stable mutable IDs.]

  Description [Uses exactly the object order of Gie_ManExport.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Dc3_Labels( Gie_Man_t * p )
{
    Vec_Int_t * v = Vec_IntAlloc( p->nAnds + Vec_IntSize(p->vCis) + Vec_IntSize(p->vCos) + 1 );
    int i, Id;
    Vec_IntPush( v, 0 );
    Vec_IntForEachEntry( p->vCis, Id, i ) Vec_IntPush( v, 2 * Id );
    Vec_IntForEachEntry( p->vOrder, Id, i )
        if ( p->pObjs[Id].Type == GIE_AND && p->pObjs[Id].Refs ) Vec_IntPush( v, 2 * Id );
    Vec_IntForEachEntry( p->vCos, Id, i ) Vec_IntPush( v, -1 );
    return v;
}

/**Function*************************************************************

  Synopsis    [Resolves replacement chains while preserving complement bits.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Dc3_LabelFind( Vec_Int_t * v, int Lit )
{
    int Root = Lit, Next;
    if ( Lit < 0 ) return Lit;
    while ( (Next = Vec_IntEntry(v, Root >> 1)) >= 0 ) Root = Next ^ (Root & 1);
    while ( (Next = Vec_IntEntry(v, Lit >> 1)) >= 0 )
    {
        Vec_IntWriteEntry( v, Lit >> 1, Root ^ (Lit & 1) );
        Lit = Next ^ (Lit & 1);
    }
    return Root;
}

/**Function*************************************************************

  Synopsis    [Records an equality already established by an accepted rewrite.]

  Description [The ordinary DC3 path passes NULL and allocates no proof data.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Dc3_LabelReplace( Vec_Int_t * v, int nObjs, int Id, int Lit )
{
    if ( !v ) return;
    Vec_IntFillExtra( v, nObjs, -1 );
    assert( Vec_IntEntry(v, Id) == -1 && (Lit >> 1) != Id );
    Vec_IntWriteEntry( v, Id, Lit );
}

/**Function*************************************************************

  Synopsis    [Runs shared rewriting/refactoring passes and final balancing.]

  Description [The first two passes require positive gain. Later passes also permit
  selected zero-gain rewrites to expose sharing. The structural hash and
  factorization caches persist; required levels and search hints are
  refreshed between passes. Choice synthesis uses one positive-gain pass,
  one zero-gain pass with a single rewrite cut, and final balancing.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Dc3_Run( Gia_Man_t * pGia, int fKeepLevel, int fVerbose, Gia_Man_t ** ppSnapshot, Vec_Ptr_t * vLabels, int fMore )
{
    Dc3_Man_t * p;
    Gia_Man_t * pNew;
    Vec_Int_t *vCiLevels, *vVisit, *vParents = NULL;
    int Round, Pos, PrevAnds, GainF, GainW, Cost, StartAnds;
    Drf_Cut_t Cut;
    Dc3_Neighbor_t * Neighbor;
    Dcr_Cut_t Cut4;
    int Id, Lit, NewStart, OldAnds, Done;
    abctime Start = Abc_Clock(), Setup, Export, Clock;
    if ( pGia == NULL || Gia_ManHasChoices( pGia ) || Gia_ManMuxNum( pGia ) || Gia_ManXorNum( pGia ) || Gia_ManBufNum( pGia ) )
        return NULL;
    // Internal sequential box views use a different CI order. Require
    // the standard normalized interface when explicit registers coexist.
    if ( Gia_ManIsSeqWithBoxes( pGia ) && !Gia_ManIsNormalized( pGia ) ) return NULL;
    if ( Gia_ManObjNum( pGia ) > Gie_ObjectLimit() / 2 ) return NULL;
    if ( vLabels ) vParents = Vec_IntStartFull( Gia_ManObjNum(pGia) );
    vCiLevels = Gia_ManBoxNum( pGia ) ? Gie_BoxCiLevels( pGia ) : NULL;
    p = ABC_CALLOC( Dc3_Man_t, 1 );
    Drf_ManInit( &p->F, pGia, fKeepLevel, GIE_HASH_ALL, vCiLevels );
    p->F.nExpandLimit = DRF_LEAF_MAX;
    // Choice synthesis keeps same-level alternatives in the zero-gain pass only.
    p->fChoiceZeros = vLabels != NULL;
    Vec_IntFreeP( &vCiLevels );
    Dcr_Programs( p );
    Setup = Abc_Clock() - Start;
    vVisit = Vec_IntAlloc( p->F.M.nObjs );
    for ( Id = 1; Id < p->F.M.nObjs; Id++ )
        if ( p->F.M.pObjs[Id].Type == GIE_AND ) Vec_IntPush( vVisit, Id );
    // Small choice-synthesis graphs need few neighborhood hints. Bound their
    // allocation by graph size; standalone DC3 retains its cache capacity.
    p->nNeighborBins = vLabels ? 256 : DC3_NEIGHBOR_BINS;
    while ( p->nNeighborBins < DC3_NEIGHBOR_BINS && p->nNeighborBins / 4 < p->F.M.nAnds )
        p->nNeighborBins *= 2;
    p->pNeighbors = ABC_CALLOC( Dc3_Neighbor_t, p->nNeighborBins );
    p->pRecipes = ABC_ALLOC( Dc3_Recipe_t, DC3_RECIPE_LIMIT );
    StartAnds = p->F.M.nAnds;
    for ( Round = 0; Round < DC3_PASSES; Round++ )
    {
        // The ordinary choice flow retains its three-pass schedule. Area
        // mapping can spend the extra passes after at least 1/16 gain.
        if ( vLabels && (Round == 1 || Round == 3) &&
             (!fMore || (long long)16*p->F.M.nAnds > (long long)15*StartAnds) ) continue;
        Clock = fVerbose ? Abc_Clock() : 0;
        PrevAnds = p->F.M.nAnds;
        p->fZeros = Round >= 2;
        p->fZeroCap = Round < 3;
        if ( Round > 0 )
        {
            ABC_SWAP( Vec_Int_t *, vVisit, p->F.M.vOrder );
            Vec_IntClear( p->F.M.vOrder );
            Vec_IntForEachEntry ( vVisit, Id, Pos )
            {
                if ( p->F.M.pObjs[Id].Type != GIE_AND ) continue;
                p->F.M.pObjs[Id].Handled = 0;
                p->F.M.pFans[Id].Required = ABC_INFINITY;
            }
            Vec_IntForEachEntry ( p->F.M.vCos, Id, Pos )
            {
                int Var = p->F.M.pObjs[Id].Fan[0] >> 1;
                p->F.M.pFans[Var].Required = Abc_MinInt( p->F.M.pFans[Var].Required, p->F.M.pFans[Id].Required );
            }
            for ( Pos = Vec_IntSize( vVisit ) - 1; Pos >= 0; Pos-- )
            {
                int k;
                Id = Vec_IntEntry( vVisit, Pos );
                if ( p->F.M.pObjs[Id].Type != GIE_AND ) continue;
                for ( k = 0; k < 2; k++ )
                {
                    int Var = p->F.M.pObjs[Id].Fan[k] >> 1;
                    p->F.M.pFans[Var].Required =
                        Abc_MinInt( p->F.M.pFans[Var].Required, p->F.M.pFans[Id].Required - 1 );
                }
            }
        }
        if ( Round == 0 ) Dc3_LevelOrder( p, vVisit );
        if ( Round < 4 )
        {
            ABC_FREE( p->pNeighborhood );
            p->pNeighborhood = Gie_Neighborhoods( &p->F.M, p->F.M.nObjs, 3 );
            p->nRecipes = 0;
        }
        // Reused ready nodes finish early. All remaining original nodes retain
        // their topological visit order; each is considered at most once.
        Vec_IntForEachEntry ( vVisit, Id, Pos )
        {
            if ( p->F.M.pObjs[Id].Type != GIE_AND || p->F.M.pObjs[Id].Handled ) continue;
            assert( !p->F.M.pObjs[Id].Handled && p->F.M.pObjs[Id].Type == GIE_AND );
            assert( p->F.M.pObjs[p->F.M.pObjs[Id].Fan[0] >> 1].Handled );
            assert( p->F.M.pObjs[p->F.M.pObjs[Id].Fan[1] >> 1].Handled );
            // Refresh the current node from its finished fanins.
            p->F.M.pObjs[Id].Level = 1 + Abc_MaxInt( p->F.M.pObjs[p->F.M.pObjs[Id].Fan[0] >> 1].Level,
                                                     p->F.M.pObjs[p->F.M.pObjs[Id].Fan[1] >> 1].Level );
            Lit = Gie_Simplify( p->F.M.pObjs[Id].Fan[0], p->F.M.pObjs[Id].Fan[1] );
            if ( Lit < 0 && ( !p->F.M.pObjs[Id].Hashed || p->F.M.pObjs[Id].Duplicate ) )
                Lit = Gie_Lookup( &p->F.M, p->F.M.pObjs[Id].Fan[0], p->F.M.pObjs[Id].Fan[1], Id );
            if ( Lit >= 0 )
            {
                Gie_Finish( &p->F.M, Lit >> 1 );
                Dc3_LabelReplace( vParents, p->F.M.nObjs, Id, Lit );
                Gie_Replace( &p->F.M, Id, Lit );
                p->nMerged++;
                continue;
            }
            if ( !p->F.M.pObjs[Id].Hashed ) Gie_HashInsert( &p->F.M, Id );
            NewStart = p->F.M.nObjs;
            OldAnds = p->F.M.nAnds;
            Neighbor = NULL;
            if ( Round == 4 )
            {
                Lit = Dc3_BalanceNode( p, Id );
                goto dc3_apply;
            }
            Lit = Drf_TwoGate( &p->F, Id, &Done );
            if ( !Done ) Lit = Drf_ThreeGate( &p->F, Id, &Done );
            if ( Lit >= 0 || p->F.M.nObjs != NewStart ) goto dc3_apply;
            Neighbor = p->pNeighbors + ( p->pNeighborhood[Id] & ( p->nNeighborBins - 1 ) );
            // Reset only touched entries. Recipes belong to this pass;
            // the epoch also invalidates entries whose hash did not change.
            if ( Neighbor->Epoch != Round + 1 || Neighbor->Hash != p->pNeighborhood[Id] )
            {
                Neighbor->Epoch = (unsigned char)(Round + 1);
                Neighbor->Hash = p->pNeighborhood[Id];
                Neighbor->Recipe = Neighbor->nRecipes = Neighbor->Failed = 0;
            }
            GainW = Dcr_RecipeTry( p, Id, Neighbor, &Cut4 );
            if ( GainW >= 0 ) goto build_w;
            if ( Neighbor->Failed >= DC3_FAILURE_LIMIT )
            {
                p->nSkipped++;
                goto finish;
            }
            GainF = GainW = -1;
            if ( !Done && Drf_SelectCut( &p->F, Id, &Cut ) )
            {
                Cost = Drf_Evaluate( &p->F, Id, &Cut );
                if ( Cost >= 0 ) GainF = Cut.Saved - Cost;
            }
            if ( p->fZeros && !vLabels )
                GainW = Dcr_ExtraCuts( p, Id, &Cut4 );
            else if ( Dcr_SelectCut( p, Id, &Cut4 ) )
            {
                Cost = Dcr_Evaluate( p, Id, &Cut4 );
                if ( Cost >= 0 ) GainW = Cut4.Saved - Cost;
            }
            if ( GainF < 0 && GainW < 0 )
            {
                Neighbor->Failed++;
                goto finish;
            }
            Neighbor->Failed = 0;
            if ( GainF > GainW || ( GainF == GainW && p->F.FactorLevel <= p->PlanLevel ) )
                Lit = Drf_BuildFactor( &p->F, &Cut );
            else
            {
                Dcr_RecipeSave( p, Id, Neighbor, &Cut4, GainW );
            build_w:
                if ( p->PlanLit >= 0 )
                    Lit = p->PlanLit;
                else
                {
                    Lit = Dcr_LibBuild_rec( p, p->PlanRoot >> 1 );
                    if ( Lit >= 0 ) Lit ^= ( p->PlanRoot & 1 ) ^ p->PlanPhase;
                }
            }
        dc3_apply:
            if ( Lit < 0 && NewStart == p->F.M.nObjs ) goto finish;
            if ( Lit >= 0 ) assert( !p->F.M.fKeepLevel || p->F.M.pObjs[Lit >> 1].Level <= p->F.M.pFans[Id].Required );
            if ( Lit >= 0 )
            {
                Dc3_LabelReplace( vParents, p->F.M.nObjs, Id, Lit );
                Gie_Replace( &p->F.M, Id, Lit );
            }
            // Dependent cut leaves can make library nodes coincide. Remove
            // any construction debris, also when a build rejected self-reuse.
            Gie_DeleteSince( &p->F.M, NewStart );
            assert( Lit < 0 || p->F.M.nAnds <= OldAnds );
            p->nRewritten += Lit >= 0;
        finish:
            Gie_Finish( &p->F.M, Id );
        }
        if ( fVerbose )
            Abc_Print( 1, "&dc3 pass %d: %d -> %d ANDs (%.3f sec)\n", Round + 1, PrevAnds, p->F.M.nAnds,
                       (double) ( Abc_Clock() - Clock ) / CLOCKS_PER_SEC );
        if ( ppSnapshot && Round == 0 )
        {
            *ppSnapshot = Gie_ManExport( &p->F.M, pGia );
            Vec_PtrPush( vLabels, Dc3_Labels(&p->F.M) );
        }
    }
    Vec_IntFree( vVisit );
    Export = Abc_Clock();
    pNew = Gie_ManExport( &p->F.M, pGia );
    assert( p->F.M.nAnds == Gia_ManAndNum( pNew ) );
    if ( vLabels )
    {
        Vec_Int_t * v;
        int k, j, Entry;
        Vec_PtrPush( vLabels, Dc3_Labels(&p->F.M) );
        Vec_IntFillExtra( vParents, p->F.M.nObjs, -1 );
        Vec_PtrForEachEntry( Vec_Int_t *, vLabels, v, k )
            Vec_IntForEachEntry( v, Entry, j )
                Vec_IntWriteEntry( v, j, Dc3_LabelFind(vParents, Entry) );
        Vec_IntFree( vParents );
    }
    Export = Abc_Clock() - Export;
    if ( fVerbose )
    {
        Abc_Print( 1, "&dc3: ANDs %d -> %d. Rewrites = %d. Merges = %d. Cut limits = %d.\n", Gia_ManAndNum( pGia ),
                   Gia_ManAndNum( pNew ), p->nRewritten, p->nMerged, p->nLimited + p->F.nLimited );
        Abc_Print( 1, "Skipped neighborhoods = %d; recipe hits = %d\n", p->nSkipped, p->nRecipeHits );
        Abc_Print( 1, "&dc3: shape-cache hits %d  resident %d.\n", p->F.nShapeHits, p->F.nShapes );
        Abc_Print( 1, "&dc3: factor-cache hits %d  resident %d. Clears = %d.\n", p->F.nHits, p->F.nCache,
                   p->F.nCacheClears );
        Abc_Print( 1, "&dc3 core: import %.3f  export %.3f  total %.3f sec\n", (double) Setup / CLOCKS_PER_SEC,
                   (double) Export / CLOCKS_PER_SEC, (double) ( Abc_Clock() - Start ) / CLOCKS_PER_SEC );
    }
    ABC_FREE( p->pRecipes );
    ABC_FREE( p->pNeighborhood );
    ABC_FREE( p->pNeighbors );
    Drf_ManRelease( &p->F );
    ABC_FREE( p );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Orders heap literals by level, with deterministic literal tie breaking.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Dcb_Less( Gia_Man_t * p, int a, int b )
{
    int x = Gia_ObjLevelId( p, a >> 1 ), y = Gia_ObjLevelId( p, b >> 1 );
    return x < y || ( x == y && a < b );
}

/**Function*************************************************************

  Synopsis    [Inserts a literal into the balancing heap.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Dcb_HeapPush( Gia_Man_t * p, Vec_Int_t * v, int Lit )
{
    int k = Vec_IntSize( v ), j;
    Vec_IntPush( v, Lit );
    while ( k )
    {
        j = ( k - 1 ) / 2;
        if ( !Dcb_Less( p, Lit, Vec_IntEntry( v, j ) ) ) break;
        Vec_IntWriteEntry( v, k, Vec_IntEntry( v, j ) );
        k = j;
    }
    Vec_IntWriteEntry( v, k, Lit );
}

/**Function*************************************************************

  Synopsis    [Removes an arbitrary literal from the balancing heap.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Dcb_HeapRemove( Gia_Man_t * p, Vec_Int_t * v, int Pos )
{
    int Res = Vec_IntEntry( v, Pos ), Lit = Vec_IntPop( v ), n = Vec_IntSize( v ), k = Pos, j;
    if ( k == n ) return Res;
    if ( k && Dcb_Less( p, Lit, Vec_IntEntry( v, ( k - 1 ) / 2 ) ) )
    {
        while ( k )
        {
            j = ( k - 1 ) / 2;
            if ( !Dcb_Less( p, Lit, Vec_IntEntry( v, j ) ) ) break;
            Vec_IntWriteEntry( v, k, Vec_IntEntry( v, j ) );
            k = j;
        }
    }
    else
        while ( 2 * k + 1 < n )
        {
            j = 2 * k + 1;
            if ( j + 1 < n && Dcb_Less( p, Vec_IntEntry( v, j + 1 ), Vec_IntEntry( v, j ) ) ) j++;
            if ( !Dcb_Less( p, Vec_IntEntry( v, j ), Lit ) ) break;
            Vec_IntWriteEntry( v, k, Vec_IntEntry( v, j ) );
            k = j;
        }
    Vec_IntWriteEntry( v, k, Lit );
    return Res;
}

/**Function*************************************************************

  Synopsis    [Builds a balanced GIA before the mutable optimization passes.]

  Description [Absorbed single-fanout gates are not built separately. Dangling gates
  are removed by the following mutable import, avoiding another GIA copy.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Dcb_Balance( Gia_Man_t * pOld )
{
    Gia_Man_t * pNew = Gia_ManStart( Gia_ManObjNum( pOld ) );
    Gia_Obj_t *o, *f;
    Vec_Int_t *vTodo = Vec_IntAlloc( 128 ), *vHeap = Vec_IntAlloc( 128 ), *vCiLevels;
    int * Refs = ABC_CALLOC( int, Gia_ManObjNum( pOld ) );
    unsigned char * Absorb = ABC_CALLOC( unsigned char, Gia_ManObjNum( pOld ) );
    int i, k, Root, Lit, Var, a, b, Pos, Lev;
    vCiLevels = Gia_ManBoxNum( pOld ) ? Gie_BoxCiLevels( pOld ) : NULL;
    Gia_ManFillValue( pOld );
    Gia_ManConst0( pOld )->Value = 0;
    pNew->pName = Abc_UtilStrsav( pOld->pName );
    pNew->pSpec = Abc_UtilStrsav( pOld->pSpec );
    pNew->vLevels = Vec_IntStart( Gia_ManObjNum( pOld ) );
    Gia_ManForEachCi ( pOld, o, i )
    {
        o->Value = Gia_ManAppendCi( pNew );
        if ( vCiLevels ) Vec_IntWriteEntry( pNew->vLevels, o->Value >> 1, Vec_IntEntry( vCiLevels, i ) );
    }
    Gia_ManForEachObj1 ( pOld, o, i )
    {
        if ( Gia_ObjIsCo( o ) )
            Refs[Gia_ObjFaninId0( o, i )]++;
        else if ( Gia_ObjIsAnd( o ) )
        {
            Refs[Gia_ObjFaninId0( o, i )]++;
            Refs[Gia_ObjFaninId1( o, i )]++;
        }
    }
    Gia_ManForEachAnd ( pOld, o, i )
    {
        a = Gia_ObjFaninLit0( o, i );
        b = Gia_ObjFaninLit1( o, i );
        if ( !( a & 1 ) && Refs[a >> 1] == 1 && Gia_ObjIsAnd( Gia_ManObj( pOld, a >> 1 ) ) ) Absorb[a >> 1] = 1;
        if ( !( b & 1 ) && Refs[b >> 1] == 1 && Gia_ObjIsAnd( Gia_ManObj( pOld, b >> 1 ) ) ) Absorb[b >> 1] = 1;
    }
    Gia_ManHashStart( pNew );
    Gia_ManForEachAnd ( pOld, o, Root )
    {
        if ( Absorb[Root] ) continue;
        Vec_IntClear( vTodo );
        Vec_IntClear( vHeap );
        Vec_IntPush( vTodo, 2 * Root );
        while ( Vec_IntSize( vTodo ) )
        {
            Lit = Vec_IntPop( vTodo );
            Var = Lit >> 1;
            f = Gia_ManObj( pOld, Var );
            if ( Var == Root || ( !( Lit & 1 ) && Absorb[Var] ) )
            {
                Vec_IntPush( vTodo, Gia_ObjFaninLit1( f, Var ) );
                Vec_IntPush( vTodo, Gia_ObjFaninLit0( f, Var ) );
            }
            else
            {
                assert( ~f->Value );
                Dcb_HeapPush( pNew, vHeap, f->Value ^ ( Lit & 1 ) );
            }
        }
        while ( Vec_IntSize( vHeap ) > 1 )
        {
            a = Dcb_HeapRemove( pNew, vHeap, 0 );
            Pos = 0;
            b = Vec_IntEntry( vHeap, 0 );
            Lev = Gia_ObjLevelId( pNew, b >> 1 );
            for ( k = 0; k < Abc_MinInt( 8, Vec_IntSize( vHeap ) ); k++ )
            {
                Lit = Vec_IntEntry( vHeap, k );
                if ( Gia_ObjLevelId( pNew, Lit >> 1 ) != Lev ) continue;
                if ( Gie_Simplify( a, Lit ) >= 0 || Gia_ManHashLookupInt( pNew, a, Lit ) )
                {
                    Pos = k;
                    break;
                }
            }
            b = Dcb_HeapRemove( pNew, vHeap, Pos );
            Lit = Gia_ManHashAnd( pNew, a, b );
            Gia_ObjSetGateLevel( pNew, Gia_ManObj( pNew, Lit >> 1 ) );
            Dcb_HeapPush( pNew, vHeap, Lit );
        }
        o->Value = Vec_IntEntry( vHeap, 0 );
    }
    Gia_ManForEachCo ( pOld, o, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy( o ) );
    Gia_ManHashStop( pNew );
    // The mutable import removes dangling gates without a second GIA copy.
    Vec_IntFree( vTodo );
    Vec_IntFree( vHeap );
    Vec_IntFreeP( &vCiLevels );
    ABC_FREE( Refs );
    ABC_FREE( Absorb );
    Gie_ManDupMetadata( pNew, pOld );

    return pNew;
}

/**Function*************************************************************

  Synopsis    [Orchestrates balancing, rewriting, refactoring, and resubstitution.]

  Description [Returns a new GIA; ownership of the input stays with the caller. The
  default preserves input logic depth, and preserves each timing-box
  interface bound. The final resubstitution uses ten-input windows and at
  most one new gate.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDc3( Gia_Man_t * p, int fKeep, int fVerbose )
{
    Gia_Man_t *q, *r;
    if ( !p || Gia_ManHasChoices( p ) || Gia_ManMuxNum( p ) || Gia_ManXorNum( p ) || Gia_ManBufNum( p ) ) return NULL;
    if ( Gia_ManIsSeqWithBoxes( p ) && !Gia_ManIsNormalized( p ) ) return NULL;
    q = Dcb_Balance( p );
    r = Dc3_Run( q, fKeep, fVerbose, NULL, NULL, 0 );
    Gia_ManStop( q );
    if ( !r ) return NULL;
    q = Rsub_ManPerform( r, 10, 1, 1, fKeep, fVerbose );
    Gia_ManStop( r );
    return q;
}

/**Function*************************************************************

  Synopsis    [Produces fast choice snapshots and their construction proofs.]

  Description [The labels name stable mutable-AIG functions, including polarity.
  Replacements preserve these functions even when their fanout edges change.
  A label of -1 denotes an object without a recorded correspondence. The
  caller owns the snapshots and the label vectors appended to vLabels.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDc3SnapshotsMore( Gia_Man_t * p, int fKeep, int fVerbose, Gia_Man_t ** ppSnapshot, Vec_Ptr_t * vLabels, int fMore )
{
    Gia_Man_t * q, * r;
    Gia_Obj_t * pObj;
    Vec_Int_t * v;
    int i;
    if ( ppSnapshot ) *ppSnapshot = NULL;
    if ( !p || !vLabels || Vec_PtrSize(vLabels) || Gia_ManHasChoices(p) ||
         Gia_ManMuxNum(p) || Gia_ManXorNum(p) || Gia_ManBufNum(p) ) return NULL;
    if ( Gia_ManIsSeqWithBoxes(p) && !Gia_ManIsNormalized(p) ) return NULL;
    if ( Gia_ManObjNum(p) > Gie_ObjectLimit() / 2 ) return NULL;
    q = Dcb_Balance( p );
    v = Vec_IntStartFull( Gia_ManObjNum(p) );
    Gia_ManForEachObj( p, pObj, i )
        if ( !Gia_ObjIsCo(pObj) ) Vec_IntWriteEntry( v, i, (int)pObj->Value );
    Vec_PtrPush( vLabels, v );
    r = Dc3_Run( q, fKeep, fVerbose, ppSnapshot, vLabels, fMore );
    Gia_ManStop( q );
    return r;
}

/**Function*************************************************************

  Synopsis    [Produces snapshots with the original choice-synthesis effort.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDc3Snapshots( Gia_Man_t * p, int fKeep, int fVerbose, Gia_Man_t ** ppSnapshot, Vec_Ptr_t * vLabels )
{
    return Gia_ManDc3SnapshotsMore( p, fKeep, fVerbose, ppSnapshot, vLabels, 0 );
}

ABC_NAMESPACE_IMPL_END
