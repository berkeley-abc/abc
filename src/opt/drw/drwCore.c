/**CFile****************************************************************

  FileName    [drwCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Compact DAG-aware AIG rewriting.]

  Synopsis    [Mutable AIG rewriting using one cut and deferred levels.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: drwCore.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "drwInt.h"
#include "drwGia.h"
#include <limits.h>
#include "misc/util/utilTruth.h"
#include "misc/tim/tim.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

enum { DRW_DEAD, DRW_CONST, DRW_CI, DRW_AND, DRW_CO };
// Bound the frontier search and the fast complete-MFFC walk. The library
// limit covers its largest class; two priority roots precede the fallback.
enum { DRW_CUT_LIMIT = 128, DRW_LIB_LIMIT = 256, DRW_SUBGRAPH_LIMIT = 2, DRW_MFFC_LIMIT = 32 };

typedef struct Drw_Obj_t_ Drw_Obj_t;
typedef struct Drw_Cut_t_ Drw_Cut_t;
typedef struct Drw_Man_t_ Drw_Man_t;

struct Drw_Obj_t_
{
    int Fan[2];                    // complemented-edge literals
    int Refs;                      // live fanout edges, temporarily adjusted for cuts
    int Hash;                      // next node in the structural hash bucket
    int Level;
    unsigned Mark;
    unsigned TruthMark;
    unsigned short Truth;
    unsigned char Type;
    unsigned char Handled : 1;
    unsigned char Inside : 1;
    unsigned char Hashed : 1;
    unsigned char Buffer : 1;
};

typedef struct Drw_Fan_t_
{
    int Next[2];                   // intrusive fanout links for this node's inputs
    int Prev[2];
    int Head;                      // first edge using this node
    int Required;
} Drw_Fan_t;

struct Drw_Cut_t_
{
    int Leaves[4];
    int nLeaves;
    int Saved;
    unsigned Truth;
    int fFullSupport;
};

typedef struct Drw_Cuts_t_
{
    Drw_Cut_t Cuts[DRW_CUT_LIMIT];
    unsigned Hash[DRW_CUT_LIMIT];
    int Links[DRW_CUT_LIMIT];
    int Table[64];
    int nCuts;
    int BestSaved;
    int fFull;
} Drw_Cuts_t;

struct Drw_Man_t_
{
    Drw_Obj_t * pObjs;
    Drw_Fan_t * pFans;
    int * pHash;
    int nObjs;
    int nCap;
    int nObjLimit;
    int nOrig;
    int nAnds;
    int nHashMask;
    int nLevelMax;
    int fKeepLevel;
    int iRoot;                     // root excluded from construction-time sharing
    unsigned Mark;
    unsigned TruthMark;
    int fFullMark;
    Vec_Int_t * vCis;
    Vec_Int_t * vCos;
    Vec_Int_t * vStack;
    Vec_Int_t * vOrder;
    int LibLits[DRW_LIB_LIMIT];
    int LibLevels[DRW_LIB_LIMIT];
    int LibSeen[DRW_LIB_LIMIT];
    word LibCosts[DRW_LIB_LIMIT];
    const Drw_LibClass_t * pClass;
    abctime timeCuts;
    abctime timeEval;
    abctime timeUpdate;
    double nCuts;
    int nLimited;
    int nRewritten;
    int nMerged;
};

static Drw_Gia_t * s_pDrwGiaCapture;
static void Drw_GiaCapture( Drw_Cut_t * pCut );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

static inline void Drw_TruthNext( Drw_Man_t * p )
{
    int i;
    if ( ++p->TruthMark ) return;
    for ( i = 0; i < p->nObjs; i++ ) p->pObjs[i].TruthMark = 0;
    p->TruthMark = 1;
}

static inline unsigned Drw_HashKey( Drw_Man_t * p, int a, int b )
{
    // Symmetric mixing avoids sorting the two fanin literals.
    word h = (word)(unsigned)a * (unsigned)b;
    h ^= ((word)(unsigned)a + (unsigned)b) * ABC_CONST(0x9e3779b97f4a7c15);
    return (unsigned)(h ^ (h >> 32)) & p->nHashMask;
}

static inline int Drw_Simplify( int a, int b )
{
    if ( a == b ) return a;
    if ( a == (b ^ 1) || a == 0 || b == 0 ) return 0;
    if ( a == 1 ) return b;
    if ( b == 1 ) return a;
    return -1;
}

static inline int Drw_Lookup( Drw_Man_t * p, int a, int b, int Skip )
{
    int i, Lit = Drw_Simplify( a, b );
    if ( Lit >= 0 ) return Lit;
    for ( i = p->pHash[Drw_HashKey(p,a,b)]; i; i = p->pObjs[i].Hash )
        if ( i != Skip && ((p->pObjs[i].Fan[0] == a && p->pObjs[i].Fan[1] == b) ||
                           (p->pObjs[i].Fan[0] == b && p->pObjs[i].Fan[1] == a)) )
            return 2*i;
    return -1;
}

static inline void Drw_HashInsert( Drw_Man_t * p, int Id )
{
    unsigned Key = Drw_HashKey( p, p->pObjs[Id].Fan[0], p->pObjs[Id].Fan[1] );
    p->pObjs[Id].Hash = p->pHash[Key];
    p->pHash[Key] = Id;
    p->pObjs[Id].Hashed = 1;
}

static inline void Drw_HashRemove( Drw_Man_t * p, int Id )
{
    int * pLink;
    if ( !p->pObjs[Id].Hashed ) return;
    pLink = p->pHash + Drw_HashKey( p, p->pObjs[Id].Fan[0], p->pObjs[Id].Fan[1] );
    while ( *pLink != Id )
    {
        assert( *pLink );
        pLink = &p->pObjs[*pLink].Hash;
    }
    *pLink = p->pObjs[Id].Hash;
    p->pObjs[Id].Hashed = 0;
}

/**Function*************************************************************

  Synopsis    [Indexes a node once both fanins have finished.]

  Description [Ready nodes have exact levels and immutable fanins. They
  can be reused before their visit without hashing all original nodes.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Drw_Ready( Drw_Man_t * p, int Id )
{
    Drw_Obj_t * pObj = p->pObjs + Id;
    if ( pObj->Type != DRW_AND || pObj->Hashed ||
         !p->pObjs[pObj->Fan[0] >> 1].Handled || !p->pObjs[pObj->Fan[1] >> 1].Handled ) return;
    pObj->Level = !pObj->Buffer + Abc_MaxInt(p->pObjs[pObj->Fan[0] >> 1].Level, p->pObjs[pObj->Fan[1] >> 1].Level);
    Drw_HashInsert(p, Id);
}

/**Function*************************************************************

  Synopsis    [Finishes a kept or reused node and indexes ready fanouts.]

  Description [A hash match already has finished fanins. Promotion is
  nonrecursive; the node enters the export order and skips its later visit.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Drw_Finish( Drw_Man_t * p, int Id )
{
    Drw_Obj_t * pObj = p->pObjs + Id;
    int Edge;
    if ( pObj->Handled ) return;
    assert(pObj->Type == DRW_AND && pObj->Hashed);
    assert(p->pObjs[pObj->Fan[0] >> 1].Handled && p->pObjs[pObj->Fan[1] >> 1].Handled);
    pObj->Handled = 1;
    Vec_IntPush(p->vOrder, Id);
    for ( Edge = p->pFans[Id].Head; Edge; Edge = p->pFans[Edge >> 1].Next[Edge & 1] )
        Drw_Ready(p, Edge >> 1);
}

static inline void Drw_Link( Drw_Man_t * p, int Id, int Pin )
{
    int Var = p->pObjs[Id].Fan[Pin] >> 1;
    int Edge = 2*Id + Pin;
    int Head = p->pFans[Var].Head;
    p->pFans[Id].Next[Pin] = Head;
    p->pFans[Id].Prev[Pin] = 0;
    if ( Head ) p->pFans[Head >> 1].Prev[Head & 1] = Edge;
    p->pFans[Var].Head = Edge;
    p->pObjs[Var].Refs++;
}

static inline int Drw_Unlink( Drw_Man_t * p, int Id, int Pin )
{
    int Var = p->pObjs[Id].Fan[Pin] >> 1;
    int Prev = p->pFans[Id].Prev[Pin], Next = p->pFans[Id].Next[Pin];
    if ( Prev ) p->pFans[Prev >> 1].Next[Prev & 1] = Next;
    else p->pFans[Var].Head = Next;
    if ( Next ) p->pFans[Next >> 1].Prev[Next & 1] = Prev;
    assert( p->pObjs[Var].Refs > 0 );
    p->pObjs[Var].Refs--;
    return Var;
}

/**Function*************************************************************

  Synopsis    [Allocates one mutable AIG object and attaches its edges.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Drw_Append( Drw_Man_t * p, int Type, int a, int b )
{
    int Id = p->nObjs++;
    Drw_Obj_t * pObj;
    if ( p->nObjs > p->nCap )
    {
        p->nCap = p->nCap > p->nObjLimit/2 ? p->nObjLimit : 2*p->nCap;
        p->pObjs = ABC_REALLOC( Drw_Obj_t, p->pObjs, p->nCap );
        p->pFans = ABC_REALLOC( Drw_Fan_t, p->pFans, p->nCap );
    }
    pObj = p->pObjs + Id;
    memset( pObj, 0, sizeof(Drw_Obj_t) );
    memset(p->pFans + Id, 0, sizeof(Drw_Fan_t));
    pObj->Type = (unsigned char)Type;
    pObj->Fan[0] = a;
    pObj->Fan[1] = b;
    p->pFans[Id].Required = ABC_INFINITY;
    if ( Type == DRW_AND )
    {
        Drw_Link( p, Id, 0 );
        Drw_Link( p, Id, 1 );
        // New gates have finished fanins and finish immediately. Original
        // gates are indexed separately when their fanins have finished.
        if ( p->nOrig )
        {
            assert(p->pObjs[a >> 1].Handled && p->pObjs[b >> 1].Handled);
            Drw_HashInsert( p, Id );
            p->pObjs[Id].Handled = 1;
            Vec_IntPush( p->vOrder, Id );
        }
        p->pObjs[Id].Level = 1 + Abc_MaxInt(p->pObjs[a >> 1].Level, p->pObjs[b >> 1].Level);
        p->nAnds++;
    }
    else if ( Type == DRW_CO ) Drw_Link( p, Id, 0 );
    else pObj->Handled = 1;
    return Id;
}

/**Function*************************************************************

  Synopsis    [Structurally hashes an AND of two literals.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Drw_And( Drw_Man_t * p, int a, int b )
{
    int Lit = Drw_Lookup( p, a, b, -1 );
    if ( Lit >= 0 )
    {
        if ( (Lit >> 1) == p->iRoot ) return -1;
        Drw_Finish(p, Lit >> 1);
        return Lit;
    }
    return 2 * Drw_Append( p, DRW_AND, a, b );
}

/**Function*************************************************************

  Synopsis    [Deletes dangling nodes without recursive stack growth.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Drw_Delete( Drw_Man_t * p, int Id )
{
    Vec_IntClear( p->vStack );
    Vec_IntPush( p->vStack, Id );
    while ( Vec_IntSize(p->vStack) )
    {
        int i, Var;
        Id = Vec_IntPop( p->vStack );
        if ( p->pObjs[Id].Type != DRW_AND || p->pObjs[Id].Refs ) continue;
        Drw_HashRemove( p, Id );
        for ( i = 0; i < 2; i++ )
        {
            Var = Drw_Unlink( p, Id, i );
            if ( p->pObjs[Var].Refs == 0 && p->pObjs[Var].Type == DRW_AND )
                Vec_IntPush( p->vStack, Var );
        }
        p->pObjs[Id].Type = DRW_DEAD;
        p->pObjs[Id].Handled = 1;
        p->nAnds--;
    }
}

/**Function*************************************************************

  Synopsis    [Redirects unhandled fanouts and deletes the old cone.]

  Description [The current root stays unhandled until it is kept. Its
  consumers are therefore unhandled and unhashed. Redirecting an edge may
  make a consumer ready, but needs neither rehashing nor a level sweep.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Drw_Replace( Drw_Man_t * p, int Old, int Lit )
{
    int Edge, Id, Pin, Head = p->pFans[Old].Head, Tail = 0;
    assert( (Lit >> 1) != Old );
    p->pObjs[Lit >> 1].Refs++;
    for ( Edge = Head; Edge; Edge = p->pFans[Edge >> 1].Next[Edge & 1] )
    {
        Tail = Edge;
        Id = Edge >> 1;
        Pin = Edge & 1;
        assert( !p->pObjs[Id].Handled && !p->pObjs[Id].Hashed );
        p->pObjs[Id].Fan[Pin] = Lit ^ (p->pObjs[Id].Fan[Pin] & 1);
        Drw_Ready(p, Id);
    }
    if ( Tail )
    {
        int Next = p->pFans[Lit >> 1].Head;
        p->pFans[Tail >> 1].Next[Tail & 1] = Next;
        if ( Next ) p->pFans[Next >> 1].Prev[Next & 1] = Tail;
        p->pFans[Lit >> 1].Head = Head;
        p->pObjs[Lit >> 1].Refs += p->pObjs[Old].Refs;
        p->pFans[Old].Head = p->pObjs[Old].Refs = 0;
    }
    Drw_Delete( p, Old );
    p->pObjs[Lit >> 1].Refs--;
}

/**Function*************************************************************

  Synopsis    [Pushes onto scratch storage with a caller-local stack size.]

  Description [The shared vector's size remains zero between traversals.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Drw_StackPush( Vec_Int_t * vStack, int * pnStack, int Id )
{
    if ( *pnStack == Vec_IntCap(vStack) ) Vec_IntGrow(vStack, 2*Vec_IntCap(vStack));
    Vec_IntArray(vStack)[(*pnStack)++] = Id;
}

/**Function*************************************************************

  Synopsis    [Counts the removable MFFC using virtual dereferencing.]

  Description [Process the root directly; most traversals need no stack.
  An explicit stack also handles deep cones exposed by support minimization.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Drw_Deref( Drw_Man_t * p, int Id, int fMark )
{
    int i, Var, Count = 0, nStack = 0;
    if ( p->pObjs[Id].Type != DRW_AND ) return 0;
    for ( ;; )
    {
        Count++;
        if ( fMark ) p->pObjs[Id].Mark = p->Mark;
        for ( i = 0; i < 2; i++ )
        {
            Var = p->pObjs[Id].Fan[i] >> 1;
            if ( p->pObjs[Var].Type != DRW_AND ) continue;
            assert(p->pObjs[Var].Refs > 0);
            if ( --p->pObjs[Var].Refs == 0 ) Drw_StackPush(p->vStack, &nStack, Var);
        }
        if ( !nStack ) break;
        Id = Vec_IntArray(p->vStack)[--nStack];
    }
    return Count;
}

/**Function*************************************************************

  Synopsis    [Restores references after virtual dereferencing.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Drw_Ref( Drw_Man_t * p, int Id )
{
    int i, Var, nStack = 0;
    if ( p->pObjs[Id].Type != DRW_AND ) return;
    for ( ;; )
    {
        for ( i = 0; i < 2; i++ )
        {
            Var = p->pObjs[Id].Fan[i] >> 1;
            if ( p->pObjs[Var].Type != DRW_AND ) continue;
            if ( p->pObjs[Var].Refs++ == 0 ) Drw_StackPush(p->vStack, &nStack, Var);
        }
        if ( !nStack ) break;
        Id = Vec_IntArray(p->vStack)[--nStack];
    }
}

/**Function*************************************************************

  Synopsis    [Counts and optionally marks an MFFC with protected cut leaves.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Drw_Mffc( Drw_Man_t * p, int Id, Drw_Cut_t * pCut, int fMark )
{
    int i, Saved;
    for ( i = 0; i < pCut->nLeaves; i++ ) if ( p->pObjs[pCut->Leaves[i]].Type == DRW_AND ) p->pObjs[pCut->Leaves[i]].Refs++;
    if ( fMark ) p->Mark++;
    Saved = Drw_Deref( p, Id, fMark );
    Drw_Ref( p, Id );
    for ( i = 0; i < pCut->nLeaves; i++ ) if ( p->pObjs[pCut->Leaves[i]].Type == DRW_AND ) p->pObjs[pCut->Leaves[i]].Refs--;
    return Saved;
}

/**Function*************************************************************

  Synopsis    [Evaluates a cut cone using stamped 16-bit truth tables.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static unsigned Drw_Truth_rec( Drw_Man_t * p, int Id )
{
    unsigned a, b;
    int Fan0, Fan1;
    if ( Id == 0 ) return 0;
    if ( p->pObjs[Id].TruthMark == p->TruthMark ) return p->pObjs[Id].Truth;
    assert( p->pObjs[Id].Type == DRW_AND );
    Fan0 = p->pObjs[Id].Fan[0];
    Fan1 = p->pObjs[Id].Fan[1];
    a = Drw_Truth_rec( p, Fan0 >> 1 ) ^ ((Fan0 & 1) ? 65535u : 0);
    b = Drw_Truth_rec( p, Fan1 >> 1 ) ^ ((Fan1 & 1) ? 65535u : 0);
    p->pObjs[Id].TruthMark = p->TruthMark;
    return p->pObjs[Id].Truth = (unsigned short)(a & b);
}

/**Function*************************************************************

  Synopsis    [Assigns cut variables and evaluates the root truth table.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static unsigned Drw_Truth( Drw_Man_t * p, int Id, Drw_Cut_t * pCut )
{
    static const unsigned short Truths[4] = { 0xAAAA, 0xCCCC, 0xF0F0, 0xFF00 };
    int i;
    Drw_TruthNext( p );
    for ( i = 0; i < pCut->nLeaves; i++ )
    {
        p->pObjs[pCut->Leaves[i]].TruthMark = p->TruthMark;
        p->pObjs[pCut->Leaves[i]].Truth = Truths[i];
    }
    return Drw_Truth_rec( p, Id );
}

/**Function*************************************************************

  Synopsis    [Removes functionally unused cut inputs.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Drw_CutMinimize( Drw_Cut_t * pCut )
{
    static const unsigned Masks[4] = { 0x5555, 0x3333, 0x0F0F, 0x00FF };
    int i, j;
    unsigned t = pCut->Truth;
    if ( s_pDrwGiaCapture ) Drw_GiaCapture(pCut);
    for ( i = 0; i < pCut->nLeaves; i++ )
    {
        if ( ((t >> (1 << i)) ^ t) & Masks[i] ) continue;
        for ( j = i; j < pCut->nLeaves-1; j++ )
        {
            if ( j == 0 ) t = (t & 0x9999u) | ((t & 0x2222u) << 1) | ((t & 0x4444u) >> 1);
            else if ( j == 1 ) t = (t & 0xC3C3u) | ((t & 0x0C0Cu) << 2) | ((t & 0x3030u) >> 2);
            else t = (t & 0xF00Fu) | ((t & 0x00F0u) << 4) | ((t & 0x0F00u) >> 4);
            pCut->Leaves[j] = pCut->Leaves[j+1];
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
static int Drw_FullCut( Drw_Man_t * p, int Id, Drw_Cut_t * pCut )
{
    static const unsigned short Truths[4] = { 0xAAAA, 0xCCCC, 0xF0F0, 0xFF00 };
    int * pNodes = Vec_IntArray(p->vStack), * pLeaves = pNodes+DRW_MFFC_LIMIT;
    int i, k, j, nNodes = 1, nCandidates = 0, nLeaves = 0, nCis = 0, Var;
    assert(Vec_IntCap(p->vStack) >= 3*DRW_MFFC_LIMIT);
    p->Mark++;
    Drw_TruthNext( p );
    pNodes[0] = Id;
    p->pObjs[Id].Mark = p->Mark;
    // Local edge counts determine the removable region without changing
    // live references. A fanin enters the queue only after all its users.
    for ( i = 0; i < nNodes; i++ )
    for ( k = 0; k < 2; k++ )
    {
        Drw_Obj_t * pFan;
        Var = p->pObjs[pNodes[i]].Fan[k] >> 1;
        if ( !Var ) continue;
        pFan = p->pObjs+Var;
        if ( pFan->TruthMark != p->TruthMark )
        {
            pFan->TruthMark = p->TruthMark;
            pFan->Truth = 0;
            // CIs cannot leave the boundary during further MFFC expansion.
            if ( pFan->Type == DRW_CI && ++nCis > 4 ) return 0;
            pLeaves[nCandidates++] = Var;
            nLeaves++;
        }
        if ( pFan->Type != DRW_AND || ++pFan->Truth != pFan->Refs ) continue;
        if ( nNodes == DRW_MFFC_LIMIT ) return 0;
        pFan->Mark = p->Mark;
        pNodes[nNodes++] = Var;
        nLeaves--;
    }
    if ( nLeaves > 4 ) return 0;
    pCut->Saved = nNodes;
    pCut->nLeaves = 0;
    for ( i = 0; i < nCandidates; i++ )
        if ( p->pObjs[pLeaves[i]].Mark != p->Mark ) pCut->Leaves[pCut->nLeaves++] = pLeaves[i];
    assert(pCut->nLeaves == nLeaves);
    for ( i = 1; i < nLeaves; i++ )
        for ( j = i; j > 0 && pCut->Leaves[j] < pCut->Leaves[j-1]; j-- )
            ABC_SWAP(int, pCut->Leaves[j], pCut->Leaves[j-1]);
    // The same queue, reversed, is a topological truth-table program.
    p->pObjs[0].Truth = 0;
    for ( i = 0; i < nLeaves; i++ ) p->pObjs[pCut->Leaves[i]].Truth = Truths[i];
    for ( i = nNodes-1; i >= 0; i-- )
    {
        int Node = pNodes[i], a = p->pObjs[Node].Fan[0], b = p->pObjs[Node].Fan[1];
        p->pObjs[Node].Truth = (unsigned short)((p->pObjs[a >> 1].Truth ^ ((a & 1) ? 65535u : 0)) &
                                              (p->pObjs[b >> 1].Truth ^ ((b & 1) ? 65535u : 0)));
    }
    pCut->Truth = p->pObjs[Id].Truth;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Tests immediate overlap when breaking maximum-MFFC ties.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Drw_LeavesOverlap( Drw_Man_t * p, int a, int b )
{
    int a0 = -1, a1 = -1, b0, b1;
    if ( p->pObjs[a].Type == DRW_AND )
    {
        a0 = p->pObjs[a].Fan[0] >> 1;
        a1 = p->pObjs[a].Fan[1] >> 1;
        if ( a0 == b || a1 == b ) return 1;
    }
    if ( p->pObjs[b].Type == DRW_AND )
    {
        b0 = p->pObjs[b].Fan[0] >> 1;
        b1 = p->pObjs[b].Fan[1] >> 1;
        if ( b0 == a || b1 == a ) return 1;
        if ( p->pObjs[a].Type == DRW_AND && (a0 == b0 || a0 == b1 || a1 == b0 || a1 == b1) ) return 1;
    }
    return 0;
}

static inline unsigned Drw_CutHash( int Id )
{
    unsigned h = (unsigned)Id * 123456791u;
    return h ^ (h >> 16);
}

/**Function*************************************************************

  Synopsis    [Enumerates bounded frontier expansions with shared MFFC updates.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Drw_CutsExplore_rec( Drw_Man_t * p, Drw_Cuts_t * pCuts, Drw_Cut_t * pCut, unsigned Hash )
{
    Drw_Cut_t New;
    int k, i, j, Var, Fan, n, Id, Added[2], nAdded, Saved;
    pCuts->BestSaved = Abc_MaxInt(pCuts->BestSaved, pCut->Saved);
    for ( k = 0; k < pCut->nLeaves && pCuts->nCuts < DRW_CUT_LIMIT; k++ )
    {
        unsigned NewHash = Hash;
        Var = pCut->Leaves[k];
        if ( p->pObjs[Var].Type != DRW_AND ) continue;
        for ( i = n = 0; i < pCut->nLeaves; i++ ) if ( i != k ) New.Leaves[n++] = pCut->Leaves[i];
        NewHash ^= Drw_CutHash(Var);
        nAdded = 0;
        for ( i = 0; i < 2; i++ )
        {
            Fan = p->pObjs[Var].Fan[i] >> 1;
            if ( Fan == 0 || p->pObjs[Fan].Inside ) continue;
            for ( j = 0; j < n; j++ ) if ( New.Leaves[j] == Fan ) break;
            if ( j < n ) continue;
            if ( n == 4 ) break;
            New.Leaves[n++] = Fan;
            Added[nAdded++] = Fan;
            NewHash ^= Drw_CutHash(Fan);
        }
        if ( i < 2 ) continue;
        for ( i = 1; i < n; i++ )
            for ( j = i; j > 0 && New.Leaves[j] < New.Leaves[j-1]; j-- )
                ABC_SWAP(int, New.Leaves[j], New.Leaves[j-1]);
        New.nLeaves = n;
        for ( i = pCuts->Table[NewHash & 63]; i; i = pCuts->Links[i] )
            if ( pCuts->Hash[i] == NewHash && pCuts->Cuts[i].nLeaves == n &&
                !memcmp(pCuts->Cuts[i].Leaves, New.Leaves, n*sizeof(int)) ) break;
        if ( i ) continue;
        Id = pCuts->nCuts++;
        pCuts->Links[Id] = pCuts->Table[NewHash & 63];
        pCuts->Table[NewHash & 63] = Id;
        pCuts->Hash[Id] = NewHash;
        Saved = 0;
        if ( !pCuts->fFull )
        {
            for ( i = 0; i < nAdded; i++ ) if ( p->pObjs[Added[i]].Type == DRW_AND ) p->pObjs[Added[i]].Refs++;
            assert(p->pObjs[Var].Refs > 0);
            Saved = --p->pObjs[Var].Refs == 0 ? Drw_Deref(p, Var, 0) : 0;
        }
        New.Saved = pCut->Saved + Saved;
        New.fFullSupport = pCut->fFullSupport && nAdded == 2;
        pCuts->Cuts[Id] = New;
        p->pObjs[Var].Inside = 1;
        Drw_CutsExplore_rec(p, pCuts, pCuts->Cuts+Id, NewHash);
        p->pObjs[Var].Inside = 0;
        if ( !pCuts->fFull )
        {
            if ( p->pObjs[Var].Refs++ == 0 ) Drw_Ref(p, Var);
            for ( i = 0; i < nAdded; i++ ) if ( p->pObjs[Added[i]].Type == DRW_AND ) p->pObjs[Added[i]].Refs--;
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
static int Drw_SelectCut( Drw_Man_t * p, int Id, Drw_Cut_t * pBest )
{
    Drw_Cuts_t Cuts;
    Drw_Cut_t * pCut;
    unsigned Hash = 0;
    int i, Fan, fFull, BestSize = INT_MAX, BestRefs = -1;
    p->fFullMark = fFull = Drw_FullCut(p, Id, pBest);
    if ( fFull )
    {
        static const unsigned Masks[4] = { 0x5555, 0x3333, 0x0F0F, 0x00FF };
        int fExpand = 0, fOverlap = pBest->nLeaves > 3, k, j;
        // A small complete boundary already maximizes the removable MFFC.
        // Keep boundaries of up to two leaves, including sharing-only XORs;
        // also keep any boundary with an improving standalone graph.
        if ( pBest->nLeaves <= 2 || Drw_MinSizes[pBest->Truth] < pBest->Saved )
        {
            Drw_CutMinimize(pBest);
            p->nCuts++;
            return 1;
        }
        for ( i = 0; i < pBest->nLeaves && !fExpand; i++ )
        {
            int Leaf = pBest->Leaves[i];
            if ( p->pObjs[Leaf].Type != DRW_AND ) continue;
            if ( pBest->nLeaves < 4 ) { fExpand = 1; break; }
            for ( k = 0; k < 2; k++ )
            {
                int FanId = p->pObjs[Leaf].Fan[k] >> 1;
                if ( !FanId ) fExpand = 1;
                for ( j = 0; j < pBest->nLeaves; j++ ) if ( pBest->Leaves[j] == FanId ) fExpand = 1;
            }
        }
        if ( fExpand && !fOverlap )
            for ( i = 0; i < pBest->nLeaves; i++ )
                for ( j = i+1; j < pBest->nLeaves; j++ )
                    fOverlap |= Drw_LeavesOverlap(p, pBest->Leaves[i], pBest->Leaves[j]);
        if ( !fExpand || !fOverlap )
        {
            Drw_CutMinimize(pBest);
            p->nCuts++;
            return 1;
        }
        pBest->fFullSupport = 1;
        for ( i = 0; i < pBest->nLeaves; i++ )
            if ( !(((pBest->Truth >> (1 << i)) ^ pBest->Truth) & Masks[i]) ) pBest->fFullSupport = 0;
    }
    memset(Cuts.Table, 0, sizeof(Cuts.Table));
    Cuts.nCuts = 2;
    Cuts.BestSaved = 0;
    Cuts.fFull = fFull;
    pCut = Cuts.Cuts+1;
    if ( fFull ) *pCut = *pBest;
    else
    {
        pCut->nLeaves = 0;
        pCut->fFullSupport = 1;
        for ( i = 0; i < 2; i++ )
        {
            Fan = p->pObjs[Id].Fan[i] >> 1;
            if ( !Fan || (pCut->nLeaves && Fan == pCut->Leaves[0]) ) continue;
            pCut->Leaves[pCut->nLeaves++] = Fan;
        }
        if ( pCut->nLeaves == 2 && pCut->Leaves[0] > pCut->Leaves[1] ) ABC_SWAP(int, pCut->Leaves[0], pCut->Leaves[1]);
    }
    memset(pBest, 0, sizeof(Drw_Cut_t));
    for ( i = 0; i < pCut->nLeaves; i++ )
    {
        Fan = pCut->Leaves[i];
        if ( !fFull && p->pObjs[Fan].Type == DRW_AND ) p->pObjs[Fan].Refs++;
        Hash ^= Drw_CutHash(Fan);
    }
    if ( !fFull ) pCut->Saved = Drw_Deref(p, Id, 0);
    Cuts.Table[Hash & 63] = 1;
    Cuts.Hash[1] = Hash;
    Cuts.Links[1] = 0;
    p->pObjs[Id].Inside = 1;
    Drw_CutsExplore_rec(p, &Cuts, pCut, Hash);
    p->pObjs[Id].Inside = 0;
    if ( !fFull )
    {
        Drw_Ref(p, Id);
        for ( i = 0; i < pCut->nLeaves; i++ ) if ( p->pObjs[pCut->Leaves[i]].Type == DRW_AND ) p->pObjs[pCut->Leaves[i]].Refs--;
    }
    for ( i = 1; i < Cuts.nCuts; i++ )
    {
        int Size, j, Refs = 0;
        pCut = Cuts.Cuts+i;
        if ( pCut->Saved != Cuts.BestSaved ) continue;
        for ( j = 0; j < pCut->nLeaves; j++ ) Refs += p->pObjs[pCut->Leaves[j]].Refs;
        if ( pCut->fFullSupport && (pCut->nLeaves-1 > BestSize ||
            (pCut->nLeaves-1 == BestSize && (pCut->nLeaves > pBest->nLeaves || (pCut->nLeaves == pBest->nLeaves && Refs <= BestRefs)))) ) continue;
        if ( !fFull || i != 1 ) pCut->Truth = Drw_Truth(p, Id, pCut);
        Size = Drw_MinSizes[pCut->Truth];
        if ( Size < BestSize || (Size == BestSize && (pCut->nLeaves < pBest->nLeaves || (pCut->nLeaves == pBest->nLeaves && Refs > BestRefs))) )
        {
            *pBest = *pCut;
            BestSize = Size;
            BestRefs = Refs;
        }
    }
    p->nCuts += Cuts.nCuts-1;
    p->nLimited += Cuts.nCuts == DRW_CUT_LIMIT;
    i = pBest->nLeaves;
    Drw_CutMinimize(pBest);
    if ( i != pBest->nLeaves )
    {
        // Keep the removal count and reuse marks tied to the final support.
        pBest->Saved = Drw_Mffc(p, Id, pBest, 1);
        p->fFullMark = 1;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Counts unmatched library nodes, stopping at the cost limit.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Drw_LibCount_rec( Drw_Man_t * p, int Id, int Visit, int Limit )
{
    int a, b, Count, Lit;
    if ( Id < 4 || p->LibSeen[Id] == Visit ) return 0;
    p->LibSeen[Id] = Visit;
    Lit = p->LibLits[Id];
    if ( Lit == -2 ) return DRW_LIB_LIMIT;
    if ( Lit >= 0 && p->pObjs[Lit >> 1].Mark != p->Mark ) return 0;
    if ( Limit < 1 ) return DRW_LIB_LIMIT;
    a = Drw_LibNodes[p->pClass->iNodes + Id - 4][0] >> 1;
    b = Drw_LibNodes[p->pClass->iNodes + Id - 4][1] >> 1;
    Count = 1 + Drw_LibCount_rec( p, a, Visit, Limit-1 );
    if ( Count > Limit ) return DRW_LIB_LIMIT;
    return Count + Drw_LibCount_rec( p, b, Visit, Limit-Count );
}

/**Function*************************************************************

  Synopsis    [Builds only the selected library graph.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Drw_LibBuild_rec( Drw_Man_t * p, int Id )
{
    int a, b, Lit0, Lit1;
    if ( p->LibLits[Id] >= 0 )
    {
        Drw_Finish(p, p->LibLits[Id] >> 1);
        return p->LibLits[Id];
    }
    assert( Id >= 4 && p->LibLits[Id] != -2 );
    a = Drw_LibNodes[p->pClass->iNodes + Id - 4][0];
    b = Drw_LibNodes[p->pClass->iNodes + Id - 4][1];
    Lit0 = Drw_LibBuild_rec( p, a >> 1 );
    if ( Lit0 < 0 ) return -1;
    Lit1 = Drw_LibBuild_rec( p, b >> 1 );
    if ( Lit1 < 0 ) return -1;
    return p->LibLits[Id] = Drw_And( p, Lit0 ^ (a & 1), Lit1 ^ (b & 1) );
}

/**Function*************************************************************

  Synopsis    [Evaluates library structures for the single selected cut.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Drw_Evaluate( Drw_Man_t * p, int Id, Drw_Cut_t * pCut )
{
    unsigned Transform;
    int i, k, nPrepared = 4, nInitial, fUseBits, nRoots, fShared = 0, nNodes = 4, Best = -1, BestCost = pCut->Saved, BestLevel = ABC_INFINITY;
    int Required = p->fKeepLevel ? p->pFans[Id].Required : ABC_INFINITY;
    static const unsigned Truths[4] = { 0xAAAA, 0xCCCC, 0xF0F0, 0xFF00 };
    p->iRoot = Id;
    if ( pCut->Truth == 0 || pCut->Truth == 65535 ) return pCut->Truth != 0;
    for ( i = 0; i < pCut->nLeaves; i++ )
        if ( pCut->Truth == Truths[i] || pCut->Truth == (Truths[i] ^ 65535) )
            return 2*pCut->Leaves[i] + (pCut->Truth != Truths[i]);
    Transform = Drw_Transforms[pCut->Truth];
    p->pClass = Drw_Classes + (Transform & 255);
    if ( !p->pClass->nRoots ) return -1;

    assert( p->pClass->nNodes + 4 <= DRW_LIB_LIMIT );
    if ( !p->fFullMark )
    {
        i = Drw_Mffc( p, Id, pCut, 1 );
        assert( i == pCut->Saved );
    }
    nRoots = p->pClass->nRoots;
    for ( i = 0; i < 4; i++ )
    {
        int Pos = (Transform >> (13+2*i)) & 3;
        p->LibLits[i] = (Pos < pCut->nLeaves ? 2*pCut->Leaves[Pos] : 0) ^ ((Transform >> (8+i)) & 1);
        p->LibLevels[i] = p->pObjs[p->LibLits[i] >> 1].Level;
    }
    // Use a feasible standalone graph when the library already offers a
    // gain. Otherwise, sharing requires an external variable-pair gate:
    // an existing internal graph brings all its fanin gates with it.
    for ( i = 0; pCut->Saved <= p->pClass->MinSize && i < p->pClass->nPairs; i++ )
    {
        int Node = Drw_LibPairs[p->pClass->iPairs+i];
        int a, b, Lit;
        a = Drw_LibNodes[p->pClass->iNodes+Node-4][0];
        b = Drw_LibNodes[p->pClass->iNodes+Node-4][1];
        Lit = Drw_Lookup(p, p->LibLits[a >> 1] ^ (a & 1), p->LibLits[b >> 1] ^ (b & 1), -1);
        if ( Lit >= 0 && p->pObjs[Lit >> 1].Mark != p->Mark ) { fShared = 1; break; }
    }
    if ( !fShared )
    {
        if ( p->pClass->MinSize >= pCut->Saved ) return -1;
        for ( i = 0; i < nRoots; i++ )
        {
            int Cost = Drw_LibSizes[p->pClass->iRoots+i], Level = 0;
            const signed char * pDepths = Drw_LibDepths[p->pClass->iRoots+i];
            if ( Cost >= pCut->Saved || Cost > BestCost ) continue;
            for ( k = 0; k < 4; k++ )
                if ( pDepths[k] >= 0 ) Level = Abc_MaxInt(Level, p->LibLevels[k]+pDepths[k]);
            if ( Level > Required ) continue;
            if ( Cost == BestCost && Level >= BestLevel ) continue;
            Best = i;
            BestCost = Cost;
            BestLevel = Level;
        }
        if ( Best < 0 ) return -1;
        i = Drw_LibRoots[p->pClass->iRoots+Best];
        memset(p->LibLits+4, 0xFF, ((i >> 1)-3)*sizeof(int));
        k = Drw_LibBuild_rec( p, i >> 1 );
        return k < 0 ? -1 : k ^ (i & 1) ^ (int)((Transform >> 12) & 1);
    }
    // Cost masks are needed only after finding an opportunity for sharing.
    nInitial = (Transform & 255) == 1 ? nRoots : Abc_MinInt(nRoots, DRW_SUBGRAPH_LIMIT);
    for ( i = 0; i < nInitial; i++ )
        nNodes = Abc_MaxInt(nNodes, (Drw_LibRoots[p->pClass->iRoots+i] >> 1) + 1);
    fUseBits = nNodes-4 <= 64;
    memset(p->LibCosts, 0, 4*sizeof(word));
    for ( i = 0; i < nRoots; i++ )
    {
        int Root = Drw_LibRoots[p->pClass->iRoots+i] >> 1;
        int Cost;
        if ( i == nInitial && Best >= 0 ) break;
        for ( ; nPrepared <= Root; nPrepared++ )
        {
            int j = nPrepared-4;
            int a = Drw_LibNodes[p->pClass->iNodes+j][0];
            int b = Drw_LibNodes[p->pClass->iNodes+j][1];
            int Lit0 = p->LibLits[a >> 1], Lit1 = p->LibLits[b >> 1], Lit = -1;
            p->LibLevels[nPrepared] = 1 + Abc_MaxInt(p->LibLevels[a >> 1], p->LibLevels[b >> 1]);
            if ( Lit0 == -2 || Lit1 == -2 ) Lit = -2;
            else if ( Lit0 >= 0 && Lit1 >= 0 )
            {
                Lit = Drw_Lookup( p, Lit0 ^ (a & 1), Lit1 ^ (b & 1), -1 );
                if ( Lit >= 0 && (Lit >> 1) == Id ) Lit = -2;
                else if ( Lit >= 0 )
                {
                    if ( Drw_Simplify(Lit0 ^ (a & 1), Lit1 ^ (b & 1)) < 0 )
                        p->pObjs[Lit >> 1].Level = p->LibLevels[nPrepared];
                    else p->LibLevels[nPrepared] = p->pObjs[Lit >> 1].Level;
                }
            }
            p->LibLits[nPrepared] = Lit;
            p->LibSeen[nPrepared] = -1;
            if ( i < nInitial && fUseBits )
                p->LibCosts[nPrepared] = (Lit >= 0 && p->pObjs[Lit >> 1].Mark != p->Mark) ? 0 :
                    p->LibCosts[a >> 1] | p->LibCosts[b >> 1] | ((word)1 << j);
        }
        if ( p->LibLevels[Root] > Required || p->LibLits[Root] == -2 ) continue;
        Cost = 0;
        if ( i < nInitial && fUseBits ) Cost = Abc_TtCountOnes(p->LibCosts[Root]);
        else Cost = Drw_LibCount_rec(p, Root, i, BestCost-(i >= nInitial));
        if ( Cost >= pCut->Saved || Cost > BestCost ||
             (Cost == BestCost && p->LibLevels[Root] >= BestLevel) ) continue;
        Best = i;
        BestCost = Cost;
        BestLevel = p->LibLevels[Root];
        if ( i >= nInitial ) break;
    }
    if ( Best < 0 ) return -1;
    i = Drw_LibRoots[p->pClass->iRoots+Best];
    k = Drw_LibBuild_rec( p, i >> 1 );
    assert( BestLevel <= Required );
    return k < 0 ? -1 : k ^ (i & 1) ^ (int)((Transform >> 12) & 1);
}

/**Function*************************************************************

  Synopsis    [Bounds allocation sizes and signed literal indices.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Drw_ObjectLimit( void )
{
    size_t Limit = INT_MAX/2;
    if ( Limit > ~(size_t)0 / sizeof(Drw_Obj_t) ) Limit = ~(size_t)0 / sizeof(Drw_Obj_t);
    if ( Limit > ~(size_t)0 / sizeof(Drw_Fan_t) ) Limit = ~(size_t)0 / sizeof(Drw_Fan_t);
    return (int)Limit;
}

/**Function*************************************************************

  Synopsis    [Computes XAIG input levels from the timing manager.]

  Description [Recomputes box-aware levels because the incoming level
  vector may contain plain AIG levels. A temporary view folds buffers and,
  when necessary, puts register outputs before box outputs for the shared
  level computation. The returned levels follow the original CI order.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Drw_BoxCiLevels( Gia_Man_t * pGia )
{
    Gia_Man_t * pLevels = pGia;
    Gia_Obj_t * pObj;
    Tim_Man_t * pTim = (Tim_Man_t *)pGia->pManTime;
    Vec_Int_t * vLevels, * vResult;
    int nRegs = Gia_ManRegNum(pGia);
    int fShuffle = nRegs && Gia_ManIsNormalized(pGia);
    int i, iCi, nCis = Gia_ManCiNum(pGia), nPis = Tim_ManPiNum(pTim) - nRegs;
    if ( nRegs || Gia_ManBufNum(pGia) )
    {
        pLevels = Gia_ManStart( Gia_ManObjNum(pGia) );
        // Folding a buffer can give an AND two identical fanins. Keep
        // such ANDs and their levels instead of simplifying this view.
        pLevels->fGiaSimple = 1;
        Gia_ManConst0(pGia)->Value = 0;
        for ( i = 0; i < nCis; i++ )
        {
            iCi = !fShuffle || i < nPis ? i : i < nPis+nRegs ? nCis-nRegs+i-nPis : i-nRegs;
            Gia_ManCi(pGia, iCi)->Value = Gia_ManAppendCi( pLevels );
        }
        Gia_ManForEachAnd( pGia, pObj, i )
            pObj->Value = !pGia->fGiaSimple && Gia_ObjIsBuf(pObj) ? Gia_ObjFanin0Copy(pObj) :
                Gia_ManAppendAnd( pLevels, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        Gia_ManForEachCo( pGia, pObj, i )
            Gia_ManAppendCo( pLevels, Gia_ObjFanin0Copy(pObj) );
        pLevels->pManTime = pTim;
        pLevels->nAnd2Delay = pGia->nAnd2Delay;
    }
    Gia_ManLevelWithBoxes( pLevels );
    vLevels = Gia_ManGetCiLevels( pLevels );
    if ( pLevels != pGia )
    {
        pLevels->pManTime = NULL;
        Gia_ManStop( pLevels );
    }
    if ( !fShuffle ) return vLevels;
    vResult = Vec_IntAlloc( Vec_IntSize(vLevels) );
    for ( i = 0; i < nPis; i++ )
        Vec_IntPush( vResult, Vec_IntEntry(vLevels, i) );
    for ( i = nPis+nRegs; i < Vec_IntSize(vLevels); i++ )
        Vec_IntPush( vResult, Vec_IntEntry(vLevels, i) );
    for ( i = nPis; i < nPis+nRegs; i++ )
        Vec_IntPush( vResult, Vec_IntEntry(vLevels, i) );
    Vec_IntFree( vLevels );
    return vResult;
}

/**Function*************************************************************

  Synopsis    [Imports a GIA and computes initial levels and required levels.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Drw_Man_t * Drw_ManStart( Gia_Man_t * pGia, int fKeepLevel, Vec_Int_t * vCiLevels )
{
    Drw_Man_t * p = ABC_CALLOC( Drw_Man_t, 1 );
    Gia_Obj_t * pObj;
    int i, Id;
    p->nObjLimit = Drw_ObjectLimit();
    p->nCap = Abc_MinInt( p->nObjLimit, Abc_MaxInt(16, 2*Gia_ManObjNum(pGia)) );
    p->pObjs = ABC_ALLOC( Drw_Obj_t, p->nCap );
    p->pFans = ABC_ALLOC( Drw_Fan_t, p->nCap );
    p->nHashMask = 16;
    while ( p->nHashMask < Gia_ManObjNum(pGia) ) p->nHashMask *= 2;
    p->pHash = ABC_CALLOC( int, p->nHashMask );
    p->nHashMask--;
    p->vCis = Vec_IntAlloc( Gia_ManCiNum(pGia) );
    p->vCos = Vec_IntAlloc( Gia_ManCoNum(pGia) );
    p->vStack = Vec_IntAlloc( 3*DRW_MFFC_LIMIT );
    p->vOrder = Vec_IntAlloc( p->nCap );
    p->fKeepLevel = fKeepLevel;
    p->iRoot = -1;
    Drw_Append( p, DRW_CONST, 0, 0 );
    Gia_ManForEachObj1( pGia, pObj, i )
    {
        if ( Gia_ObjIsCi(pObj) )
        {
            Id = Drw_Append( p, DRW_CI, 0, 0 );
            if ( vCiLevels ) p->pObjs[Id].Level = Vec_IntEntry(vCiLevels, Gia_ObjCioId(pObj));
        }
        else if ( Gia_ObjIsCo(pObj) )
        {
            Id = Drw_Append( p, DRW_CO, Gia_ObjFaninLit0(pObj, i), 0 );
            p->nLevelMax = Abc_MaxInt(p->nLevelMax, p->pObjs[p->pObjs[Id].Fan[0] >> 1].Level);
        }
        else
        {
            assert( Gia_ObjIsAnd(pObj) );
            Id = Drw_Append( p, DRW_AND, Gia_ObjFaninLit0(pObj, i), Gia_ObjFaninLit1(pObj, i) );
            if ( !pGia->fGiaSimple && Gia_ObjIsBuf(pObj) )
            {
                p->pObjs[Id].Buffer = 1;
                p->pObjs[Id].Level = p->pObjs[p->pObjs[Id].Fan[0] >> 1].Level;
            }
        }
        if ( p->pObjs[Id].Type == DRW_AND ) Drw_Ready(p, Id);
        assert( Id == i );
    }
    Gia_ManForEachCi(pGia, pObj, i) Vec_IntPush(p->vCis, Gia_ObjId(pGia, pObj));
    Gia_ManForEachCo(pGia, pObj, i) Vec_IntPush(p->vCos, Gia_ObjId(pGia, pObj));
    p->nOrig = p->nObjs;
    // Rewriting never adds a dependency between unhandled original nodes.
    // Their remaining fanout paths keep these required levels valid for
    // the whole pass. Forward levels are refreshed only when needed.
    for ( i = p->nObjs-1; i > 0; i-- )
    {
        Drw_Obj_t * pNode = p->pObjs + i;
        if ( pNode->Type == DRW_CO )
        {
            // Fixed XAIG input arrivals are upper bounds only if each
            // interface output keeps its original arrival bound as well.
            p->pFans[i].Required = vCiLevels ? p->pObjs[pNode->Fan[0] >> 1].Level : p->nLevelMax;
            p->pFans[pNode->Fan[0] >> 1].Required = Abc_MinInt(p->pFans[pNode->Fan[0] >> 1].Required, p->pFans[i].Required);
        }
        else if ( pNode->Type == DRW_AND )
        {
            int k;
            if ( pNode->Refs == 0 ) { Drw_Delete( p, i ); continue; }
            for ( k = 0; k < 2; k++ )
            {
                int Var = pNode->Fan[k] >> 1;
                p->pFans[Var].Required = Abc_MinInt(p->pFans[Var].Required, p->pFans[i].Required-!pNode->Buffer);
            }
        }
    }
    return p;
}

/**Function*************************************************************

  Synopsis    [Copies interface metadata, including an empty vector.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Drw_DupVector( Vec_Int_t * pVec )
{
    return Vec_IntSize(pVec) ? Vec_IntDup(pVec) : Vec_IntAlloc(0);
}

/**Function*************************************************************

  Synopsis    [Exports the handled topological order as a normalized GIA.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Drw_ManExport( Drw_Man_t * p, Gia_Man_t * pOld )
{
    Gia_Man_t * pNew = Gia_ManStart( p->nAnds + Vec_IntSize(p->vCis) + Vec_IntSize(p->vCos) + 1 );
    int * pCopies = ABC_ALLOC( int, p->nObjs );
    int i, Id, Lit;
    memset( pCopies, 0xFF, p->nObjs * sizeof(int) );
    pCopies[0] = 0;
    pNew->pName = Abc_UtilStrsav( pOld->pName );
    pNew->pSpec = Abc_UtilStrsav( pOld->pSpec );
    Vec_IntForEachEntry( p->vCis, Id, i ) pCopies[Id] = Gia_ManAppendCi( pNew );

    // The handled-node vector is already topological. Stable IDs let dead
    // entries remain until export without maintaining a second linked list.
    Vec_IntForEachEntry( p->vOrder, Id, i )
    {
        int a, b;
        if ( p->pObjs[Id].Type != DRW_AND || !p->pObjs[Id].Refs ) continue;
        a = p->pObjs[Id].Fan[0];
        b = p->pObjs[Id].Fan[1];
        assert(pCopies[a >> 1] >= 0 && pCopies[b >> 1] >= 0);
        pCopies[Id] = Gia_ManAppendAnd(pNew, pCopies[a >> 1] ^ (a & 1), pCopies[b >> 1] ^ (b & 1));
    }
    Vec_IntForEachEntry(p->vCos, Id, i)
    {
        Lit = p->pObjs[Id].Fan[0];
        assert(pCopies[Lit >> 1] >= 0);
        assert(!p->fKeepLevel || p->pObjs[Lit >> 1].Level <= p->pFans[Id].Required);
        Gia_ManAppendCo(pNew, pCopies[Lit >> 1] ^ (Lit & 1));
    }
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(pOld) );
    pNew->nConstrs = pOld->nConstrs;
    if ( pOld->vRegInits ) pNew->vRegInits = Drw_DupVector( pOld->vRegInits );
    if ( pOld->vRegClasses ) pNew->vRegClasses = Drw_DupVector( pOld->vRegClasses );
    if ( pOld->vFlopClasses ) pNew->vFlopClasses = Drw_DupVector( pOld->vFlopClasses );
    if ( pOld->vNamesIn ) pNew->vNamesIn = Vec_PtrDupStr( pOld->vNamesIn );
    if ( pOld->vNamesOut ) pNew->vNamesOut = Vec_PtrDupStr( pOld->vNamesOut );
    if ( pOld->vUserPiIds ) pNew->vUserPiIds = Drw_DupVector( pOld->vUserPiIds );
    if ( pOld->vUserPoIds ) pNew->vUserPoIds = Drw_DupVector( pOld->vUserPoIds );
    if ( pOld->vUserFfIds ) pNew->vUserFfIds = Drw_DupVector( pOld->vUserFfIds );
    if ( pOld->pManTime ) pNew->pManTime = Tim_ManDup( (Tim_Man_t *)pOld->pManTime, 0 );
    if ( pOld->pAigExtra ) pNew->pAigExtra = Gia_ManDup( pOld->pAigExtra );
    if ( pOld->vCiArrs ) pNew->vCiArrs = Drw_DupVector( pOld->vCiArrs );
    if ( pOld->vCoReqs ) pNew->vCoReqs = Drw_DupVector( pOld->vCoReqs );
    if ( pOld->vCoArrs ) pNew->vCoArrs = Drw_DupVector( pOld->vCoArrs );
    if ( pOld->vCoAttrs ) pNew->vCoAttrs = Drw_DupVector( pOld->vCoAttrs );
    if ( pOld->vInArrs ) pNew->vInArrs = Vec_FltSize(pOld->vInArrs) ? Vec_FltDup(pOld->vInArrs) : Vec_FltAlloc(0);
    if ( pOld->vOutReqs ) pNew->vOutReqs = Vec_FltSize(pOld->vOutReqs) ? Vec_FltDup(pOld->vOutReqs) : Vec_FltAlloc(0);
    pNew->DefInArrs = pOld->DefInArrs;
    pNew->DefOutReqs = pOld->DefOutReqs;
    pNew->And2Delay = pOld->And2Delay;
    pNew->nAnd2Delay = pOld->nAnd2Delay;
    ABC_FREE( pCopies );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Performs one rewriting pass and returns a new GIA.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Drw_ManRewrite( Gia_Man_t * pGia, int fKeepLevel, int fVerbose )
{
    Drw_Man_t * p;
    Gia_Man_t * pNew;
    Vec_Int_t * vCiLevels;
    Drw_Cut_t Cut;
    int Id, Lit, i, NewStart;
    abctime Start = Abc_Clock(), Setup, Export, Clock;
    if ( pGia == NULL || Gia_ManHasChoices(pGia) || pGia->pMuxes || Gia_ManXorNum(pGia) ) return NULL;
    // Internal sequential box views use a different CI order. Require
    // the standard normalized interface when explicit registers coexist.
    if ( Gia_ManIsSeqWithBoxes(pGia) && !Gia_ManIsNormalized(pGia) ) return NULL;
    if ( (word)Gia_ManObjNum(pGia) + (word)Drw_LibMaxSize*Gia_ManAndNum(pGia) > (word)Drw_ObjectLimit() ) return NULL;
    vCiLevels = Gia_ManBoxNum(pGia) ? Drw_BoxCiLevels(pGia) : NULL;
    p = Drw_ManStart( pGia, fKeepLevel, vCiLevels );
    Vec_IntFreeP( &vCiLevels );
    Setup = Abc_Clock() - Start;
    // Reused ready nodes finish early. All remaining original nodes retain
    // their topological visit order; each is considered at most once.
    for ( Id = 1; Id < p->nOrig; Id++ )
    {
        if ( p->pObjs[Id].Type != DRW_AND || p->pObjs[Id].Handled ) continue;
        assert( !p->pObjs[Id].Handled && p->pObjs[Id].Type == DRW_AND );
        assert( p->pObjs[p->pObjs[Id].Fan[0] >> 1].Handled );
        assert( p->pObjs[p->pObjs[Id].Fan[1] >> 1].Handled );
        p->pObjs[Id].Level = !p->pObjs[Id].Buffer + Abc_MaxInt(p->pObjs[p->pObjs[Id].Fan[0] >> 1].Level, p->pObjs[p->pObjs[Id].Fan[1] >> 1].Level);
        Lit = Drw_Lookup( p, p->pObjs[Id].Fan[0], p->pObjs[Id].Fan[1], Id );
        if ( Lit >= 0 )
        {
            Drw_Finish(p, Lit >> 1);
            Drw_Replace( p, Id, Lit );
            p->nMerged++;
            continue;
        }
        if ( !p->pObjs[Id].Hashed ) Drw_HashInsert( p, Id );
        // If neither fanin is removable, the immediate cut already attains
        // the maximum possible MFFC of one node. It cannot give a gain.
        if ( (p->pObjs[p->pObjs[Id].Fan[0] >> 1].Type != DRW_AND || p->pObjs[p->pObjs[Id].Fan[0] >> 1].Refs > 1) &&
             (p->pObjs[p->pObjs[Id].Fan[1] >> 1].Type != DRW_AND || p->pObjs[p->pObjs[Id].Fan[1] >> 1].Refs > 1) ) goto finish;
        Clock = fVerbose ? Abc_Clock() : 0;
        if ( !Drw_SelectCut(p, Id, &Cut) ) goto finish;
        if ( fVerbose ) p->timeCuts += Abc_Clock() - Clock;
        Clock = fVerbose ? Abc_Clock() : 0;
        NewStart = p->nObjs;
        Lit = Drw_Evaluate( p, Id, &Cut );
        if ( fVerbose ) p->timeEval += Abc_Clock() - Clock;
        if ( Lit < 0 && NewStart == p->nObjs ) goto finish;
        Clock = fVerbose ? Abc_Clock() : 0;
        if ( Lit >= 0 ) Drw_Replace( p, Id, Lit );
        // Dependent cut leaves can make library nodes coincide. Remove
        // any construction debris, also when a build rejected self-reuse.
        for ( i = p->nObjs-1; i >= NewStart; i-- )
            if ( p->pObjs[i].Type == DRW_AND && !p->pObjs[i].Refs ) Drw_Delete( p, i );
        if ( fVerbose ) p->timeUpdate += Abc_Clock() - Clock;
        p->nRewritten += Lit >= 0;
finish:
        Drw_Finish(p, Id);
    }
    Export = Abc_Clock();
    pNew = Drw_ManExport( p, pGia );
    assert( p->nAnds == Gia_ManAndNum(pNew) );
    Export = Abc_Clock() - Export;
    if ( fVerbose )
    {
        Abc_Print( 1, "&drw: ANDs %d -> %d. Rewrites = %d. Merges = %d. Cut states = %.0f. Limited = %d.\n",
            Gia_ManAndNum(pGia), Gia_ManAndNum(pNew), p->nRewritten, p->nMerged, p->nCuts, p->nLimited );
        Abc_Print( 1, "&drw: import %.6f  cuts %.6f  evaluate %.6f  update %.6f  export %.6f  total %.6f sec\n",
            (double)Setup/CLOCKS_PER_SEC, (double)p->timeCuts/CLOCKS_PER_SEC, (double)p->timeEval/CLOCKS_PER_SEC,
            (double)p->timeUpdate/CLOCKS_PER_SEC, (double)Export/CLOCKS_PER_SEC, (double)(Abc_Clock()-Start)/CLOCKS_PER_SEC );
    }
    Vec_IntFree( p->vCis );
    Vec_IntFree( p->vCos );
    Vec_IntFree( p->vStack );
    Vec_IntFree( p->vOrder );
    ABC_FREE( p->pObjs );
    ABC_FREE( p->pFans );
    ABC_FREE( p->pHash );
    ABC_FREE( p );
    return pNew;
}

struct Drw_Gia_t_
{
    Drw_Man_t Core;
    Drw_Cut_t Structural;
    int Captures;
};

static void Drw_GiaRequire( int Condition, const char * pMessage )
{
    if ( Condition ) return;
    fprintf(stderr, "SRESUB_DRW_FAIL %s\n", pMessage);
    abort();
}

static void Drw_GiaCapture( Drw_Cut_t * pCut )
{
    Drw_GiaRequire(s_pDrwGiaCapture != NULL, "observer outside selection");
    s_pDrwGiaCapture->Structural = *pCut;
    s_pDrwGiaCapture->Captures++;
}

Drw_Gia_t * Drw_GiaStart( Gia_Man_t * pGia )
{
    Drw_Gia_t * p = ABC_CALLOC(Drw_Gia_t, 1);
    Gia_Obj_t * pObj;
    int Id;
    p->Core.nObjs = p->Core.nCap = Gia_ManObjNum(pGia);
    p->Core.pObjs = ABC_CALLOC(Drw_Obj_t, p->Core.nObjs);
    p->Core.vStack = Vec_IntAlloc(3*DRW_MFFC_LIMIT);
    // IDs and physical fanout counts are preserved, including dangling nodes.
    // GIA and DRW both use const0; complemented literals need no translation.
    Gia_ManForEachObj(pGia, pObj, Id)
    {
        Drw_Obj_t * q = p->Core.pObjs + Id;
        if ( !Id ) q->Type = DRW_CONST;
        else if ( Gia_ObjIsCi(pObj) ) q->Type = DRW_CI;
        else if ( Gia_ObjIsCo(pObj) ) q->Type = DRW_CO;
        else
        {
            Drw_GiaRequire(Gia_ObjIsAndNotBuf(pObj) && !Gia_ObjIsXor(pObj), "only plain AIG ANDs supported");
            Drw_GiaRequire(Gia_ObjFaninId0p(pGia,pObj) && Gia_ObjFaninId1p(pGia,pObj), "unsimplified constant AND");
            q->Type = DRW_AND;
        }
        if ( q->Type == DRW_AND || q->Type == DRW_CO )
        {
            q->Fan[0] = Gia_ObjFaninLit0p(pGia,pObj);
            p->Core.pObjs[q->Fan[0] >> 1].Refs++;
        }
        if ( q->Type == DRW_AND )
        {
            q->Fan[1] = Gia_ObjFaninLit1p(pGia,pObj);
            p->Core.pObjs[q->Fan[1] >> 1].Refs++;
        }
    }
    return p;
}

Vec_Int_t * Drw_GiaSelect( Drw_Gia_t * p, int Id )
{
    Drw_Cut_t Cut;
    Vec_Int_t * vLeaves;
    int i;
    Drw_GiaRequire(!s_pDrwGiaCapture && Id > 0 && Id < p->Core.nObjs &&
        p->Core.pObjs[Id].Type == DRW_AND, "invalid/concurrent query");
    p->Captures = 0;
    s_pDrwGiaCapture = p;
    Drw_SelectCut(&p->Core, Id, &Cut);
    s_pDrwGiaCapture = NULL;
    Drw_GiaRequire(p->Captures == 1 && p->Structural.nLeaves <= 4, "missing structural boundary");
    vLeaves = Vec_IntAlloc(4);
    for ( i = 0; i < p->Structural.nLeaves; ++i )
        Vec_IntPush(vLeaves,p->Structural.Leaves[i]);
    return vLeaves;
}

void Drw_GiaStop( Drw_Gia_t * p )
{
    if ( !p ) return;
    Vec_IntFree(p->Core.vStack);
    ABC_FREE(p->Core.pObjs);
    ABC_FREE(p);
}

ABC_NAMESPACE_IMPL_END
