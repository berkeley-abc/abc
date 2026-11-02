/**CFile****************************************************************

  FileName    [giaEdit.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Shared mutable AIG editing kernel for local optimization.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaEdit.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__aig__gia__giaEdit_h
#define ABC__aig__gia__giaEdit_h

#include "gia.h"

ABC_NAMESPACE_HEADER_START

// Stable object IDs and singly linked fanout lists with dead-edge tombstones.
// Finished nodes have immutable fanins for the current pass. The ready policy
// hashes only nodes with finished fanins; the all-node policy maintains the
// whole live graph and promotes reused cones. Busy excludes pending resub roots.
enum
{
    GIE_DEAD,
    GIE_CONST,
    GIE_CI,
    GIE_AND,
    GIE_CO
};
enum
{
    GIE_HASH_READY,
    GIE_HASH_ALL,
    GIE_HASH_DEFER
};
enum
{
    GIE_STACK_INITIAL = 96
};
typedef struct Gie_Obj_t_ Gie_Obj_t;
typedef struct Gie_Man_t_ Gie_Man_t;
struct Gie_Obj_t_
{
    int Fan[2];
    int Refs;
    int Hash;
    int Level;
    unsigned Mark;
    unsigned TruthMark;
    unsigned short Truth;
    unsigned char Type;
    unsigned char Handled : 1;
    unsigned char Inside : 1;
    unsigned char Hashed : 1;
    unsigned char Duplicate : 1;
    unsigned char CanEqual : 1;
    unsigned char Busy : 1;
};

typedef struct Gie_Fan_t_
{
    int Next[2];
    int Head;
    int Required;
} Gie_Fan_t;

struct Gie_Man_t_
{
    Gie_Obj_t * pObjs;
    Gie_Fan_t * pFans;
    int * pHash;
    int nObjs, nCap, nObjLimit, nOrig, nAnds, nHashMask, nLevelMax;
    int fKeepLevel, fHashAll, iRoot;
    unsigned Mark, TruthMark;
    Vec_Int_t *vCis, *vCos, *vStack, *vOrder, *vPromote;
};

extern int Gie_ObjectLimit( void );
extern Vec_Int_t * Gie_BoxCiLevels( Gia_Man_t * pGia );
extern void Gie_ManStart( Gie_Man_t * p, Gia_Man_t * pGia, int fKeepLevel, int HashMode, Vec_Int_t * vCiLevels );
extern void Gie_ManStop( Gie_Man_t * p );
extern Gia_Man_t * Gie_ManExport( Gie_Man_t * p, Gia_Man_t * pOld );
extern void Gie_ManDupMetadata( Gia_Man_t * pNew, Gia_Man_t * pOld );
extern unsigned * Gie_Neighborhoods( Gie_Man_t * p, int nObjs, int Rounds );

static inline unsigned Gie_MixColor( unsigned a )
{
    a ^= a >> 16;
    a *= 0x7feb352du;
    a ^= a >> 15;
    a *= 0x846ca68bu;
    return a ^ ( a >> 16 );
}

/**Function*************************************************************

  Synopsis    [Starts a fresh MFFC marking generation.]

  Description [Clears old stamps on wrap so they cannot alias a new traversal.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Gie_MarkNext( Gie_Man_t * p )
{
    int i;
    if ( ++p->Mark ) return;
    for ( i = 0; i < p->nObjs; i++ )
        p->pObjs[i].Mark = 0;
    p->Mark = 1;
}

static inline void Gie_TruthNext( Gie_Man_t * p )
{
    int i;
    if ( ++p->TruthMark ) return;
    for ( i = 0; i < p->nObjs; i++ )
        p->pObjs[i].TruthMark = 0;
    p->TruthMark = 1;
}

static inline unsigned Gie_HashKey( Gie_Man_t * p, int a, int b )
{
    // Symmetric mixing avoids sorting the two fanin literals.
    word h = (word) (unsigned) a * (unsigned) b;
    h ^= ( (word) (unsigned) a + (unsigned) b ) * ABC_CONST( 0x9e3779b97f4a7c15 );
    return (unsigned) ( h ^ ( h >> 32 ) ) & p->nHashMask;
}

static inline int Gie_Simplify( int a, int b )
{
    if ( a == b ) return a;
    if ( a == ( b ^ 1 ) || a == 0 || b == 0 ) return 0;
    if ( a == 1 ) return b;
    if ( b == 1 ) return a;
    return -1;
}

static inline int Gie_AndLevel( int a, int b, int LevA, int LevB )
{
    int Lit = Gie_Simplify( a, b );
    return Lit < 0 ? 1 + Abc_MaxInt( LevA, LevB ) : Lit < 2 ? 0 : ( Lit >> 1 ) == ( a >> 1 ) ? LevA : LevB;
}

static inline int Gie_Lookup( Gie_Man_t * p, int a, int b, int Skip )
{
    int i, Lit = Gie_Simplify( a, b );
    if ( Lit >= 0 ) return Lit;
    for ( i = p->pHash[Gie_HashKey( p, a, b )]; i; i = p->pObjs[i].Hash )
        if ( i != Skip && !p->pObjs[i].Busy &&
             ( ( p->pObjs[i].Fan[0] == a && p->pObjs[i].Fan[1] == b ) ||
               ( p->pObjs[i].Fan[0] == b && p->pObjs[i].Fan[1] == a ) ) )
            return 2 * i;
    return -1;
}

static inline void Gie_HashInsert( Gie_Man_t * p, int Id )
{
    int a = p->pObjs[Id].Fan[0], b = p->pObjs[Id].Fan[1], i;
    unsigned Key = Gie_HashKey( p, a, b );
    p->pObjs[Id].Hash = p->pHash[Key];
    p->pObjs[Id].Duplicate = 0;
    for ( i = p->pHash[Key]; i; i = p->pObjs[i].Hash )
        if ( ( p->pObjs[i].Fan[0] == a && p->pObjs[i].Fan[1] == b ) ||
             ( p->pObjs[i].Fan[0] == b && p->pObjs[i].Fan[1] == a ) )
        {
            p->pObjs[Id].Duplicate = p->pObjs[i].Duplicate = 1;
            break;
        }
    p->pHash[Key] = Id;
    p->pObjs[Id].Hashed = 1;
}

static inline void Gie_HashRemove( Gie_Man_t * p, int Id )
{
    int * pLink;
    if ( !p->pObjs[Id].Hashed ) return;
    pLink = p->pHash + Gie_HashKey( p, p->pObjs[Id].Fan[0], p->pObjs[Id].Fan[1] );
    while ( *pLink != Id )
    {
        assert( *pLink );
        pLink = &p->pObjs[*pLink].Hash;
    }
    *pLink = p->pObjs[Id].Hash;
    p->pObjs[Id].Hashed = 0;
}

/**Function*************************************************************

  Synopsis    [Indexes a node according to the selected sharing policy.]

  Description [Ready mode indexes only nodes with finished fanins and exact
  levels. All-node mode also indexes unvisited cones; Gie_Finish computes
  their exact levels before reuse. The selected policy stays fixed per call.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Gie_Ready( Gie_Man_t * p, int Id )
{
    Gie_Obj_t * pObj = p->pObjs + Id;
    if ( pObj->Type != GIE_AND || pObj->Hashed ) return;
    if ( !p->fHashAll )
    {
        if ( !p->pObjs[pObj->Fan[0] >> 1].Handled || !p->pObjs[pObj->Fan[1] >> 1].Handled ) return;
        pObj->Level = 1 + Abc_MaxInt( p->pObjs[pObj->Fan[0] >> 1].Level, p->pObjs[pObj->Fan[1] >> 1].Level );
    }
    Gie_HashInsert( p, Id );
}

/**Function*************************************************************

  Synopsis    [Finishes a node and any unvisited fanins in topological order.]

  Description [Promotion is nonrecursive. Each promoted node receives its
  exact level, enters the export order, and skips its later optimization
  turn. Finished nodes never change their fanins during the pass.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Gie_Finish( Gie_Man_t * p, int Id )
{
    int a, b, Edge;
    if ( p->pObjs[Id].Handled ) return;
    if ( !p->fHashAll )
    {
        assert( p->pObjs[Id].Type == GIE_AND && p->pObjs[Id].Hashed );
        assert( p->pObjs[p->pObjs[Id].Fan[0] >> 1].Handled && p->pObjs[p->pObjs[Id].Fan[1] >> 1].Handled );
        p->pObjs[Id].Handled = 1;
        Vec_IntPush( p->vOrder, Id );
        for ( Edge = p->pFans[Id].Head; Edge; Edge = p->pFans[Edge >> 1].Next[Edge & 1] )
            Gie_Ready( p, Edge >> 1 );
        return;
    }
    assert( !Vec_IntSize( p->vPromote ) );
    Vec_IntPush( p->vPromote, Id );
    while ( Vec_IntSize( p->vPromote ) )
    {
        Id = Vec_IntEntryLast( p->vPromote );
        if ( p->pObjs[Id].Handled )
        {
            Vec_IntPop( p->vPromote );
            continue;
        }
        assert( p->pObjs[Id].Type == GIE_AND && p->pObjs[Id].Hashed );
        a = p->pObjs[Id].Fan[0] >> 1;
        b = p->pObjs[Id].Fan[1] >> 1;
        if ( !p->pObjs[a].Handled )
        {
            Vec_IntPush( p->vPromote, a );
            continue;
        }
        if ( !p->pObjs[b].Handled )
        {
            Vec_IntPush( p->vPromote, b );
            continue;
        }
        p->pObjs[Id].Level = 1 + Abc_MaxInt( p->pObjs[a].Level, p->pObjs[b].Level );
        p->pObjs[Id].Handled = 1;
        Vec_IntPush( p->vOrder, Id );
        Vec_IntPop( p->vPromote );
    }
}

static inline void Gie_Link( Gie_Man_t * p, int Id, int Pin )
{
    int Var = p->pObjs[Id].Fan[Pin] >> 1;
    int Edge = 2 * Id + Pin;
    int Head = p->pFans[Var].Head;
    p->pFans[Id].Next[Pin] = Head;
    p->pFans[Var].Head = Edge;
    p->pObjs[Var].Refs++;
}

static inline int Gie_Unlink( Gie_Man_t * p, int Id, int Pin )
{
    int Var = p->pObjs[Id].Fan[Pin] >> 1;
    // Deleted fanouts remain as tombstones in this singly linked list.
    // A finished node is never rewired; traversals ignore dead fanouts.
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
static inline int Gie_Append( Gie_Man_t * p, int Type, int a, int b )
{
    int Id = p->nObjs++;
    Gie_Obj_t * pObj;
    if ( p->nObjs > p->nCap )
    {
        p->nCap = p->nCap > p->nObjLimit / 2 ? p->nObjLimit : 2 * p->nCap;
        p->pObjs = ABC_REALLOC( Gie_Obj_t, p->pObjs, p->nCap );
        p->pFans = ABC_REALLOC( Gie_Fan_t, p->pFans, p->nCap );
    }
    pObj = p->pObjs + Id;
    memset( pObj, 0, sizeof( Gie_Obj_t ) );
    memset( p->pFans + Id, 0, sizeof( Gie_Fan_t ) );
    pObj->Type = (unsigned char) Type;
    pObj->Fan[0] = a;
    pObj->Fan[1] = b;
    p->pFans[Id].Required = ABC_INFINITY;
    if ( Type == GIE_AND )
    {
        Gie_Link( p, Id, 0 );
        Gie_Link( p, Id, 1 );
        // New gates have finished fanins and finish immediately.
        // Original gates are already indexed, including unvisited ones.
        if ( p->nOrig )
        {
            assert( p->pObjs[a >> 1].Handled && p->pObjs[b >> 1].Handled );
            Gie_HashInsert( p, Id );
            p->pObjs[Id].Handled = 1;
            Vec_IntPush( p->vOrder, Id );
        }
        p->pObjs[Id].Level = 1 + Abc_MaxInt( p->pObjs[a >> 1].Level, p->pObjs[b >> 1].Level );
        p->nAnds++;
    }
    else if ( Type == GIE_CO )
        Gie_Link( p, Id, 0 );
    else
        pObj->Handled = 1;
    return Id;
}

/**Function*************************************************************

  Synopsis    [Structurally hashes an AND of two literals.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Gie_And( Gie_Man_t * p, int a, int b )
{
    int Lit = Gie_Lookup( p, a, b, -1 );
    if ( Lit >= 0 )
    {
        if ( ( Lit >> 1 ) == p->iRoot ) return -1;
        // Promotion is permanent even if this build is later rejected.
        // The reused node stays valid but skips its own refactoring turn.
        Gie_Finish( p, Lit >> 1 );
        return Lit;
    }
    if ( p->nObjs == p->nObjLimit ) return -1;
    return 2 * Gie_Append( p, GIE_AND, a, b );
}

/**Function*************************************************************

  Synopsis    [Deletes dangling nodes without recursive stack growth.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Gie_Delete( Gie_Man_t * p, int Id )
{
    Vec_IntClear( p->vStack );
    Vec_IntPush( p->vStack, Id );
    while ( Vec_IntSize( p->vStack ) )
    {
        int i, Var;
        Id = Vec_IntPop( p->vStack );
        if ( p->pObjs[Id].Type != GIE_AND || p->pObjs[Id].Refs ) continue;
        Gie_HashRemove( p, Id );
        for ( i = 0; i < 2; i++ )
        {
            Var = Gie_Unlink( p, Id, i );
            if ( p->pObjs[Var].Refs == 0 && p->pObjs[Var].Type == GIE_AND ) Vec_IntPush( p->vStack, Var );
        }
        p->pObjs[Id].Type = GIE_DEAD;
        p->pObjs[Id].Handled = 1;
        p->nAnds--;
    }
}

// Remove construction debris after a failed or simplified replacement.
static inline void Gie_DeleteSince( Gie_Man_t * p, int First )
{
    int Id;
    for ( Id = p->nObjs - 1; Id >= First; Id-- )
        if ( p->pObjs[Id].Type == GIE_AND && !p->pObjs[Id].Refs ) Gie_Delete( p, Id );
}

/**Function*************************************************************

  Synopsis    [Redirects unhandled fanouts and deletes the old cone.]

  Description [The current root stays unhandled until it is kept. Its
  consumers are unvisited and are rehashed when rewired. Redirecting an edge may
  make a consumer ready. No fanout-level sweep is needed.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Gie_Replace( Gie_Man_t * p, int Old, int Lit )
{
    int Edge, Id, Pin, Head = p->pFans[Old].Head, Tail = 0;
    assert( ( Lit >> 1 ) != Old );
    p->pObjs[Lit >> 1].Refs++;
    for ( Edge = Head; Edge; Edge = p->pFans[Edge >> 1].Next[Edge & 1] )
    {
        Tail = Edge;
        Id = Edge >> 1;
        Pin = Edge & 1;
        if ( p->pObjs[Id].Type == GIE_DEAD ) continue;
        assert( !p->pObjs[Id].Handled );
        Gie_HashRemove( p, Id );
        p->pObjs[Id].Fan[Pin] = Lit ^ ( p->pObjs[Id].Fan[Pin] & 1 );
        Gie_Ready( p, Id );
    }
    if ( Tail )
    {
        int Next = p->pFans[Lit >> 1].Head;
        p->pFans[Tail >> 1].Next[Tail & 1] = Next;
        p->pFans[Lit >> 1].Head = Head;
        p->pObjs[Lit >> 1].Refs += p->pObjs[Old].Refs;
        p->pFans[Old].Head = p->pObjs[Old].Refs = 0;
    }
    Gie_Delete( p, Old );
    p->pObjs[Lit >> 1].Refs--;
}

/**Function*************************************************************

  Synopsis    [Pushes onto scratch storage with a caller-local stack size.]

  Description [The shared vector's size remains zero between traversals.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Gie_StackPush( Vec_Int_t * vStack, int * pnStack, int Id )
{
    if ( *pnStack == Vec_IntCap( vStack ) ) Vec_IntGrow( vStack, 2 * Vec_IntCap( vStack ) );
    Vec_IntArray( vStack )[( *pnStack )++] = Id;
}

/**Function*************************************************************

  Synopsis    [Counts the removable MFFC using virtual dereferencing.]

  Description [Process the root directly; most traversals need no stack.
  An explicit stack also handles deep cones exposed by support minimization.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Gie_Deref( Gie_Man_t * p, int Id, int fMark )
{
    int i, Var, Count = 0, nStack = 0;
    if ( p->pObjs[Id].Type != GIE_AND ) return 0;
    for ( ;; )
    {
        Count++;
        if ( fMark ) p->pObjs[Id].Mark = p->Mark;
        for ( i = 0; i < 2; i++ )
        {
            Var = p->pObjs[Id].Fan[i] >> 1;
            if ( p->pObjs[Var].Type != GIE_AND ) continue;
            assert( p->pObjs[Var].Refs > 0 );
            if ( --p->pObjs[Var].Refs == 0 ) Gie_StackPush( p->vStack, &nStack, Var );
        }
        if ( !nStack ) break;
        Id = Vec_IntArray( p->vStack )[--nStack];
    }
    return Count;
}

/**Function*************************************************************

  Synopsis    [Restores references after virtual dereferencing.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Gie_Ref( Gie_Man_t * p, int Id )
{
    int i, Var, nStack = 0;
    if ( p->pObjs[Id].Type != GIE_AND ) return;
    for ( ;; )
    {
        for ( i = 0; i < 2; i++ )
        {
            Var = p->pObjs[Id].Fan[i] >> 1;
            if ( p->pObjs[Var].Type != GIE_AND ) continue;
            if ( p->pObjs[Var].Refs++ == 0 ) Gie_StackPush( p->vStack, &nStack, Var );
        }
        if ( !nStack ) break;
        Id = Vec_IntArray( p->vStack )[--nStack];
    }
}

/**Function*************************************************************

  Synopsis    [Counts and optionally marks an MFFC with protected cut leaves.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Gie_Mffc( Gie_Man_t * p, int Id, int * pLeaves, int nLeaves, int fMark )
{
    int i, Saved;
    for ( i = 0; i < nLeaves; i++ )
        if ( p->pObjs[pLeaves[i]].Type == GIE_AND ) p->pObjs[pLeaves[i]].Refs++;
    if ( fMark ) Gie_MarkNext( p );
    Saved = Gie_Deref( p, Id, fMark );
    Gie_Ref( p, Id );
    for ( i = 0; i < nLeaves; i++ )
        if ( p->pObjs[pLeaves[i]].Type == GIE_AND ) p->pObjs[pLeaves[i]].Refs--;
    return Saved;
}

ABC_NAMESPACE_HEADER_END

#endif
