/**CFile****************************************************************

  FileName    [giaDch2.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Fast structural choices from shared synthesis snapshots.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaDch2.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "giaEdit.h"
// Four-input rewrite-library tables shared with the DC3 synthesis passes.
#include "opt/drw/drwInt.h"
#include "opt/dau/dau.h"
#include <limits.h>

ABC_NAMESPACE_IMPL_START

extern int CecZ_ManComputeEquivs( Gia_Man_t * p, Vec_Int_t * vOrigins, Vec_Int_t * vEquivs, int nConfs, int nConfsChoice,
                                  int fVerbose );
extern Gia_Man_t * Gia_ManDc3SnapshotsMore( Gia_Man_t * p, int fKeep, int fVerbose, Gia_Man_t ** ppSnapshot,
                                            Vec_Ptr_t * vLabels, int fMore );
extern void Gia_ManRemoveBadChoices( Gia_Man_t * p );

/**Function*************************************************************

  Synopsis    [Merges construction-proven equalities before simulation and SAT.]

  Description [The original miter retains the alternative implementations. SAT sees a
  smaller graph and does not need to reprove these relations.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Dch2_Reduce( Gia_Man_t * p, Vec_Int_t * vKnown, Vec_Int_t ** pvMap, Vec_Int_t ** pvOrigins,
                                int nSnapshots )
{
    Gia_Man_t * q = Gia_ManStart( Gia_ManObjNum( p ) );
    Vec_Int_t * vMap = Vec_IntStartFull( Gia_ManObjNum( p ) );
    Vec_Int_t * vOrigins;
    Gia_Obj_t * pObj;
    int i, Lit, Known;
    q->pName = Abc_UtilStrsav( p->pName );
    q->pSpec = Abc_UtilStrsav( p->pSpec );
    Vec_IntWriteEntry( vMap, 0, 0 );
    Gia_ManForEachCi ( p, pObj, i ) Vec_IntWriteEntry( vMap, Gia_ObjId( p, pObj ), Gia_ManAppendCi( q ) );
    Gia_ManHashAlloc( q );
    Gia_ManForEachAnd ( p, pObj, i )
    {
        Known = Vec_IntEntry( vKnown, i );
        assert( ( Known >> 1 ) <= i );
        if ( ( Known >> 1 ) < i )
            Lit = Vec_IntEntry( vMap, Known >> 1 ) ^ ( Known & 1 );
        else
            Lit = Gia_ManHashAnd( q, Vec_IntEntry( vMap, Gia_ObjFaninId0( pObj, i ) ) ^ Gia_ObjFaninC0( pObj ),
                                  Vec_IntEntry( vMap, Gia_ObjFaninId1( pObj, i ) ) ^ Gia_ObjFaninC1( pObj ) );
        assert( Lit >= 0 );
        Vec_IntWriteEntry( vMap, i, Lit );
    }
    Gia_ManForEachCo ( p, pObj, i )
        if ( i % nSnapshots == 0 )
            Gia_ManAppendCo( q, Vec_IntEntry( vMap, Gia_ObjFaninId0p( p, pObj ) ) ^ Gia_ObjFaninC0( pObj ) );
    Gia_ManHashStop( q );
    // A proved class may contain nodes from several snapshots. Preserve all
    // origins so that an equivalence within any one snapshot keeps its budget.
    vOrigins = Vec_IntStart( Gia_ManObjNum( q ) );
    Vec_IntForEachEntry ( vMap, Lit, i )
        if ( Lit >= 0 ) *Vec_IntEntryP( vOrigins, Lit >> 1 ) |= Vec_IntEntry( *pvOrigins, i );
    Vec_IntFree( *pvOrigins );
    *pvOrigins = vOrigins;
    *pvMap = vMap;
    return q;
}
/**Function*************************************************************

  Synopsis    [Combines construction proofs with the sweeper's proved classes.]

  Description [The explicit literal map records only proof and hash merges in the
  swept graph. Candidate representatives and Proved flags are not proof records.
  Simulation phases check polarity but do not establish equivalence.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Dch2_Restore( Gia_Man_t * p, Vec_Int_t * vMap, Vec_Int_t * vEquivs )
{
    Vec_Int_t * vFirst = Vec_IntStartFull( Vec_IntSize( vEquivs ) );
    Gia_Obj_t * o;
    int i, Lit, First;
    p->pReprs = ABC_CALLOC( Gia_Rpr_t, Gia_ManObjNum( p ) );
    for ( i = 0; i < Gia_ManObjNum( p ); i++ ) Gia_ObjSetRepr( p, i, GIA_VOID );
    Gia_ManSetPhase( p );
    Gia_ManForEachObj ( p, o, i )
    {
        if ( Gia_ObjIsCo( o ) ) continue;
        Lit = Vec_IntEntry( vMap, i );
        Lit = Vec_IntEntry( vEquivs, Lit >> 1 ) ^ ( Lit & 1 );
        First = Vec_IntEntry( vFirst, Lit >> 1 );
        if ( First < 0 )
            Vec_IntWriteEntry( vFirst, Lit >> 1, 2 * i + ( Lit & 1 ) );
        else
        {
            assert( ( First >> 1 ) < i );
            assert( ( ( First ^ Lit ) & 1 ) == ( o->fPhase ^ Gia_ManObj( p, First >> 1 )->fPhase ) );
            Gia_ObjSetRepr( p, i, First >> 1 );
            Gia_ObjSetProved( p, i );
        }
    }
    p->pNexts = Gia_ManDeriveNexts( p );
    Vec_IntFree( vFirst );
}

/**Function*************************************************************

  Synopsis    [Resolves signed equivalence classes with path compression.]

  Description [Class representatives always have smaller object IDs.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Dch2_Find( Vec_Int_t * v, int Lit )
{
    int Root = Lit, Next;
    while ( ( Next = Vec_IntEntry( v, Root >> 1 ) ) != 2 * ( Root >> 1 ) ) Root = Next ^ ( Root & 1 );
    while ( ( Next = Vec_IntEntry( v, Lit >> 1 ) ) != 2 * ( Lit >> 1 ) )
    {
        Vec_IntWriteEntry( v, Lit >> 1, Root ^ ( Lit & 1 ) );
        Lit = Next ^ ( Lit & 1 );
    }
    return Root;
}
/**Function*************************************************************

  Synopsis    [Imports equalities established by accepted synthesis operations.]

  Description [Snapshots are final-to-original; labels are in reverse order. The miter
  builder leaves snapshot-to-miter literal mappings in object Values.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Dch2_Known( Gia_Man_t * pMiter, Vec_Ptr_t * vSnapshots, Vec_Ptr_t * vLabels, Vec_Int_t * vOrigins )
{
    Vec_Int_t *vFirst, *v, *vKnown = Vec_IntAlloc( Gia_ManObjNum( pMiter ) );
    Gia_Man_t * p;
    Gia_Obj_t * o;
    int k, i, Id, Key, Lit, a, b, MaxLabel = 0;
    assert( Vec_PtrSize( vSnapshots ) == Vec_PtrSize( vLabels ) );
    Vec_PtrForEachEntry ( Vec_Int_t *, vLabels, v, k )
        if ( Vec_IntSize( v ) ) MaxLabel = Abc_MaxInt( MaxLabel, Vec_IntFindMax( v ) );
    vFirst = Vec_IntStartFull( ( MaxLabel >> 1 ) + 1 );
    for ( i = 0; i < Gia_ManObjNum( pMiter ); i++ ) Vec_IntPush( vKnown, 2 * i );
    Vec_PtrForEachEntry ( Gia_Man_t *, vSnapshots, p, k )
    {
        v = (Vec_Int_t *)Vec_PtrEntry( vLabels, Vec_PtrSize( vLabels ) - 1 - k );
        assert( Vec_IntSize( v ) == Gia_ManObjNum( p ) );
        Gia_ManForEachObj ( p, o, i )
        {
            // Origin tracking is independent of the optional synthesis label.
            if ( !~o->Value || Gia_ObjIsCo( o ) ) continue;
            *Vec_IntEntryP( vOrigins, o->Value >> 1 ) |= 1 << k;
            Key = Vec_IntEntry( v, i );
            if ( Key < 0 ) continue;
            Id = Key >> 1;
            Lit = o->Value ^ ( Key & 1 );
            if ( Vec_IntEntry( vFirst, Id ) < 0 ) Vec_IntWriteEntry( vFirst, Id, Lit );
            a = Dch2_Find( vKnown, Vec_IntEntry( vFirst, Id ) );
            b = Dch2_Find( vKnown, Lit );
            if ( a == b ) continue;
            assert( ( a >> 1 ) != ( b >> 1 ) );
            if ( a > b ) ABC_SWAP( int, a, b );
            Vec_IntWriteEntry( vKnown, b >> 1, a ^ ( b & 1 ) );
        }
    }
    for ( i = 0; i < Vec_IntSize( vKnown ); i++ ) Vec_IntWriteEntry( vKnown, i, Dch2_Find( vKnown, 2 * i ) );
    Vec_IntFree( vFirst );
    return vKnown;
}

/**Function*************************************************************

  Synopsis    [Builds one immutable four-input library expression.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Dch2_LutBuild_rec( Gia_Man_t * q, const Drw_LibClass_t * c, int Id, int * Lits )
{
    int a, b, Lit;
    if ( Lits[Id] >= 0 ) return Lits[Id];
    a = Drw_LibNodes[c->iNodes + Id - 4][0];
    b = Drw_LibNodes[c->iNodes + Id - 4][1];
    a = Dch2_LutBuild_rec( q, c, a >> 1, Lits ) ^ ( a & 1 );
    b = Dch2_LutBuild_rec( q, c, b >> 1, Lits ) ^ ( b & 1 );
    Lit = Lits[Id] = Gia_ManHashAnd( q, a, b );
    Gia_ObjSetGateLevel( q, Gia_ManObj( q, Lit >> 1 ) );
    return Lit;
}
/**Function*************************************************************

  Synopsis    [Selects a shallow four-input implementation with area tie breaking.]

  Description [Unused library inputs are assigned constant zero. Wider functions use
  the standard decomposition routine.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Dch2_LutBuild( Gia_Man_t * q, word Truth, Vec_Int_t * vLeaves, Vec_Int_t * vCover )
{
    unsigned T;
    const Drw_LibClass_t * c;
    int Lits[256], i, k, Lev, Best = -1, BestLev = ABC_INFINITY, BestSize = ABC_INFINITY;
    assert( Vec_IntSize( vLeaves ) <= 4 );
    T = Drw_Transforms[(unsigned short)Truth];
    c = Drw_Classes + ( T & 255 );
    if ( !c->nRoots ) return Dsm_ManTruthToGia( q, &Truth, vLeaves, vCover );
    assert( c->nNodes + 4 <= 256 );
    memset( Lits, 0xFF, sizeof( Lits ) );
    for ( i = 0; i < 4; i++ )
    {
        int Pos = ( T >> ( 13 + 2 * i ) ) & 3;
        Lits[i] = ( Pos < Vec_IntSize( vLeaves ) ? Vec_IntEntry( vLeaves, Pos ) : 0 ) ^ ( ( T >> ( 8 + i ) ) & 1 );
    }
    for ( i = 0; i < c->nRoots; i++ )
    {
        const signed char * Depths = Drw_LibDepths[c->iRoots + i];
        Lev = 0;
        for ( k = 0; k < 4; k++ )
            if ( Depths[k] >= 0 ) Lev = Abc_MaxInt( Lev, Gia_ObjLevelId( q, Lits[k] >> 1 ) + Depths[k] );
        if ( Lev > BestLev || ( Lev == BestLev && Drw_LibSizes[c->iRoots + i] >= BestSize ) ) continue;
        Best = i;
        BestLev = Lev;
        BestSize = Drw_LibSizes[c->iRoots + i];
    }
    assert( Best >= 0 );
    i = Drw_LibRoots[c->iRoots + Best];
    return Dch2_LutBuild_rec( q, c, i >> 1, Lits ) ^ ( i & 1 ) ^ ( ( T >> 12 ) & 1 );
}
typedef struct
{
    int n, Leaf[4];
} Dch2_QuickCut_t;
/**Function*************************************************************

  Synopsis    [Merges sorted supports for a four-input cut.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Dch2_QuickMerge( Dch2_QuickCut_t * a, Dch2_QuickCut_t * b, Dch2_QuickCut_t * r )
{
    int i = 0, k = 0, Id;
    r->n = 0;
    while ( i < a->n || k < b->n )
    {
        if ( r->n == 4 ) return 0;
        if ( k == b->n || ( i < a->n && a->Leaf[i] < b->Leaf[k] ) )
            Id = a->Leaf[i++];
        else if ( i == a->n || b->Leaf[k] < a->Leaf[i] )
            Id = b->Leaf[k++];
        else
        {
            Id = a->Leaf[i++];
            k++;
        }
        r->Leaf[r->n++] = Id;
    }
    return 1;
}
/**Function*************************************************************

  Synopsis    [Finds a quick four-input cover and its critical roots.]

  Description [At equal depth, prefer the larger support. The returned temporary GIA
  carries the cover; the vector marks referenced roots with no level slack.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Dch2_QuickMap( Gia_Man_t * p, Vec_Int_t ** pvMap )
{
    Gia_Man_t * q = Gia_ManDup( p );
    Dch2_QuickCut_t * Cuts = ABC_CALLOC( Dch2_QuickCut_t, Gia_ManObjNum( p ) );
    int * Levels = ABC_CALLOC( int, Gia_ManObjNum( p ) );
    unsigned char * Used = ABC_CALLOC( unsigned char, Gia_ManObjNum( p ) );
    Vec_Int_t * vMap = Vec_IntStart( Gia_ManObjNum( p ) );
    Gia_Obj_t * o;
    Dch2_QuickCut_t ua, ub, r, *a, *b;
    int i, j, k, ia, ib, Lev, Best, Target = 0;
    int * Required = ABC_ALLOC( int, Gia_ManObjNum( p ) );
    Gia_ManForEachCi ( p, o, i )
    {
        j = Gia_ObjId( p, o );
        Cuts[j].n = 1;
        Cuts[j].Leaf[0] = j;
    }
    Gia_ManForEachAnd ( p, o, i )
    {
        ia = Gia_ObjFaninId0( o, i );
        ib = Gia_ObjFaninId1( o, i );
        ua.n = 1;
        ua.Leaf[0] = ia;
        ub.n = 1;
        ub.Leaf[0] = ib;
        Best = ABC_INFINITY;
        for ( k = 0; k < 4; k++ )
        {
            a = ( k & 1 ) ? &ua : Cuts + ia;
            b = ( k & 2 ) ? &ub : Cuts + ib;
            if ( !Dch2_QuickMerge( a, b, &r ) ) continue;
            Lev = 0;
            for ( j = 0; j < r.n; j++ ) Lev = Abc_MaxInt( Lev, Levels[r.Leaf[j]] );
            Lev++;
            if ( Lev > Best || ( Lev == Best && r.n <= Cuts[i].n ) ) continue;
            Best = Lev;
            Cuts[i] = r;
        }
        assert( Best < ABC_INFINITY );
        Levels[i] = Best;
    }
    for ( i = 0; i < Gia_ManObjNum( p ); i++ ) Required[i] = ABC_INFINITY;
    Gia_ManForEachCo ( p, o, i ) Target = Abc_MaxInt( Target, Levels[Gia_ObjFaninId0p( p, o )] );
    Gia_ManForEachCo ( p, o, i )
    {
        j = Gia_ObjFaninId0p( p, o );
        Used[j] = 1;
        Required[j] = Target;
    }
    for ( i = Gia_ManObjNum( p ) - 1; i > 0; i-- )
        if ( Used[i] && Gia_ObjIsAnd( Gia_ManObj( p, i ) ) )
            for ( j = 0; j < Cuts[i].n; j++ )
            {
                k = Cuts[i].Leaf[j];
                Used[k] = 1;
                Required[k] = Abc_MinInt( Required[k], Required[i] - 1 );
            }
    q->vMapping = Vec_IntStart( Gia_ManObjNum( q ) );
    Gia_ManForEachAnd ( p, o, i )
        if ( Used[i] )
        {
            Vec_IntWriteEntry( q->vMapping, i, Vec_IntSize( q->vMapping ) );
            Vec_IntPush( q->vMapping, Cuts[i].n );
            for ( j = 0; j < Cuts[i].n; j++ ) Vec_IntPush( q->vMapping, Cuts[i].Leaf[j] );
            Vec_IntPush( q->vMapping, i );
        }
    for ( i = 0; i < Gia_ManObjNum( p ); i++ ) Vec_IntWriteEntry( vMap, i, Used[i] && Required[i] - Levels[i] <= 0 );
    ABC_FREE( Required );
    ABC_FREE( Cuts );
    ABC_FREE( Levels );
    ABC_FREE( Used );
    *pvMap = vMap;
    return q;
}

/**Function*************************************************************

  Synopsis    [Adds construction-proved alternatives at critical cover roots.]

  Description [A cut truth table proves each replacement directly. Only unused roots
  created in this call become alternatives. Older dangling snapshot nodes may
  precede the representative and cannot be linked as its choice members.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Dch2_AddLocal( Gia_Man_t * p, int fVerbose )
{
    Gia_Man_t * g;
    Vec_Int_t *vMap, *vNext, *vMember, *vRefs, *vLeaves = Vec_IntAlloc( 6 ), *vCover = Vec_IntAlloc( 64 );
    Gia_Obj_t * o;
    int nOld = Gia_ManObjNum( p ), i, j, k, Var, Lit, Start, End, Added = 0;
    word Truth;
    g = Dch2_QuickMap( p, &vMap );
    vNext = Vec_IntStart( nOld );
    vMember = Vec_IntStart( nOld );
    vRefs = Vec_IntStart( nOld );
    for ( i = 0; i < nOld; i++ )
    {
        Vec_IntWriteEntry( vNext, i, Gia_ObjNext( p, i ) );
        Vec_IntWriteEntry( vMember, i, Gia_ObjHasRepr( p, i ) );
    }
    Gia_ManForEachAnd ( p, o, i )
    {
        Vec_IntAddToEntry( vRefs, Gia_ObjFaninId0( o, i ), 1 );
        Vec_IntAddToEntry( vRefs, Gia_ObjFaninId1( o, i ), 1 );
    }
    Gia_ManForEachCo ( p, o, i ) Vec_IntAddToEntry( vRefs, Gia_ObjFaninId0p( p, o ), 1 );
    ABC_FREE( p->pReprs );
    ABC_FREE( p->pNexts );
    Gia_ManLevelNum( p );
    Gia_ManHashStart( p );
    Gia_ObjComputeTruthTableStart( g, 4 );
    Gia_ManForEachLut ( g, i )
    {
        if ( !Vec_IntEntry( vMap, i ) ) continue;
        Vec_IntClear( vLeaves );
        Gia_LutForEachFanin ( g, i, Var, k ) Vec_IntPush( vLeaves, Var );
        Truth = *Gia_ObjComputeTruthTableCut( g, Gia_ManObj( g, i ), vLeaves );
        for ( k = 0; k < Vec_IntSize( vLeaves ); k++ ) Vec_IntWriteEntry( vLeaves, k, 2 * Vec_IntEntry( vLeaves, k ) );
        Start = Gia_ManObjNum( p );
        Lit = Dch2_LutBuild( p, Truth, vLeaves, vCover );
        End = Gia_ManObjNum( p );
        Vec_IntFillExtra( vNext, End, 0 );
        Vec_IntFillExtra( vMember, End, 0 );
        Vec_IntFillExtra( vRefs, End, 0 );
        for ( j = Start; j < End; j++ )
        {
            o = Gia_ManObj( p, j );
            Vec_IntAddToEntry( vRefs, Gia_ObjFaninId0( o, j ), 1 );
            Vec_IntAddToEntry( vRefs, Gia_ObjFaninId1( o, j ), 1 );
        }
        Var = Lit >> 1;
        if ( Var < nOld || !Gia_ObjIsAnd( Gia_ManObj( p, Var ) ) || Vec_IntEntry( vRefs, Var ) ||
             Vec_IntEntry( vMember, Var ) || Vec_IntEntry( vNext, Var ) )
            continue;
        assert( !Vec_IntEntry( vMember, i ) );
        Vec_IntWriteEntry( vNext, Var, Vec_IntEntry( vNext, i ) );
        Vec_IntWriteEntry( vNext, i, Var );
        Vec_IntWriteEntry( vMember, Var, 1 );
        Added++;
    }
    Gia_ObjComputeTruthTableStop( g );
    Gia_ManStop( g );
    Gia_ManHashStop( p );
    p->pNexts = Vec_IntReleaseArray( vNext );
    Vec_IntFree( vNext );
    p->pReprs = ABC_CALLOC( Gia_Rpr_t, Gia_ManObjNum( p ) );
    for ( i = 0; i < Gia_ManObjNum( p ); i++ ) Gia_ObjSetRepr( p, i, GIA_VOID );
    for ( i = 0; i < Gia_ManObjNum( p ); i++ )
        if ( Gia_ObjNext( p, i ) && !Vec_IntEntry( vMember, i ) )
            for ( Var = Gia_ObjNext( p, i ); Var; Var = Gia_ObjNext( p, Var ) ) Gia_ObjSetRepr( p, Var, i );
    Gia_ManRemoveBadChoices( p );
    if ( fVerbose ) Abc_Print( 1, "Post-SAT local alternatives: %d, added nodes %d\n", Added, Gia_ManObjNum( p ) - nOld );
    Vec_IntFree( vMap );
    Vec_IntFree( vMember );
    Vec_IntFree( vRefs );
    Vec_IntFree( vLeaves );
    Vec_IntFree( vCover );
}

/**Function*************************************************************

  Synopsis    [Collects alternatives without repeated fanin-cone cycle searches.]

  Description [Only dangling alternative roots become choices. Cycles in the combined
  fanin and choice graph are rejected during export.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Dch2_Collect( Gia_Man_t * p, int nSnapshots )
{
    Gia_Man_t * q = Gia_ManStart( Gia_ManObjNum( p ) );
    Vec_Int_t * vTail = Vec_IntStart( Gia_ManObjNum( p ) );
    Gia_Obj_t *o, *r;
    int i, Lit, Root, Prev;
    q->pName = Abc_UtilStrsav( p->pName );
    q->pSpec = Abc_UtilStrsav( p->pSpec );
    q->pNexts = ABC_CALLOC( int, Gia_ManObjNum( p ) );
    q->pReprs = ABC_CALLOC( Gia_Rpr_t, Gia_ManObjNum( p ) );
    for ( i = 0; i < Gia_ManObjNum( p ); i++ ) q->pReprs[i].iRepr = GIA_VOID;
    Gia_ManFillValue( p );
    Gia_ManConst0( p )->Value = 0;
    Gia_ManForEachCi ( p, o, i ) o->Value = Gia_ManAppendCi( q );
    Gia_ManHashAlloc( q );
    Gia_ManForEachAnd ( p, o, i )
    {
        r = Gia_ObjReprObj( p, i );
        if ( r && Gia_ObjIsConst0( r ) )
        {
            o->Value = o->fPhase;
            continue;
        }
        Lit = o->Value = Gia_ManHashAnd( q, Gia_ObjFanin0Copy( o ), Gia_ObjFanin1Copy( o ) );
        if ( !r ) continue;
        Root = r->Value ^ r->fPhase ^ o->fPhase;
        if ( ( Lit >> 1 ) != ( Root >> 1 ) && Lit > Root && Gia_ObjIsAnd( Gia_ManObj( q, Root >> 1 ) ) &&
             Gia_ObjIsAnd( Gia_ManObj( q, Lit >> 1 ) ) && !Gia_ObjHasRepr( q, Lit >> 1 ) && !Gia_ObjNext( q, Lit >> 1 ) )
        {
            // Choice links store IDs; the mapper recovers polarity from phases.
            Prev = Vec_IntEntry( vTail, Root >> 1 );
            Gia_ObjSetNext( q, Prev ? Prev : Root >> 1, Lit >> 1 );
            Vec_IntWriteEntry( vTail, Root >> 1, Lit >> 1 );
            Gia_ObjSetRepr( q, Lit >> 1, Root >> 1 );
        }
        o->Value = Root;
    }
    Gia_ManForEachCo ( p, o, i )
        if ( i % nSnapshots == 0 ) Gia_ManAppendCo( q, Gia_ObjFanin0Copy( o ) );
    Gia_ManHashStop( q );
    Gia_ManRemoveBadChoices( q );
    Vec_IntFree( vTail );
    return q;
}

/**Function*************************************************************

  Synopsis    [Copies fanins and alternatives with iterative cycle rejection.]

  Description [Each stack frame stores an ID, traversal state, and next alternative.
  A back edge fails the current alternative. Completed fanins are reusable.
  Alternatives precede their representative, as required by pSibls.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Dch2_Copy( Gia_Man_t * p, Gia_Man_t * q, int Id, Vec_Int_t * vStack, int * pnRejected )
{
    Gia_Obj_t * pObj;
    int Pos, State, Next, Result = -1, Alt;
    assert( Vec_IntSize( vStack ) == 0 );
    Vec_IntPush( vStack, Id );
    Vec_IntPush( vStack, 0 );
    Vec_IntPush( vStack, 0 );
    while ( Vec_IntSize( vStack ) )
    {
        Pos = Vec_IntSize( vStack ) - 3;
        Id = Vec_IntEntry( vStack, Pos );
        State = Vec_IntEntry( vStack, Pos + 1 );
        pObj = Gia_ManObj( p, Id );
        if ( State == 0 )
        {
            if ( pObj->fMark0 || ~pObj->Value )
            {
                Result = pObj->fMark0 ? -1 : (int)pObj->Value;
                Vec_IntShrink( vStack, Pos );
                continue;
            }
            assert( Gia_ObjIsAnd( pObj ) );
            pObj->fMark0 = 1;
            Vec_IntWriteEntry( vStack, Pos + 1, 1 );
            Next = Gia_ObjFaninId0( pObj, Id );
        }
        else if ( State == 1 || State == 2 )
        {
            if ( Result < 0 )
            {
                pObj->fMark0 = 0;
                Vec_IntShrink( vStack, Pos );
                continue;
            }
            if ( State == 1 )
            {
                Vec_IntWriteEntry( vStack, Pos + 1, 2 );
                Next = Gia_ObjFaninId1( pObj, Id );
            }
            else
            {
                Next = Gia_ObjNext( p, Id );
                if ( !Next )
                {
                    Alt = -1;
                    goto emit;
                }
                Vec_IntWriteEntry( vStack, Pos + 1, 3 );
                Vec_IntWriteEntry( vStack, Pos + 2, Next );
            }
        }
        else
        {
            if ( Result >= 0 )
            {
                Alt = Result;
                goto emit;
            }
            ( *pnRejected )++;
            Next = Gia_ObjNext( p, Vec_IntEntry( vStack, Pos + 2 ) );
            if ( !Next )
            {
                Alt = -1;
                goto emit;
            }
            Vec_IntWriteEntry( vStack, Pos + 2, Next );
        }
        Vec_IntPush( vStack, Next );
        Vec_IntPush( vStack, 0 );
        Vec_IntPush( vStack, 0 );
        continue;
    emit:
        Result = Gia_ManAppendAnd( q, Gia_ObjFanin0Copy( pObj ), Gia_ObjFanin1Copy( pObj ) );
        if ( Alt >= 0 ) q->pSibls[Result >> 1] = Alt >> 1;
        pObj->Value = Result;
        pObj->fMark0 = 0;
        Vec_IntShrink( vStack, Pos );
    }
    return Result;
}
/**Function*************************************************************

  Synopsis    [Exports an acyclic choice GIA in mapper order.]

  Description [Rejected alternatives can leave unreachable completed nodes. Cleanup
  precedes deriving representatives because the sibling-derived convention
  differs from the collector's convention.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Dch2_Export( Gia_Man_t * p )
{
    Gia_Man_t * q = Gia_ManStart( Gia_ManObjNum( p ) );
    Gia_Obj_t * o;
    Vec_Int_t * vStack = Vec_IntAlloc( 384 );
    int i, Lit, nRejected = 0;
    q->pName = Abc_UtilStrsav( p->pName );
    q->pSpec = Abc_UtilStrsav( p->pSpec );
    q->pSibls = ABC_CALLOC( int, Gia_ManObjNum( p ) );
    Gia_ManFillValue( p );
    Gia_ManConst0( p )->Value = 0;
    Gia_ManForEachCi ( p, o, i ) o->Value = Gia_ManAppendCi( q );
    Gia_ManForEachCo ( p, o, i )
    {
        Lit = Dch2_Copy( p, q, Gia_ObjFaninId0p( p, o ), vStack, &nRejected );
        if ( Lit < 0 )
        {
            Vec_IntFree( vStack );
            Gia_ManStop( q );
            return NULL;
        }
    }
    Vec_IntFree( vStack );
    Gia_ManForEachCo ( p, o, i ) Gia_ManAppendCo( q, Gia_ObjFanin0Copy( o ) );
    if ( nRejected )
    {
        Gia_Man_t * r = Gia_ManCleanup( q );
        Gia_ManStop( q );
        q = r;
    }
    Gia_ManDeriveReprsFromSibls( q );
    return q;
}

/**Function*************************************************************

  Synopsis    [Builds choices from two or three fast DC3 synthesis snapshots.]

  Description [The final snapshot supplies the primary implementation. Construction
  proofs and SAT-proved equalities connect the alternatives. The caller
  retains the input; the result is independently owned.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Dch2_Perform( Gia_Man_t * p, int nSnapshots, int nConfs, int nConfsChoice, int fKeepLevel,
                                 int fSweep, int fMore, int fVerbose )
{
    Gia_Man_t *pLast, *pMiddle = NULL, *pMiter, *pChoices, *pNew;
    Vec_Ptr_t *vSnapshots, *vLabels;
    Vec_Int_t *vKnown, *vMap, *vOrigins, *vEquivs;
    Gia_Man_t * pReduced;
    int k;
    abctime Start = Abc_Clock(), Synth, Merge, Sweep, Export;
    int nMiterAnds, nChoices;
    if ( !p || ( nSnapshots != 2 && nSnapshots != 3 ) || nConfs < 0 || nConfsChoice < 0 || Gia_ManHasChoices( p ) ||
         Gia_ManMuxNum( p ) || Gia_ManXorNum( p ) || Gia_ManBufNum( p ) || Gia_ManObjNum( p ) > INT_MAX / 16 )
        return NULL;
    if ( Gia_ManIsSeqWithBoxes( p ) && !Gia_ManIsNormalized( p ) ) return NULL;
    vLabels = Vec_PtrAlloc( nSnapshots );
    pLast = Gia_ManDc3SnapshotsMore( p, fKeepLevel, fVerbose, &pMiddle, vLabels, fMore );
    if ( !pLast )
    {
        if ( pMiddle ) Gia_ManStop( pMiddle );
        for ( k = 0; k < Vec_PtrSize( vLabels ); k++ ) Vec_IntFree( (Vec_Int_t *)Vec_PtrEntry( vLabels, k ) );
        Vec_PtrFree( vLabels );
        return NULL;
    }
    Synth = Abc_Clock() - Start;
    vSnapshots = Vec_PtrAlloc( nSnapshots );
    Vec_PtrPush( vSnapshots, pLast );
    if ( pMiddle ) Vec_PtrPush( vSnapshots, pMiddle );
    if ( nSnapshots == 2 )
    {
        Vec_IntFree( (Vec_Int_t *)Vec_PtrEntry( vLabels, 0 ) );
        Vec_PtrDrop( vLabels, 0 );
    }
    else
        Vec_PtrPush( vSnapshots, p );
    Merge = Abc_Clock();
    pMiter = Gia_ManChoiceMiter( vSnapshots );
    vOrigins = Vec_IntStart( Gia_ManObjNum( pMiter ) );
    vKnown = Dch2_Known( pMiter, vSnapshots, vLabels, vOrigins );
    for ( k = 0; k < Vec_PtrSize( vLabels ); k++ ) Vec_IntFree( (Vec_Int_t *)Vec_PtrEntry( vLabels, k ) );
    Vec_PtrFree( vLabels );
    nSnapshots = Vec_PtrSize( vSnapshots );
    Vec_PtrFree( vSnapshots );
    Gia_ManStop( pLast );
    if ( pMiddle ) Gia_ManStop( pMiddle );
    nMiterAnds = Gia_ManAndNum( pMiter );
    Merge = Abc_Clock() - Merge;
    Sweep = Abc_Clock();
    pReduced = Dch2_Reduce( pMiter, vKnown, &vMap, &vOrigins, nSnapshots );
    vEquivs = Vec_IntAlloc( Gia_ManObjNum( pReduced ) );
    if ( fVerbose )
        Abc_Print( 1, "Provenance reduction: %d -> %d ANDs\n", Gia_ManAndNum( pMiter ), Gia_ManAndNum( pReduced ) );
    if ( !fSweep )
    {
        // Reduction already merged construction-proved and hashed equalities.
        // Identity here adds no unproved relation to those exact merges.
        for ( k = 0; k < Gia_ManObjNum(pReduced); k++ ) Vec_IntPush( vEquivs, 2*k );
    }
    else if ( !CecZ_ManComputeEquivs( pReduced, vOrigins, vEquivs, nConfs, nConfsChoice, fVerbose ) )
    {
        Gia_ManStop( pMiter );
        Gia_ManStop( pReduced );
        Vec_IntFree( vMap );
        Vec_IntFree( vKnown );
        Vec_IntFree( vOrigins );
        Vec_IntFree( vEquivs );
        return NULL;
    }
    Dch2_Restore( pMiter, vMap, vEquivs );
    Vec_IntFree( vEquivs );
    Gia_ManStop( pReduced );
    Vec_IntFree( vMap );
    Vec_IntFree( vKnown );
    Vec_IntFree( vOrigins );
    Sweep = Abc_Clock() - Sweep;
    Export = Abc_Clock();
    pChoices = Dch2_Collect( pMiter, nSnapshots );
    Gia_ManStop( pMiter );
    Dch2_AddLocal( pChoices, fVerbose );
    pNew = Dch2_Export( pChoices );
    Gia_ManStop( pChoices );
    if ( !pNew ) return NULL;
    Gie_ManDupMetadata( pNew, p );
    nChoices = Gia_ManChoiceNum( pNew );
    Export = Abc_Clock() - Export;
    if ( fVerbose )
    {
        Abc_Print( 1, "&dch2: %d snapshots, %d merged ANDs, %d result ANDs, %d choices.\n", nSnapshots, nMiterAnds,
                   Gia_ManAndNum( pNew ), nChoices );
        Abc_Print( 1, "&dch2: synthesis %.3f  merge %.3f  sweep %.3f  export %.3f  total %.3f sec\n",
                   (double)Synth / CLOCKS_PER_SEC, (double)Merge / CLOCKS_PER_SEC, (double)Sweep / CLOCKS_PER_SEC,
                   (double)Export / CLOCKS_PER_SEC, (double)( Abc_Clock() - Start ) / CLOCKS_PER_SEC );
    }
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Collects construction and SAT-proved synthesis choices.]

  Description [Preserves the existing DCH2 command and resource limits.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDch2( Gia_Man_t * p, int nSnapshots, int nConfs, int nConfsChoice, int fKeepLevel, int fVerbose )
{
    return Dch2_Perform( p, nSnapshots, nConfs, nConfsChoice, fKeepLevel, 1, 0, fVerbose );
}

/**Function*************************************************************

  Synopsis    [Collects construction-proved choices without SAT sweeping.]

  Description [Two synthesized structures remain available to the mapper.
  Every alternative follows from an exact synthesis operation
  or structural hashing; simulation classes are not used as proofs.
  Extra synthesis passes depend on measured structural gain.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDch2Construct( Gia_Man_t * p, int fKeepLevel, int fVerbose )
{
    return Dch2_Perform( p, 2, 0, 0, fKeepLevel, 0, 1, fVerbose );
}

/**Function*************************************************************

  Synopsis    [Exports proven representative relations as acyclic choices.]

  Description [All outputs are retained. The caller supplies sound representative
  relations, including phases, and retains ownership of the input GIA.]

  SideEffects [Uses the input objects' scratch values.]

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDch2DeriveChoices( Gia_Man_t * p )
{
    Gia_Man_t * q = Dch2_Collect( p, 1 );
    Gia_Man_t * r = Dch2_Export( q );
    Gia_ManStop( q );
    if ( r ) Gia_ManSetRegNum( r, Gia_ManRegNum(p) );
    return r;
}

ABC_NAMESPACE_IMPL_END
