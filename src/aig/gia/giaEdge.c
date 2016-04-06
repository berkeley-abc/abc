/**CFile****************************************************************

  FileName    [giaEdge.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Edge-related procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaEdge.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline int Sbm_ObjEdgeCount( int iObj, Vec_Int_t * vEdge1, Vec_Int_t * vEdge2 )
{
    return (Vec_IntEntry(vEdge1, iObj) > 0) + (Vec_IntEntry(vEdge2, iObj) > 0);
}
static inline void Sbm_ObjEdgeAdd( int iObj, int iNext, Vec_Int_t * vEdge1, Vec_Int_t * vEdge2 )
{
    if ( Vec_IntEntry(vEdge1, iObj) == 0 )
        Vec_IntWriteEntry(vEdge1, iObj, iNext);
    else if ( Vec_IntEntry(vEdge2, iObj) == 0 )
        Vec_IntWriteEntry(vEdge2, iObj, iNext);
    else assert( 0 );
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Transforms edge assignment.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManEdgeFromArray( Gia_Man_t * p, Vec_Int_t * vArray )
{
    int i, iObj1, iObj2;
    Vec_IntFreeP( &p->vEdge1 );
    Vec_IntFreeP( &p->vEdge1 );
    p->vEdge1 = Vec_IntStart( Gia_ManObjNum(p) );
    p->vEdge2 = Vec_IntStart( Gia_ManObjNum(p) );
    Vec_IntForEachEntryDouble( vArray, iObj1, iObj2, i )
    {
        assert( iObj1 != iObj2 );
        Sbm_ObjEdgeAdd( iObj1, iObj2, p->vEdge1, p->vEdge2 );
        Sbm_ObjEdgeAdd( iObj2, iObj1, p->vEdge1, p->vEdge2 );
    }
}
Vec_Int_t * Gia_ManEdgeToArray( Gia_Man_t * p )
{
    int i, Entry;
    Vec_Int_t * vArray = Vec_IntAlloc( 1000 );
    assert( p->vEdge1 && p->vEdge2 );
    assert( Vec_IntSize(p->vEdge1) == Gia_ManObjNum(p) );
    assert( Vec_IntSize(p->vEdge2) == Gia_ManObjNum(p) );
    for ( i = 0; i < Gia_ManObjNum(p); i++ )
    {
        Entry = Vec_IntEntry(p->vEdge1, i);
        if ( Entry && Entry < i )
            Vec_IntPushTwo( vArray, Entry, i );
        Entry = Vec_IntEntry(p->vEdge2, i);
        if ( Entry && Entry < i )
            Vec_IntPushTwo( vArray, Entry, i );
    }
    return vArray;
}

/**Function*************************************************************

  Synopsis    [Evaluates given edge assignment.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Gia_ObjHaveEdge( Gia_Man_t * p, int iObj, int iNext )
{
    return Vec_IntEntry(p->vEdge1, iObj) == iNext || Vec_IntEntry(p->vEdge2, iObj) == iNext;
}
static inline int Gia_ObjEvalEdgeDelay( Gia_Man_t * p, int iObj, Vec_Int_t * vDelay )
{
    int i, iFan, Delay, DelayMax = 0;
    assert( Gia_ObjIsLut(p, iObj) );
    assert( Gia_ObjLutSize(p, iObj) <= 4 );
    Gia_LutForEachFanin( p, iObj, iFan, i )
    {
        Delay = Vec_IntEntry(vDelay, iFan) + !Gia_ObjHaveEdge(p, iObj, iFan);
        DelayMax = Abc_MaxInt( DelayMax, Delay );
    }
    return DelayMax;
}
int Gia_ManEvalEdgeDelay( Gia_Man_t * p )
{
    int k, iLut, DelayMax = 0;
    assert( p->vEdge1 && p->vEdge2 );
    Vec_IntFreeP( &p->vEdgeDelay );
    p->vEdgeDelay = Vec_IntStart( Gia_ManObjNum(p) );
    Gia_ManForEachLut( p, iLut )
        Vec_IntWriteEntry( p->vEdgeDelay, iLut, Gia_ObjEvalEdgeDelay(p, iLut, p->vEdgeDelay) );
    Gia_ManForEachCoDriverId( p, iLut, k )
        DelayMax = Abc_MaxInt( DelayMax, Vec_IntEntry(p->vEdgeDelay, iLut) );
    return DelayMax;
}


/**Function*************************************************************

  Synopsis    [Finds edge assignment.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ObjComputeEdgeDelay( Gia_Man_t * p, int iObj, Vec_Int_t * vDelay, Vec_Int_t * vEdge1, Vec_Int_t * vEdge2 )
{
    int i, iFan, Status[4], Delay[4];
    int DelayMax = 0, nCountMax = 0;
    int iFanMax1 = -1, iFanMax2 = -1;
    int iMax1 = -1, iMax2 = -1; 
    assert( Gia_ObjIsLut(p, iObj) );
    assert( Gia_ObjLutSize(p, iObj) <= 4 );
    Vec_IntWriteEntry(vEdge1, iObj, 0);
    Vec_IntWriteEntry(vEdge2, iObj, 0);
    Gia_LutForEachFanin( p, iObj, iFan, i )
    {
        Status[i] = Sbm_ObjEdgeCount( iFan, vEdge1, vEdge2 );
        Delay[i]  = Vec_IntEntry( vDelay, iFan ) + 1;
        if ( DelayMax < Delay[i] )
        {
            DelayMax  = Delay[i];
            iFanMax1  = iFan;
            iMax1     = i;
            nCountMax = 1;
        }
        else if ( DelayMax == Delay[i] )
        {
            iFanMax2  = iFan;
            iMax2     = i;
            nCountMax++;
        }
    }
    assert( nCountMax > 0 );
    if ( nCountMax == 1 && Status[iMax1] <= 1 )
    {
        Sbm_ObjEdgeAdd( iFanMax1, iObj, vEdge1, vEdge2 );
        Sbm_ObjEdgeAdd( iObj, iFanMax1, vEdge1, vEdge2 );
        Vec_IntWriteEntry( vDelay, iObj, DelayMax-1 );
        return 1;
    }
    if ( nCountMax == 2 && Status[iMax1] <= 1 && Status[iMax2] <= 1 )
    {
        Sbm_ObjEdgeAdd( iFanMax1, iObj, vEdge1, vEdge2 );
        Sbm_ObjEdgeAdd( iFanMax2, iObj, vEdge1, vEdge2 );
        Sbm_ObjEdgeAdd( iObj, iFanMax1, vEdge1, vEdge2 );
        Sbm_ObjEdgeAdd( iObj, iFanMax2, vEdge1, vEdge2 );
        Vec_IntWriteEntry( vDelay, iObj, DelayMax-1 );
        return 2;
    }
    Vec_IntWriteEntry( vDelay, iObj, DelayMax );
    return 0;
}
int Gia_ManComputeEdgeDelay( Gia_Man_t * p )
{
    int k, iLut, DelayMax = 0, EdgeCount = 0;
    Vec_IntFreeP( &p->vEdgeDelay );
    Vec_IntFreeP( &p->vEdge1 );
    Vec_IntFreeP( &p->vEdge1 );
    p->vEdge1 = Vec_IntStart( Gia_ManObjNum(p) );
    p->vEdge2 = Vec_IntStart( Gia_ManObjNum(p) );
    p->vEdgeDelay = Vec_IntStart( Gia_ManObjNum(p) );
    Gia_ManForEachLut( p, iLut )
        EdgeCount += Gia_ObjComputeEdgeDelay( p, iLut, p->vEdgeDelay, p->vEdge1, p->vEdge2 );
    Gia_ManForEachCoDriverId( p, iLut, k )
        DelayMax = Abc_MaxInt( DelayMax, Vec_IntEntry(p->vEdgeDelay, iLut) );
    assert( 2 * EdgeCount == Vec_IntCountPositive(p->vEdge1) + Vec_IntCountPositive(p->vEdge2) );
    printf( "The number of edges = %d.  ", EdgeCount );
    printf( "Delay = %d.\n", DelayMax );
    return DelayMax;
}

/**Function*************************************************************

  Synopsis    [Finds edge assignment to reduce delay.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManComputeEdgeDelay2( Gia_Man_t * p )
{
    return 0;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

