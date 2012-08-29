/**CFile****************************************************************

  FileName    [sclBuff.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  Synopsis    [Standard-cell library representation.]

  Author      [Alan Mishchenko, Niklas Een]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 24, 2012.]

  Revision    [$Id: sclBuff.c,v 1.0 2012/08/24 00:00:00 alanmi Exp $]

***********************************************************************/

#include "base/abc/abc.h"
#include "map/mio/mio.h"
#include "sclInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Make sure the network has no dangling nodes.]

  Description [Returns 1 iff the network is fine.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_SclCheckNtk( Abc_Ntk_t * p, int fVerbose )
{
    Abc_Obj_t * pObj, * pFanin;
    int i, k, fFlag = 1;
    Abc_NtkIncrementTravId( p );        
    Abc_NtkForEachCi( p, pObj, i )
        Abc_NodeSetTravIdCurrent( pObj );
    Abc_NtkForEachNode( p, pObj, i )
    {
        Abc_ObjForEachFanin( pObj, pFanin, k )
            if ( !Abc_NodeIsTravIdCurrent( pFanin ) )
                printf( "obj %d and its fanin %d are not in the topo order\n", Abc_ObjId(pObj), Abc_ObjId(pFanin) ), fFlag = 0;
        Abc_NodeSetTravIdCurrent( pObj );
        if ( Abc_ObjFanoutNum(pObj) == 0 )
            printf( "node %d has no fanout\n", Abc_ObjId(pObj) ), fFlag = 0;
    }
    if ( fFlag && fVerbose )
        printf( "The network is in topo order and no dangling nodes.\n" );
    return fFlag;
}

/**Function*************************************************************

  Synopsis    [Make sure the network has no dangling nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_SclCheckNtk2( Abc_Ntk_t * p )
{
    Abc_Obj_t * pObj, * pFanout;
    int i, k, fFlag = 0;
    Abc_NtkStartReverseLevels( p, 0 );
    Abc_NtkForEachNode( p, pObj, i )
    {
        if ( Abc_ObjFanoutNum(pObj) <= 3 )
            continue;
        printf( "Node %5d (%2d) : fans = %3d  ", i, Abc_ObjLevel(pObj), Abc_ObjFanoutNum(pObj) );
        Abc_ObjForEachFanout( pObj, pFanout, k )
            printf( "%d ", Abc_ObjReverseLevel(pFanout) );
        printf( "\n" );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Performs buffering of the mapped network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeCompareLevels( Abc_Obj_t ** pp1, Abc_Obj_t ** pp2 )
{
    int Diff = Abc_ObjLevel(*pp1) - Abc_ObjLevel(*pp2);
    if ( Diff < 0 )
        return -1;
    if ( Diff > 0 ) 
        return 1;
    Diff = (*pp1)->Id - (*pp2)->Id;
    if ( Diff < 0 )
        return -1;
    if ( Diff > 0 ) 
        return 1;
    return 0; 
}
int Abc_SclComputeReverseLevel( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanout;
    int i, Level = 0;
    Abc_ObjForEachFanout( pObj, pFanout, i )
        Level = Abc_MaxInt( Level, pFanout->Level );
    return Level + 1;
}
Abc_Obj_t * Abc_SclPerformBufferingOne( Abc_Obj_t * pObj, int Degree, int fVerbose )
{
    Vec_Ptr_t * vFanouts;
    Abc_Obj_t * pBuffer, * pFanout;
    int i, Degree0 = Degree;
    assert( Abc_ObjFanoutNum(pObj) > Degree );
    // collect fanouts and sort by reverse level
    vFanouts = Vec_PtrAlloc( Abc_ObjFanoutNum(pObj) );
    Abc_NodeCollectFanouts( pObj, vFanouts );
    Vec_PtrSort( vFanouts, Abc_NodeCompareLevels );
    // select the first Degree fanouts
    pBuffer = Abc_NtkCreateNodeBuf( pObj->pNtk, NULL );
    // check if it is possible to not increase level
    if ( Vec_PtrSize(vFanouts) < 2 * Degree )
    {
        Abc_Obj_t * pFanPrev = (Abc_Obj_t *)Vec_PtrEntry(vFanouts, Vec_PtrSize(vFanouts)-1-Degree);
        Abc_Obj_t * pFanThis = (Abc_Obj_t *)Vec_PtrEntry(vFanouts, Degree-1);
        Abc_Obj_t * pFanLast = (Abc_Obj_t *)Vec_PtrEntryLast(vFanouts);
        if ( Abc_ObjLevel(pFanThis) == Abc_ObjLevel(pFanLast) &&
             Abc_ObjLevel(pFanPrev) <  Abc_ObjLevel(pFanThis) )
        {
            // find the first one whose level is the same as last
            Vec_PtrForEachEntry( Abc_Obj_t *, vFanouts, pFanout, i )
                if ( Abc_ObjLevel(pFanout) == Abc_ObjLevel(pFanLast) )
                    break;
            assert( i < Vec_PtrSize(vFanouts) );
            if ( i > 1 )
                Degree = i;
        }
        // make the last two more well-balanced
        if ( Degree == Degree0 && Degree > Vec_PtrSize(vFanouts) - Degree )
            Degree = Vec_PtrSize(vFanouts)/2 + (Vec_PtrSize(vFanouts) & 1);
        assert( Degree <= Degree0 );
    }
    // select fanouts
    Vec_PtrForEachEntryStop( Abc_Obj_t *, vFanouts, pFanout, i, Degree )
        Abc_ObjPatchFanin( pFanout, pObj, pBuffer );
    if ( fVerbose )
    {
        printf( "%5d : ", Abc_ObjId(pObj) );
        Vec_PtrForEachEntry( Abc_Obj_t *, vFanouts, pFanout, i )
            printf( "%d%s ", Abc_ObjLevel(pFanout), i == Degree-1 ? "  " : "" );
        printf( "\n" );
    }
    Vec_PtrFree( vFanouts );
    Abc_ObjAddFanin( pBuffer, pObj );
    pBuffer->Level = Abc_SclComputeReverseLevel( pBuffer );
    return pBuffer;
}
void Abc_SclPerformBuffering_rec( Abc_Obj_t * pObj, int Degree, int fVerbose )
{
    Abc_Obj_t * pFanout;
    int i;
    if ( Abc_NodeIsTravIdCurrent( pObj ) )
        return;
    Abc_NodeSetTravIdCurrent( pObj );
    pObj->Level = 0;
    if ( Abc_ObjIsCo(pObj) )
        return;
    assert( Abc_ObjIsCi(pObj) || Abc_ObjIsNode(pObj) );
    // buffer fanouts and collect reverse levels
    Abc_ObjForEachFanout( pObj, pFanout, i )
        Abc_SclPerformBuffering_rec( pFanout, Degree, fVerbose );
    // perform buffering as long as needed
    while ( Abc_ObjFanoutNum(pObj) > Degree )
        Abc_SclPerformBufferingOne( pObj, Degree, fVerbose );
    // compute the new level of the node
    pObj->Level = Abc_SclComputeReverseLevel( pObj );
}
Abc_Ntk_t * Abc_SclPerformBuffering( Abc_Ntk_t * p, int Degree, int fVerbose )
{
    Abc_Ntk_t * pNew;
    Abc_Obj_t * pObj;
    int i;
    assert( Abc_NtkHasMapping(p) );
    Abc_NtkIncrementTravId( p );        
    Abc_NtkForEachCi( p, pObj, i )
        Abc_SclPerformBuffering_rec( pObj, Degree, fVerbose );
    Abc_NtkLevel( p );
    // duplication in topo order
    pNew = Abc_NtkDupDfs( p );
    Abc_SclCheckNtk( pNew, fVerbose );
//    Abc_NtkDelete( pNew );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

