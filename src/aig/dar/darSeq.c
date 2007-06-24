/**CFile****************************************************************

  FileName    [darSeq.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: darSeq.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "dar.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Converts combinational AIG manager into a sequential one.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ManSeqStrashConvert( Dar_Man_t * p, int nLatches, int * pInits )
{
    Dar_Obj_t * pObjLi, * pObjLo, * pLatch;
    int i;
    // collect the POs to be converted into latches
    for ( i = 0; i < nLatches; i++ )
    {
        // get the corresponding PI/PO pair
        pObjLi = Dar_ManPo( p, Dar_ManPoNum(p) - nLatches + i );
        pObjLo = Dar_ManPi( p, Dar_ManPiNum(p) - nLatches + i );
        // create latch
        pLatch = Dar_Latch( p, Dar_ObjChild0(pObjLi), pInits? pInits[i] : 0 );
        // recycle the old PO object
        Dar_ObjDisconnect( p, pObjLi );
        Vec_PtrWriteEntry( p->vObjs, pObjLi->Id, NULL );
        Dar_ManRecycleMemory( p, pObjLi );
        // convert the corresponding PI to be a buffer and connect it to the latch
        pObjLo->Type = DAR_AIG_BUF;
        Dar_ObjConnect( p, pObjLo, pLatch, NULL );
    }
    // shrink the arrays
    Vec_PtrShrink( p->vPis, Dar_ManPiNum(p) - nLatches );
    Vec_PtrShrink( p->vPos, Dar_ManPoNum(p) - nLatches );
    // update the counters of different objects
    p->nObjs[DAR_AIG_PI]  -= nLatches;
    p->nObjs[DAR_AIG_PO]  -= nLatches;
    p->nObjs[DAR_AIG_BUF] += nLatches;
}

/**Function*************************************************************

  Synopsis    [Collects internal nodes in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ManDfsSeq_rec( Dar_Man_t * p, Dar_Obj_t * pObj, Vec_Ptr_t * vNodes )
{
    assert( !Dar_IsComplement(pObj) );
    if ( pObj == NULL )
        return;
    if ( Dar_ObjIsTravIdCurrent( p, pObj ) )
        return;
    Dar_ObjSetTravIdCurrent( p, pObj );
    if ( Dar_ObjIsPi(pObj) || Dar_ObjIsConst1(pObj) )
        return;
    Dar_ManDfsSeq_rec( p, Dar_ObjFanin0(pObj), vNodes );
    Dar_ManDfsSeq_rec( p, Dar_ObjFanin1(pObj), vNodes );
//    if ( (Dar_ObjFanin0(pObj) == NULL || Dar_ObjIsBuf(Dar_ObjFanin0(pObj))) &&
//         (Dar_ObjFanin1(pObj) == NULL || Dar_ObjIsBuf(Dar_ObjFanin1(pObj))) )
        Vec_PtrPush( vNodes, pObj );
}

/**Function*************************************************************

  Synopsis    [Collects internal nodes in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Dar_ManDfsSeq( Dar_Man_t * p )
{
    Vec_Ptr_t * vNodes;
    Dar_Obj_t * pObj;
    int i;
    Dar_ManIncrementTravId( p );
    vNodes = Vec_PtrAlloc( Dar_ManNodeNum(p) );
    Dar_ManForEachPo( p, pObj, i )
        Dar_ManDfsSeq_rec( p, Dar_ObjFanin0(pObj), vNodes );
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Collects internal nodes in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ManDfsUnreach_rec( Dar_Man_t * p, Dar_Obj_t * pObj, Vec_Ptr_t * vNodes )
{
    assert( !Dar_IsComplement(pObj) );
    if ( pObj == NULL )
        return;
    if ( Dar_ObjIsTravIdPrevious(p, pObj) || Dar_ObjIsTravIdCurrent(p, pObj) )
        return;
    Dar_ObjSetTravIdPrevious( p, pObj ); // assume unknown
    Dar_ManDfsUnreach_rec( p, Dar_ObjFanin0(pObj), vNodes );
    Dar_ManDfsUnreach_rec( p, Dar_ObjFanin1(pObj), vNodes );
    if ( Dar_ObjIsTravIdPrevious(p, Dar_ObjFanin0(pObj)) && 
        (Dar_ObjFanin1(pObj) == NULL || Dar_ObjIsTravIdPrevious(p, Dar_ObjFanin1(pObj))) )
        Vec_PtrPush( vNodes, pObj );
    else
        Dar_ObjSetTravIdCurrent( p, pObj );
}

/**Function*************************************************************

  Synopsis    [Collects internal nodes unreachable from PIs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Dar_ManDfsUnreach( Dar_Man_t * p )
{
    Vec_Ptr_t * vNodes;
    Dar_Obj_t * pObj, * pFanin;
    int i, k;//, RetValue;
    // collect unreachable nodes
    Dar_ManIncrementTravId( p ); 
    Dar_ManIncrementTravId( p ); 
    // mark the constant and PIs
    Dar_ObjSetTravIdPrevious( p, Dar_ManConst1(p) );
    Dar_ManForEachPi( p, pObj, i )
        Dar_ObjSetTravIdCurrent( p, pObj );
    // curr marks visited nodes reachable from PIs
    // prev marks visited nodes unreachable or unknown

    // collect the unreachable nodes
    vNodes = Vec_PtrAlloc( 32 );
    Dar_ManForEachPo( p, pObj, i )
        Dar_ManDfsUnreach_rec( p, Dar_ObjFanin0(pObj), vNodes );

    // refine resulting nodes
    do 
    {
        k = 0;
        Vec_PtrForEachEntry( vNodes, pObj, i )
        {
            assert( Dar_ObjIsTravIdPrevious(p, pObj) );
            if ( Dar_ObjIsLatch(pObj) || Dar_ObjIsBuf(pObj) )
            {
                pFanin = Dar_ObjFanin0(pObj);
                assert( Dar_ObjIsTravIdPrevious(p, pFanin) || Dar_ObjIsTravIdCurrent(p, pFanin) );
                if ( Dar_ObjIsTravIdCurrent(p, pFanin) )
                {
                    Dar_ObjSetTravIdCurrent( p, pObj );
                    continue;
                }
            }
            else // AND gate
            {
                assert( Dar_ObjIsNode(pObj) );
                pFanin = Dar_ObjFanin0(pObj);
                assert( Dar_ObjIsTravIdPrevious(p, pFanin) || Dar_ObjIsTravIdCurrent(p, pFanin) );
                if ( Dar_ObjIsTravIdCurrent(p, pFanin) )
                {
                    Dar_ObjSetTravIdCurrent( p, pObj );
                    continue;
                }
                pFanin = Dar_ObjFanin1(pObj);
                assert( Dar_ObjIsTravIdPrevious(p, pFanin) || Dar_ObjIsTravIdCurrent(p, pFanin) );
                if ( Dar_ObjIsTravIdCurrent(p, pFanin) )
                {
                    Dar_ObjSetTravIdCurrent( p, pObj );
                    continue;
                }
            }
            // write it back
            Vec_PtrWriteEntry( vNodes, k++, pObj );
        }
        Vec_PtrShrink( vNodes, k );
    } 
    while ( k < i );

//    if ( Vec_PtrSize(vNodes) > 0 )
//        printf( "Found %d unreachable.\n", Vec_PtrSize(vNodes) ); 
    return vNodes;

/*
    // the resulting array contains all unreachable nodes except const 1
    if ( Vec_PtrSize(vNodes) == 0 )
    {
        Vec_PtrFree( vNodes );
        return 0;
    }
    RetValue = Vec_PtrSize(vNodes);

    // mark these nodes
    Dar_ManIncrementTravId( p ); 
    Vec_PtrForEachEntry( vNodes, pObj, i )
        Dar_ObjSetTravIdCurrent( p, pObj );
    Vec_PtrFree( vNodes );
    return RetValue;
*/
}


/**Function*************************************************************

  Synopsis    [Removes nodes that do not fanout into POs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_ManRemoveUnmarked( Dar_Man_t * p )
{
    Vec_Ptr_t * vNodes;
    Dar_Obj_t * pObj;
    int i, RetValue;
    // collect unmarked nodes
    vNodes = Vec_PtrAlloc( 100 );
    Dar_ManForEachObj( p, pObj, i )
    {
        if ( Dar_ObjIsTerm(pObj) )
            continue;
        if ( Dar_ObjIsTravIdCurrent(p, pObj) )
            continue;
//Dar_ObjPrintVerbose( pObj, 0 );
        Dar_ObjDisconnect( p, pObj );
        Vec_PtrPush( vNodes, pObj );
    }
    if ( Vec_PtrSize(vNodes) == 0 )
    {
        Vec_PtrFree( vNodes );
        return 0;
    }
    // remove the dangling objects
    RetValue = Vec_PtrSize(vNodes);
    Vec_PtrForEachEntry( vNodes, pObj, i )
        Dar_ObjDelete( p, pObj );
//    printf( "Removed %d dangling.\n", Vec_PtrSize(vNodes) ); 
    Vec_PtrFree( vNodes );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Rehashes the nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_ManSeqRehashOne( Dar_Man_t * p, Vec_Ptr_t * vNodes, Vec_Ptr_t * vUnreach )
{
    Dar_Obj_t * pObj, * pObjNew, * pFanin0, * pFanin1;
    int i, RetValue = 0, Counter = 0, Counter2 = 0;

    // mark the unreachable nodes
    Dar_ManIncrementTravId( p );
    Vec_PtrForEachEntry( vUnreach, pObj, i )
        Dar_ObjSetTravIdCurrent(p, pObj);
/*
    // count the number of unreachable object connections
    // that is the number of unreachable objects connected to main objects
    Dar_ManForEachObj( p, pObj, i )
    {
        if ( Dar_ObjIsTravIdCurrent(p, pObj) )
            continue;

        pFanin0 = Dar_ObjFanin0(pObj);
        if ( pFanin0 == NULL )
            continue;
        if ( Dar_ObjIsTravIdCurrent(p, pFanin0) )
            pFanin0->fMarkA = 1;

        pFanin1 = Dar_ObjFanin1(pObj);
        if ( pFanin1 == NULL )
            continue;
        if ( Dar_ObjIsTravIdCurrent(p, pFanin1) )
            pFanin1->fMarkA = 1;
    }

    // count the objects
    Dar_ManForEachObj( p, pObj, i )
        Counter2 += pObj->fMarkA, pObj->fMarkA = 0;
    printf( "Connections = %d.\n", Counter2 );
*/

    // go through the nodes while skipping unreachable
    Vec_PtrForEachEntry( vNodes, pObj, i )
    {
        // skip nodes unreachable from the PIs
        if ( Dar_ObjIsTravIdCurrent(p, pObj) )
            continue;
        // process the node
        if ( Dar_ObjIsPo(pObj) )
        {
            if ( !Dar_ObjIsBuf(Dar_ObjFanin0(pObj)) )
                continue;
            pFanin0 = Dar_ObjReal_rec( Dar_ObjChild0(pObj) );
            Dar_ObjPatchFanin0( p, pObj, pFanin0 );
            continue;
        }
        if ( Dar_ObjIsLatch(pObj) )
        {
            if ( !Dar_ObjIsBuf(Dar_ObjFanin0(pObj)) )
                continue;
            pObjNew = Dar_ObjReal_rec( Dar_ObjChild0(pObj) );
            pObjNew = Dar_Latch( p, pObjNew, 0 );
            Dar_ObjReplace( p, pObj, pObjNew, 1 );
            RetValue = 1;
            Counter++;
            continue;
        }
        if ( Dar_ObjIsNode(pObj) )
        {
            if ( !Dar_ObjIsBuf(Dar_ObjFanin0(pObj)) && !Dar_ObjIsBuf(Dar_ObjFanin1(pObj)) )
                continue;
            pFanin0 = Dar_ObjReal_rec( Dar_ObjChild0(pObj) );
            pFanin1 = Dar_ObjReal_rec( Dar_ObjChild1(pObj) );
            pObjNew = Dar_And( p, pFanin0, pFanin1 );
            Dar_ObjReplace( p, pObj, pObjNew, 1 );
            RetValue = 1;
            Counter++;
            continue;
        }
    }
//    printf( "Rehashings = %d.\n", Counter++ );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [If AIG contains buffers, this procedure removes them.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ManRemoveBuffers( Dar_Man_t * p )
{
    Dar_Obj_t * pObj, * pObjNew, * pFanin0, * pFanin1;
    int i;
    if ( Dar_ManBufNum(p) == 0 )
        return;
    Dar_ManForEachObj( p, pObj, i )
    {
        if ( Dar_ObjIsPo(pObj) )
        {
            if ( !Dar_ObjIsBuf(Dar_ObjFanin0(pObj)) )
                continue;
            pFanin0 = Dar_ObjReal_rec( Dar_ObjChild0(pObj) );
            Dar_ObjPatchFanin0( p, pObj, pFanin0 );
        }
        else if ( Dar_ObjIsLatch(pObj) )
        {
            if ( !Dar_ObjIsBuf(Dar_ObjFanin0(pObj)) )
                continue;
            pFanin0 = Dar_ObjReal_rec( Dar_ObjChild0(pObj) );
            pObjNew = Dar_Latch( p, pFanin0, 0 );
            Dar_ObjReplace( p, pObj, pObjNew, 0 );
        }
        else if ( Dar_ObjIsAnd(pObj) )
        {
            if ( !Dar_ObjIsBuf(Dar_ObjFanin0(pObj)) && !Dar_ObjIsBuf(Dar_ObjFanin1(pObj)) )
                continue;
            pFanin0 = Dar_ObjReal_rec( Dar_ObjChild0(pObj) );
            pFanin1 = Dar_ObjReal_rec( Dar_ObjChild1(pObj) );
            pObjNew = Dar_And( p, pFanin0, pFanin1 );
            Dar_ObjReplace( p, pObj, pObjNew, 0 );
        }
    }
    assert( Dar_ManBufNum(p) == 0 );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_ManSeqStrash( Dar_Man_t * p, int nLatches, int * pInits )
{
    Vec_Ptr_t * vNodes, * vUnreach;
//    Dar_Obj_t * pObj, * pFanin;
//    int i;
    int Iter, RetValue = 1;

    // create latches out of the additional PI/PO pairs
    Dar_ManSeqStrashConvert( p, nLatches, pInits );

    // iteratively rehash the network
    for ( Iter = 0; RetValue; Iter++ )
    {
//        Dar_ManPrintStats( p );
/*
        Dar_ManForEachObj( p, pObj, i )
        {
            assert( pObj->Type > 0 );
            pFanin = Dar_ObjFanin0(pObj);
            assert( pFanin == NULL || pFanin->Type > 0 );
            pFanin = Dar_ObjFanin1(pObj);
            assert( pFanin == NULL || pFanin->Type > 0 );
        }
*/
        // mark nodes unreachable from the PIs
        vUnreach = Dar_ManDfsUnreach( p );
        if ( Iter == 0 && Vec_PtrSize(vUnreach) > 0 )
            printf( "Unreachable objects = %d.\n", Vec_PtrSize(vUnreach) );
        // collect nodes reachable from the POs
        vNodes = Dar_ManDfsSeq( p );
        // remove nodes unreachable from the POs
        if ( Iter == 0 )
            Dar_ManRemoveUnmarked( p );
        // continue rehashing as long as there are changes
        RetValue = Dar_ManSeqRehashOne( p, vNodes, vUnreach );
        Vec_PtrFree( vNodes );
        Vec_PtrFree( vUnreach );
    }

    // perform the final cleanup
    Dar_ManIncrementTravId( p );
    vNodes = Dar_ManDfsSeq( p );
    Dar_ManRemoveUnmarked( p );
    Vec_PtrFree( vNodes );
    // remove buffers if they are left
//    Dar_ManRemoveBuffers( p );

    // clean up
    if ( !Dar_ManCheck( p ) )
    {
        printf( "Dar_ManSeqStrash: The network check has failed.\n" );
        return 0;
    }
    return 1;

}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


