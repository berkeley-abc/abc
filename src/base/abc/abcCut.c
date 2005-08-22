/**CFile****************************************************************

  FileName    [abcCut.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Interface to cut computation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcCut.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "cut.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
 
static Vec_Int_t * Abc_NtkFanoutCounts( Abc_Ntk_t * pNtk );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computes the cuts for the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cut_Man_t * Abc_NtkCuts( Abc_Ntk_t * pNtk, Cut_Params_t * pParams )
{
    Cut_Man_t *  p;
    Abc_Obj_t * pObj, * pDriver, * pNode;
    Vec_Ptr_t * vNodes;
    Vec_Int_t * vChoices;
    int i;
    int clk = clock();

    assert( Abc_NtkIsAig(pNtk) );

    // start the manager
    pParams->nIdsMax = Abc_NtkObjNumMax( pNtk );
    p = Cut_ManStart( pParams );
    if ( pParams->fDrop )
        Cut_ManSetFanoutCounts( p, Abc_NtkFanoutCounts(pNtk) );
    // set cuts for PIs
    Abc_NtkForEachCi( pNtk, pObj, i )
        if ( Abc_ObjFanoutNum(pObj) > 0 )
            Cut_NodeSetTriv( p, pObj->Id );
    // compute cuts for internal nodes
    vNodes = Abc_AigDfs( pNtk, 0, 1 );
    vChoices = Vec_IntAlloc( 100 );
    Vec_PtrForEachEntry( vNodes, pObj, i )
    {
        // when we reached a CO, it is time to deallocate the cuts
        if ( Abc_ObjIsCo(pObj) )
        {
            if ( pParams->fDrop )
                Cut_NodeTryDroppingCuts( p, Abc_ObjFaninId0(pObj) );
            continue;
        }
        // skip constant node, it has no cuts
        if ( Abc_NodeIsConst(pObj) )
            continue;
        // compute the cuts to the internal node
        Cut_NodeComputeCuts( p, pObj->Id, Abc_ObjFaninId0(pObj), Abc_ObjFaninId1(pObj),  
            Abc_ObjFaninC0(pObj), Abc_ObjFaninC1(pObj) );  
        // add cuts due to choices
        if ( Abc_NodeIsAigChoice(pObj) )
        {
            Vec_IntClear( vChoices );
            for ( pNode = pObj; pNode; pNode = pNode->pData )
                Vec_IntPush( vChoices, pNode->Id );
            Cut_NodeUnionCuts( p, vChoices );
        }
    }
    if ( !pParams->fSeq )
    {
        Vec_PtrFree( vNodes );
        Vec_IntFree( vChoices );
PRT( "Total", clock() - clk );
        return p;
    }
    assert( 0 );

    // compute sequential cuts
    Abc_NtkIncrementTravId( pNtk );
    Abc_NtkForEachLatch( pNtk, pObj, i )
    {
        pDriver = Abc_ObjFanin0(pObj);
        if ( !Abc_ObjIsNode(pDriver) )
            continue;
        if ( Abc_NodeIsTravIdCurrent(pDriver) )
            continue;
        Abc_NodeSetTravIdCurrent(pDriver);
        Cut_NodeSetComputedAsNew( p, pDriver->Id );
    }
    // compute as long as new cuts appear


    return p;
}

/**Function*************************************************************

  Synopsis    [Creates the array of fanout counters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_NtkFanoutCounts( Abc_Ntk_t * pNtk )
{
    Vec_Int_t * vFanNums;
    Abc_Obj_t * pObj;//, * pFanout;
    int i;//, k, nFanouts;
    vFanNums = Vec_IntAlloc( 0 );
    Vec_IntFill( vFanNums, Abc_NtkObjNumMax(pNtk), -1 );
    Abc_NtkForEachObj( pNtk, pObj, i )
        if ( Abc_ObjIsCi(pObj) || Abc_ObjIsNode(pObj) )
        {
            Vec_IntWriteEntry( vFanNums, i, Abc_ObjFanoutNum(pObj) );
/*
            // get the number of non-CO fanouts
            nFanouts = 0;
            Abc_ObjForEachFanout( pObj, pFanout, k )
                if ( !Abc_ObjIsCo(pFanout) )
                    nFanouts++;
            Vec_IntWriteEntry( vFanNums, i, nFanouts );
*/
        }
    return vFanNums;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


