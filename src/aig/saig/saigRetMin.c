/**CFile****************************************************************

  FileName    [saigRetMin.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [Min-area retiming for the AIG.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: saigRetMin.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "saig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern Vec_Ptr_t * Nwk_ManDeriveRetimingCut( Aig_Man_t * p, int fForward, int fVerbose );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Marks the TFI cone with the current traversal ID.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManMarkCone_rec( Aig_Man_t * p, Aig_Obj_t * pObj )
{
    if ( pObj == NULL )
        return;
    if ( Aig_ObjIsTravIdCurrent( p, pObj ) )
        return;
    Aig_ObjSetTravIdCurrent( p, pObj );
    Saig_ManMarkCone_rec( p, Aig_ObjFanin0(pObj) );
    Saig_ManMarkCone_rec( p, Aig_ObjFanin1(pObj) );
}

/**Function*************************************************************

  Synopsis    [Marks the TFI cones with the current traversal ID.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManMarkCones( Aig_Man_t * p, Vec_Ptr_t * vNodes )
{
    Aig_Obj_t * pObj;
    int i;
    Aig_ManIncrementTravId( p );
    Vec_PtrForEachEntry( vNodes, pObj, i )
        Saig_ManMarkCone_rec( p, pObj );
}

/**Function*************************************************************

  Synopsis    [Counts the number of nodes to get registers after retiming.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_ManRetimeCountCut( Aig_Man_t * p, Vec_Ptr_t * vCut )
{
    Vec_Ptr_t * vNodes;
    Aig_Obj_t * pObj, * pFanin;
    int i, RetValue;
    Saig_ManMarkCones( p, vCut );
    vNodes = Vec_PtrAlloc( 1000 );
    Aig_ManForEachObj( p, pObj, i )
    {
        if ( Aig_ObjIsTravIdCurrent(p, pObj) )
            continue;
        pFanin = Aig_ObjFanin0( pObj );
        if ( pFanin && !pFanin->fMarkA && Aig_ObjIsTravIdCurrent(p, pFanin) )
        {
            Vec_PtrPush( vNodes, pFanin );
            pFanin->fMarkA = 1;
        }
        pFanin = Aig_ObjFanin1( pObj );
        if ( pFanin && !pFanin->fMarkA && Aig_ObjIsTravIdCurrent(p, pFanin) )
        {
            Vec_PtrPush( vNodes, pFanin );
            pFanin->fMarkA = 1;
        }
    }
    RetValue = Vec_PtrSize( vNodes );
    Vec_PtrForEachEntry( vNodes, pObj, i )
        pObj->fMarkA = 0;
    Vec_PtrFree( vNodes );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG while retiming the registers to the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManRetimeDupForward_rec( Aig_Man_t * pNew, Aig_Obj_t * pObj )
{
    if ( pObj->pData )
        return;
    assert( Aig_ObjIsNode(pObj) );
    Saig_ManRetimeDupForward_rec( pNew, Aig_ObjFanin0(pObj) );
    Saig_ManRetimeDupForward_rec( pNew, Aig_ObjFanin1(pObj) );
    pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG while retiming the registers to the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_ManRetimeDupForward( Aig_Man_t * p, Vec_Ptr_t * vCut )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pObjLi, * pObjLo;
    int i;
    // mark the cones under the cut
//    assert( Vec_PtrSize(vCut) == Saig_ManRetimeCountCut(p, vCut) );
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    pNew->pSpec = Aig_UtilStrsav( p->pSpec );
    pNew->nRegs = Vec_PtrSize(vCut);
    pNew->nTruePis = p->nTruePis;
    pNew->nTruePos = p->nTruePos;
    // create the true PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Saig_ManForEachPi( p, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pNew );
    // create the registers
    Vec_PtrForEachEntry( vCut, pObj, i )
        pObj->pData = Aig_NotCond( Aig_ObjCreatePi(pNew), pObj->fPhase );
    // duplicate the logic above the cut
    Aig_ManForEachPo( p, pObj, i )
        Saig_ManRetimeDupForward_rec( pNew, Aig_ObjFanin0(pObj) );
    // create the true POs
    Saig_ManForEachPo( p, pObj, i )
        Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    // remember value in LI
    Saig_ManForEachLi( p, pObj, i )
        pObj->pData = Aig_ObjChild0Copy(pObj);
    // transfer values from the LIs to the LOs
    Saig_ManForEachLiLo( p, pObjLi, pObjLo, i )
        pObjLo->pData = pObjLi->pData;
    // erase the data values on the internal nodes of the cut
    Vec_PtrForEachEntry( vCut, pObj, i )
        if ( !Aig_ObjIsPi(pObj) )
            pObj->pData = NULL;
    // duplicate the logic below the cut
    Vec_PtrForEachEntry( vCut, pObj, i )
    {
        Saig_ManRetimeDupForward_rec( pNew, pObj );
        Aig_ObjCreatePo( pNew, Aig_NotCond(pObj->pData, pObj->fPhase) );
    }
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG while retiming the registers to the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_ManRetimeDupBackward( Aig_Man_t * p, Vec_Ptr_t * vCut )
{
    Aig_Man_t * pNew;
    pNew = Aig_ManDup( p );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Performs min-area retiming.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_ManRetimeMinArea( Aig_Man_t * p, int fForwardOnly, int fBackwardOnly, int fVerbose )
{
    Vec_Ptr_t * vCut;
    Aig_Man_t * pNew, * pTemp;
    pNew = Aig_ManDup( p );
    // perform several iterations of forward retiming
    if ( !fBackwardOnly )
    while ( 1 )
    {
        vCut = Nwk_ManDeriveRetimingCut( pNew, 1, fVerbose );
        if ( Vec_PtrSize(vCut) >= Aig_ManRegNum(pNew) )
        {
            Vec_PtrFree( vCut );
            break;
        }
        pNew = Saig_ManRetimeDupForward( pTemp = pNew, vCut );
        Aig_ManStop( pTemp );
        Vec_PtrFree( vCut );
    }
    // perform one iteration of backward retiming
    if ( !fForwardOnly )
    {
        vCut = Nwk_ManDeriveRetimingCut( pNew, 0, fVerbose );
        if ( Vec_PtrSize(vCut) < Aig_ManRegNum(pNew) )
        {
            pNew = Saig_ManRetimeDupBackward( pTemp = pNew, vCut );
            Aig_ManStop( pTemp );
        }
        Vec_PtrFree( vCut );
    }
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


