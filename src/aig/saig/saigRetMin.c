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
#include "satSolver.h"
#include "cnf.h"

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
    // mark the cones
    Aig_ManIncrementTravId( p );
    Vec_PtrForEachEntry( vCut, pObj, i )
        Saig_ManMarkCone_rec( p, pObj );
    // collect the new cut
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
    Vec_PtrForEachEntry( vNodes, pObj, i )
        pObj->fMarkA = 0;
    RetValue = Vec_PtrSize( vNodes );
    Vec_PtrFree( vNodes );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Computes the new cut after excluding the nodes in the set.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Saig_ManRetimeExtendCut( Aig_Man_t * p, Vec_Ptr_t * vCut, Vec_Ptr_t * vToExclude )
{
    Vec_Ptr_t * vNodes;
    Aig_Obj_t * pObj, * pFanin;
    int i;
    // mark the cones
    Aig_ManIncrementTravId( p );
    Vec_PtrForEachEntry( vCut, pObj, i )
        Saig_ManMarkCone_rec( p, pObj );
    Vec_PtrForEachEntry( vToExclude, pObj, i )
        Saig_ManMarkCone_rec( p, pObj );
    // collect the new cut
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
    Vec_PtrForEachEntry( vNodes, pObj, i )
        pObj->fMarkA = 0;
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG recursively.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManRetimeDup_rec( Aig_Man_t * pNew, Aig_Obj_t * pObj )
{
    if ( pObj->pData )
        return;
    assert( Aig_ObjIsNode(pObj) );
    Saig_ManRetimeDup_rec( pNew, Aig_ObjFanin0(pObj) );
    Saig_ManRetimeDup_rec( pNew, Aig_ObjFanin1(pObj) );
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
    // duplicate logic above the cut
    Aig_ManForEachPo( p, pObj, i )
        Saig_ManRetimeDup_rec( pNew, Aig_ObjFanin0(pObj) );
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
        if ( Aig_ObjIsNode(pObj) )
            pObj->pData = NULL;
    // duplicate logic below the cut
    Vec_PtrForEachEntry( vCut, pObj, i )
    {
        Saig_ManRetimeDup_rec( pNew, pObj );
        Aig_ObjCreatePo( pNew, Aig_NotCond(pObj->pData, pObj->fPhase) );
    }
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Derives AIG for the initial state computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_ManRetimeDupInitState( Aig_Man_t * p, Vec_Ptr_t * vCut )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i;
    // mark the cones under the cut
//    assert( Vec_PtrSize(vCut) == Saig_ManRetimeCountCut(p, vCut) );
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    // create the true PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    // create the registers
    Vec_PtrForEachEntry( vCut, pObj, i )
        pObj->pData = Aig_ObjCreatePi(pNew);
    // duplicate logic above the cut and create POs
    Saig_ManForEachLi( p, pObj, i )
    {
        Saig_ManRetimeDup_rec( pNew, Aig_ObjFanin0(pObj) );
        Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    }
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Derives the initial state after backward retiming.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Saig_ManRetimeFindInitState( Aig_Man_t * p )
{
    int nConfLimit = 1000000;
    Vec_Int_t * vCiIds, * vInit = NULL;
    Cnf_Dat_t * pCnf;
    sat_solver * pSat;
    Aig_Obj_t * pObj;
    int i, RetValue, * pAssumps, * pModel;
    // solve the SAT problem
    pCnf = Cnf_DeriveSimple( p, Aig_ManPoNum(p) );
    pSat = Cnf_DataWriteIntoSolver( pCnf, 1, 0 );
    pAssumps = ALLOC( int, Aig_ManPoNum(p) );
    Aig_ManForEachPo( p, pObj, i )
        pAssumps[i] = toLitCond( pCnf->pVarNums[pObj->Id], 1 );
    RetValue = sat_solver_solve( pSat, pAssumps, pAssumps+Aig_ManPoNum(p), (sint64)nConfLimit, (sint64)0, (sint64)0, (sint64)0 );
    free( pAssumps );
    if ( RetValue == l_True )
    {
        // accumulate SAT variables of the CIs
        vCiIds = Vec_IntAlloc( Aig_ManPiNum(p) );
        Aig_ManForEachPi( p, pObj, i )
            Vec_IntPush( vCiIds, pCnf->pVarNums[pObj->Id] );
        // create the model
        pModel = Sat_SolverGetModel( pSat, vCiIds->pArray, vCiIds->nSize );
        vInit = Vec_IntAllocArray( pModel, Aig_ManPiNum(p) );
        Vec_IntFree( vCiIds );
    }
    sat_solver_delete( pSat );
    Cnf_DataFree( pCnf );
    return vInit;
}

/**Function*************************************************************

  Synopsis    [Returns the array of bad registers.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Saig_ManGetRegistersToExclude( Aig_Man_t * p )
{
    Vec_Ptr_t * vNodes = NULL;
    Aig_Obj_t * pObj, * pFanin;
    int i, Diffs;
    assert( Saig_ManRegNum(p) > 0 );
    Saig_ManForEachLi( p, pObj, i )
    {
        pFanin = Aig_ObjFanin0(pObj);
        if ( !Aig_ObjFaninC0(pObj) )
            pFanin->fMarkA = 1;
        else
            pFanin->fMarkB = 1;
    }
    Diffs = 0;
    Saig_ManForEachLi( p, pObj, i )
    {
        pFanin = Aig_ObjFanin0(pObj);
        Diffs += pFanin->fMarkA && pFanin->fMarkB;
    }
    if ( Diffs > 0 )
        vNodes = Vec_PtrAlloc( Diffs );
    Saig_ManForEachLi( p, pObj, i )
    {
        pFanin = Aig_ObjFanin0(pObj);
        if ( vNodes && pFanin->fMarkA && pFanin->fMarkB )
            Vec_PtrPush( vNodes, pFanin );
        pFanin->fMarkA = pFanin->fMarkB = 0;
    }
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG while retiming the registers to the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_ManRetimeDupBackward( Aig_Man_t * p, Vec_Ptr_t * vCutInit )
{
    Vec_Ptr_t * vToExclude, * vCut;
    Vec_Int_t * vInit = NULL;
    Aig_Man_t * pNew, * pInit;
    Aig_Obj_t * pObj, * pObjLi, * pObjLo;
    int i;
    // check if there are bad registers
    vToExclude = Saig_ManGetRegistersToExclude( p );
    if ( vToExclude )
    {
        vCut = Saig_ManRetimeExtendCut( p, vCutInit, vToExclude );
        printf( "Bad registers = %d. Extended cut from %d to %d nodes.\n", 
            Vec_PtrSize(vToExclude), Vec_PtrSize(vCutInit), Vec_PtrSize(vCut) );
        Vec_PtrFree( vToExclude );
    }
    else
        vCut = Vec_PtrDup( vCutInit );
    // mark the cones under the cut
//    assert( Vec_PtrSize(vCut) == Saig_ManRetimeCountCut(p, vCut) );
    // count if there are registers to disable
    // derive the initial state
    pInit = Saig_ManRetimeDupInitState( p, vCut );
    vInit = Saig_ManRetimeFindInitState( pInit );
    if ( vInit == NULL )
        printf( "Initial state computation has failed.\n" );
    Aig_ManStop( pInit );
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
        pObj->pData = Aig_NotCond( Aig_ObjCreatePi(pNew), vInit?Vec_IntEntry(vInit,i):0 );
    // duplicate logic above the cut and remember values
    Saig_ManForEachLi( p, pObj, i )
    {
        Saig_ManRetimeDup_rec( pNew, Aig_ObjFanin0(pObj) );
        pObj->pData = Aig_ObjChild0Copy(pObj);
    }
    // transfer values from the LIs to the LOs
    Saig_ManForEachLiLo( p, pObjLi, pObjLo, i )
        pObjLo->pData = pObjLi->pData;
    // erase the data values on the internal nodes of the cut
    Vec_PtrForEachEntry( vCut, pObj, i )
        if ( Aig_ObjIsNode(pObj) )
            pObj->pData = NULL;
    // replicate the data on the primary inputs
    Saig_ManForEachPi( p, pObj, i )
        pObj->pData = Aig_ManPi( pNew, i );
    // duplicate logic below the cut
    Saig_ManForEachPo( p, pObj, i )
    {
        Saig_ManRetimeDup_rec( pNew, Aig_ObjFanin0(pObj) );
        Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    }
    Vec_PtrForEachEntry( vCut, pObj, i )
    {
        Saig_ManRetimeDup_rec( pNew, pObj );
        Aig_ObjCreatePo( pNew, Aig_NotCond(pObj->pData, vInit?Vec_IntEntry(vInit,i):0) );
    }
    if ( vInit )
        Vec_IntFree( vInit );
    Vec_PtrFree( vCut );
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


