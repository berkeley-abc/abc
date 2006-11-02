/**CFile****************************************************************

  FileName    [retArea.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Retiming package.]

  Synopsis    [Min-area retiming.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - Oct 31, 2006.]

  Revision    [$Id: retArea.c,v 1.00 2006/10/31 00:00:00 alanmi Exp $]

***********************************************************************/

#include "retInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int         Abc_NtkRetimeMinAreaFwd( Abc_Ntk_t * pNtk, int fVerbose );
static Abc_Ntk_t * Abc_NtkRetimeMinAreaBwd( Abc_Ntk_t * pNtk, int fVerbose );
static void        Abc_NtkRetimeMinAreaPrepare( Abc_Ntk_t * pNtk, int fForward );
static Vec_Ptr_t * Abc_NtkRetimeMinAreaAddBuffers( Abc_Ntk_t * pNtk );
static void        Abc_NtkRetimeMinAreaRemoveBuffers( Abc_Ntk_t * pNtk, Vec_Ptr_t * vBuffers );
static void        Abc_NtkRetimeMinAreaInitValue( Abc_Ntk_t * pNtk, Vec_Ptr_t * vMinCut );
static Abc_Ntk_t * Abc_NtkRetimeMinAreaConstructNtk( Abc_Ntk_t * pNtk, Vec_Ptr_t * vMinCut );
static void        Abc_NtkRetimeMinAreaUpdateLatches( Abc_Ntk_t * pNtk, Vec_Ptr_t * vMinCut, int fForward );

extern Abc_Ntk_t * Abc_NtkAttachBottom( Abc_Ntk_t * pNtkTop, Abc_Ntk_t * pNtkBottom );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs min-area retiming.]

  Description [Returns the number of latches reduced.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRetimeMinArea( Abc_Ntk_t * pNtk, int fVerbose )
{
    Abc_Ntk_t * pNtkTotal = NULL, * pNtkBottom, * pNtkMiter;
    Vec_Int_t * vValues;
    int nLatches = Abc_NtkLatchNum(pNtk);
    // there should not be black boxes
    assert( Abc_NtkIsSopLogic(pNtk) );
    assert( Abc_NtkLatchNum(pNtk) == Vec_PtrSize(pNtk->vBoxes) );
    // reorder CI/CO/latch inputs
    Abc_NtkOrderCisCos( pNtk );
    // perform forward retiming
    vValues = Abc_NtkCollectLatchValues( pNtk );
//    Abc_NtkRetimeMinAreaFwd( pNtk, fVerbose );
    pNtkTotal = Abc_NtkRetimeMinAreaBwd( pNtk, fVerbose );

//    while ( Abc_NtkRetimeMinAreaFwd( pNtk, fVerbose ) );
    // perform backward retiming
//    while ( pNtkBottom = Abc_NtkRetimeMinAreaBwd( pNtk, fVerbose ) )
//        pNtkTotal = Abc_NtkAttachBottom( pNtkTotal, pNtkBottom );  
    // compute initial values
    if ( pNtkTotal )
    {
        // convert the target network to AIG
        Abc_NtkLogicToAig( pNtkTotal );
        // get the miter
        pNtkMiter = Abc_NtkCreateTarget( pNtkTotal, pNtkTotal->vCos, vValues );
        Abc_NtkDelete( pNtkTotal );
        // get the initial values
        Abc_NtkRetimeInitialValues( pNtk, pNtkMiter, fVerbose );
        Abc_NtkDelete( pNtkMiter );
    }
    Vec_IntFree( vValues );
    // fix the COs
    Abc_NtkLogicMakeSimpleCos( pNtk, 0 );
    // check for correctness
    if ( !Abc_NtkCheck( pNtk ) )
        fprintf( stdout, "Abc_NtkRetimeMinArea(): Network check has failed.\n" );
    // return the number of latches saved
    return nLatches - Abc_NtkLatchNum(pNtk);
}

/**Function*************************************************************

  Synopsis    [Performs min-area retiming forward.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRetimeMinAreaFwd( Abc_Ntk_t * pNtk, int fVerbose )
{
    Vec_Ptr_t * vBuffers, * vMinCut;
    int nLatches = Abc_NtkLatchNum(pNtk);
    // mark current latches and TFO(PIs)
    Abc_NtkRetimeMinAreaPrepare( pNtk, 1 );
    // add buffers on edges feeding into the marked nodes
    vBuffers = Abc_NtkRetimeMinAreaAddBuffers( pNtk );
    // run the maximum forward flow
    vMinCut = Abc_NtkMaxFlow( pNtk, 1, fVerbose );
    assert( Vec_PtrSize(vMinCut) <= Abc_NtkLatchNum(pNtk) );
    // create new latch boundary if there is improvement
    if ( Vec_PtrSize(vMinCut) < Abc_NtkLatchNum(pNtk) )
    {
        Abc_NtkRetimeMinAreaInitValue( pNtk, vMinCut );
        Abc_NtkRetimeMinAreaUpdateLatches( pNtk, vMinCut, 1 );
    }
    // clean up
    Abc_NtkRetimeMinAreaRemoveBuffers( pNtk, vBuffers );
    Vec_PtrFree( vMinCut );
    Abc_NtkCleanMarkA( pNtk );
    return nLatches - Abc_NtkLatchNum(pNtk);
}

/**Function*************************************************************

  Synopsis    [Performs min-area retiming backward.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkRetimeMinAreaBwd( Abc_Ntk_t * pNtk, int fVerbose )
{
    Abc_Ntk_t * pNtkNew = NULL;
    Vec_Ptr_t * vMinCut;
    int nLatches = Abc_NtkLatchNum(pNtk);
    // mark current latches and TFI(POs)
    Abc_NtkRetimeMinAreaPrepare( pNtk, 0 );
    // run the maximum forward flow
    vMinCut = Abc_NtkMaxFlow( pNtk, 0, fVerbose );
    assert( Vec_PtrSize(vMinCut) <= Abc_NtkLatchNum(pNtk) );
    // create new latch boundary if there is improvement
    if ( Vec_PtrSize(vMinCut) < Abc_NtkLatchNum(pNtk) )
    {
        pNtkNew = Abc_NtkRetimeMinAreaConstructNtk( pNtk, vMinCut );
        Abc_NtkRetimeMinAreaUpdateLatches( pNtk, vMinCut, 0 );
    }
    // clean up
    Vec_PtrFree( vMinCut );
    Abc_NtkCleanMarkA( pNtk );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Marks the cone with MarkA.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkMarkCone_rec( Abc_Obj_t * pObj, int fForward )
{
    Abc_Obj_t * pNext;
    int i;
    if ( pObj->fMarkA )
        return;
    pObj->fMarkA = 1;
    if ( fForward )
    {
        Abc_ObjForEachFanout( pObj, pNext, i )
            Abc_NtkMarkCone_rec( pNext, fForward );
    }
    else
    {
        Abc_ObjForEachFanin( pObj, pNext, i )
            Abc_NtkMarkCone_rec( pNext, fForward );
    }
}

/**Function*************************************************************

  Synopsis    [Prepares the network for running MaxFlow.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRetimeMinAreaPrepare( Abc_Ntk_t * pNtk, int fForward )
{
    Abc_Obj_t * pObj;
    int i;
    if ( fForward )
    {
        // mark the frontier
        Abc_NtkForEachPo( pNtk, pObj, i )
            pObj->fMarkA = 1;
        Abc_NtkForEachLatch( pNtk, pObj, i )
        {
            pObj->fMarkA = 1;
            Abc_ObjFanin0(pObj)->fMarkA = 1;
        }
        // mark the nodes reachable from the POs
        Abc_NtkForEachPi( pNtk, pObj, i )
            Abc_NtkMarkCone_rec( pObj, fForward );
    }
    else
    {
        // mark the frontier
        Abc_NtkForEachPi( pNtk, pObj, i )
            pObj->fMarkA = 1;
        Abc_NtkForEachLatch( pNtk, pObj, i )
        {
            pObj->fMarkA = 1;
            Abc_ObjFanout0(pObj)->fMarkA = 1;
        }
        // mark the nodes reachable from the POs
        Abc_NtkForEachPo( pNtk, pObj, i )
            Abc_NtkMarkCone_rec( pObj, fForward );
    }
}

/**Function*************************************************************

  Synopsis    [Add extra buffers.]

  Description [This is needed to make sure that forward retiming 
  works correctly. This has to do with the nodes in the TFO cone
  of the PIs having multiple incoming edges.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkRetimeMinAreaAddBuffers( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vFeeds, * vFanouts;
    Abc_Obj_t * pObj, * pFanin, * pFanout, * pBuffer;
    int i, k;
    // collect all nodes that are feeding into the marked nodes
    Abc_NtkIncrementTravId(pNtk);
    vFeeds = Vec_PtrAlloc( 100 );
    Abc_NtkForEachObj( pNtk, pObj, i )
    {
        if ( !pObj->fMarkA )
            continue;
        Abc_ObjForEachFanin( pObj, pFanin, k )
            if ( !pFanin->fMarkA && !Abc_NodeIsTravIdCurrent(pFanin) )
            {
                Abc_NodeSetTravIdCurrent( pFanin );
                Vec_PtrPush( vFeeds, pFanin );
            }
    }
    // add buffers for each such node
    vFanouts = Vec_PtrAlloc( 100 );
    Vec_PtrForEachEntry( vFeeds, pObj, i )
    {
        // create and remember the buffers
        pBuffer = Abc_NtkCreateNodeBuf( pNtk, pObj );
        Vec_PtrWriteEntry( vFeeds, i, pBuffer );
        // patch the fanin of each marked fanout to point to the buffer
        Abc_NodeCollectFanouts( pObj, vFanouts );
        Vec_PtrForEachEntry( vFanouts, pFanout, k )
            if ( pFanout->fMarkA )
                Abc_ObjPatchFanin( pFanout, pObj, pBuffer );
    }
    Vec_PtrFree( vFanouts );
    // mark the new buffers
    Vec_PtrForEachEntry( vFeeds, pObj, i )
        pObj->fMarkA = 1;
    return vFeeds;
}

/**Function*************************************************************

  Synopsis    [Removes extra buffers.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRetimeMinAreaRemoveBuffers( Abc_Ntk_t * pNtk, Vec_Ptr_t * vBuffers )
{
    Abc_Obj_t * pObj;
    int i;
    Vec_PtrForEachEntry( vBuffers, pObj, i )
    {
        Abc_ObjTransferFanout( pObj, Abc_ObjFanin0(pObj) );
        Abc_NtkDeleteObj( pObj );
    }
    Vec_PtrFree( vBuffers );
}

/**Function*************************************************************

  Synopsis    [Computes the results of simulating one node.]

  Description [Assumes that fanins have pCopy set to the input values.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_ObjSopSimulate( Abc_Obj_t * pObj )
{
    char * pCube, * pSop = pObj->pData;
    int nVars, Value, v, ResOr, ResAnd, ResVar;
    assert( pSop && !Abc_SopIsExorType(pSop) );
    // simulate the SOP of the node
    ResOr = 0;
    nVars = Abc_SopGetVarNum(pSop);
    Abc_SopForEachCube( pSop, nVars, pCube )
    {
        ResAnd = 1;
        Abc_CubeForEachVar( pCube, Value, v )
        {
            if ( Value == '0' )
                ResVar = 1 ^ ((int)Abc_ObjFanin(pObj, v)->pCopy);
            else if ( Value == '1' )
                ResVar = (int)Abc_ObjFanin(pObj, v)->pCopy;
            else
                continue;
            ResAnd &= ResVar;
        }
        ResOr |= ResAnd;
    }
    // complement the result if necessary
    if ( !Abc_SopGetPhase(pSop) )
        ResOr ^= 1;
    return ResOr;
}

/**Function*************************************************************

  Synopsis    [Compute initial values.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRetimeMinAreaInitValue_rec( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanin;
    int i;
    // skip visited nodes
    if ( Abc_NodeIsTravIdCurrent(pObj) )
        return (int)pObj->pCopy;
    Abc_NodeSetTravIdCurrent(pObj);
    // consider the case of a latch output
    if ( Abc_ObjIsBi(pObj) )
    {
        assert( Abc_ObjIsLatch(Abc_ObjFanin0(pObj)) );
        pObj->pCopy = (void *)Abc_NtkRetimeMinAreaInitValue_rec( Abc_ObjFanin0(pObj) );
        return (int)pObj->pCopy;
    }
    assert( Abc_ObjIsNode(pObj) );
    // visit the fanins
    Abc_ObjForEachFanin( pObj, pFanin, i )
        Abc_NtkRetimeMinAreaInitValue_rec( pFanin );
    // compute the value of the node
    pObj->pCopy = (void *)Abc_ObjSopSimulate(pObj);
    return (int)pObj->pCopy;
}

/**Function*************************************************************

  Synopsis    [Compute initial values.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRetimeMinAreaInitValue( Abc_Ntk_t * pNtk, Vec_Ptr_t * vMinCut )
{
    Abc_Obj_t * pObj;
    int i;
    // transfer initial values to pCopy and mark the latches
    Abc_NtkIncrementTravId(pNtk);
    Abc_NtkForEachLatch( pNtk, pObj, i )
    {
        pObj->pCopy = (void *)Abc_LatchIsInit1(pObj);
        Abc_NodeSetTravIdCurrent( pObj );
    }
    // propagate initial values
    Vec_PtrForEachEntry( vMinCut, pObj, i )
        Abc_NtkRetimeMinAreaInitValue_rec( pObj );
}

/**Function*************************************************************

  Synopsis    [Performs min-area retiming backward.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkRetimeMinAreaConstructNtk_rec( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanin;
    int i;
    // skip visited nodes
    if ( Abc_NodeIsTravIdCurrent(pObj) )
        return pObj->pCopy;
    Abc_NodeSetTravIdCurrent(pObj);
    // consider the case of a latch output
    if ( Abc_ObjIsBo(pObj) )
        return Abc_NtkRetimeMinAreaConstructNtk_rec( pNtkNew, Abc_ObjFanin0(pObj) );
    assert( Abc_ObjIsNode(pObj) );
    // visit the fanins
    Abc_ObjForEachFanin( pObj, pFanin, i )
        Abc_NtkRetimeMinAreaConstructNtk_rec( pNtkNew, pFanin );
    // compute the value of the node
    Abc_NtkDupObj( pNtkNew, pObj, 0 );
    Abc_ObjForEachFanin( pObj, pFanin, i )
        Abc_ObjAddFanin( pObj->pCopy, pFanin->pCopy );
    return pObj->pCopy;
}

/**Function*************************************************************

  Synopsis    [Creates the network from computing initial state.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkRetimeMinAreaConstructNtk( Abc_Ntk_t * pNtk, Vec_Ptr_t * vMinCut )
{
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pObj, * pObjNew;
    int i;
    // create new network
    pNtkNew = Abc_NtkAlloc( ABC_NTK_LOGIC, ABC_FUNC_SOP, 1 );
    // set mapping of new latches into the PIs of the network
    Abc_NtkIncrementTravId(pNtk);
    Vec_PtrForEachEntry( vMinCut, pObj, i )
    {
        pObj->pCopy = Abc_NtkCreatePi(pNtkNew);
        Abc_NodeSetTravIdCurrent( pObj );
    }
    // construct the network recursively
    Abc_NtkForEachLatch( pNtk, pObj, i )
    {
        pObjNew = Abc_NtkRetimeMinAreaConstructNtk_rec( pNtkNew, Abc_ObjFanin0(pObj) );
        Abc_ObjAddFanin( Abc_NtkCreatePo(pNtkNew), pObjNew );
    }
    // assign dummy node names
    Abc_NtkAddDummyPiNames( pNtkNew );
    Abc_NtkAddDummyPoNames( pNtkNew );
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkRetimeMinAreaConstructNtk(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Updates the network after backward retiming.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRetimeMinAreaUpdateLatches( Abc_Ntk_t * pNtk, Vec_Ptr_t * vMinCut, int fForward )
{
    Vec_Ptr_t * vCis, * vCos, * vBoxes, * vBoxesNew, * vFanouts;
    Abc_Obj_t * pObj, * pLatch, * pLatchIn, * pLatchOut, * pFanout;
    int i, k;
    // create new latches
    Vec_PtrShrink( pNtk->vCis, Abc_NtkCiNum(pNtk) - Abc_NtkLatchNum(pNtk) );
    Vec_PtrShrink( pNtk->vCos, Abc_NtkCoNum(pNtk) - Abc_NtkLatchNum(pNtk) );
    vCis   = pNtk->vCis;   pNtk->vCis   = NULL;  
    vCos   = pNtk->vCos;   pNtk->vCos   = NULL;  
    vBoxes = pNtk->vBoxes; pNtk->vBoxes = NULL; 
    // transfer boxes
    vBoxesNew = Vec_PtrAlloc(100);
    Vec_PtrForEachEntry( vBoxes, pObj, i )
        if ( !Abc_ObjIsLatch(pObj) )
            Vec_PtrPush( vBoxesNew, pObj );
    // create or reuse latches
    Abc_NtkIncrementTravId(pNtk);
    vFanouts = Vec_PtrAlloc( 100 );
    Vec_PtrForEachEntry( vMinCut, pObj, i )
    {
        if ( Abc_ObjIsCi(pObj) && fForward )
        {
            pLatchOut = pObj;
            pLatch    = Abc_ObjFanin0(pLatchOut);
            pLatchIn  = Abc_ObjFanin0(pLatch);
            assert( Abc_ObjIsBi(pLatchOut) && Abc_ObjIsLatch(pLatch) && Abc_ObjIsBo(pLatchIn) );
            // mark the latch as reused
            Abc_NodeSetTravIdCurrent( pLatch );
        }
        else if ( Abc_ObjIsCo(pObj) && !fForward )
        {
            pLatchIn  = pObj;
            pLatch    = Abc_ObjFanout0(pLatchIn);
            pLatchOut = Abc_ObjFanout0(pLatch);
            assert( Abc_ObjIsBi(pLatchOut) && Abc_ObjIsLatch(pLatch) && Abc_ObjIsBo(pLatchIn) );
            // mark the latch as reused
            Abc_NodeSetTravIdCurrent( pLatch );
        }
        else
        {
            pLatchOut = Abc_NtkCreateBi(pNtk);
            pLatch    = Abc_NtkCreateLatch(pNtk);
            pLatchIn  = Abc_NtkCreateBo(pNtk);
            Abc_ObjAssignName( pLatchOut, Abc_ObjName(pLatchOut), NULL );
            Abc_ObjAssignName( pLatchIn,  Abc_ObjName(pLatchIn), NULL );
            // connect
            Abc_ObjAddFanin( pLatchOut, pLatch );
            Abc_ObjAddFanin( pLatch, pLatchIn );
            if ( fForward )
            {
                Abc_ObjTransferFanout( pObj, pLatchOut );
                pLatch->pData = (void *)(pObj->pCopy? ABC_INIT_ONE : ABC_INIT_ZERO);
            }
            else
            {
                // redirect unmarked edges
                Abc_NodeCollectFanouts( pObj, vFanouts );
                Vec_PtrForEachEntry( vFanouts, pFanout, k )
                    if ( !pFanout->fMarkA )
                        Abc_ObjPatchFanin( pFanout, pObj, pLatchOut );
            }
            // connect latch to the node
            Abc_ObjAddFanin( pLatchIn, pObj );
        }
        Vec_PtrPush( vCis, pLatchOut );
        Vec_PtrPush( vBoxesNew, pLatch );
        Vec_PtrPush( vCos, pLatchIn );
    }
    Vec_PtrFree( vFanouts );
    // remove useless latches
    Vec_PtrForEachEntry( vBoxes, pObj, i )
    {
        if ( !Abc_ObjIsLatch(pObj) )
            continue;
        if ( Abc_NodeIsTravIdCurrent(pObj) )
            continue;
        pLatchOut = Abc_ObjFanout0(pObj);
        pLatch    = pObj;
        pLatchIn  = Abc_ObjFanin0(pObj);
        Abc_ObjTransferFanout( pLatchOut, Abc_ObjFanin0(pLatchIn) );
        Abc_NtkDeleteObj( pLatchOut );
        Abc_NtkDeleteObj( pObj );
        Abc_NtkDeleteObj( pLatchIn );
    }
    // set the arrays
    pNtk->vCis = vCis;
    pNtk->vCos = vCos;
    pNtk->vBoxes = vBoxesNew;
    Vec_PtrFree( vBoxes );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


