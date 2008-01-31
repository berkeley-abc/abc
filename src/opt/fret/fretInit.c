/**CFile****************************************************************

  FileName    [fretInit.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Flow-based retiming package.]

  Synopsis    [Initialization for retiming package.]

  Author      [Aaron Hurst]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - January 1, 2008.]

  Revision    [$Id: fretInit.c,v 1.00 2008/01/01 00:00:00 ahurst Exp $]

***********************************************************************/

#include "abc.h"
#include "vec.h"
#include "io.h"
#include "fretime.h"
#include "mio.h"

////////////////////////////////////////////////////////////////////////
///                     FUNCTION PROTOTYPES                          ///
////////////////////////////////////////////////////////////////////////

static void Abc_FlowRetime_UpdateForwardInit_rec( Abc_Obj_t * pObj );
static void Abc_FlowRetime_VerifyBackwardInit( Abc_Ntk_t * pNtk );
static void Abc_FlowRetime_VerifyBackwardInit_rec( Abc_Obj_t * pObj );
static Abc_Obj_t* Abc_FlowRetime_UpdateBackwardInit_rec( Abc_Obj_t *pOrigObj, 
                                                         Abc_Obj_t *pUseThisPi, Vec_Ptr_t *vOtherPis, 
                                                         int recurse);
static void Abc_FlowRetime_SimulateNode( Abc_Obj_t * pObj );
static void Abc_FlowRetime_SimulateSop( Abc_Obj_t * pObj, char *pSop );

extern void * Abc_FrameReadLibGen();                    
extern Abc_Ntk_t * Abc_NtkRestrash( Abc_Ntk_t * pNtk, bool fCleanup );


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Updates initial state information.]

  Description [Assumes latch boxes in original position, latches in
               new positions.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void
Abc_FlowRetime_InitState( Abc_Ntk_t * pNtk ) {

  if (!pManMR->fComputeInitState) return;

  if (pManMR->fIsForward)
    Abc_FlowRetime_UpdateForwardInit( pNtk );
  else {
    Abc_FlowRetime_UpdateBackwardInit( pNtk );
  }
}


/**Function*************************************************************

  Synopsis    [Prints initial state information.]

  Description [Prints distribution of 0,1,and X initial states.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void
Abc_FlowRetime_PrintInitStateInfo( Abc_Ntk_t * pNtk ) {
  int i, n0=0, n1=0, nDC=0, nOther=0;
  Abc_Obj_t *pLatch;

  Abc_NtkForEachLatch( pNtk, pLatch, i ) {
    if (Abc_LatchIsInit0(pLatch)) n0++;
    else if (Abc_LatchIsInit1(pLatch)) n1++;
    else if (Abc_LatchIsInitDc(pLatch)) nDC++;
    else nOther++;
  }     

  printf("\tinitial states {0,1,x} = {%d, %d, %d}", n0, n1, nDC);
  if (nOther)
    printf(" + %d UNKNOWN", nOther);
  printf("\n");
}


/**Function*************************************************************

  Synopsis    [Computes initial state after forward retiming.]

  Description [Assumes box outputs in old positions stored w/ init values.
               Uses three-value simulation to preserve don't cares.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FlowRetime_UpdateForwardInit( Abc_Ntk_t * pNtk ) {
  Abc_Obj_t *pObj, *pFanin;
  int i;

  vprintf("\t\tupdating init state\n");

  Abc_NtkIncrementTravId( pNtk );

  Abc_NtkForEachLatch( pNtk, pObj, i ) {
    pFanin = Abc_ObjFanin0(pObj);
    Abc_FlowRetime_UpdateForwardInit_rec( pFanin );

    if (FTEST(pFanin, INIT_0))
      Abc_LatchSetInit0( pObj );
    else if (FTEST(pFanin, INIT_1))
      Abc_LatchSetInit1( pObj );
    else
      Abc_LatchSetInitDc( pObj );
  }
}

void Abc_FlowRetime_UpdateForwardInit_rec( Abc_Obj_t * pObj ) {
  Abc_Obj_t *pNext;
  int i;

  assert(!Abc_ObjIsPi(pObj)); // should never reach the inputs

  if (Abc_ObjIsBo(pObj)) return;

  // visited?
  if (Abc_NodeIsTravIdCurrent(pObj)) return;
  Abc_NodeSetTravIdCurrent(pObj);

  Abc_ObjForEachFanin( pObj, pNext, i ) {
    Abc_FlowRetime_UpdateForwardInit_rec( pNext );
  }
  
  Abc_FlowRetime_SimulateNode( pObj );
}


/**Function*************************************************************

  Synopsis    [Sets initial value flags.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_FlowRetime_SetInitValue( Abc_Obj_t * pObj,
                                                int val, int dc ) {
  
  // store init value
  FUNSET(pObj, INIT_CARE);
  if (!dc){
    if (val) {
      FSET(pObj, INIT_1);
    } else {
      FSET(pObj, INIT_0);
    }
  }
}


/**Function*************************************************************

  Synopsis    [Propogates initial state through a logic node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FlowRetime_SimulateNode( Abc_Obj_t * pObj ) {
  Abc_Ntk_t *pNtk = Abc_ObjNtk(pObj);
  Abc_Obj_t * pFanin;
  int i, rAnd, rVar, dcAnd, dcVar;
  DdManager * dd = pNtk->pManFunc;
  DdNode *pBdd = pObj->pData, *pVar;
  
  assert(!Abc_ObjIsLatch(pObj));

  // (i) constant nodes
  if (Abc_NtkHasAig(pNtk) && Abc_AigNodeIsConst(pObj)) {
    Abc_FlowRetime_SetInitValue(pObj, 1, 0);
    return;
  }
  if (!Abc_NtkIsStrash( pNtk ) && Abc_ObjIsNode(pObj)) {
    if (Abc_NodeIsConst0(pObj)) {
      Abc_FlowRetime_SetInitValue(pObj, 0, 0);
      return;
    } else if (Abc_NodeIsConst1(pObj)) {
      Abc_FlowRetime_SetInitValue(pObj, 1, 0);
      return;
    }
  }
  
  // (ii) terminal nodes
  if (!Abc_ObjIsNode(pObj)) {
    pFanin = Abc_ObjFanin0(pObj);
    
    Abc_FlowRetime_SetInitValue(pObj, 
         (FTEST(pFanin, INIT_1) ? 1 : 0) ^ pObj->fCompl0, 
         !FTEST(pFanin, INIT_CARE));    
    return;
  }

  // (iii) logic nodes

  // ------ SOP network
  if ( Abc_NtkHasSop( pNtk )) {
    Abc_FlowRetime_SimulateSop( pObj, (char *)Abc_ObjData(pObj) );
    return;
  }

  // ------ BDD network
  else if ( Abc_NtkHasBdd( pNtk )) {
    assert(dd);
    assert(pBdd);

    // cofactor for 0,1 inputs
    // do nothing for X values
    Abc_ObjForEachFanin(pObj, pFanin, i) {
      pVar = Cudd_bddIthVar( dd, i );
      if (FTEST(pFanin, INIT_CARE)) {
        if (FTEST(pFanin, INIT_0))
          pBdd = Cudd_Cofactor( dd, pBdd, Cudd_Not(pVar) ); 
        else
          pBdd = Cudd_Cofactor( dd, pBdd, pVar ); 
      }
    }

    // if function has not been reduced to 
    // a constant, propagate an X
    rVar = (pBdd == Cudd_ReadOne(dd));
    dcVar = !Cudd_IsConstant(pBdd);
    
    Abc_FlowRetime_SetInitValue(pObj, rVar, dcVar);
    return;
  }

  // ------ AIG network
  else if ( Abc_NtkHasAig( pNtk )) {

    assert(Abc_AigNodeIsAnd(pObj));
    dcAnd = 0, rAnd = 1;
    
    pFanin = Abc_ObjFanin0(pObj);
    dcAnd |= FTEST(pFanin, INIT_CARE) ? 0 : 1;
    rVar = FTEST(pFanin, INIT_0) ? 0 : 1;
    if (pObj->fCompl0) rVar ^= 1; // complimented?
    rAnd &= rVar;
    
    pFanin = Abc_ObjFanin1(pObj);
    dcAnd |= FTEST(pFanin, INIT_CARE) ? 0 : 1;
    rVar = FTEST(pFanin, INIT_0) ? 0 : 1;
    if (pObj->fCompl1) rVar ^= 1; // complimented?
    rAnd &= rVar;
    
    if (!rAnd) dcAnd = 0; /* controlling value */
    
    Abc_FlowRetime_SetInitValue(pObj, rAnd, dcAnd);
    return;
  }

  // ------ MAPPED network
  else if ( Abc_NtkHasMapping( pNtk )) {
    Abc_FlowRetime_SimulateSop( pObj, (char *)Mio_GateReadSop(pObj->pData) );
    return;
  }

  assert(0);
}


/**Function*************************************************************

  Synopsis    [Propogates initial state through a SOP node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FlowRetime_SimulateSop( Abc_Obj_t * pObj, char *pSop ) {
  Abc_Obj_t * pFanin;
  char *pCube;
  int i, j, rAnd, rOr, rVar, dcAnd, dcOr, v;

  assert( pSop && !Abc_SopIsExorType(pSop) );
      
  rOr = 0, dcOr = 0;

  i = Abc_SopGetVarNum(pSop);
  Abc_SopForEachCube( pSop, i, pCube ) {
    rAnd = 1, dcAnd = 0;
    Abc_CubeForEachVar( pCube, v, j ) {
      pFanin = Abc_ObjFanin(pObj, j);
      if ( v == '0' )
        rVar = FTEST(pFanin, INIT_0) ? 1 : 0;
      else if ( v == '1' )
        rVar = FTEST(pFanin, INIT_1) ? 1 : 0;
      else
        continue;
      
      if (FTEST(pFanin, INIT_CARE))
        rAnd &= rVar;
      else
        dcAnd = 1;
    }
    if (!rAnd) dcAnd = 0; /* controlling value */
    if (dcAnd) 
      dcOr = 1;
    else
      rOr |= rAnd;
  }
  if (rOr) dcOr = 0; /* controlling value */
  
  // complement the result if necessary
  if ( !Abc_SopGetPhase(pSop) )
    rOr ^= 1;
      
  Abc_FlowRetime_SetInitValue(pObj, rOr, dcOr);
}

/**Function*************************************************************

  Synopsis    [Sets up backward initial state computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FlowRetime_SetupBackwardInit( Abc_Ntk_t * pNtk ) {
  Abc_Obj_t *pLatch, *pObj, *pPi;
  int i;
  Vec_Ptr_t *vObj = Vec_PtrAlloc(100);

  // create the network used for the initial state computation
  if (Abc_NtkHasMapping(pNtk))
    pManMR->pInitNtk = Abc_NtkAlloc( pNtk->ntkType, ABC_FUNC_SOP, 1 );
  else
    pManMR->pInitNtk = Abc_NtkAlloc( pNtk->ntkType, pNtk->ntkFunc, 1 );

  // mitre inputs
  Abc_NtkForEachLatch( pNtk, pLatch, i ) {
    // map latch to initial state network
    pPi = Abc_NtkCreatePi( pManMR->pInitNtk );

    // has initial state requirement?
    if (Abc_LatchIsInit0(pLatch)) {
      
      if (Abc_NtkHasAig(pNtk))
        pObj = Abc_ObjNot( pPi );
      else
        pObj = Abc_NtkCreateNodeInv( pManMR->pInitNtk, pPi );

      Vec_PtrPush(vObj, pObj);
    }
    else if (Abc_LatchIsInit1(pLatch)) {
      Vec_PtrPush(vObj, pPi);
    }
    
    Abc_ObjSetData( pLatch, pPi );     // if not verifying init state
    // FDATA(pLatch)->pInitObj = pPi;  // if verifying init state
  }

  // are there any nodes not DC?
  if (!Vec_PtrSize(vObj)) {
    pManMR->fSolutionIsDc = 1;
    return;
  } else 
    pManMR->fSolutionIsDc = 0;

  // mitre output
  if (Abc_NtkHasAig(pNtk)) {
    // create AND-by-AND
    pObj = Vec_PtrPop( vObj );
    while( Vec_PtrSize(vObj) )
      pObj = Abc_AigAnd( pManMR->pInitNtk->pManFunc, pObj, Vec_PtrPop( vObj ) ); 
  } else
    // create n-input AND gate
    pObj = Abc_NtkCreateNodeAnd( pManMR->pInitNtk, vObj );

  Abc_ObjAddFanin( Abc_NtkCreatePo( pManMR->pInitNtk ), pObj );

  Vec_PtrFree( vObj );
}


/**Function*************************************************************

  Synopsis    [Solves backward initial state computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_FlowRetime_SolveBackwardInit( Abc_Ntk_t * pNtk ) {
  int i;
  Abc_Obj_t *pObj, *pInitObj;
  Vec_Ptr_t *vDelete = Vec_PtrAlloc(0);
  int result;

  assert(pManMR->pInitNtk);

  // is the solution entirely DC's?
  if (pManMR->fSolutionIsDc) {
    Abc_NtkDelete(pManMR->pInitNtk);
    Vec_PtrFree(vDelete);
    Abc_NtkForEachLatch( pNtk, pObj, i ) Abc_LatchSetInitDc( pObj );
    vprintf("\tno init state computation: all-don't-care solution\n");
    return 1;
  }

  // check that network is combinational
  // mark superfluous BI nodes for deletion
  Abc_NtkForEachObj( pManMR->pInitNtk, pObj, i ) {
    assert(!Abc_ObjIsLatch(pObj));
    assert(!Abc_ObjIsBo(pObj));
    
    if (Abc_ObjIsBi(pObj)) {
      Abc_ObjBetterTransferFanout( pObj, Abc_ObjFanin0(pObj), Abc_ObjFaninC0(pObj) );
      Vec_PtrPush( vDelete, pObj );
    }
  }
  
  // delete superfluous nodes
  while(Vec_PtrSize( vDelete )) {
    pObj = (Abc_Obj_t *)Vec_PtrPop( vDelete );
    Abc_NtkDeleteObj( pObj );
  }
  Vec_PtrFree(vDelete);

  // do some final cleanup on the network
  Abc_NtkAddDummyPoNames(pManMR->pInitNtk);
  Abc_NtkAddDummyPiNames(pManMR->pInitNtk);
  if (Abc_NtkIsLogic(pManMR->pInitNtk))
    Abc_NtkCleanup(pManMR->pInitNtk, 0);
  else if (Abc_NtkIsStrash(pManMR->pInitNtk)) {  
    Abc_NtkReassignIds(pManMR->pInitNtk);
  }
  
  vprintf("\tsolving for init state (%d nodes)... ", Abc_NtkObjNum(pManMR->pInitNtk));
  fflush(stdout);

  // convert SOPs to BDD
  if (Abc_NtkHasSop(pManMR->pInitNtk))
    Abc_NtkSopToBdd( pManMR->pInitNtk );
  
  // solve
  result = Abc_NtkMiterSat( pManMR->pInitNtk, (sint64)500000, (sint64)50000000, 0, NULL, NULL );

  if (!result) { 
    vprintf("SUCCESS\n");
  } else  {    
    vprintf("FAILURE\n");
    printf("WARNING: no equivalent init state. setting all initial states to don't-cares\n");
    Abc_NtkForEachLatch( pNtk, pObj, i ) Abc_LatchSetInitDc( pObj );
    Abc_NtkDelete(pManMR->pInitNtk);
    return 0;
  }

  // clear initial values, associate PIs to latches
  Abc_NtkForEachPi( pManMR->pInitNtk, pInitObj, i ) Abc_ObjSetCopy( pInitObj, NULL );
  Abc_NtkForEachLatch( pNtk, pObj, i ) {
    pInitObj = Abc_ObjData( pObj );
    assert( Abc_ObjIsPi( pInitObj ));
    Abc_ObjSetCopy( pInitObj, pObj );
    Abc_LatchSetInitNone( pObj );
  }

  // copy solution from PIs to latches
  assert(pManMR->pInitNtk->pModel);
  Abc_NtkForEachPi( pManMR->pInitNtk, pInitObj, i ) {
    if ((pObj = Abc_ObjCopy( pInitObj ))) {
      if ( pManMR->pInitNtk->pModel[i] )
        Abc_LatchSetInit1( pObj );
      else
        Abc_LatchSetInit0( pObj );
    }
  }

#if defined(DEBUG_CHECK)
  // check that all latches have initial state
  Abc_NtkForEachLatch( pNtk, pObj, i ) assert( !Abc_LatchIsInitNone( pObj ) );
#endif

  // deallocate
  Abc_NtkDelete( pManMR->pInitNtk );

  return 1;
}


/**Function*************************************************************

  Synopsis    [Updates backward initial state computation problem.]

  Description [Assumes box outputs in old positions stored w/ init values.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FlowRetime_UpdateBackwardInit( Abc_Ntk_t * pNtk ) {
  Abc_Obj_t *pOrigObj,  *pInitObj;
  Vec_Ptr_t *vBo = Vec_PtrAlloc(100);
  Vec_Ptr_t *vOldPis = Vec_PtrAlloc(100);
  int i;

  // remove PIs from network (from BOs)
  Abc_NtkForEachObj( pNtk, pOrigObj, i )
    if (Abc_ObjIsBo(pOrigObj)) {
      pInitObj = FDATA(pOrigObj)->pInitObj;
      assert(Abc_ObjIsPi(pInitObj));
      Vec_PtrPush(vBo, pOrigObj);

      Abc_FlowRetime_UpdateBackwardInit_rec( Abc_ObjFanin0( pOrigObj ), pInitObj, vOldPis, 0 );
    }

  // add PIs to network (at latches)
  Abc_NtkForEachLatch( pNtk, pOrigObj, i )
    Abc_FlowRetime_UpdateBackwardInit_rec( pOrigObj, NULL, vOldPis, 0 );
  
  // connect nodes in init state network
  Vec_PtrForEachEntry( vBo, pOrigObj, i )
    Abc_FlowRetime_UpdateBackwardInit_rec( Abc_ObjFanin0( pOrigObj ), NULL, NULL, 1 );
  
  // clear flags
  Abc_NtkForEachObj( pNtk, pOrigObj, i )
    pOrigObj->fMarkA = pOrigObj->fMarkB = 0;

  // deallocate
  Vec_PtrFree( vBo );
  Vec_PtrFree( vOldPis );
}


/**Function*************************************************************

  Synopsis    [Updates backward initial state computation problem.]

  Description [Creates a duplicate node in the initial state network 
               corresponding to a node in the original circuit.  If
               fRecurse is set, the procedure recurses on and connects
               the new node to its fan-ins.  A latch in the original
               circuit corresponds to a PI in the initial state network.
               An existing PI may be supplied by pUseThisPi, and if the
               node is a latch, it will be used; otherwise the PI is
               saved in the list vOtherPis and subsequently used for
               another latch.]
               
  SideEffects [Nodes that have a corresponding initial state node
               are marked with fMarkA.  Nodes that have been fully
               connected in the initial state network are marked with
               fMarkB.]

  SeeAlso     []

***********************************************************************/
Abc_Obj_t* Abc_FlowRetime_UpdateBackwardInit_rec( Abc_Obj_t *pOrigObj, 
                                                  Abc_Obj_t *pUseThisPi, Vec_Ptr_t *vOtherPis, 
                                                  int fRecurse) {
  Abc_Obj_t *pInitObj, *pOrigFanin, *pInitFanin;
  void      *pData;
  int i;
  Abc_Ntk_t *pNtk = Abc_ObjNtk( pOrigObj );

  // should never reach primary IOs
  assert(!Abc_ObjIsPi(pOrigObj));
  assert(!Abc_ObjIsPo(pOrigObj));

  // if fanin is latch, it becomes a primary input
  if (Abc_ObjIsLatch( pOrigObj )) {
    if (pOrigObj->fMarkA)  return FDATA(pOrigObj)->pInitObj;

    assert(vOtherPis);
    
    if (pUseThisPi) { 
      // reuse curent PI     
      pInitObj = pUseThisPi; }
    else { 
      // reuse previous PI
      pInitObj = (Abc_Obj_t*)Vec_PtrPop(vOtherPis); 
    }
    
    // remember link from original node to init ntk
    Abc_ObjSetData( pOrigObj, pInitObj ); 

    pOrigObj->fMarkA = 1;
    return (FDATA(pOrigObj)->pInitObj = pInitObj);
  } 

  // does an init node already exist?
  if(!pOrigObj->fMarkA) {

    if (Abc_NtkHasMapping( pNtk )) {
      if (!pOrigObj->pData) {
        // assume terminal...
        assert(Abc_ObjFaninNum(pOrigObj) == 1);
        pInitObj = Abc_NtkCreateNodeBuf( pManMR->pInitNtk, NULL );
      } else {
        pInitObj = Abc_NtkCreateObj( pManMR->pInitNtk, Abc_ObjType(pOrigObj) );
        pData = Mio_GateReadSop(pOrigObj->pData);
        assert( Abc_SopGetVarNum(pData) == Abc_ObjFaninNum(pOrigObj) );

        pInitObj->pData = Abc_SopRegister( pManMR->pInitNtk->pManFunc, pData );
      }
    } else {
      pData = Abc_ObjCopy( pOrigObj );   // save ptr to flow data    
      if (Abc_NtkIsStrash( pNtk ) && Abc_AigNodeIsConst( pOrigObj ))
        pInitObj = Abc_AigConst1( pManMR->pInitNtk );
      else
        pInitObj = Abc_NtkDupObj( pManMR->pInitNtk, pOrigObj, 0 );
      Abc_ObjSetCopy( pOrigObj, pData ); // restore ptr to flow data

      // copy complementation
      pInitObj->fCompl0 = pOrigObj->fCompl0;
      pInitObj->fCompl1 = pOrigObj->fCompl1;
      pInitObj->fPhase = pOrigObj->fPhase;
    }

    // if we didn't use given PI, immediately transfer fanouts
    // and add to list for later reuse
    if (pUseThisPi) {
      Abc_ObjBetterTransferFanout( pUseThisPi, pInitObj, 0 );
      Vec_PtrPush( vOtherPis, pUseThisPi );
    }

    pOrigObj->fMarkA = 1;
    FDATA(pOrigObj)->pInitObj = pInitObj;
  } else {
    pInitObj = FDATA(pOrigObj)->pInitObj;
  }
    
  // have we already connected this object?
  if (fRecurse && !pOrigObj->fMarkB) {

    // create and/or connect fanins
    Abc_ObjForEachFanin( pOrigObj, pOrigFanin, i ) {
      pInitFanin = Abc_FlowRetime_UpdateBackwardInit_rec( pOrigFanin, NULL, NULL, fRecurse );
      Abc_ObjAddFanin( pInitObj, pInitFanin );
    }

    pOrigObj->fMarkB = 1;
  }

  return pInitObj;
}


/**Function*************************************************************

  Synopsis    [Verifies backward init state computation.]

  Description [This procedure requires the BOs to store the original
               latch values and the latches to store the new values:
               both in the INIT_0 and INIT_1 flags in the Flow_Data
               structure.  (This is not currently the case in the rest
               of the code.)  Also, can not verify backward state
               computations that span multiple combinational frames.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FlowRetime_VerifyBackwardInit( Abc_Ntk_t * pNtk ) {
  Abc_Obj_t *pObj, *pFanin;
  int i;

  vprintf("\t\tupdating init state\n");

  Abc_NtkIncrementTravId( pNtk );

  Abc_NtkForEachObj( pNtk, pObj, i )
    if (Abc_ObjIsBo( pObj )) {
      pFanin = Abc_ObjFanin0(pObj);
      Abc_FlowRetime_VerifyBackwardInit_rec( pFanin );

      if (FTEST(pObj, INIT_CARE)) {
        if(FTEST(pObj, INIT_CARE) != FTEST(pFanin, INIT_CARE)) {
          printf("ERROR: expected val=%d care=%d and got val=%d care=%d\n",
                 FTEST(pObj, INIT_1)?1:0, FTEST(pObj, INIT_CARE)?1:0, 
                 FTEST(pFanin, INIT_1)?1:0, FTEST(pFanin, INIT_CARE)?1:0 );

        }
      }
    }
}

void Abc_FlowRetime_VerifyBackwardInit_rec( Abc_Obj_t * pObj ) {
  Abc_Obj_t *pNext;
  int i;

  assert(!Abc_ObjIsBo(pObj)); // should never reach the inputs
  assert(!Abc_ObjIsPi(pObj)); // should never reach the inputs

  // visited?
  if (Abc_NodeIsTravIdCurrent(pObj)) return;
  Abc_NodeSetTravIdCurrent(pObj);

  if (Abc_ObjIsLatch(pObj)) {
    FUNSET(pObj, INIT_CARE);
    if (Abc_LatchIsInit0(pObj))
      FSET(pObj, INIT_0);
    else if (Abc_LatchIsInit1(pObj))
      FSET(pObj, INIT_1);
    return;
  }

  Abc_ObjForEachFanin( pObj, pNext, i ) {
    Abc_FlowRetime_VerifyBackwardInit_rec( pNext );
  }
  
  Abc_FlowRetime_SimulateNode( pObj );
}


/**Function*************************************************************

  Synopsis    [Constrains backward retiming for initializability.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FlowRetime_ConstrainInit( ) {
  // unimplemented
}
