/**CFile****************************************************************

  FileName    [fretMain.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Flow-based retiming package.]

  Synopsis    [Main file for retiming package.]

  Author      [Aaron Hurst]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - January 1, 2008.]

  Revision    [$Id: fretMain.c,v 1.00 2008/01/01 00:00:00 ahurst Exp $]

***********************************************************************/

#include "abc.h"
#include "vec.h"
#include "fretime.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void Abc_FlowRetime_AddDummyFanin( Abc_Obj_t * pObj );

static void Abc_FlowRetime_MarkBlocks( Abc_Ntk_t * pNtk );
static void Abc_FlowRetime_MarkReachable_rec( Abc_Obj_t * pObj, char end );
static int  Abc_FlowRetime_PushFlows( Abc_Ntk_t * pNtk );
static int  Abc_FlowRetime_ImplementCut( Abc_Ntk_t * pNtk );
static void  Abc_FlowRetime_RemoveLatchBubbles( Abc_Obj_t * pLatch );

static void Abc_FlowRetime_VerifyPathLatencies( Abc_Ntk_t * pNtk );
static int  Abc_FlowRetime_VerifyPathLatencies_rec( Abc_Obj_t * pObj, int markD );

extern void Abc_NtkMarkCone_rec( Abc_Obj_t * pObj, int fForward );
extern Abc_Ntk_t * Abc_NtkRestrash( Abc_Ntk_t * pNtk, bool fCleanup );

int         fIsForward, fComputeInitState;
int         fSinkDistTerminate;
Vec_Int_t  *vSinkDistHist;
int         maxDelayCon;

int         fPathError = 0;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs minimum-register retiming.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t *
Abc_FlowRetime_MinReg( Abc_Ntk_t * pNtk, int fVerbose, int fComputeInitState_,
                       int fForwardOnly, int fBackwardOnly, int nMaxIters,
                       int maxDelay ) {

  int i, j, nNodes, nLatches, flow, last, cut;
  int iteration = 0;
  Flow_Data_t *pDataArray;
  Abc_Obj_t   *pObj, *pNext;

  fComputeInitState = fComputeInitState_;

  printf("Flow-based minimum-register retiming...\n");  

  if (!Abc_NtkHasOnlyLatchBoxes(pNtk)) {
    printf("\tERROR: Can not retime with black/white boxes\n");
    return pNtk;
  }

  maxDelayCon = maxDelay;
  if (maxDelayCon) {
    printf("\tmax delay constraint = %d\n", maxDelayCon);
    if (maxDelayCon < (i = Abc_NtkLevel(pNtk))) {
      printf("ERROR: max delay constraint must be > current max delay (%d)\n", i);
      return pNtk;
    }
  }

  // print info about type of network
  printf("\tnetlist type = ");
  if (Abc_NtkIsNetlist( pNtk )) printf("netlist/");
  else if (Abc_NtkIsLogic( pNtk )) printf("logic/");
  else if (Abc_NtkIsStrash( pNtk )) printf("strash/");
  else printf("***unknown***/");
  if (Abc_NtkHasSop( pNtk )) printf("sop\n");
  else if (Abc_NtkHasBdd( pNtk )) printf("bdd\n");
  else if (Abc_NtkHasAig( pNtk )) printf("aig\n");
  else if (Abc_NtkHasMapping( pNtk )) printf("mapped\n");
  else printf("***unknown***\n");

  printf("\tinitial reg count = %d\n", Abc_NtkLatchNum(pNtk));

  // remove bubbles from latch boxes
  Abc_FlowRetime_PrintInitStateInfo(pNtk);
  printf("\tpushing bubbles out of latch boxes\n");
  Abc_NtkForEachLatch( pNtk, pObj, i )
    Abc_FlowRetime_RemoveLatchBubbles(pObj);
  Abc_FlowRetime_PrintInitStateInfo(pNtk);

  // check for box inputs/outputs
  Abc_NtkForEachLatch( pNtk, pObj, i ) {
    assert(Abc_ObjFaninNum(pObj) == 1);
    assert(Abc_ObjFanoutNum(pObj) == 1);
    assert(!Abc_ObjFaninC0(pObj));

    pNext = Abc_ObjFanin0(pObj);
    assert(Abc_ObjIsBi(pNext));
    assert(Abc_ObjFaninNum(pNext) <= 1);
    if(Abc_ObjFaninNum(pNext) == 0) // every Bi should have a fanin
      Abc_FlowRetime_AddDummyFanin( pNext );
 
    pNext = Abc_ObjFanout0(pObj);
    assert(Abc_ObjIsBo(pNext));
    assert(Abc_ObjFaninNum(pNext) == 1);
    assert(!Abc_ObjFaninC0(pNext));
  }

  nLatches = Abc_NtkLatchNum( pNtk );
  nNodes = Abc_NtkObjNumMax( pNtk )+1;
   
  // build histogram
  vSinkDistHist = Vec_IntStart( nNodes*2+10 );

  // create Flow_Data structure
  pDataArray = (Flow_Data_t *)malloc(sizeof(Flow_Data_t)*nNodes);
  memset(pDataArray, 0, sizeof(Flow_Data_t)*nNodes);
  Abc_NtkForEachObj( pNtk, pObj, i )
    Abc_ObjSetCopy( pObj, (void *)(&pDataArray[i]) );

  // (i) forward retiming loop
  fIsForward = 1;

  if (!fBackwardOnly) do {
    if (iteration == nMaxIters) break;

    printf("\tforward iteration %d\n", iteration);
    last = Abc_NtkLatchNum( pNtk );

    Abc_FlowRetime_MarkBlocks( pNtk );
    flow = Abc_FlowRetime_PushFlows( pNtk );
    cut = Abc_FlowRetime_ImplementCut( pNtk );

    // clear all
    memset(pDataArray, 0, sizeof(Flow_Data_t)*nNodes);    
    iteration++;
  } while( flow != last );

  // print info about initial states
  if (fComputeInitState)
    Abc_FlowRetime_PrintInitStateInfo( pNtk );

  // (ii) backward retiming loop
  fIsForward = 0;
  iteration = 0;

  if (!fForwardOnly) {
    if (fComputeInitState) {
      Abc_FlowRetime_SetupBackwardInit( pNtk );
    }

    do {
      if (iteration == nMaxIters) break;

      printf("\tbackward iteration %d\n", iteration);
      last = Abc_NtkLatchNum( pNtk );
      
      Abc_FlowRetime_MarkBlocks( pNtk );
      flow = Abc_FlowRetime_PushFlows( pNtk );
      cut = Abc_FlowRetime_ImplementCut( pNtk );
      
      // clear all
      memset(pDataArray, 0, sizeof(Flow_Data_t)*nNodes);    
      iteration++;

    } while( flow != last );
    
    // compute initial states
    if (fComputeInitState) {
      Abc_FlowRetime_SolveBackwardInit( pNtk );
      Abc_FlowRetime_PrintInitStateInfo( pNtk );
    }
  }

  // clear pCopy field
  Abc_NtkForEachObj( pNtk, pObj, i ) {
    Abc_ObjSetCopy( pObj, NULL );

    // if not computing init state, set all latches to DC
    if (!fComputeInitState && Abc_ObjIsLatch(pObj))
      Abc_LatchSetInitDc(pObj);
  }

  // restrash if necessary
  if (Abc_NtkIsStrash(pNtk)) {
    Abc_NtkReassignIds( pNtk );
    pNtk = Abc_NtkRestrash( pNtk, 1 );
  }
  
#if defined(DEBUG_CHECK)
  Abc_NtkDoCheck( pNtk );
#endif

  // deallocate space
  free(pDataArray);
  if (vSinkDistHist) Vec_IntFree(vSinkDistHist);

  printf("\tfinal reg count = %d\n", Abc_NtkLatchNum(pNtk));

  return pNtk;
}

/**Function*************************************************************

  Synopsis    [Pushes latch bubbles outside of box.]

  Description [If network is an AIG, a fCompl0 is allowed to remain on
               the BI node.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void
Abc_FlowRetime_RemoveLatchBubbles( Abc_Obj_t * pLatch ) {
  int i, j, k, bubble = 0;
  Abc_Ntk_t *pNtk = Abc_ObjNtk( pLatch );
  Abc_Obj_t *pBi, *pBo, *pInv;
      
  pBi = Abc_ObjFanin0(pLatch);
  pBo = Abc_ObjFanout0(pLatch);
  assert(!Abc_ObjIsComplement(pBi));
  assert(!Abc_ObjIsComplement(pBo));

  // push bubbles on BO into latch box
  if (Abc_ObjFaninC0(pBo) && Abc_ObjFanoutNum(pBo) > 0) {
    bubble = 1;
    if (Abc_LatchIsInit0(pLatch)) Abc_LatchSetInit1(pLatch);
    else if (Abc_LatchIsInit1(pLatch)) Abc_LatchSetInit0(pLatch);  
  }

  // absorb bubbles on BI
  pBi->fCompl0 ^= bubble ^ Abc_ObjFaninC0(pLatch);

  // convert bubble to INV if not AIG
  if (!Abc_NtkHasAig( pNtk ) && Abc_ObjFaninC0(pBi)) {
    pBi->fCompl0 = 0;
    pInv = Abc_NtkCreateNodeInv( pNtk, Abc_ObjFanin0(pBi) );
    Abc_ObjPatchFanin( pBi, Abc_ObjFanin0(pBi), pInv );
  }

  pBo->fCompl0 = 0;
  pLatch->fCompl0 = 0;
}


/**Function*************************************************************

  Synopsis    [Marks nodes in TFO/TFI of PI/PO.]

  Description [Sets flow data flag BLOCK appropriately.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void
Abc_FlowRetime_MarkBlocks( Abc_Ntk_t * pNtk ) {
  int i;
  Abc_Obj_t *pObj;

  if (fIsForward){
    // mark the frontier
    Abc_NtkForEachPo( pNtk, pObj, i )
      pObj->fMarkA = 1;
    Abc_NtkForEachLatch( pNtk, pObj, i )
      {
        pObj->fMarkA = 1;
      }
    // mark the nodes reachable from the PIs
    Abc_NtkForEachPi( pNtk, pObj, i )
      Abc_NtkMarkCone_rec( pObj, fIsForward );
  } else {
    // mark the frontier
    Abc_NtkForEachPi( pNtk, pObj, i )
      pObj->fMarkA = 1;
    Abc_NtkForEachLatch( pNtk, pObj, i )
      {
        pObj->fMarkA = 1;
      }
    // mark the nodes reachable from the POs
    Abc_NtkForEachPo( pNtk, pObj, i )
      Abc_NtkMarkCone_rec( pObj, fIsForward );
  }

  // copy marks
  Abc_NtkForEachObj( pNtk, pObj, i ) {
    if (pObj->fMarkA) {
      pObj->fMarkA = 0;
      if (!Abc_ObjIsLatch(pObj) && 
          !Abc_ObjIsPi(pObj))
        FSET(pObj, BLOCK);
    }
  }
}


/**Function*************************************************************

  Synopsis    [Computes maximum flow.]

  Description []
               
  SideEffects [Leaves VISITED flags on source-reachable nodes.]

  SeeAlso     []

***********************************************************************/
int
Abc_FlowRetime_PushFlows( Abc_Ntk_t * pNtk ) {
  int i, j, flow = 0, last, srcDist = 0;
  Abc_Obj_t   *pObj, *pObj2;

  fSinkDistTerminate = 0;
  dfsfast_preorder( pNtk );

  // (i) fast max-flow computation
  while(!fSinkDistTerminate && srcDist < MAX_DIST) {
    srcDist = MAX_DIST;
    Abc_NtkForEachLatch( pNtk, pObj, i )
      if (FDATA(pObj)->e_dist)    
        srcDist = MIN(srcDist, FDATA(pObj)->e_dist);
    
    Abc_NtkForEachLatch( pNtk, pObj, i ) {
      if (srcDist == FDATA(pObj)->e_dist &&
          dfsfast_e( pObj, NULL )) {
#ifdef DEBUG_PRINT_FLOWS
        printf("\n\n");
#endif
        flow++;
      }
    }
  }

  printf("\t\tmax-flow1 = %d \t", flow);

  // (ii) complete max-flow computation
  // also, marks source-reachable nodes
  do {
    last = flow;
    Abc_NtkForEachLatch( pNtk, pObj, i ) {
      if (dfsplain_e( pObj, NULL )) {
#ifdef DEBUG_PRINT_FLOWS
        printf("\n\n");
#endif
        flow++;
        Abc_NtkForEachObj( pNtk, pObj2, j )
          FUNSET( pObj2, VISITED );
      }
    }
  } while (flow > last);
  
  printf("max-flow2 = %d\n", flow);

  return flow;
}


/**Function*************************************************************

  Synopsis    [Restores latch boxes.]

  Description [Latchless BI/BO nodes are removed.  Latch boxes are 
               restored around remaining latches.]
               
  SideEffects [Deletes nodes as appropriate.]

  SeeAlso     []

***********************************************************************/
void
Abc_FlowRetime_FixLatchBoxes( Abc_Ntk_t *pNtk, Vec_Ptr_t *vBoxIns ) {
  int i;
  Abc_Obj_t *pObj, *pNext, *pBo = NULL, *pBi = NULL;
  Vec_Ptr_t *vFreeBi = Vec_PtrAlloc( 100 );
  Vec_Ptr_t *vFreeBo = Vec_PtrAlloc( 100 );
  Vec_Ptr_t *vNodes;

  // 1. remove empty bi/bo pairs
  while(Vec_PtrSize( vBoxIns )) {
    pBi = (Abc_Obj_t *)Vec_PtrPop( vBoxIns );
    assert(Abc_ObjIsBi(pBi));
    assert(Abc_ObjFanoutNum(pBi) == 1);
    assert(Abc_ObjFaninNum(pBi) == 1);
    pBo = Abc_ObjFanout0(pBi);
    assert(!Abc_ObjFaninC0(pBo));

    if (Abc_ObjIsBo(pBo)) {
      // an empty bi/bo pair

      Abc_ObjRemoveFanins( pBo );
      // transfer complement from BI, if present 
      assert(!Abc_ObjIsComplement(Abc_ObjFanin0(pBi)));
      Abc_ObjBetterTransferFanout( pBo, Abc_ObjFanin0(pBi), Abc_ObjFaninC0(pBi) );

      Abc_ObjRemoveFanins( pBi );
      pBi->fCompl0 = 0;
      Vec_PtrPush( vFreeBi, pBi );
      Vec_PtrPush( vFreeBo, pBo );

      // free names
      // if (Nm_ManFindNameById(pNtk->pManName, Abc_ObjId(pBi)))
      //  Nm_ManDeleteIdName( pNtk->pManName, Abc_ObjId(pBi));
      //if (Nm_ManFindNameById(pNtk->pManName, Abc_ObjId(pBo)))
      //  Nm_ManDeleteIdName( pNtk->pManName, Abc_ObjId(pBo));

      // check for complete detachment
      assert(Abc_ObjFaninNum(pBi) == 0);
      assert(Abc_ObjFanoutNum(pBi) == 0);
      assert(Abc_ObjFaninNum(pBo) == 0);
      assert(Abc_ObjFanoutNum(pBo) == 0);
    } else assert(Abc_ObjIsLatch(pBo));
  }

  // 2. add bi/bos as necessary for latches
  Abc_NtkForEachLatch( pNtk, pObj, i ) {
    assert(Abc_ObjFaninNum(pObj) == 1);
    if (Abc_ObjFanoutNum(pObj))
      pBo = Abc_ObjFanout0(pObj);
    else pBo = NULL;
    pBi = Abc_ObjFanin0(pObj);
    
    // add BO
    if (!pBo || !Abc_ObjIsBo(pBo)) {
      pBo = (Abc_Obj_t *)Vec_PtrPop( vFreeBo );
      if (Abc_ObjFanoutNum(pObj))  Abc_ObjTransferFanout( pObj, pBo );
      Abc_ObjAddFanin( pBo, pObj );
    }
    // add BI
    if (!Abc_ObjIsBi(pBi)) {
      pBi = (Abc_Obj_t *)Vec_PtrPop( vFreeBi );
      assert(Abc_ObjFaninNum(pBi) == 0);
      Abc_ObjAddFanin( pBi, Abc_ObjFanin0(pObj) );
      pBi->fCompl0 = pObj->fCompl0;
      Abc_ObjRemoveFanins( pObj );
      Abc_ObjAddFanin( pObj, pBi );
    }
  }

  // delete remaining BIs and BOs
  while(Vec_PtrSize( vFreeBi )) {
    pObj = (Abc_Obj_t *)Vec_PtrPop( vFreeBi );
    Abc_NtkDeleteObj( pObj );
  }
  while(Vec_PtrSize( vFreeBo )) {
    pObj = (Abc_Obj_t *)Vec_PtrPop( vFreeBo );
    Abc_NtkDeleteObj( pObj );
  }

#if defined(DEBUG_CHECK)
  Abc_NtkForEachObj( pNtk, pObj, i ) {
    if (Abc_ObjIsBo(pObj)) {
      assert(Abc_ObjFaninNum(pObj) == 1);
      assert(Abc_ObjIsLatch(Abc_ObjFanin0(pObj))); 
    }
    if (Abc_ObjIsBi(pObj)) {
      assert(Abc_ObjFaninNum(pObj) == 1);
      assert(Abc_ObjFanoutNum(pObj) == 1);
      assert(Abc_ObjIsLatch(Abc_ObjFanout0(pObj))); 
    }
    if (Abc_ObjIsLatch(pObj)) {
      assert(Abc_ObjFanoutNum(pObj) == 1);
      assert(Abc_ObjFaninNum(pObj) == 1);
    }
  }
#endif

  Vec_PtrFree( vFreeBi );
  Vec_PtrFree( vFreeBo );
}


/**Function*************************************************************

  Synopsis    [Checks register count along all combinational paths.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void
Abc_FlowRetime_VerifyPathLatencies( Abc_Ntk_t * pNtk ) {
  int i;
  Abc_Obj_t *pObj;
  fPathError = 0;

  printf("\t\tVerifying latency along all paths...");

  Abc_NtkForEachObj( pNtk, pObj, i ) {
    if (Abc_ObjIsBo(pObj)) {
      Abc_FlowRetime_VerifyPathLatencies_rec( pObj, 0 );
    } else if (!fIsForward && Abc_ObjIsPi(pObj)) {
      Abc_FlowRetime_VerifyPathLatencies_rec( pObj, 0 );
    }

    if (fPathError) {
      if (Abc_ObjFaninNum(pObj) > 0) {
        printf("fanin ");
        print_node(Abc_ObjFanin0(pObj));
      }
      printf("\n");
      exit(0);
    }
  }

  printf(" ok\n");

  Abc_NtkForEachObj( pNtk, pObj, i ) {
    pObj->fMarkA = 0;
    pObj->fMarkB = 0;
    pObj->fMarkC = 0;
  }
}


int
Abc_FlowRetime_VerifyPathLatencies_rec( Abc_Obj_t * pObj, int markD ) {
  int i, j;
  Abc_Obj_t *pNext;
  int fCare = 0;
  int markC = pObj->fMarkC;

  if (!pObj->fMarkB) {
    pObj->fMarkB = 1; // visited
    
    if (Abc_ObjIsLatch(pObj))
      markC = 1;      // latch in output
    
    if (!fIsForward && !Abc_ObjIsPo(pObj) && !Abc_ObjFanoutNum(pObj))
      return -1; // dangling non-PO outputs : don't care what happens
    
    Abc_ObjForEachFanout( pObj, pNext, i ) {
      // reached end of cycle?
      if ( Abc_ObjIsBo(pNext) ||
           (fIsForward && Abc_ObjIsPo(pNext)) ) {
        if (!markD && !Abc_ObjIsLatch(pObj)) {
          printf("\nERROR: no-latch path (end)\n");
          print_node(pNext);
          printf("\n");
          fPathError = 1;
        }
      } else if (!fIsForward && Abc_ObjIsPo(pNext)) {
        if (markD || Abc_ObjIsLatch(pObj)) {
          printf("\nERROR: extra-latch path to outputs\n");
          print_node(pNext);
          printf("\n");
          fPathError = 1;
        }
      } else {
        j = Abc_FlowRetime_VerifyPathLatencies_rec( pNext, markD || Abc_ObjIsLatch(pObj) );
        if (j >= 0) {
          markC |= j;
          fCare = 1;
        }
      }

      if (fPathError) {
        print_node(pObj);
        printf("\n");
        return 0;
      }
    }
  }

  if (!fCare) return -1;

  if (markC && markD) {
    printf("\nERROR: mult-latch path\n");
    print_node(pObj);
    printf("\n");
    fPathError = 1;
  }
  if (!markC && !markD) {
    printf("\nERROR: no-latch path (inter)\n");
    print_node(pObj);
    printf("\n");
    fPathError = 1;
  }

  return (pObj->fMarkC = markC);
}


/**Function*************************************************************

  Synopsis    [Copies initial state from latches to BO nodes.]

  Description [Initial states are marked on BO nodes with INIT_0 and
               INIT_1 flags in their Flow_Data structures.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void
Abc_FlowRetime_CopyInitState( Abc_Obj_t * pSrc, Abc_Obj_t * pDest ) {
  Abc_Obj_t *pObj;

  if (!fComputeInitState) return;

  assert(Abc_ObjIsLatch(pSrc));
  assert(Abc_ObjFanin0(pDest) == pSrc);
  assert(!Abc_ObjFaninC0(pDest));

  FUNSET(pDest, INIT_CARE);
  if (Abc_LatchIsInit0(pSrc)) {
    FSET(pDest, INIT_0);
  } else if (Abc_LatchIsInit1(pSrc)) {
    FSET(pDest, INIT_1);  
  }
  
  if (!fIsForward) {
    pObj = Abc_ObjData(pSrc);
    assert(Abc_ObjIsPi(pObj));
    FDATA(pDest)->pInitObj = pObj;
  }
}


/**Function*************************************************************

  Synopsis    [Implements min-cut.]

  Description [Requires source-reachable nodes to be marked VISITED.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int
Abc_FlowRetime_ImplementCut( Abc_Ntk_t * pNtk ) {
  int i, j, cut = 0, unmoved = 0;
  Abc_Obj_t *pObj, *pReg, *pNext, *pBo = NULL, *pBi = NULL;
  Vec_Ptr_t *vFreeRegs = Vec_PtrAlloc( Abc_NtkLatchNum(pNtk) );
  Vec_Ptr_t *vBoxIns = Vec_PtrAlloc( Abc_NtkLatchNum(pNtk) );
  Vec_Ptr_t *vMove = Vec_PtrAlloc( 100 );

  // remove latches from netlist
  Abc_NtkForEachLatch( pNtk, pObj, i ) {
    pBo = Abc_ObjFanout0(pObj);
    pBi = Abc_ObjFanin0(pObj);
    assert(Abc_ObjIsBo(pBo) && Abc_ObjIsBi(pBi));
    Vec_PtrPush( vBoxIns, pBi );

    // copy initial state values to BO
    Abc_FlowRetime_CopyInitState( pObj, pBo );

    // re-use latch elsewhere
    Vec_PtrPush( vFreeRegs, pObj );
    FSET(pBo, CROSS_BOUNDARY);

    // cut out of netlist
    Abc_ObjPatchFanin( pBo, pObj, pBi );
    Abc_ObjRemoveFanins( pObj );

    // free name
    // if (Nm_ManFindNameById(pNtk->pManName, Abc_ObjId(pObj)))
    //  Nm_ManDeleteIdName( pNtk->pManName, Abc_ObjId(pObj));
  }

  // insert latches into netlist
  Abc_NtkForEachObj( pNtk, pObj, i ) {
    if (Abc_ObjIsLatch( pObj )) continue;
    
    // a latch is required on every node that lies across the min-cit
    assert(!fIsForward || !FTEST(pObj, VISITED_E) || FTEST(pObj, VISITED_R));
    if (FTEST(pObj, VISITED_R) && !FTEST(pObj, VISITED_E)) {
      assert(FTEST(pObj, FLOW));

      // count size of cut
      cut++;
      if ((fIsForward && Abc_ObjIsBo(pObj)) || 
          (!fIsForward && Abc_ObjIsBi(pObj)))
        unmoved++;
      
      // only insert latch between fanouts that lie across min-cut
      // some fanout paths may be cut at deeper points
      Abc_ObjForEachFanout( pObj, pNext, j )
        if (fIsForward) {
          if (!FTEST(pNext, VISITED_R) || 
              FTEST(pNext, BLOCK) || 
              FTEST(pNext, CROSS_BOUNDARY) || 
              Abc_ObjIsLatch(pNext))
            Vec_PtrPush(vMove, pNext);
        } else {
          if (FTEST(pNext, VISITED_E) ||
              FTEST(pNext, CROSS_BOUNDARY))
            Vec_PtrPush(vMove, pNext);
        }
      if (Vec_PtrSize(vMove) == 0)
        print_node(pObj);

      assert(Vec_PtrSize(vMove) > 0);
      
      // insert one of re-useable registers
      assert(Vec_PtrSize( vFreeRegs ));
      pReg = (Abc_Obj_t *)Vec_PtrPop( vFreeRegs );
      
      Abc_ObjAddFanin(pReg, pObj);
      while(Vec_PtrSize( vMove )) {
        pNext = (Abc_Obj_t *)Vec_PtrPop( vMove );
        Abc_ObjPatchFanin( pNext, pObj, pReg );
        if (Abc_ObjIsBi(pNext)) assert(Abc_ObjFaninNum(pNext) == 1);

      }
      if (Abc_ObjIsBi(pObj)) assert(Abc_ObjFaninNum(pObj) == 1);
    }
  }

#if defined(DEBUG_CHECK)        
  Abc_FlowRetime_VerifyPathLatencies( pNtk );
#endif

  // delete remaining latches
  while(Vec_PtrSize( vFreeRegs )) {
    pReg = (Abc_Obj_t *)Vec_PtrPop( vFreeRegs );
    Abc_NtkDeleteObj( pReg );
  }
  
  // update initial states
  Abc_FlowRetime_InitState( pNtk );

  // restore latch boxes
  Abc_FlowRetime_FixLatchBoxes( pNtk, vBoxIns );

  Vec_PtrFree( vFreeRegs );
  Vec_PtrFree( vMove );
  Vec_PtrFree( vBoxIns );

  printf("\t\tmin-cut = %d (unmoved = %d)\n", cut, unmoved);
  return cut;
}

/**Function*************************************************************

  Synopsis    [Adds dummy fanin.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void
Abc_FlowRetime_AddDummyFanin( Abc_Obj_t * pObj ) {
  Abc_Ntk_t *pNtk = Abc_ObjNtk( pObj );

  if (Abc_NtkHasAig(pNtk)) 
    Abc_ObjAddFanin(pObj, Abc_AigConst1( pNtk ));
  else
    Abc_ObjAddFanin(pObj, Abc_NtkCreateNodeConst0( pNtk ));
}


/**Function*************************************************************

  Synopsis    [Prints information about a node.]

  Description [Debuging.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void
print_node(Abc_Obj_t *pObj) {
  int i;
  Abc_Obj_t * pNext;
  char m[6];

  m[0] = 0;
  if (pObj->fMarkA)
    strcat(m, "A");
  if (pObj->fMarkB)
    strcat(m, "B");
  if (pObj->fMarkC)
    strcat(m, "C");

  printf("node %d type=%d (%x%s) fanouts {", Abc_ObjId(pObj), Abc_ObjType(pObj), FDATA(pObj)->mark, m);
  Abc_ObjForEachFanout( pObj, pNext, i )
    printf("%d (%d),", Abc_ObjId(pNext), FDATA(pNext)->mark);
  printf("} fanins {");
  Abc_ObjForEachFanin( pObj, pNext, i )
    printf("%d (%d),", Abc_ObjId(pNext), FDATA(pNext)->mark);
  printf("} ");
}

void
print_node2(Abc_Obj_t *pObj) {
  int i;
  Abc_Obj_t * pNext;
  char m[6];

  m[0] = 0;
  if (pObj->fMarkA)
    strcat(m, "A");
  if (pObj->fMarkB)
    strcat(m, "B");
  if (pObj->fMarkC)
    strcat(m, "C");

  printf("node %d type=%d fanouts {", Abc_ObjId(pObj), Abc_ObjType(pObj), m);
  Abc_ObjForEachFanout( pObj, pNext, i )
    printf("%d ,", Abc_ObjId(pNext));
  printf("} fanins {");
  Abc_ObjForEachFanin( pObj, pNext, i )
    printf("%d ,", Abc_ObjId(pNext));
  printf("} ");
}


/**Function*************************************************************

  Synopsis    [Transfers fanout.]

  Description [Does not produce an error if there is no fanout.
               Complements as necessary.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void 
Abc_ObjBetterTransferFanout( Abc_Obj_t * pFrom, Abc_Obj_t * pTo, int compl ) {
  Abc_Obj_t *pNext;
  
  while(Abc_ObjFanoutNum(pFrom) > 0) {
    pNext = Abc_ObjFanout0(pFrom);
    Abc_ObjPatchFanin( pNext, pFrom, Abc_ObjNotCond(pTo, compl) );
  }
}
