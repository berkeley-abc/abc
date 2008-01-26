/**CFile****************************************************************

  FileName    [fretime.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Flow-based retiming package.]

  Synopsis    [Header file for retiming package.]

  Author      [Aaron Hurst]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - January 1, 2008.]

  Revision    [$Id: fretime.h,v 1.00 2008/01/01 00:00:00 ahurst Exp $]

***********************************************************************/

#if !defined(RETIME_H_)
#define RETIME_H_

#include "abc.h"

// #define IGNORE_TIMING
// #define DEBUG_PRINT_FLOWS
// #define DEBUG_VISITED
// #define DEBUG_PREORDER
// #define DEBUG_CHECK

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define MAX_DIST 30000

// flags in Flow_Data structure...
#define VISITED_E       0x01
#define VISITED_R       0x02
#define VISITED  (VISITED_E | VISITED_R)
#define FLOW            0x04
#define CROSS_BOUNDARY  0x08
#define BLOCK           0x10
#define INIT_0          0x20
#define INIT_1          0x40
#define INIT_CARE (INIT_0 | INIT_1)
#define CONSERVATIVE    0x80
#define BLOCK_OR_CONS (BLOCK | CONSERVATIVE)

typedef struct Flow_Data_t_ {
  unsigned int mark : 16;

  union {
    Abc_Obj_t   *pred;
    /* unsigned int var; */
    Abc_Obj_t   *pInitObj;
    Vec_Ptr_t   *vNodes;
  };

  unsigned int e_dist : 16;
  unsigned int r_dist : 16;
} Flow_Data_t;

// useful macros for manipulating Flow_Data structure...
#define FDATA( x )     ((Flow_Data_t *)Abc_ObjCopy(x))
#define FSET( x, y )   ((Flow_Data_t *)Abc_ObjCopy(x))->mark |= y
#define FUNSET( x, y ) ((Flow_Data_t *)Abc_ObjCopy(x))->mark &= ~y
#define FTEST( x, y )  (((Flow_Data_t *)Abc_ObjCopy(x))->mark & y)
#define FTIMEEDGES( x )  &(pManMR->vTimeEdges[Abc_ObjId( x )])

static inline void FSETPRED(Abc_Obj_t *pObj, Abc_Obj_t *pPred) {
  assert(!Abc_ObjIsLatch(pObj)); // must preserve field to maintain init state linkage
  FDATA(pObj)->pred = pPred;
}
static inline Abc_Obj_t * FGETPRED(Abc_Obj_t *pObj) {
  return FDATA(pObj)->pred;
}


typedef struct MinRegMan_t_ {
 
  // problem description:
  int         maxDelay;
  bool        fComputeInitState, fGuaranteeInitState;
  int         nNodes, nLatches;
  bool        fForwardOnly, fBackwardOnly;
  bool        fConservTimingOnly;
  int         nMaxIters;
  bool        fVerbose;
  Abc_Ntk_t  *pNtk;

  int         nPreRefine;

  // problem state
  bool        fIsForward;
  bool        fSinkDistTerminate;
  int         nExactConstraints, nConservConstraints;
  int         fSolutionIsDc;
  int         constraintMask;
  int         iteration, subIteration;
  
  // problem data
  Vec_Int_t   *vSinkDistHist;
  Flow_Data_t *pDataArray;
  Vec_Ptr_t   *vTimeEdges;
  Vec_Ptr_t   *vExactNodes;
  Abc_Ntk_t   *pInitNtk;
  Vec_Ptr_t   *vNodes; // re-useable struct

} MinRegMan_t ;

#define vprintf if (pManMR->fVerbose) printf 

/*=== fretMain.c ==========================================================*/
 
extern MinRegMan_t *pManMR;

Abc_Ntk_t *    Abc_FlowRetime_MinReg( Abc_Ntk_t * pNtk, int fVerbose, int fComputeInitState,
                                      int fForward, int fBackward, int nMaxIters,
                                      int maxDelay, int fFastButConservative);

void print_node(Abc_Obj_t *pObj);

void Abc_ObjBetterTransferFanout( Abc_Obj_t * pFrom, Abc_Obj_t * pTo, int compl );

int  Abc_FlowRetime_PushFlows( Abc_Ntk_t * pNtk, bool fVerbose );
bool Abc_FlowRetime_IsAcrossCut( Abc_Obj_t *pCur, Abc_Obj_t *pNext );
void Abc_FlowRetime_ClearFlows( bool fClearAll );

/*=== fretFlow.c ==========================================================*/

int  dfsplain_e( Abc_Obj_t *pObj, Abc_Obj_t *pPred );
int  dfsplain_r( Abc_Obj_t *pObj, Abc_Obj_t *pPred );

void dfsfast_preorder( Abc_Ntk_t *pNtk );
int  dfsfast_e( Abc_Obj_t *pObj, Abc_Obj_t *pPred );
int  dfsfast_r( Abc_Obj_t *pObj, Abc_Obj_t *pPred );

/*=== fretInit.c ==========================================================*/

void Abc_FlowRetime_PrintInitStateInfo( Abc_Ntk_t * pNtk );

void Abc_FlowRetime_InitState( Abc_Ntk_t * pNtk );

void Abc_FlowRetime_UpdateForwardInit( Abc_Ntk_t * pNtk );
void Abc_FlowRetime_UpdateBackwardInit( Abc_Ntk_t * pNtk );

void Abc_FlowRetime_SetupBackwardInit( Abc_Ntk_t * pNtk );
int  Abc_FlowRetime_SolveBackwardInit( Abc_Ntk_t * pNtk );

void Abc_FlowRetime_ConstrainInit(  );

/*=== fretTime.c ==========================================================*/

void Abc_FlowRetime_InitTiming( Abc_Ntk_t *pNtk );
void Abc_FlowRetime_FreeTiming( Abc_Ntk_t *pNtk );

bool Abc_FlowRetime_RefineConstraints( );

void Abc_FlowRetime_ConstrainConserv( Abc_Ntk_t * pNtk );
void Abc_FlowRetime_ConstrainExact( Abc_Obj_t * pObj );
void Abc_FlowRetime_ConstrainExactAll( Abc_Ntk_t * pNtk );

#endif
