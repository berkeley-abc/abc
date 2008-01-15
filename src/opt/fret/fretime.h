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

#define IGNORE_TIMING
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

typedef struct Untimed_Flow_Data_t_ {
  unsigned int mark : 8;

  union {
    Abc_Obj_t   *pred;
    /* unsigned int var; */
    Abc_Obj_t   *pInitObj;
  };

  unsigned int e_dist : 16;
  unsigned int r_dist : 16;
} Untimed_Flow_Data_t;

typedef struct Timed_Flow_Data_t_ {
  unsigned int mark : 8;

  union {
    Abc_Obj_t   *pred;
    Vec_Ptr_t   *vTimeInEdges;
    /* unsigned int var; */
    Abc_Obj_t   *pInitObj;
  };

  unsigned int e_dist : 16;
  unsigned int r_dist : 16;

  Vec_Ptr_t    vTimeEdges;

} Timed_Flow_Data_t;

#if defined(IGNORE_TIMING)
typedef Untimed_Flow_Data_t Flow_Data_t;
#else
typedef Timed_Flow_Data_t Flow_Data_t;
#endif

// useful macros for manipulating Flow_Data structure...
#define FDATA( x )     ((Flow_Data_t *)Abc_ObjCopy(x))
#define FSET( x, y )   ((Flow_Data_t *)Abc_ObjCopy(x))->mark |= y
#define FUNSET( x, y ) ((Flow_Data_t *)Abc_ObjCopy(x))->mark &= ~y
#define FTEST( x, y )  (((Flow_Data_t *)Abc_ObjCopy(x))->mark & y)
#define FTIMEEDGES( x )  &(((Timed_Flow_Data_t *)Abc_ObjCopy(x))->vTimeEdges)

static inline void FSETPRED(Abc_Obj_t *pObj, Abc_Obj_t *pPred) {
  assert(!Abc_ObjIsLatch(pObj)); // must preserve field to maintain init state linkage
  FDATA(pObj)->pred = pPred;
}
static inline Abc_Obj_t * FGETPRED(Abc_Obj_t *pObj) {
  return FDATA(pObj)->pred;
}

/*=== fretMain.c ==========================================================*/

Abc_Ntk_t *    Abc_FlowRetime_MinReg( Abc_Ntk_t * pNtk, int fVerbose, int fComputeInitState,
                                      int fForward, int fBackward, int nMaxIters,
                                      int maxDelay);

void print_node(Abc_Obj_t *pObj);

void Abc_ObjBetterTransferFanout( Abc_Obj_t * pFrom, Abc_Obj_t * pTo, int compl );

extern int         fIsForward;
extern int         fSinkDistTerminate;
extern Vec_Int_t  *vSinkDistHist;
extern int         maxDelayCon;
extern int         fComputeInitState;

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
void Abc_FlowRetime_SolveBackwardInit( Abc_Ntk_t * pNtk );

extern Abc_Ntk_t *pInitNtk;
extern int        fSolutionIsDc;

#endif
