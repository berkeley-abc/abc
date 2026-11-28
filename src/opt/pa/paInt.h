/**CFile****************************************************************

  FileName    [paInt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Placement-aware synthesis.]

  Synopsis    [Internal declarations.]

  Author      [Anqi Lu]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 27, 2026.]

  Revision    [$Id: paInt.h,v 1.00 2026/11/27 00:00:00 anqilu Exp $]

***********************************************************************/

#ifndef ABC__opt__pa__paInt_h
#define ABC__opt__pa__paInt_h


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "base/abc/abc.h"
#include "bool/dec/dec.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_HEADER_START

// initial placement step in bin widths
#define PA_PLACE_STEP 0.28

// slots of the per-frame state; each source file owns one
enum { PA_STATE_PLACE, PA_STATE_EVAL, PA_STATE_RWR, PA_STATE_AGR, PA_STATE_NUM };

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

// optional root filter of the operators: fVisit returns whether a root is
// tried; fDone, if given, reports whether a candidate was found for it
typedef struct Pa_Filter_t_ Pa_Filter_t;
struct Pa_Filter_t_
{
    int            (* fVisit)( void * pData, Abc_Obj_t * pRoot );
    void           (* fDone)( void * pData, Abc_Obj_t * pRoot, int fFound );
    void *            pData;
};

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== paCommands.c ======================================================*/
extern void *        Pa_FrameState( int Slot, void * (*pAlloc)( void ), void (*pFree)( void * ) );
/*=== paPlace.cpp =======================================================*/
extern int           Pa_ManPlace( Abc_Ntk_t * pNtk, double Step );
extern int           Pa_ManHasPlacement( Abc_Ntk_t * pNtk );
extern int           Pa_ManHasInheritedPlacement( Abc_Ntk_t * pNtk );
extern int           Pa_ManBeginMappedUnmap( Abc_Ntk_t * pNtk );
extern void          Pa_ManCaptureUnmappedCell( Abc_Obj_t * pCell );
extern int           Pa_ManFinishMappedUnmap( Abc_Ntk_t * pAig );
extern void          Pa_ManAbortMappedUnmap( void );
extern int           Pa_ManBeginPass( Abc_Ntk_t * pNtk );
extern int           Pa_ManEndPass( Abc_Ntk_t * pNtk );
extern int           Pa_ManIsPassActive( Abc_Ntk_t * pNtk );
extern int           Pa_ManBeginEdit( Abc_Ntk_t * pNtk );
extern int           Pa_ManReadObjectPosition( Abc_Ntk_t * pNtk, Abc_Obj_t * pObj, double * pX, double * pY );
extern int           Pa_ManReadObjectGeometry( Abc_Ntk_t * pNtk, Abc_Obj_t * pObj, double * pX, double * pY, double * pWidth, double * pDensityHalfX, double * pDensityHalfY, double * pDensityScale );
extern int           Pa_ManStageObjectRemoval( Abc_Ntk_t * pNtk, Abc_Obj_t * pObj );
extern int           Pa_ManStageObjectRefresh( Abc_Ntk_t * pNtk, Abc_Obj_t * pObj );
extern int           Pa_ManWriteObjectPosition( Abc_Ntk_t * pNtk, Abc_Obj_t * pObj, double X, double Y );
extern int           Pa_ManFinishLocalEdit( Abc_Ntk_t * pNtk, double HpwlReduction );
extern int           Pa_ManFinishGlobalEdit( Abc_Ntk_t * pNtk );
extern int           Pa_ManFinishEdit( Abc_Ntk_t * pNtk );
extern int           Pa_ManReadCanvas( Abc_Ntk_t * pNtk, double * pWidth, double * pHeight, int * pBins, double * pBinSizeX, double * pBinSizeY );
extern int           Pa_ManReadDensityBin( Abc_Ntk_t * pNtk, int BinX, int BinY, double * pCellArea, double * pTargetArea );
extern int           Pa_ManReadMetrics( Abc_Ntk_t * pNtk, double * pHpwl, double * pOverflow, double * pHpwlScale, double * pCellArea );
extern void          Pa_ManClearPlacement( void );
/*=== paEvaluate.cpp ====================================================*/
extern void          Pa_ManSetTimingEvaluation( int fEnable );
extern void          Pa_ManSetExactTiming( int fEnable );
extern void          Pa_ManSetClusterEvaluation( int fEnable );
extern void          Pa_ManSetPhysicalAreaGuard( int fEnable );
extern void          Pa_ManSetCapacityRepair( int fEnable );
extern void          Pa_ManSetWireTolerance( int fEnable );
extern int           Pa_ManPrepareTimingPass( Abc_Ntk_t * pNtk );
extern int           Pa_ManEvaluateCandidate( Abc_Obj_t * pRoot, Dec_Graph_t * pGraph, int nNodesSaved, int LevelMax, int fRootComplement, int * pGain, double * pScore, double * pHpwlSaved, double * pHpwlAdded, double * pDensityDelta );
extern int           Pa_ManCommitCandidate( Abc_Obj_t * pRoot, Dec_Graph_t * pGraph, Vec_Ptr_t * vLeaves, int fUpdateLevel, int nGain );
/*=== paAig.cpp =========================================================*/
extern int           Pa_AigReplace( Abc_Aig_t * pMan, Abc_Obj_t * pOld, Abc_Obj_t * pNew, int fUpdateLevel );
/*=== paResub.c =========================================================*/
extern int           Pa_NtkResubstitute( Abc_Ntk_t * pNtk, Pa_Filter_t * pFilter, int fReassignIds, int fLazyPairs );
/*=== paRewrite.c =======================================================*/
extern int           Pa_NtkRewrite( Abc_Ntk_t * pNtk, Pa_Filter_t * pFilter, int fReassignIds );
/*=== paRefactor.c ======================================================*/
extern int           Pa_NtkRefactor( Abc_Ntk_t * pNtk, Pa_Filter_t * pFilter, int fReassignIds );
/*=== paStrash.c ========================================================*/
extern Abc_Ntk_t *   Pa_NtkStrash( Abc_Ntk_t * pNtk );
extern Abc_Obj_t *   Pa_GraphToNetwork( Abc_Ntk_t * pNtk, Dec_Graph_t * pGraph );

ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
