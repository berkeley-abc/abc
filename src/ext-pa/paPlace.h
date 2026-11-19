#ifndef ABC__ext_pa__paPlace_h
#define ABC__ext_pa__paPlace_h

#include "base/abc/abc.h"

ABC_NAMESPACE_HEADER_START

typedef struct Abc_Frame_t_ Abc_Frame_t;

#ifdef __cplusplus
extern "C" {
#endif

/*
 * Placement belongs to the current network and normally uses object IDs for
 * lookup.  Structural transforms must bracket accepted graph edits with
 * BeginEdit/FinishEdit and assign every new node a position through the
 * object-based interface.  A physical optimization command additionally owns
 * a BeginPass/EndPass session, which validates the structural fingerprint once
 * and audits accumulated HPWL when the command finishes.
 */
int Pa_ManHasPlacement( Abc_Ntk_t * pNtk );
void Pa_RegisterSynthesisCommands( Abc_Frame_t * pAbc );
void Pa_RegisterPlacementCommands( Abc_Frame_t * pAbc );
int Pa_ManHasInheritedPlacement( Abc_Ntk_t * pNtk );
/* Bracket mapped-cell strashing so each resulting AIG node inherits the
 * center of the mapped cell that created it. */
int Pa_ManBeginMappedUnmap( Abc_Ntk_t * pNtk );
void Pa_ManCaptureUnmappedCell( Abc_Obj_t * pCell );
int Pa_ManFinishMappedUnmap( Abc_Ntk_t * pAig );
void Pa_ManAbortMappedUnmap();
int Pa_ManReadPosition( Abc_Ntk_t * pNtk, int ObjId, float * pX, float * pY );
int Pa_ManBeginPass( Abc_Ntk_t * pNtk );
int Pa_ManEndPass( Abc_Ntk_t * pNtk );
int Pa_ManIsPassActive( Abc_Ntk_t * pNtk );
int Pa_ManBeginEdit( Abc_Ntk_t * pNtk );
int Pa_ManIsEditing( Abc_Ntk_t * pNtk );
int Pa_ManReadObjectPosition( Abc_Ntk_t * pNtk, Abc_Obj_t * pObj, double * pX, double * pY );
int Pa_ManReadObjectGeometry( Abc_Ntk_t * pNtk, Abc_Obj_t * pObj,
    double * pX, double * pY, double * pWidth, double * pDensityHalfX,
    double * pDensityHalfY, double * pDensityScale );
int Pa_ManStageObjectRemoval( Abc_Ntk_t * pNtk, Abc_Obj_t * pObj );
int Pa_ManStageObjectRefresh( Abc_Ntk_t * pNtk, Abc_Obj_t * pObj );
int Pa_ManWriteObjectPosition( Abc_Ntk_t * pNtk, Abc_Obj_t * pObj, double X, double Y );
int Pa_ManFinishLocalEdit( Abc_Ntk_t * pNtk, double HpwlReduction );
int Pa_ManFinishGlobalEdit( Abc_Ntk_t * pNtk );
int Pa_ManFinishEdit( Abc_Ntk_t * pNtk );
int Pa_ManReadCanvas( Abc_Ntk_t * pNtk, double * pWidth, double * pHeight,
    int * pBins, double * pBinSizeX, double * pBinSizeY );
int Pa_ManReadDensityBin( Abc_Ntk_t * pNtk, int BinX, int BinY,
    double * pCellArea, double * pTargetArea );
int Pa_ManReadMetrics( Abc_Ntk_t * pNtk, double * pHpwl,
    double * pOverflow, double * pHpwlScale, double * pCellArea );
void Pa_ManClearPlacement();

#ifdef __cplusplus
}
#endif

ABC_NAMESPACE_HEADER_END

#endif
