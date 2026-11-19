#ifndef ABC__ext_agr__agrPlace_h
#define ABC__ext_agr__agrPlace_h

#include "base/abc/abc.h"

ABC_NAMESPACE_HEADER_START

typedef struct Abc_Frame_t_ Abc_Frame_t;

#ifdef __cplusplus
extern "C"
{
#endif

    /*
     * Placement belongs to the current network and normally uses object IDs for
     * lookup.  Structural transforms must bracket accepted graph edits with
     * BeginEdit/FinishEdit and assign every new node a position through the
     * object-based interface.  A physical optimization command additionally owns
     * a BeginPass/EndPass session, which validates the structural fingerprint once
     * and audits accumulated HPWL when the command finishes.
     */

    int Agr_Epoch(void);
    int Agr_InFlight(void);
    /* Read-only diagnostic restart export. Never used to accept/revert an edit. */

    int Agr_ManHasPlacement(Abc_Ntk_t *pNtk);

    void Agr_RegisterPlacementCommands(Abc_Frame_t *pAbc);

    /* Bracket mapped-cell strashing so each resulting AIG node inherits the
     * center of the mapped cell that created it. */

    int Agr_ManBeginPass(Abc_Ntk_t *pNtk);
    int Agr_ManEndPass(Abc_Ntk_t *pNtk);
    int Agr_ManIsPassActive(Abc_Ntk_t *pNtk);
    int Agr_ManBeginEdit(Abc_Ntk_t *pNtk);

    int Agr_ManReadObjectPosition(Abc_Ntk_t *pNtk, Abc_Obj_t *pObj, double *pX, double *pY);
    int Agr_ManReadObjectGeometry(Abc_Ntk_t *pNtk, Abc_Obj_t *pObj, double *pX, double *pY,
                                 double *pWidth, double *pDensityHalfX, double *pDensityHalfY,
                                 double *pDensityScale);
    int Agr_ManStageObjectRemoval(Abc_Ntk_t *pNtk, Abc_Obj_t *pObj);
    int Agr_ManStageObjectRefresh(Abc_Ntk_t *pNtk, Abc_Obj_t *pObj);
    int Agr_ManWriteObjectPosition(Abc_Ntk_t *pNtk, Abc_Obj_t *pObj, double X, double Y);
    int Agr_ManFinishLocalEdit(Abc_Ntk_t *pNtk, double HpwlReduction);
    int Agr_ManFinishGlobalEdit(Abc_Ntk_t *pNtk);
    int Agr_ManFinishEdit(Abc_Ntk_t *pNtk);
    int Agr_ManReadCanvas(Abc_Ntk_t *pNtk, double *pWidth, double *pHeight, int *pBins,
                         double *pBinSizeX, double *pBinSizeY);
    int Agr_ManReadDensityBin(Abc_Ntk_t *pNtk, int BinX, int BinY, double *pCellArea,
                             double *pTargetArea);
    int Agr_ManReadMetrics(Abc_Ntk_t *pNtk, double *pHpwl, double *pOverflow, double *pHpwlScale,
                          double *pCellArea);
    void Agr_ManClearPlacement();
    void Agr_ManShutdown();

#ifdef __cplusplus
}
#endif

ABC_NAMESPACE_HEADER_END

#endif
