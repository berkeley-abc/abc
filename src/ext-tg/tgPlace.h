#ifndef ABC__ext_tg__tgPlace_h
#define ABC__ext_tg__tgPlace_h

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

    int Tg_Epoch(void);
    int Tg_InFlight(void);
    /* Read-only diagnostic restart export. Never used to accept/revert an edit. */

    int Tg_ManHasPlacement(Abc_Ntk_t *pNtk);

    void Tg_RegisterPlacementCommands(Abc_Frame_t *pAbc);

    /* Bracket mapped-cell strashing so each resulting AIG node inherits the
     * center of the mapped cell that created it. */

    int Tg_ManBeginPass(Abc_Ntk_t *pNtk);
    int Tg_ManEndPass(Abc_Ntk_t *pNtk);
    int Tg_ManIsPassActive(Abc_Ntk_t *pNtk);
    int Tg_ManBeginEdit(Abc_Ntk_t *pNtk);

    int Tg_ManReadObjectPosition(Abc_Ntk_t *pNtk, Abc_Obj_t *pObj, double *pX, double *pY);
    int Tg_ManReadObjectGeometry(Abc_Ntk_t *pNtk, Abc_Obj_t *pObj, double *pX, double *pY,
                                 double *pWidth, double *pDensityHalfX, double *pDensityHalfY,
                                 double *pDensityScale);
    int Tg_ManStageObjectRemoval(Abc_Ntk_t *pNtk, Abc_Obj_t *pObj);
    int Tg_ManStageObjectRefresh(Abc_Ntk_t *pNtk, Abc_Obj_t *pObj);
    int Tg_ManWriteObjectPosition(Abc_Ntk_t *pNtk, Abc_Obj_t *pObj, double X, double Y);
    int Tg_ManFinishLocalEdit(Abc_Ntk_t *pNtk, double HpwlReduction);
    int Tg_ManFinishGlobalEdit(Abc_Ntk_t *pNtk);
    int Tg_ManFinishEdit(Abc_Ntk_t *pNtk);
    int Tg_ManReadCanvas(Abc_Ntk_t *pNtk, double *pWidth, double *pHeight, int *pBins,
                         double *pBinSizeX, double *pBinSizeY);
    int Tg_ManReadDensityBin(Abc_Ntk_t *pNtk, int BinX, int BinY, double *pCellArea,
                             double *pTargetArea);
    int Tg_ManReadMetrics(Abc_Ntk_t *pNtk, double *pHpwl, double *pOverflow, double *pHpwlScale,
                          double *pCellArea);
    void Tg_ManClearPlacement();
    void Tg_ManShutdown();

#ifdef __cplusplus
}
#endif

ABC_NAMESPACE_HEADER_END

#endif
