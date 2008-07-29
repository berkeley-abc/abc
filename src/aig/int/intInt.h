/**CFile****************************************************************

  FileName    [intInt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Interpolation engine.]

  Synopsis    [Internal declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 24, 2008.]

  Revision    [$Id: intInt.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __INT_INT_H__
#define __INT_INT_H__

#ifdef __cplusplus
extern "C" {
#endif

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "saig.h"
#include "cnf.h"
#include "satSolver.h"
#include "satStore.h"
#include "int.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

// interpolation manager
typedef struct Inter_Man_t_ Inter_Man_t;
struct Inter_Man_t_
{
    // AIG manager
    Aig_Man_t *      pAig;         // the original AIG manager
    Aig_Man_t *      pAigTrans;    // the transformed original AIG manager
    Cnf_Dat_t *      pCnfAig;      // CNF for the original manager
    // interpolant
    Aig_Man_t *      pInter;       // the current interpolant
    Cnf_Dat_t *      pCnfInter;    // CNF for the current interplant
    // timeframes
    Aig_Man_t *      pFrames;      // the timeframes      
    Cnf_Dat_t *      pCnfFrames;   // CNF for the timeframes 
    // other data
    Vec_Int_t *      vVarsAB;      // the variables participating in 
    // temporary place for the new interpolant
    Aig_Man_t *      pInterNew;
    Vec_Ptr_t *      vInters;
    // parameters
    int              nFrames;      // the number of timeframes
    int              nConfCur;     // the current number of conflicts
    int              nConfLimit;   // the limit on the number of conflicts
    int              fVerbose;     // the verbosiness flag
    // runtime
    int              timeRwr;
    int              timeCnf;
    int              timeSat;
    int              timeInt;
    int              timeEqu;
    int              timeOther;
    int              timeTotal;
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== intContain.c ==========================================================*/
extern int           Inter_ManCheckContainment( Aig_Man_t * pNew, Aig_Man_t * pOld );
extern int           Inter_ManCheckEquivalence( Aig_Man_t * pNew, Aig_Man_t * pOld );
extern int           Inter_ManCheckInductiveContainment( Aig_Man_t * pTrans, Aig_Man_t * pInter, int nSteps, int fBackward );

/*=== intDup.c ==========================================================*/
extern Aig_Man_t *   Inter_ManStartInitState( int nRegs );
extern Aig_Man_t *   Inter_ManStartDuplicated( Aig_Man_t * p );
extern Aig_Man_t *   Inter_ManStartOneOutput( Aig_Man_t * p, int fAddFirstPo );

/*=== intFrames.c ==========================================================*/
extern Aig_Man_t *   Inter_ManFramesInter( Aig_Man_t * pAig, int nFrames, int fAddRegOuts );

/*=== intMan.c ==========================================================*/
extern Inter_Man_t * Inter_ManCreate( Aig_Man_t * pAig, Inter_ManParams_t * pPars );
extern void          Inter_ManClean( Inter_Man_t * p );
extern void          Inter_ManStop( Inter_Man_t * p );

/*=== intM114.c ==========================================================*/
extern int           Inter_ManPerformOneStep( Inter_Man_t * p, int fUseBias, int fUseBackward );

/*=== intM114p.c ==========================================================*/
#ifdef ABC_USE_LIBRARIES
extern int           Inter_ManPerformOneStepM114p( Inter_Man_t * p, int fUsePudlak, int fUseOther );
#endif

/*=== intUtil.c ==========================================================*/
extern int           Inter_ManCheckInitialState( Aig_Man_t * p );
extern int           Inter_ManCheckAllStates( Aig_Man_t * p );

#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

