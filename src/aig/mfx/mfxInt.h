/**CFile****************************************************************

  FileName    [mfxInt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [The good old minimization with complete don't-cares.]

  Synopsis    [Internal declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: mfxInt.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __MFX_INT_H__
#define __MFX_INT_H__

#ifdef __cplusplus
extern "C" {
#endif

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "nwk.h"
#include "mfx.h"
#include "aig.h"
#include "cnf.h"
#include "satSolver.h"
#include "satStore.h"
#include "bdc.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

#define MFX_FANIN_MAX   12

typedef struct Mfx_Man_t_ Mfx_Man_t;
struct Mfx_Man_t_
{
    // input data
    Mfx_Par_t *         pPars;
    Nwk_Man_t *         pNtk;
    Aig_Man_t *         pCare;
    Vec_Ptr_t *         vSuppsInv;
    int                 nFaninMax;
    // intermeditate data for the node
    Vec_Ptr_t *         vRoots;    // the roots of the window
    Vec_Ptr_t *         vSupp;     // the support of the window
    Vec_Ptr_t *         vNodes;    // the internal nodes of the window
    Vec_Ptr_t *         vDivs;     // the divisors of the node
    Vec_Int_t *         vDivLits;  // the SAT literals of divisor nodes
    Vec_Int_t *         vProjVars; // the projection variables
    // intermediate simulation data
    Vec_Ptr_t *         vDivCexes; // the counter-example for dividors
    int                 nDivWords; // the number of words
    int                 nCexes;    // the numbe rof current counter-examples
    int                 nSatCalls; 
    int                 nSatCexes;
    // used for bidecomposition
    Vec_Int_t *         vTruth;
    Bdc_Man_t *         pManDec;
    int                 nNodesDec;
    int                 nNodesGained;
    int                 nNodesGainedLevel;
    // solving data
    Aig_Man_t *         pAigWin;   // window AIG with constraints
    Cnf_Dat_t *         pCnf;      // the CNF for the window
    sat_solver *        pSat;      // the SAT solver used 
    Int_Man_t *         pMan;      // interpolation manager;
    Vec_Int_t *         vMem;      // memory for intermediate SOPs
    Vec_Vec_t *         vLevels;   // levelized structure for updating
    Vec_Ptr_t *         vFanins;   // the new set of fanins
    int                 nTotConfLim; // total conflict limit
    int                 nTotConfLevel; // total conflicts on this level
    // switching activity
    Vec_Int_t *         vProbs; 
    // the result of solving
    int                 nFanins;   // the number of fanins
    int                 nWords;    // the number of words
    int                 nCares;    // the number of care minterms
    unsigned            uCare[(MFX_FANIN_MAX<=5)?1:1<<(MFX_FANIN_MAX-5)];  // the computed care-set
    // performance statistics
    int                 nNodesTried;
    int                 nNodesResub;
    int                 nMintsCare;
    int                 nMintsTotal;
    int                 nNodesBad;
    int                 nTotalDivs;
    int                 nTimeOuts;
    int                 nTimeOutsLevel;
    int                 nDcMints;
    double              dTotalRatios;
    // node/edge stats
    int                 nTotalNodesBeg;
    int                 nTotalNodesEnd;
    int                 nTotalEdgesBeg;
    int                 nTotalEdgesEnd;
    // statistics
    int                 timeWin;
    int                 timeDiv;
    int                 timeAig;
    int                 timeCnf;
    int                 timeSat;
    int                 timeInt;
    int                 timeTotal;
};

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== mfxDiv.c ==========================================================*/
extern Vec_Ptr_t *      Mfx_ComputeDivisors( Mfx_Man_t * p, Nwk_Obj_t * pNode, float tArrivalMax );
/*=== mfxInter.c ==========================================================*/
extern sat_solver *     Mfx_CreateSolverResub( Mfx_Man_t * p, int * pCands, int nCands, int fInvert );
extern Hop_Obj_t *      Mfx_Interplate( Mfx_Man_t * p, int * pCands, int nCands );
extern int              Mfx_InterplateEval( Mfx_Man_t * p, int * pCands, int nCands );
/*=== mfxMan.c ==========================================================*/
extern Mfx_Man_t *      Mfx_ManAlloc( Mfx_Par_t * pPars );
extern void             Mfx_ManStop( Mfx_Man_t * p );
extern void             Mfx_ManClean( Mfx_Man_t * p );
/*=== mfxResub.c ==========================================================*/
extern void             Mfx_PrintResubStats( Mfx_Man_t * p );
extern int              Mfx_EdgePower( Mfx_Man_t * p, Nwk_Obj_t * pNode );
extern int              Mfx_EdgeSwapEval( Mfx_Man_t * p, Nwk_Obj_t * pNode );
extern int              Mfx_ResubNode( Mfx_Man_t * p, Nwk_Obj_t * pNode );
extern int              Mfx_ResubNode2( Mfx_Man_t * p, Nwk_Obj_t * pNode );
/*=== mfxSat.c ==========================================================*/
extern int              Mfx_SolveSat( Mfx_Man_t * p, Nwk_Obj_t * pNode );
/*=== mfxStrash.c ==========================================================*/
extern Aig_Man_t *      Mfx_ConstructAig( Mfx_Man_t * p, Nwk_Obj_t * pNode );
extern double           Mfx_ConstraintRatio( Mfx_Man_t * p, Nwk_Obj_t * pNode );
/*=== mfxWin.c ==========================================================*/
extern Vec_Ptr_t *      Mfx_ComputeRoots( Nwk_Obj_t * pNode, int nWinTfoMax, int nFanoutLimit );


#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

