/**CFile****************************************************************

  FileName    [ssw.h] 

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Inductive prover with constraints.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 1, 2008.]

  Revision    [$Id: ssw.h,v 1.00 2008/09/01 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __SSW_H__
#define __SSW_H__

#ifdef __cplusplus
extern "C" { 
#endif

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

// choicing parameters
typedef struct Ssw_Pars_t_ Ssw_Pars_t;
struct Ssw_Pars_t_
{
    int              nPartSize;     // size of the partition
    int              nOverSize;     // size of the overlap between partitions
    int              nFramesK;      // the induction depth
    int              nFramesAddSim; // the number of additional frames to simulate
    int              nConstrs;      // treat the last nConstrs POs as seq constraints
    int              nMaxLevs;      // the max number of levels of nodes to consider
    int              nBTLimit;      // conflict limit at a node
    int              nMinDomSize;   // min clock domain considered for optimization
    int              fPolarFlip;    // uses polarity adjustment
    int              fSkipCheck;    // do not run equivalence check for unaffected cones
    int              fLatchCorr;    // perform register correspondence
    int              fSemiFormal;   // enable semiformal filtering
    int              fVerbose;      // verbose stats
    // optimized latch correspondence
    int              fLatchCorrOpt; // perform register correspondence (optimized)
    int              nSatVarMax;    // max number of SAT vars before recycling SAT solver (optimized latch corr only)
    int              nRecycleCalls; // calls to perform before recycling SAT solver (optimized latch corr only)
    // internal parameters
    int              nIters;        // the number of iterations performed
};

// sequential counter-example
typedef struct Ssw_Cex_t_   Ssw_Cex_t;
struct Ssw_Cex_t_
{
    int              iPo;               // the zero-based number of PO, for which verification failed
    int              iFrame;            // the zero-based number of the time-frame, for which verificaiton failed
    int              nRegs;             // the number of registers in the miter 
    int              nPis;              // the number of primary inputs in the miter
    int              nBits;             // the number of words of bit data used
    unsigned         pData[0];          // the cex bit data (the number of bits: nRegs + (iFrame+1) * nPis)
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== sswCore.c ==========================================================*/
extern void          Ssw_ManSetDefaultParams( Ssw_Pars_t * p );
extern void          Ssw_ManSetDefaultParamsLcorr( Ssw_Pars_t * p );
extern Aig_Man_t *   Ssw_SignalCorrespondence( Aig_Man_t * pAig, Ssw_Pars_t * pPars );
extern Aig_Man_t *   Ssw_LatchCorrespondence( Aig_Man_t * pAig, Ssw_Pars_t * pPars );
/*=== sswPart.c ==========================================================*/
extern Aig_Man_t *   Ssw_SignalCorrespondencePart( Aig_Man_t * pAig, Ssw_Pars_t * pPars );
/*=== sswPairs.c ===================================================*/
extern int           Ssw_SecWithPairs( Aig_Man_t * pAig1, Aig_Man_t * pAig2, Vec_Int_t * vIds1, Vec_Int_t * vIds2, Ssw_Pars_t * pPars );
extern int           Ssw_SecGeneral( Aig_Man_t * pAig1, Aig_Man_t * pAig2, Ssw_Pars_t * pPars );
extern int           Ssw_SecGeneralMiter( Aig_Man_t * pMiter, Ssw_Pars_t * pPars );
/*=== sswSim.c ===================================================*/
extern Ssw_Cex_t *   Ssw_SmlAllocCounterExample( int nRegs, int nRealPis, int nFrames );
extern void          Ssw_SmlFreeCounterExample( Ssw_Cex_t * pCex );
extern int           Ssw_SmlRunCounterExample( Aig_Man_t * pAig, Ssw_Cex_t * p );
extern int           Ssw_SmlFindOutputCounterExample( Aig_Man_t * pAig, Ssw_Cex_t * p );
extern Ssw_Cex_t *   Ssw_SmlDupCounterExample( Ssw_Cex_t * p, int nRegsNew );

#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

