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
    int              nConstrs;      // treat the last nConstrs POs as seq constraints
    int              nMaxLevs;      // the max number of levels of nodes to consider
    int              nBTLimit;      // conflict limit at a node
    int              fPolarFlip;    // uses polarity adjustment
    int              fLatchCorr;    // perform register correspondence
    int              fVerbose;      // verbose stats
    // internal parameters
    int              nIters;        // the number of iterations performed
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== sswCore.c ==========================================================*/
extern void          Ssw_ManSetDefaultParams( Ssw_Pars_t * p );
extern Aig_Man_t *   Ssw_SignalCorrespondence( Aig_Man_t * p, Ssw_Pars_t * pPars );


#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

