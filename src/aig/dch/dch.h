/**CFile****************************************************************

  FileName    [dch.h] 

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Choice computation for tech-mapping.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 29, 2008.]

  Revision    [$Id: dch.h,v 1.00 2008/07/29 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __DCH_H__
#define __DCH_H__

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
typedef struct Dch_Pars_t_ Dch_Pars_t;
struct Dch_Pars_t_
{
    int              nWords;        // the number of simulation words
    int              nBTLimit;      // conflict limit at a node
    int              nSatVarMax;    // the max number of SAT variables
    int              fSynthesis;    // set to 1 to perform synthesis
    int              fPolarFlip;    // uses polarity adjustment
    int              fSimulateTfo;  // uses simulatin of TFO classes
    int              fVerbose;      // verbose stats
    int              timeSynth;     // synthesis runtime
    int              nNodesAhead;   // the lookahead in terms of nodes
    int              nCallsRecycle; // calls to perform before recycling SAT solver
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== dchCore.c ==========================================================*/
extern void          Dch_ManSetDefaultParams( Dch_Pars_t * p );
extern Aig_Man_t *   Dch_ComputeChoices( Vec_Ptr_t * vAigs, Dch_Pars_t * pPars );


#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

