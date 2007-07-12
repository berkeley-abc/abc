/**CFile****************************************************************

  FileName    [dar.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: dar.h,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef __DAR_H__
#define __DAR_H__

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

typedef struct Dar_Par_t_            Dar_Par_t;

// the rewriting parameters
struct Dar_Par_t_  
{
    int              nCutsMax;       // the maximum number of cuts to try
    int              nSubgMax;       // the maximum number of subgraphs to try
    int              fUpdateLevel;   // update level 
    int              fUseZeros;      // performs zero-cost replacement
    int              fVerbose;       // enables verbose output
    int              fVeryVerbose;   // enables very verbose output
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                             ITERATORS                            ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== darCore.c ========================================================*/
extern void            Dar_ManDefaultParams( Dar_Par_t * pPars );
extern int             Dar_ManRewrite( Aig_Man_t * pAig, Dar_Par_t * pPars );
extern Aig_MmFixed_t * Dar_ManComputeCuts( Aig_Man_t * pAig );

#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

