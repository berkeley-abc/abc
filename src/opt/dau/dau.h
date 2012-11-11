/**CFile****************************************************************

  FileName    [dau.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware unmapping.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: dau.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef ABC__DAU___h
#define ABC__DAU___h


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <time.h>
#include "misc/vec/vec.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_HEADER_START

#define DAU_MAX_VAR    16 // should be 6 or more
#define DAU_MAX_STR   256
#define DAU_MAX_WORD  (1<<(DAU_MAX_VAR-6))

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== dauCanon.c ==========================================================*/
extern unsigned      Abc_TtCanonicize( word * pTruth, int nVars, char * pCanonPerm );
/*=== dauDsd.c  ==========================================================*/
extern int           Dau_DsdDecompose( word * pTruth, int nVarsInit, int fSplitPrime, char * pRes );
extern word *        Dau_DsdToTruth( char * p, int nVars );
extern word          Dau_Dsd6ToTruth( char * p );
extern void          Dau_DsdNormalize( char * p );

/*=== dauMerge.c  ==========================================================*/
extern void          Dau_DsdRemoveBraces( char * pDsd, int * pMatches );
extern char *        Dau_DsdMerge( char * pDsd0i, int * pPerm0, char * pDsd1i, int * pPerm1, int fCompl0, int fCompl1 );

ABC_NAMESPACE_HEADER_END



#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

