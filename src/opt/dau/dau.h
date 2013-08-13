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

#define DAU_MAX_VAR    12 // should be 6 or more
#define DAU_MAX_STR  1000
#define DAU_MAX_WORD  (1<<(DAU_MAX_VAR-6))

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

// network types
typedef enum { 
    DAU_DSD_NONE = 0,      // 0:  unknown
    DAU_DSD_CONST0,        // 1:  constant
    DAU_DSD_VAR,           // 2:  variable
    DAU_DSD_AND,           // 3:  AND
    DAU_DSD_XOR,           // 4:  XOR
    DAU_DSD_MUX,           // 5:  MUX
    DAU_DSD_PRIME          // 6:  PRIME
} Dau_DsdType_t;

typedef struct Dss_Man_t_ Dss_Man_t;

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

static inline int Dau_DsdIsConst( char * p )  { return (p[0] == '0' || p[0] == '1') && p[1] == 0;    }
static inline int Dau_DsdIsConst0( char * p ) { return  p[0] == '0' && p[1] == 0;                    }
static inline int Dau_DsdIsConst1( char * p ) { return  p[0] == '1' && p[1] == 0;                    }
static inline int Dau_DsdIsVar( char * p )    { if ( *p == '!' ) p++; return *p >= 'a' && *p <= 'z'; }
static inline int Dau_DsdReadVar( char * p )  { if ( *p == '!' ) p++; return *p - 'a';               }

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== dauCanon.c ==========================================================*/
extern unsigned      Abc_TtCanonicize( word * pTruth, int nVars, char * pCanonPerm );
/*=== dauDsd.c  ==========================================================*/
extern int *         Dau_DsdComputeMatches( char * p );
extern int           Dau_DsdDecompose( word * pTruth, int nVarsInit, int fSplitPrime, int fWriteTruth, char * pRes );
extern void          Dau_DsdPrintFromTruth( FILE * pFile, word * pTruth, int nVarsInit );
extern word *        Dau_DsdToTruth( char * p, int nVars );
extern word          Dau_Dsd6ToTruth( char * p );
extern void          Dau_DsdNormalize( char * p );
extern int           Dau_DsdCountAnds( char * pDsd );
extern void          Dau_DsdTruthCompose_rec( word * pFunc, word pFanins[DAU_MAX_VAR][DAU_MAX_WORD], word * pRes, int nVars, int nWordsR );
extern int           Dau_DsdCheck1Step( word * pTruth, int nVarsInit );

/*=== dauMerge.c  ==========================================================*/
extern void          Dau_DsdRemoveBraces( char * pDsd, int * pMatches );
extern char *        Dau_DsdMerge( char * pDsd0i, int * pPerm0, char * pDsd1i, int * pPerm1, int fCompl0, int fCompl1, int nVars );

/*=== dauTree.c  ==========================================================*/
extern Dss_Man_t *   Dss_ManAlloc( int nVars, int nNonDecLimit );
extern void          Dss_ManFree( Dss_Man_t * p );
extern int           Dss_ManMerge( Dss_Man_t * p, int * iDsd, int * nFans, int ** pFans, unsigned uSharedMask, int nKLutSize, unsigned char * pPerm, word * pTruth );
extern void          Dss_ManPrint( char * pFileName, Dss_Man_t * p );


ABC_NAMESPACE_HEADER_END



#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

