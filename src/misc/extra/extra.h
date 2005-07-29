/**CFile****************************************************************

  FileName    [extra.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [extra]

  Synopsis    [Various reusable software utilities.]

  Description [This library contains a number of operators and 
  traversal routines developed to extend the functionality of 
  CUDD v.2.3.x, by Fabio Somenzi (http://vlsi.colorado.edu/~fabio/)
  To compile your code with the library, #include "extra.h" 
  in your source files and link your project to CUDD and this 
  library. Use the library at your own risk and with caution. 
  Note that debugging of some operators still continues.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: extra.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef __EXTRA_H__
#define __EXTRA_H__

#ifdef _WIN32
#define inline __inline // compatible with MS VS 6.0
#endif

/*---------------------------------------------------------------------------*/
/* Nested includes                                                           */
/*---------------------------------------------------------------------------*/

#include <string.h>
#include <time.h>
#include "util.h"
#include "st.h"
#include "cuddInt.h"

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Stucture declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/* constants of the manager */
#define     b0     Cudd_Not((dd)->one)
#define     b1              (dd)->one
#define     z0              (dd)->zero
#define     z1              (dd)->one
#define     a0              (dd)->zero
#define     a1              (dd)->one

// hash key macros
#define hashKey1(a,TSIZE) \
((unsigned)(a) % TSIZE)

#define hashKey2(a,b,TSIZE) \
(((unsigned)(a) + (unsigned)(b) * DD_P1) % TSIZE)

#define hashKey3(a,b,c,TSIZE) \
(((((unsigned)(a) + (unsigned)(b)) * DD_P1 + (unsigned)(c)) * DD_P2 ) % TSIZE)

#define hashKey4(a,b,c,d,TSIZE) \
((((((unsigned)(a) + (unsigned)(b)) * DD_P1 + (unsigned)(c)) * DD_P2 + \
   (unsigned)(d)) * DD_P3) % TSIZE)

#define hashKey5(a,b,c,d,e,TSIZE) \
(((((((unsigned)(a) + (unsigned)(b)) * DD_P1 + (unsigned)(c)) * DD_P2 + \
   (unsigned)(d)) * DD_P3 + (unsigned)(e)) * DD_P1) % TSIZE)

/*===========================================================================*/
/*     Various Utilities                                                     */
/*===========================================================================*/

/*=== extraUtilBdd.c ========================================================*/
extern DdNode *     Extra_TransferPermute( DdManager * ddSource, DdManager * ddDestination, DdNode * f, int * Permute );
extern DdNode *     Extra_TransferLevelByLevel( DdManager * ddSource, DdManager * ddDestination, DdNode * f );
extern DdNode *     Extra_bddRemapUp( DdManager * dd, DdNode * bF );
extern DdNode *     Extra_bddMove( DdManager * dd, DdNode * bF, int fShiftUp );
extern DdNode *     extraBddMove( DdManager * dd, DdNode * bF, DdNode * bFlag );
extern void         Extra_StopManager( DdManager * dd );
extern void         Extra_bddPrint( DdManager * dd, DdNode * F );
extern void         extraDecomposeCover( DdManager* dd, DdNode*  zC, DdNode** zC0, DdNode** zC1, DdNode** zC2 );
extern int          Extra_bddSuppSize( DdManager * dd, DdNode * bSupp );
extern int          Extra_bddSuppContainVar( DdManager * dd, DdNode * bS, DdNode * bVar );
extern int          Extra_bddSuppOverlapping( DdManager * dd, DdNode * S1, DdNode * S2 );
extern int          Extra_bddSuppDifferentVars( DdManager * dd, DdNode * S1, DdNode * S2, int DiffMax );
extern int          Extra_bddSuppCheckContainment( DdManager * dd, DdNode * bL, DdNode * bH, DdNode ** bLarge, DdNode ** bSmall );
extern int *        Extra_SupportArray( DdManager * dd, DdNode * F, int * support );
extern int *        Extra_VectorSupportArray( DdManager * dd, DdNode ** F, int n, int * support );
extern DdNode *     Extra_bddFindOneCube( DdManager * dd, DdNode * bF );
extern DdNode *     Extra_bddGetOneCube( DdManager * dd, DdNode * bFunc );

/*=== extraUtilFile.c ========================================================*/

extern char *       Extra_FileGetSimilarName( char * pFileNameWrong, char * pS1, char * pS2, char * pS3, char * pS4, char * pS5 );
extern int          Extra_FileNameCheckExtension( char * FileName, char * Extension );
extern char *       Extra_FileNameAppend( char * pBase, char * pSuffix );
extern char *       Extra_FileNameGeneric( char * FileName );
extern int          Extra_FileSize( char * pFileName );
extern char *       Extra_FileRead( FILE * pFile );
extern char *       Extra_TimeStamp();
extern char *       Extra_StringAppend( char * pStrGiven, char * pStrAdd );
extern unsigned     Extra_ReadBinary( char * Buffer );
extern void         Extra_PrintBinary( FILE * pFile, unsigned Sign[], int nBits );
extern void         Extra_PrintSymbols( FILE * pFile, char Char, int nTimes, int fPrintNewLine );

/*=== extraUtilReader.c ========================================================*/

typedef struct Extra_FileReader_t_ Extra_FileReader_t;
extern Extra_FileReader_t * Extra_FileReaderAlloc( char * pFileName, 
    char * pCharsComment, char * pCharsStop, char * pCharsClean );
extern void         Extra_FileReaderFree( Extra_FileReader_t * p );
extern char *       Extra_FileReaderGetFileName( Extra_FileReader_t * p );
extern int          Extra_FileReaderGetFileSize( Extra_FileReader_t * p );
extern int          Extra_FileReaderGetCurPosition( Extra_FileReader_t * p );
extern void *       Extra_FileReaderGetTokens( Extra_FileReader_t * p );
extern int          Extra_FileReaderGetLineNumber( Extra_FileReader_t * p, int iToken );

/*=== extraUtilMemory.c ========================================================*/

typedef struct Extra_MmFixed_t_    Extra_MmFixed_t;    
typedef struct Extra_MmFlex_t_     Extra_MmFlex_t;     
typedef struct Extra_MmStep_t_     Extra_MmStep_t;     

// fixed-size-block memory manager
extern Extra_MmFixed_t *  Extra_MmFixedStart( int nEntrySize );
extern void        Extra_MmFixedStop( Extra_MmFixed_t * p, int fVerbose );
extern char *      Extra_MmFixedEntryFetch( Extra_MmFixed_t * p );
extern void        Extra_MmFixedEntryRecycle( Extra_MmFixed_t * p, char * pEntry );
extern void        Extra_MmFixedRestart( Extra_MmFixed_t * p );
extern int         Extra_MmFixedReadMemUsage( Extra_MmFixed_t * p );
// flexible-size-block memory manager
extern Extra_MmFlex_t * Extra_MmFlexStart();
extern void        Extra_MmFlexStop( Extra_MmFlex_t * p, int fVerbose );
extern char *      Extra_MmFlexEntryFetch( Extra_MmFlex_t * p, int nBytes );
extern int         Extra_MmFlexReadMemUsage( Extra_MmFlex_t * p );
// hierarchical memory manager
extern Extra_MmStep_t * Extra_MmStepStart( int nSteps );
extern void        Extra_MmStepStop( Extra_MmStep_t * p, int fVerbose );
extern char *      Extra_MmStepEntryFetch( Extra_MmStep_t * p, int nBytes );
extern void        Extra_MmStepEntryRecycle( Extra_MmStep_t * p, char * pEntry, int nBytes );
extern int         Extra_MmStepReadMemUsage( Extra_MmStep_t * p );

/*=== extraUtilMisc.c ========================================================*/

/* finds the smallest integer larger of equal than the logarithm. */
extern int         Extra_Base2Log( unsigned Num );
extern int         Extra_Base2LogDouble( double Num );
extern int         Extra_Base10Log( unsigned Num );
/* returns the power of two as a double */
extern double      Extra_Power2( int Num );
extern int         Extra_Power3( int Num );
/* the number of combinations of k elements out of n */
extern int         Extra_NumCombinations( int k, int n  );
extern int *       Extra_DeriveRadixCode( int Number, int Radix, int nDigits );
/* the factorial of number */
extern int         Extra_Factorial( int n );
/* the permutation of the given number of elements */
extern char **     Extra_Permutations( int n );
extern unsigned int Cudd_PrimeCopy( unsigned int  p );

/*=== extraUtilProgress.c ================================================================*/

typedef struct ProgressBarStruct ProgressBar;

extern ProgressBar * Extra_ProgressBarStart( FILE * pFile, int nItemsTotal );
extern void        Extra_ProgressBarStop( ProgressBar * p );
extern void        Extra_ProgressBarUpdate_int( ProgressBar * p, int nItemsCur, char * pString );

static inline void Extra_ProgressBarUpdate( ProgressBar * p, int nItemsCur, char * pString ) 
{  if ( nItemsCur < *((int*)p) ) return; Extra_ProgressBarUpdate_int(p, nItemsCur, pString); }

/*=== extraUtilIntVec.c ================================================================*/

typedef struct Extra_IntVec_t_    Extra_IntVec_t;
extern Extra_IntVec_t * Extra_IntVecAlloc( int nCap );
extern Extra_IntVec_t * Extra_IntVecAllocArray( int * pArray, int nSize );
extern Extra_IntVec_t * Extra_IntVecAllocArrayCopy( int * pArray, int nSize );
extern Extra_IntVec_t * Extra_IntVecDup( Extra_IntVec_t * pVec );
extern Extra_IntVec_t * Extra_IntVecDupArray( Extra_IntVec_t * pVec );
extern void        Extra_IntVecFree( Extra_IntVec_t * p );
extern void        Extra_IntVecFill( Extra_IntVec_t * p, int nSize, int Entry );
extern int *       Extra_IntVecReleaseArray( Extra_IntVec_t * p );
extern int *       Extra_IntVecReadArray( Extra_IntVec_t * p );
extern int         Extra_IntVecReadSize( Extra_IntVec_t * p );
extern int         Extra_IntVecReadEntry( Extra_IntVec_t * p, int i );
extern int         Extra_IntVecReadEntryLast( Extra_IntVec_t * p );
extern void        Extra_IntVecWriteEntry( Extra_IntVec_t * p, int i, int Entry );
extern void        Extra_IntVecGrow( Extra_IntVec_t * p, int nCapMin );
extern void        Extra_IntVecShrink( Extra_IntVec_t * p, int nSizeNew );
extern void        Extra_IntVecClear( Extra_IntVec_t * p );
extern void        Extra_IntVecPush( Extra_IntVec_t * p, int Entry );
extern int         Extra_IntVecPop( Extra_IntVec_t * p );
extern void        Extra_IntVecSort( Extra_IntVec_t * p );

/**AutomaticEnd***************************************************************/

#endif /* __EXTRA_H__ */
