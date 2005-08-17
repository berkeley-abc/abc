/**CFile****************************************************************

  FileName    [rwrExp.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting package.]

  Synopsis    [Computation of practically used NN-classes of 4-input cuts.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: rwrExp.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "rwr.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Abc_ManRwrExp_t_ Abc_ManRwrExp_t;
struct Abc_ManRwrExp_t_
{
    // internal lookups
    int                nFuncs;           // the number of four-var functions
    unsigned short *   puCanons;         // canonical forms
    int *              pnCounts;         // the counters of functions in each class
    int                nConsidered;      // the number of nodes considered
    int                nClasses;         // the number of NN classes
};

static Abc_ManRwrExp_t * s_pManRwrExp = NULL;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////


/**Function*************************************************************

  Synopsis    [Collects stats about 4-var functions appearing in netlists.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwt_ManExploreStart()
{
    Abc_ManRwrExp_t * p;
    unsigned uTruth;
    int i, k, nClasses;
    int clk = clock();

    p = ALLOC( Abc_ManRwrExp_t, 1 );
    memset( p, 0, sizeof(Abc_ManRwrExp_t) );
    // canonical forms
    p->nFuncs    = (1<<16);
    p->puCanons  = ALLOC( unsigned short, p->nFuncs );
    memset( p->puCanons, 0, sizeof(unsigned short) * p->nFuncs );
    // counters
    p->pnCounts  = ALLOC( int, p->nFuncs );
    memset( p->pnCounts, 0, sizeof(int) * p->nFuncs );

    // initialize the canonical forms
    nClasses = 1;
    for ( i = 1; i < p->nFuncs-1; i++ )
    {
        if ( p->puCanons[i] )
            continue;
        nClasses++;
        for ( k = 0; k < 32; k++ )
        {
            uTruth = Rwr_FunctionPhase( (unsigned)i, (unsigned)k );
            if ( p->puCanons[uTruth] == 0 )
                p->puCanons[uTruth] = (unsigned short)i;
            else
                assert( p->puCanons[uTruth] == (unsigned short)i );
        }
    }
    // set info for constant 1
    p->puCanons[p->nFuncs-1] = 0;
    printf( "The number of NN-canonical forms = %d.\n", nClasses );
    s_pManRwrExp = p;
}

/**Function*************************************************************

  Synopsis    [Collects stats about 4-var functions appearing in netlists.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwt_ManExploreCount( unsigned uTruth )
{
    assert( uTruth < (1<<16) );
    s_pManRwrExp->pnCounts[ s_pManRwrExp->puCanons[uTruth] ]++;    
}

/**Function*************************************************************

  Synopsis    [Collects stats about 4-var functions appearing in netlists.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwt_ManExplorePrint()
{
    FILE * pFile;
    int i, CountMax, CountWrite, nCuts, nClasses;
    int * pDistrib;
    int * pReprs;
    // find the max number of occurences
    nCuts = nClasses = 0;
    CountMax = 0;
    for ( i = 0; i < s_pManRwrExp->nFuncs; i++ )
    {
        if ( CountMax < s_pManRwrExp->pnCounts[i] )
            CountMax = s_pManRwrExp->pnCounts[i];
        nCuts += s_pManRwrExp->pnCounts[i];
        if ( s_pManRwrExp->pnCounts[i] > 0 )
            nClasses++;
    }
    printf( "Number of cuts considered       = %8d.\n", nCuts );
    printf( "Classes occurring at least once = %8d.\n", nClasses );
    // print the distribution of classes
    pDistrib = ALLOC( int, CountMax + 1 );
    pReprs   = ALLOC( int, CountMax + 1 );
    memset( pDistrib, 0, sizeof(int)*(CountMax + 1) );
    for ( i = 0; i < s_pManRwrExp->nFuncs; i++ )
    {
        pDistrib[ s_pManRwrExp->pnCounts[i] ]++;
        pReprs[ s_pManRwrExp->pnCounts[i] ] = i;
    }

    printf( "Occurence = %6d.  Num classes = %4d.  \n", 0, 2288-nClasses );
    for ( i = 1; i <= CountMax; i++ )
        if ( pDistrib[i] )
        {
            printf( "Occurence = %6d.  Num classes = %4d.  Repr = ", i, pDistrib[i] );
            Extra_PrintBinary( stdout, (unsigned*)&(pReprs[i]), 16 ); 
            printf( "\n" );
        }
    free( pDistrib );
    free( pReprs );
    // write into a file all classes above limit (5)
    CountWrite = 0;
    pFile = fopen( "nnclass_stats.txt", "w" );
    for ( i = 0; i < s_pManRwrExp->nFuncs; i++ )
        if ( s_pManRwrExp->pnCounts[i] > 5 )
        {
            fprintf( pFile, "%d ", i );
            CountWrite++;
        }
    fclose( pFile );
    printf( "%d classes written into file \"%s\".\n", CountWrite, "nnclass_stats.txt" );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


