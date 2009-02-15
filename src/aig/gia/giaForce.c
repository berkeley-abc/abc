/**CFile****************************************************************

  FileName    [gia.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: gia.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [This is implementation of qsort in MiniSat.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int num_cmp ( int * x, int * y) { return ((*x) < (*y)) ? -1 : 1; }
// Returns a random float 0 <= x < 1. Seed must never be 0.
static inline double drand(double* seed) {
    int q;
    *seed *= 1389796;
    q = (int)(*seed / 2147483647);
    *seed -= (double)q * 2147483647;
    return *seed / 2147483647; }
// Returns a random integer 0 <= x < size. Seed must never be 0.
static inline int irand(double* seed, int size) {
    return (int)(drand(seed) * size); }
static inline void selectionsort(int* array, int size, int(*comp)(const void *, const void *))
{
    int     i, j, best_i;
    int     tmp;
    for (i = 0; i < size-1; i++){
        best_i = i;
        for (j = i+1; j < size; j++){
            if (comp(array + j, array + best_i) < 0)
                best_i = j;
        }
        tmp = array[i]; array[i] = array[best_i]; array[best_i] = tmp;
    }
}
static void sortrnd(int* array, int size, int(*comp)(const void *, const void *), double* seed)
{
    if (size <= 15)
        selectionsort(array, size, comp);
    else{
        int *  pivot = array + irand(seed, size);
        int    tmp;
        int    i = -1;
        int    j = size;
        for(;;){
            do i++; while(comp(array + i, pivot)<0);
            do j--; while(comp(pivot, array + j)<0);
            if (i >= j) break;
            tmp = array[i]; array[i] = array[j]; array[j] = tmp;
        }
        sortrnd(array    , i     , comp, seed);
        sortrnd(&array[i], size-i, comp, seed);
    }
}
void minisat_sort(int* array, int size, int(*comp)(const void *, const void *))
{
    double seed = 91648253;
    sortrnd(array,size,comp,&seed);
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int * Gia_SortGetTest( int nSize )
{
    int i, * pArray;
    Aig_ManRandom( 1 );
    pArray = ABC_ALLOC( int, nSize );
    for ( i = 0; i < nSize; i++ )
        pArray[i] = (Aig_ManRandom( 0 ) >> 2);
    return pArray;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_SortVerifySorted( int * pArray, int nSize )
{
    int i;
    for ( i = 1; i < nSize; i++ )
        assert( pArray[i-1] <= pArray[i] );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_SortTest()
{
    int nSize = 1000000;
    int * pArray;
    int clk = clock();
    pArray = Gia_SortGetTest( nSize );
clk = clock();
    qsort( pArray, nSize, 4, (int (*)(const void *, const void *)) num_cmp );
ABC_PRT( "qsort  ", clock() - clk );
    Gia_SortVerifySorted( pArray, nSize );
    ABC_FREE( pArray );
    pArray = Gia_SortGetTest( nSize );
clk = clock();
    minisat_sort( pArray, nSize, (int (*)(const void *, const void *)) num_cmp );
ABC_PRT( "minisat", clock() - clk );
    Gia_SortVerifySorted( pArray, nSize );
    ABC_FREE( pArray );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


