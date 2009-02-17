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
static int num_cmp1( int * x, int * y) { return ((*x) < (*y)) ? -1 : (((*x) > (*y)) ? 1 : 0); }
static int num_cmp2( int * x, int * y) { return (*x) < (*y); }
static inline void selectionsort(int* array, int size, int(*comp)(const void *, const void *))
{
    int     i, j, best_i;
    int     tmp;
    for (i = 0; i < size-1; i++){
        best_i = i;
        for (j = i+1; j < size; j++){
            if (comp(array + j, array + best_i))
                best_i = j;
        }
        tmp = array[i]; array[i] = array[best_i]; array[best_i] = tmp;
    }
}
static void sort_rec(int* array, int size, int(*comp)(const void *, const void *))
{
    if (size <= 15)
        selectionsort(array, size, comp);
    else{
        int *  pivot = array + size/2;
        int    tmp;
        int    i = -1;
        int    j = size;
        for(;;){
            do i++; while(comp(array + i, pivot));
            do j--; while(comp(pivot, array + j));
            if (i >= j) break;
            tmp = array[i]; array[i] = array[j]; array[j] = tmp;
        }
        sort_rec(array    , i     , comp);
        sort_rec(&array[i], size-i, comp);
    }
}
void minisat_sort(int* array, int size, int(*comp)(const void *, const void *))
{
    sort_rec(array,size,comp);
}


int * Gia_SortGetTest( int nSize )
{
    int i, * pArray;
    srand( 0 );
    pArray = ABC_ALLOC( int, nSize );
    for ( i = 0; i < nSize; i++ )
        pArray[i] = rand();
    return pArray;
}
void Gia_SortVerifySorted( int * pArray, int nSize )
{
    int i;
    for ( i = 1; i < nSize; i++ )
        assert( pArray[i-1] <= pArray[i] );
}
void Gia_SortTest()
{
    int nSize = 1000000;
    int * pArray;
    int clk = clock();

    pArray = Gia_SortGetTest( nSize );
clk = clock();
    qsort( pArray, nSize, 4, (int (*)(const void *, const void *)) num_cmp1 );
ABC_PRT( "qsort  ", clock() - clk );
    Gia_SortVerifySorted( pArray, nSize );
    ABC_FREE( pArray );

    pArray = Gia_SortGetTest( nSize );
clk = clock();
    minisat_sort( pArray, nSize, (int (*)(const void *, const void *)) num_cmp2 );
ABC_PRT( "minisat", clock() - clk );
    Gia_SortVerifySorted( pArray, nSize );
    ABC_FREE( pArray );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


