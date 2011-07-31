/**CFile****************************************************************

  FileName    [utilSort.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Merge sort with user-specified cost.]

  Synopsis    [Merge sort with user-specified cost.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - Feburary 13, 2011.]

  Revision    [$Id: utilSort.c,v 1.00 2011/02/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>

#include "abc_global.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Merging two lists of entries.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SortMerge( int * p1Beg, int * p1End, int * p2Beg, int * p2End, int * pOut )
{
    int nEntries = (p1End - p1Beg) + (p2End - p2Beg);
    int * pOutBeg = pOut;
    while ( p1Beg < p1End && p2Beg < p2End )
    {
        if ( *p1Beg == *p2Beg )
            *pOut++ = *p1Beg++, *pOut++ = *p2Beg++; 
        else if ( *p1Beg < *p2Beg )
            *pOut++ = *p1Beg++; 
        else // if ( *p1Beg > *p2Beg )
            *pOut++ = *p2Beg++; 
    }
    while ( p1Beg < p1End )
        *pOut++ = *p1Beg++; 
    while ( p2Beg < p2End )
        *pOut++ = *p2Beg++;
    assert( pOut - pOutBeg == nEntries );
}

/**Function*************************************************************

  Synopsis    [Recursive sorting.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_Sort_rec( int * pInBeg, int * pInEnd, int * pOutBeg )
{
    int nSize = pInEnd - pInBeg;
    assert( nSize > 0 );
    if ( nSize == 1 )
        return;
    if ( nSize == 2 )
    {
         if ( pInBeg[0] > pInBeg[1] )
         {
             pInBeg[0] ^= pInBeg[1];
             pInBeg[1] ^= pInBeg[0];
             pInBeg[0] ^= pInBeg[1];
         }
    }
    else if ( nSize < 8 )
    {
        int temp, i, j, best_i;
        for ( i = 0; i < nSize-1; i++ )
        {
            best_i = i;
            for ( j = i+1; j < nSize; j++ )
                if ( pInBeg[j] < pInBeg[best_i] )
                    best_i = j;
            temp = pInBeg[i]; 
            pInBeg[i] = pInBeg[best_i]; 
            pInBeg[best_i] = temp;
        }
    }
    else
    {
        Abc_Sort_rec( pInBeg, pInBeg + nSize/2, pOutBeg );
        Abc_Sort_rec( pInBeg + nSize/2, pInEnd, pOutBeg + nSize/2 );
        Abc_SortMerge( pInBeg, pInBeg + nSize/2, pInBeg + nSize/2, pInEnd, pOutBeg );
        memcpy( pInBeg, pOutBeg, sizeof(int) * nSize );
    }
}

/**Function*************************************************************

  Synopsis    [Returns the sorted array of integers.]

  Description [This procedure is about 10% faster than qsort().]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_Sort( int * pInput, int nSize )
{
    int * pOutput;
    if ( nSize < 2 )
        return;
    pOutput = (int *) malloc( sizeof(int) * nSize );
    Abc_Sort_rec( pInput, pInput + nSize, pOutput );
    free( pOutput );
}



/**Function*************************************************************

  Synopsis    [Merging two lists of entries.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SortCostMerge( int * p1Beg, int * p1End, int * p2Beg, int * p2End, int * pOut )
{
    int nEntries = (p1End - p1Beg) + (p2End - p2Beg);
    int * pOutBeg = pOut;
    while ( p1Beg < p1End && p2Beg < p2End )
    {
        if ( p1Beg[1] == p2Beg[1] )
            *pOut++ = *p1Beg++, *pOut++ = *p1Beg++, *pOut++ = *p2Beg++, *pOut++ = *p2Beg++; 
        else if ( p1Beg[1] < p2Beg[1] )
            *pOut++ = *p1Beg++, *pOut++ = *p1Beg++; 
        else // if ( p1Beg[1] > p2Beg[1] )
            *pOut++ = *p2Beg++, *pOut++ = *p2Beg++; 
    }
    while ( p1Beg < p1End )
        *pOut++ = *p1Beg++, *pOut++ = *p1Beg++; 
    while ( p2Beg < p2End )
        *pOut++ = *p2Beg++, *pOut++ = *p2Beg++;
    assert( pOut - pOutBeg == nEntries );
}

/**Function*************************************************************

  Synopsis    [Recursive sorting.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SortCost_rec( int * pInBeg, int * pInEnd, int * pOutBeg )
{
    int nSize = (pInEnd - pInBeg)/2;
    assert( nSize > 0 );
    if ( nSize == 1 )
        return;
    if ( nSize == 2 )
    {
         if ( pInBeg[1] > pInBeg[3] )
         {
             pInBeg[1] ^= pInBeg[3];
             pInBeg[3] ^= pInBeg[1];
             pInBeg[1] ^= pInBeg[3];
             pInBeg[0] ^= pInBeg[2];
             pInBeg[2] ^= pInBeg[0];
             pInBeg[0] ^= pInBeg[2];
         }
    }
    else if ( nSize < 8 )
    {
        int temp, i, j, best_i;
        for ( i = 0; i < nSize-1; i++ )
        {
            best_i = i;
            for ( j = i+1; j < nSize; j++ )
                if ( pInBeg[2*j+1] < pInBeg[2*best_i+1] )
                    best_i = j;
            temp = pInBeg[2*i]; 
            pInBeg[2*i] = pInBeg[2*best_i]; 
            pInBeg[2*best_i] = temp;
            temp = pInBeg[2*i+1]; 
            pInBeg[2*i+1] = pInBeg[2*best_i+1]; 
            pInBeg[2*best_i+1] = temp;
        }
    }
    else
    {
        Abc_SortCost_rec( pInBeg, pInBeg + 2*(nSize/2), pOutBeg );
        Abc_SortCost_rec( pInBeg + 2*(nSize/2), pInEnd, pOutBeg + 2*(nSize/2) );
        Abc_SortCostMerge( pInBeg, pInBeg + 2*(nSize/2), pInBeg + 2*(nSize/2), pInEnd, pOutBeg );
        memcpy( pInBeg, pOutBeg, sizeof(int) * 2 * nSize );
    }
}

/**Function*************************************************************

  Synopsis    [Sorting procedure.]

  Description [Returns permutation for the non-decreasing order of costs.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int * Abc_SortCost( int * pCosts, int nSize )
{
    int i, * pResult, * pInput, * pOutput;
    pResult = (int *) calloc( sizeof(int), nSize );
    if ( nSize < 2 )
        return pResult;
    pInput  = (int *) malloc( sizeof(int) * 2 * nSize );
    pOutput = (int *) malloc( sizeof(int) * 2 * nSize );
    for ( i = 0; i < nSize; i++ )
        pInput[2*i] = i, pInput[2*i+1] = pCosts[i];
    Abc_SortCost_rec( pInput, pInput + 2*nSize, pOutput );
    for ( i = 0; i < nSize; i++ )
        pResult[i] = pInput[2*i];
    free( pOutput );
    free( pInput );
    return pResult;
}


// this implementation uses 3x less memory but is 30% slower due to cache misses

#if 0  

/**Function*************************************************************

  Synopsis    [Merging two lists of entries.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SortCostMerge( int * p1Beg, int * p1End, int * p2Beg, int * p2End, int * pOut, int * pCost )
{
    int nEntries = (p1End - p1Beg) + (p2End - p2Beg);
    int * pOutBeg = pOut;
    while ( p1Beg < p1End && p2Beg < p2End )
    {
        if ( pCost[*p1Beg] == pCost[*p2Beg] )
            *pOut++ = *p1Beg++, *pOut++ = *p2Beg++; 
        else if ( pCost[*p1Beg] < pCost[*p2Beg] )
            *pOut++ = *p1Beg++; 
        else // if ( pCost[*p1Beg] > pCost[*p2Beg] )
            *pOut++ = *p2Beg++; 
    }
    while ( p1Beg < p1End )
        *pOut++ = *p1Beg++; 
    while ( p2Beg < p2End )
        *pOut++ = *p2Beg++;
    assert( pOut - pOutBeg == nEntries );
}

/**Function*************************************************************

  Synopsis    [Recursive sorting.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SortCost_rec( int * pInBeg, int * pInEnd, int * pOutBeg, int * pCost )
{
    int nSize = pInEnd - pInBeg;
    assert( nSize > 0 );
    if ( nSize == 1 )
        return;
    if ( nSize == 2 )
    {
         if ( pCost[pInBeg[0]] > pCost[pInBeg[1]] )
         {
             pInBeg[0] ^= pInBeg[1];
             pInBeg[1] ^= pInBeg[0];
             pInBeg[0] ^= pInBeg[1];
         }
    }
    else if ( nSize < 8 )
    {
        int temp, i, j, best_i;
        for ( i = 0; i < nSize-1; i++ )
        {
            best_i = i;
            for ( j = i+1; j < nSize; j++ )
                if ( pCost[pInBeg[j]] < pCost[pInBeg[best_i]] )
                    best_i = j;
            temp = pInBeg[i]; 
            pInBeg[i] = pInBeg[best_i]; 
            pInBeg[best_i] = temp;
        }
    }
    else
    {
        Abc_SortCost_rec( pInBeg, pInBeg + nSize/2, pOutBeg, pCost );
        Abc_SortCost_rec( pInBeg + nSize/2, pInEnd, pOutBeg + nSize/2, pCost );
        Abc_SortCostMerge( pInBeg, pInBeg + nSize/2, pInBeg + nSize/2, pInEnd, pOutBeg, pCost );
        memcpy( pInBeg, pOutBeg, sizeof(int) * nSize );
    }
}

/**Function*************************************************************

  Synopsis    [Sorting procedure.]

  Description [Returns permutation for the non-decreasing order of costs.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int * Abc_SortCost( int * pCosts, int nSize )
{
    int i, * pInput, * pOutput;
    pInput = (int *) malloc( sizeof(int) * nSize );
    for ( i = 0; i < nSize; i++ )
        pInput[i] = i;
    if ( nSize < 2 )
        return pInput;
    pOutput = (int *) malloc( sizeof(int) * nSize );
    Abc_SortCost_rec( pInput, pInput + nSize, pOutput, pCosts );
    free( pOutput );
    return pInput;
}

#endif




/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_SortNumCompare( int * pNum1, int * pNum2 )
{
    return *pNum1 - *pNum2;
}

/**Function*************************************************************

  Synopsis    [Testing the sorting procedure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SortTest()
{
    int fUseNew = 0;
    int i, clk, nSize = 50000000;
    int * pArray = (int *)malloc( sizeof(int) * nSize );
    int * pPerm;
    // generate numbers
    srand( 1000 );
    for ( i = 0; i < nSize; i++ )
        pArray[i] = rand();

    // try sorting
    if ( fUseNew )
    {
        int fUseCost = 1;
        if ( fUseCost )
        {
            clk = clock();
            pPerm = Abc_SortCost( pArray, nSize );
            Abc_PrintTime( 1, "New sort", clock() - clk );
            // check
            for ( i = 1; i < nSize; i++ )
                assert( pArray[pPerm[i-1]] <= pArray[pPerm[i]] );
            free( pPerm );
        }
        else
        {
            clk = clock();
            Abc_Sort( pArray, nSize );
            Abc_PrintTime( 1, "New sort", clock() - clk );
            // check
            for ( i = 1; i < nSize; i++ )
                assert( pArray[i-1] <= pArray[i] );
        }
    }
    else
    {
        clk = clock();
        qsort( (void *)pArray, nSize, sizeof(int), (int (*)(const void *, const void *)) Abc_SortNumCompare );
        Abc_PrintTime( 1, "Old sort", clock() - clk );
        // check
        for ( i = 1; i < nSize; i++ )
            assert( pArray[i-1] <= pArray[i] );
    }

    free( pArray );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

