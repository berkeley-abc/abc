/**CFile****************************************************************

  FileName    [extraUtilMisc.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [extra]

  Synopsis    [Misc procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: extraUtilMisc.c,v 1.0 2003/09/01 00:00:00 alanmi Exp $]

***********************************************************************/

#include "extra.h"

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


/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

/**AutomaticEnd***************************************************************/

static void Extra_Permutations_rec( char ** pRes, int nFact, int n, char Array[] );

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/


/**Function********************************************************************

  Synopsis    [Finds the smallest integer larger of equal than the logarithm.]

  Description [Returns [Log2(Num)].]

  SideEffects []

  SeeAlso     []

******************************************************************************/
int Extra_Base2Log( unsigned Num )
{
    int Res;
    assert( Num >= 0 );
    if ( Num == 0 ) return 0;
    if ( Num == 1 ) return 1;
    for ( Res = 0, Num--; Num; Num >>= 1, Res++ );
    return Res;
} /* end of Extra_Base2Log */

/**Function********************************************************************

  Synopsis    [Finds the smallest integer larger of equal than the logarithm.]

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int Extra_Base2LogDouble( double Num )
{
    double Res;
    int ResInt;

    Res    = log(Num)/log(2.0);
    ResInt = (int)Res;
    if ( ResInt == Res )
        return ResInt;
    else 
        return ResInt+1;
}

/**Function********************************************************************

  Synopsis    [Finds the smallest integer larger of equal than the logarithm.]

  Description [Returns [Log10(Num)].]

  SideEffects []

  SeeAlso     []

******************************************************************************/
int Extra_Base10Log( unsigned Num )
{
    int Res;
    assert( Num >= 0 );
    if ( Num == 0 ) return 0;
    if ( Num == 1 ) return 1;
    for ( Res = 0, Num--;  Num;  Num /= 10,  Res++ );
    return Res;
} /* end of Extra_Base2Log */

/**Function********************************************************************

  Synopsis    [Returns the power of two as a double.]

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
double Extra_Power2( int Degree )
{
    double Res;
    assert( Degree >= 0 );
    if ( Degree < 32 )
        return (double)(01<<Degree); 
    for ( Res = 1.0; Degree; Res *= 2.0, Degree-- );
    return Res;
}


/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Extra_Power3( int Num )
{
    int i;
    int Res;
    Res = 1;
    for ( i = 0; i < Num; i++ )
        Res *= 3;
    return Res;
}

/**Function********************************************************************

  Synopsis    [Finds the number of combinations of k elements out of n.]

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int Extra_NumCombinations( int k, int n )
{
    int i, Res = 1;
    for ( i = 1; i <= k; i++ )
            Res = Res * (n-i+1) / i;
    return Res;
} /* end of Extra_NumCombinations */

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int * Extra_DeriveRadixCode( int Number, int Radix, int nDigits )
{
    static int Code[100];
    int i;
    assert( nDigits < 100 );
    for ( i = 0; i < nDigits; i++ )
    {
        Code[i] = Number % Radix;
        Number  = Number / Radix;
    }
    assert( Number == 0 );
    return Code;
}

/**Function********************************************************************

  Synopsis    [Computes the factorial.]

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int Extra_Factorial( int n )
{
    int i, Res = 1;
    for ( i = 1; i <= n; i++ )
        Res *= i;
    return Res;
}

/**Function********************************************************************

  Synopsis    [Computes the set of all permutations.]

  Description [The number of permutations in the array is n!. The number of
  entries in each permutation is n. Therefore, the resulting array is a 
  two-dimentional array of the size: n! x n. To free the resulting array,
  call free() on the pointer returned by this procedure.]

  SideEffects []

  SeeAlso     []

******************************************************************************/
char ** Extra_Permutations( int n )
{
    char Array[50];
    char ** pRes;
    char * pBuffer;
    int nFact, i;
    // allocate all memory at once
    nFact   = Extra_Factorial( n );
    pBuffer = ALLOC( char, nFact * sizeof(char *) + nFact * n * sizeof(char) );
    // split the chunk
    pRes = (char **)pBuffer;
    for ( i = 0; i < nFact; i++ )
        pRes[i] = pBuffer + nFact * sizeof(char *) + i * n * sizeof(char);
    // fill in the permutations
    for ( i = 0; i < n; i++ )
        Array[i] = i;
    Extra_Permutations_rec( pRes, nFact, n, Array );
    // print the permutations
/*
    {
    int i, k;
    for ( i = 0; i < nFact; i++ )
    {
        printf( "{" );
        for ( k = 0; k < n; k++ )
            printf( " %d", pRes[i][k] );
        printf( " }\n" );
    }
    }
*/
    return pRes;
}

/**Function********************************************************************

  Synopsis    [Fills in the array of permutations.]

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
void Extra_Permutations_rec( char ** pRes, int nFact, int n, char Array[] )
{
    char ** pNext;
    int nFactNext;
    int iTemp, iCur, iLast, p;

    if ( n == 1 )
    {
        pRes[0][0] = Array[0];
        return;
    }

    // get the next factorial
    nFactNext = nFact / n;
    // get the last entry
    iLast = n - 1;

    for ( iCur = 0; iCur < n; iCur++ )
    {
        // swap Cur and Last
        iTemp        = Array[iCur];
        Array[iCur]  = Array[iLast];
        Array[iLast] = iTemp;

        // get the pointer to the current section
        pNext = pRes + (n - 1 - iCur) * nFactNext;

        // set the last entry 
        for ( p = 0; p < nFactNext; p++ )
            pNext[p][iLast] = Array[iLast];

        // call recursively for this part
        Extra_Permutations_rec( pNext, nFactNext, n - 1, Array );

        // swap them back
        iTemp        = Array[iCur];
        Array[iCur]  = Array[iLast];
        Array[iLast] = iTemp;
    }
}

/**Function*************************************************************

  Synopsis    [Returns the smallest prime larger than the number.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned int Cudd_PrimeCopy( unsigned int  p)
{
    int i,pn;

    p--;
    do {
        p++;
        if (p&1) {
        pn = 1;
        i = 3;
        while ((unsigned) (i * i) <= p) {
        if (p % i == 0) {
            pn = 0;
            break;
        }
        i += 2;
        }
    } else {
        pn = 0;
    }
    } while (!pn);
    return(p);

} /* end of Cudd_Prime */


/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Definition of static Functions                                            */
/*---------------------------------------------------------------------------*/


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


