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

  Synopsis    [Permutes the given vector of minterms.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Extra_TruthPermute_int( int * pMints, int nMints, char * pPerm, int nVars, int * pMintsP )
{
    int m, v;
    // clean the storage for minterms
    memset( pMintsP, 0, sizeof(int) * nMints );
    // go through minterms and add the variables
    for ( m = 0; m < nMints; m++ )
        for ( v = 0; v < nVars; v++ )
            if ( pMints[m] & (1 << v) )
                pMintsP[m] |= (1 << pPerm[v]);
}

/**Function*************************************************************

  Synopsis    [Permutes the function.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned Extra_TruthPermute( unsigned Truth, char * pPerms, int nVars, int fReverse )
{
    unsigned Result;
    int * pMints;
    int * pMintsP;
    int nMints;
    int i, m;

    assert( nVars < 6 );
    nMints  = (1 << nVars);
    pMints  = ALLOC( int, nMints );
    pMintsP = ALLOC( int, nMints );
    for ( i = 0; i < nMints; i++ )
        pMints[i] = i;

    Extra_TruthPermute_int( pMints, nMints, pPerms, nVars, pMintsP );

    Result = 0;
    if ( fReverse )
    {
        for ( m = 0; m < nMints; m++ )
            if ( Truth & (1 << pMintsP[m]) )
                Result |= (1 << m);
    }
    else
    {
        for ( m = 0; m < nMints; m++ )
            if ( Truth & (1 << m) )
                Result |= (1 << pMintsP[m]);
    }

    free( pMints );
    free( pMintsP );

    return Result;
}

/**Function*************************************************************

  Synopsis    [Changes the phase of the function.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned Extra_TruthPolarize( unsigned uTruth, int Polarity, int nVars )
{
    // elementary truth tables
    static unsigned Signs[5] = {
        0xAAAAAAAA,    // 1010 1010 1010 1010 1010 1010 1010 1010
        0xCCCCCCCC,    // 1010 1010 1010 1010 1010 1010 1010 1010
        0xF0F0F0F0,    // 1111 0000 1111 0000 1111 0000 1111 0000
        0xFF00FF00,    // 1111 1111 0000 0000 1111 1111 0000 0000
        0xFFFF0000     // 1111 1111 1111 1111 0000 0000 0000 0000
    };
    unsigned uTruthRes, uCof0, uCof1;
    int nMints, Shift, v;
    assert( nVars < 6 );
    nMints = (1 << nVars);
    uTruthRes = uTruth;
    for ( v = 0; v < nVars; v++ )
        if ( Polarity & (1 << v) )
        {
            uCof0  = uTruth & ~Signs[v];
            uCof1  = uTruth &  Signs[v];
            Shift  = (1 << v);
            uCof0 <<= Shift;
            uCof1 >>= Shift;
            uTruth = uCof0 | uCof1;
        }
    if ( nVars < 5 )
        uTruth &= ((~0) >> (32-nMints));
    return uTruth;
}

/**Function*************************************************************

  Synopsis    [Computes N-canonical form using brute-force methods.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned Extra_TruthCanonN( unsigned uTruth, int nVars )
{
    unsigned uTruthMin, uPhase;
    int nMints, p;
    nMints    = (1 << nVars);
    uTruthMin = 0xFFFFFFFF;
    for ( p = 0; p < nMints; p++ )
    {
        uPhase = Extra_TruthPolarize( uTruth, p, nVars ); 
        if ( uTruthMin > uPhase )
            uTruthMin = uPhase;
    }
    return uTruthMin;
}

/**Function*************************************************************

  Synopsis    [Computes NN-canonical form using brute-force methods.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned Extra_TruthCanonNN( unsigned uTruth, int nVars )
{
    unsigned uTruthMin, uTruthC, uPhase;
    int nMints, p;
    nMints    = (1 << nVars);
    uTruthC   = (unsigned)( (~uTruth) & ((~((unsigned)0)) >> (32-nMints)) );
    uTruthMin = 0xFFFFFFFF;
    for ( p = 0; p < nMints; p++ )
    {
        uPhase = Extra_TruthPolarize( uTruth, p, nVars ); 
        if ( uTruthMin > uPhase )
            uTruthMin = uPhase;
        uPhase = Extra_TruthPolarize( uTruthC, p, nVars ); 
        if ( uTruthMin > uPhase )
            uTruthMin = uPhase;
    }
    return uTruthMin;
}

/**Function*************************************************************

  Synopsis    [Computes P-canonical form using brute-force methods.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned Extra_TruthCanonP( unsigned uTruth, int nVars )
{
    static int nVarsOld, nPerms;
    static char ** pPerms = NULL;

    unsigned uTruthMin, uPerm;
    int k;

    if ( pPerms == NULL )
    {
        nPerms = Extra_Factorial( nVars );   
        pPerms = Extra_Permutations( nVars );
        nVarsOld = nVars;
    }
    else if ( nVarsOld != nVars )
    {
        free( pPerms );
        nPerms = Extra_Factorial( nVars );   
        pPerms = Extra_Permutations( nVars );
        nVarsOld = nVars;
    }

    uTruthMin = 0xFFFFFFFF;
    for ( k = 0; k < nPerms; k++ )
    {
        uPerm = Extra_TruthPermute( uTruth, pPerms[k], nVars, 0 );
        if ( uTruthMin > uPerm )
            uTruthMin = uPerm;
    }
    return uTruthMin;
}

/**Function*************************************************************

  Synopsis    [Computes NP-canonical form using brute-force methods.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned Extra_TruthCanonNP( unsigned uTruth, int nVars )
{
    static int nVarsOld, nPerms;
    static char ** pPerms = NULL;

    unsigned uTruthMin, uPhase, uPerm;
    int nMints, k, p;

    if ( pPerms == NULL )
    {
        nPerms = Extra_Factorial( nVars );   
        pPerms = Extra_Permutations( nVars );
        nVarsOld = nVars;
    }
    else if ( nVarsOld != nVars )
    {
        free( pPerms );
        nPerms = Extra_Factorial( nVars );   
        pPerms = Extra_Permutations( nVars );
        nVarsOld = nVars;
    }

    nMints    = (1 << nVars);
    uTruthMin = 0xFFFFFFFF;
    for ( p = 0; p < nMints; p++ )
    {
        uPhase = Extra_TruthPolarize( uTruth, p, nVars ); 
        for ( k = 0; k < nPerms; k++ )
        {
            uPerm = Extra_TruthPermute( uPhase, pPerms[k], nVars, 0 );
            if ( uTruthMin > uPerm )
                uTruthMin = uPerm;
        }
    }
    return uTruthMin;
}

/**Function*************************************************************

  Synopsis    [Computes NPN-canonical form using brute-force methods.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned Extra_TruthCanonNPN( unsigned uTruth, int nVars )
{
    static int nVarsOld, nPerms;
    static char ** pPerms = NULL;

    unsigned uTruthMin, uTruthC, uPhase, uPerm;
    int nMints, k, p;

    if ( pPerms == NULL )
    {
        nPerms = Extra_Factorial( nVars );   
        pPerms = Extra_Permutations( nVars );
        nVarsOld = nVars;
    }
    else if ( nVarsOld != nVars )
    {
        free( pPerms );
        nPerms = Extra_Factorial( nVars );   
        pPerms = Extra_Permutations( nVars );
        nVarsOld = nVars;
    }

    nMints    = (1 << nVars);
    uTruthC   = (unsigned)( (~uTruth) & ((~((unsigned)0)) >> (32-nMints)) );
    uTruthMin = 0xFFFFFFFF;
    for ( p = 0; p < nMints; p++ )
    {
        uPhase = Extra_TruthPolarize( uTruth, p, nVars ); 
        for ( k = 0; k < nPerms; k++ )
        {
            uPerm = Extra_TruthPermute( uPhase, pPerms[k], nVars, 0 );
            if ( uTruthMin > uPerm )
                uTruthMin = uPerm;
        }
        uPhase = Extra_TruthPolarize( uTruthC, p, nVars ); 
        for ( k = 0; k < nPerms; k++ )
        {
            uPerm = Extra_TruthPermute( uPhase, pPerms[k], nVars, 0 );
            if ( uTruthMin > uPerm )
                uTruthMin = uPerm;
        }
    }
    return uTruthMin;
}

/**Function*************************************************************

  Synopsis    [Computes NPN canonical forms for 4-variable functions.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Extra_Truth4VarNPN( unsigned short ** puCanons, char ** puPhases, char ** puPerms )
{
    unsigned short * uCanons;
    unsigned uTruth, uPhase, uPerm;
    char ** pPerms4, * uPhases, * uPerms;
    int nFuncs, nClasses;
    int p, k;

    nFuncs  = (1 << 16);
    uCanons = ALLOC( unsigned short, nFuncs );
    uPhases = ALLOC( char, nFuncs );
    uPerms  = ALLOC( char, nFuncs );
    memset( uCanons, 0, sizeof(unsigned short) * nFuncs );
    memset( uPhases, 0, sizeof(char) * nFuncs );
    memset( uPerms,  0, sizeof(char) * nFuncs );
    pPerms4 = Extra_Permutations( 4 );

    nClasses = 1;
    nFuncs = (1 << 15);
    for ( uTruth = 1; uTruth < (unsigned)nFuncs; uTruth++ )
    {
        // skip already assigned
        if ( uCanons[uTruth] )
            continue;
        nClasses++;
        for ( p = 0; p < 16; p++ )
        {
            uPhase = Extra_TruthPolarize( uTruth, p, 4 );
            for ( k = 0; k < 24; k++ )
            {
                uPerm = Extra_TruthPermute( uPhase, pPerms4[k], 4, 0 );
                if ( uCanons[uPerm] == 0 )
                {
                    uCanons[uPerm] = uTruth;
                    uPhases[uPerm] = p;
                    uPerms[uPerm]  = k;

                    uPerm = ~uPerm & 0xFFFF;
                    uCanons[uPerm] = uTruth;
                    uPhases[uPerm] = p | 16;
                    uPerms[uPerm]  = k;
                }
                else
                    assert( uCanons[uPerm] == uTruth );
            }
            uPhase = Extra_TruthPolarize( ~uTruth & 0xFFFF, p, 4 ); 
            for ( k = 0; k < 24; k++ )
            {
                uPerm = Extra_TruthPermute( uPhase, pPerms4[k], 4, 0 );
                if ( uCanons[uPerm] == 0 )
                {
                    uCanons[uPerm] = uTruth;
                    uPhases[uPerm] = p;
                    uPerms[uPerm]  = k;

                    uPerm = ~uPerm & 0xFFFF;
                    uCanons[uPerm] = uTruth;
                    uPhases[uPerm] = p | 16;
                    uPerms[uPerm]  = k;
                }
                else
                    assert( uCanons[uPerm] == uTruth );
            }
        }
    }
    uPhases[(1<<16)-1] = 16;
    assert( nClasses == 222 );
    free( pPerms4 );
    if ( puCanons ) 
        *puCanons = uCanons;
    else
        free( uCanons );
    if ( puPhases ) 
        *puPhases = uPhases;
    else
        free( uPhases );
    if ( puPerms ) 
        *puPerms = uPerms;
    else
        free( uPerms );
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


