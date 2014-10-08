/**CFile****************************************************************

  FileName    [extraUtilThresh.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [extra]

  Synopsis    [Dealing with threshold functions.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 7, 2014.]

  Revision    [$Id: extraUtilThresh.c,v 1.0 2014/10/07 00:00:00 alanmi Exp $]

***********************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include "misc/vec/vec.h"
#include "misc/util/utilTruth.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Checks thresholdness of the function.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Extra_ThreshPrintChow( int Chow0, int * pChow, int nVars )
{
    int i;
    for ( i = 0; i < nVars; i++ )
        printf( "%d ", pChow[i] );
    printf( "  %d\n", Chow0 );
}
int Extra_ThreshComputeChow( word * t, int nVars, int * pChow )
{
    int i, k, Chow0 = 0, nMints = (1 << nVars);
    memset( pChow, 0, sizeof(int) * nVars );
    // compute Chow coefs
    for ( i = 0; i < nMints; i++ )
        if ( Abc_TtGetBit(t, i) )
            for ( Chow0++, k = 0; k < nVars; k++ )
                if ( (i >> k) & 1 )
                    pChow[k]++;
    // compute modified Chow coefs
    for ( k = 0; k < nVars; k++ )
        pChow[k] = 2 * pChow[k] - Chow0;
    return Chow0 - (1 << (nVars-1));
}
void Extra_ThreshSortByChow( word * t, int nVars, int * pChow )
{
    int i, nWords = Abc_TtWordNum(nVars);
    while ( 1 )
    {
        int fChange = 0;
        for ( i = 0; i < nVars - 1; i++ )
        {
            if ( pChow[i] >= pChow[i+1] )
                continue;
            ABC_SWAP( int, pChow[i], pChow[i+1] );
            Abc_TtSwapAdjacent( t, nWords, i );
            fChange = 1;
        }
        if ( !fChange )
            return;
    }
}
static inline int Extra_ThreshWeightedSum( int * pW, int nVars, int m )
{
    int i, Cost = 0;
    for ( i = 0; i < nVars; i++ )
        if ( (m >> i) & 1 )
            Cost += pW[i];
    return Cost;
}
int Extra_ThreshSelectWeights3( word * t, int nVars, int * pW )
{
    int m, Lmin, Lmax, nMints = (1 << nVars);
    assert( nVars == 3 );
    for ( pW[2] = 1;     pW[2] <= nVars; pW[2]++ )
    for ( pW[1] = pW[2]; pW[1] <= nVars; pW[1]++ )
    for ( pW[0] = pW[1]; pW[0] <= nVars; pW[0]++ )
    {
        Lmin = 10000; Lmax = 0;
        for ( m = 0; m < nMints; m++ )
        {
            if ( Abc_TtGetBit(t, m) )
                Lmin = Abc_MinInt( Lmin, Extra_ThreshWeightedSum(pW, nVars, m) );
            else
                Lmax = Abc_MaxInt( Lmax, Extra_ThreshWeightedSum(pW, nVars, m) );
            if ( Lmax >= Lmin )
                break;
//            printf( "%c%d ", Abc_TtGetBit(t, m) ? '+' : '-', Extra_ThreshWeightedSum(pW, nVars, m) );
        }
//        printf( "  -%d +%d\n", Lmax, Lmin );
        if ( m < nMints )
            continue;
        assert( Lmax < Lmin );
        return Lmin;
    }
    return 0;
}
int Extra_ThreshSelectWeights4( word * t, int nVars, int * pW )
{
    int m, Lmin, Lmax, nMints = (1 << nVars);
    assert( nVars == 4 );
    for ( pW[3] = 1;     pW[3] <= nVars; pW[3]++ )
    for ( pW[2] = pW[3]; pW[2] <= nVars; pW[2]++ )
    for ( pW[1] = pW[2]; pW[1] <= nVars; pW[1]++ )
    for ( pW[0] = pW[1]; pW[0] <= nVars; pW[0]++ )
    {
        Lmin = 10000; Lmax = 0;
        for ( m = 0; m < nMints; m++ )
        {
            if ( Abc_TtGetBit(t, m) )
                Lmin = Abc_MinInt( Lmin, Extra_ThreshWeightedSum(pW, nVars, m) );
            else
                Lmax = Abc_MaxInt( Lmax, Extra_ThreshWeightedSum(pW, nVars, m) );
            if ( Lmax >= Lmin )
                break;
        }
        if ( m < nMints )
            continue;
        assert( Lmax < Lmin );
        return Lmin;
    }
    return 0;
}
int Extra_ThreshSelectWeights5( word * t, int nVars, int * pW )
{
    int m, Lmin, Lmax, nMints = (1 << nVars), Limit = nVars + 0;
    assert( nVars == 5 );
    for ( pW[4] = 1;     pW[4] <= Limit; pW[4]++ )
    for ( pW[3] = pW[4]; pW[3] <= Limit; pW[3]++ )
    for ( pW[2] = pW[3]; pW[2] <= Limit; pW[2]++ )
    for ( pW[1] = pW[2]; pW[1] <= Limit; pW[1]++ )
    for ( pW[0] = pW[1]; pW[0] <= Limit; pW[0]++ )
    {
        Lmin = 10000; Lmax = 0;
        for ( m = 0; m < nMints; m++ )
        {
            if ( Abc_TtGetBit(t, m) )
                Lmin = Abc_MinInt( Lmin, Extra_ThreshWeightedSum(pW, nVars, m) );
            else
                Lmax = Abc_MaxInt( Lmax, Extra_ThreshWeightedSum(pW, nVars, m) );
            if ( Lmax >= Lmin )
                break;
        }
        if ( m < nMints )
            continue;
        assert( Lmax < Lmin );
        return Lmin;
    }
    return 0;
}
int Extra_ThreshSelectWeights6( word * t, int nVars, int * pW )
{
    int m, Lmin, Lmax, nMints = (1 << nVars), Limit = nVars + 3;
    assert( nVars == 6 );
    for ( pW[5] = 1;     pW[5] <= Limit; pW[5]++ )
    for ( pW[4] = pW[5]; pW[4] <= Limit; pW[4]++ )
    for ( pW[3] = pW[4]; pW[3] <= Limit; pW[3]++ )
    for ( pW[2] = pW[3]; pW[2] <= Limit; pW[2]++ )
    for ( pW[1] = pW[2]; pW[1] <= Limit; pW[1]++ )
    for ( pW[0] = pW[1]; pW[0] <= Limit; pW[0]++ )
    {
        Lmin = 10000; Lmax = 0;
        for ( m = 0; m < nMints; m++ )
        {
            if ( Abc_TtGetBit(t, m) )
                Lmin = Abc_MinInt( Lmin, Extra_ThreshWeightedSum(pW, nVars, m) );
            else
                Lmax = Abc_MaxInt( Lmax, Extra_ThreshWeightedSum(pW, nVars, m) );
            if ( Lmax >= Lmin )
                break;
        }
        if ( m < nMints )
            continue;
        assert( Lmax < Lmin );
        return Lmin;
    }
    return 0;
}
int Extra_ThreshSelectWeights7( word * t, int nVars, int * pW )
{
    int m, Lmin, Lmax, nMints = (1 << nVars), Limit = nVars + 6;
    assert( nVars == 7 );
    for ( pW[6] = 1;     pW[6] <= Limit; pW[6]++ )
    for ( pW[5] = pW[6]; pW[5] <= Limit; pW[5]++ )
    for ( pW[4] = pW[5]; pW[4] <= Limit; pW[4]++ )
    for ( pW[3] = pW[4]; pW[3] <= Limit; pW[3]++ )
    for ( pW[2] = pW[3]; pW[2] <= Limit; pW[2]++ )
    for ( pW[1] = pW[2]; pW[1] <= Limit; pW[1]++ )
    for ( pW[0] = pW[1]; pW[0] <= Limit; pW[0]++ )
    {
        Lmin = 10000; Lmax = 0;
        for ( m = 0; m < nMints; m++ )
        {
            if ( Abc_TtGetBit(t, m) )
                Lmin = Abc_MinInt( Lmin, Extra_ThreshWeightedSum(pW, nVars, m) );
            else
                Lmax = Abc_MaxInt( Lmax, Extra_ThreshWeightedSum(pW, nVars, m) );
            if ( Lmax >= Lmin )
                break;
        }
        if ( m < nMints )
            continue;
        assert( Lmax < Lmin );
        return Lmin;
    }
    return 0;
}
int Extra_ThreshSelectWeights8( word * t, int nVars, int * pW )
{
    int m, Lmin, Lmax, nMints = (1 << nVars), Limit = nVars + 1; // <<-- incomplete detection to save runtime!
    assert( nVars == 8 );
    for ( pW[7] = 1;     pW[7] <= Limit; pW[7]++ )
    for ( pW[6] = pW[7]; pW[6] <= Limit; pW[6]++ )
    for ( pW[5] = pW[6]; pW[5] <= Limit; pW[5]++ )
    for ( pW[4] = pW[5]; pW[4] <= Limit; pW[4]++ )
    for ( pW[3] = pW[4]; pW[3] <= Limit; pW[3]++ )
    for ( pW[2] = pW[3]; pW[2] <= Limit; pW[2]++ )
    for ( pW[1] = pW[2]; pW[1] <= Limit; pW[1]++ )
    for ( pW[0] = pW[1]; pW[0] <= Limit; pW[0]++ )
    {
        Lmin = 10000; Lmax = 0;
        for ( m = 0; m < nMints; m++ )
        {
            if ( Abc_TtGetBit(t, m) )
                Lmin = Abc_MinInt( Lmin, Extra_ThreshWeightedSum(pW, nVars, m) );
            else
                Lmax = Abc_MaxInt( Lmax, Extra_ThreshWeightedSum(pW, nVars, m) );
            if ( Lmax >= Lmin )
                break;
        }
        if ( m < nMints )
            continue;
        assert( Lmax < Lmin );
        return Lmin;
    }
    return 0;
}
int Extra_ThreshSelectWeights( word * t, int nVars, int * pW )
{
    if ( nVars <= 2 )
        return (t[0] & 0xF) != 6 && (t[0] & 0xF) != 9;
    if ( nVars == 3 )
        return Extra_ThreshSelectWeights3( t, nVars, pW );
    if ( nVars == 4 )
        return Extra_ThreshSelectWeights4( t, nVars, pW );
    if ( nVars == 5 )
        return Extra_ThreshSelectWeights5( t, nVars, pW );
    if ( nVars == 6 )
        return Extra_ThreshSelectWeights6( t, nVars, pW );
    if ( nVars == 7 )
        return Extra_ThreshSelectWeights7( t, nVars, pW );
    if ( nVars == 8 )
        return Extra_ThreshSelectWeights8( t, nVars, pW );
    return 0;
}
int Extra_ThreshCheck( word * t, int nVars, int * pW )
{
    int Chow0, Chow[16];
    if ( !Abc_TtIsUnate(t, nVars) )
        return 0;
    Abc_TtMakePosUnate( t, nVars );
    Chow0 = Extra_ThreshComputeChow( t, nVars, Chow );
    Extra_ThreshSortByChow( t, nVars, Chow );
    return Extra_ThreshSelectWeights( t, nVars, pW );
}

/**Function*************************************************************

  Synopsis    [Checks unateness of a function.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Extra_ThreshCheckTest()
{
    int nVars = 5;
    int T, Chow0, Chow[16], Weights[16];
//    word t =  s_Truths6[0] & s_Truths6[1] & s_Truths6[2] & s_Truths6[3] & s_Truths6[4];
//    word t =  (s_Truths6[0] & s_Truths6[1]) | (s_Truths6[0] & s_Truths6[2] & s_Truths6[3]) | (s_Truths6[0] & s_Truths6[2] & s_Truths6[4]);
    word t =  (s_Truths6[2] & s_Truths6[1]) | (s_Truths6[2] & s_Truths6[0] & s_Truths6[3]) | (s_Truths6[2] & s_Truths6[0] & ~s_Truths6[4]);
//    word t =  (s_Truths6[0] & s_Truths6[1]) | (s_Truths6[0] & s_Truths6[2] & s_Truths6[3]) | (s_Truths6[0] & s_Truths6[2] & s_Truths6[4]) | (s_Truths6[1] & s_Truths6[2] & s_Truths6[3]);
//    word t =  (s_Truths6[0] & s_Truths6[1]) | (s_Truths6[0] & s_Truths6[2]) | (s_Truths6[0] & s_Truths6[3] & s_Truths6[4] & s_Truths6[5]) | 
//        (s_Truths6[1] & s_Truths6[2] & s_Truths6[3]) | (s_Truths6[1] & s_Truths6[2] & s_Truths6[4]) | (s_Truths6[1] & s_Truths6[2] & s_Truths6[5]);
    int i;
    assert( nVars <= 8 );
    for ( i = 0; i < nVars; i++ )
        printf( "%d %d %d\n", i, Abc_TtPosVar(&t, nVars, i), Abc_TtNegVar(&t, nVars, i) );
//    word t = s_Truths6[0] & s_Truths6[1] & s_Truths6[2];
    Chow0 = Extra_ThreshComputeChow( &t, nVars, Chow );
    if ( (T = Extra_ThreshCheck(&t, nVars, Weights)) )
        Extra_ThreshPrintChow( T, Weights, nVars );
    else
        printf( "No threshold\n" );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

