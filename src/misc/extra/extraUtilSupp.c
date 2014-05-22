/**CFile****************************************************************

  FileName    [extraUtilSupp.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [extra]

  Synopsis    [Support minimization.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: extraUtilSupp.c,v 1.0 2003/02/01 00:00:00 alanmi Exp $]

***********************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "misc/vec/vec.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Generate m-out-of-n vectors.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_SuppCountOnes( unsigned i )
{
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    i = ((i + (i >> 4)) & 0x0F0F0F0F);
    return (i*(0x01010101))>>24;
}
Vec_Int_t * Abc_SuppGen( int m, int n )
{
    Vec_Int_t * vRes = Vec_IntAlloc( 1000 );
    int i, Size = (1 << n);
    for ( i = 0; i < Size; i++ )
        if ( Abc_SuppCountOnes(i) == m )
            Vec_IntPush( vRes, i );
    return vRes;
}

/**Function*************************************************************

  Synopsis    [Perform verification.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SuppVerify( Vec_Int_t * p, unsigned * pMatrix, int nVars, int nVarsMin )
{
    Vec_Int_t * pNew;
    int * pLimit, * pEntry1, * pEntry2;
    int i, k, v, Entry, EntryNew, Value, Counter = 0;
    pNew = Vec_IntAlloc( Vec_IntSize(p) );
    Vec_IntForEachEntry( p, Entry, i )
    {
        EntryNew = 0;
        for ( v = 0; v < nVarsMin; v++ )
        {
            Value = 0;
            for ( k = 0; k < nVars; k++ )
                if ( ((pMatrix[v] >> k) & 1) && ((Entry >> k) & 1) )
                    Value ^= 1;
            if ( Value )
                EntryNew |= (1 << v);            
        }
        Vec_IntPush( pNew, EntryNew );
    }
    // check that they are disjoint
    pLimit  = Vec_IntLimit(pNew);
    pEntry1 = Vec_IntArray(pNew);
    for ( ; pEntry1 < pLimit; pEntry1++ )
    for ( pEntry2 = pEntry1 + 1; pEntry2 < pLimit; pEntry2++ )
        if ( *pEntry1 == *pEntry2 )
            Counter++;
    if ( Counter )
        printf( "The total of %d pairs fail verification.\n", Counter );
    else
        printf( "Verification successful.\n" );
    Vec_IntFree( pNew );
}

/**Function*************************************************************

  Synopsis    [Generate pairs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_SuppGenPairs( Vec_Int_t * p, int nBits )
{
    Vec_Int_t * vRes = Vec_IntAlloc( 1000 );
    unsigned * pMap = ABC_CALLOC( unsigned, 1 << Abc_MaxInt(0,nBits-5) ); 
    int * pLimit = Vec_IntLimit(p);
    int * pEntry1 = Vec_IntArray(p);
    int * pEntry2, Value;
    for ( ; pEntry1 < pLimit; pEntry1++ )
    for ( pEntry2 = pEntry1 + 1; pEntry2 < pLimit; pEntry2++ )
    {
        Value = *pEntry1 ^ *pEntry2;
        if ( Abc_InfoHasBit(pMap, Value) )
            continue;
        Abc_InfoXorBit( pMap, Value );
        Vec_IntPush( vRes, Value );
    }
    ABC_FREE( pMap );
    return vRes;
}
Vec_Int_t * Abc_SuppGenPairs2( int nOnes, int nBits )
{
    Vec_Int_t * vRes = Vec_IntAlloc( 1000 );
    int i, k, Size = (1 << nBits), Value;
    for ( i = 0; i < Size; i++ )
    {
        Value = Abc_SuppCountOnes(i);
        for ( k = 1; k <= nOnes; k++ )
            if ( Value == 2*k )
                break;
        if ( k <= nOnes )
            Vec_IntPush( vRes, i );
    }
    return vRes;
}

/**Function*************************************************************

  Synopsis    [Select variable.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SuppPrintMask( unsigned uMask, int nBits )
{
    int i;
    for ( i = 0; i < nBits; i++ )
        printf( "%d", (uMask >> i) & 1 );
    printf( "\n" );
}
void Abc_SuppGenProfile( Vec_Int_t * p, int nBits, int * pCounts )
{
    int i, k, b, Ent;
    Vec_IntForEachEntry( p, Ent, i )
        for ( b = ((Ent >> nBits) & 1), k = 0; k < nBits; k++ )
            pCounts[k] += ((Ent >> k) & 1) ^ b;
}
void Abc_SuppPrintProfile( Vec_Int_t * p, int nBits )
{
    int k, Counts[32] = {0};
    Abc_SuppGenProfile( p, nBits, Counts );
    for ( k = 0; k < nBits; k++ )
        printf( "%2d : %6d  %6.2f %%\n", k, Counts[k], 100.0 * Counts[k] / Vec_IntSize(p) );
}
int Abc_SuppGenFindBest( Vec_Int_t * p, int nBits, int * pMerit )
{
    int k, kBest = 0, Counts[32] = {0};
    Abc_SuppGenProfile( p, nBits, Counts );
    for ( k = 1; k < nBits; k++ )
        if ( Counts[kBest] < Counts[k] )
            kBest = k;
    *pMerit = Counts[kBest];
    return kBest;
}
void Abc_SuppGenSelectVar( Vec_Int_t * p, int nBits, int iVar )
{
    int * pEntry = Vec_IntArray(p);
    int * pLimit = Vec_IntLimit(p);
    for ( ; pEntry < pLimit; pEntry++ )
        if ( (*pEntry >> iVar) & 1 )
            *pEntry ^= (1 << nBits);
}
void Abc_SuppGenFilter( Vec_Int_t * p, int nBits )
{
    int i, k = 0, Ent;
    Vec_IntForEachEntry( p, Ent, i )
        if ( ((Ent >> nBits) & 1) == 0 )
            Vec_IntWriteEntry( p, k++, Ent );
    Vec_IntShrink( p, k );
}
unsigned Abc_SuppFindOne( Vec_Int_t * p, int nBits )
{
    unsigned uMask = 0;
    int Prev = -1, This, Var;
    while ( 1 )
    {
        Var = Abc_SuppGenFindBest( p, nBits, &This );
        if ( Prev >= This )
            break;
        Prev = This;
        Abc_SuppGenSelectVar( p, nBits, Var );
        uMask |= (1 << Var);
    }
    return uMask;
}
int Abc_SuppMinimize( unsigned * pMatrix, Vec_Int_t * p, int nBits, int fVerbose )
{
    int i;
    for ( i = 0; Vec_IntSize(p) > 0; i++ )
    {
//        Abc_SuppPrintProfile( p, nBits );
        pMatrix[i] = Abc_SuppFindOne( p, nBits );
        Abc_SuppGenFilter( p, nBits );   
        if ( !fVerbose )
            continue;
        // print stats
        printf( "%2d : ", i );
        printf( "%6d  ", Vec_IntSize(p) );
        Abc_SuppPrintMask( pMatrix[i], nBits );
//        printf( "\n" );
    }
    return i;
}

/**Function*************************************************************

  Synopsis    [Create representation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SuppTest( int nOnes, int nVars, int fUseSimple, int fCheck, int fVerbose )
{
    int nVarsMin;
    unsigned Matrix[100];
    abctime clk = Abc_Clock();
    // create the problem
    Vec_Int_t * vRes = Abc_SuppGen( nOnes, nVars );
    Vec_Int_t * vPairs = fUseSimple ? Abc_SuppGenPairs2( nOnes, nVars ) : Abc_SuppGenPairs( vRes, nVars );
    assert( nVars < 100 );
    printf( "M = %2d  N = %2d : ", nOnes, nVars );
    printf( "K = %6d   ",  Vec_IntSize(vRes) );
    printf( "Total = %12.0f  ", 0.5 * Vec_IntSize(vRes) * (Vec_IntSize(vRes) - 1) );
    printf( "Distinct = %8d  ",  Vec_IntSize(vPairs) );
    Abc_PrintTime( 1, "Reduction time", Abc_Clock() - clk );
    // solve the problem
    clk = Abc_Clock();
    nVarsMin = Abc_SuppMinimize( Matrix, vPairs, nVars, fVerbose );
    printf( "Solution with %d variables found.  ", nVarsMin );
    Abc_PrintTime( 1, "Covering time", Abc_Clock() - clk );
    if ( fCheck )
        Abc_SuppVerify( vRes, Matrix, nVars, nVarsMin );
    Vec_IntFree( vPairs );
    Vec_IntFree( vRes );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

