/**CFile****************************************************************

  FileName    [utilCex.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Handling counter-examples.]

  Synopsis    [Handling counter-examples.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - Feburary 13, 2011.]

  Revision    [$Id: utilCex.c,v 1.00 2011/02/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>

#include "abc_global.h"
#include "utilCex.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////


/**Function*************************************************************

  Synopsis    [Allocates a counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t * Abc_CexAlloc( int nRegs, int nRealPis, int nFrames )
{
    Abc_Cex_t * pCex;
    int nWords = Abc_BitWordNum( nRegs + nRealPis * nFrames );
    pCex = (Abc_Cex_t *)ABC_ALLOC( char, sizeof(Abc_Cex_t) + sizeof(unsigned) * nWords );
    memset( pCex, 0, sizeof(Abc_Cex_t) + sizeof(unsigned) * nWords );
    pCex->nRegs  = nRegs;
    pCex->nPis   = nRealPis;
    pCex->nBits  = nRegs + nRealPis * nFrames;
    return pCex;
}

/**Function*************************************************************

  Synopsis    [Make the trivial counter-example for the trivially asserted output.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t * Abc_CexMakeTriv( int nRegs, int nTruePis, int nTruePos, int iFrameOut )
{
    Abc_Cex_t * pCex;
    int iPo, iFrame;
    assert( nRegs > 0 );
    iPo    = iFrameOut % nTruePos;
    iFrame = iFrameOut / nTruePos;
    // allocate the counter example
    pCex = Abc_CexAlloc( nRegs, nTruePis, iFrame + 1 );
    pCex->iPo    = iPo;
    pCex->iFrame = iFrame;
    return pCex;
}

/**Function*************************************************************

  Synopsis    [Derives the counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t * Abc_CexCreate( int nRegs, int nPis, int * pArray, int iFrame, int iPo, int fSkipRegs )
{
    Abc_Cex_t * pCex;
    int i;
    pCex = Abc_CexAlloc( nRegs, nPis, iFrame+1 );
    pCex->iPo    = iPo;
    pCex->iFrame = iFrame;
    if ( pArray == NULL )
        return pCex;
    if ( fSkipRegs )
    {
        for ( i = nRegs; i < pCex->nBits; i++ )
            if ( pArray[i-nRegs] )
                Abc_InfoSetBit( pCex->pData, i );
    }
    else
    {
        for ( i = 0; i < pCex->nBits; i++ )
            if ( pArray[i] )
                Abc_InfoSetBit( pCex->pData, i );
    }
    return pCex;
}

/**Function*************************************************************

  Synopsis    [Make the trivial counter-example for the trivially asserted output.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t * Abc_CexDup( Abc_Cex_t * p, int nRegsNew )
{
    Abc_Cex_t * pCex;
    int i;
    if ( nRegsNew == -1 )
        nRegsNew = p->nRegs;
    pCex = Abc_CexAlloc( nRegsNew, p->nPis, p->iFrame+1 );
    pCex->iPo    = p->iPo;
    pCex->iFrame = p->iFrame;
    for ( i = p->nRegs; i < p->nBits; i++ )
        if ( Abc_InfoHasBit(p->pData, i) )
            Abc_InfoSetBit( pCex->pData, pCex->nRegs + i - p->nRegs );
    return pCex;
}

/**Function*************************************************************

  Synopsis    [Derives CEX from comb model.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t * Abc_CexDeriveFromCombModel( int * pModel, int nPis, int nRegs, int iPo )
{
    Abc_Cex_t * pCex;
    int i;
    pCex = Abc_CexAlloc( nRegs, nPis, 1 );
    pCex->iPo = iPo;
    pCex->iFrame = 0;
    for ( i = 0; i < nPis; i++ )
        if ( pModel[i] )
            pCex->pData[i>>5] |= (1<<(i & 31));     
    return pCex;
}

/**Function*************************************************************

  Synopsis    [Prints out the counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_CexPrintStats( Abc_Cex_t * p )
{
    int k, Counter = 0;
    if ( p == NULL )
    {
        printf( "The counter example is NULL.\n" );
        return;
    }
    for ( k = 0; k < p->nBits; k++ )
        Counter += Abc_InfoHasBit(p->pData, k);
    printf( "CEX: iPo = %d  iFrame = %d  nRegs = %d  nPis = %d  nBits = %d  nOnes = %5d (%5.2f %%)\n", 
        p->iPo, p->iFrame, p->nRegs, p->nPis, p->nBits, Counter, 100.0 * Counter / (p->nBits - p->nRegs) );
}

/**Function*************************************************************

  Synopsis    [Prints out the counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_CexPrint( Abc_Cex_t * p )
{
    int i, f, k;
    if ( p == NULL )
    {
        printf( "The counter example is NULL.\n" );
        return;
    }
    Abc_CexPrintStats( p );
    printf( "State    : " );
    for ( k = 0; k < p->nRegs; k++ )
        printf( "%d", Abc_InfoHasBit(p->pData, k) );
    printf( "\n" );
    for ( f = 0; f <= p->iFrame; f++ )
    {
        printf( "Frame %3d : ", f );
        for ( i = 0; i < p->nPis; i++ )
            printf( "%d", Abc_InfoHasBit(p->pData, k++) );
        printf( "\n" );
    }
    assert( k == p->nBits );
}

/**Function*************************************************************

  Synopsis    [Frees the counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_CexFreeP( Abc_Cex_t ** p )
{
    if ( *p == NULL )
        return;
    ABC_FREE( *p );
}

/**Function*************************************************************

  Synopsis    [Frees the counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_CexFree( Abc_Cex_t * p )
{
    ABC_FREE( p );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

