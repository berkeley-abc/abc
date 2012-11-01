/**CFile****************************************************************

  FileName    [dauCanon.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware unmapping.]

  Synopsis    [Canonical form computation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: dauCanon.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "dauInt.h"
#include "misc/util/utilTruth.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Generate reverse bytes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_TtReverseBypes()
{
    int i, k;
    for ( i = 0; i < 256; i++ )
    {
        int Mask = 0;
        for ( k = 0; k < 8; k++ )
            if ( (i >> k) & 1 )
            Mask |= (1 << (7-k));
//        printf( "%3d %3d\n", i, Mask );

        if ( i % 16 == 0 )
            printf( "\n" );
        printf( "%-3d, ", Mask );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_TtCofactorTest7( word * pTruth, int nVars, int N )
{
    word Cof[4][1024];
    int i, nWords = Abc_TtWordNum( nVars );
//    int Counter = 0;
    for ( i = 0; i < nVars-1; i++ )
    {
        Abc_TtCopy( Cof[0], pTruth, nWords, 0 );
        Abc_TtCofactor0( Cof[0], nWords, i );
        Abc_TtCofactor0( Cof[0], nWords, i + 1 );

        Abc_TtCopy( Cof[1], pTruth, nWords, 0 );
        Abc_TtCofactor1( Cof[1], nWords, i );
        Abc_TtCofactor0( Cof[1], nWords, i + 1 );

        Abc_TtCopy( Cof[2], pTruth, nWords, 0 );
        Abc_TtCofactor0( Cof[2], nWords, i );
        Abc_TtCofactor1( Cof[2], nWords, i + 1 );

        Abc_TtCopy( Cof[3], pTruth, nWords, 0 );
        Abc_TtCofactor1( Cof[3], nWords, i );
        Abc_TtCofactor1( Cof[3], nWords, i + 1 );

        if ( i == 5 && N == 4 )
        {
            printf( "\n" );
            Abc_TtPrintHex( Cof[0], nVars );
            Abc_TtPrintHex( Cof[1], nVars );
            Abc_TtPrintHex( Cof[2], nVars );
            Abc_TtPrintHex( Cof[3], nVars );
        }

        assert( Abc_TtCompareRev(Cof[0], Cof[1], nWords) == Abc_TtCompare2VarCofsRev(pTruth, nWords, i, 0, 1) );
        assert( Abc_TtCompareRev(Cof[0], Cof[2], nWords) == Abc_TtCompare2VarCofsRev(pTruth, nWords, i, 0, 2) );
        assert( Abc_TtCompareRev(Cof[0], Cof[3], nWords) == Abc_TtCompare2VarCofsRev(pTruth, nWords, i, 0, 3) );
        assert( Abc_TtCompareRev(Cof[1], Cof[2], nWords) == Abc_TtCompare2VarCofsRev(pTruth, nWords, i, 1, 2) );
        assert( Abc_TtCompareRev(Cof[1], Cof[3], nWords) == Abc_TtCompare2VarCofsRev(pTruth, nWords, i, 1, 3) );
        assert( Abc_TtCompareRev(Cof[2], Cof[3], nWords) == Abc_TtCompare2VarCofsRev(pTruth, nWords, i, 2, 3) );
/*
        Counter += Abc_TtCompare(Cof[0], Cof[1], nWords);
        Counter += Abc_TtCompare(Cof[0], Cof[2], nWords);
        Counter += Abc_TtCompare(Cof[0], Cof[3], nWords);
        Counter += Abc_TtCompare(Cof[1], Cof[2], nWords);
        Counter += Abc_TtCompare(Cof[1], Cof[3], nWords);
        Counter += Abc_TtCompare(Cof[2], Cof[3], nWords);

        Counter += Abc_TtCompare2VarCofs(pTruth, nWords, i, 0, 1);
        Counter += Abc_TtCompare2VarCofs(pTruth, nWords, i, 0, 2);
        Counter += Abc_TtCompare2VarCofs(pTruth, nWords, i, 0, 3);
        Counter += Abc_TtCompare2VarCofs(pTruth, nWords, i, 1, 2);
        Counter += Abc_TtCompare2VarCofs(pTruth, nWords, i, 1, 3);
        Counter += Abc_TtCompare2VarCofs(pTruth, nWords, i, 2, 3);
*/ 
    }
}
void Abc_TtCofactorTest2( word * pTruth, int nVars, int N )
{
//    word Cof[4][1024];
    int i, j, nWords = Abc_TtWordNum( nVars );
    int Counter = 0;
    for ( i = 0; i < nVars-1; i++ )
    for ( j = i+1; j < nVars; j++ )
    {
/*
        Abc_TtCopy( Cof[0], pTruth, nWords, 0 );
        Abc_TtCofactor0( Cof[0], nWords, i );
        Abc_TtCofactor0( Cof[0], nWords, j );

        Abc_TtCopy( Cof[1], pTruth, nWords, 0 );
        Abc_TtCofactor1( Cof[1], nWords, i );
        Abc_TtCofactor0( Cof[1], nWords, j );

        Abc_TtCopy( Cof[2], pTruth, nWords, 0 );
        Abc_TtCofactor0( Cof[2], nWords, i );
        Abc_TtCofactor1( Cof[2], nWords, j );

        Abc_TtCopy( Cof[3], pTruth, nWords, 0 );
        Abc_TtCofactor1( Cof[3], nWords, i );
        Abc_TtCofactor1( Cof[3], nWords, j );
*/
/*
        if ( i == 0 && j == 1 && N == 0 )
        {
            printf( "\n" );
            Abc_TtPrintHexSpecial( Cof[0], nVars ); printf( "\n" );
            Abc_TtPrintHexSpecial( Cof[1], nVars ); printf( "\n" );
            Abc_TtPrintHexSpecial( Cof[2], nVars ); printf( "\n" );
            Abc_TtPrintHexSpecial( Cof[3], nVars ); printf( "\n" );
        }
*/
/*
        assert( Abc_TtEqual(Cof[0], Cof[1], nWords) == Abc_TtCheckEqualCofs(pTruth, nWords, i, j, 0, 1) );
        assert( Abc_TtEqual(Cof[0], Cof[2], nWords) == Abc_TtCheckEqualCofs(pTruth, nWords, i, j, 0, 2) );
        assert( Abc_TtEqual(Cof[0], Cof[3], nWords) == Abc_TtCheckEqualCofs(pTruth, nWords, i, j, 0, 3) );
        assert( Abc_TtEqual(Cof[1], Cof[2], nWords) == Abc_TtCheckEqualCofs(pTruth, nWords, i, j, 1, 2) );
        assert( Abc_TtEqual(Cof[1], Cof[3], nWords) == Abc_TtCheckEqualCofs(pTruth, nWords, i, j, 1, 3) );
        assert( Abc_TtEqual(Cof[2], Cof[3], nWords) == Abc_TtCheckEqualCofs(pTruth, nWords, i, j, 2, 3) );
*/

        Counter += Abc_TtCheckEqualCofs(pTruth, nWords, i, j, 0, 1);
        Counter += Abc_TtCheckEqualCofs(pTruth, nWords, i, j, 0, 2);
        Counter += Abc_TtCheckEqualCofs(pTruth, nWords, i, j, 0, 3);
        Counter += Abc_TtCheckEqualCofs(pTruth, nWords, i, j, 1, 2);
        Counter += Abc_TtCheckEqualCofs(pTruth, nWords, i, j, 1, 3);
        Counter += Abc_TtCheckEqualCofs(pTruth, nWords, i, j, 2, 3);
/*
        Counter += Abc_TtEqual(Cof[0], Cof[1], nWords);
        Counter += Abc_TtEqual(Cof[0], Cof[2], nWords);
        Counter += Abc_TtEqual(Cof[0], Cof[3], nWords);
        Counter += Abc_TtEqual(Cof[1], Cof[2], nWords);
        Counter += Abc_TtEqual(Cof[1], Cof[3], nWords);
        Counter += Abc_TtEqual(Cof[2], Cof[3], nWords);
*/
    }
}
void Abc_TtCofactorTest3( word * pTruth, int nVars, int N )
{
    word Cof[4][1024];
    int i, j, nWords = Abc_TtWordNum( nVars );
    for ( i = 0; i < nVars-1; i++ )
    for ( j = i+1; j < nVars; j++ )
    {
        Abc_TtCopy( Cof[0], pTruth, nWords, 0 );
        Abc_TtCofactor0( Cof[0], nWords, i );
        Abc_TtCofactor0( Cof[0], nWords, j );

        Abc_TtCopy( Cof[1], pTruth, nWords, 0 );
        Abc_TtCofactor1( Cof[1], nWords, i );
        Abc_TtCofactor0( Cof[1], nWords, j );

        Abc_TtCopy( Cof[2], pTruth, nWords, 0 );
        Abc_TtCofactor0( Cof[2], nWords, i );
        Abc_TtCofactor1( Cof[2], nWords, j );

        Abc_TtCopy( Cof[3], pTruth, nWords, 0 );
        Abc_TtCofactor1( Cof[3], nWords, i );
        Abc_TtCofactor1( Cof[3], nWords, j );

        assert( Abc_TtEqual(Cof[0], Cof[1], nWords) == Abc_TtCheckEqualCofs(pTruth, nWords, i, j, 0, 1) );
        assert( Abc_TtEqual(Cof[0], Cof[2], nWords) == Abc_TtCheckEqualCofs(pTruth, nWords, i, j, 0, 2) );
        assert( Abc_TtEqual(Cof[0], Cof[3], nWords) == Abc_TtCheckEqualCofs(pTruth, nWords, i, j, 0, 3) );
        assert( Abc_TtEqual(Cof[1], Cof[2], nWords) == Abc_TtCheckEqualCofs(pTruth, nWords, i, j, 1, 2) );
        assert( Abc_TtEqual(Cof[1], Cof[3], nWords) == Abc_TtCheckEqualCofs(pTruth, nWords, i, j, 1, 3) );
        assert( Abc_TtEqual(Cof[2], Cof[3], nWords) == Abc_TtCheckEqualCofs(pTruth, nWords, i, j, 2, 3) );
    }
}

void Abc_TtCofactorTest4( word * pTruth, int nVars, int N )
{
    word Cof[4][1024];
    int i, j, nWords = Abc_TtWordNum( nVars );
    int Sum = 0;
    for ( i = 0; i < nVars-1; i++ )
    for ( j = i+1; j < nVars; j++ )
    {
        Abc_TtCopy( Cof[0], pTruth, nWords, 0 );
        Abc_TtCofactor0( Cof[0], nWords, i );
        Abc_TtCofactor0( Cof[0], nWords, j );

        Abc_TtCopy( Cof[1], pTruth, nWords, 0 );
        Abc_TtCofactor1( Cof[1], nWords, i );
        Abc_TtCofactor0( Cof[1], nWords, j );

        Abc_TtCopy( Cof[2], pTruth, nWords, 0 );
        Abc_TtCofactor0( Cof[2], nWords, i );
        Abc_TtCofactor1( Cof[2], nWords, j );

        Abc_TtCopy( Cof[3], pTruth, nWords, 0 );
        Abc_TtCofactor1( Cof[3], nWords, i );
        Abc_TtCofactor1( Cof[3], nWords, j );


        Sum = 0;
        Sum += Abc_TtEqual(Cof[0], Cof[1], nWords);
        Sum += Abc_TtEqual(Cof[0], Cof[2], nWords);
        Sum += Abc_TtEqual(Cof[0], Cof[3], nWords);
        Sum += Abc_TtEqual(Cof[1], Cof[2], nWords);
        Sum += Abc_TtEqual(Cof[1], Cof[3], nWords);
        Sum += Abc_TtEqual(Cof[2], Cof[3], nWords);

        assert( Abc_TtEqual(Cof[0], Cof[1], nWords) == Abc_TtCheckEqualCofs(pTruth, nWords, i, j, 0, 1) );
        assert( Abc_TtEqual(Cof[0], Cof[2], nWords) == Abc_TtCheckEqualCofs(pTruth, nWords, i, j, 0, 2) );
        assert( Abc_TtEqual(Cof[0], Cof[3], nWords) == Abc_TtCheckEqualCofs(pTruth, nWords, i, j, 0, 3) );
        assert( Abc_TtEqual(Cof[1], Cof[2], nWords) == Abc_TtCheckEqualCofs(pTruth, nWords, i, j, 1, 2) );
        assert( Abc_TtEqual(Cof[1], Cof[3], nWords) == Abc_TtCheckEqualCofs(pTruth, nWords, i, j, 1, 3) );
        assert( Abc_TtEqual(Cof[2], Cof[3], nWords) == Abc_TtCheckEqualCofs(pTruth, nWords, i, j, 2, 3) );
    }
}

void Abc_TtCofactorTest6( word * pTruth, int nVars, int N )
{
//    word Cof[4][1024];
    int i, nWords = Abc_TtWordNum( nVars );
//    if ( N != 30 )
//        return;
    printf( "\n   " );
    Abc_TtPrintHex( pTruth, nVars );
//    Kit_DsdPrintFromTruth( pTruth, nVars ); printf( "\n" );

    for ( i = nVars - 1; i >= 0; i-- )
    {
/*
        Abc_TtCopy( Cof[0], pTruth, nWords, 0 );
        Abc_TtCofactor0( Cof[0], nWords, i );
        printf( "-  " );
        Abc_TtPrintHex( Cof[0], nVars );

        Abc_TtCopy( Cof[1], pTruth, nWords, 0 );
        Abc_TtCofactor1( Cof[1], nWords, i );
        printf( "+  " );
        Abc_TtPrintHex( Cof[1], nVars );
*/
        if ( Abc_TtCompare1VarCofsRev( pTruth, nWords, i ) == -1 )
        {
            printf( "%d  ", i );
            Abc_TtFlip( pTruth, nWords, i );
            Abc_TtPrintHex( pTruth, nVars );
//            Kit_DsdPrintFromTruth( pTruth, nVars ); printf( "\n" );
        }


/*
        Abc_TtCopy( Cof[0], pTruth, nWords, 0 );
        Abc_TtCofactor0( Cof[0], nWords, i );

        Abc_TtCopy( Cof[1], pTruth, nWords, 0 );
        Abc_TtCofactor1( Cof[1], nWords, i );

        assert( Abc_TtCompareRev(Cof[0], Cof[1], nWords) == Abc_TtCompare1VarCofsRev(pTruth, nWords, i) );
*/
    }
    i = 0;
}

int Abc_TtCofactorPermNaive( word * pTruth, int i, int nWords, int fSwapOnly )
{
    static word pCopy[1024];
    static word pBest[1024];

    if ( fSwapOnly )
    {
        Abc_TtCopy( pCopy, pTruth, nWords, 0 );
        Abc_TtSwapAdjacent( pCopy, nWords, i );
        if ( Abc_TtCompareRev(pTruth, pCopy, nWords) == 1 )
        {
            Abc_TtCopy( pTruth, pCopy, nWords, 0 );
            return 1;
        }
        return 0;
    }

    // save two copies
    Abc_TtCopy( pCopy, pTruth, nWords, 0 );
    Abc_TtCopy( pBest, pTruth, nWords, 0 );

    // PXY
    // 001
    Abc_TtFlip( pCopy, nWords, i );
    if ( Abc_TtCompareRev(pBest, pCopy, nWords) == 1 )
        Abc_TtCopy( pBest, pCopy, nWords, 0 );

    // PXY
    // 011
    Abc_TtFlip( pCopy, nWords, i+1 );
    if ( Abc_TtCompareRev(pBest, pCopy, nWords) == 1 )
        Abc_TtCopy( pBest, pCopy, nWords, 0 );

    // PXY
    // 010
    Abc_TtFlip( pCopy, nWords, i );
    if ( Abc_TtCompareRev(pBest, pCopy, nWords) == 1 )
        Abc_TtCopy( pBest, pCopy, nWords, 0 );

    // PXY
    // 110
    Abc_TtSwapAdjacent( pCopy, nWords, i );
    if ( Abc_TtCompareRev(pBest, pCopy, nWords) == 1 )
        Abc_TtCopy( pBest, pCopy, nWords, 0 );

    // PXY
    // 111
    Abc_TtFlip( pCopy, nWords, i+1 );
    if ( Abc_TtCompareRev(pBest, pCopy, nWords) == 1 )
        Abc_TtCopy( pBest, pCopy, nWords, 0 );

    // PXY
    // 101
    Abc_TtFlip( pCopy, nWords, i );
    if ( Abc_TtCompareRev(pBest, pCopy, nWords) == 1 )
        Abc_TtCopy( pBest, pCopy, nWords, 0 );

    // PXY
    // 100
    Abc_TtFlip( pCopy, nWords, i+1 );
    if ( Abc_TtCompareRev(pBest, pCopy, nWords) == 1 )
        Abc_TtCopy( pBest, pCopy, nWords, 0 );

    // PXY
    // 000
    Abc_TtSwapAdjacent( pCopy, nWords, i );
    if ( Abc_TtCompareRev(pBest, pCopy, nWords) == 1 )
        Abc_TtCopy( pBest, pCopy, nWords, 0 );

    assert( Abc_TtEqual( pTruth, pCopy, nWords ) );
    if ( Abc_TtEqual( pTruth, pBest, nWords ) )
        return 0;
    assert( Abc_TtCompareRev(pTruth, pBest, nWords) == 1 );
    Abc_TtCopy( pTruth, pBest, nWords, 0 );
    return 1;
}


int Abc_TtCofactorPerm( word * pTruth, int i, int nWords, char * pCanonPerm, unsigned * puCanonPhase, int fSwapOnly )
{
    static word pCopy1[1024];
    int fComp01, fComp02, fComp03, fComp12, fComp13, fComp23;
    unsigned uPhaseInit = *puCanonPhase;
    int RetValue = 0;

    if ( fSwapOnly )
    {
        fComp12 = Abc_TtCompare2VarCofsRev( pTruth, nWords, i, 1, 2 );
        if ( fComp12 < 0 ) // Cof1 < Cof2
        {
            Abc_TtSwapAdjacent( pTruth, nWords, i );
            RetValue = 1;

            if ( ((*puCanonPhase >> i) & 1) != ((*puCanonPhase >> (i+1)) & 1) )
            {
                *puCanonPhase ^= (1 << i);
                *puCanonPhase ^= (1 << (i+1));
            }

            ABC_SWAP( int, pCanonPerm[i], pCanonPerm[i+1] );
        }
        return RetValue;
    }

    Abc_TtCopy( pCopy1, pTruth, nWords, 0 );
  
    fComp01 = Abc_TtCompare2VarCofsRev( pTruth, nWords, i, 0, 1 );
    fComp23 = Abc_TtCompare2VarCofsRev( pTruth, nWords, i, 2, 3 );
    if ( fComp23 >= 0 ) // Cof2 >= Cof3 
    {
        if ( fComp01 >= 0 ) // Cof0 >= Cof1
        {
            fComp13 = Abc_TtCompare2VarCofsRev( pTruth, nWords, i, 1, 3 );
            if ( fComp13 < 0 ) // Cof1 < Cof3 
            {
                Abc_TtFlip( pTruth, nWords, i + 1 );
                *puCanonPhase ^= (1 << (i+1));
                RetValue = 1;
            }
            else if ( fComp13 == 0 ) // Cof1 == Cof3 
            {
                fComp02 = Abc_TtCompare2VarCofsRev( pTruth, nWords, i, 0, 2 );
                if ( fComp02 < 0 )
                {
                    Abc_TtFlip( pTruth, nWords, i + 1 );
                    *puCanonPhase ^= (1 << (i+1));
                    RetValue = 1;
                }
            }
            // else   Cof1 > Cof3 -- do nothing
        }
        else // Cof0 < Cof1
        {
            fComp03 = Abc_TtCompare2VarCofsRev( pTruth, nWords, i, 0, 3 );
            if ( fComp03 < 0 ) // Cof0 < Cof3
            {
                Abc_TtFlip( pTruth, nWords, i );
                Abc_TtFlip( pTruth, nWords, i + 1 );
                *puCanonPhase ^= (1 << i);
                *puCanonPhase ^= (1 << (i+1));
                RetValue = 1;
            }
            else //  Cof0 >= Cof3
            {
                if ( fComp23 == 0 ) // can flip Cof0 and Cof1
                {
                    Abc_TtFlip( pTruth, nWords, i );
                    *puCanonPhase ^= (1 << i);
                    RetValue = 1;
                }
            }
        }
    }
    else // Cof2 < Cof3 
    {
        if ( fComp01 >= 0 ) // Cof0 >= Cof1
        {
            fComp12 = Abc_TtCompare2VarCofsRev( pTruth, nWords, i, 1, 2 );
            if ( fComp12 > 0 ) // Cof1 > Cof2 
            {
                Abc_TtFlip( pTruth, nWords, i );
                *puCanonPhase ^= (1 << i);
            }
            else if ( fComp12 == 0 ) // Cof1 == Cof2 
            {
                Abc_TtFlip( pTruth, nWords, i );
                Abc_TtFlip( pTruth, nWords, i + 1 );
                *puCanonPhase ^= (1 << i);
                *puCanonPhase ^= (1 << (i+1));
            }
            else // Cof1 < Cof2
            {
                Abc_TtFlip( pTruth, nWords, i + 1 );
                *puCanonPhase ^= (1 << (i+1));
                if ( fComp01 == 0 )
                {
                    Abc_TtFlip( pTruth, nWords, i );
                    *puCanonPhase ^= (1 << i);
                }
            }
        }
        else // Cof0 < Cof1
        {
            fComp02 = Abc_TtCompare2VarCofsRev( pTruth, nWords, i, 0, 2 );
            if ( fComp02 == -1 ) // Cof0 < Cof2 
            {
                Abc_TtFlip( pTruth, nWords, i );
                Abc_TtFlip( pTruth, nWords, i + 1 );
                *puCanonPhase ^= (1 << i);
                *puCanonPhase ^= (1 << (i+1));
            }
            else if ( fComp02 == 0 ) // Cof0 == Cof2
            {
                fComp13 = Abc_TtCompare2VarCofsRev( pTruth, nWords, i, 1, 3 );
                if ( fComp13 >= 0 ) // Cof1 >= Cof3 
                {
                    Abc_TtFlip( pTruth, nWords, i );
                    *puCanonPhase ^= (1 << i);
                }
                else // Cof1 < Cof3 
                {
                    Abc_TtFlip( pTruth, nWords, i );
                    Abc_TtFlip( pTruth, nWords, i + 1 );
                    *puCanonPhase ^= (1 << i);
                    *puCanonPhase ^= (1 << (i+1));
                }
            }
            else // Cof0 > Cof2
            {
                Abc_TtFlip( pTruth, nWords, i );
                *puCanonPhase ^= (1 << i);
            }
        }
        RetValue = 1;
    }
    // perform final swap if needed
    fComp12 = Abc_TtCompare2VarCofsRev( pTruth, nWords, i, 1, 2 );
    if ( fComp12 < 0 ) // Cof1 < Cof2
    {
        Abc_TtSwapAdjacent( pTruth, nWords, i );
        RetValue = 1;

        if ( ((*puCanonPhase >> i) & 1) != ((*puCanonPhase >> (i+1)) & 1) )
        {
            *puCanonPhase ^= (1 << i);
            *puCanonPhase ^= (1 << (i+1));
        }

        ABC_SWAP( int, pCanonPerm[i], pCanonPerm[i+1] );
    }

    if ( RetValue == 1 )
    {
        if ( Abc_TtCompareRev(pTruth, pCopy1, nWords) == 1 ) // made it worse
        {
            Abc_TtCopy( pTruth, pCopy1, nWords, 0 );
            // undo the flips
            *puCanonPhase = uPhaseInit; 
            // undo the swap
            if ( fComp12 < 0 ) // Cof1 < Cof2
                ABC_SWAP( int, pCanonPerm[i], pCanonPerm[i+1] );
            RetValue = 0;
        }
    }
    return RetValue;
}


void Abc_TtCofactorTest__( word * pTruth, int nVars, int N )
{
    char pCanonPerm[16];
    unsigned uCanonPhase;
    static word pCopy1[1024];
    static word pCopy2[1024];
    int i, nWords = Abc_TtWordNum( nVars );
    static int Counter = 0;

//    pTruth[0] = (s_Truths6[0] & s_Truths6[1]) | s_Truths6[2];
//    nVars = 3;

/*
    printf( "\n" );
    Kit_DsdPrintFromTruth( pTruth, nVars ); printf( "\n" );
    Abc_TtPrintBinary( pTruth, nVars );
    printf( "\n" );
*/

//    for ( i = nVars - 2; i >= 0; i-- )
    for ( i = 3; i < nVars - 1; i++ )
    {
/*
        word Cof0s = Abc_Tt6Cof0( pTruth[0], i+1 );
        word Cof1s = Abc_Tt6Cof1( pTruth[0], i+1 );

        word Cof0 = Abc_Tt6Cof0( Cof0s, i );
        word Cof1 = Abc_Tt6Cof1( Cof0s, i );
        word Cof2 = Abc_Tt6Cof0( Cof1s, i );
        word Cof3 = Abc_Tt6Cof1( Cof1s, i );

        Abc_TtPrintBinary( &Cof0, 6 );
        Abc_TtPrintBinary( &Cof1, 6 );
        Abc_TtPrintBinary( &Cof2, 6 );
        Abc_TtPrintBinary( &Cof3, 6 );

        printf( "01 = %d\n", Abc_TtCompare2VarCofsRev(pTruth, nWords, i, 0, 1) );
        printf( "02 = %d\n", Abc_TtCompare2VarCofsRev(pTruth, nWords, i, 0, 2) );
        printf( "03 = %d\n", Abc_TtCompare2VarCofsRev(pTruth, nWords, i, 0, 3) );
        printf( "12 = %d\n", Abc_TtCompare2VarCofsRev(pTruth, nWords, i, 1, 2) );
        printf( "13 = %d\n", Abc_TtCompare2VarCofsRev(pTruth, nWords, i, 1, 3) );
        printf( "23 = %d\n", Abc_TtCompare2VarCofsRev(pTruth, nWords, i, 2, 3) );

        if ( i == 0 && N == 74 )
        {
            int s = 0;
            continue;
        }
*/
        Abc_TtCopy( pCopy1, pTruth, nWords, 0 );
        Abc_TtCofactorPermNaive( pCopy1, i, nWords, 0 );

        Abc_TtCopy( pCopy2, pTruth, nWords, 0 );
        Abc_TtCofactorPerm( pCopy2, i, nWords, pCanonPerm, &uCanonPhase, 0 );

//        assert( Abc_TtEqual( pCopy1, pCopy2, nWords ) );
        if ( !Abc_TtEqual( pCopy1, pCopy2, nWords ) )
            Counter++;

    }
    if ( Counter % 1000 == 0 )
        printf( "%d ", Counter );

}



void Abc_TtCofactorTest8( word * pTruth, int nVars, int N )
{
    int fVerbose = 0;
    int i;
    int nWords = Abc_TtWordNum( nVars );

    if ( fVerbose )
        printf( "\n   " ), Abc_TtPrintHex( pTruth, nVars );

    if ( fVerbose )
    printf( "Round 1\n" );
    for ( i = nVars - 2; i >= 0; i-- )
    {
        if ( Abc_TtCofactorPermNaive( pTruth, i, nWords, 0 ) )
        {
            if ( fVerbose )
                printf( "%d  ", i ), Abc_TtPrintHex( pTruth, nVars );
        }
    }

    if ( fVerbose )
    printf( "Round 2\n" );
    for ( i = 0; i < nVars - 1; i++ )
    {
        if ( Abc_TtCofactorPermNaive( pTruth, i, nWords, 0 ) )
        {
            if ( fVerbose )
                printf( "%d  ", i ), Abc_TtPrintHex( pTruth, nVars );
        }
    }

    return;

    if ( fVerbose )
    printf( "Round 3\n" );
    for ( i = nVars - 2; i >= 0; i-- )
    {
        if ( Abc_TtCofactorPermNaive( pTruth, i, nWords, 0 ) )
        {
            if ( fVerbose )
                printf( "%d  ", i ), Abc_TtPrintHex( pTruth, nVars );
        }
    }

    if ( fVerbose )
    printf( "Round 4\n" );
    for ( i = 0; i < nVars - 1; i++ )
    {
        if ( Abc_TtCofactorPermNaive( pTruth, i, nWords, 0 ) )
        {
            if ( fVerbose )
                printf( "%d  ", i ), Abc_TtPrintHex( pTruth, nVars );
        }
    }
    i = 0;
}

void Abc_TtCofactorTest10( word * pTruth, int nVars, int N )
{
    static word pCopy1[1024];
    static word pCopy2[1024];
    int nWords = Abc_TtWordNum( nVars );
    int i;

    for ( i = 0; i < nVars - 1; i++ )
    {
//        Kit_DsdPrintFromTruth( pTruth, nVars ); printf( "\n" );

        Abc_TtCopy( pCopy1, pTruth, nWords, 0 );
        Abc_TtSwapAdjacent( pCopy1, nWords, i );
//        Kit_DsdPrintFromTruth( pCopy1, nVars ); printf( "\n" );

        Abc_TtCopy( pCopy2, pTruth, nWords, 0 );
        Abc_TtSwapVars( pCopy2, nVars, i, i+1 );
//        Kit_DsdPrintFromTruth( pCopy2, nVars ); printf( "\n" );

        assert( Abc_TtEqual( pCopy1, pCopy2, nWords ) );
    }
}


void Abc_TtCofactorTest111( word * pTruth, int nVars, int N )
{
    char pCanonPerm[32];
    static word pCopy1[1024];
    static word pCopy2[1024];
    int nWords = Abc_TtWordNum( nVars );

//        Kit_DsdPrintFromTruth( pTruth, nVars ); printf( "\n" );

    Abc_TtCopy( pCopy1, pTruth, nWords, 0 );
//    Kit_TruthSemiCanonicize_Yasha( pCopy1, nVars, pCanonPerm );
//        Kit_DsdPrintFromTruth( pCopy1, nVars ); printf( "\n" );

    Abc_TtCopy( pCopy2, pTruth, nWords, 0 );
    Abc_TtSemiCanonicize( pCopy2, nVars, pCanonPerm, NULL );
//        Kit_DsdPrintFromTruth( pCopy2, nVars ); printf( "\n" );

    assert( Abc_TtEqual( pCopy1, pCopy2, nWords ) );
}




void Abc_TtCofactorMinimize( word * pTruth, int nVars, int N )
{
    char pCanonPerm[16];
    unsigned uCanonPhase;
    int i, fVerbose = 0;
    int nWords = Abc_TtWordNum( nVars );

    if ( fVerbose )
        printf( "\n   " ), Abc_TtPrintHex( pTruth, nVars );

    if ( fVerbose )
    printf( "Round 1\n" );
    for ( i = nVars - 2; i >= 0; i-- )
    {
        if ( Abc_TtCofactorPerm( pTruth, i, nWords, pCanonPerm, &uCanonPhase, 0 ) )
        {
            if ( fVerbose )
                printf( "%d  ", i ), Abc_TtPrintHex( pTruth, nVars );
        }
    }

    if ( fVerbose )
    printf( "Round 2\n" );
    for ( i = 0; i < nVars - 1; i++ )
    {
        if ( Abc_TtCofactorPerm( pTruth, i, nWords, pCanonPerm, &uCanonPhase, 0 ) )
        {
            if ( fVerbose )
                printf( "%d  ", i ), Abc_TtPrintHex( pTruth, nVars );
        }
    }
}


void Abc_TtCofactorVerify( word * pTruth, int nVars, char * pCanonPerm, unsigned uCanonPhase )
{
    int i, k, nWords = Abc_TtWordNum( nVars );
    if ( (uCanonPhase >> nVars) & 1 )
        Abc_TtNot( pTruth, nWords );
    for ( i = 0; i < nVars; i++ )
        if ( (uCanonPhase >> i) & 1 )
            Abc_TtFlip( pTruth, nWords, i );
    for ( i = 0; i < nVars; i++ )
    {
        for ( k = i; k < nVars; k++ )
            if ( pCanonPerm[k] == i )
                break;
        assert( k < nVars );
        if ( i == k )
            continue;
        Abc_TtSwapVars( pTruth, nVars, i, k );
        ABC_SWAP( int, pCanonPerm[i], pCanonPerm[k] );
    }
}

//#define CANON_VERIFY

void Abc_TtCofactorTest( word * pTruth, int nVars, int N )
{
    int pStoreIn[17];
    char pCanonPerm[16];
    unsigned uCanonPhase;
    int i, nWords = Abc_TtWordNum( nVars );

#ifdef CANON_VERIFY
    char pCanonPermCopy[16];
    static word pCopy1[1024];
    static word pCopy2[1024];
    Abc_TtCopy( pCopy1, pTruth, nWords, 0 );
#endif

    uCanonPhase = Abc_TtSemiCanonicize( pTruth, nVars, pCanonPerm, pStoreIn );

    for ( i = nVars - 2; i >= 0; i-- )
        if ( pStoreIn[i] == pStoreIn[i+1] )
            Abc_TtCofactorPerm( pTruth, i, nWords, pCanonPerm, &uCanonPhase, pStoreIn[i] != pStoreIn[nVars]/2 );
//            Abc_TtCofactorPermNaive( pTruth, i, nWords, pStoreIn[i] != pStoreIn[nVars]/2 );

    for ( i = 1; i < nVars - 1; i++ )
        if ( pStoreIn[i] == pStoreIn[i+1] )
            Abc_TtCofactorPerm( pTruth, i, nWords, pCanonPerm, &uCanonPhase, pStoreIn[i] != pStoreIn[nVars]/2 );
//            Abc_TtCofactorPermNaive( pTruth, i, nWords, pStoreIn[i] != pStoreIn[nVars]/2 );

    for ( i = nVars - 3; i >= 0; i-- )
        if ( pStoreIn[i] == pStoreIn[i+1] )
            Abc_TtCofactorPerm( pTruth, i, nWords, pCanonPerm, &uCanonPhase, pStoreIn[i] != pStoreIn[nVars]/2 );
//            Abc_TtCofactorPermNaive( pTruth, i, nWords, pStoreIn[i] != pStoreIn[nVars]/2 );

    for ( i = 1; i < nVars - 1; i++ )
        if ( pStoreIn[i] == pStoreIn[i+1] )
            Abc_TtCofactorPerm( pTruth, i, nWords, pCanonPerm, &uCanonPhase, pStoreIn[i] != pStoreIn[nVars]/2 );
//            Abc_TtCofactorPermNaive( pTruth, i, nWords, pStoreIn[i] != pStoreIn[nVars]/2 );

#ifdef CANON_VERIFY
    Abc_TtCopy( pCopy2, pTruth, nWords, 0 );
    memcpy( pCanonPermCopy, pCanonPerm, sizeof(char) * nVars );
    Abc_TtCofactorVerify( pCopy2, nVars, pCanonPermCopy, uCanonPhase );
    if ( !Abc_TtEqual( pCopy1, pCopy2, nWords ) )
        printf( "Canonical form verification failed!\n" );
#endif
/*
    if ( !Abc_TtEqual( pCopy1, pCopy2, nWords ) )
    {
        Kit_DsdPrintFromTruth( pCopy1, nVars ); printf( "\n" );
        Kit_DsdPrintFromTruth( pCopy2, nVars ); printf( "\n" );
        i = 0;
    }
*/
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

