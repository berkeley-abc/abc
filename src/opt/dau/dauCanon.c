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
void Abc_TtConfactorTest7( word * pTruth, int nVars, int N )
{
    word Cof[4][1024];
    int i, nWords = Abc_TtWordNum( nVars );
    int Counter = 0;
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
void Abc_TtConfactorTest2( word * pTruth, int nVars, int N )
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
void Abc_TtConfactorTest3( word * pTruth, int nVars, int N )
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

void Abc_TtConfactorTest4( word * pTruth, int nVars, int N )
{
    word Cof[4][1024];
    int i, j, nWords = Abc_TtWordNum( nVars );
    int Counter = 0, Sum = 0;
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

void Abc_TtConfactorTest6( word * pTruth, int nVars, int N )
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

int Abc_TtConfactorPermNaive( word * pTruth, int i, int nVars )
{
    static word pCopy[1024];
    static word pBest[1024];

    int nWords = Abc_TtWordNum( nVars );

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
    Abc_TtSwapVars( pCopy, nVars, i, i+1 );
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
    Abc_TtSwapVars( pCopy, nVars, i, i+1 );
    if ( Abc_TtCompareRev(pBest, pCopy, nWords) == 1 )
        Abc_TtCopy( pBest, pCopy, nWords, 0 );

    assert( Abc_TtEqual( pTruth, pCopy, nWords ) );
    if ( Abc_TtEqual( pTruth, pBest, nWords ) )
        return 0;
    Abc_TtCopy( pTruth, pBest, nWords, 0 );
    return 1;
}


int Abc_TtConfactorPerm( word * pTruth, int i, int nVars )
{
    int nWords = Abc_TtWordNum( nVars );
    int fComp01, fComp02, fComp03, fComp12, fComp13, fComp23;
    int RetValue = 0;
    fComp23 = Abc_TtCompare2VarCofsRev( pTruth, nWords, i, 2, 3 );
    fComp01 = Abc_TtCompare2VarCofsRev( pTruth, nWords, i, 0, 1 );
    if ( fComp23 >= 1 ) // Cof2 >= Cof3 
    {
        if ( fComp01 >= 1 ) // Cof0 >= Cof1
        {
            fComp13 = Abc_TtCompare2VarCofsRev( pTruth, nWords, i, 1, 3 );
            if ( fComp13 < 1 ) // Cof1 < Cof3 )
                Abc_TtFlip( pTruth, nWords, i + 1 ), RetValue = 1;
        }
        else // Cof0 < Cof1
        {
            fComp03 = Abc_TtCompare2VarCofsRev( pTruth, nWords, i, 0, 3 );
            if ( fComp03 < 1 ) // Cof0 < Cof3 )
            {
                Abc_TtFlip( pTruth, nWords, i );
                Abc_TtFlip( pTruth, nWords, i + 1 ), RetValue = 1;
            }
            else // Cof0 >= Cof3
            {
                if ( fComp23 == 0 )
                    Abc_TtFlip( pTruth, nWords, i ), RetValue = 1;
            }
        }
    }
    else // Cof2 < Cof3 
    {
        if ( fComp01 >= 1 ) // Cof0 >= Cof1
        {
            fComp12 = Abc_TtCompare2VarCofsRev( pTruth, nWords, i, 1, 2 );
            if ( fComp12 < 1 ) // Cof1 < Cof2 )
                Abc_TtFlip( pTruth, nWords, i + 1 ), RetValue = 1;
        }
        else // Cof0 < Cof1
        {
            fComp02 = Abc_TtCompare2VarCofsRev( pTruth, nWords, i, 0, 2 );
            if ( fComp02 == -1 ) // Cof0 < Cof2 )
                Abc_TtFlip( pTruth, nWords, i + 1 );
            Abc_TtFlip( pTruth, nWords, i ), RetValue = 1;
        }
    }

    // perform final swap if needed
    fComp12 = Abc_TtCompare2VarCofsRev( pTruth, nWords, i, 1, 2 );
    if ( fComp12 == 1 ) // Cof1 > Cof2
        Abc_TtSwapVars( pTruth, nVars, i, i+1 ), RetValue = 1;
    return RetValue;
}

void Abc_TtConfactorTest8( word * pTruth, int nVars, int N )
{
    int fVerbose = 0;
    int i;

    if ( fVerbose )
        printf( "\n   " ), Abc_TtPrintHex( pTruth, nVars );

    if ( fVerbose )
    printf( "Round 1\n" );
    for ( i = nVars - 2; i >= 0; i-- )
    {
        if ( Abc_TtConfactorPermNaive( pTruth, i, nVars ) )
        {
            if ( fVerbose )
                printf( "%d  ", i ), Abc_TtPrintHex( pTruth, nVars );
        }
    }

    if ( fVerbose )
    printf( "Round 2\n" );
    for ( i = 0; i < nVars - 1; i++ )
    {
        if ( Abc_TtConfactorPermNaive( pTruth, i, nVars ) )
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
        if ( Abc_TtConfactorPermNaive( pTruth, i, nVars ) )
        {
            if ( fVerbose )
                printf( "%d  ", i ), Abc_TtPrintHex( pTruth, nVars );
        }
    }

    if ( fVerbose )
    printf( "Round 4\n" );
    for ( i = 0; i < nVars - 1; i++ )
    {
        if ( Abc_TtConfactorPermNaive( pTruth, i, nVars ) )
        {
            if ( fVerbose )
                printf( "%d  ", i ), Abc_TtPrintHex( pTruth, nVars );
        }
    }
    i = 0;
}

void Abc_TtConfactorTest10( word * pTruth, int nVars, int N )
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


void Abc_TtConfactorTest( word * pTruth, int nVars, int N )
{
    char pCanonPerm[32];
    static word pCopy1[1024];
    static word pCopy2[1024];
    int nWords = Abc_TtWordNum( nVars );

//        Kit_DsdPrintFromTruth( pTruth, nVars ); printf( "\n" );

//    Abc_TtCopy( pCopy1, pTruth, nWords, 0 );
//    Kit_TruthSemiCanonicize_Yasha( pCopy1, nVars, pCanonPerm );
//        Kit_DsdPrintFromTruth( pCopy1, nVars ); printf( "\n" );

    Abc_TtCopy( pCopy2, pTruth, nWords, 0 );
    Abc_TtSemiCanonicize( pCopy2, nVars, pCanonPerm );
//        Kit_DsdPrintFromTruth( pCopy2, nVars ); printf( "\n" );

//    assert( Abc_TtEqual( pCopy1, pCopy2, nWords ) );
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

