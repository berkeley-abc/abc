/**CFile****************************************************************

  FileName    [bdcSpfd.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Truth-table-based bi-decomposition engine.]

  Synopsis    [The gateway to bi-decomposition.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - January 30, 2007.]

  Revision    [$Id: bdcSpfd.c,v 1.00 2007/01/30 00:00:00 alanmi Exp $]

***********************************************************************/

#include "bdcInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Bdc_Nod_t_ Bdc_Nod_t;
struct Bdc_Nod_t_
{
    unsigned         iFan0g :  8;
    unsigned         iFan0n : 12;
    unsigned         Type   : 12;  // 0-3 = AND; 4 = XOR

    unsigned         iFan1g :  8;
    unsigned         iFan1n : 12;
    unsigned         Weight : 12;

    word             Truth;
};

static word Truths[6] = {
    0xAAAAAAAAAAAAAAAA,
    0xCCCCCCCCCCCCCCCC,
    0xF0F0F0F0F0F0F0F0,
    0xFF00FF00FF00FF00,
    0xFFFF0000FFFF0000,
    0xFFFFFFFF00000000
};

static inline int Bdc_CountOnes( word t )
{
    t =    (t & 0x5555555555555555) + ((t>> 1) & 0x5555555555555555);
    t =    (t & 0x3333333333333333) + ((t>> 2) & 0x3333333333333333);
    t =    (t & 0x0F0F0F0F0F0F0F0F) + ((t>> 4) & 0x0F0F0F0F0F0F0F0F);
    t =    (t & 0x00FF00FF00FF00FF) + ((t>> 8) & 0x00FF00FF00FF00FF);
    t =    (t & 0x0000FFFF0000FFFF) + ((t>>16) & 0x0000FFFF0000FFFF);
    return (t & 0x00000000FFFFFFFF) +  (t>>32);
}

static inline int Bdc_CountSpfd( word t, word f )
{
    int n00 = Bdc_CountOnes( ~t & ~f );
    int n01 = Bdc_CountOnes(  t & ~f );
    int n10 = Bdc_CountOnes( ~t &  f );
    int n11 = Bdc_CountOnes(  t &  f );
    return n00 * n11 + n10 * n01;
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Bdc_SpfdPrint_rec( Bdc_Nod_t * pNode, int Level, Vec_Ptr_t * vLevels )
{
    assert( Level > 0 );
    printf( "(" );

    if ( pNode->Type & 1 )
        printf( "!" );
    if ( pNode->iFan0g == 0 )
        printf( "%c", 'a' + pNode->iFan0n );
    else
    {
        Bdc_Nod_t * pNode0 = (Bdc_Nod_t *)Vec_PtrEntry(vLevels, pNode->iFan0g);
        Bdc_SpfdPrint_rec( pNode0 + pNode->iFan0n, pNode->iFan0g, vLevels );
    }

    if ( pNode->Type & 4 )
        printf( "+" );
    else
        printf( "*" );

    if ( pNode->Type & 2 )
        printf( "!" );
    if ( pNode->iFan1g == 0 )
        printf( "%c", 'a' + pNode->iFan1n );
    else
    {
        Bdc_Nod_t * pNode1 = (Bdc_Nod_t *)Vec_PtrEntry(vLevels, pNode->iFan1g);
        Bdc_SpfdPrint_rec( pNode1 + pNode->iFan1n, pNode->iFan1g, vLevels );
    }

    printf( ")" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Bdc_SpfdPrint( Bdc_Nod_t * pNode, int Level, Vec_Ptr_t * vLevels )
{
    Bdc_SpfdPrint_rec( pNode, Level, vLevels );
    printf( "    %d\n", pNode->Weight );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Bdc_SpfdDecompose( word Truth, int nVars, int nCands, int nGatesMax )
{
    int nSize = nCands * nCands * (nGatesMax + 1) * 5;
    Vec_Ptr_t * vLevels;
    Vec_Int_t * vCounts, * vWeight;
    Bdc_Nod_t * pNode, * pNode0, * pNode1, * pNode2;
    int Count0, Count1, * pPerm;
    int i, j, k, c, n, clk;
    assert( nGatesMax < (1<<8) );
    assert( nCands < (1<<12) );
    assert( (1<<(nVars-1))*(1<<(nVars-1)) < (1<<12) ); // max SPFD

    printf( "Storage size = %d (%d * %d * %d * %d).\n", nSize, nCands, nCands, nGatesMax + 1, 5 );

    printf( "SPFD = %d.\n", Bdc_CountOnes(Truth) * Bdc_CountOnes(~Truth) );

    // consider elementary functions
    if ( Truth == 0 || Truth == ~0 )
    {
        printf( "Function is a constant.\n" );
        return;
    }
    for ( i = 0; i < nVars; i++ )
        if ( Truth == Truths[i] || Truth == ~Truths[i] )
        {
            printf( "Function is an elementary variable.\n" );
            return;
        }

    // allocate
    vLevels = Vec_PtrAlloc( 100 );
    vCounts = Vec_IntAlloc( 100 );
    vWeight = Vec_IntAlloc( 100 );

    // initialize elementary variables
    pNode = ABC_CALLOC( Bdc_Nod_t, nVars );
    for ( i = 0; i < nVars; i++ )
        pNode[i].Truth  = Truths[i];
    for ( i = 0; i < nVars; i++ )
        pNode[i].Weight = Bdc_CountSpfd( pNode[i].Truth, Truth );
    Vec_PtrPush( vLevels, pNode );
    Vec_IntPush( vCounts, nVars );

    // the next level
clk = clock();
    pNode0 = pNode;
    pNode  = ABC_CALLOC( Bdc_Nod_t, 5 * nVars * (nVars - 1) / 2 );
    for ( c = i = 0; i < nVars; i++ )
    for ( j = i+1; j < nVars; j++ )
    {
        pNode[c].Truth =  pNode0[i].Truth &  pNode0[j].Truth;  pNode[c].iFan0n = i; pNode[c].iFan1n = j;  pNode[c++].Type = 0;
        pNode[c].Truth = ~pNode0[i].Truth &  pNode0[j].Truth;  pNode[c].iFan0n = i; pNode[c].iFan1n = j;  pNode[c++].Type = 1;
        pNode[c].Truth =  pNode0[i].Truth & ~pNode0[j].Truth;  pNode[c].iFan0n = i; pNode[c].iFan1n = j;  pNode[c++].Type = 2;
        pNode[c].Truth = ~pNode0[i].Truth & ~pNode0[j].Truth;  pNode[c].iFan0n = i; pNode[c].iFan1n = j;  pNode[c++].Type = 3;
        pNode[c].Truth =  pNode0[i].Truth ^  pNode0[j].Truth;  pNode[c].iFan0n = i; pNode[c].iFan1n = j;  pNode[c++].Type = 4;
    }
    assert( c == 5 * nVars * (nVars - 1) / 2 );
    Vec_PtrPush( vLevels, pNode );
    Vec_IntPush( vCounts, c );
    for ( i = 0; i < c; i++ )
    {
        pNode[i].Weight = Bdc_CountSpfd( pNode[i].Truth, Truth );
//Bdc_SpfdPrint( pNode + i, 1, vLevels );
        if ( Truth == pNode[i].Truth || Truth == ~pNode[i].Truth )
        {
            printf( "Function can be implemented using 1 gate.\n" );
            pNode = NULL;
            goto cleanup;
        }
    }
printf( "Selected %6d gates on level %2d.   ", c, 1 );
Abc_PrintTime( 1, "Time", clock() - clk );


    // iterate through levels
    pNode = ABC_CALLOC( Bdc_Nod_t, nSize );
    for ( n = 2; n <= nGatesMax; n++ )
    {
clk = clock();
        c = 0;
        pNode1 = Vec_PtrEntry( vLevels, n-1 );
        Count1 = Vec_IntEntry( vCounts, n-1 );
        // go through previous levels
        for ( k = 0; k < n-1; k++ )
        {
            pNode0 = Vec_PtrEntry( vLevels, k );
            Count0 = Vec_IntEntry( vCounts, k );
            for ( i = 0; i < Count0; i++ )
            for ( j = 0; j < Count1; j++ )
            {
                pNode[c].Truth =  pNode0[i].Truth &  pNode1[j].Truth;  pNode[c].iFan0g = k; pNode[c].iFan1g = n-1;  pNode[c].iFan0n = i; pNode[c].iFan1n = j;  pNode[c++].Type = 0;
                pNode[c].Truth = ~pNode0[i].Truth &  pNode1[j].Truth;  pNode[c].iFan0g = k; pNode[c].iFan1g = n-1;  pNode[c].iFan0n = i; pNode[c].iFan1n = j;  pNode[c++].Type = 1;
                pNode[c].Truth =  pNode0[i].Truth & ~pNode1[j].Truth;  pNode[c].iFan0g = k; pNode[c].iFan1g = n-1;  pNode[c].iFan0n = i; pNode[c].iFan1n = j;  pNode[c++].Type = 2;
                pNode[c].Truth = ~pNode0[i].Truth & ~pNode1[j].Truth;  pNode[c].iFan0g = k; pNode[c].iFan1g = n-1;  pNode[c].iFan0n = i; pNode[c].iFan1n = j;  pNode[c++].Type = 3;
                pNode[c].Truth =  pNode0[i].Truth ^  pNode1[j].Truth;  pNode[c].iFan0g = k; pNode[c].iFan1g = n-1;  pNode[c].iFan0n = i; pNode[c].iFan1n = j;  pNode[c++].Type = 4;
            }
            assert( c < nSize );
        }
        // go through current level
        for ( i = 0; i < Count1; i++ )
        for ( j = i+1; j < Count1; j++ )
        {
            pNode[c].Truth =  pNode1[i].Truth &  pNode1[j].Truth;  pNode[c].iFan0g = n-1; pNode[c].iFan1g = n-1;  pNode[c].iFan0n = i; pNode[c].iFan1n = j;  pNode[c++].Type = 0;
            pNode[c].Truth = ~pNode1[i].Truth &  pNode1[j].Truth;  pNode[c].iFan0g = n-1; pNode[c].iFan1g = n-1;  pNode[c].iFan0n = i; pNode[c].iFan1n = j;  pNode[c++].Type = 1;
            pNode[c].Truth =  pNode1[i].Truth & ~pNode1[j].Truth;  pNode[c].iFan0g = n-1; pNode[c].iFan1g = n-1;  pNode[c].iFan0n = i; pNode[c].iFan1n = j;  pNode[c++].Type = 2;
            pNode[c].Truth = ~pNode1[i].Truth & ~pNode1[j].Truth;  pNode[c].iFan0g = n-1; pNode[c].iFan1g = n-1;  pNode[c].iFan0n = i; pNode[c].iFan1n = j;  pNode[c++].Type = 3;
            pNode[c].Truth =  pNode1[i].Truth ^  pNode1[j].Truth;  pNode[c].iFan0g = n-1; pNode[c].iFan1g = n-1;  pNode[c].iFan0n = i; pNode[c].iFan1n = j;  pNode[c++].Type = 4;
        }
        assert( c < nSize );
        // sort
        Vec_IntClear( vWeight );
        for ( i = 0; i < c; i++ )
        {
            pNode[i].Weight = Bdc_CountSpfd( pNode[i].Truth, Truth );
//Bdc_SpfdPrint( pNode + i, 1, vLevels );
            Vec_IntPush( vWeight, pNode[i].Weight );

            if ( Truth == pNode[i].Truth || Truth == ~pNode[i].Truth )
            {
                printf( "Function can be implemented using %d gates.\n", n );
                Bdc_SpfdPrint( pNode + i, n, vLevels );
                goto cleanup;
            }
        }
        pPerm = Abc_SortCost( Vec_IntArray(vWeight), c );
        assert( Vec_IntEntry(vWeight, pPerm[0]) <= Vec_IntEntry(vWeight, pPerm[c-1]) );

        printf( "Best SPFD = %d.\n", Vec_IntEntry(vWeight, pPerm[c-1]) );
//        for ( i = 0; i < c; i++ )
//printf( "%d ", Vec_IntEntry(vWeight, pPerm[i]) );

        // choose the best ones
        pNode2 = ABC_CALLOC( Bdc_Nod_t, nCands );
        for ( j = 0, i = c-1; i >= 0; i-- )
        {
            pNode2[j++] = pNode[pPerm[i]];
            if ( j == nCands )
                break;
        }
        ABC_FREE( pPerm );
        Vec_PtrPush( vLevels, pNode2 );
        Vec_IntPush( vCounts, j );

printf( "Selected %6d gates (out of %6d) on level %2d.   ", j, c, n );
Abc_PrintTime( 1, "Time", clock() - clk );

        for ( i = 0; i < 10; i++ )
            Bdc_SpfdPrint( pNode2 + i, n, vLevels );
    }

cleanup:
    ABC_FREE( pNode );
    Vec_PtrForEachEntry( Bdc_Nod_t *, vLevels, pNode, i )
        ABC_FREE( pNode );
    Vec_PtrFree( vLevels );
    Vec_IntFree( vCounts );
    Vec_IntFree( vWeight );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Bdc_SpfdDecomposeTest()
{
    int fTry = 0;
//    word T[17];
//    int i;

//    word Truth    = Truths[0] & ~Truths[3];
//    word Truth    = (Truths[0] & Truths[1]) | (Truths[2] & Truths[3]) | (Truths[4] & Truths[5]);
//    word Truth    = (Truths[0] & Truths[1]) | ((Truths[2] & ~Truths[3]) ^ (Truths[4] & ~Truths[5]));
//    word Truth    = (Truths[0] & Truths[1]) | (Truths[2] & Truths[3]);
    word Truth = 0x9ef7a8d9c7193a0f;
//    word Truth = 0x5052585a0002080a;
    int nVars     =    6;
    int nCands    =  200;// 75;
    int nGatesMax =   20;

    if ( fTry )
    Bdc_SpfdDecompose( Truth, nVars, nCands, nGatesMax );
/*
    for ( i = 0; i < 6; i++ )
        T[i] = Truths[i];
    T[7]  = 0;
    T[8]  = ~T[1]  &  T[3];
    T[9]  = ~T[8]  &  T[0];
    T[10] =  T[1]  &  T[4];
    T[11] =  T[10] &  T[2];
    T[12] =  T[11] &  T[9];
    T[13] = ~T[0]  &  T[5];
    T[14] =  T[2]  &  T[13];
    T[15] = ~T[12] & ~T[14];
    T[16] = ~T[15];
//    if ( T[16] != Truth )
//        printf( "Failed\n" );

    for ( i = 0; i < 17; i++ )
    {
//        printf( "%2d = %3d  ", i, Bdc_CountSpfd(T[i], Truth) );
        printf( "%2d = %3d  ", i, Bdc_CountSpfd(T[i], T[16]) );
        Extra_PrintBinary( stdout, (unsigned *)&T[i], 64 ); printf( "\n" );
    }
//    Extra_PrintBinary( stdout, (unsigned *)&Truth, 64 ); printf( "\n" );
*/
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

