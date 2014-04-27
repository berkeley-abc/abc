/**CFile****************************************************************

  FileName    [extraUtilEnum.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [extra]

  Synopsis    [Function enumeration.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: extraUtilEnum.c,v 1.0 2003/02/01 00:00:00 alanmi Exp $]

***********************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "misc/vec/vec.h"
#include "misc/vec/vecHsh.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_GetFirst( int * pnVars, int * pnMints, int * pnFuncs, unsigned * pVars, unsigned * pMints, unsigned * pFuncs )
{
    int nVars  = 8;
    int nMints = 16;
    int nFuncs = 8;
    char * pMintStrs[16] = { 
        "1-1-1-1-",
        "1-1--11-",
        "1-1-1--1",
        "1-1--1-1",

        "-11-1-1-",
        "-11--11-",
        "-11-1--1",
        "-11--1-1",

        "1--11-1-",
        "1--1-11-",
        "1--11--1",
        "1--1-1-1",

        "-1-11-1-",
        "-1-1-11-",
        "-1-11--1",
        "-1-1-1-1"
    };
    char * pFuncStrs[8] = { 
        "1111101011111010",
        "0000010100000101",
        "1111110010101001",
        "0000001101010110",
        "1111111111001101",
        "0000000000110010",
        "1111111111111110",
        "0000000000000001",
    };
    int i, k;
    *pnVars  = nVars;
    *pnMints = nMints;
    *pnFuncs = nFuncs;
    // extract mints
    for ( i = 0; i < nMints; i++ )
        for ( k = 0; k < nVars; k++ )
            if ( pMintStrs[i][k] == '1' )
                pMints[i] |= (1 << k), pVars[k] |= (1 << i);
    // extract funcs
    for ( i = 0; i < nFuncs; i++ )
        for ( k = 0; k < nMints; k++ )
            if ( pFuncStrs[i][k] == '1' )
                pFuncs[i] |= (1 << k);
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_GetSecond( int * pnVars, int * pnMints, int * pnFuncs, unsigned * pVars, unsigned * pMints, unsigned * pFuncs )
{
    int nVars  = 10;
    int nMints = 32;
    int nFuncs = 7;
    char * pMintStrs[32] = { 
        "1-1---1---",
        "1-1----1--",
        "1-1-----1-",
        "1-1------1",

        "1--1--1---",
        "1--1---1--",
        "1--1----1-",
        "1--1-----1",

        "1---1-1---",
        "1---1--1--",
        "1---1---1-",
        "1---1----1",

        "1----11---",
        "1----1-1--",
        "1----1--1-",
        "1----1---1",


        "-11---1---",
        "-11----1--",
        "-11-----1-",
        "-11------1",

        "-1-1--1---",
        "-1-1---1--",
        "-1-1----1-",
        "-1-1-----1",

        "-1--1-1---",
        "-1--1--1--",
        "-1--1---1-",
        "-1--1----1",

        "-1---11---",
        "-1---1-1--",
        "-1---1--1-",
        "-1---1---1"
    };
    char * pFuncStrs[7] = { 
        "11111110110010001110110010000000",
        "00000001001101110001001101111111",
        "10000001001001000001001001001000",
        "01001000000100101000000100100100",
        "00100100100000010100100000010010",
        "00010010010010000010010010000001",
        "11111111111111111111000000000000"
    };
    int i, k;
    *pnVars  = nVars;
    *pnMints = nMints;
    *pnFuncs = nFuncs;
    // extract mints
    for ( i = 0; i < nMints; i++ )
        for ( k = 0; k < nVars; k++ )
            if ( pMintStrs[i][k] == '1' )
                pMints[i] |= (1 << k), pVars[k] |= (1 << i);
    // extract funcs
    for ( i = 0; i < nFuncs; i++ )
        for ( k = 0; k < nMints; k++ )
            if ( pFuncStrs[i][k] == '1' )
                pFuncs[i] |= (1 << k);
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_GetThird( int * pnVars, int * pnMints, int * pnFuncs, unsigned * pVars, unsigned * pMints, unsigned * pFuncs )
{
    int nVars  = 8;
    int nMints = 16;
    int nFuncs = 7;
    char * pMintStrs[16] = { 
        "1---1---",
        "1----1--",
        "1-----1-",
        "1------1",

        "-1--1---",
        "-1---1--",
        "-1----1-",
        "-1-----1",

        "--1-1---",
        "--1--1--",
        "--1---1-",
        "--1----1",

        "---11---",
        "---1-1--",
        "---1--1-",
        "---1---1"
    };
    char * pFuncStrs[7] = { 
        "1111111011001000",
        "0000000100110111",
        "1000000100100100",
        "0100100000010010",
        "0010010010000001",
        "0001001001001000",
        "1111111111111111"
    };
    int i, k;
    *pnVars  = nVars;
    *pnMints = nMints;
    *pnFuncs = nFuncs;
    // extract mints
    for ( i = 0; i < nMints; i++ )
        for ( k = 0; k < nVars; k++ )
            if ( pMintStrs[i][k] == '1' )
                pMints[i] |= (1 << k), pVars[k] |= (1 << i);
    // extract funcs
    for ( i = 0; i < nFuncs; i++ )
        for ( k = 0; k < nMints; k++ )
            if ( pFuncStrs[i][k] == '1' )
                pFuncs[i] |= (1 << k);
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_EnumPrint_rec( Vec_Int_t * vGates, int i, int nVars )
{
    int Fan0 = Vec_IntEntry(vGates, 2*i);
    int Fan1 = Vec_IntEntry(vGates, 2*i+1);
    char * pOper = Fan0 < Fan1 ? "" : "+";
    if ( Fan0 > Fan1 )
        ABC_SWAP( int, Fan0, Fan1 );
    if ( Fan0 < nVars )
        printf( "%c", 'a'+Fan0 );
    else
    {
        printf( "(" );
        Abc_EnumPrint_rec( vGates, Fan0, nVars );
        printf( ")" );
    }
    printf( "%s", pOper );
    if ( Fan1 < nVars )
        printf( "%c", 'a'+Fan1 );
    else
    {
        printf( "(" );
        Abc_EnumPrint_rec( vGates, Fan1, nVars );
        printf( ")" );
    }
}
void Abc_EnumPrint( Vec_Int_t * vGates, int i, int nVars )
{
    assert( 2*i < Vec_IntSize(vGates) );
    Abc_EnumPrint_rec( vGates, i, nVars );
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int  Abc_DataHasBit( word * p, word i )  { return (p[(i)>>6] & (1<<((i) & 63))) > 0; }
static inline void Abc_DataXorBit( word * p, word i )  { p[(i)>>6] ^= (1<<((i) & 63));             }

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_EnumerateFunctions( int nDecMax )
{
    int nVars;
    int nMints;
    int nFuncs;
    unsigned pVars[100] = {0};
    unsigned pMints[100] = {0};
    unsigned pFuncs[100] = {0};
    unsigned Truth;
    int FuncDone[100] = {0}, nFuncDone = 0;
    int GateCount[100] = {0};
    int i, k, n, a, b, v;
    abctime clk = Abc_Clock();
    Vec_Int_t * vGates = Vec_IntAlloc( 100000 );
    Vec_Int_t * vTruths = Vec_IntAlloc( 100000 );
//    Vec_Int_t * vHash = Vec_IntStartFull( 1 << 16 );
    word * pHash;

    // extract data
//    Abc_GetFirst( &nVars, &nMints, &nFuncs, pVars, pMints, pFuncs );
    Abc_GetSecond( &nVars, &nMints, &nFuncs, pVars, pMints, pFuncs );
//    Abc_GetThird( &nVars, &nMints, &nFuncs, pVars, pMints, pFuncs );

    // create hash table
    assert( nMints == 16 || nMints == 32 );
    pHash = (word *)ABC_CALLOC( char, 1 << (nMints-3) );

    // create elementary gates
    for ( k = 0; k < nVars; k++ )
    {
//        Vec_IntWriteEntry( vHash, pVars[k], k );
        Abc_DataXorBit( pHash, pVars[k] );
        Vec_IntPush( vTruths, pVars[k] );
        Vec_IntPush( vGates, -1 );
        Vec_IntPush( vGates, -1 );
    }

    // go through different number of variables
    GateCount[0] = 0;
    GateCount[1] = nVars;
    assert( Vec_IntSize(vTruths) == nVars );
    for ( n = 0; n < nDecMax && nFuncDone < nFuncs; n++ )
    {
        for ( a = 0; a <= n; a++ )
        for ( b = a; b <= n; b++ )
        if ( a + b == n )
        {
            printf( "Trying %d + %d + 1 = %d\n", a, b, n+1 );
            for ( i = GateCount[a]; i < GateCount[a+1]; i++ )
            for ( k = GateCount[b]; k < GateCount[b+1]; k++ )
            if ( i < k )
            {
                Truth = Vec_IntEntry(vTruths, i) & Vec_IntEntry(vTruths, k);
//                if ( Vec_IntEntry(vHash, Truth) == -1 )
                if ( !Abc_DataHasBit(pHash, Truth) )
                {
//                    Vec_IntWriteEntry( vHash, Truth, Vec_IntSize(vTruths) );
                    Abc_DataXorBit( pHash, Truth );
                    Vec_IntPush( vTruths, Truth );
                    Vec_IntPush( vGates, i );
                    Vec_IntPush( vGates, k );

                    for ( v = 0; v < nFuncs; v++ )
                    if ( !FuncDone[v] && Truth == pFuncs[v] )
                    {
                        printf( "Found function %d with %d gates: ", v, n+1 );
                        Abc_EnumPrint( vGates, Vec_IntSize(vTruths)-1, nVars );
                        FuncDone[v] = 1;
                        nFuncDone++;
                    }
                }
                Truth = Vec_IntEntry(vTruths, i) | Vec_IntEntry(vTruths, k);
//                if ( Vec_IntEntry(vHash, Truth) == -1 )
                if ( !Abc_DataHasBit(pHash, Truth) )
                {
//                    Vec_IntWriteEntry( vHash, Truth, Vec_IntSize(vTruths) );
                    Abc_DataXorBit( pHash, Truth );
                    Vec_IntPush( vTruths, Truth );
                    Vec_IntPush( vGates, k );
                    Vec_IntPush( vGates, i );

                    for ( v = 0; v < nFuncs; v++ )
                    if ( !FuncDone[v] && Truth == pFuncs[v] )
                    {
                        printf( "Found function %d with %d gates: ", v, n+1 );
                        Abc_EnumPrint( vGates, Vec_IntSize(vTruths)-1, nVars );
                        FuncDone[v] = 1;
                        nFuncDone++;
                    }
                }
            }
        }
        GateCount[n+2] = Vec_IntSize(vTruths);
        printf( "Finished %d gates.  Truths = %10d.  ", n+1, Vec_IntSize(vTruths) );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    }
    ABC_FREE( pHash );
//    Vec_IntFree( vHash );
    Vec_IntFree( vGates );
    Vec_IntFree( vTruths );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

