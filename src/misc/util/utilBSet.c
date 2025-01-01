/**CFile****************************************************************

  FileName    [utilBSet.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Bound set evaluation.]

  Synopsis    [Bound set evaluation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - December 25, 2024.]

  Revision    [$Id: utilBSet.c,v 1.00 2024/12/25 00:00:00 alanmi Exp $]

***********************************************************************/

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>

#include "misc/vec/vec.h"
#include "misc/extra/extra.h"
#include "misc/util/utilTruth.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Abc_BSEval_t_  Abc_BSEval_t;
struct Abc_BSEval_t_
{
    int           nVars;
    int           nBVars;
    Vec_Int_t *   vPairs;   // perm pairs
    Vec_Int_t *   vCounts;  // cofactor counts
    Vec_Int_t *   vTable;   // hash table
    Vec_Int_t *   vUsed;    // used entries
    Vec_Wrd_t *   vStore;   // cofactors
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Bound-set evalution.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_TtGetCM1( word * p, int nVars )
{
    int Counts[4] = {0};
    int i, Res = 0, nDigits = 1 << (nVars - 1);
    for ( i = 0; i < nDigits; i++ )
        Counts[Abc_TtGetQua(p, i)]++;
    for ( i = 0; i < 4; i++ )
        Res += Counts[i] > 0;
    return Res;
}
int Abc_TtGetCM2( word * p, int nVars )
{
    int Counts[16] = {0};
    int i, Res = 0, nDigits = 1 << (nVars - 2);
    for ( i = 0; i < nDigits; i++ )
        Counts[Abc_TtGetHex(p, i)]++;
    for ( i = 0; i < 16; i++ )
        Res += Counts[i] > 0;
    return Res;
}
int Abc_TtGetCM3( word * p, int nVars, int * pCounts, Vec_Int_t * vUsed )
{
    unsigned char * q = (unsigned char *)p;
    int i, Digit, nDigits = 1 << (nVars - 3);
    Vec_IntClear( vUsed );
    for ( i = 0; i < nDigits; i++ ) {
        if ( pCounts[q[i]] == 1 )
            continue;
        pCounts[q[i]] = 1;
        Vec_IntPush(vUsed, q[i]);
    }
    Vec_IntForEachEntry( vUsed, Digit, i )
        pCounts[Digit] = -1;
    return Vec_IntSize(vUsed);
}
int Abc_TtGetCM4( word * p, int nVars, int * pCounts, Vec_Int_t * vUsed )
{
    unsigned short * q = (unsigned short *)p;
    int i, Digit, nDigits = 1 << (nVars - 4);
    Vec_IntClear( vUsed );
    for ( i = 0; i < nDigits; i++ ) {
        if ( pCounts[q[i]] == 1 )
            continue;
        pCounts[q[i]] = 1;
        Vec_IntPush(vUsed, q[i]);
    }
    Vec_IntForEachEntry( vUsed, Digit, i )
        pCounts[Digit] = -1;
    return Vec_IntSize(vUsed);
}

// https://en.wikipedia.org/wiki/Jenkins_hash_function
int Abc_TtGetKey( unsigned char * p, int nSize, int nTableSize )
{
    int i = 0; unsigned hash = 0;
    while ( i != nSize ) 
    {
        hash += p[i++];
        hash += hash << 10;
        hash ^= hash >> 6;
    }
    hash += hash << 3;
    hash ^= hash >> 11;
    hash += hash << 15;
    return (int)(hash % nTableSize);
}
int Abc_TtHashLookup5( int Entry, Vec_Int_t * vTable, Vec_Wrd_t * vStore, Vec_Int_t * vUsed )
{
    int Key = Abc_TtGetKey( (unsigned char*)&Entry, 4, Vec_IntSize(vTable) );
    int * pTable = Vec_IntArray(vTable);
    for ( ; pTable[Key] >= 0; Key = (Key + 1) % Vec_IntSize(vTable) )
        if ( Entry == (int)Vec_WrdEntry(vStore, pTable[Key]) )
            return pTable[Key];
    assert( pTable[Key] == -1 );
    pTable[Key] = Vec_WrdSize(vStore);
    Vec_WrdPush( vStore, (word)Entry );
    Vec_IntPush( vUsed, Key );
    return pTable[Key];
}
int Abc_TtGetCM5( word * p, int nVars, Vec_Int_t * vTable, Vec_Wrd_t * vStore, Vec_Int_t * vUsed )
{
    unsigned * q = (unsigned *)p;
    int i, Item, nDigits = 1 << (nVars - 5);
    Vec_WrdClear( vStore );
    Vec_IntClear( vUsed );
    for ( i = 0; i < nDigits; i++ )
        Abc_TtHashLookup5( q[i], vTable, vStore, vUsed );
    Vec_IntForEachEntry( vUsed, Item, i )
        Vec_IntWriteEntry( vTable, Item, -1 );
    return Vec_IntSize(vUsed);
}
int Abc_TtHashLookup6( word * pEntry, int nWords, Vec_Int_t * vTable, Vec_Wrd_t * vStore, Vec_Int_t * vUsed )
{
    int i, Key = Abc_TtGetKey( (unsigned char*)pEntry, 8*nWords, Vec_IntSize(vTable) );
    int * pTable = Vec_IntArray(vTable);
    for ( ; pTable[Key] >= 0; Key = (Key + 1) % Vec_IntSize(vTable) )
        if ( !memcmp(pEntry, Vec_WrdEntryP(vStore, nWords*pTable[Key]), 8*nWords) )
            return pTable[Key];
    assert( pTable[Key] == -1 );
    pTable[Key] = Vec_WrdSize(vStore)/nWords;
    for ( i = 0; i < nWords; i++ )
        Vec_WrdPush( vStore, pEntry[i] );
    Vec_IntPush( vUsed, Key );
    return pTable[Key];
}
int Abc_TtGetCM6( word * p, int nVars, int nFVars, Vec_Int_t * vTable, Vec_Wrd_t * vStore, Vec_Int_t * vUsed )
{
    assert( nFVars >= 6 && nFVars < nVars );
    int i, Item, nDigits = 1 << (nVars - nFVars), nWords = 1 << (nFVars - 6);
    Vec_WrdClear( vStore );
    Vec_IntClear( vUsed );
    //assert( Vec_IntSum(vTable) == -Vec_IntSize(vTable) );
    for ( i = 0; i < nDigits; i++ )
        Abc_TtHashLookup6( p + i*nWords, nWords, vTable, vStore, vUsed );
    Vec_IntForEachEntry( vUsed, Item, i )
        Vec_IntWriteEntry( vTable, Item, -1 );
    return Vec_IntSize(vUsed);
}
int Abc_TtGetCMCount( word * p, int nVars, int nFVars, Vec_Int_t * vCounts, Vec_Int_t * vTable, Vec_Wrd_t * vStore, Vec_Int_t * vUsed )
{
    if ( nFVars == 1 ) 
        return Abc_TtGetCM1( p, nVars );
    if ( nFVars == 2 ) 
        return Abc_TtGetCM2( p, nVars );
    if ( nFVars == 3 ) 
        return Abc_TtGetCM3( p, nVars, Vec_IntArray(vCounts), vUsed );
    if ( nFVars == 4 ) 
        return Abc_TtGetCM4( p, nVars, Vec_IntArray(vCounts), vUsed );
    if ( nFVars == 5 ) 
        return Abc_TtGetCM5( p, nVars, vTable, vStore, vUsed );
    if ( nFVars == 6 ) 
        return Abc_TtGetCM6( p, nVars, nFVars, vTable, vStore, vUsed );
    assert( 0 );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Bound-set evalution.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_TtGetCM1Pat( word * p, int nVars, word * pPat )
{
    int nUsed = 0, pUsed[4], pMap[4];
    int i, nDigits = 1 << (nVars - 1), nWordsBS = Abc_TtWordNum(nVars - 1);
    memset( pMap, 0xFF, 16 );
    for ( i = 0; i < nDigits; i++ ) {
        int Digit = Abc_TtGetQua(p, i);
        if ( pMap[Digit] == -1 ) {
            pMap[Digit] = nUsed;
            pUsed[nUsed++] = Digit;
        }
        if ( pPat ) Abc_TtSetBit( pPat + nWordsBS*pMap[Digit], i );
    }
    return nUsed;
}
int Abc_TtGetCM2Pat( word * p, int nVars, word * pPat )
{
    int nUsed = 0, pUsed[16], pMap[16];
    int i, nDigits = 1 << (nVars - 2), nWordsBS = Abc_TtWordNum(nVars - 2);
    memset( pMap, 0xFF, 64 );
    for ( i = 0; i < nDigits; i++ ) {
        int Digit = Abc_TtGetHex(p, i);
        if ( pMap[Digit] == -1 ) {
            pMap[Digit] = nUsed;
            pUsed[nUsed++] = Digit;
        }
        if ( pPat ) Abc_TtSetBit( pPat + nWordsBS*pMap[Digit], i );
    }
    return nUsed;
}
int Abc_TtGetCM3Pat( word * p, int nVars, int * pMap, Vec_Int_t * vUsed, word * pPat )
{
    unsigned char * q = (unsigned char *)p;
    int i, Digit, nDigits = 1 << (nVars - 3), nWordsBS = Abc_TtWordNum(nVars - 3);
    Vec_IntClear( vUsed );
    for ( i = 0; i < nDigits; i++ ) {
        if ( pMap[q[i]] == -1 ) {
            pMap[q[i]] = Vec_IntSize(vUsed);
            Vec_IntPush(vUsed, q[i]);
        }
        if ( pPat ) Abc_TtSetBit( pPat + nWordsBS*pMap[q[i]], i );
    }
    Vec_IntForEachEntry( vUsed, Digit, i )
        pMap[Digit] = -1;
    return Vec_IntSize(vUsed);
}
int Abc_TtGetCM4Pat( word * p, int nVars, int * pMap, Vec_Int_t * vUsed, word * pPat )
{
    unsigned short * q = (unsigned short *)p;
    int i, Digit, nDigits = 1 << (nVars - 4), nWordsBS = Abc_TtWordNum(nVars - 4);
    Vec_IntClear( vUsed );
    for ( i = 0; i < nDigits; i++ ) {
        if ( pMap[q[i]] == -1 ) {
            pMap[q[i]] = Vec_IntSize(vUsed);
            Vec_IntPush(vUsed, q[i]);
        }
        if ( pPat ) Abc_TtSetBit( pPat + nWordsBS*pMap[q[i]], i );
    }
    Vec_IntForEachEntry( vUsed, Digit, i )
        pMap[Digit] = -1;
    return Vec_IntSize(vUsed);
}
int Abc_TtGetCM5Pat( word * p, int nVars, Vec_Int_t * vTable, Vec_Wrd_t * vStore, Vec_Int_t * vUsed, word * pPat )
{
    unsigned * q = (unsigned *)p;
    int i, Item, nDigits = 1 << (nVars - 5), nWordsBS = Abc_TtWordNum(nVars - 5);
    Vec_WrdClear( vStore );
    Vec_IntClear( vUsed );
    if ( pPat )
        for ( i = 0; i < nDigits; i++ )
            Abc_TtSetBit( pPat + nWordsBS*Abc_TtHashLookup5(q[i], vTable, vStore, vUsed), i );
    else
        for ( i = 0; i < nDigits; i++ )
            Abc_TtHashLookup5( q[i], vTable, vStore, vUsed );
    Vec_IntForEachEntry( vUsed, Item, i )
        Vec_IntWriteEntry( vTable, Item, -1 );
    return Vec_IntSize(vUsed);
}
int Abc_TtGetCM6Pat( word * p, int nVars, int nFVars, Vec_Int_t * vTable, Vec_Wrd_t * vStore, Vec_Int_t * vUsed, word * pPat )
{
    assert( nFVars >= 6 && nFVars < nVars );
    int i, Item, nDigits = 1 << (nVars - nFVars), nWords = 1 << (nFVars - 6), nWordsBS = Abc_TtWordNum(nVars - nFVars);
    Vec_WrdClear( vStore );
    Vec_IntClear( vUsed );    
    if ( pPat )
        for ( i = 0; i < nDigits; i++ )
            Abc_TtSetBit( pPat + nWordsBS*Abc_TtHashLookup6(p + i*nWords, nWords, vTable, vStore, vUsed), i );
    else
        for ( i = 0; i < nDigits; i++ )
            Abc_TtHashLookup6( p + i*nWords, nWords, vTable, vStore, vUsed );
    Vec_IntForEachEntry( vUsed, Item, i )
        Vec_IntWriteEntry( vTable, Item, -1 );
    return Vec_IntSize(vUsed);
}

void Abc_TtPrintPat( word * pPat, int nVars, int nMyu )
{
    printf( "ACD i-sets with %d variables and column multiplicity %d:\n", nVars, nMyu );
    for ( int m = 0; m < nMyu; m++ )
        Extra_PrintBinary( stdout, (unsigned *)&pPat[m], (1 << nVars) ), printf("\n");
}
int Abc_TtCheck1Shared( word * pPat, int nVars, int nFVars, int nMyu )
{
    int fVerbose = 0;
    if ( fVerbose ) Abc_TtPrintPat( pPat, nVars-nFVars, nMyu );
    assert( nMyu > 2 );
    int nRails  = Abc_Base2Log(nMyu);
    int nMyuMax = 1 << (nRails - 1);
    for ( int v = 0; v < nVars - nFVars; v++ ) {
        int m, n, Counts[2] = {0};
        for ( n = 0; n < 2; n++ ) {
            for ( m = 0; m < nMyu; m++ )
                if ( (Counts[n] += ((s_Truth26[n][v] & pPat[m]) != 0)) > nMyuMax )
                    break;
            if ( m < nMyu )
                break;
        }
        if ( fVerbose ) printf( "%d : %2d %2d  %2d\n", v, Counts[0], Counts[1], nMyuMax );
        if ( n == 2 ) {
            //Abc_TtPrintPat( pPat, nVars-nFVars, nMyu );
            //printf( "%d : %2d %2d  %2d\n", v, Counts[0], Counts[1], nMyuMax );
            return nRails - 1;
        }
    }
    if ( fVerbose ) printf( "Not found\n" );
    return nRails;
}
int Abc_TtGetCMPat( word * p, int nVars, int nFVars, Vec_Int_t * vCounts, Vec_Int_t * vTable, Vec_Wrd_t * vStore, Vec_Int_t * vUsed )
{
    word pPat[1024];
    int nMintsBS = 1 << (nVars - nFVars);
    int nWordsBS = Abc_TtWordNum(nVars - nFVars);
    assert( nMintsBS * nWordsBS <= 1024 );
    memset( pPat, 0, 8 * nMintsBS * nWordsBS );
    int nMyu = 0, nRails;
    if ( nFVars == 1 ) 
        nMyu = Abc_TtGetCM1Pat( p, nVars, pPat );
    else if ( nFVars == 2 ) 
        nMyu = Abc_TtGetCM2Pat( p, nVars, pPat );
    else if ( nFVars == 3 ) 
        nMyu = Abc_TtGetCM3Pat( p, nVars, Vec_IntArray(vCounts), vUsed, pPat );
    else if ( nFVars == 4 ) 
        nMyu = Abc_TtGetCM4Pat( p, nVars, Vec_IntArray(vCounts), vUsed, pPat );
    else if ( nFVars == 5 ) 
        nMyu = Abc_TtGetCM5Pat( p, nVars, vTable, vStore, vUsed, pPat );
    else if ( nFVars == 6 ) 
        nMyu = Abc_TtGetCM6Pat( p, nVars, nFVars, vTable, vStore, vUsed, pPat );
    else assert( 0 );
    if ( nMyu <= 2 )
        nRails = 1;
    else
        nRails = Abc_TtCheck1Shared( pPat, nVars, nFVars, nMyu );
    return nRails;
}
int Abc_TtGetCM( word * p, int nVars, int nFVars, Vec_Int_t * vCounts, Vec_Int_t * vTable, Vec_Wrd_t * vStore, Vec_Int_t * vUsed, int fShared )
{
    if ( fShared )
        return Abc_TtGetCMPat( p, nVars, nFVars, vCounts, vTable, vStore, vUsed );
    return Abc_TtGetCMCount( p, nVars, nFVars, vCounts, vTable, vStore, vUsed );
}


/**Function*************************************************************

  Synopsis    [Permutation generation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Abc_TtPermGen( int * currPerm, int nVars, word * pT, int nTtVars )
{
    int i = nVars - 1;
    while ( i >= 0 && currPerm[i - 1] >= currPerm[i] )
        i--;
    if (i >= 0)
    {
        int j = nVars;
        while ( j > i && currPerm[j - 1] <= currPerm[i - 1 ])
            j--;
        ABC_SWAP( int, currPerm[i - 1], currPerm[j - 1] )
        if ( pT ) Abc_TtSwapVars( pT, nTtVars, i-1, j-1 );
        i++;
        j = nVars;
        while ( i < j )
        {
            ABC_SWAP( int, currPerm[i - 1], currPerm[j - 1] )
            if ( pT ) Abc_TtSwapVars( pT, nTtVars, i-1, j-1 );
            i++;
            j--;
        }
    }
}
static int Abc_TtFactorial(int nVars)
{
    int i, Res = 1;
    for ( i = 1; i <= nVars; i++ )
        Res *= i;
    return Res;
}
void Abc_TtPermGenTest()
{
    int i, k, nVars = 5, currPerm[5] = {0};
    for ( i = 0; i < nVars; i++ )
        currPerm[i] = i;
    int fact = Abc_TtFactorial( nVars );
    for ( i = 0; i < fact; i++ )
    {
        printf( "%3d :", i );
        for ( k = 0; k < nVars; k++ )
            printf( " %d", currPerm[k] );
        printf( "\n" );
        Abc_TtPermGen( currPerm, nVars, NULL, 0 );
    }
}

/**Function*************************************************************

  Synopsis    [Combination generation.]

  Description [https://stackoverflow.com/questions/22650522/how-to-generate-chases-sequence]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_GenChaseNext(int a[], int w[], int *r) 
{
    int found_r = 0;
    int j;
    for (j = *r; !w[j]; j++) {
        int b = a[j] + 1;
        int n = a[j + 1];
        if (b < (w[j + 1] ? n - (2 - (n & 1)) : n)) {
            if ((b & 1) == 0 && b + 1 < n) b++;
            a[j] = b;
            if (!found_r) *r = j > 1 ? j - 1 : 0;
            return;
        }
        w[j] = a[j] - 1 >= j;
        if (w[j] && !found_r) {
            *r = j;
            found_r = 1;
        }
    }
    int b = a[j] - 1;
    if ((b & 1) != 0 && b - 1 >= j) b--;
    a[j] = b;
    w[j] = b - 1 >= j;
    if (!found_r) *r = j;
}
Vec_Int_t * Abc_GenChasePairs( int N, int T ) 
{
    Vec_Int_t * vPairs = Vec_IntAlloc( 100 );
    int j, z, r = 0, Count = 0, a[32], b[32], w[32];
    for ( j = 0; j < T + 1; j++ ) {
        a[j] = N - (T - j);
        w[j] = 1;
    }
    do {
        for ( z = 0; z <= T; z++ )
            b[z] = a[z];
        Abc_GenChaseNext( a, w, &r );
        for ( z = 0; z < T; z++ ) {
            if ( a[z] == b[z] )
                continue;
            Vec_IntPushTwo( vPairs, b[z], a[z] );
            if ( 0 ) {
                printf( "%3d : ", Count++ );
                for (j = T - 1; j > -1; j--) printf("%x", b[j]);
                printf( "  %d <-> %d  ", b[z], a[z] );
                for (j = T - 1; j > -1; j--) printf("%x", a[j]);
                printf( "\n" );
            }
            break;
        }
    } while (a[T] == N);
    Vec_IntPushTwo( vPairs, 0, 0 );
    return vPairs;
}
void Abc_GenChasePrint( int Count, int * pPerm, int nVars, int nFVars, int Var0, int Var1 )
{
    int k;
    printf( "%3d :  ", Count++ );
    for ( k = nVars-1; k >= nFVars; k-- )
        printf( "%d", pPerm[k] );
    printf( " " );
    for ( k = nFVars-1; k >= 0; k-- )
        printf( "%d", pPerm[k] );
    printf( "  %d <-> %d\n", Var0, Var1 );
}
void Abc_GenChaseTest()
{
    int nVars  = 4;
    int nFVars = 2;
    Vec_Int_t * vPairs = Abc_GenChasePairs( nVars, nVars-nFVars );
    int i, Var0, Var1, Pla2Var[32], Var2Pla[32];
    for ( i = 0; i < nVars; i++ )
        Pla2Var[i] = Var2Pla[i] = i;
    int Count = 0;
    Vec_IntForEachEntryDouble( vPairs, Var0, Var1, i ) {
        Abc_GenChasePrint( Count++, Pla2Var, nVars, nFVars, Var0, Var1 );
        int iPlace0 = Var2Pla[Var0];
        int iPlace1 = Var2Pla[Var1];
        //Abc_TtSwapVars( pTruth, nVars, iPlace0, iPlace1 );
        Var2Pla[Pla2Var[iPlace0]] = iPlace1;
        Var2Pla[Pla2Var[iPlace1]] = iPlace0;
        Pla2Var[iPlace0] ^= Pla2Var[iPlace1];
        Pla2Var[iPlace1] ^= Pla2Var[iPlace0];
        Pla2Var[iPlace0] ^= Pla2Var[iPlace1];
    }
    Vec_IntFree( vPairs );
}


/**Function*************************************************************

  Synopsis    [Bound-set evalution for one function.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_BSEval_t * Abc_BSEvalAlloc()
{
    Abc_BSEval_t * p = ABC_CALLOC( Abc_BSEval_t, 1 );
    p->vCounts  = Vec_IntStartFull( 1 << 16 );
    p->vTable   = Vec_IntStartFull( 997 );
    p->vUsed    = Vec_IntAlloc(100);
    p->vStore   = Vec_WrdAlloc(1000);
    return p;
}
void Abc_BSEvalFree( Abc_BSEval_t * p )
{
    Vec_IntFreeP( &p->vPairs );
    Vec_IntFree( p->vCounts );
    Vec_IntFree( p->vTable  );
    Vec_IntFree( p->vUsed   );
    Vec_WrdFree( p->vStore  );
    ABC_FREE( p );
}
void Abc_BSEvalOneTest( word * pT, int nVars, int nBVars, int fVerbose )
{
    assert( nVars > nBVars );
    Abc_BSEval_t * p = Abc_BSEvalAlloc();
    if ( p->nVars != nVars || p->nBVars != nBVars ) {
        Vec_IntFreeP( &p->vPairs );
        p->vPairs = Abc_GenChasePairs( nVars, nBVars );
        p->nVars = nVars;
        p->nBVars = nBVars;
    }
    int Best = Abc_TtGetCM( pT, nVars, nVars-nBVars, p->vCounts, p->vTable, p->vStore, p->vUsed, 0 );
    printf( "Function: " ); Extra_PrintHex( stdout, (unsigned *)pT, nVars ); printf( "\n" );
    printf( "The column multiplicity of the %d-var function with bound-sets of size %d is %d.\n", nVars, nBVars, Best );
    Abc_BSEvalFree(p);
}
int Abc_BSEvalBest( Abc_BSEval_t * p, word * pIn, word * pBest, int nVars, int nCVars, int nFVars, int fVerbose, int * pPermBest, int fShared )
{
    int i, k, Var0, Var1, Pla2Var[32], Var2Pla[32];
    int nPermVars = nVars-nCVars;
    assert( p->nVars == nPermVars && p->nBVars == nPermVars-nFVars );
    for ( i = 0; i < nVars; i++ )
        Pla2Var[i] = Var2Pla[i] = i;
    if ( pPermBest )
        for ( i = 0; i < nVars; i++ )
            pPermBest[i] = i;
    int CostBest = 1 << nVars;
    //int Count = 0;
    Vec_IntForEachEntryDouble( p->vPairs, Var0, Var1, i ) {
        //Abc_GenChasePrint( Count++, Pla2Var, nVars, nFVars, Var0, Var1 );
        int  CostThis = Abc_TtGetCM( pIn, nVars, nFVars, p->vCounts, p->vTable, p->vStore, p->vUsed, fShared );
        if ( CostBest > CostThis ) {
            CostBest = CostThis;
            if ( pBest )     Abc_TtCopy( pBest, pIn, Abc_Truth6WordNum(nVars), 0 );
            if ( pPermBest ) memcpy( pPermBest, Pla2Var, sizeof(int)*nPermVars );
        }
        if ( fVerbose )
        {
            printf( "%3d : ", i/2 );
            for ( k = nCVars-1; k >= 0; k-- )
                printf( " %d", nVars-nCVars+k );
            printf( " " );
            for ( k = nPermVars-1; k >= nFVars; k-- )
                printf( " %d", Pla2Var[k] );
            printf( " " );
            for ( k = nFVars-1; k >= 0; k-- )
                printf( " %d", Pla2Var[k] );
            printf( "  : Myu = %3d", CostThis );
            printf( "\n" );
        }
        int iPlace0 = Var2Pla[Var0];
        int iPlace1 = Var2Pla[Var1];
        if ( iPlace0 == iPlace1 )
            continue;
        Abc_TtSwapVars( pIn, nVars, iPlace0, iPlace1 );
        Var2Pla[Pla2Var[iPlace0]] = iPlace1;
        Var2Pla[Pla2Var[iPlace1]] = iPlace0;
        Pla2Var[iPlace0] ^= Pla2Var[iPlace1];
        Pla2Var[iPlace1] ^= Pla2Var[iPlace0];
        Pla2Var[iPlace0] ^= Pla2Var[iPlace1];
    }
    for ( i = 0; i < nPermVars; i++ )
    {
        int iPlace0 = i;
        int iPlace1 = Var2Pla[i];
        if ( iPlace0 == iPlace1 )
            continue;
        Abc_TtSwapVars( pIn, nVars, iPlace0, iPlace1 );
        Var2Pla[Pla2Var[iPlace0]] = iPlace1;
        Var2Pla[Pla2Var[iPlace1]] = iPlace0;
        Pla2Var[iPlace0] ^= Pla2Var[iPlace1];
        Pla2Var[iPlace1] ^= Pla2Var[iPlace0];
        Pla2Var[iPlace0] ^= Pla2Var[iPlace1];
    }
    return CostBest;
}
void Abc_BSEvalBestTest( word * pIn, int nVars, int nBVars, int fShared, int fVerbose )
{
    assert( nVars > nBVars );
    Abc_BSEval_t * p = Abc_BSEvalAlloc(); int i, pPerm[32] = {0};
    if ( p->nVars != nVars || p->nBVars != nBVars ) {
        Vec_IntFreeP( &p->vPairs );
        p->vPairs = Abc_GenChasePairs( nVars, nBVars );
        p->nVars = nVars;
        p->nBVars = nBVars;        
    }    
    word * pFun = ABC_ALLOC( word, Abc_TtWordNum(nVars) );
    int Best = Abc_BSEvalBest( p, pIn, pFun, nVars, 0, nVars-nBVars, fVerbose, pPerm, fShared );
    printf( "The minimum %s of the %d-var function with bound-sets of size %d is %d.\n", 
        fShared ? "number of rails" : "column multiplicity", nVars, nBVars, Best );
    printf( "Original: " ); Extra_PrintHex( stdout, (unsigned *)pIn,  nVars ); printf( "\n" );
    printf( "Permuted: " ); Extra_PrintHex( stdout, (unsigned *)pFun, nVars ); printf( "\n" );
    printf( "Permutation is " );
    for ( i = 0; i < nVars; i++ )
        printf( "%d ", pPerm[i] );
    printf( "\n" );
    ABC_FREE( pFun );
    Abc_BSEvalFree(p);
}

/**Function*************************************************************

  Synopsis    [Testing on random functions.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_BSEvalBestGen( int nVars, int nBVars, int nFuncs, int nMints, int fTryAll, int fShared, int fVerbose )
{
    assert( nVars > nBVars );
    abctime clkTotal = Abc_Clock();
    Abc_BSEval_t * p = Abc_BSEvalAlloc();
    Vec_Int_t * vCounts[2] = { Vec_IntStart(1 << nVars), Vec_IntStart(1 << nVars) };
    int i, k, Count, nWords = Abc_TtWordNum(nVars);
    word * pFun = ABC_ALLOC( word, nWords );
    if ( p->nVars != nVars || p->nBVars != nBVars ) {
        Vec_IntFreeP( &p->vPairs );
        p->vPairs = Abc_GenChasePairs( nVars, nBVars );
        p->nVars = nVars;
        p->nBVars = nBVars;        
    }    
    Abc_Random(1);
    for ( i = 0; i < nFuncs; i++ ) {
        if ( nMints == 0 )
            for ( k = 0; k < nWords; k++ )
                pFun[k] = Abc_RandomW(0);
        else {
            Abc_TtClear( pFun, nWords );
            for ( k = 0; k < nMints; k++ ) {
                int iMint = 0;
                do iMint = Abc_Random(0) % (1 << nVars);
                while ( Abc_TtGetBit(pFun, iMint) );
                Abc_TtSetBit( pFun, iMint );
            }
        }
        if ( fVerbose ) {
            printf( "Function %5d ", i );
            if ( nMints )
                printf( "with %d positive minterms ", nMints );
            if ( nVars <= 8 ) {
                printf( "has truth table: " );
                Extra_PrintHex( stdout, (unsigned *)pFun, nVars );
            }
            if ( fTryAll )
                printf( "\n" );
            else 
                printf( "  " );
        }
        
        if ( fTryAll )
            Count = Abc_BSEvalBest( p, pFun, NULL, nVars, 0, nVars-nBVars, fVerbose, NULL, fShared );
        else 
            Count = Abc_TtGetCM( pFun, nVars, nVars-nBVars, p->vCounts, p->vTable, p->vStore, p->vUsed, fShared );
        if ( fVerbose )
            printf( "Myu = %d\n", Count );        
        Vec_IntAddToEntry( vCounts[0], Count, 1 );
        Vec_IntAddToEntry( vCounts[1], Abc_Base2Log(Count), 1 );
    }
    ABC_FREE( pFun );
    Abc_BSEvalFree(p);
    if ( nMints )
        printf( "Generated %d random %d-var functions with %d positive minterms.\n", nFuncs, nVars, nMints );
    else
        printf( "Generated %d random %d-var functions.\n", nFuncs, nVars );
    if ( fShared ) {
        printf( "Distribution of the %s number of rails for bound set size %d with one shared variable:\n", fTryAll ? "MINIMUM": "ORIGINAL", nBVars );
        assert( Vec_IntSum(vCounts[0]) == nFuncs );
        Vec_IntForEachEntry( vCounts[0], Count, i )
            if ( Count ) printf( "%d=%d (%.2f %%)  ", i, Count, 100.0*Count/nFuncs );
        printf( "\n" );
    }
    else {
        printf( "Distribution of the %s column multiplicity for bound set size %d with no shared variables:\n", fTryAll ? "MINIMUM": "ORIGINAL", nBVars );
        assert( Vec_IntSum(vCounts[0]) == nFuncs );
        Vec_IntForEachEntry( vCounts[0], Count, i )
            if ( Count ) printf( "%d=%d (%.2f %%)  ", i, Count, 100.0*Count/nFuncs );
        printf( "\n" );
        printf( "Distribution of the %s number of rails for bound set size %d with no shared variables:\n", fTryAll ? "MINIMUM": "ORIGINAL", nBVars );
        assert( Vec_IntSum(vCounts[1]) == nFuncs );
        Vec_IntForEachEntry( vCounts[1], Count, i )
            if ( Count ) printf( "%d=%d (%.2f %%)  ", i, Count, 100.0*Count/nFuncs );
        printf( "\n" );
    }
    Vec_IntFree( vCounts[0] );
    Vec_IntFree( vCounts[1] );
    Abc_PrintTime( 1, "Total runtime", Abc_Clock() - clkTotal );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
