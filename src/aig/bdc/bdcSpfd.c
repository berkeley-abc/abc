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

static inline word Bdc_Cof6( word t, int iVar, int fCof1 )
{
    assert( iVar >= 0 && iVar < 6 );
    if ( fCof1 )
        return (t & Truths[iVar]) | ((t & Truths[iVar]) >> (1<<iVar));
    else
        return (t &~Truths[iVar]) | ((t &~Truths[iVar]) << (1<<iVar));
}


extern void Abc_Show6VarFunc( word F0, word F1 );

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
void Bdc_SpfdPrint( Bdc_Nod_t * pNode, int Level, Vec_Ptr_t * vLevels, word Truth )
{
    word Diff = Truth ^ pNode->Truth;
    Extra_PrintHex( stdout, (unsigned *)&pNode->Truth, 6 ); printf( "   " );
    Extra_PrintHex( stdout, (unsigned *)&Diff, 6 );         printf( "   " );
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
    Vec_Int_t * vBegs, * vWeight;
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
    vBegs = Vec_IntAlloc( 100 );
    vWeight = Vec_IntAlloc( 100 );

    // initialize elementary variables
    pNode = ABC_CALLOC( Bdc_Nod_t, nVars );
    for ( i = 0; i < nVars; i++ )
        pNode[i].Truth  = Truths[i];
    for ( i = 0; i < nVars; i++ )
        pNode[i].Weight = Bdc_CountSpfd( pNode[i].Truth, Truth );
    Vec_PtrPush( vLevels, pNode );
    Vec_IntPush( vBegs, nVars );

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
    Vec_IntPush( vBegs, c );
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
        Count1 = Vec_IntEntry( vBegs, n-1 );
        // go through previous levels
        for ( k = 0; k < n-1; k++ )
        {
            pNode0 = Vec_PtrEntry( vLevels, k );
            Count0 = Vec_IntEntry( vBegs, k );
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
if ( pNode[i].Weight > 300 )
Bdc_SpfdPrint( pNode + i, 1, vLevels, Truth );
            Vec_IntPush( vWeight, pNode[i].Weight );

            if ( Truth == pNode[i].Truth || Truth == ~pNode[i].Truth )
            {
                printf( "Function can be implemented using %d gates.\n", n );
                Bdc_SpfdPrint( pNode + i, n, vLevels, Truth );
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
        Vec_IntPush( vBegs, j );

printf( "Selected %6d gates (out of %6d) on level %2d.   ", j, c, n );
Abc_PrintTime( 1, "Time", clock() - clk );

        for ( i = 0; i < 10; i++ )
            Bdc_SpfdPrint( pNode2 + i, n, vLevels, Truth );
    }

cleanup:
    ABC_FREE( pNode );
    Vec_PtrForEachEntry( Bdc_Nod_t *, vLevels, pNode, i )
        ABC_FREE( pNode );
    Vec_PtrFree( vLevels );
    Vec_IntFree( vBegs );
    Vec_IntFree( vWeight );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Bdc_SpfdDecomposeTest_()
{
    int fTry = 0;
//    word T[17];
//    int i;

//    word Truth    = Truths[0] & ~Truths[3];
//    word Truth    = (Truths[0] & Truths[1]) | (Truths[2] & Truths[3]) | (Truths[4] & Truths[5]);
//    word Truth    = (Truths[0] & Truths[1]) | ((Truths[2] & ~Truths[3]) ^ (Truths[4] & ~Truths[5]));
//    word Truth    = (Truths[0] & Truths[1]) | (Truths[2] & Truths[3]);
//    word Truth = 0x9ef7a8d9c7193a0f;  // AAFFAAFF0A0F0A0F
//    word Truth = 0x34080226CD163000;
    word Truth = 0x5052585a0002080a;
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




typedef struct Bdc_Ent_t_ Bdc_Ent_t; // 24 bytes
struct Bdc_Ent_t_
{
    unsigned         iFan0   : 30;
    unsigned         fCompl0 :  1;
    unsigned         fCompl  :  1;
    unsigned         iFan1   : 30;
    unsigned         fCompl1 :  1;
    unsigned         fExor   :  1;
    int              iNext;
    int              iList;
    word             Truth;
};

#define BDC_TERM 0x3FFFFFFF

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Bdc_SpfdHashValue( word t, int Size )
{
    // http://planetmath.org/encyclopedia/GoodHashTablePrimes.html
    // 53,
    // 97,
    // 193,
    // 389,
    // 769,
    // 1543,
    // 3079,
    // 6151,
    // 12289,
    // 24593,
    // 49157,
    // 98317,
    // 196613,
    // 393241,
    // 786433,
    // 1572869,
    // 3145739,
    // 6291469,
    // 12582917,
    // 25165843,
    // 50331653,
    // 100663319,
    // 201326611,
    // 402653189,
    // 805306457,
    // 1610612741,
    static unsigned BigPrimes[8] = {12582917, 25165843, 50331653, 100663319, 201326611, 402653189, 805306457, 1610612741};
    unsigned char * s = (unsigned char *)&t;
    unsigned i, Value = 0;
    for ( i = 0; i < 8; i++ )
        Value ^= BigPrimes[i] * s[i];
    return Value % Size;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int * Bdc_SpfdHashLookup( Bdc_Ent_t * p, int Size, word t )
{
    Bdc_Ent_t * pBin = p + Bdc_SpfdHashValue( t, Size );
    if ( pBin->iList == 0 )
        return &pBin->iList;
    for ( pBin = p + pBin->iList; ; pBin = p + pBin->iNext )
    {
        if ( pBin->Truth == t )
            return NULL;
        if ( pBin->iNext == 0 )
            return &pBin->iNext;
    }
    assert( 0 );
    return NULL;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Wrd_t * Bdc_SpfdDecomposeTest__( Vec_Int_t ** pvWeights )
{
    int nFuncs = 3000000; // the number of functions to compute
    int nSize  = 2777111; // the hash table size to use
    int Limit  = 5;

    
//    int nFuncs = 13000000; // the number of functions to compute
//    int nSize  = 12582917; // the hash table size to use
//    int Limit  = 6;

//    int nFuncs =  60000000; // the number of functions to compute
//    int nSize  =  50331653; // the hash table size to use
//    int Limit  = 6;

    int * pPlace, i, n, m, s, fCompl, clk = clock(), clk2;
    Vec_Int_t * vStops;
    Vec_Wrd_t * vTruths;
    Vec_Int_t * vWeights;
    Bdc_Ent_t * p, * q, * pBeg0, * pEnd0, * pBeg1, * pEnd1, * pThis0, * pThis1;
    word t0, t1, t;
    assert( nSize <= nFuncs );

    printf( "Allocating %.2f Mb of internal memory.\n", 1.0*sizeof(Bdc_Ent_t)*nFuncs/(1<<20) );

    p = (Bdc_Ent_t *)calloc( nFuncs, sizeof(Bdc_Ent_t) );
    memset( p, 255, sizeof(Bdc_Ent_t) );
    p->iList = 0;
    q = p + 1;
    printf( "Added %d + %d + 0 = %d. Total = %8d.\n", 0, 0, 0, q-p );

    vTruths = Vec_WrdAlloc( 100 );
    vWeights = Vec_IntAlloc( 100 );

    // create elementary vars
    vStops = Vec_IntAlloc( 10 );
    Vec_IntPush( vStops, 1 );
    for ( i = 0; i < 6; i++ )
    {
        q->iFan0 = BDC_TERM;
        q->iFan1 = i;
        q->Truth = Truths[i];
        pPlace   = Bdc_SpfdHashLookup( p, nSize, q->Truth );
        *pPlace  = q-p;
        q++;
        Vec_WrdPush( vTruths, Truths[i] );
        Vec_IntPush( vWeights, 0 );
    }
    Vec_IntPush( vStops, 7 );
    printf( "Added %d + %d + 0 = %d. Total = %8d.\n", 0, 0, 0, q-p );

    // create gates
    for ( n = 0; n < 10; n++ )
    {
        // set the start and stop
        pBeg1 = p + Vec_IntEntry( vStops, n );
        pEnd1 = p + Vec_IntEntry( vStops, n+1 );

        // try previous
        for ( m = 0; m < n; m++ )
        if ( m+n+1 <= Limit )
        {
            clk2 = clock();
            pBeg0 = p + Vec_IntEntry( vStops, m );
            pEnd0 = p + Vec_IntEntry( vStops, m+1 );
            printf( "Trying %6d x %6d.  ", pEnd0-pBeg0, pEnd1-pBeg1 );
            for ( pThis0 = pBeg0; pThis0 < pEnd0; pThis0++ )
            for ( pThis1 = pBeg1; pThis1 < pEnd1; pThis1++ )
            for ( s = 0; s < 5; s++ )
            {
                t0 = (s&1)      ? ~pThis0->Truth : pThis0->Truth;
                t1 = ((s>>1)&1) ? ~pThis1->Truth : pThis1->Truth;
                t  = ((s>>2)&1) ? t0 ^ t1 : t0 & t1;
                fCompl = t & 1;
                if ( fCompl )
                    t = ~t;
                if ( t == 0 )
                    continue;
                pPlace = Bdc_SpfdHashLookup( p, nSize, t );
                if ( pPlace == NULL )
                    continue;
                q->iFan0   = pThis0-p;
                q->fCompl0 = s&1;
                q->iFan1   = pThis1-p;
                q->fCompl1 = (s>>1)&1;
                q->fExor   = (s>>2)&1;
                q->Truth   = t;
                q->fCompl  = fCompl;
                *pPlace = q-p;
                q++;
                Vec_WrdPush( vTruths, t );
                Vec_IntPush( vWeights, m+n+1 );
                if ( q-p == nFuncs )
                    goto finish;
            }
            Vec_IntPush( vStops, q-p );
            printf( "Added %d + %d + 1 = %d. Total = %8d.   ", m, n, m+n+1, q-p );
            Abc_PrintTime( 1, "Time", clock() - clk2 );
        }
        if ( n+n+1 > Limit )
            continue;

        // try current
        clk2 = clock();
        printf( "Trying %6d x %6d.  ", pEnd1-pBeg1, pEnd1-pBeg1 );
        for ( pThis0 = pBeg1; pThis0 < pEnd1; pThis0++ )
        for ( pThis1 = pThis0+1; pThis1 < pEnd1; pThis1++ )
        for ( s = 0; s < 5; s++ )
        {
            t0 = (s&1)      ? ~pThis0->Truth : pThis0->Truth;
            t1 = ((s>>1)&1) ? ~pThis1->Truth : pThis1->Truth;
            t  = ((s>>2)&1) ? t0 ^ t1 : t0 & t1;
            fCompl = t & 1;
            if ( fCompl )
                t = ~t;
            if ( t == 0 )
                continue;
            pPlace = Bdc_SpfdHashLookup( p, nSize, t );
            if ( pPlace == NULL )
                continue;
            q->iFan0   = pThis0-p;
            q->fCompl0 = s&1;
            q->iFan1   = pThis1-p;
            q->fCompl1 = (s>>1)&1;
            q->fExor   = (s>>2)&1;
            q->Truth   = t;
            q->fCompl  = fCompl;
            *pPlace = q-p;
            q++;
            Vec_WrdPush( vTruths, t );
            Vec_IntPush( vWeights, n+n+1 );
            if ( q-p == nFuncs )
                goto finish;
        }
        Vec_IntPush( vStops, q-p );
        assert( n || q-p == 82 );
        printf( "Added %d + %d + 1 = %d. Total = %8d.   ", n, n, n+n+1, q-p );
        Abc_PrintTime( 1, "Time", clock() - clk2 );
    }
    Abc_PrintTime( 1, "Time", clock() - clk );

/*
    {
        FILE * pFile = fopen( "func6var5node.txt", "w" );
        word t;
        Vec_WrdSortUnsigned( vTruths );
        Vec_WrdForEachEntry( vTruths, t, i )
            Extra_PrintHex( pFile, (unsigned *)&t, 6 ), fprintf( pFile, "\n" );
        fclose( pFile );
    }
*/
    {
        FILE * pFile = fopen( "func6v5n_bin.txt", "wb" );
//        Vec_WrdSortUnsigned( vTruths );
        fwrite( Vec_WrdArray(vTruths), sizeof(word), Vec_WrdSize(vTruths), pFile );
        fclose( pFile );
    }
    {
        FILE * pFile = fopen( "func6v5nW_bin.txt", "wb" );
        fwrite( Vec_IntArray(vWeights), sizeof(int), Vec_IntSize(vWeights), pFile );
        fclose( pFile );
    }

finish:
    Vec_IntFree( vStops );
//    Vec_WrdFree( vTruths );
    free( p );

    *pvWeights = vWeights;
    return vTruths;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Wrd_t * Bdc_SpfdReadFiles( Vec_Int_t ** pvWeights )
{
    Vec_Int_t * vWeights;
    Vec_Wrd_t * vDivs = Vec_WrdStart( 12776759 );
    FILE * pFile = fopen( "func6v6n_bin.txt", "rb" );
    fread( Vec_WrdArray(vDivs), sizeof(word), Vec_WrdSize(vDivs), pFile );
    fclose( pFile );

    vWeights = Vec_IntStart( 12776759 );
    pFile = fopen( "func6v6nW_bin.txt", "rb" );
    fread( Vec_IntArray(vWeights), sizeof(int), Vec_IntSize(vWeights), pFile );
    fclose( pFile );

    *pvWeights = vWeights;
    return vDivs;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Bdc_SpfdComputeCost( word f, int i, Vec_Int_t * vWeights )
{
    int Ones = Bdc_CountOnes(f);
    if ( Ones == 0 )
        return -1;
    return 7*Ones + 10*(8 - Vec_IntEntry(vWeights, i));
//    return Bdc_CountOnes(f);
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
word Bdc_SpfdFindBest( Vec_Wrd_t * vDivs, Vec_Int_t * vWeights, word F0, word F1, int * pCost )
{
    word Func, FuncBest;
    int i, Cost, CostBest = -1, NumBest;
    Vec_WrdForEachEntry( vDivs, Func, i )
    {
        if ( (Func & F0) == 0 )
        {
            Cost = Bdc_SpfdComputeCost(Func & F1, i, vWeights);
            if ( CostBest < Cost )
            {
                CostBest = Cost;
                FuncBest = Func;
                NumBest  = i;
            }
        }
        if ( (Func & F1) == 0 )
        {
            Cost = Bdc_SpfdComputeCost(Func & F0, i, vWeights);
            if ( CostBest < Cost )
            {
                CostBest = Cost;
                FuncBest = Func;
                NumBest  = i;
            }
        }
        if ( (~Func & F0) == 0 )
        {
            Cost = Bdc_SpfdComputeCost(~Func & F1, i, vWeights);
            if ( CostBest < Cost )
            {
                CostBest = Cost;
                FuncBest = ~Func;
                NumBest  = i;
            }
        }
        if ( (~Func & F1) == 0 )
        {
            Cost = Bdc_SpfdComputeCost(~Func & F0, i, vWeights);
            if ( CostBest < Cost )
            {
                CostBest = Cost;
                FuncBest = ~Func;
                NumBest  = i;
            }
        }
    }
    (*pCost) += Vec_IntEntry(vWeights, NumBest);
    assert( CostBest > 0 );
    printf( "Selected %8d with cost %2d and weight %d: ", NumBest, 0, Vec_IntEntry(vWeights, NumBest) );
    Extra_PrintHex( stdout, (unsigned *)&FuncBest, 6 ); printf( "\n" );
    return FuncBest;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Bdc_SpfdDecomposeTestOne( word t, Vec_Wrd_t * vDivs, Vec_Int_t * vWeights )
{
    word F1 = t;
    word F0 = ~F1;
    word Func;
    int i, Cost = 0;
//    Abc_Show6VarFunc( F0, F1 );   
    for ( i = 0; F0 && F1; i++ )
    {
        printf( "*** ITER %2d   ", i );
        Func = Bdc_SpfdFindBest( vDivs, vWeights, F0, F1, &Cost );
        F0 &= ~Func;
        F1 &= ~Func;
//        Abc_Show6VarFunc( F0, F1 );    
    }
    Cost += (i-1);
    printf( "Produce solution with cost %d.\n", Cost );
    return Cost;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Bdc_SpfdDecomposeTest()
{
//    word t = 0x5052585a0002080a;
    word t = 0x9ef7a8d9c7193a0f;
//    word t = 0x6BFDA276C7193A0F;
//    word t = 0xA3756AFE0B1DF60B;

    Vec_Int_t * vWeights;
    Vec_Wrd_t * vDivs;
    word c0, c1, s, tt, ttt, tbest;
    int i, j, k, n, Cost, CostBest = 100000;
    int clk = clock();

    return;

    // vDivs = Bdc_SpfdDecomposeTest__( &vWeights );
    vDivs = Bdc_SpfdReadFiles( &vWeights );

//    Abc_Show6VarFunc( ~t, t );  

/*
    for ( i = 0; i < 6; i++ )
    for ( j = 0; j < 6; j++ )
    {
        if ( i == j )
            continue;
        c0 = Bdc_Cof6( t, i, 0 );
        c1 = Bdc_Cof6( t, i, 1 );
        s  = Truths[i] ^ Truths[j];
        tt = (~s & c0) | (s & c1);

        Cost = Bdc_SpfdDecomposeTestOne( tt, vDivs, vWeights );
        if ( CostBest > Cost )
        {
            CostBest = Cost;
            tbest = tt;
        }
    }
*/

    for ( i = 0; i < 6; i++ )
    for ( j = 0; j < 6; j++ )
    {
        if ( i == j )
            continue;
        c0 = Bdc_Cof6( t, i, 0 );
        c1 = Bdc_Cof6( t, i, 1 );
        s  = Truths[i] ^ Truths[j];
        tt = (~s & c0) | (s & c1);

        for ( k = 0; k < 6; k++ )
        for ( n = 0; n < 6; n++ )
        {
            if ( k == n )
                continue;
            c0 = Bdc_Cof6( tt, k, 0 );
            c1 = Bdc_Cof6( tt, k, 1 );
            s  = Truths[k] ^ Truths[n];
            ttt= (~s & c0) | (s & c1);

            Cost = Bdc_SpfdDecomposeTestOne( ttt, vDivs, vWeights );
            if ( CostBest > Cost )
            {
                CostBest = Cost;
                tbest = ttt;
            }
        }
    }


    printf( "Best solution found with cost %d.  ", CostBest );
    Extra_PrintHex( stdout, (unsigned *)&tbest, 6 ); //printf( "\n" );
    Abc_PrintTime( 1, "  Time", clock() - clk );

    Vec_WrdFree( vDivs );
    Vec_IntFree( vWeights );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

