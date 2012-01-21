/**CFile****************************************************************

  FileName    [ifDec07.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [Performs additional check.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: ifDec07.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "if.h"
#include "src/misc/extra/extra.h"
#include "src/bool/kit/kit.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// the bit count for the first 256 integer numbers
static int BitCount8[256] = {
    0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,
    1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,
    1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,
    2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,
    1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,
    2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,
    2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,
    3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,4,5,5,6,5,6,6,7,5,6,6,7,6,7,7,8
};
// variable swapping code
static word PMasks[5][3] = {
    { 0x9999999999999999, 0x2222222222222222, 0x4444444444444444 },
    { 0xC3C3C3C3C3C3C3C3, 0x0C0C0C0C0C0C0C0C, 0x3030303030303030 },
    { 0xF00FF00FF00FF00F, 0x00F000F000F000F0, 0x0F000F000F000F00 },
    { 0xFF0000FFFF0000FF, 0x0000FF000000FF00, 0x00FF000000FF0000 },
    { 0xFFFF00000000FFFF, 0x00000000FFFF0000, 0x0000FFFF00000000 }
};
// elementary truth tables
static word Truth6[6] = {
    0xAAAAAAAAAAAAAAAA,
    0xCCCCCCCCCCCCCCCC,
    0xF0F0F0F0F0F0F0F0,
    0xFF00FF00FF00FF00,
    0xFFFF0000FFFF0000,
    0xFFFFFFFF00000000
};
static word Truth7[7][2] = {
    0xAAAAAAAAAAAAAAAA,0xAAAAAAAAAAAAAAAA,
    0xCCCCCCCCCCCCCCCC,0xCCCCCCCCCCCCCCCC,
    0xF0F0F0F0F0F0F0F0,0xF0F0F0F0F0F0F0F0,
    0xFF00FF00FF00FF00,0xFF00FF00FF00FF00,
    0xFFFF0000FFFF0000,0xFFFF0000FFFF0000,
    0xFFFFFFFF00000000,0xFFFFFFFF00000000,
    0x0000000000000000,0xFFFFFFFFFFFFFFFF
};

extern void Kit_DsdPrintFromTruth( unsigned * pTruth, int nVars );
extern void Extra_PrintBinary( FILE * pFile, unsigned Sign[], int nBits );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

void If_DecPrintConfig( word z )
{
   unsigned S[1];
   S[0] = (z & 0xffff) | ((z & 0xffff) << 16);
   Extra_PrintBinary( stdout, S, 16 ); 
   printf( " " );
   Kit_DsdPrintFromTruth( S, 4 );
   printf( " " );
   printf( " %d", (z >> 16) & 7 );
   printf( " %d", (z >> 20) & 7 );
   printf( " %d", (z >> 24) & 7 );
   printf( " %d", (z >> 28) & 7 );
   printf( "   " );
   S[0] = ((z >> 32) & 0xffff) | (((z >> 32) & 0xffff) << 16);
   Extra_PrintBinary( stdout, S, 16 );
   printf( " " );
   Kit_DsdPrintFromTruth( S, 4 );
   printf( " " );
   printf( " %d", (z >> 48) & 7 );
   printf( " %d", (z >> 52) & 7 );
   printf( " %d", (z >> 56) & 7 );
   printf( " %d", (z >> 60) & 7 );
   printf( "\n" );
}

// verification for 6-input function
static word If_Dec6ComposeLut4( int t, word f[4] )
{
    int m, v;
    word c, r = 0;
    for ( m = 0; m < 16; m++ )
    {
        if ( !((t >> m) & 1) )
            continue;
        c = ~0;
        for ( v = 0; v < 4; v++ )
            c &= ((m >> v) & 1) ? f[v] : ~f[v];
        r |= c;
    }
    return r;
}
void If_Dec6Verify( word t, word z )
{
    word r, q, f[4];
    int i, v;
    assert( z );
    for ( i = 0; i < 4; i++ )
    {
        v = (z >> (16+(i<<2))) & 7;
        assert( v != 7 );
        f[i] = Truth6[v];
    }
    q = If_Dec6ComposeLut4( (int)(z & 0xffff), f );
    for ( i = 0; i < 4; i++ )
    {
        v = (z >> (48+(i<<2))) & 7;
        f[i] = (v == 7) ? q : Truth6[v];
    }
    r = If_Dec6ComposeLut4( (int)((z >> 32) & 0xffff), f );
    if ( r != t )
    {
        If_DecPrintConfig( z );
        Kit_DsdPrintFromTruth( (unsigned*)&t, 6 ); printf( "\n" );
        Kit_DsdPrintFromTruth( (unsigned*)&q, 6 ); printf( "\n" );
        Kit_DsdPrintFromTruth( (unsigned*)&r, 6 ); printf( "\n" );
        printf( "Verification failed!\n" );
    }
}
// verification for 7-input function
static void If_Dec7ComposeLut4( int t, word f[4][2], word r[2] )
{
    int m, v;
    word c[2];
    r[0] = r[1] = 0;
    for ( m = 0; m < 16; m++ )
    {
        if ( !((t >> m) & 1) )
            continue;
        c[0] = c[1] = ~0;
        for ( v = 0; v < 4; v++ )
        {
            c[0] &= ((m >> v) & 1) ? f[v][0] : ~f[v][0];
            c[1] &= ((m >> v) & 1) ? f[v][1] : ~f[v][1];
        }
        r[0] |= c[0];
        r[1] |= c[1];
    }
}
void If_Dec7Verify( word t[2], word z )
{
    word f[4][2], r[2];
    int i, v;
    assert( z );
    for ( i = 0; i < 4; i++ )
    {
        v = (z >> (16+(i<<2))) & 7;
        f[i][0] = Truth7[v][0];
        f[i][1] = Truth7[v][1];
    }
    If_Dec7ComposeLut4( (int)(z & 0xffff), f, r );
    f[3][0] = r[0];
    f[3][1] = r[1];
    for ( i = 0; i < 3; i++ )
    {
        v = (z >> (48+(i<<2))) & 7;
        f[i][0] = Truth7[v][0];
        f[i][1] = Truth7[v][1];
    }
    If_Dec7ComposeLut4( (int)((z >> 32) & 0xffff), f, r );
    if ( r[0] != t[0] || r[1] != t[1] )
    {
        If_DecPrintConfig( z );
        Kit_DsdPrintFromTruth( (unsigned*)t, 7 ); printf( "\n" );
        Kit_DsdPrintFromTruth( (unsigned*)r, 7 ); printf( "\n" );
        printf( "Verification failed!\n" );
    }
}


// count the number of unique cofactors
static inline int If_Dec6CofCount2( word t )
{
    int i, Mask = 0;
    for ( i = 0; i < 16; i++ )
        Mask |= (1 << ((t >> (i<<2)) & 15));
    return BitCount8[((unsigned char*)&Mask)[0]] + BitCount8[((unsigned char*)&Mask)[1]];
}
// count the number of unique cofactors (up to 3)
static inline int If_Dec7CofCount3( word t[2] )
{
    unsigned char * pTruth = (unsigned char *)t;
    int i, iCof2 = 0;
    for ( i = 1; i < 16; i++ )
    {
        if ( pTruth[i] == pTruth[0] )
            continue;
        if ( iCof2 == 0 )
            iCof2 = i;
        else if ( pTruth[i] != pTruth[iCof2] )
            return 3;
    }
    assert( iCof2 );
    return 2;
}

// permute 6-input function
static inline word If_Dec6SwapAdjacent( word t, int v )
{
    assert( v < 5 );
    return (t & PMasks[v][0]) | ((t & PMasks[v][1]) << (1 << v)) | ((t & PMasks[v][2]) >> (1 << v));
}
static inline word If_Dec6MoveTo( word t, int v, int p, int Pla2Var[6], int Var2Pla[6] )
{
    int iPlace0, iPlace1;
    assert( Var2Pla[v] >= p );
    while ( Var2Pla[v] != p )
    {
        iPlace0 = Var2Pla[v]-1;
        iPlace1 = Var2Pla[v];
        t = If_Dec6SwapAdjacent( t, iPlace0 );
        Var2Pla[Pla2Var[iPlace0]]++;
        Var2Pla[Pla2Var[iPlace1]]--;
        Pla2Var[iPlace0] ^= Pla2Var[iPlace1];
        Pla2Var[iPlace1] ^= Pla2Var[iPlace0];
        Pla2Var[iPlace0] ^= Pla2Var[iPlace1];
    }
    assert( Pla2Var[p] == v );
    return t;
}

// permute 7-input function
static inline void If_Dec7SwapAdjacent( word t[2], int v )
{
    if ( v == 5 )
    {
        unsigned Temp = (t[0] >> 32);
        t[0]  = (t[0] & 0xFFFFFFFF) | ((t[1] & 0xFFFFFFFF) << 32);
        t[1] ^= (t[1] & 0xFFFFFFFF) ^ Temp;
        return;
    }
    assert( v < 5 );
    t[0] = If_Dec6SwapAdjacent( t[0], v );
    t[1] = If_Dec6SwapAdjacent( t[1], v );
}
static inline void If_Dec7MoveTo( word t[2], int v, int p, int Pla2Var[7], int Var2Pla[7] )
{
    int iPlace0, iPlace1;
    assert( Var2Pla[v] >= p );
    while ( Var2Pla[v] != p )
    {
        iPlace0 = Var2Pla[v]-1;
        iPlace1 = Var2Pla[v];
        If_Dec7SwapAdjacent( t, iPlace0 );
        Var2Pla[Pla2Var[iPlace0]]++;
        Var2Pla[Pla2Var[iPlace1]]--;
        Pla2Var[iPlace0] ^= Pla2Var[iPlace1];
        Pla2Var[iPlace1] ^= Pla2Var[iPlace0];
        Pla2Var[iPlace0] ^= Pla2Var[iPlace1];
    }
    assert( Pla2Var[p] == v );
}

// derive binary function
static inline int If_Dec6DeriveCount2( word t, int * pCof0, int * pCof1 )
{
    int i, Mask = 0;
    *pCof0 = (t & 15);
    *pCof1 = (t & 15);
    for ( i = 1; i < 16; i++ )
        if ( *pCof0 != ((t >> (i<<2)) & 15) )
        {
            *pCof1 = ((t >> (i<<2)) & 15);
            Mask |= (1 << i);
        }
    return Mask;
}
static inline int If_Dec7DeriveCount3( word t[2], int * pCof0, int * pCof1 )
{
    unsigned char * pTruth = (unsigned char *)t;
    int i, Mask = 0;
    *pCof0 = pTruth[0];
    *pCof1 = pTruth[0];
    for ( i = 1; i < 16; i++ )
        if ( *pCof0 != pTruth[i] )
        {
            *pCof1 = pTruth[i];
            Mask |= (1 << i);
        }
    return Mask;
}

// derives decomposition
static inline word If_Dec6Cofactor( word t, int iVar, int fCof1 )
{
    assert( iVar >= 0 && iVar < 6 );
    if ( fCof1 )
        return (t & Truth6[iVar]) | ((t & Truth6[iVar]) >> (1<<iVar));
    else
        return (t &~Truth6[iVar]) | ((t &~Truth6[iVar]) << (1<<iVar));
}
static word If_Dec6DeriveDisjoint( word t, int Pla2Var[6], int Var2Pla[6] )
{
    int i, Cof0, Cof1;
    word z = If_Dec6DeriveCount2( t, &Cof0, &Cof1 );
    for ( i = 0; i < 4; i++ )
        z |= (((word)Pla2Var[i+2]) << (16 + 4*i));
    z |= ((word)((Cof1 << 4) | Cof0) << 32);
    z |= ((word)((Cof1 << 4) | Cof0) << 40);
    for ( i = 0; i < 2; i++ )
        z |= (((word)Pla2Var[i]) << (48 + 4*i));
    z |= (((word)7) << (48 + 4*i++));
    assert( i == 3 );
    return z;
}
static word If_Dec6DeriveNonDisjoint( word t, int s, int Pla2Var0[6], int Var2Pla0[6] )
{
    word z, c0, c1;
    int Cof0[2], Cof1[2];
    int Truth0, Truth1, i;
    int Pla2Var[6], Var2Pla[6];
    assert( s >= 2 && s <= 5 );
    for ( i = 0; i < 6; i++ )
    {
        Pla2Var[i] = Pla2Var0[i];
        Var2Pla[i] = Var2Pla0[i];
    }
    for ( i = s; i < 5; i++ )
    {
        t = If_Dec6SwapAdjacent( t, i );
        Var2Pla[Pla2Var[i]]++;
        Var2Pla[Pla2Var[i+1]]--;
        Pla2Var[i] ^= Pla2Var[i+1];
        Pla2Var[i+1] ^= Pla2Var[i];
        Pla2Var[i] ^= Pla2Var[i+1];
    }
    c0 = If_Dec6Cofactor( t, 5, 0 );
    c1 = If_Dec6Cofactor( t, 5, 1 );
    assert( 2 >= If_Dec6CofCount2(c0) );
    assert( 2 >= If_Dec6CofCount2(c1) );
    Truth0 = If_Dec6DeriveCount2( c0, &Cof0[0], &Cof0[1] );
    Truth1 = If_Dec6DeriveCount2( c1, &Cof1[0], &Cof1[1] );
    z = ((Truth1 & 0xFF) << 8) | (Truth0 & 0xFF);
    for ( i = 0; i < 4; i++ )
        z |= (((word)Pla2Var[i+2]) << (16 + 4*i));
    z |= ((word)((Cof0[1] << 4) | Cof0[0]) << 32);
    z |= ((word)((Cof1[1] << 4) | Cof1[0]) << 40);
    for ( i = 0; i < 2; i++ )
        z |= (((word)Pla2Var[i]) << (48 + 4*i));
    z |= (((word)7) << (48 + 4*i++));
    z |= (((word)Pla2Var[5]) << (48 + 4*i++));
    assert( i == 4 );
    return z;
}
static word If_Dec7DeriveDisjoint( word t[2], int Pla2Var[7], int Var2Pla[7] )
{
    int i, Cof0, Cof1;
    word z = If_Dec7DeriveCount3( t, &Cof0, &Cof1 );
    for ( i = 0; i < 4; i++ )
        z |= (((word)Pla2Var[i+3]) << (16 + 4*i));
    z |= ((word)((Cof1 << 8) | Cof0) << 32);
    for ( i = 0; i < 3; i++ )
        z |= (((word)Pla2Var[i]) << (48 + 4*i));
    z |= (((word)7) << (48 + 4*i));
    return z;
}

static inline int If_Dec6CountOnes( word t )
{
    t =    (t & 0x5555555555555555) + ((t>> 1) & 0x5555555555555555);
    t =    (t & 0x3333333333333333) + ((t>> 2) & 0x3333333333333333);
    t =    (t & 0x0F0F0F0F0F0F0F0F) + ((t>> 4) & 0x0F0F0F0F0F0F0F0F);
    t =    (t & 0x00FF00FF00FF00FF) + ((t>> 8) & 0x00FF00FF00FF00FF);
    t =    (t & 0x0000FFFF0000FFFF) + ((t>>16) & 0x0000FFFF0000FFFF);
    return (t & 0x00000000FFFFFFFF) +  (t>>32);
}
static inline int If_Dec6HasVar( word t, int v )
{
    return ((t & Truth6[v]) >> (1<<v)) != (t & ~Truth6[v]);
}
static inline int If_Dec7HasVar( word t[2], int v )
{
    assert( v >= 0 && v < 7 );
    if ( v == 6 )
        return t[0] != t[1]; 
    return ((t[0] & Truth6[v]) >> (1<<v)) != (t[0] & ~Truth6[v])
        || ((t[1] & Truth6[v]) >> (1<<v)) != (t[1] & ~Truth6[v]);
}

static inline void If_DecVerifyPerm( int Pla2Var[6], int Var2Pla[6] )
{
    int i;
    for ( i = 0; i < 6; i++ )
        assert( Pla2Var[Var2Pla[i]] == i );
} 
word If_Dec6Perform( word t, int fDerive )
{ 
    word r = 0;
    int i, v, u, x, Count, Pla2Var[6], Var2Pla[6];
    // start arrays
    for ( i = 0; i < 6; i++ )
    {
        assert( If_Dec6HasVar( t, i ) );
        Pla2Var[i] = Var2Pla[i] = i;
    }
    // generate permutations
    i = 0;
    for ( v = 0;   v < 6; v++ )
    for ( u = v+1; u < 6; u++, i++ )
    {
        t = If_Dec6MoveTo( t, v, 0, Pla2Var, Var2Pla );
        t = If_Dec6MoveTo( t, u, 1, Pla2Var, Var2Pla );
//        If_DecVerifyPerm( Pla2Var, Var2Pla );
        Count = If_Dec6CofCount2( t );
        assert( Count > 1 );
        if ( Count == 2 )
            return !fDerive ? 1 : If_Dec6DeriveDisjoint( t, Pla2Var, Var2Pla );
        // check non-disjoint decomposition
        if ( !r && (Count == 3 || Count == 4) )
        {
            for ( x = 0; x < 4; x++ )
            {
                word c0 = If_Dec6Cofactor( t, x+2, 0 );
                word c1 = If_Dec6Cofactor( t, x+2, 1 );
                if ( If_Dec6CofCount2( c0 ) <= 2 && If_Dec6CofCount2( c1 ) <= 2 )
                {
                    r = !fDerive ? 1 : If_Dec6DeriveNonDisjoint( t, x+2, Pla2Var, Var2Pla );
                    break;
                }
            }
        }
    }
    assert( i == 15 );
    return r;
}
word If_Dec7Perform( word t0[2], int fDerive )
{
    word t[2] = {t0[0], t0[1]}; 
    int i, v, u, y, Pla2Var[7], Var2Pla[7];
    // start arrays
    for ( i = 0; i < 7; i++ )
    {
        if ( i < 6 )
            assert( If_Dec6HasVar( t[0], i ) || If_Dec6HasVar( t[1], i ) );
        else
            assert( t[0] != t[1] );
        Pla2Var[i] = Var2Pla[i] = i;
    }
    // generate permutations
    for ( v = 0;   v < 7; v++ )
    for ( u = v+1; u < 7; u++ )
    for ( y = u+1; y < 7; y++ )
    {
        If_Dec7MoveTo( t, v, 0, Pla2Var, Var2Pla );
        If_Dec7MoveTo( t, u, 1, Pla2Var, Var2Pla );
        If_Dec7MoveTo( t, y, 2, Pla2Var, Var2Pla );
//        If_DecVerifyPerm( Pla2Var, Var2Pla );
        if ( If_Dec7CofCount3( t ) == 2 )
        {
            return !fDerive ? 1 : If_Dec7DeriveDisjoint( t, Pla2Var, Var2Pla );
        }
    }
    return 0;
}


// support minimization
static inline int If_DecSuppIsMinBase( int Supp )
{
    return (Supp & (Supp+1)) == 0;
}
static inline word If_Dec6TruthShrink( word uTruth, int nVars, int nVarsAll, unsigned Phase )
{
    int i, k, Var = 0;
    assert( nVarsAll <= 6 );
    for ( i = 0; i < nVarsAll; i++ )
        if ( Phase & (1 << i) )
        {
            for ( k = i-1; k >= Var; k-- )
                uTruth = If_Dec6SwapAdjacent( uTruth, k );
            Var++;
        }
    assert( Var == nVars );
    return uTruth;
}
word If_Dec6MinimumBase( word uTruth, int * pSupp, int nVarsAll, int * pnVars )
{
    int v, iVar = 0, uSupp = 0;
    assert( nVarsAll <= 6 );
    for ( v = 0; v < nVarsAll; v++ )
        if ( If_Dec6HasVar( uTruth, v ) )
        {
            uSupp |= (1 << v);
            if ( pSupp )
                pSupp[iVar] = pSupp[v];
            iVar++;
        }
    if ( pnVars )
        *pnVars = iVar;
    if ( If_DecSuppIsMinBase( uSupp ) )
        return uTruth;
    return If_Dec6TruthShrink( uTruth, iVar, nVarsAll, uSupp );
}

static inline void If_Dec7TruthShrink( word uTruth[2], int nVars, int nVarsAll, unsigned Phase )
{
    int i, k, Var = 0;
    assert( nVarsAll <= 7 );
    for ( i = 0; i < nVarsAll; i++ )
        if ( Phase & (1 << i) )
        {
            for ( k = i-1; k >= Var; k-- )
                If_Dec7SwapAdjacent( uTruth, k );
            Var++;
        }
    assert( Var == nVars );
}
void If_Dec7MinimumBase( word uTruth[2], int * pSupp, int nVarsAll, int * pnVars )
{
    int v, iVar = 0, uSupp = 0;
    assert( nVarsAll <= 7 );
    for ( v = 0; v < nVarsAll; v++ )
        if ( If_Dec7HasVar( uTruth, v ) )
        {
            uSupp |= (1 << v);
            if ( pSupp )
                pSupp[iVar] = pSupp[v];
            iVar++;
        }
    if ( pnVars )
        *pnVars = iVar;
    if ( If_DecSuppIsMinBase( uSupp ) )
        return;
    If_Dec7TruthShrink( uTruth, iVar, nVarsAll, uSupp );
}



// check for MUX decomposition
static inline int If_Dec6SuppSize( word t )
{
    int v, Count = 0;
    for ( v = 0; v < 6; v++ )
        if ( If_Dec6Cofactor(t, v, 0) != If_Dec6Cofactor(t, v, 1) )
            Count++;
    return Count;
}
static inline int If_Dec6CheckMux( word t )
{
    int v;
    for ( v = 0; v < 6; v++ )
        if ( If_Dec6SuppSize(If_Dec6Cofactor(t, v, 0)) < 5 &&
             If_Dec6SuppSize(If_Dec6Cofactor(t, v, 1)) < 5 )
             return v;
    return -1;
}

// check for MUX decomposition
static inline void If_Dec7Cofactor( word t[2], int iVar, int fCof1, word r[2] )
{
    assert( iVar >= 0 && iVar < 7 );
    if ( iVar == 6 )
    {
        if ( fCof1 )
            r[0] = r[1] = t[1];
        else
            r[0] = r[1] = t[0];
    }
    else
    {
        if ( fCof1 )
        {
            r[0] = (t[0] & Truth6[iVar]) | ((t[0] & Truth6[iVar]) >> (1<<iVar));
            r[1] = (t[1] & Truth6[iVar]) | ((t[1] & Truth6[iVar]) >> (1<<iVar));
        }
        else
        {
            r[0] = (t[0] &~Truth6[iVar]) | ((t[0] &~Truth6[iVar]) << (1<<iVar));
            r[1] = (t[1] &~Truth6[iVar]) | ((t[1] &~Truth6[iVar]) << (1<<iVar));
        }
    }
}
static inline int If_Dec7SuppSize( word t[2] )
{
    word c0[2], c1[2];
    int v, Count = 0;
    for ( v = 0; v < 7; v++ )
    {
        If_Dec7Cofactor( t, v, 0, c0 );
        If_Dec7Cofactor( t, v, 1, c1 );
        if ( c0[0] != c1[0] || c0[1] != c1[1] )
            Count++;
    }
    return Count;
}
static inline int If_Dec7CheckMux( word t[2] )
{
    word c0[2], c1[2];
    int v;
    for ( v = 0; v < 7; v++ )
    {
        If_Dec7Cofactor( t, v, 0, c0 );
        If_Dec7Cofactor( t, v, 1, c1 );
        if ( If_Dec7SuppSize(c0) < 5 && If_Dec7SuppSize(c1) < 5 )
            return v;
    }
    return -1;
}

// find the best MUX decomposition
int If_Dec6PickBestMux( word t, word Cofs[2] )
{
    int v, vBest = -1, Count0, Count1, CountBest = 1000;
    for ( v = 0; v < 6; v++ )
    {
        Count0 = If_Dec6SuppSize( If_Dec6Cofactor(t, v, 0) );
        Count1 = If_Dec6SuppSize( If_Dec6Cofactor(t, v, 1) );
        if ( Count0 < 5 && Count1 < 5 && CountBest > Count0 + Count1 )
        {
            CountBest = Count0 + Count1;
            vBest = v;
            Cofs[0] = If_Dec6Cofactor(t, v, 0);
            Cofs[1] = If_Dec6Cofactor(t, v, 1);
        }
    }
    return vBest;
}
int If_Dec7PickBestMux( word t[2], word c0r[2], word c1r[2] )
{
    word c0[2], c1[2];
    int v, vBest = -1, Count0, Count1, CountBest = 1000;
    for ( v = 0; v < 7; v++ )
    {
        If_Dec7Cofactor( t, v, 0, c0 );
        If_Dec7Cofactor( t, v, 1, c1 );
        Count0 = If_Dec7SuppSize(c0);
        Count1 = If_Dec7SuppSize(c1);
        if ( Count0 < 5 && Count1 < 5 && CountBest > Count0 + Count1 )
        {
            CountBest = Count0 + Count1;
            vBest = v;
            c0r[0] = c0[0]; c0r[1] = c0[1];
            c1r[0] = c1[0]; c1r[1] = c1[1];
        }
    }
    return vBest;
}


/**Function*************************************************************

  Synopsis    [Performs additional check.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CutPerformCheck07( If_Man_t * p, unsigned * pTruth, int nVars, int nLeaves, char * pStr )
{
    int fDerive = 0;
    if ( nLeaves < 6 )
        return 1;
    if ( nLeaves == 6 )
    {
        word z, t = ((word *)pTruth)[0];
        if ( If_Dec6CheckMux(t) >= 0 )
            return 1;
        z = If_Dec6Perform( t, fDerive );
        if ( fDerive && z )
        {
//            If_DecPrintConfig( z );
            If_Dec6Verify( t, z );
        }
        return z != 0;
    }
    if ( nLeaves == 7 )
    {
        word z, t[2];
        t[0] = ((word *)pTruth)[0];
        t[1] = ((word *)pTruth)[1];
        if ( If_Dec7CheckMux(t) >= 0 )
            return 1;
        z = If_Dec7Perform( t, fDerive );
        if ( fDerive && z )
            If_Dec7Verify( t, z );
        return z != 0;
    }
    assert( 0 );
    return 0;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

