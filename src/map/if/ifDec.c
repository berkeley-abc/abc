/**CFile****************************************************************

  FileName    [ifDec.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [Performs additional check.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: ifDec.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "if.h"

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
    0xFFFFFFFFFFFFFFFF,0x0000000000000000
};

extern void Kit_DsdPrintFromTruth( unsigned * pTruth, int nVars );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

// verification for 6-input function
static word If_Dec6ComposeLut4( int t, word f[4] )
{
    int m, v;
    word c, r = 0;
    for ( m = 0; m < 16; m++ )
    {
        c = ~0;
        for ( v = 0; v < 4; v++ )
            c &= ((m >> v) & 1) ? f[v] : ~f[v];
        r |= c;
    }
    return r;
}
static void If_Dec6Verify( word t, word z )
{
    word f[4];
    int i, v;
    for ( i = 0; i < 4; i++ )
    {
        v = (z >> (16+(i<<2))) & 7;
        f[i] = (v == 7) ? 0 : Truth6[v];
    }
    f[0] = If_Dec6ComposeLut4( (int)(z & 0xffff), f );
    for ( i = 0; i < 3; i++ )
    {
        v = (z >> (48+(i<<2))) & 7;
        f[i+1] = (v == 7) ? 0 : Truth6[v];
    }
    f[0] = If_Dec6ComposeLut4( (int)((z >> 32) & 0xffff), f );
    if ( f[0] != t )
        printf( "Verification failed!\n" );
}
// verification for 7-input function
static void If_Dec7ComposeLut4( int t, word f[4][2], word r[2] )
{
    int m, v;
    word c[2];
    r[0] = r[1] = 0;
    for ( m = 0; m < 16; m++ )
    {
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
static void If_Dec7Verify( word t[2], word z )
{
    word f[4][2], r[2];
    int i, v;
    for ( i = 0; i < 4; i++ )
    {
        v = (z >> (16+(i<<2))) & 7;
        f[i][0] = Truth7[v][0];
        f[i][1] = Truth7[v][1];
    }
    If_Dec7ComposeLut4( (int)(z & 0xffff), f, r );
    f[0][0] = r[0];
    f[0][1] = r[1];
    for ( i = 0; i < 3; i++ )
    {
        v = (z >> (48+(i<<2))) & 7;
        f[i+1][0] = Truth7[v][0];
        f[i+1][1] = Truth7[v][1];
    }
    If_Dec7ComposeLut4( (int)((z >> 32) & 0xffff), f, r );
    if ( r[0] != t[0] || r[1] != t[1] )
        printf( "Verification failed!\n" );
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


// derives decomposition
static word If_Dec6DeriveDisjoint( word t, int Pla2Var[6], int Var2Pla[6] )
{
    word z = 1;
//    If_Dec6Verify( t, z );
    return z;
}
static word If_Dec6DeriveNonDisjoint( word t, word c0, word c1, int s, int Pla2Var[6], int Var2Pla[6] )
{
    word z = 1;
//    If_Dec6Verify( t, z );
    return z;
}
static word If_Dec7DeriveDisjoint( word t[2], int Pla2Var[7], int Var2Pla[7] )
{
    word z = 1;
//    If_Dec7Verify( t, z );
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

static inline void If_DecVerifyPerm( int Pla2Var[6], int Var2Pla[6] )
{
    int i;
    for ( i = 0; i < 6; i++ )
        assert( Pla2Var[Var2Pla[i]] == i );
}
static inline word If_Dec6Cofactor( word t, int iVar, int fCof1 )
{
    assert( iVar >= 0 && iVar < 6 );
    if ( fCof1 )
        return (t & Truth6[iVar]) | ((t & Truth6[iVar]) >> (1<<iVar));
    else
        return (t &~Truth6[iVar]) | ((t &~Truth6[iVar]) << (1<<iVar));
}
static word If_Dec6Perform( word t )
{ 
    int i, v, u, x, Count, Pla2Var[6], Var2Pla[6];
    int fFound = 0;
//    if ( If_Dec6CountOnes(t) == 1 )
//        return 1;
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
            return If_Dec6DeriveDisjoint( t, Pla2Var, Var2Pla );
        // check non-disjoint decomposition
        if ( !fFound && (Count == 3 || Count == 4) )
        {
            for ( x = 0; x < 4; x++ )
            {
                word c0 = If_Dec6Cofactor( t, Pla2Var[x+2], 0 );
                word c1 = If_Dec6Cofactor( t, Pla2Var[x+2], 1 );
                if ( If_Dec6CofCount2( c0 ) <= 2 && If_Dec6CofCount2( c1 ) <= 2 )
                {
                    fFound = 1;
                    break;
                 //   return If_Dec6DeriveNonDisjoint( t, c0, c1, x+2, Pla2Var, Var2Pla );
                }
            }
        }
    }
    assert( i == 15 );
    return fFound;
}
static word If_Dec7Perform( word t0[2] )
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
            return If_Dec7DeriveDisjoint( t, Pla2Var, Var2Pla );
    }
    return 0;
}


/**Function*************************************************************

  Synopsis    [Performs additional check.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CutPerformCheckInt( unsigned * pTruth, int nVars, int nLeaves )
{
    if ( nLeaves < 6 )
        return 1;
    if ( nLeaves == 6 )
    {
        word t = ((word *)pTruth)[0];
        return If_Dec6Perform( t ) != 0;
    }
    if ( nLeaves == 7 )
    {
        word t[2];
        t[0] = ((word *)pTruth)[0];
        t[1] = ((word *)pTruth)[1];
        return If_Dec7Perform( t ) != 0;
    }
    assert( 0 );
    return 0;
}
int If_CutPerformCheck( unsigned * pTruth, int nVars, int nLeaves )
{
    int RetValue = If_CutPerformCheckInt( pTruth, nVars, nLeaves );
/*
//    if ( nLeaves == 6 || nLeaves == 7 )
    if ( nLeaves == 7 )
    {
        if ( RetValue == 0 )
        {
            printf( "%d ", RetValue );
            Kit_DsdPrintFromTruth( pTruth, nLeaves );
            printf( "\n" );
            If_CutPerformCheckInt( pTruth, nVars, nLeaves );
        }
    }
*/
    return RetValue;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

