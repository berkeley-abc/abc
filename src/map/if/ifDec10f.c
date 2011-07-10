/**CFile****************************************************************

  FileName    [ifDec10f.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [Fast checking procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: ifDec10f.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

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
static word Truth10[10][16] = {
    0xAAAAAAAAAAAAAAAA,0xAAAAAAAAAAAAAAAA,0xAAAAAAAAAAAAAAAA,0xAAAAAAAAAAAAAAAA,0xAAAAAAAAAAAAAAAA,0xAAAAAAAAAAAAAAAA,0xAAAAAAAAAAAAAAAA,0xAAAAAAAAAAAAAAAA,0xAAAAAAAAAAAAAAAA,0xAAAAAAAAAAAAAAAA,0xAAAAAAAAAAAAAAAA,0xAAAAAAAAAAAAAAAA,0xAAAAAAAAAAAAAAAA,0xAAAAAAAAAAAAAAAA,0xAAAAAAAAAAAAAAAA,0xAAAAAAAAAAAAAAAA,
    0xCCCCCCCCCCCCCCCC,0xCCCCCCCCCCCCCCCC,0xCCCCCCCCCCCCCCCC,0xCCCCCCCCCCCCCCCC,0xCCCCCCCCCCCCCCCC,0xCCCCCCCCCCCCCCCC,0xCCCCCCCCCCCCCCCC,0xCCCCCCCCCCCCCCCC,0xCCCCCCCCCCCCCCCC,0xCCCCCCCCCCCCCCCC,0xCCCCCCCCCCCCCCCC,0xCCCCCCCCCCCCCCCC,0xCCCCCCCCCCCCCCCC,0xCCCCCCCCCCCCCCCC,0xCCCCCCCCCCCCCCCC,0xCCCCCCCCCCCCCCCC,
    0xF0F0F0F0F0F0F0F0,0xF0F0F0F0F0F0F0F0,0xF0F0F0F0F0F0F0F0,0xF0F0F0F0F0F0F0F0,0xF0F0F0F0F0F0F0F0,0xF0F0F0F0F0F0F0F0,0xF0F0F0F0F0F0F0F0,0xF0F0F0F0F0F0F0F0,0xF0F0F0F0F0F0F0F0,0xF0F0F0F0F0F0F0F0,0xF0F0F0F0F0F0F0F0,0xF0F0F0F0F0F0F0F0,0xF0F0F0F0F0F0F0F0,0xF0F0F0F0F0F0F0F0,0xF0F0F0F0F0F0F0F0,0xF0F0F0F0F0F0F0F0,
    0xFF00FF00FF00FF00,0xFF00FF00FF00FF00,0xFF00FF00FF00FF00,0xFF00FF00FF00FF00,0xFF00FF00FF00FF00,0xFF00FF00FF00FF00,0xFF00FF00FF00FF00,0xFF00FF00FF00FF00,0xFF00FF00FF00FF00,0xFF00FF00FF00FF00,0xFF00FF00FF00FF00,0xFF00FF00FF00FF00,0xFF00FF00FF00FF00,0xFF00FF00FF00FF00,0xFF00FF00FF00FF00,0xFF00FF00FF00FF00,
    0xFFFF0000FFFF0000,0xFFFF0000FFFF0000,0xFFFF0000FFFF0000,0xFFFF0000FFFF0000,0xFFFF0000FFFF0000,0xFFFF0000FFFF0000,0xFFFF0000FFFF0000,0xFFFF0000FFFF0000,0xFFFF0000FFFF0000,0xFFFF0000FFFF0000,0xFFFF0000FFFF0000,0xFFFF0000FFFF0000,0xFFFF0000FFFF0000,0xFFFF0000FFFF0000,0xFFFF0000FFFF0000,0xFFFF0000FFFF0000,
    0xFFFFFFFF00000000,0xFFFFFFFF00000000,0xFFFFFFFF00000000,0xFFFFFFFF00000000,0xFFFFFFFF00000000,0xFFFFFFFF00000000,0xFFFFFFFF00000000,0xFFFFFFFF00000000,0xFFFFFFFF00000000,0xFFFFFFFF00000000,0xFFFFFFFF00000000,0xFFFFFFFF00000000,0xFFFFFFFF00000000,0xFFFFFFFF00000000,0xFFFFFFFF00000000,0xFFFFFFFF00000000,
    0x0000000000000000,0xFFFFFFFFFFFFFFFF,0x0000000000000000,0xFFFFFFFFFFFFFFFF,0x0000000000000000,0xFFFFFFFFFFFFFFFF,0x0000000000000000,0xFFFFFFFFFFFFFFFF,0x0000000000000000,0xFFFFFFFFFFFFFFFF,0x0000000000000000,0xFFFFFFFFFFFFFFFF,0x0000000000000000,0xFFFFFFFFFFFFFFFF,0x0000000000000000,0xFFFFFFFFFFFFFFFF,
    0x0000000000000000,0x0000000000000000,0xFFFFFFFFFFFFFFFF,0xFFFFFFFFFFFFFFFF,0x0000000000000000,0x0000000000000000,0xFFFFFFFFFFFFFFFF,0xFFFFFFFFFFFFFFFF,0x0000000000000000,0x0000000000000000,0xFFFFFFFFFFFFFFFF,0xFFFFFFFFFFFFFFFF,0x0000000000000000,0x0000000000000000,0xFFFFFFFFFFFFFFFF,0xFFFFFFFFFFFFFFFF,
    0x0000000000000000,0x0000000000000000,0x0000000000000000,0x0000000000000000,0xFFFFFFFFFFFFFFFF,0xFFFFFFFFFFFFFFFF,0xFFFFFFFFFFFFFFFF,0xFFFFFFFFFFFFFFFF,0x0000000000000000,0x0000000000000000,0x0000000000000000,0x0000000000000000,0xFFFFFFFFFFFFFFFF,0xFFFFFFFFFFFFFFFF,0xFFFFFFFFFFFFFFFF,0xFFFFFFFFFFFFFFFF,
    0x0000000000000000,0x0000000000000000,0x0000000000000000,0x0000000000000000,0x0000000000000000,0x0000000000000000,0x0000000000000000,0x0000000000000000,0xFFFFFFFFFFFFFFFF,0xFFFFFFFFFFFFFFFF,0xFFFFFFFFFFFFFFFF,0xFFFFFFFFFFFFFFFF,0xFFFFFFFFFFFFFFFF,0xFFFFFFFFFFFFFFFF,0xFFFFFFFFFFFFFFFF,0xFFFFFFFFFFFFFFFF
};

extern void Kit_DsdPrintFromTruth( unsigned * pTruth, int nVars );
extern void Extra_PrintBinary( FILE * pFile, unsigned Sign[], int nBits );

//  vars are numbered starting from MSB
//  moving down means moving from MSB -> LSB
//  moving up means moving from LSB -> MSB
//  groups list vars indices from MSB to LSB

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

// variable permutation for large functions
static inline int If_CluWordNum( int nVars )
{
    return nVars <= 6 ? 1 : 1 << (nVars-6);
}
static inline void If_CluCopy( word * pOut, word * pIn, int nVars )
{
    int w, nWords = If_CluWordNum( nVars );
    for ( w = 0; w < nWords; w++ )
        pOut[w] = pIn[w];
}
static inline void If_CluSwapAdjacent( word * pOut, word * pIn, int iVar, int nVars )
{
    int i, k, nWords = If_CluWordNum( nVars );
    assert( iVar < nVars - 1 );
    if ( iVar < 5 )
    {
        int Shift = (1 << iVar);
        for ( i = 0; i < nWords; i++ )
            pOut[i] = (pIn[i] & PMasks[iVar][0]) | ((pIn[i] & PMasks[iVar][1]) << Shift) | ((pIn[i] & PMasks[iVar][2]) >> Shift);
    }
    else if ( iVar > 5 )
    {
        int Step = (1 << (iVar - 6));
        for ( k = 0; k < nWords; k += 4*Step )
        {
            for ( i = 0; i < Step; i++ )
                pOut[i] = pIn[i];
            for ( i = 0; i < Step; i++ )
                pOut[Step+i] = pIn[2*Step+i];
            for ( i = 0; i < Step; i++ )
                pOut[2*Step+i] = pIn[Step+i];
            for ( i = 0; i < Step; i++ )
                pOut[3*Step+i] = pIn[3*Step+i];
            pIn  += 4*Step;
            pOut += 4*Step;
        }
    }
    else // if ( iVar == 5 )
    {
        for ( i = 0; i < nWords; i += 2 )
        {
            pOut[i]   = (pIn[i]   & 0x00000000FFFFFFFF) | ((pIn[i+1] & 0x00000000FFFFFFFF) << 32);
            pOut[i+1] = (pIn[i+1] & 0xFFFFFFFF00000000) | ((pIn[i]   & 0xFFFFFFFF00000000) >> 32);
        }
    }
}

// moves one var (v) to the given position (p)
void If_CluMoveVarOneUp( word * pF, int * Var2Pla, int * Pla2Var, int nVars, int v, int p )
{
    word pG[16], * pIn = pF, * pOut = pG, * pTemp;
    int iPlace0, iPlace1, Count = 0;
    assert( v >= 0 && v < nVars );
    assert( Var2Pla[v] >= p );
    while ( Var2Pla[v] > p )
    {
        iPlace0 = Var2Pla[v]-1;
        iPlace1 = Var2Pla[v];
        If_CluSwapAdjacent( pOut, pIn, iPlace0, nVars );
        pTemp = pIn; pIn = pOut, pOut = pTemp;
        Var2Pla[Pla2Var[iPlace0]]++;
        Var2Pla[Pla2Var[iPlace1]]--;
        Pla2Var[iPlace0] ^= Pla2Var[iPlace1];
        Pla2Var[iPlace1] ^= Pla2Var[iPlace0];
        Pla2Var[iPlace0] ^= Pla2Var[iPlace1];
        Count++;
    }
    if ( Count & 1 )
        If_CluCopy( pF, pIn, nVars );
    assert( Pla2Var[p] == v );
}

// moves one var (v) to the given position (p)
void If_CluMoveVarOneDown( word * pF, int * Var2Pla, int * Pla2Var, int nVars, int v, int p )
{
    word pG[16], * pIn = pF, * pOut = pG, * pTemp;
    int iPlace0, iPlace1, Count = 0;
    assert( v >= 0 && v < nVars );
    assert( Var2Pla[v] <= p );
    while ( Var2Pla[v] < p )
    {
        iPlace0 = Var2Pla[v];
        iPlace1 = Var2Pla[v]+1;
        If_CluSwapAdjacent( pOut, pIn, iPlace0, nVars );
        pTemp = pIn; pIn = pOut, pOut = pTemp;
        Var2Pla[Pla2Var[iPlace0]]++;
        Var2Pla[Pla2Var[iPlace1]]--;
        Pla2Var[iPlace0] ^= Pla2Var[iPlace1];
        Pla2Var[iPlace1] ^= Pla2Var[iPlace0];
        Pla2Var[iPlace0] ^= Pla2Var[iPlace1];
        Count++;
    }
    if ( Count & 1 )
        If_CluCopy( pF, pIn, nVars );
    assert( Pla2Var[p] == v );
}

// moves vars to be the most signiticant ones (Group[0] is MSB)
void If_CluMoveVars( word * pF, int * V2P, int * P2V, int nVars, int Group )
{
    int v;
    for ( v = 0; v < 4; v++ )
        If_CluMoveVarOneUp( pF, V2P, P2V, nVars, (Group >> (8*v)) & 0xFF, v );
}

// return the number of cofactors w.r.t. the topmost vars (nBSsize)
int If_CluCountCofs( word * pF, int * V2P, int * P2V, int nVars, int nBSsize )
{
    int nShift = (1 << (nVars - nBSsize));
    word Mask  = (((word)1) << nShift) - 1;
    word iCofs[16], iCof;
    int i, c, nMints = (1 << nBSsize), nCofs = 1;
    assert( nBSsize >= 3 && nBSsize <= 5 );
    assert( nVars - nBSsize >= 0 && nVars - nBSsize <= 6 );
    if ( nVars - nBSsize == 6 )
        Mask = ~0;
    iCofs[0] = pF[0] & Mask;
    for ( i = 1; i < nMints; i++ )
    {
        iCof = (pF[(i * nShift) / 64] >> ((i * nShift) & 63)) & Mask;
        for ( c = 0; c < nCofs; c++ )
            if ( iCof == iCofs[c] )
                break;
        if ( c == nCofs )
            iCofs[nCofs++] = iCof;
        if ( nCofs == 5 )
            break;
    }
    assert( nCofs >= 2 && nCofs <= 5 );
    return nCofs;
}

// finds a good var group (cof count < 6; vars are MSBs)
int If_CluFindGroup( word * pF, int * V2P, int * P2V, int nVars, int GroupEx )
{
/*
    int i, Excl[10];
    if ( GroupEx )
    {
        for ( i = 0; i < nVars; i++ )
            Excl[i] = 0;
        for ( i = 0; i < 4; i++ )
            Excl[(GroupEx >> (8*i)) & 0xFF] = 1;
    }
*/
    int nRounds = 3;
    int GroupBest, nCofsBest;
    int VarBest, nCofsBest2;
    int i, r, v, nCofs;
    assert( nVars > 4 );
    // start with the default group
    nCofsBest = If_CluCountCofs( pF, V2P, P2V, nVars, 4 );
    GroupBest = 0;
    for ( i = 0; i < 4; i++ )
        GroupBest |= ( P2V[i] << (8*i) );
    // try to find better group
    for ( r = 0; r < nRounds && nCofsBest > 2; r++ )
    {
        // find the best var to add
        VarBest = P2V[4];
        nCofsBest2 = If_CluCountCofs( pF, V2P, P2V, nVars, 5 );
        for ( v = 5; v < nVars; v++ )
        {
            If_CluMoveVarOneUp( pF, V2P, P2V, nVars, P2V[v], 4 );
            nCofs = If_CluCountCofs( pF, V2P, P2V, nVars, 5 );
            if ( nCofsBest2 > nCofs )
            {
                nCofsBest2 = nCofs;
                VarBest = P2V[4];
            }
        }
        // go back
        If_CluMoveVarOneUp( pF, V2P, P2V, nVars, VarBest, 4 );

        // find the best var to remove
        VarBest = P2V[4];
        nCofsBest2 = If_CluCountCofs( pF, V2P, P2V, nVars, 4 );
        for ( v = 3; v >= 0; v-- )
        {
            If_CluMoveVarOneDown( pF, V2P, P2V, nVars, v, 4 );
            nCofs = If_CluCountCofs( pF, V2P, P2V, nVars, 4 );
            if ( nCofsBest2 > nCofs )
            {
                nCofsBest2 = nCofs;
                VarBest = P2V[4];
            }
        }
        // go back
        If_CluMoveVarOneDown( pF, V2P, P2V, nVars, VarBest, 4 );

        // update best bound set
        nCofs = If_CluCountCofs( pF, V2P, P2V, nVars, 4 );
        assert( nCofs == nCofsBest2 );
        if ( nCofsBest > nCofs )
        {
            nCofsBest = nCofs;
            for ( i = 0; i < 4; i++ )
                GroupBest |= ( P2V[i] << (8*i) );
        }
    }
    if ( nCofsBest <= 4 )
        return GroupBest;
    assert( r == nRounds );
    return 0;
}

static inline int If_CluSuppIsMinBase( int Supp )
{
    return (Supp & (Supp+1)) == 0;
}
static inline int If_CluHasVar( word * t, int nVars, int iVar )
{
    int nWords = If_CluWordNum( nVars );
    assert( iVar < nVars );
    if ( iVar < 6 )
    {
        int i, Shift = (1 << iVar);
        for ( i = 0; i < nWords; i++ )
            if ( (t[i] & ~Truth6[iVar]) != ((t[i] & Truth6[iVar]) >> Shift) )
                return 1;
        return 0;
    }
    else
    {
        int i, k, Step = (1 << (iVar - 6));
        for ( k = 0; k < nWords; k += 2*Step )
        {
            for ( i = 0; i < Step; i++ )
                if ( t[i] != t[Step+i] )
                    return 1;
            t += 2*Step;
        }
        return 0;
    }
}
static inline int If_CluSupport( word * t, int nVars )
{
    int v, Supp = 0;
    for ( v = 0; v < nVars; v++ )
        if ( If_CluHasVar( t, nVars, v ) )
            Supp |= (1 << v);
    return Supp;
}



// returns the number of nodes and conf bits in vConf
int If_CluCheck( word * pTruth, int nVars, Vec_Int_t * vConf )
{
    int fDerive = 0;
    int V2P[10], P2V[10];
    int i, nSupp, nNodes, Group1, Group2, nCofs1, nCofs2;
    word pF[16];
    assert( nVars <= 10 );
    if ( nVars <= 5 )
        return 1;

    // check minnimum base
    If_CluCopy( pF, pTruth, nVars );
    nSupp = If_CluSupport( pF, nVars );
    if ( !nSupp || !If_CluSuppIsMinBase(nSupp) )
        return 0;

    // perform testing
    for ( i = 0; i < nVars; i++ )
        V2P[i] = P2V[i] = i;
    Group1 = If_CluFindGroup( pF, V2P, P2V, nVars, 0 );
    if ( Group1 == 0 )
        return 0;
    nCofs1 = If_CluCountCofs( pF, V2P, P2V, nVars, 4 );
    assert( nCofs1 >= 2 && nCofs1 <= 4 );
    if ( nVars <= 6 )
        return 1;
    if ( nCofs1 == 2 && nVars == 7 )
        return 1;
    if ( nCofs1 > 2 && nVars == 10 )
        return 0;

    // perform testing
    Group2 = If_CluFindGroup( pF, V2P, P2V, nVars, Group1 );
    if ( Group2 == 0 )
        return 0;
    nCofs2 = If_CluCountCofs( pF, V2P, P2V, nVars, 4 );
    assert( nCofs2 >= 2 && nCofs2 <= 4 );
    if ( nVars - 6 + (nCofs1 > 2) + (nCofs2 > 2) <= 4 )
        return 1;
    return 0;

    // compute conf bits

    return nNodes;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

