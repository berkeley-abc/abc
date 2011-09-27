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

#define CLU_VAR_MAX  16
#define CLU_WRD_MAX  (1 << ((CLU_VAR_MAX)-6))

// decomposition
typedef struct If_Grp_t_ If_Grp_t;
struct If_Grp_t_
{
    char nVars;
    char nMyu;
    char pVars[6];
};

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
static word TruthAll[CLU_VAR_MAX][CLU_WRD_MAX];

extern void Kit_DsdPrintFromTruth( unsigned * pTruth, int nVars );
extern void Extra_PrintBinary( FILE * pFile, unsigned Sign[], int nBits );

//  group representation (MSB <-> LSB)
//  nVars | nMyu | v5 | v4 | v3 | v2 | v1 | v0 
//  if nCofs > 2, v0 is the shared variable

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

void If_CluInitTruthTables()
{
    int i, k;
    assert( CLU_VAR_MAX <= 16 );
    for ( i = 0; i < 6; i++ )
        for ( k = 0; k < CLU_WRD_MAX; k++ )
            TruthAll[i][k] = Truth6[i];
    for ( i = 6; i < CLU_VAR_MAX; i++ )
        for ( k = 0; k < CLU_WRD_MAX; k++ )
            TruthAll[i][k] = ((k >> i) & 1) ? ~0 : 0;
}

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
static inline int If_CluEqual( word * pOut, word * pIn, int nVars )
{
    int w, nWords = If_CluWordNum( nVars );
    for ( w = 0; w < nWords; w++ )
        if ( pOut[w] != pIn[w] )
            return 0;
    return 1;
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
void If_CluMoveVar( word * pF, int nVars, int * Var2Pla, int * Pla2Var, int v, int p )
{
    word pG[CLU_WRD_MAX], * pIn = pF, * pOut = pG, * pTemp;
    int iPlace0, iPlace1, Count = 0;
    assert( v >= 0 && v < nVars );
    if ( Var2Pla[v] <= p )
    {
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
    }
    else
    {
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
    }
    if ( Count & 1 )
        If_CluCopy( pF, pIn, nVars );
    assert( Pla2Var[p] == v );
}

// moves vars to be the most signiticant ones (Group[0] is MSB)
void If_CluMoveGroupToMsb( word * pF, int nVars, int * V2P, int * P2V, If_Grp_t * g )
{
    int v;
    for ( v = 0; v < g->nVars; v++ )
        If_CluMoveVar( pF, nVars, V2P, P2V, g->pVars[g->nVars - 1 - v], nVars - 1 - v );
}

// return the number of cofactors w.r.t. the topmost vars (nBSsize)
int If_CluCountCofs( word * pF, int nVars, int nBSsize, int iShift, word * pCofs[2] )
{
    word iCofs[64], iCof;
    int i, c, w, nMints = (1 << nBSsize), nCofs;

    assert( nBSsize < nVars );
    assert( nBSsize >= 3 && nBSsize <= 6 );

    if ( nVars - nBSsize >= 6 )
    {
        word * pCofA, * pCofB;
        int nWords = (1 << (nVars - nBSsize - 6));
        assert( nWords * nMints == If_CluWordNum(nVars) );
        for ( nCofs = i = 0; i < nMints; i++ )
        {
            for ( c = 0; c < nCofs; c++ )
            {
                pCofA = pF + i * nWords;
                pCofB = pF + iCofs[c] * nWords;
                for ( w = 0; w < nWords; w++ )
                    if ( pCofA[w] != pCofB[w] )
                        break;
                if ( w == nWords )
                    break;
            }
            if ( c == nCofs )
                iCofs[nCofs++] = i;
            if ( nCofs == 5 )
                break;
        }
        if ( nCofs == 2 && pCofs )
        {
            for ( c = 0; c < nCofs; c++ )
            {
                word * pCofA = pF + iCofs[c] * nWords;
                for ( w = 0; w < nWords; w++ )
                    pCofs[c][w] = pCofA[w];
            }
        }
    }
    else
    {
        int nShift = (1 << (nVars - nBSsize));
        word Mask  = ((((word)1) << nShift) - 1);
        for ( nCofs = i = 0; i < nMints; i++ )
        {
            iCof = (pF[(iShift + i * nShift) / 64] >> ((iShift + i * nShift) & 63)) & Mask;
            for ( c = 0; c < nCofs; c++ )
                if ( iCof == iCofs[c] )
                    break;
            if ( c == nCofs )
                iCofs[nCofs++] = iCof;
            if ( nCofs == 5 )
                break;
        }
    }
    assert( nCofs >= 2 && nCofs <= 5 );
    return nCofs;
}

void If_CluCofactors( word * pF, int nVars, int iVar, word * pCof0, word * pCof1 )
{
    int nWords = If_CluWordNum( nVars );
    assert( iVar < nVars );
    if ( iVar < 6 )
    {
        int i, Shift = (1 << iVar);
        for ( i = 0; i < nWords; i++ )
        {
            pCof0[i] = (pF[i] & ~Truth6[iVar]) | ((pF[i] & ~Truth6[iVar]) << Shift);
            pCof1[i] = (pF[i] &  Truth6[iVar]) | ((pF[i] &  Truth6[iVar]) >> Shift);
        }
        return;
    }
    else
    {
        int i, k, Step = (1 << (iVar - 6));
        for ( k = 0; k < nWords; k += 2*Step )
        {
            for ( i = 0; i < Step; i++ )
            {
                pCof0[i] = pCof0[Step+i] = pF[i];
                pCof1[i] = pCof1[Step+i] = pF[Step+i];
            }
            pF    += 2*Step;
            pCof0 += 2*Step;
            pCof1 += 2*Step;
        }
        return;
    }
}

// derives non-disjoint decomposition (assumes the shared var in pG->pVars[pG->nVars-1]
word If_CluDeriveNonDisjoint( word * pF, int nVars, int * V2P, int * P2V, If_Grp_t * g, If_Grp_t * pG )
{
    /*
    word Truth, Truth0, Truth1;
    word Cof[2][CLU_WRD_MAX], Cof0[2][CLU_WRD_MAX], Cof1[2][CLU_WRD_MAX];
    int i, nFSvars, nFSHalfBits, nBSHalfBits;
    assert( pG->nVars >= 3 && pG->nVar <= 6 );
    assert( pG->nMyu == 3 || pG->nMyu == 4 );

    If_CluMoveGroupToMsb( pF, nVars, V2P, P2V, pG );

    If_CluCofactors( pF, nVars, nVars - 1, Cof[0], Cof[1] );

    assert( 2 >= If_Dec6CofCount2(c0) );
    assert( 2 >= If_Dec6CofCount2(c1) );

    assert( 2 >= If_CluCountCofs( Cof[0], nVars - 1, pG->nVars - 1, 0 ) );
    assert( 2 >= If_CluCountCofs( Cof[1], nVars - 1, pG->nVars - 1, 0 ) );

    Truth0 = If_CluExtract2Cofs( Cof[0], nVars - 1, pG->nVars - 1, &Cof0[0], &Cof0[1] );
    Truth1 = If_CluExtract2Cofs( Cof[1], nVars - 1, pG->nVars - 1, &Cof0[0], &Cof0[1] );

    nFSHalfBits = (1 << (nVars - pG->nVars - 1));
    nBSHalfBits = (1 << (pG->nVars - 1))

    Truth = ((Truth0 && ((1 << nBSHalfBits) - 1)) << nBSHalfBits) | (Truth0 && ((1 << nBSHalfBits) - 1))


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
    */
    return 0;
}


// check non-disjoint decomposition
int If_CluCheckNonDisjoint( word * pF, int nVars, int * V2P, int * P2V, If_Grp_t * g )
{
    int v, i, nCofsBest2;
    if ( (g->nMyu == 3 || g->nMyu == 4) )
    {
        word pCof0[CLU_WRD_MAX];
        word pCof1[CLU_WRD_MAX];
        // try cofactoring w.r.t. each variable
        for ( v = 0; v < g->nVars; v++ )
        {
            If_CluCofactors( pF, nVars, V2P[g->pVars[v]], pCof0, pCof1 );
            nCofsBest2 = If_CluCountCofs( pCof0, nVars, g->nVars, 0, NULL );
            if ( nCofsBest2 > 2 )
                continue;
            nCofsBest2 = If_CluCountCofs( pCof1, nVars, g->nVars, 0, NULL );
            if ( nCofsBest2 > 2 )
                continue;
            // found good shared variable - move to the end
            If_CluMoveVar( pF, nVars, V2P, P2V, g->pVars[v], nVars-1 );
            for ( i = 0; i < g->nVars; i++ )
                g->pVars[i] = P2V[nVars-g->nVars+i];
            return 1;
        }
    }
    return 0;
}

void If_CluPrintGroup( If_Grp_t * g )
{
    int i;
    for ( i = 0; i < g->nVars; i++ )
        printf( "%d ", g->pVars[i] );
    printf( "\n" );
    printf( "Cofs = %d", g->nMyu );
    printf( "\n" );
    printf( "Vars = %d", g->nVars );
    printf( "\n" );
}


// finds a good var group (cof count < 6; vars are MSBs)
If_Grp_t If_CluFindGroup( word * pF, int nVars, int iVarStart, int * V2P, int * P2V, int nBSsize, int fDisjoint )
{
    If_Grp_t G = {0}, * g = &G;
    int i, r, v, nCofs, VarBest, nCofsBest2;
    assert( nVars >= nBSsize + iVarStart && nVars <= CLU_VAR_MAX );
    assert( nBSsize >= 3 && nBSsize <= 6 );
    // start with the default group
    g->nVars = nBSsize;
    g->nMyu = If_CluCountCofs( pF, nVars, nBSsize, 0, NULL );
    for ( i = 0; i < nBSsize; i++ )
        g->pVars[i] = P2V[nVars-nBSsize+i];
    // check if good enough
    if ( g->nMyu == 2 )
        return G;
    if ( If_CluCheckNonDisjoint( pF, nVars, V2P, P2V, g ) )
        return G;

    printf( "Iter %d  ", -1 );
    If_CluPrintGroup( g );

    // try to find better group
    for ( r = 0; r < nBSsize; r++ )
    {
        // find the best var to add
        VarBest = P2V[nVars-1-nBSsize];
        nCofsBest2 = If_CluCountCofs( pF, nVars, nBSsize+1, 0, NULL );
        for ( v = nVars-2-nBSsize; v >= iVarStart; v-- )
        {
            If_CluMoveVar( pF, nVars, V2P, P2V, P2V[v], nVars-1-nBSsize );
            nCofs = If_CluCountCofs( pF, nVars, nBSsize+1, 0, NULL );
            if ( nCofsBest2 >= nCofs )
            {
                nCofsBest2 = nCofs;
                VarBest = P2V[nVars-1-nBSsize];
            }
        }
        // go back
        If_CluMoveVar( pF, nVars, V2P, P2V, VarBest, nVars-1-nBSsize );
        // update best bound set
        nCofs = If_CluCountCofs( pF, nVars, nBSsize+1, 0, NULL );
        assert( nCofs == nCofsBest2 );

        // find the best var to remove
        VarBest = P2V[nVars-1-nBSsize];
        nCofsBest2 = If_CluCountCofs( pF, nVars, nBSsize, 0, NULL );
        for ( v = nVars-nBSsize; v < nVars; v++ )
        {
            If_CluMoveVar( pF, nVars, V2P, P2V, P2V[v], nVars-1-nBSsize );
            nCofs = If_CluCountCofs( pF, nVars, nBSsize, 0, NULL );
            if ( nCofsBest2 >= nCofs )
            {
                nCofsBest2 = nCofs;
                VarBest = P2V[nVars-1-nBSsize];
            }
        }

        // go back
        If_CluMoveVar( pF, nVars, V2P, P2V, VarBest, nVars-1-nBSsize );
        // update best bound set
        nCofs = If_CluCountCofs( pF, nVars, nBSsize, 0, NULL );
        assert( nCofs == nCofsBest2 );
        if ( g->nMyu >= nCofs )
        {
            g->nVars = nBSsize;
            g->nMyu = nCofs;
            for ( i = 0; i < nBSsize; i++ )
                g->pVars[i] = P2V[nVars-nBSsize+i];
        }

        printf( "Iter %d  ", r );
        If_CluPrintGroup( g );

        // check if good enough
        if ( g->nMyu == 2 )
            return G;
        if ( If_CluCheckNonDisjoint( pF, nVars, V2P, P2V, g ) )
            return G;
    }
    assert( r == nBSsize );
    g->nVars = 0;
    return G;
}


// double check that the given group has a decomposition
void If_CluCheckGroup( word * pTruth, int nVars, If_Grp_t * g )
{
    word pF[CLU_WRD_MAX];
    int v, nCofs, V2P[CLU_VAR_MAX], P2V[CLU_VAR_MAX];
    assert( g->nVars >= 3 && g->nVars <= 6 ); // vars
    assert( g->nMyu >= 2 && g->nMyu <= 4 ); // cofs
    // create permutation
    for ( v = 0; v < nVars; v++ )
        V2P[v] = P2V[v] = v;
    // create truth table
    If_CluCopy( pF, pTruth, nVars );
    // move group up
    If_CluMoveGroupToMsb( pF, nVars, V2P, P2V, g );
    // check the number of cofactors
    nCofs = If_CluCountCofs( pF, nVars, g->nVars, 0, NULL );
    if ( nCofs != g->nMyu )
        printf( "Group check 0 has failed.\n" );
    // check compatible
    if ( nCofs > 2 )
    {
        nCofs = If_CluCountCofs( pF, nVars-1, g->nVars-1, 0, NULL );
        if ( nCofs > 2 )
            printf( "Group check 1 has failed.\n" );
        nCofs = If_CluCountCofs( pF, nVars-1, g->nVars-1, (1 << (nVars-1)), NULL );
        if ( nCofs > 2 )
            printf( "Group check 2 has failed.\n" );
    }
}


// double check that the permutation derived is correct
void If_CluCheckPerm( word * pTruth, word * pF, int nVars, int * V2P, int * P2V )
{
    int i;
    for ( i = 0; i < nVars; i++ )
        If_CluMoveVar( pF, nVars, V2P, P2V, i, i );

    if ( If_CluEqual( pTruth, pF, nVars ) )
        printf( "Permutation successful\n" );
    else
        printf( "Permutation FAILED.\n" );
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

// returns the best group found
If_Grp_t If_CluCheck( word * pTruth, int nVars, int nLutLeaf, int nLutRoot )
{
    int V2P[CLU_VAR_MAX], P2V[CLU_VAR_MAX];
    word pF[CLU_WRD_MAX];
    If_Grp_t G1 = {0};
    int i, nSupp;
    assert( nVars <= CLU_VAR_MAX );
    assert( nVars <= nLutLeaf + nLutRoot - 1 );

    // check minnimum base
    If_CluCopy( pF, pTruth, nVars );
    nSupp = If_CluSupport( pF, nVars );
    if ( !nSupp || !If_CluSuppIsMinBase(nSupp) )
        return G1;

    // perform testing
    for ( i = 0; i < nVars; i++ )
        V2P[i] = P2V[i] = i;
    G1 = If_CluFindGroup( pF, nVars, 0, V2P, P2V, nLutLeaf, nLutLeaf + nLutRoot == nVars + 1 );

    // check permutation
    If_CluCheckPerm( pTruth, pF, nVars, V2P, P2V );

    if ( G1.nVars == 0 )
        return G1;

    // perform checking
    If_CluCheckGroup( pTruth, nVars, &G1 );
    return G1;
}


// computes delay of the decomposition
float If_CluDelayMax( If_Grp_t * g, float * pDelays )
{
    float Delay = 0.0;
    int i;
    for ( i = 0; i < g->nVars; i++ )
        Delay = Abc_MaxFloat( Delay, pDelays[g->pVars[i]] );
    return Delay;
}

// returns delay of the decomposition;  sets area of the cut as its cost
float If_CutDelayLutStruct( If_Man_t * p, If_Cut_t * pCut, char * pStr, float WireDelay )
{
    float Delays[CLU_VAR_MAX+2];
    int fUsed[CLU_VAR_MAX+2] = {0};
    If_Obj_t * pLeaf;
    If_Grp_t G1 = {0}, G2 = {0}, G3 = {0};
    int nLeaves = If_CutLeaveNum(pCut);
    int i, nLutLeaf, nLutRoot;
    // mark the cut as user cut
    pCut->fUser = 1;
    // quit if parameters are wrong
    if ( strlen(pStr) != 2 )
    {
        printf( "Wrong LUT struct (%s)\n", pStr );
        return ABC_INFINITY;
    }
    nLutLeaf = pStr[0] - '0';
    if ( nLutLeaf < 3 || nLutLeaf > 6 )
    {
        printf( "Leaf size (%d) should belong to {3,4,5,6}.\n", nLutLeaf );
        return ABC_INFINITY;
    }
    nLutRoot = pStr[1] - '0';
    if ( nLutRoot < 3 || nLutRoot > 6 )
    {
        printf( "Leaf size (%d) should belong to {3,4,5,6}.\n", nLutRoot );
        return ABC_INFINITY;
    }
    if ( nLeaves > nLutLeaf + nLutRoot - 1 )
    {
        printf( "The cut size (%d) is too large for the LUT structure %d%d.\n", If_CutLeaveNum(pCut), nLutLeaf, nLutRoot );
        return ABC_INFINITY;
    }

    // remember the delays
    If_CutForEachLeaf( p, pCut, pLeaf, i )
        Delays[nLeaves-1-i] = If_ObjCutBest(pLeaf)->Delay;

    // consider easy case
    if ( nLeaves <= Abc_MaxInt( nLutLeaf, nLutRoot ) )
    {
        assert( nLeaves <= 6 );
        for ( i = 0; i < nLeaves; i++ )
        {
            pCut->pPerm[i] = 1;
            G1.pVars[i] = i;
        }
        G1.nVars = nLeaves;
        pCut->Cost = 1;
        return 1.0 + If_CluDelayMax( &G1, Delays );
    }

    // derive the first group
    G1 = If_CluCheck( (word *)If_CutTruth(pCut), nLeaves, nLutLeaf, nLutRoot );
    if ( G1.nVars == 0 )
        return ABC_INFINITY;
    // compute the delay
    Delays[nLeaves] = If_CluDelayMax( &G1, Delays ) + (WireDelay == 0.0)?1.0:WireDelay;
    if ( G2.nVars )
        Delays[nLeaves+1] = If_CluDelayMax( &G2, Delays ) + (WireDelay == 0.0)?1.0:WireDelay;

    // mark used groups
    for ( i = 0; i < G1.nVars; i++ )
        fUsed[G1.pVars[i]] = 1;
    for ( i = 0; i < G2.nVars; i++ )
        fUsed[G2.pVars[i]] = 1;
    // mark unused groups
    assert( G1.nMyu >= 2 && G1.nMyu <= 4 );
    if ( G1.nMyu > 2 )
        fUsed[G1.pVars[G1.nVars-1]] = 0;
    assert( G2.nMyu >= 2 && G2.nMyu <= 4 );
    if ( G2.nMyu > 2 )
        fUsed[G2.pVars[G2.nVars-1]] = 0;

    // create remaining group
    assert( G3.nVars == 0 );
    for ( i = 0; i < nLeaves; i++ )
        if ( !fUsed[i] )
            G3.pVars[G3.nVars++] = i;
    G3.pVars[G3.nVars++] = nLeaves;
    if ( G2.nVars )
        G3.pVars[G3.nVars++] = nLeaves+1;
    assert( G1.nVars + G2.nVars + G3.nVars == nLeaves + 
        (G1.nVars > 0) + (G2.nVars > 0) + (G1.nMyu > 2) + (G2.nMyu > 2) );
    // what if both non-disjoint vars are the same???

    pCut->Cost = 2 + (G2.nVars > 0);
    return 1.0 + If_CluDelayMax( &G3, Delays );
}

// testing procedure
void If_CluTest()
{
//    word t = 0xff00f0f0ccccaaaa;
    word t = 0xfedcba9876543210;
    int nLeaves  = 6;
    int nLutLeaf = 4;
    int nLutRoot = 4;
    If_Grp_t G;

    G = If_CluCheck( &t, nLeaves, nLutLeaf, nLutRoot );

    If_CluPrintGroup( &G );
}




////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

