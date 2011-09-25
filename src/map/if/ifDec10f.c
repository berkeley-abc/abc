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

#define CLU_MAX 16

// decomposition
typedef struct If_Bst_t_ If_Bst_t;
struct If_Bst_t_
{
    int   nMyu;
    int   nVars;
    int   Vars[CLU_MAX];
    float Dels[CLU_MAX];
    word  Truth[1 << (CLU_MAX-6)];
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
static word TruthAll[CLU_MAX][1 << (CLU_MAX-6)];

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
    assert( CLU_MAX <= 16 );
    for ( i = 0; i < 6; i++ )
        for ( k = 0; k < (1 << (CLU_MAX-6)); k++ )
            TruthAll[i][k] = Truth6[i];
    for ( i = 6; i < CLU_MAX; i++ )
        for ( k = 0; k < (1 << (CLU_MAX-6)); k++ )
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
    word pG[1 << (CLU_MAX-6)], * pIn = pF, * pOut = pG, * pTemp;
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
void If_CluMoveGroupToMsb( word * pF, int nVars, int * V2P, int * P2V, word Group )
{
    char * pVars = (char *)&Group;
    int v;
    for ( v = 0; v < pVars[7]; v++ )
        If_CluMoveVar( pF, nVars, V2P, P2V, pVars[pVars[7] - 1 - v], nVars - 1 - v );
}

// return the number of cofactors w.r.t. the topmost vars (nBSsize)
int If_CluCountCofs( word * pF, int nVars, int nBSsize, int iShift )
{
    int nShift = (1 << (nVars - nBSsize));
    word Mask  = (((word)1) << nShift) - 1;
    word iCofs[64], iCof;
    int i, c, nMints = (1 << nBSsize), nCofs = 1;
    assert( nBSsize >= 3 && nBSsize <= 6 );
    assert( nVars - nBSsize > 0 && nVars - nBSsize <= 6 );
    if ( nVars - nBSsize == 6 )
        Mask = ~0;
    iCofs[0] = (pF[iShift / 64] >> (iShift & 63)) & Mask;
    for ( i = 1; i < nMints; i++ )
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

// check non-disjoint decomposition
int If_CluCheckNonDisjoint( word * pF, int nVars, int * V2P, int * P2V, int nBSsize, char * pGroup )
{
    int v, i, nCofsBest2;
    if ( (pGroup[6] == 3 || pGroup[6] == 4) )
    {
        word pCof0[1 << (CLU_MAX-6)];
        word pCof1[1 << (CLU_MAX-6)];
        // try cofactoring w.r.t. each variable
        for ( v = 0; v < pGroup[7]; v++ )
        {
            If_CluCofactors( pF, nVars, pGroup[v], pCof0, pCof1 );
            nCofsBest2 = If_CluCountCofs( pCof0, nVars, nBSsize, 0 );
            if ( nCofsBest2 > 2 )
                continue;
            nCofsBest2 = If_CluCountCofs( pCof1, nVars, nBSsize, 0 );
            if ( nCofsBest2 > 2 )
                continue;
            // find a good variable - move to the end
            If_CluMoveVar( pF, nVars, V2P, P2V, pGroup[v], nVars-1 );
            for ( i = 0; i < nBSsize; i++ )
                pGroup[i] = P2V[nVars-nBSsize+i];
            return 1;
        }
    }
    return 0;
}

void If_CluPrintGroup( word Group )
{
    char * pGroup = (char *)&Group;
    int i;
    for ( i = 0; i < pGroup[7]; i++ )
        printf( "%d ", pGroup[i] );
    printf( "\n" );
    printf( "Cofs = %d", pGroup[6] );
    printf( "\n" );
    printf( "Vars = %d", pGroup[7] );
    printf( "\n" );
}


// finds a good var group (cof count < 6; vars are MSBs)
word If_CluFindGroup( word * pF, int nVars, int iVarStart, int * V2P, int * P2V, int nBSsize, int fDisjoint )
{
    int nRounds = 3;
    word GroupBest = 0;
    char * pGroupBest = (char *)&GroupBest;
    int i, r, v, nCofs, VarBest, nCofsBest2;
    assert( nVars >= nBSsize + iVarStart && nVars <= CLU_MAX );
    assert( nBSsize >= 3 && nBSsize <= 6 );
    // start with the default group
    pGroupBest[7] = nBSsize;
    pGroupBest[6] = If_CluCountCofs( pF, nVars, nBSsize, 0 );
    for ( i = 0; i < nBSsize; i++ )
        pGroupBest[i] = P2V[nVars-nBSsize+i];
    // check if good enough
    if ( pGroupBest[6] == 2 )
        return GroupBest;
    if ( If_CluCheckNonDisjoint( pF, nVars, V2P, P2V, nBSsize, pGroupBest ) )
        return GroupBest;

    printf( "Iter %d  ", -1 );
    If_CluPrintGroup( GroupBest );

    // try to find better group
    for ( r = 0; r < nRounds; r++ )
    {
        // find the best var to add
        VarBest = P2V[nVars-1-nBSsize];
        nCofsBest2 = If_CluCountCofs( pF, nVars, nBSsize+1, 0 );
        for ( v = nVars-2-nBSsize; v >= iVarStart; v-- )
        {
            If_CluMoveVar( pF, nVars, V2P, P2V, P2V[v], nVars-1-nBSsize );
            nCofs = If_CluCountCofs( pF, nVars, nBSsize+1, 0 );
            if ( nCofsBest2 > nCofs )
            {
                nCofsBest2 = nCofs;
                VarBest = P2V[nVars-1-nBSsize];
            }
        }
        // go back
        If_CluMoveVar( pF, nVars, V2P, P2V, VarBest, nVars-1-nBSsize );

        // find the best var to remove
        VarBest = P2V[nVars-1-nBSsize];
        nCofsBest2 = If_CluCountCofs( pF, nVars, nBSsize, 0 );
        for ( v = nVars-nBSsize; v < nVars; v++ )
        {
            If_CluMoveVar( pF, nVars, V2P, P2V, v, nVars-1-nBSsize );
            nCofs = If_CluCountCofs( pF, nVars, nBSsize, 0 );
            if ( nCofsBest2 > nCofs )
            {
                nCofsBest2 = nCofs;
                VarBest = P2V[nVars-1-nBSsize];
            }
        }
        // go back
        If_CluMoveVar( pF, nVars, V2P, P2V, VarBest, nVars-1-nBSsize );

        // update best bound set
        nCofs = If_CluCountCofs( pF, nVars, nBSsize, 0 );
        assert( nCofs == nCofsBest2 );
        if ( pGroupBest[6] > nCofs )
        {
            pGroupBest[7] = nBSsize;
            pGroupBest[6] = nCofs;
            for ( i = 0; i < nBSsize; i++ )
                pGroupBest[i] = P2V[nVars-nBSsize+i];
        }

        printf( "Iter %d  ", r );
        If_CluPrintGroup( GroupBest );

        // check if good enough
        if ( pGroupBest[6] == 2 )
            return GroupBest;
        if ( If_CluCheckNonDisjoint( pF, nVars, V2P, P2V, nBSsize, pGroupBest ) )
            return GroupBest;
    }
    assert( r == nRounds );
    return 0;
}


// double check that the given group has a decomposition
void If_CluCheckGroup( word * pTruth, int nVars, word Group )
{
    word pF[1 << (CLU_MAX-6)];
    int v, nCofs, V2P[CLU_MAX], P2V[CLU_MAX];
    char * pVars = (char *)&Group;
    assert( pVars[7] >= 3 && pVars[7] <= 6 ); // vars
    assert( pVars[6] >= 2 && pVars[6] <= 4 ); // cofs
    // create permutation
    for ( v = 0; v < nVars; v++ )
        V2P[v] = P2V[v] = v;
    // create truth table
    If_CluCopy( pF, pTruth, nVars );
    // move group up
    If_CluMoveGroupToMsb( pF, nVars, V2P, P2V, Group );
    // check the number of cofactors
    nCofs = If_CluCountCofs( pF, nVars, pVars[7], 0 );
    if ( nCofs != pVars[6] )
        printf( "Group check 0 has failed.\n" );
    // check compatible
    if ( nCofs > 2 )
    {
        nCofs = If_CluCountCofs( pF, nVars-1, pVars[7]-1, 0 );
        if ( nCofs > 2 )
            printf( "Group check 1 has failed.\n" );
        nCofs = If_CluCountCofs( pF, nVars-1, pVars[7]-1, (1 << (nVars-1)) );
        if ( nCofs > 2 )
            printf( "Group check 2 has failed.\n" );
    }
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
word If_CluCheck( word * pTruth, int nVars, int nLutLeaf, int nLutRoot )
{
    int V2P[CLU_MAX], P2V[CLU_MAX];
    word Group1, pF[1 << (CLU_MAX-6)];
    int i, nSupp;
    assert( nVars <= CLU_MAX );
    assert( nVars <= nLutLeaf + nLutRoot - 1 );

    // check minnimum base
    If_CluCopy( pF, pTruth, nVars );
    nSupp = If_CluSupport( pF, nVars );
    if ( !nSupp || !If_CluSuppIsMinBase(nSupp) )
        return 0;

    // perform testing
    for ( i = 0; i < nVars; i++ )
        V2P[i] = P2V[i] = i;
    Group1 = If_CluFindGroup( pF, nVars, 0, V2P, P2V, nLutLeaf, nLutLeaf + nLutRoot == nVars + 1 );
    if ( Group1 == 0 )
        return 0;

    // perform checking
    If_CluCheckGroup( pTruth, nVars, Group1 );

    // compute conf bits
    return Group1;
}


// computes delay of the decomposition
float If_CluDelayMax( word Group, float * pDelays )
{
    char * pVars = (char *)&Group;
    float Delay = 0.0;
    int i;
    for ( i = 0; i < pVars[7]; i++ )
        Delay = Abc_MaxFloat( Delay, pDelays[pVars[i]] );
    return Delay;
}

// returns delay of the decomposition;  sets area of the cut as its cost
float If_CutDelayLutStruct( If_Man_t * p, If_Cut_t * pCut, char * pStr, float WireDelay )
{
    float Delays[CLU_MAX+2];
    int fUsed[CLU_MAX+2] = {0};
    If_Obj_t * pLeaf;
    word Group1 = 0, Group2 = 0, Group3 = 0;
    char * pGroup1 = (char *)&Group1;
    char * pGroup2 = (char *)&Group2;
    char * pGroup3 = (char *)&Group3;
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
            pGroup1[i] = i;
        }
        pGroup1[7] = nLeaves;
        pCut->Cost = 1;
        return 1.0 + If_CluDelayMax( Group1, Delays );
    }

    // derive the first group
    Group1 = If_CluCheck( (word *)If_CutTruth(pCut), nLeaves, nLutLeaf, nLutRoot );
    if ( Group1 == 0 )
        return ABC_INFINITY;
    // compute the delay
    Delays[nLeaves] = If_CluDelayMax( Group1, Delays ) + (WireDelay == 0.0)?1.0:WireDelay;
    if ( Group2 )
        Delays[nLeaves+1] = If_CluDelayMax( Group2, Delays ) + (WireDelay == 0.0)?1.0:WireDelay;

    // mark used groups
    for ( i = 0; i < pGroup1[7]; i++ )
        fUsed[pGroup1[i]] = 1;
    for ( i = 0; i < pGroup2[7]; i++ )
        fUsed[pGroup2[i]] = 1;
    // mark unused groups
    assert( pGroup1[6] >= 2 && pGroup1[6] <= 4 );
    if ( pGroup1[6] > 2 )
        fUsed[pGroup1[0]] = 0;
    assert( pGroup2[6] >= 2 && pGroup2[6] <= 4 );
    if ( pGroup2[6] > 2 )
        fUsed[pGroup2[0]] = 0;

    // create remaining group
    assert( pGroup3[7] == 0 );
    for ( i = 0; i < nLeaves; i++ )
        if ( !fUsed[i] )
            pGroup3[pGroup3[7]++] = i;
    pGroup3[pGroup3[7]++] = nLeaves;
    if ( Group2 )
        pGroup3[pGroup3[7]++] = nLeaves+1;
    assert( pGroup1[7] + pGroup2[7] + pGroup3[7] == nLeaves + (pGroup1[7] > 0) + (pGroup2[7] > 0) + (pGroup1[6] > 2) + (pGroup2[6] > 2) );
    // what if both non-disjoint vars are the same???

    pCut->Cost = 2 + (pGroup2[7] > 0);
    return 1.0 + If_CluDelayMax( Group3, Delays );
}

// testing procedure
void If_CluTest()
{
//    word t = 0xff00f0f0ccccaaaa;
    word t = 0xfedcba9876543210;
    int nLeaves  = 6;
    int nLutLeaf = 4;
    int nLutRoot = 4;
    word Group1;
    char * pVars = (char *)&Group1;
//    return;

    Group1 = If_CluCheck( &t, nLeaves, nLutLeaf, nLutRoot );

    If_CluPrintGroup( Group1 );
}




////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

