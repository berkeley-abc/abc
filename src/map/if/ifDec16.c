/**CFile****************************************************************

  FileName    [ifDec16.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [Fast checking procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: ifDec16.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "if.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define CLU_VAR_MAX  16
#define CLU_WRD_MAX  (1 << ((CLU_VAR_MAX)-6))
#define CLU_UNUSED   99

// decomposition
typedef struct If_Grp_t_ If_Grp_t;
struct If_Grp_t_
{
    char       nVars;
    char       nMyu;
    char       pVars[CLU_VAR_MAX];
};

// hash table entry
typedef struct If_Hte_t_ If_Hte_t;
struct If_Hte_t_
{
    If_Hte_t * pNext;
    If_Grp_t   Group;
    word       pTruth[1];
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
static word TruthAll[CLU_VAR_MAX][CLU_WRD_MAX] = {{0}};

extern void Kit_DsdPrintFromTruth( unsigned * pTruth, int nVars );
extern void Extra_PrintBinary( FILE * pFile, unsigned Sign[], int nBits );


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

// hash table
static inline int If_CluWordNum( int nVars )
{
    return nVars <= 6 ? 1 : 1 << (nVars-6);
}
int If_CluHashKey( word * pTruth, int nWords, int Size )
{
    static unsigned BigPrimes[8] = {12582917, 25165843, 50331653, 100663319, 201326611, 402653189, 805306457, 1610612741};
    unsigned char * s = (unsigned char *)pTruth;
    unsigned Value = 0;
    int i;
    for ( i = 0; i < 8 * nWords; i++ )
        Value ^= BigPrimes[i % 7] * s[i];
    return Value % Size;
}
If_Grp_t * If_CluHashLookup( If_Man_t * p, word * pTruth )
{
    If_Hte_t * pEntry;
    int nWords, HashKey;
    if ( p == NULL )
        return NULL;
    nWords = If_CluWordNum(p->pPars->nLutSize);
    if ( p->pMemEntries == NULL )
    {
        p->pMemEntries = Mem_FixedStart( sizeof(If_Hte_t) + sizeof(word) * (If_CluWordNum(p->pPars->nLutSize) - 1) );
        p->nTableSize  = Vec_PtrSize(p->vObjs) * p->pPars->nCutsMax;
        p->pHashTable  = ABC_CALLOC( void *, p->nTableSize );
    }
    // check if this entry exists
    HashKey = If_CluHashKey( pTruth, nWords, p->nTableSize );
    for ( pEntry = ((If_Hte_t **)p->pHashTable)[HashKey]; pEntry; pEntry = pEntry->pNext )
        if ( memcmp(pEntry->pTruth, pTruth, sizeof(word) * nWords) == 0 )
            return &pEntry->Group;
    // create entry
    p->nTableEntries++;
    pEntry = (If_Hte_t *)Mem_FixedEntryFetch( p->pMemEntries );
    memcpy( pEntry->pTruth, pTruth, sizeof(word) * nWords );
    memset( &pEntry->Group, 0, sizeof(If_Grp_t) );
    pEntry->Group.nVars = CLU_UNUSED;
    pEntry->pNext = ((If_Hte_t **)p->pHashTable)[HashKey];
    ((If_Hte_t **)p->pHashTable)[HashKey] = pEntry;
    return &pEntry->Group;
}

// variable permutation for large functions
static inline void If_CluClear( word * pIn, int nVars )
{
    int w, nWords = If_CluWordNum( nVars );
    for ( w = 0; w < nWords; w++ )
        pIn[w] = 0;
}
static inline void If_CluFill( word * pIn, int nVars )
{
    int w, nWords = If_CluWordNum( nVars );
    for ( w = 0; w < nWords; w++ )
        pIn[w] = ~0;
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
static inline void If_CluAnd( word * pRes, word * pIn1, word * pIn2, int nVars )
{
    int w, nWords = If_CluWordNum( nVars );
    for ( w = 0; w < nWords; w++ )
        pRes[w] = pIn1[w] & pIn2[w];
}
static inline void If_CluSharp( word * pRes, word * pIn1, word * pIn2, int nVars )
{
    int w, nWords = If_CluWordNum( nVars );
    for ( w = 0; w < nWords; w++ )
        pRes[w] = pIn1[w] & ~pIn2[w];
}
static inline void If_CluOr( word * pRes, word * pIn1, word * pIn2, int nVars )
{
    int w, nWords = If_CluWordNum( nVars );
    for ( w = 0; w < nWords; w++ )
        pRes[w] = pIn1[w] | pIn2[w];
}
static inline word If_CluAdjust( word t, int nVars )
{
    assert( nVars >= 0 && nVars < 6 );
    t &= (1 << (1 << nVars)) - 1;
    if ( nVars == 0 )
        t |= t << (1<<nVars++);
    if ( nVars == 1 )
        t |= t << (1<<nVars++);
    if ( nVars == 2 )
        t |= t << (1<<nVars++);
    if ( nVars == 3 )
        t |= t << (1<<nVars++);
    if ( nVars == 4 )
        t |= t << (1<<nVars++);
    if ( nVars == 5 )
        t |= t << (1<<nVars++);
    return t;
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

void If_CluPrintGroup( If_Grp_t * g )
{
    int i;
    printf( "Vars = %d   ", g->nVars );
    printf( "Myu = %d   ", g->nMyu );
    for ( i = 0; i < g->nVars; i++ )
        printf( "%d ", g->pVars[i] );
    printf( "\n" );
}

void If_CluPrintConfig( int nVars, If_Grp_t * g, If_Grp_t * r, word BStruth, word * pFStruth )
{
    assert( r->nVars == nVars - g->nVars + 1 + (g->nMyu > 2) );
    If_CluPrintGroup( g );
    if ( g->nVars < 6 )
        BStruth = If_CluAdjust( BStruth, g->nVars );
    Kit_DsdPrintFromTruth( (unsigned *)&BStruth, g->nVars );
    printf( "\n" );
    If_CluPrintGroup( r );
    if ( r->nVars < 6 )
        pFStruth[0] = If_CluAdjust( pFStruth[0], r->nVars );
    Kit_DsdPrintFromTruth( (unsigned *)pFStruth, r->nVars );
    printf( "\n" );
}


void If_CluInitTruthTables()
{
    int i, k;
    assert( CLU_VAR_MAX <= 16 );
    for ( i = 0; i < 6; i++ )
        for ( k = 0; k < CLU_WRD_MAX; k++ )
            TruthAll[i][k] = Truth6[i];
    for ( i = 6; i < CLU_VAR_MAX; i++ )
        for ( k = 0; k < CLU_WRD_MAX; k++ )
            TruthAll[i][k] = ((k >> (i-6)) & 1) ? ~0 : 0;

//    Extra_PrintHex( stdout, TruthAll[6], 8 ); printf( "\n" );
//    Extra_PrintHex( stdout, TruthAll[7], 8 ); printf( "\n" );
}


// verification
static void If_CluComposeLut( int nVars, If_Grp_t * g, word * t, word f[6][CLU_WRD_MAX], word * r )
{
    word c[CLU_WRD_MAX];
    int m, v;
    If_CluClear( r, nVars ); 
    for ( m = 0; m < (1<<g->nVars); m++ )
    {
        if ( !((t[m >> 6] >> (m & 63)) & 1) )
            continue;
        If_CluFill( c, nVars );
        for ( v = 0; v < g->nVars; v++ )
            if ( (m >> v) & 1 )
                If_CluAnd( c, c, f[v], nVars );
            else
                If_CluSharp( c, c, f[v], nVars );
        If_CluOr( r, r, c, nVars );
    }
}
void If_CluVerify( word * pF, int nVars, If_Grp_t * g, If_Grp_t * r, word BStruth, word * pFStruth )
{
    word pTTFans[6][CLU_WRD_MAX], pTTWire[CLU_WRD_MAX], pTTRes[CLU_WRD_MAX];
    int i;
    assert( g->nVars <= 6 && r->nVars <= 6 );

    if ( TruthAll[0][0] == 0 )
        If_CluInitTruthTables();

    for ( i = 0; i < g->nVars; i++ )
        If_CluCopy( pTTFans[i], TruthAll[g->pVars[i]], nVars );
    If_CluComposeLut( nVars, g, &BStruth, pTTFans, pTTWire );

    for ( i = 0; i < r->nVars; i++ )
        if ( r->pVars[i] == nVars )
            If_CluCopy( pTTFans[i], pTTWire, nVars );
        else
            If_CluCopy( pTTFans[i], TruthAll[r->pVars[i]], nVars );
    If_CluComposeLut( nVars, r, pFStruth, pTTFans, pTTRes );

    if ( !If_CluEqual(pTTRes, pF, nVars) )
    {
        printf( "\n" );
        If_CluPrintConfig( nVars, g, r, BStruth, pFStruth );
        Kit_DsdPrintFromTruth( (unsigned*)pTTRes, nVars ); printf( "\n" );
        Kit_DsdPrintFromTruth( (unsigned*)pF, nVars ); printf( "\n" );
//        Extra_PrintHex( stdout, (unsigned *)pF, nVars ); printf( "\n" );
        printf( "Verification FAILED!\n" );
    }
//    else
//        printf( "Verification succeed!\n" );
}


// moves one var (v) to the given position (p)
void If_CluMoveVar( word * pF, int nVars, int * Var2Pla, int * Pla2Var, int v, int p )
{
    word pG[CLU_WRD_MAX], * pIn = pF, * pOut = pG, * pTemp;
    int iPlace0, iPlace1, Count = 0;
    assert( v >= 0 && v < nVars );
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

// moves vars to be the most signiticant ones (Group[0] is MSB)
void If_CluMoveGroupToMsb( word * pF, int nVars, int * V2P, int * P2V, If_Grp_t * g )
{
    int v;
    for ( v = 0; v < g->nVars; v++ )
        If_CluMoveVar( pF, nVars, V2P, P2V, g->pVars[g->nVars - 1 - v], nVars - 1 - v );
}

// reverses the variable order
void If_CluReverseOrder( word * pF, int nVars, int * V2P, int * P2V )
{
    int v;
    for ( v = 0; v < nVars; v++ )
        If_CluMoveVar( pF, nVars, V2P, P2V, P2V[0], nVars - 1 - v );
}

// return the number of cofactors w.r.t. the topmost vars (nBSsize)
int If_CluCountCofs( word * pF, int nVars, int nBSsize, int iShift, word pCofs[3][CLU_WRD_MAX/4] )
{
    word iCofs[128], iCof, Result = 0;
    word * pCofA, * pCofB;
    int nMints = (1 << nBSsize);
    int i, c, w, nCofs;
    assert( nBSsize >= 2 && nBSsize <= 7 && nBSsize < nVars );
    if ( nVars - nBSsize < 6 )
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
            if ( pCofs && iCof != iCofs[0] )
                Result |= (((word)1) << i);
            if ( nCofs == 5 )
                break;
        }
        if ( nCofs <= 2 && pCofs )
        {
            assert( nBSsize <= 6 );
            pCofs[0][0] = iCofs[0];
            pCofs[1][0] = (nCofs == 2) ? iCofs[1] : iCofs[0];
            pCofs[2][0] = Result;
        }
    }
    else
    {
        int nWords = If_CluWordNum( nVars - nBSsize );
        assert( nWords * nMints == If_CluWordNum(nVars) );
        for ( nCofs = i = 0; i < nMints; i++ )
        {
            pCofA = pF + i * nWords;
            for ( c = 0; c < nCofs; c++ )
            {
                pCofB = pF + iCofs[c] * nWords;
                for ( w = 0; w < nWords; w++ )
                    if ( pCofA[w] != pCofB[w] )
                        break;
                if ( w == nWords )
                    break;
            }
            if ( c == nCofs )
                iCofs[nCofs++] = i;
            if ( pCofs )
            {
                assert( nBSsize <= 6 );
                pCofB = pF + iCofs[0] * nWords;
                for ( w = 0; w < nWords; w++ )
                    if ( pCofA[w] != pCofB[w] )
                        break;
                if ( w != nWords )
                    Result |= (((word)1) << i);
            }
            if ( nCofs == 5 )
                break;
        }
        if ( nCofs <= 2 && pCofs )
        {
            If_CluCopy( pCofs[0], pF + iCofs[0] * nWords, nVars - nBSsize );
            If_CluCopy( pCofs[1], pF + ((nCofs == 2) ? iCofs[1] : iCofs[0]) * nWords, nVars - nBSsize );
            pCofs[2][0] = Result;
        }
    }
    assert( nCofs >= 1 && nCofs <= 5 );
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
    }
}

// returns 1 if we have special case of cofactors; otherwise, returns 0
int If_CluDetectSpecialCaseCofs( word * pF, int nVars, int iVar )
{
    word Cof0, Cof1;
    int State[6] = {0};
    int i, nWords = If_CluWordNum( nVars );
    assert( iVar < nVars );
    if ( iVar < 6 )
    {
        int Shift = (1 << iVar);
        for ( i = 0; i < nWords; i++ )
        {
            Cof0 =  (pF[i] & ~Truth6[iVar]);
            Cof1 = ((pF[i] &  Truth6[iVar]) >> Shift);

            if ( Cof0 == 0 )
                State[0]++;
            else if ( Cof0 == ~Truth6[iVar] )
                State[1]++;
            else if ( Cof1 == 0 )
                State[2]++;
            else if ( Cof1 == ~Truth6[iVar] )
                State[3]++;
            else if ( Cof0 == ~Cof1 )
                State[4]++;
            else if ( Cof0 == Cof1 )
                State[5]++;
        }
    }
    else
    {
        int k, Step = (1 << (iVar - 6));
        for ( k = 0; k < nWords; k += 2*Step )
        {
            for ( i = 0; i < Step; i++ )
            {
                Cof0 = pF[i];
                Cof1 = pF[Step+i];

                if ( Cof0 == 0 )
                    State[0]++;
                else if ( Cof0 == ~Truth6[iVar] )
                    State[1]++;
                else if ( Cof1 == 0 )
                    State[2]++;
                else if ( Cof1 == ~Truth6[iVar] )
                    State[3]++;
                else if ( Cof0 == ~Cof1 )
                    State[4]++;
                else if ( Cof0 == Cof1 )
                    State[5]++;
            }
            pF    += 2*Step;
        }
        nWords /= 2;
    }
    assert( State[5] != nWords );
    for ( i = 0; i < 5; i++ )
    {
        assert( State[i] <= nWords );
        if ( State[i] == nWords )
            return i;
    }
    return -1;
}

// returns 1 if we have special case of cofactors; otherwise, returns 0
If_Grp_t If_CluDecUsingCofs( word * pTruth, int nVars, int nLutLeaf )
{
    If_Grp_t G = {0};
    word pF2[CLU_WRD_MAX], * pF = pF2;
    int Var2Pla[CLU_VAR_MAX+2], Pla2Var[CLU_VAR_MAX+2];
    int V2P[CLU_VAR_MAX+2], P2V[CLU_VAR_MAX+2];
    int nVarsNeeded = nVars - nLutLeaf;
    int v, i, k, iVar, State;
//Kit_DsdPrintFromTruth( (unsigned*)pTruth, nVars ); printf( "\n" );
    // create local copy
    If_CluCopy( pF, pTruth, nVars );
    for ( k = 0; k < nVars; k++ )
        Var2Pla[k] = Pla2Var[k] = k;
    // find decomposable vars 
    for ( i = 0; i < nVarsNeeded; i++ )
    {
        for ( v = nVars - 1; v >= 0; v-- )
        {
            State = If_CluDetectSpecialCaseCofs( pF, nVars, v );
            if ( State == -1 )
                continue;
            // update the variable place
            iVar = Pla2Var[v];
            while ( Var2Pla[iVar] < nVars - 1 )
            {
                int iPlace0 = Var2Pla[iVar];
                int iPlace1 = Var2Pla[iVar]+1;
                Var2Pla[Pla2Var[iPlace0]]++;
                Var2Pla[Pla2Var[iPlace1]]--;
                Pla2Var[iPlace0] ^= Pla2Var[iPlace1];
                Pla2Var[iPlace1] ^= Pla2Var[iPlace0];
                Pla2Var[iPlace0] ^= Pla2Var[iPlace1];
            }
            // move this variable to the top
            for ( k = 0; k < nVars; k++ )
                V2P[k] = P2V[k] = k;
//Kit_DsdPrintFromTruth( (unsigned*)pF, nVars ); printf( "\n" );
            If_CluMoveVar( pF, nVars, V2P, P2V, v, nVars - 1 );
//Kit_DsdPrintFromTruth( (unsigned*)pF, nVars ); printf( "\n" );
            // choose cofactor to follow
            iVar = nVars - 1;
            if ( State == 0 || State == 1 ) // need cof1
            {
                if ( iVar < 6 )
                    pF[0] = (pF[0] &  Truth6[iVar]) | ((pF[0] &  Truth6[iVar]) >> (1 << iVar));
                else
                    pF += If_CluWordNum( nVars ) / 2;
            }
            else // need cof0
            {
                if ( iVar < 6 )
                    pF[0] = (pF[0] & ~Truth6[iVar]) | ((pF[0] & ~Truth6[iVar]) << (1 << iVar));
            }
            // update the variable count
            nVars--;
            break;
        }
        if ( v == -1 )
            return G;
    }
    // create the resulting group
    G.nVars = nLutLeaf;
    G.nMyu = 2;
    for ( v = 0; v < G.nVars; v++ )
        G.pVars[v] = Pla2Var[v];
    return G;
}



// deriving decomposition
word If_CluDeriveDisjoint( word * pF, int nVars, int * V2P, int * P2V, If_Grp_t * g, If_Grp_t * r )
{
    word pCofs[3][CLU_WRD_MAX/4];
    int i, RetValue, nFSset = nVars - g->nVars;
    RetValue = If_CluCountCofs( pF, nVars, g->nVars, 0, pCofs );
//    assert( RetValue == 2 );

    if ( nFSset < 6 )
        pF[0] = (pCofs[1][0] << (1 << nFSset)) | pCofs[0][0];
    else
    {
        If_CluCopy( pF, pCofs[0], nFSset );
        If_CluCopy( pF + If_CluWordNum(nFSset), pCofs[1], nFSset );
    }
    // create the resulting group
    if ( r )
    {
        r->nVars = nFSset + 1;
        r->nMyu = 0;
        for ( i = 0; i < nFSset; i++ )
            r->pVars[i] = P2V[i];
        r->pVars[nFSset] = nVars;
    }
    return pCofs[2][0];
}
word If_CluDeriveNonDisjoint( word * pF, int nVars, int * V2P, int * P2V, If_Grp_t * g, If_Grp_t * r )
{
    word pCofs[2][CLU_WRD_MAX];
    word Truth0, Truth1, Truth;
    int i, nFSset = nVars - g->nVars, nFSset1 = nFSset + 1;
    If_CluCofactors( pF, nVars, nVars - 1, pCofs[0], pCofs[1] );

//    Extra_PrintHex( stdout, (unsigned *)pCofs[0], nVars ); printf( "\n" );
//    Extra_PrintHex( stdout, (unsigned *)pCofs[1], nVars ); printf( "\n" );

    g->nVars--;
    Truth0 = If_CluDeriveDisjoint( pCofs[0], nVars - 1, V2P, P2V, g, NULL );
    Truth1 = If_CluDeriveDisjoint( pCofs[1], nVars - 1, V2P, P2V, g, NULL );
    Truth  = (Truth1 << (1 << g->nVars)) | Truth0;
    g->nVars++;
    if ( nFSset1 < 6 )
        pF[0] = (pCofs[1][0] << (1 << nFSset1)) | pCofs[0][0];
    else
    {
        If_CluCopy( pF, pCofs[0], nFSset1 );
        If_CluCopy( pF + If_CluWordNum(nFSset1), pCofs[1], nFSset1 );
    }

//    Extra_PrintHex( stdout, (unsigned *)&Truth0, 6 ); printf( "\n" );
//    Extra_PrintHex( stdout, (unsigned *)&Truth1, 6 ); printf( "\n" );
//    Extra_PrintHex( stdout, (unsigned *)&pCofs[0][0], 6 ); printf( "\n" );
//    Extra_PrintHex( stdout, (unsigned *)&pCofs[1][0], 6 ); printf( "\n" );
//    Extra_PrintHex( stdout, (unsigned *)&Truth, 6 ); printf( "\n" );
//    Extra_PrintHex( stdout, (unsigned *)&pF[0], 6 ); printf( "\n" );

    // create the resulting group
    r->nVars = nFSset + 2;
    r->nMyu = 0;
    for ( i = 0; i < nFSset; i++ )
        r->pVars[i] = P2V[i];
    r->pVars[nFSset] = nVars;
    r->pVars[nFSset+1] = g->pVars[g->nVars - 1];
    return Truth;
}

// check non-disjoint decomposition
int If_CluCheckNonDisjointGroup( word * pF, int nVars, int * V2P, int * P2V, If_Grp_t * g )
{
    int v, i, nCofsBest2;
    if ( (g->nMyu == 3 || g->nMyu == 4) )
    {
        word pCofs[2][CLU_WRD_MAX];
        // try cofactoring w.r.t. each variable
        for ( v = 0; v < g->nVars; v++ )
        {
            If_CluCofactors( pF, nVars, V2P[g->pVars[v]], pCofs[0], pCofs[1] );
            nCofsBest2 = If_CluCountCofs( pCofs[0], nVars, g->nVars, 0, NULL );
            if ( nCofsBest2 > 2 )
                continue;
            nCofsBest2 = If_CluCountCofs( pCofs[1], nVars, g->nVars, 0, NULL );
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

 
// finds a good var group (cof count < 6; vars are MSBs)
If_Grp_t If_CluFindGroup( word * pF, int nVars, int iVarStart, int * V2P, int * P2V, int nBSsize, int fDisjoint )
{
    int fVerbose = 0;
    int nRounds = 2;//nBSsize;
    If_Grp_t G = {0}, * g = &G;
    int i, r, v, nCofs, VarBest, nCofsBest2;
    assert( nVars > nBSsize && nVars >= nBSsize + iVarStart && nVars <= CLU_VAR_MAX );
    assert( nBSsize >= 3 && nBSsize <= 6 );
    // start with the default group
    g->nVars = nBSsize;
    g->nMyu = If_CluCountCofs( pF, nVars, nBSsize, 0, NULL );
    for ( i = 0; i < nBSsize; i++ )
        g->pVars[i] = P2V[nVars-nBSsize+i];
    // check if good enough
    if ( g->nMyu == 2 )
        return G;
    if ( !fDisjoint && If_CluCheckNonDisjointGroup( pF, nVars, V2P, P2V, g ) )
        return G;

    if ( fVerbose )
    {
        printf( "Iter %2d  ", -1 );
        If_CluPrintGroup( g );
    }

    // try to find better group
    for ( r = 0; r < nRounds; r++ )
    {
        if ( nBSsize < nVars-1 )
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
        }

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

        if ( fVerbose )
        {
            printf( "Iter %2d  ", r );
            If_CluPrintGroup( g );
        }

        // check if good enough
        if ( g->nMyu == 2 )
            return G;
        if ( !fDisjoint && If_CluCheckNonDisjointGroup( pF, nVars, V2P, P2V, g ) )
            return G;
    }

    assert( r == nRounds );
    g->nVars = 0;
    return G;
}


// double check that the given group has a decomposition
void If_CluCheckGroup( word * pTruth, int nVars, If_Grp_t * g )
{
    word pF[CLU_WRD_MAX];
    int v, nCofs, V2P[CLU_VAR_MAX], P2V[CLU_VAR_MAX];
    assert( g->nVars >= 2 && g->nVars <= 6 ); // vars
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

    if ( !If_CluEqual( pTruth, pF, nVars ) )
        printf( "Permutation FAILED.\n" );
//    else
//        printf( "Permutation successful\n" );
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
If_Grp_t If_CluCheck( If_Man_t * p, word * pTruth, int nVars, int nLutLeaf, int nLutRoot )
{
    If_Grp_t G1 = {0}, R = {0}, * pHashed = NULL;
    word Truth, pF[CLU_WRD_MAX];//, pG[CLU_WRD_MAX];
    int V2P[CLU_VAR_MAX+2], P2V[CLU_VAR_MAX+2];
    int i, nSupp;
    assert( nVars <= CLU_VAR_MAX );
    assert( nVars <= nLutLeaf + nLutRoot - 1 );

 /*
    {
        int pCanonPerm[32];
        short pStore[32];
        unsigned uCanonPhase;
        If_CluCopy( pF, pTruth, nVars );
        uCanonPhase = Kit_TruthSemiCanonicize( pF, pG, nVars, pCanonPerm, pStore );
        G1.nVars = 1;
        return G1;
    }
*/

    // check minnimum base
    If_CluCopy( pF, pTruth, nVars );
    for ( i = 0; i < nVars; i++ )
        V2P[i] = P2V[i] = i;
    // check support
    nSupp = If_CluSupport( pF, nVars );
//Extra_PrintBinary( stdout, &nSupp, 16 );  printf( "\n" );
    if ( !nSupp || !If_CluSuppIsMinBase(nSupp) )
        return G1;

    // check hash table
    pHashed = If_CluHashLookup( p, pTruth );
    if ( pHashed && pHashed->nVars != CLU_UNUSED )
        return *pHashed;

    // detect easy cofs
    G1 = If_CluDecUsingCofs( pTruth, nVars, nLutLeaf );
    if ( G1.nVars == 0 )
    {
        // perform testing
        G1 = If_CluFindGroup( pF, nVars, 0, V2P, P2V, nLutLeaf, nLutLeaf + nLutRoot == nVars + 1 );
//        If_CluCheckPerm( pTruth, pF, nVars, V2P, P2V );
        if ( G1.nVars == 0 )
        {
            // perform testing with a smaller set
            if ( nVars < nLutLeaf + nLutRoot - 2 )
            {
                nLutLeaf--;
                G1 = If_CluFindGroup( pF, nVars, 0, V2P, P2V, nLutLeaf, nLutLeaf + nLutRoot == nVars + 1 );
                nLutLeaf++;
            }
            if ( G1.nVars == 0 )
            {
                // perform testing with a different order
                If_CluReverseOrder( pF, nVars, V2P, P2V );
                G1 = If_CluFindGroup( pF, nVars, 0, V2P, P2V, nLutLeaf, nLutLeaf + nLutRoot == nVars + 1 );

                // check permutation
//                If_CluCheckPerm( pTruth, pF, nVars, V2P, P2V );
                if ( G1.nVars == 0 )
                {
/*
                    if ( nVars == 6 )
                    {
                        Extra_PrintHex( stdout, (unsigned *)pF, nVars );  printf( "    " );
                        Kit_DsdPrintFromTruth( (unsigned*)pF, nVars );  printf( "\n" );
                        if ( !If_CutPerformCheck07( (unsigned *)pF, 6, 6, NULL ) )
                            printf( "no\n" );
                    } 
*/
                    return pHashed ? (*pHashed = G1) : G1;
                }
            }
        }
    }

    // derive
    if ( 0 )
    {
        If_CluMoveGroupToMsb( pF, nVars, V2P, P2V, &G1 );
        if ( G1.nMyu == 2 )
            Truth = If_CluDeriveDisjoint( pF, nVars, V2P, P2V, &G1, &R );
        else
            Truth = If_CluDeriveNonDisjoint( pF, nVars, V2P, P2V, &G1, &R );

        // perform checking
        if ( 0 )
        {
            If_CluCheckGroup( pTruth, nVars, &G1 );
            If_CluVerify( pTruth, nVars, &G1, &R, Truth, pF );
        }
    }
    return pHashed ? (*pHashed = G1) : G1;
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
//    pCut->fUser = 1;
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
        printf( "Root size (%d) should belong to {3,4,5,6}.\n", nLutRoot );
        return ABC_INFINITY;
    }
    if ( nLeaves > nLutLeaf + nLutRoot - 1 )
    {
        printf( "The cut size (%d) is too large for the LUT structure %d%d.\n", If_CutLeaveNum(pCut), nLutLeaf, nLutRoot );
        return ABC_INFINITY;
    }

    // remember the delays
    If_CutForEachLeaf( p, pCut, pLeaf, i )
        Delays[i] = If_ObjCutBest(pLeaf)->Delay;

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
        return 1.0 + If_CluDelayMax( &G1, Delays );
    }

    // derive the first group
    G1 = If_CluCheck( p, (word *)If_CutTruth(pCut), nLeaves, nLutLeaf, nLutRoot );
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
    assert( !G2.nVars || (G2.nMyu >= 2 && G2.nMyu <= 4) );
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


/**Function*************************************************************

  Synopsis    [Performs additional check.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CutPerformCheck16( If_Man_t * p, unsigned * pTruth, int nVars, int nLeaves, char * pStr )
{
    If_Grp_t G1 = {0}, G2 = {0}, G3 = {0};
    int nLutLeaf, nLutRoot;
    // quit if parameters are wrong
    if ( strlen(pStr) != 2 )
    {
        printf( "Wrong LUT struct (%s)\n", pStr );
        return 0;
    }
    nLutLeaf = pStr[0] - '0';
    if ( nLutLeaf < 3 || nLutLeaf > 6 )
    {
        printf( "Leaf size (%d) should belong to {3,4,5,6}.\n", nLutLeaf );
        return 0;
    }
    nLutRoot = pStr[1] - '0';
    if ( nLutRoot < 3 || nLutRoot > 6 )
    {
        printf( "Root size (%d) should belong to {3,4,5,6}.\n", nLutRoot );
        return 0;
    }
    if ( nLeaves > nLutLeaf + nLutRoot - 1 )
    {
        printf( "The cut size (%d) is too large for the LUT structure %d%d.\n", nLeaves, nLutLeaf, nLutRoot );
        return 0;
    }

    // consider easy case
    if ( nLeaves <= Abc_MaxInt( nLutLeaf, nLutRoot ) )
        return 1;

    // derive the first group
    G1 = If_CluCheck( p, (word *)pTruth, nLeaves, nLutLeaf, nLutRoot );
    if ( G1.nVars == 0 )
    {
//        printf( "-%d ", nLeaves );
        return 0;
    }
//    printf( "+%d ", nLeaves );
    return 1;
}


// testing procedure
void If_CluTest()
{
//    word t = 0xff00f0f0ccccaaaa;
//    word t = 0xfedcba9876543210;
//    word t = 0xec64000000000000;
//    word t = 0x0100200000000001;
//    word t2[4] = { 0x0000800080008000, 0x8000000000008000, 0x8000000080008000, 0x0000000080008000 };
//    word t = 0x07770FFF07770FFF;
//    word t = 0x002000D000D00020;
//    word t = 0x000F000E000F000F;
    word t = 0xF7FFF7F7F7F7F7F7;
    int nVars    = 6;
    int nLutLeaf = 4;
    int nLutRoot = 4;
    If_Grp_t G;

    return;

    If_CutPerformCheck07( NULL, (unsigned *)&t, 6, 6, NULL );
//    return;

    Kit_DsdPrintFromTruth( (unsigned*)&t, nVars ); printf( "\n" );

    G = If_CluCheck( NULL, &t, nVars, nLutLeaf, nLutRoot );

    If_CluPrintGroup( &G );
}




////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

