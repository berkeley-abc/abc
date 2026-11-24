/**CFile****************************************************************

  FileName    [abcLutResyn.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Reduces the LUT count by post-mapping Boolean decomposition.]

  Description [For every LUT of a mapped network, tries to re-implement the
  function of a fanout-free cone rooted at the LUT by one or two LUTs of the
  same size. The timing is protected: the levels of all nodes are never
  increased (with a user-given growth bound), by requiring the new LUTs to
  finish no later than the required level of the replaced root.]

  Author      [Longfei Fan]

***********************************************************************/

#include "base/abc/abc.h"
#include "misc/util/utilTruth.h"
#include "map/if/if.h"

ABC_NAMESPACE_IMPL_START

#define LUTRESYN_CONE_MAX   16
#define LUTRESYN_LEAF_MAX   11
#define LUTRESYN_WORD_MAX   ( 1 << ( LUTRESYN_LEAF_MAX - 6 ) )
#define LUTRESYN_SLICE_MAX  ( 1 << 5 )
#define LUTRESYN_KIND_MAX   ( 1 << 6 )
#define LUTRESYN_M3_TRY_MAX 20000
#define LUTRESYN_CUT_EXPAND_MAX 16
#define LUTRESYN_CUT_TRY_MAX    2
#define LUTRESYN_CUT_CAND_MAX   16

extern Hop_Obj_t * Kit_TruthToHop( Hop_Man_t * pMan, unsigned * pTruth, int nVars, Vec_Int_t * vMemory );

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Abc_LutResynSol_t_
{
    int              Mode;                         // 0 = none, 1/2/3 = number of resulting LUTs
    int              nLeaves;                      // one-LUT solution
    int              pLeaves[LUTRESYN_LEAF_MAX];   // one-LUT solution: indices into vLeaves
    word             Truth1[LUTRESYN_WORD_MAX];    // one-LUT solution: truth over pLeaves
    int              nG;                           // two/three-LUT solution: first prefix g1
    int              pGLeaves[LUTRESYN_LEAF_MAX];  // two/three-LUT solution: indices into vLeaves
    word             TruthG;                       // two/three-LUT solution: truth over pGLeaves
    int              nG2;                          // three-LUT solution: second prefix g2
    int              pG2Leaves[LUTRESYN_LEAF_MAX]; // three-LUT solution: indices into vLeaves
    word             TruthG2;                      // three-LUT solution: truth over pG2Leaves
    int              nH;                           // two/three-LUT solution: suffix h
    int              pHLeaves[LUTRESYN_LEAF_MAX];  // suffix h: -1 marks g1, -2 marks g2
    word             TruthH;                       // suffix h: truth over pHLeaves
} Abc_LutResynSol_t;

typedef struct Abc_LutResynCone_t_
{
    Vec_Ptr_t *      vCone;                      // fanout-free cone rooted at a node
    Vec_Ptr_t *      vLeaves;                    // leaves of the cone
} Abc_LutResynCone_t;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns the next combination of nComb elements out of nTotal.]

  Description [The combination is stored as increasing indices and starts
  from (0, 1, ..., nComb-1). Returns 0 when the combinations are exhausted.]

***********************************************************************/
static int Abc_LutResynNextComb( int * pComb, int nComb, int nTotal )
{
    int i, j;
    for ( i = nComb - 1; i >= 0; i-- )
        if ( pComb[i] < nTotal - nComb + i )
        {
            pComb[i]++;
            for ( j = i + 1; j < nComb; j++ )
                pComb[j] = pComb[j-1] + 1;
            return 1;
        }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Computes the truth table of variable iVar over nVars variables.]

***********************************************************************/
static void Abc_LutResynTruthVar( word * pTruth, int nVars, int iVar )
{
    int nWords = Abc_TtWordNum( nVars );
    int Limit = 1 << nVars;
    int i;
    for ( i = 0; i < nWords; i++ )
        pTruth[i] = 0;
    for ( i = 0; i < Limit; i++ )
        if ( (i >> iVar) & 1 )
            pTruth[i>>6] |= (word)1 << (i & 63);
}

/**Function*************************************************************

  Synopsis    [Converts a 64-bit truth table into the Kit word format.]

***********************************************************************/
static void Abc_LutResynToKit( word * pTruth, int nVars, unsigned * pKit )
{
    int nWords = Abc_TtWordNum( nVars );
    int i;
    if ( nVars <= 5 )
    {
        // Kit stores small functions periodically in a 32-bit word
        unsigned u = (unsigned)pTruth[0];
        int nShift = 1 << nVars;
        while ( nShift < 32 )
        {
            u |= u << nShift;
            nShift <<= 1;
        }
        pKit[0] = u;
        return;
    }
    for ( i = 0; i < nWords; i++ )
    {
        pKit[2*i]   = (unsigned)pTruth[i];
        pKit[2*i+1] = (unsigned)(pTruth[i] >> 32);
    }
}

/**Function*************************************************************

  Synopsis    [Counts the fanouts of a node that are outside the cone.]

  Description [A node with outside fanouts is duplicated when absorbed.]

***********************************************************************/
static int Abc_LutResynLeafOutside( Vec_Ptr_t * vCone, Abc_Obj_t * pObj )
{
    int k, nOutside = 0;
    for ( k = 0; k < Abc_ObjFanoutNum(pObj); k++ )
        nOutside += Vec_PtrFind( vCone, Abc_ObjFanout(pObj, k) ) == -1;
    return nOutside;
}

/**Function*************************************************************

  Synopsis    [Collects a fanout-free cone rooted at pRoot.]

  Description [Starts from the root and greedily absorbs the leaf whose
  inclusion adds the fewest new leaves. A leaf is absorbed only when all
  its fanouts are already in the cone, unless it has outside fanouts and
  the duplicated-LUT budget nMaxExt is not exhausted. The cone is limited
  to LUTRESYN_CONE_MAX nodes and its leaves to min(LUTRESYN_LEAF_MAX, 2K-1).]

***********************************************************************/
static int Abc_LutResynCollectCone( Abc_Obj_t * pRoot, int nLutSize, int nMaxExt, Vec_Ptr_t * vCone, Vec_Ptr_t * vLeaves )
{
    int nLeafMax = Abc_MinInt( LUTRESYN_LEAF_MAX, 2 * nLutSize - 1 );
    Abc_Obj_t * pObj, * pFanin;
    int i, k, Best, BestDelta, Delta, nNew, nOutside, nExt = 0, fExt, fBestExt = 0;
    Vec_PtrClear( vCone );
    Vec_PtrClear( vLeaves );
    if ( Abc_ObjFaninNum(pRoot) > nLeafMax )
        return 0;
    Vec_PtrPush( vCone, pRoot );
    for ( i = 0; i < Abc_ObjFaninNum(pRoot); i++ )
        Vec_PtrPushUnique( vLeaves, Abc_ObjFanin(pRoot, i) );
    while ( Vec_PtrSize(vCone) < LUTRESYN_CONE_MAX )
    {
        Best = -1;
        BestDelta = 0;
        fBestExt = 0;
        for ( i = 0; i < Vec_PtrSize(vLeaves); i++ )
        {
            pObj = (Abc_Obj_t *)Vec_PtrEntry( vLeaves, i );
            if ( !Abc_ObjIsNode(pObj) || pObj->pData == NULL || Abc_ObjFanoutNum(pObj) == 0 )
                continue;
            nOutside = Abc_LutResynLeafOutside( vCone, pObj );
            fExt = nOutside > 0;
            if ( fExt && nExt >= nMaxExt )
                continue;
            nNew = 0;
            for ( k = 0; k < Abc_ObjFaninNum(pObj); k++ )
            {
                pFanin = Abc_ObjFanin( pObj, k );
                if ( Vec_PtrFind(vLeaves, pFanin) == -1 && Vec_PtrFind(vCone, pFanin) == -1 )
                    nNew++;
            }
            Delta = nNew - 1;
            if ( Vec_PtrSize(vLeaves) + Delta > nLeafMax )
                continue;
            if ( Best == -1 || Delta < BestDelta || (Delta == BestDelta && !fExt && fBestExt) )
            {
                Best = i;
                BestDelta = Delta;
                fBestExt = fExt;
                if ( Delta == -1 && !fExt )
                    break;
            }
        }
        if ( Best == -1 )
            break;
        if ( fBestExt )
            nExt++;
        pObj = (Abc_Obj_t *)Vec_PtrEntry( vLeaves, Best );
        Vec_PtrRemove( vLeaves, pObj );
        Vec_PtrPush( vCone, pObj );
        for ( k = 0; k < Abc_ObjFaninNum(pObj); k++ )
        {
            pFanin = Abc_ObjFanin( pObj, k );
            if ( Vec_PtrFind(vLeaves, pFanin) == -1 && Vec_PtrFind(vCone, pFanin) == -1 )
                Vec_PtrPush( vLeaves, pFanin );
        }
    }
    return Vec_PtrSize(vCone) >= 2;
}

/**Function*************************************************************

  Synopsis    [Records the current cone state as a candidate cut.]

***********************************************************************/
static void Abc_LutResynCollectCuts_rec( Vec_Ptr_t * vCone, Vec_Ptr_t * vLeaves, int nLeafMax, int nMaxExt, int nExtUsed,
                                       Abc_LutResynCone_t * pCands, int * pnCands, int * pnExpand )
{
    Abc_Obj_t * pObj, * pFanin;
    int pOrder[LUTRESYN_LEAF_MAX], pDelta[LUTRESYN_LEAF_MAX], pExt[LUTRESYN_LEAF_MAX];
    int nAvail = 0, i, j, k, nLeavesOld, nNew, nOutside, Delta, fExt;
    if ( Vec_PtrSize(vCone) >= 2 && Vec_PtrSize(vLeaves) <= nLeafMax && *pnCands < LUTRESYN_CUT_CAND_MAX )
    {
        pCands[*pnCands].vCone = Vec_PtrDup( vCone );
        pCands[*pnCands].vLeaves = Vec_PtrDup( vLeaves );
        (*pnCands)++;
    }
    if ( Vec_PtrSize(vCone) >= LUTRESYN_CONE_MAX || *pnExpand >= LUTRESYN_CUT_EXPAND_MAX )
        return;
    if ( Vec_PtrSize(vLeaves) > LUTRESYN_LEAF_MAX )
        return;
    // rank the absorbable leaves by the number of new leaves they add
    for ( i = 0; i < Vec_PtrSize(vLeaves); i++ )
    {
        pObj = (Abc_Obj_t *)Vec_PtrEntry( vLeaves, i );
        if ( !Abc_ObjIsNode(pObj) || pObj->pData == NULL || Abc_ObjFanoutNum(pObj) == 0 )
            continue;
        nOutside = Abc_LutResynLeafOutside( vCone, pObj );
        fExt = nOutside > 0;
        if ( fExt && nExtUsed >= nMaxExt )
            continue;
        nNew = 0;
        for ( k = 0; k < Abc_ObjFaninNum(pObj); k++ )
        {
            pFanin = Abc_ObjFanin( pObj, k );
            if ( Vec_PtrFind(vLeaves, pFanin) == -1 && Vec_PtrFind(vCone, pFanin) == -1 )
                nNew++;
        }
        Delta = nNew - 1;
        if ( Vec_PtrSize(vLeaves) + Delta > nLeafMax )
            continue;
        pOrder[nAvail] = i;
        pDelta[nAvail] = Delta;
        pExt[nAvail] = fExt;
        nAvail++;
    }
    for ( i = 1; i < nAvail; i++ )
        for ( j = i; j > 0 && pDelta[j-1] > pDelta[j]; j-- )
        {
            int Temp = pDelta[j]; pDelta[j] = pDelta[j-1]; pDelta[j-1] = Temp;
            Temp = pOrder[j]; pOrder[j] = pOrder[j-1]; pOrder[j-1] = Temp;
            Temp = pExt[j]; pExt[j] = pExt[j-1]; pExt[j-1] = Temp;
        }
    for ( i = 0; i < nAvail && *pnExpand < LUTRESYN_CUT_EXPAND_MAX; i++ )
    {
        pObj = (Abc_Obj_t *)Vec_PtrEntry( vLeaves, pOrder[i] );
        (*pnExpand)++;
        nLeavesOld = Vec_PtrSize( vLeaves );
        Vec_PtrRemove( vLeaves, pObj );
        Vec_PtrPush( vCone, pObj );
        for ( k = 0; k < Abc_ObjFaninNum(pObj); k++ )
        {
            pFanin = Abc_ObjFanin( pObj, k );
            if ( Vec_PtrFind(vLeaves, pFanin) == -1 && Vec_PtrFind(vCone, pFanin) == -1 )
                Vec_PtrPush( vLeaves, pFanin );
        }
        Abc_LutResynCollectCuts_rec( vCone, vLeaves, nLeafMax, nMaxExt, nExtUsed + pExt[i], pCands, pnCands, pnExpand );
        Vec_PtrShrink( vLeaves, nLeavesOld - 1 );
        Vec_PtrPop( vCone );
        if ( pOrder[i] < Vec_PtrSize(vLeaves) )
            Vec_PtrInsert( vLeaves, pOrder[i], pObj );
        else
            Vec_PtrPush( vLeaves, pObj );
    }
}

/**Function*************************************************************

  Synopsis    [Enumerates several fanout-free cones rooted at pRoot.]

  Description [Runs a bounded depth-first search over the states obtained
  by absorbing leaves. Every state is a valid cone, so the search covers
  all cones that the greedy collector can build in any absorption order,
  including its own result. The number of expansions is limited by
  LUTRESYN_CUT_EXPAND_MAX and the number of recorded cones by
  LUTRESYN_CUT_CAND_MAX.]

***********************************************************************/
static int Abc_LutResynCollectCuts( Abc_Obj_t * pRoot, int nLutSize, int nMaxExt, Abc_LutResynCone_t * pCands )
{
    Vec_Ptr_t * vCone = Vec_PtrAlloc( LUTRESYN_CONE_MAX );
    Vec_Ptr_t * vLeaves = Vec_PtrAlloc( LUTRESYN_LEAF_MAX );
    int nLeafMax = Abc_MinInt( LUTRESYN_LEAF_MAX, 2 * nLutSize - 1 );
    int nCands = 0, nExpand = 0, i;
    Vec_PtrPush( vCone, pRoot );
    for ( i = 0; i < Abc_ObjFaninNum(pRoot); i++ )
        Vec_PtrPushUnique( vLeaves, Abc_ObjFanin(pRoot, i) );
    Abc_LutResynCollectCuts_rec( vCone, vLeaves, nLeafMax, nMaxExt, 0, pCands, &nCands, &nExpand );
    Vec_PtrFree( vCone );
    Vec_PtrFree( vLeaves );
    return nCands;
}

/**Function*************************************************************

  Synopsis    [Orders candidate cones by decreasing node count.]

***********************************************************************/
static int Abc_LutResynConeCompare( const void * p1, const void * p2 )
{
    Abc_LutResynCone_t * pC1 = (Abc_LutResynCone_t *)p1;
    Abc_LutResynCone_t * pC2 = (Abc_LutResynCone_t *)p2;
    if ( Vec_PtrSize(pC1->vCone) != Vec_PtrSize(pC2->vCone) )
        return Vec_PtrSize(pC2->vCone) - Vec_PtrSize(pC1->vCone);
    return Vec_PtrSize(pC1->vLeaves) - Vec_PtrSize(pC2->vLeaves);
}

/**Function*************************************************************

  Synopsis    [Checks whether two cones have the same leaves.]

***********************************************************************/
static int Abc_LutResynConeSameLeaves( Abc_LutResynCone_t * pC1, Abc_LutResynCone_t * pC2 )
{
    int i;
    if ( Vec_PtrSize(pC1->vLeaves) != Vec_PtrSize(pC2->vLeaves) )
        return 0;
    for ( i = 0; i < Vec_PtrSize(pC1->vLeaves); i++ )
        if ( Vec_PtrFind( pC2->vLeaves, Vec_PtrEntry(pC1->vLeaves, i) ) == -1 )
            return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Builds the truth table of the cone root over its leaves.]

  Description [The leaves are the first variables. The cone nodes are
  ordered so that every node is processed after its fanins. This order
  is computed here because absorbed nodes with outside fanouts can make
  the absorption order non-topological.]

***********************************************************************/
static int Abc_LutResynTruthCone( Abc_Ntk_t * pNtk, Vec_Ptr_t * vCone, Vec_Ptr_t * vLeaves, word * pStore, word * pCube, word * pConeTruth )
{
    Hop_Man_t * pMan = (Hop_Man_t *)pNtk->pManFunc;
    Vec_Int_t * vTruth = Vec_IntAlloc( 0 );
    int n = Vec_PtrSize( vLeaves );
    int nCone = Vec_PtrSize( vCone );
    int nWords = Abc_TtWordNum( n );
    int pOrder[LUTRESYN_CONE_MAX], fDone[LUTRESYN_CONE_MAX];
    int i, k, j, m, Limit, nFans, iLeaf, iCone, nBits, nDone, kNext, fReady;
    Abc_Obj_t * pObj, * pFanin;
    word * pFaninTruth, t;
    unsigned * pTruth;
    int fOk = 1;

    for ( i = 0; i < n; i++ )
        Abc_LutResynTruthVar( pStore + i * nWords, n, i );
    for ( k = 0; k < nCone; k++ )
        fDone[k] = 0;
    for ( nDone = 0; nDone < nCone; nDone++ )
    {
        kNext = -1;
        for ( k = 0; k < nCone && kNext == -1; k++ )
        {
            if ( fDone[k] )
                continue;
            pObj = (Abc_Obj_t *)Vec_PtrEntry( vCone, k );
            fReady = 1;
            for ( j = 0; j < Abc_ObjFaninNum(pObj); j++ )
            {
                iCone = Vec_PtrFind( vCone, Abc_ObjFanin(pObj, j) );
                if ( iCone >= 0 && !fDone[iCone] )
                {
                    fReady = 0;
                    break;
                }
            }
            if ( fReady )
                kNext = k;
        }
        if ( kNext == -1 )
        {
            fOk = 0;
            break;
        }
        fDone[kNext] = 1;
        pOrder[nDone] = kNext;
    }
    for ( m = 0; m < nDone; m++ )
    {
        k = pOrder[m];
        pObj = (Abc_Obj_t *)Vec_PtrEntry( vCone, k );
        nFans = Abc_ObjFaninNum( pObj );
        if ( nFans > 6 || nFans > Hop_ManPiNum(pMan) )
        {
            fOk = 0;
            break;
        }
        pTruth = Hop_ManConvertAigToTruth( pMan, (Hop_Obj_t *)pObj->pData, nFans, vTruth, 0 );
        t = (word)pTruth[0] | (nFans >= 6 ? ((word)pTruth[1] << 32) : (word)0);
        if ( nFans == 0 )
        {
            if ( t & 1 )
                Abc_TtFill( pStore + (n + k) * nWords, nWords );
            else
                Abc_TtClear( pStore + (n + k) * nWords, nWords );
            continue;
        }
        Abc_TtClear( pStore + (n + k) * nWords, nWords );
        Limit = 1 << nFans;
        for ( i = 0; i < Limit; i++ )
        {
            if ( ((t >> i) & 1) == 0 )
                continue;
            Abc_TtFill( pCube, nWords );
            for ( j = 0; j < nFans; j++ )
            {
                pFanin = Abc_ObjFanin( pObj, j );
                iLeaf = Vec_PtrFind( vLeaves, pFanin );
                if ( iLeaf >= 0 )
                    pFaninTruth = pStore + iLeaf * nWords;
                else
                {
                    iCone = Vec_PtrFind( vCone, pFanin );
                    assert( iCone >= 0 );
                    pFaninTruth = pStore + (n + iCone) * nWords;
                }
                Abc_TtAndCompl( pCube, pCube, 0, pFaninTruth, ((i >> j) & 1) ? 0 : 1, nWords );
            }
            Abc_TtOr( pStore + (n + k) * nWords, pStore + (n + k) * nWords, pCube, nWords );
        }
    }
    if ( fOk )
    {
        Abc_TtCopy( pConeTruth, pStore + n * nWords, nWords, 0 );
        nBits = 1 << n;
        if ( nBits & 63 )
            pConeTruth[nWords-1] &= ((word)1 << (nBits & 63)) - 1;
    }
    Vec_IntFree( vTruth );
    return fOk;
}

/**Function*************************************************************

  Synopsis    [Returns the level of a leaf given its truth-table variable.]

***********************************************************************/
static int Abc_LutResynLeafLevel( Vec_Ptr_t * vLeaves, int * pPerm, int iVar )
{
    return Abc_ObjLevel( (Abc_Obj_t *)Vec_PtrEntry(vLeaves, pPerm[iVar]) );
}

/**Function*************************************************************

  Synopsis    [Tries one partition of the variables into Free, Bound, and
  Shared sets.]

  Description [The prefix LUT g is over Bound and Shared; the suffix LUT h
  is over Free, Shared, and g. A partition works when for every assignment
  of Shared the cofactors over Bound produce at most two distinct slices
  over Free. The timing is checked first: Free leaves must arrive by
  ReqLevel-1 and Bound/Shared leaves by ReqLevel-2.]

***********************************************************************/
static int Abc_LutResynTryPartition( Abc_LutResynSol_t * pSol, word * pTruth, int n, int * pPerm, Vec_Ptr_t * vLeaves, int ReqLevel,
                                   int * pFree, int nFree, int * pBound, int nBound, int * pShared, int nShared )
{
    word Buf[LUTRESYN_WORD_MAX];
    word Slice0[LUTRESYN_SLICE_MAX], Slice1[LUTRESYN_SLICE_MAX];
    int nKinds[LUTRESYN_SLICE_MAX];
    word TruthG = 0, TruthH = 0;
    int pOrder[16], pGMap[16], pHMap[16];
    int nWords = Abc_TtWordNum( n );
    int nFbits = 1 << nFree, nBbits = 1 << nBound, nSbits = 1 << nShared;
    int i, s, b, f, pos, idx, fG1, fHasG;
    int Lev, MaxFree, MaxRest, nG, nH;
    assert( nFree + nBound + nShared == n );
    assert( nShared <= 5 && nBound + nShared <= 6 && nFree + nShared + 1 <= 6 );
    // timing
    MaxFree = -1;
    for ( i = 0; i < nFree; i++ )
    {
        Lev = Abc_LutResynLeafLevel( vLeaves, pPerm, pFree[i] );
        MaxFree = Abc_MaxInt( MaxFree, Lev );
    }
    MaxRest = -1;
    for ( i = 0; i < nBound; i++ )
    {
        Lev = Abc_LutResynLeafLevel( vLeaves, pPerm, pBound[i] );
        MaxRest = Abc_MaxInt( MaxRest, Lev );
    }
    for ( i = 0; i < nShared; i++ )
    {
        Lev = Abc_LutResynLeafLevel( vLeaves, pPerm, pShared[i] );
        MaxRest = Abc_MaxInt( MaxRest, Lev );
    }
    if ( MaxFree + 1 > ReqLevel || MaxRest > ReqLevel - 2 )
        return 0;
    // reorder the truth as [Free, Bound, Shared]
    pos = 0;
    for ( i = 0; i < nFree; i++ )
        pOrder[pos++] = pFree[i];
    for ( i = 0; i < nBound; i++ )
        pOrder[pos++] = pBound[i];
    for ( i = 0; i < nShared; i++ )
        pOrder[pos++] = pShared[i];
    assert( pos == n );
    Abc_TtCopy( Buf, pTruth, nWords, 0 );
    Abc_TtPermute( Buf, pOrder, n );
    // slice the cofactors over Shared and Bound
    for ( s = 0; s < nSbits; s++ )
    {
        nKinds[s] = 0;
        for ( b = 0; b < nBbits; b++ )
        {
            word Slice = 0;
            for ( f = 0; f < nFbits; f++ )
            {
                idx = f | (b << nFree) | (s << (nFree + nBound));
                if ( (Buf[idx>>6] >> (idx & 63)) & 1 )
                    Slice |= (word)1 << f;
            }
            if ( nKinds[s] == 0 )
            {
                Slice0[s] = Slice;
                nKinds[s] = 1;
                fG1 = 0;
            }
            else if ( Slice == Slice0[s] )
                fG1 = 0;
            else if ( nKinds[s] == 1 )
            {
                Slice1[s] = Slice;
                nKinds[s] = 2;
                fG1 = 1;
            }
            else if ( Slice == Slice1[s] )
                fG1 = 1;
            else
                return 0;
            if ( fG1 )
                TruthG |= (word)1 << (b | (s << nBound));
        }
    }
    // build the suffix truth over [Free, Shared, g]
    for ( s = 0; s < nSbits; s++ )
    {
        word SliceX = (nKinds[s] == 2) ? Slice1[s] : Slice0[s];
        for ( f = 0; f < nFbits; f++ )
        {
            if ( (Slice0[s] >> f) & 1 )
                TruthH |= (word)1 << (f | (s << nFree));
            if ( (SliceX >> f) & 1 )
                TruthH |= (word)1 << (f | (s << nFree) | (1 << (nFree + nShared)));
        }
    }
    // minimize the pins of g and h
    for ( i = 0; i < nBound + nShared; i++ )
        pGMap[i] = i;
    for ( i = 0; i < nFree + nShared + 1; i++ )
        pHMap[i] = i;
    nG = Abc_Tt6MinBase( &TruthG, pGMap, nBound + nShared );
    nH = Abc_Tt6MinBase( &TruthH, pHMap, nFree + nShared + 1 );
    if ( nG == 0 || nH == 0 )
        return 0;
    // h does not depend on g: the function fits in one LUT
    fHasG = 0;
    for ( i = 0; i < nH; i++ )
        if ( pHMap[i] == nFree + nShared )
            fHasG = 1;
    if ( !fHasG )
    {
        pSol->Mode = 1;
        pSol->nLeaves = nH;
        for ( i = 0; i < nH; i++ )
            pSol->pLeaves[i] = pPerm[ pHMap[i] < nFree ? pFree[pHMap[i]] : pShared[pHMap[i] - nFree] ];
        Abc_TtCopy( pSol->Truth1, &TruthH, 1, 0 );
        return 1;
    }
    pSol->Mode = 2;
    pSol->nG = nG;
    for ( i = 0; i < nG; i++ )
        pSol->pGLeaves[i] = pPerm[ pGMap[i] < nBound ? pBound[pGMap[i]] : pShared[pGMap[i] - nBound] ];
    pSol->TruthG = TruthG;
    pSol->nH = nH;
    for ( i = 0; i < nH; i++ )
    {
        if ( pHMap[i] < nFree )
            pSol->pHLeaves[i] = pPerm[ pFree[pHMap[i]] ];
        else if ( pHMap[i] < nFree + nShared )
            pSol->pHLeaves[i] = pPerm[ pShared[pHMap[i] - nFree] ];
        else
            pSol->pHLeaves[i] = -1;
    }
    pSol->TruthH = TruthH;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Tries a three-LUT decomposition with two prefixes.]

  Description [The variables are split into Free, Bound1, Bound2, and
  Shared. The prefixes are g1(Bound1, Shared) and g2(Bound2, Shared); the
  suffix is h(Free, Shared, g1, g2). For every assignment of Shared, the
  slices of the function over Free, indexed by (Bound1, Bound2), must
  depend on (Bound1, Bound2) only through a class of Bound1 (at most two)
  and a class of Bound2 (at most two). Then g1 and g2 compute the class
  numbers and h implements the suffix.]

***********************************************************************/
static int Abc_LutResynTryPartition3( Abc_LutResynSol_t * pSol, word * pTruth, int n, int * pPerm, Vec_Ptr_t * vLeaves, int ReqLevel,
                                    int * pFree, int nFree, int * pBound1, int nBound1,
                                    int * pBound2, int nBound2, int * pShared, int nShared )
{
    word Buf[LUTRESYN_WORD_MAX];
    word * pSlices;
    word TruthG1 = 0, TruthG2 = 0, TruthH = 0;
    int pOrder[16], pMap1[16], pMap2[16], pHMap[16];
    int pRowKind[LUTRESYN_KIND_MAX], pColKind[LUTRESYN_KIND_MAX];
    int nWords = Abc_TtWordNum( n );
    int nFbits = 1 << nFree, nSbits = 1 << nShared;
    int nB1bits = 1 << nBound1, nB2bits = 1 << nBound2;
    int i, k, s, b1, b2, f, pos, idx, nG1, nG2, nH;
    int MaxFree, MaxRest, fOk;
    assert( nFree + nBound1 + nBound2 + nShared == n );
    assert( nBound1 > 0 && nBound2 > 0 );
    assert( nShared <= 5 && nBound1 + nShared <= 6 && nBound2 + nShared <= 6 && nFree + nShared + 2 <= 6 );
    // timing: Free arrives by ReqLevel-1; prefix inputs by ReqLevel-2;
    // the prefixes have level ReqLevel-1 and the suffix ReqLevel
    MaxFree = -1;
    for ( i = 0; i < nFree; i++ )
        MaxFree = Abc_MaxInt( MaxFree, Abc_LutResynLeafLevel( vLeaves, pPerm, pFree[i] ) );
    MaxRest = -1;
    for ( i = 0; i < nBound1; i++ )
        MaxRest = Abc_MaxInt( MaxRest, Abc_LutResynLeafLevel( vLeaves, pPerm, pBound1[i] ) );
    for ( i = 0; i < nBound2; i++ )
        MaxRest = Abc_MaxInt( MaxRest, Abc_LutResynLeafLevel( vLeaves, pPerm, pBound2[i] ) );
    for ( i = 0; i < nShared; i++ )
        MaxRest = Abc_MaxInt( MaxRest, Abc_LutResynLeafLevel( vLeaves, pPerm, pShared[i] ) );
    if ( MaxFree + 1 > ReqLevel || MaxRest > ReqLevel - 2 )
        return 0;
    // reorder the truth as [Free, Bound1, Bound2, Shared]
    pos = 0;
    for ( i = 0; i < nFree; i++ )
        pOrder[pos++] = pFree[i];
    for ( i = 0; i < nBound1; i++ )
        pOrder[pos++] = pBound1[i];
    for ( i = 0; i < nBound2; i++ )
        pOrder[pos++] = pBound2[i];
    for ( i = 0; i < nShared; i++ )
        pOrder[pos++] = pShared[i];
    assert( pos == n );
    Abc_TtCopy( Buf, pTruth, nWords, 0 );
    Abc_TtPermute( Buf, pOrder, n );
    // for every shared assignment, check the (Bound1, Bound2) matrix of slices
    pSlices = ABC_ALLOC( word, nB1bits * nB2bits );
    fOk = 1;
    for ( s = 0; s < nSbits && fOk; s++ )
    {
        int pRowRep[2] = { -1, -1 }, pColRep[2] = { -1, -1 }, nRows = 0, nCols = 0;
        // extract all slices
        for ( b1 = 0; b1 < nB1bits; b1++ )
            for ( b2 = 0; b2 < nB2bits; b2++ )
            {
                word Slice = 0;
                for ( f = 0; f < nFbits; f++ )
                {
                    idx = f | (b1 << nFree) | (b2 << (nFree + nBound1)) | (s << (nFree + nBound1 + nBound2));
                    if ( (Buf[idx>>6] >> (idx & 63)) & 1 )
                        Slice |= (word)1 << f;
                }
                pSlices[b1 * nB2bits + b2] = Slice;
            }
        // classify the rows (at most two classes)
        for ( b1 = 0; b1 < nB1bits && fOk; b1++ )
        {
            for ( k = 0; k < nRows; k++ )
            {
                int b1r = pRowRep[k], fSame = 1;
                for ( b2 = 0; b2 < nB2bits; b2++ )
                    if ( pSlices[b1*nB2bits + b2] != pSlices[b1r*nB2bits + b2] )
                    {
                        fSame = 0;
                        break;
                    }
                if ( fSame )
                    break;
            }
            if ( k < nRows )
                pRowKind[b1] = k;
            else if ( nRows < 2 )
            {
                pRowRep[nRows] = b1;
                pRowKind[b1] = nRows++;
            }
            else
                fOk = 0;
        }
        // classify the columns (at most two classes)
        for ( b2 = 0; b2 < nB2bits && fOk; b2++ )
        {
            for ( k = 0; k < nCols; k++ )
            {
                int b2r = pColRep[k], fSame = 1;
                for ( b1 = 0; b1 < nB1bits; b1++ )
                    if ( pSlices[b1*nB2bits + b2] != pSlices[b1*nB2bits + b2r] )
                    {
                        fSame = 0;
                        break;
                    }
                if ( fSame )
                    break;
            }
            if ( k < nCols )
                pColKind[b2] = k;
            else if ( nCols < 2 )
            {
                pColRep[nCols] = b2;
                pColKind[b2] = nCols++;
            }
            else
                fOk = 0;
        }
        if ( !fOk )
            break;
        // the class numbers must determine the slice
        for ( b1 = 0; b1 < nB1bits && fOk; b1++ )
            for ( b2 = 0; b2 < nB2bits; b2++ )
                if ( pSlices[b1*nB2bits + b2] !=
                     pSlices[pRowRep[pRowKind[b1]]*nB2bits + pColRep[pColKind[b2]]] )
                {
                    fOk = 0;
                    break;
                }
        if ( !fOk )
            break;
        // add this shared assignment to g1 and g2
        for ( b1 = 0; b1 < nB1bits; b1++ )
            if ( pRowKind[b1] )
                TruthG1 |= (word)1 << (b1 | (s << nBound1));
        for ( b2 = 0; b2 < nB2bits; b2++ )
            if ( pColKind[b2] )
                TruthG2 |= (word)1 << (b2 | (s << nBound2));
        // fill the four planes of the suffix
        for ( k = 0; k < 4; k++ )
        {
            int g1 = k & 1, g2 = (k >> 1) & 1;
            int r = (g1 < nRows) ? pRowRep[g1] : pRowRep[0];
            int c = (g2 < nCols) ? pColRep[g2] : pColRep[0];
            word Slice = pSlices[r*nB2bits + c];
            for ( f = 0; f < nFbits; f++ )
                if ( (Slice >> f) & 1 )
                    TruthH |= (word)1 << (f | (s << nFree) | (g1 << (nFree + nShared)) | (g2 << (nFree + nShared + 1)));
        }
    }
    ABC_FREE( pSlices );
    if ( !fOk )
        return 0;
    // minimize the pins
    for ( i = 0; i < nBound1 + nShared; i++ )
        pMap1[i] = i;
    for ( i = 0; i < nBound2 + nShared; i++ )
        pMap2[i] = i;
    for ( i = 0; i < nFree + nShared + 2; i++ )
        pHMap[i] = i;
    nG1 = Abc_Tt6MinBase( &TruthG1, pMap1, nBound1 + nShared );
    nG2 = Abc_Tt6MinBase( &TruthG2, pMap2, nBound2 + nShared );
    nH  = Abc_Tt6MinBase( &TruthH,  pHMap, nFree + nShared + 2 );
    if ( nG1 == 0 || nG2 == 0 || nH == 0 )
        return 0;
    pSol->Mode = 3;
    pSol->nG = nG1;
    for ( i = 0; i < nG1; i++ )
        pSol->pGLeaves[i] = pPerm[ pMap1[i] < nBound1 ? pBound1[pMap1[i]] : pShared[pMap1[i] - nBound1] ];
    pSol->TruthG = TruthG1;
    pSol->nG2 = nG2;
    for ( i = 0; i < nG2; i++ )
        pSol->pG2Leaves[i] = pPerm[ pMap2[i] < nBound2 ? pBound2[pMap2[i]] : pShared[pMap2[i] - nBound2] ];
    pSol->TruthG2 = TruthG2;
    pSol->nH = nH;
    for ( i = 0; i < nH; i++ )
    {
        if ( pHMap[i] < nFree )
            pSol->pHLeaves[i] = pPerm[ pFree[pHMap[i]] ];
        else if ( pHMap[i] < nFree + nShared )
            pSol->pHLeaves[i] = pPerm[ pShared[pHMap[i] - nFree] ];
        else if ( pHMap[i] == nFree + nShared )
            pSol->pHLeaves[i] = -1;
        else
            pSol->pHLeaves[i] = -2;
    }
    pSol->TruthH = TruthH;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Enumerates the Free subset for a given Shared subset.]

***********************************************************************/
static int Abc_LutResynTryFree( Abc_LutResynSol_t * pSol, word * pTruth, int n, int * pPerm, Vec_Ptr_t * vLeaves,
                              int nLutSize, int ReqLevel, int * pShared, int nShared, int * pAvail, int nAvail )
{
    int pFree[LUTRESYN_LEAF_MAX], pBound[LUTRESYN_LEAF_MAX], pComb[LUTRESYN_LEAF_MAX];
    int nFree, nBound, i, j, k, fIn;
    for ( nFree = 0; nFree <= nLutSize - 1 - nShared && nFree <= nAvail; nFree++ )
    {
        nBound = nAvail - nFree;
        if ( nBound <= 0 || nBound > nLutSize - nShared )
            continue;
        for ( i = 0; i < nFree; i++ )
            pComb[i] = i;
        while ( 1 )
        {
            for ( i = 0; i < nFree; i++ )
                pFree[i] = pAvail[pComb[i]];
            for ( j = 0, i = 0; i < nAvail; i++ )
            {
                for ( fIn = 0, k = 0; k < nFree; k++ )
                    if ( pAvail[i] == pFree[k] )
                    {
                        fIn = 1;
                        break;
                    }
                if ( !fIn )
                    pBound[j++] = pAvail[i];
            }
            assert( j == nBound );
            if ( Abc_LutResynTryPartition( pSol, pTruth, n, pPerm, vLeaves, ReqLevel,
                                         pFree, nFree, pBound, nBound, pShared, nShared ) )
                return 1;
            if ( nFree == 0 || !Abc_LutResynNextComb( pComb, nFree, nAvail ) )
                break;
        }
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Enumerates the Free and Bound1 subsets for the three-LUT search.]

  Description [The Bound2 set is the remainder. At most LUTRESYN_M3_TRY_MAX
  partitions are tried, so that large cones do not make the search hang.]

***********************************************************************/
static int Abc_LutResynTryFree3( Abc_LutResynSol_t * pSol, word * pTruth, int n, int * pPerm, Vec_Ptr_t * vLeaves,
                               int nLutSize, int ReqLevel, int * pShared, int nShared, int * pAvail, int nAvail, int * pnTries )
{
    int pFree[LUTRESYN_LEAF_MAX], pB1[LUTRESYN_LEAF_MAX], pB2[LUTRESYN_LEAF_MAX];
    int pCombF[LUTRESYN_LEAF_MAX], pComb1[LUTRESYN_LEAF_MAX], pRest[LUTRESYN_LEAF_MAX];
    int nFree, nB1, nB2, nRest, i, j, k, fIn;
    for ( nFree = 0; nFree <= nLutSize - 2 - nShared && nFree <= nAvail; nFree++ )
    {
        for ( nB1 = 1; nB1 <= nLutSize - nShared && nB1 <= nAvail - nFree; nB1++ )
        {
            nB2 = nAvail - nFree - nB1;
            if ( nB2 < 1 || nB2 > nLutSize - nShared )
                continue;
            for ( i = 0; i < nFree; i++ )
                pCombF[i] = i;
            while ( 1 )
            {
                for ( i = 0; i < nFree; i++ )
                    pFree[i] = pAvail[pCombF[i]];
                for ( nRest = 0, i = 0; i < nAvail; i++ )
                {
                    for ( fIn = 0, k = 0; k < nFree; k++ )
                        if ( pAvail[i] == pFree[k] )
                        {
                            fIn = 1;
                            break;
                        }
                    if ( !fIn )
                        pRest[nRest++] = pAvail[i];
                }
                assert( nRest == nB1 + nB2 );
                for ( i = 0; i < nB1; i++ )
                    pComb1[i] = i;
                while ( 1 )
                {
                    for ( i = 0; i < nB1; i++ )
                        pB1[i] = pRest[pComb1[i]];
                    for ( j = 0, i = 0; i < nRest; i++ )
                    {
                        for ( fIn = 0, k = 0; k < nB1; k++ )
                            if ( pRest[i] == pB1[k] )
                            {
                                fIn = 1;
                                break;
                            }
                        if ( !fIn )
                            pB2[j++] = pRest[i];
                    }
                    assert( j == nB2 );
                    if ( ++(*pnTries) > LUTRESYN_M3_TRY_MAX )
                        return 0;
                    if ( Abc_LutResynTryPartition3( pSol, pTruth, n, pPerm, vLeaves, ReqLevel,
                                                  pFree, nFree, pB1, nB1, pB2, nB2, pShared, nShared ) )
                        return 1;
                    if ( !Abc_LutResynNextComb( pComb1, nB1, nRest ) )
                        break;
                }
                if ( nFree == 0 || !Abc_LutResynNextComb( pCombF, nFree, nAvail ) )
                    break;
            }
        }
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Tries a chained three-LUT decomposition g -> h1 -> h2.]

  Description [The variables are split into Bound, Free1, Free2, and
  Shared. The prefix g(Bound, Shared) feeds the middle LUT h1(Free1,
  Shared, g), which feeds the root LUT h2(Free2, Shared, h1). For every
  Shared assignment, the cofactors over Bound take at most two values
  (the classes of g), and within each of them the rows over Free2 take at
  most two values (the classes of h1); a row obtained for the same h1
  class from different g classes must be identical.]

***********************************************************************/
static int Abc_LutResynTryPartition3Chain( Abc_LutResynSol_t * pSol, word * pTruth, int n, int * pPerm, Vec_Ptr_t * vLeaves, int ReqLevel,
                                         int * pFree1, int nFree1, int * pFree2, int nFree2,
                                         int * pBound, int nBound, int * pShared, int nShared )
{
    word Buf[LUTRESYN_WORD_MAX];
    word * pSlices;
    word TruthG = 0, TruthH1 = 0, TruthH2 = 0;
    word pRows[2][2], pRowDef[2];
    int pOrder[16], pMapG[16], pMapH1[16], pMapH2[16];
    int pGRep[2], pRowRep[2][2], nRowCls[2], nDefined[2];
    int nWords = Abc_TtWordNum( n );
    int nW12 = Abc_TtWordNum( nFree1 + nFree2 );
    int nF1bits = 1 << nFree1, nF2bits = 1 << nFree2;
    int nBbits = 1 << nBound, nSbits = 1 << nShared;
    int i, k, v, s, b, f1, f2, pos, idx, nG, nH1, nH2, MaxB, MaxF1, MaxF2, fOk = 1;
    assert( nFree1 + nFree2 + nBound + nShared == n );
    assert( nBound > 0 );
    assert( nBound + nShared <= 6 && nFree1 + nShared + 1 <= 6 && nFree2 + nShared + 1 <= 6 );
    // timing: h2 at ReqLevel, h1 at ReqLevel-1, g at ReqLevel-2
    MaxB = -1;
    for ( i = 0; i < nBound; i++ )
        MaxB = Abc_MaxInt( MaxB, Abc_LutResynLeafLevel( vLeaves, pPerm, pBound[i] ) );
    for ( i = 0; i < nShared; i++ )
        MaxB = Abc_MaxInt( MaxB, Abc_LutResynLeafLevel( vLeaves, pPerm, pShared[i] ) );
    MaxF1 = -1;
    for ( i = 0; i < nFree1; i++ )
        MaxF1 = Abc_MaxInt( MaxF1, Abc_LutResynLeafLevel( vLeaves, pPerm, pFree1[i] ) );
    MaxF2 = -1;
    for ( i = 0; i < nFree2; i++ )
        MaxF2 = Abc_MaxInt( MaxF2, Abc_LutResynLeafLevel( vLeaves, pPerm, pFree2[i] ) );
    if ( MaxB > ReqLevel - 3 || MaxF1 > ReqLevel - 2 || MaxF2 > ReqLevel - 1 )
        return 0;
    // reorder the truth as [Free1, Free2, Bound, Shared]
    pos = 0;
    for ( i = 0; i < nFree1; i++ )
        pOrder[pos++] = pFree1[i];
    for ( i = 0; i < nFree2; i++ )
        pOrder[pos++] = pFree2[i];
    for ( i = 0; i < nBound; i++ )
        pOrder[pos++] = pBound[i];
    for ( i = 0; i < nShared; i++ )
        pOrder[pos++] = pShared[i];
    assert( pos == n );
    Abc_TtCopy( Buf, pTruth, nWords, 0 );
    Abc_TtPermute( Buf, pOrder, n );
    pSlices = ABC_ALLOC( word, nBbits * nW12 );
    for ( s = 0; s < nSbits && fOk; s++ )
    {
        word * pSlice;
        int nCls = 0;
        // extract the slices over (Free1, Free2) for every bound assignment
        for ( b = 0; b < nBbits; b++ )
        {
            pSlice = pSlices + b * nW12;
            Abc_TtClear( pSlice, nW12 );
            for ( f2 = 0; f2 < nF2bits; f2++ )
                for ( f1 = 0; f1 < nF1bits; f1++ )
                {
                    idx = f1 | (f2 << nFree1) | (b << (nFree1 + nFree2)) | (s << (nFree1 + nFree2 + nBound));
                    if ( (Buf[idx>>6] >> (idx & 63)) & 1 )
                        pSlice[(f1 | (f2 << nFree1)) >> 6] |= (word)1 << ((f1 | (f2 << nFree1)) & 63);
                }
        }
        // classify the bound assignments: at most two classes of g
        for ( b = 0; b < nBbits && fOk; b++ )
        {
            for ( k = 0; k < nCls; k++ )
                if ( memcmp( pSlices + b*nW12, pSlices + pGRep[k]*nW12, sizeof(word)*nW12 ) == 0 )
                    break;
            if ( k < nCls )
                continue;
            if ( nCls < 2 )
                pGRep[nCls++] = b;
            else
                fOk = 0;
        }
        if ( !fOk )
            break;
        // fill the g truth for this shared assignment
        for ( b = 0; b < nBbits; b++ )
        {
            for ( k = 0; k < nCls; k++ )
                if ( memcmp( pSlices + b*nW12, pSlices + pGRep[k]*nW12, sizeof(word)*nW12 ) == 0 )
                    break;
            if ( k )
                TruthG |= (word)1 << (b | (s << nBound));
        }
        // classify the Free1 rows over Free2 and check the consistency
        for ( v = 0; v < 2; v++ )
            nDefined[v] = 0;
        for ( k = 0; k < nCls && fOk; k++ )
        {
            word * pT = pSlices + pGRep[k]*nW12;
            nRowCls[k] = 0;
            for ( f1 = 0; f1 < nF1bits && fOk; f1++ )
            {
                word Row = 0;
                for ( f2 = 0; f2 < nF2bits; f2++ )
                {
                    int i12 = f1 | (f2 << nFree1);
                    if ( (pT[i12>>6] >> (i12 & 63)) & 1 )
                        Row |= (word)1 << f2;
                }
                for ( i = 0; i < nRowCls[k]; i++ )
                    if ( Row == pRows[k][i] )
                        break;
                if ( i < nRowCls[k] )
                    continue;
                if ( nRowCls[k] < 2 )
                {
                    pRows[k][nRowCls[k]] = Row;
                    pRowRep[k][nRowCls[k]] = f1;
                    nRowCls[k]++;
                }
                else
                    fOk = 0;
            }
            if ( !fOk )
                break;
            // the same h1 class must give the same row in both g classes
            for ( v = 0; v < nRowCls[k]; v++ )
            {
                if ( !nDefined[v] )
                {
                    pRowDef[v] = pRows[k][v];
                    nDefined[v] = 1;
                }
                else if ( pRowDef[v] != pRows[k][v] )
                {
                    fOk = 0;
                    break;
                }
            }
        }
        if ( !fOk )
            break;
        // fill the h1 truth: the Free1 row class for every g class
        for ( k = 0; k < nCls; k++ )
        {
            word * pT = pSlices + pGRep[k]*nW12;
            for ( f1 = 0; f1 < nF1bits; f1++ )
            {
                word Row = 0;
                int Class = 0;
                for ( f2 = 0; f2 < nF2bits; f2++ )
                {
                    int i12 = f1 | (f2 << nFree1);
                    if ( (pT[i12>>6] >> (i12 & 63)) & 1 )
                        Row |= (word)1 << f2;
                }
                if ( nRowCls[k] == 2 && Row == pRows[k][1] )
                    Class = 1;
                if ( Class )
                    TruthH1 |= (word)1 << (f1 | (s << nFree1) | (k << (nFree1 + nShared)));
            }
        }
        // fill the h2 truth: the Free2 row selected by h1
        for ( v = 0; v < 2; v++ )
        {
            if ( !nDefined[v] )
                continue;
            for ( f2 = 0; f2 < nF2bits; f2++ )
                if ( (pRowDef[v] >> f2) & 1 )
                    TruthH2 |= (word)1 << (f2 | (s << nFree2) | (v << (nFree2 + nShared)));
        }
    }
    ABC_FREE( pSlices );
    if ( !fOk )
        return 0;
    // minimize the pins
    for ( i = 0; i < nBound + nShared; i++ )
        pMapG[i] = i;
    for ( i = 0; i < nFree1 + nShared + 1; i++ )
        pMapH1[i] = i;
    for ( i = 0; i < nFree2 + nShared + 1; i++ )
        pMapH2[i] = i;
    nG  = Abc_Tt6MinBase( &TruthG,  pMapG,  nBound + nShared );
    nH1 = Abc_Tt6MinBase( &TruthH1, pMapH1, nFree1 + nShared + 1 );
    nH2 = Abc_Tt6MinBase( &TruthH2, pMapH2, nFree2 + nShared + 1 );
    if ( nG == 0 || nH1 == 0 || nH2 == 0 )
        return 0;
    pSol->Mode = 3;
    pSol->nG = nG;
    for ( i = 0; i < nG; i++ )
        pSol->pGLeaves[i] = pPerm[ pMapG[i] < nBound ? pBound[pMapG[i]] : pShared[pMapG[i] - nBound] ];
    pSol->TruthG = TruthG;
    pSol->nG2 = nH1;
    for ( i = 0; i < nH1; i++ )
    {
        if ( pMapH1[i] < nFree1 )
            pSol->pG2Leaves[i] = pPerm[ pFree1[pMapH1[i]] ];
        else if ( pMapH1[i] < nFree1 + nShared )
            pSol->pG2Leaves[i] = pPerm[ pShared[pMapH1[i] - nFree1] ];
        else
            pSol->pG2Leaves[i] = -1;
    }
    pSol->TruthG2 = TruthH1;
    pSol->nH = nH2;
    for ( i = 0; i < nH2; i++ )
    {
        if ( pMapH2[i] < nFree2 )
            pSol->pHLeaves[i] = pPerm[ pFree2[pMapH2[i]] ];
        else if ( pMapH2[i] < nFree2 + nShared )
            pSol->pHLeaves[i] = pPerm[ pShared[pMapH2[i] - nFree2] ];
        else
            pSol->pHLeaves[i] = -2;
    }
    pSol->TruthH = TruthH2;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Enumerates the Free1 and Free2 subsets for the chained search.]

***********************************************************************/
static int Abc_LutResynTryFree3Chain( Abc_LutResynSol_t * pSol, word * pTruth, int n, int * pPerm, Vec_Ptr_t * vLeaves,
                                    int nLutSize, int ReqLevel, int * pShared, int nShared, int * pAvail, int nAvail, int * pnTries )
{
    int pFree1[LUTRESYN_LEAF_MAX], pFree2[LUTRESYN_LEAF_MAX], pBound[LUTRESYN_LEAF_MAX];
    int pComb1[LUTRESYN_LEAF_MAX], pComb2[LUTRESYN_LEAF_MAX], pRest[LUTRESYN_LEAF_MAX];
    int nFree1, nFree2, nBound, nRest, i, j, k, fIn;
    for ( nFree1 = 0; nFree1 <= nLutSize - 1 - nShared && nFree1 <= nAvail; nFree1++ )
    {
        for ( i = 0; i < nFree1; i++ )
            pComb1[i] = i;
        while ( 1 )
        {
            for ( i = 0; i < nFree1; i++ )
                pFree1[i] = pAvail[pComb1[i]];
            for ( nRest = 0, i = 0; i < nAvail; i++ )
            {
                for ( fIn = 0, k = 0; k < nFree1; k++ )
                    if ( pAvail[i] == pFree1[k] )
                    {
                        fIn = 1;
                        break;
                    }
                if ( !fIn )
                    pRest[nRest++] = pAvail[i];
            }
            for ( nFree2 = 0; nFree2 <= nLutSize - 1 - nShared && nFree2 < nRest; nFree2++ )
            {
                nBound = nRest - nFree2;
                if ( nBound < 1 || nBound > nLutSize - nShared )
                    continue;
                for ( i = 0; i < nFree2; i++ )
                    pComb2[i] = i;
                while ( 1 )
                {
                    for ( i = 0; i < nFree2; i++ )
                        pFree2[i] = pRest[pComb2[i]];
                    for ( j = 0, i = 0; i < nRest; i++ )
                    {
                        for ( fIn = 0, k = 0; k < nFree2; k++ )
                            if ( pRest[i] == pFree2[k] )
                            {
                                fIn = 1;
                                break;
                            }
                        if ( !fIn )
                            pBound[j++] = pRest[i];
                    }
                    assert( j == nBound );
                    if ( ++(*pnTries) > LUTRESYN_M3_TRY_MAX )
                        return 0;
                    if ( Abc_LutResynTryPartition3Chain( pSol, pTruth, n, pPerm, vLeaves, ReqLevel,
                                                       pFree1, nFree1, pFree2, nFree2, pBound, nBound, pShared, nShared ) )
                        return 1;
                    if ( nFree2 == 0 || !Abc_LutResynNextComb( pComb2, nFree2, nRest ) )
                        break;
                }
            }
            if ( nFree1 == 0 || !Abc_LutResynNextComb( pComb1, nFree1, nAvail ) )
                break;
        }
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Enumerates the Shared subsets for the chained search.]

***********************************************************************/
static int Abc_LutResynComposeThreeChain( Abc_LutResynSol_t * pSol, word * pTruth, int n, int * pPerm, Vec_Ptr_t * vLeaves, int nLutSize, int ReqLevel, int * pnTries )
{
    int pShared[LUTRESYN_LEAF_MAX], pAvail[LUTRESYN_LEAF_MAX], pComb[LUTRESYN_LEAF_MAX], pUsed[LUTRESYN_LEAF_MAX];
    int nShared, i, m;
    if ( nLutSize > 6 || n < 3 )
        return 0;
    for ( nShared = 0; nShared <= nLutSize - 2 && nShared <= n; nShared++ )
    {
        if ( nShared == 0 )
        {
            for ( m = 0; m < n; m++ )
                pAvail[m] = m;
            if ( Abc_LutResynTryFree3Chain( pSol, pTruth, n, pPerm, vLeaves, nLutSize, ReqLevel, pShared, 0, pAvail, n, pnTries ) )
                return 1;
            continue;
        }
        for ( i = 0; i < nShared; i++ )
            pComb[i] = i;
        while ( 1 )
        {
            for ( i = 0; i < nShared; i++ )
                pShared[i] = pComb[i];
            for ( i = 0; i < n; i++ )
                pUsed[i] = 0;
            for ( i = 0; i < nShared; i++ )
                pUsed[pShared[i]] = 1;
            for ( m = 0, i = 0; i < n; i++ )
                if ( !pUsed[i] )
                    pAvail[m++] = i;
            if ( Abc_LutResynTryFree3Chain( pSol, pTruth, n, pPerm, vLeaves, nLutSize, ReqLevel, pShared, nShared, pAvail, m, pnTries ) )
                return 1;
            if ( !Abc_LutResynNextComb( pComb, nShared, n ) )
                break;
        }
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Enumerates all four-way partitions for the three-LUT search.]

***********************************************************************/
static int Abc_LutResynComposeThree( Abc_LutResynSol_t * pSol, word * pTruth, int n, int * pPerm, Vec_Ptr_t * vLeaves, int nLutSize, int ReqLevel, int * pnTries )
{
    int pShared[LUTRESYN_LEAF_MAX], pAvail[LUTRESYN_LEAF_MAX], pComb[LUTRESYN_LEAF_MAX], pUsed[LUTRESYN_LEAF_MAX];
    int nShared, i, m;
    if ( nLutSize > 6 || n < 3 )
        return 0;
    if ( Abc_LutResynComposeThreeChain( pSol, pTruth, n, pPerm, vLeaves, nLutSize, ReqLevel, pnTries ) )
        return 1;
    for ( nShared = 0; nShared <= nLutSize - 2 && nShared <= n; nShared++ )
    {
        if ( nShared == 0 )
        {
            for ( m = 0; m < n; m++ )
                pAvail[m] = m;
            if ( Abc_LutResynTryFree3( pSol, pTruth, n, pPerm, vLeaves, nLutSize, ReqLevel, pShared, 0, pAvail, n, pnTries ) )
                return 1;
            continue;
        }
        for ( i = 0; i < nShared; i++ )
            pComb[i] = i;
        while ( 1 )
        {
            for ( i = 0; i < nShared; i++ )
                pShared[i] = pComb[i];
            for ( i = 0; i < n; i++ )
                pUsed[i] = 0;
            for ( i = 0; i < nShared; i++ )
                pUsed[pShared[i]] = 1;
            for ( m = 0, i = 0; i < n; i++ )
                if ( !pUsed[i] )
                    pAvail[m++] = i;
            if ( Abc_LutResynTryFree3( pSol, pTruth, n, pPerm, vLeaves, nLutSize, ReqLevel, pShared, nShared, pAvail, m, pnTries ) )
                return 1;
            if ( !Abc_LutResynNextComb( pComb, nShared, n ) )
                break;
        }
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Enumerates all three-way partitions for the two-LUT search.]

***********************************************************************/
static int Abc_LutResynComposeTwo( Abc_LutResynSol_t * pSol, word * pTruth, int n, int * pPerm, Vec_Ptr_t * vLeaves, int nLutSize, int ReqLevel )
{
    int pShared[LUTRESYN_LEAF_MAX], pAvail[LUTRESYN_LEAF_MAX], pComb[LUTRESYN_LEAF_MAX], pUsed[LUTRESYN_LEAF_MAX];
    int nShared, i, m;
    if ( nLutSize > 6 )
        return 0;
    for ( nShared = 0; nShared <= nLutSize - 1 && nShared <= n; nShared++ )
    {
        if ( nShared == 0 )
        {
            for ( m = 0; m < n; m++ )
                pAvail[m] = m;
            if ( Abc_LutResynTryFree( pSol, pTruth, n, pPerm, vLeaves, nLutSize, ReqLevel, pShared, 0, pAvail, n ) )
                return 1;
            continue;
        }
        for ( i = 0; i < nShared; i++ )
            pComb[i] = i;
        while ( 1 )
        {
            for ( i = 0; i < nShared; i++ )
                pShared[i] = pComb[i];
            for ( i = 0; i < n; i++ )
                pUsed[i] = 0;
            for ( i = 0; i < nShared; i++ )
                pUsed[pShared[i]] = 1;
            for ( m = 0, i = 0; i < n; i++ )
                if ( !pUsed[i] )
                    pAvail[m++] = i;
            if ( Abc_LutResynTryFree( pSol, pTruth, n, pPerm, vLeaves, nLutSize, ReqLevel, pShared, nShared, pAvail, m ) )
                return 1;
            if ( !Abc_LutResynNextComb( pComb, nShared, n ) )
                break;
        }
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Decomposes the cone truth table into one or two LUTs.]

***********************************************************************/
static int Abc_LutResynCompose( Abc_LutResynSol_t * pSol, word * pTruth, int n, Vec_Ptr_t * vLeaves, int nLutSize, int ReqLevel, int nMaxLuts )
{
    word Buf[LUTRESYN_WORD_MAX];
    int pPerm[16];
    int nWords = Abc_TtWordNum( n );
    int nEss, i, MaxLev, Lev, nTries = 0;
    pSol->Mode = 0;
    if ( n > LUTRESYN_LEAF_MAX )
        return 0;
    Abc_TtCopy( Buf, pTruth, nWords, 0 );
    for ( i = 0; i < n; i++ )
        pPerm[i] = i;
    nEss = Abc_TtMinBase( Buf, pPerm, n, n );
    if ( nEss == 0 )
        return 0;
    if ( nEss <= nLutSize )
    {
        MaxLev = -1;
        for ( i = 0; i < nEss; i++ )
        {
            Lev = Abc_LutResynLeafLevel( vLeaves, pPerm, i );
            MaxLev = Abc_MaxInt( MaxLev, Lev );
        }
        if ( MaxLev + 1 > ReqLevel )
            return 0;
        pSol->Mode = 1;
        pSol->nLeaves = nEss;
        for ( i = 0; i < nEss; i++ )
            pSol->pLeaves[i] = pPerm[i];
        Abc_TtCopy( pSol->Truth1, Buf, Abc_TtWordNum(nEss), 0 );
        return 1;
    }
    if ( nMaxLuts >= 2 && Abc_LutResynComposeTwo( pSol, Buf, nEss, pPerm, vLeaves, nLutSize, ReqLevel ) )
        return 1;
    if ( nMaxLuts >= 3 && Abc_LutResynComposeThree( pSol, Buf, nEss, pPerm, vLeaves, nLutSize, ReqLevel, &nTries ) )
        return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Rewrites the cone to the decomposition found.]

***********************************************************************/
static void Abc_LutResynCommit( Abc_Ntk_t * pNtk, Abc_Obj_t * pRoot, Vec_Ptr_t * vCone, Vec_Ptr_t * vLeaves, Abc_LutResynSol_t * pSol, Vec_Vec_t * vLevels )
{
    Hop_Man_t * pMan = (Hop_Man_t *)pNtk->pManFunc;
    unsigned KitTruth[2 * LUTRESYN_WORD_MAX];
    Abc_Obj_t * pObj, * pBound = NULL, * pBound2 = NULL;
    int i, k;
    if ( pSol->Mode == 1 )
    {
        Abc_ObjRemoveFanins( pRoot );
        for ( i = 0; i < pSol->nLeaves; i++ )
            Abc_ObjAddFanin( pRoot, (Abc_Obj_t *)Vec_PtrEntry(vLeaves, pSol->pLeaves[i]) );
        Abc_LutResynToKit( pSol->Truth1, pSol->nLeaves, KitTruth );
        pRoot->pData = Kit_TruthToHop( pMan, KitTruth, pSol->nLeaves, NULL );
    }
    else
    {
        pBound = Abc_NtkCreateNode( pNtk );
        for ( i = 0; i < pSol->nG; i++ )
            Abc_ObjAddFanin( pBound, (Abc_Obj_t *)Vec_PtrEntry(vLeaves, pSol->pGLeaves[i]) );
        Abc_ObjSetLevel( pBound, Abc_ObjLevelNew(pBound) );
        Abc_LutResynToKit( &pSol->TruthG, pSol->nG, KitTruth );
        pBound->pData = Kit_TruthToHop( pMan, KitTruth, pSol->nG, NULL );
        if ( pSol->Mode == 3 )
        {
            pBound2 = Abc_NtkCreateNode( pNtk );
            for ( i = 0; i < pSol->nG2; i++ )
                Abc_ObjAddFanin( pBound2, pSol->pG2Leaves[i] == -1 ? pBound : (Abc_Obj_t *)Vec_PtrEntry(vLeaves, pSol->pG2Leaves[i]) );
            Abc_ObjSetLevel( pBound2, Abc_ObjLevelNew(pBound2) );
            Abc_LutResynToKit( &pSol->TruthG2, pSol->nG2, KitTruth );
            pBound2->pData = Kit_TruthToHop( pMan, KitTruth, pSol->nG2, NULL );
        }

        Abc_ObjRemoveFanins( pRoot );
        for ( i = 0; i < pSol->nH; i++ )
            Abc_ObjAddFanin( pRoot, pSol->pHLeaves[i] == -1 ? pBound :
                                   ( pSol->pHLeaves[i] == -2 ? pBound2 : (Abc_Obj_t *)Vec_PtrEntry(vLeaves, pSol->pHLeaves[i]) ) );
        Abc_LutResynToKit( &pSol->TruthH, pSol->nH, KitTruth );
        pRoot->pData = Kit_TruthToHop( pMan, KitTruth, pSol->nH, NULL );
    }
    // delete the cone nodes that lost all their fanouts
    for ( ;; )
    {
        int fProgress = 0;
        for ( k = 1; k < Vec_PtrSize(vCone); k++ )
        {
            pObj = (Abc_Obj_t *)Vec_PtrEntry( vCone, k );
            if ( pObj == NULL || Abc_ObjFanoutNum(pObj) > 0 )
                continue;
            Abc_NtkDeleteObj( pObj );
            Vec_PtrWriteEntry( vCone, k, NULL );
            fProgress = 1;
        }
        if ( !fProgress )
            break;
    }
    // update the forward levels
    Abc_NtkUpdateLevel( pRoot, vLevels );
    // update the reverse levels
    if ( pBound )
        Abc_NtkUpdateReverseLevel( pBound, vLevels );
    if ( pBound2 )
        Abc_NtkUpdateReverseLevel( pBound2, vLevels );
    // remove the leaves that became dangling
    for ( i = 0; i < Vec_PtrSize(vLeaves); i++ )
    {
        pObj = (Abc_Obj_t *)Vec_PtrEntry( vLeaves, i );
        if ( Abc_ObjIsNode(pObj) && Abc_ObjFanoutNum(pObj) == 0 )
            Abc_NtkDeleteObj_rec( pObj, 1 );
    }
}

/**Function*************************************************************

  Synopsis    [Counts the absorbed nodes with fanouts outside the cone.]

***********************************************************************/
static int Abc_LutResynConeExtNum( Vec_Ptr_t * vCone )
{
    int i, nExt = 0;
    for ( i = 1; i < Vec_PtrSize(vCone); i++ )
        nExt += Abc_LutResynLeafOutside( vCone, (Abc_Obj_t *)Vec_PtrEntry(vCone, i) ) > 0;
    return nExt;
}

/**Function*************************************************************

  Synopsis    [Marks the cone nodes that stay in the network.]

  Description [A cone node stays when it has a fanout outside the cone
  or when one of its fanouts stays. The root is rewired, so it never
  keeps its old fanins alive and is not marked.]

***********************************************************************/
static void Abc_LutResynConeAliveFlags( Vec_Ptr_t * vCone, int * pAlive )
{
    int nCone = Vec_PtrSize( vCone );
    int i, k, iFanout, fChange;
    for ( i = 0; i < nCone; i++ )
    {
        Abc_Obj_t * pObj = (Abc_Obj_t *)Vec_PtrEntry( vCone, i );
        pAlive[i] = 0;
        for ( k = 0; k < Abc_ObjFanoutNum(pObj); k++ )
            if ( Vec_PtrFind( vCone, Abc_ObjFanout(pObj, k) ) == -1 )
            {
                pAlive[i] = 1;
                break;
            }
    }
    pAlive[0] = 0;
    do {
        fChange = 0;
        for ( i = 1; i < nCone; i++ )
        {
            Abc_Obj_t * pObj = (Abc_Obj_t *)Vec_PtrEntry( vCone, i );
            if ( pAlive[i] )
                continue;
            for ( k = 0; k < Abc_ObjFanoutNum(pObj); k++ )
            {
                iFanout = Vec_PtrFind( vCone, Abc_ObjFanout(pObj, k) );
                if ( iFanout >= 0 && pAlive[iFanout] )
                {
                    pAlive[i] = 1;
                    fChange = 1;
                    break;
                }
            }
        }
    } while ( fChange );
}

/**Function*************************************************************

  Synopsis    [Tries to reduce the cone rooted at pRoot.]

  Description [Returns 1 if the network was changed and the number of
  removed nodes is added to pnSaved together with the area gain.]

***********************************************************************/
static int Abc_LutResynTryCone( Abc_Ntk_t * pNtk, Abc_Obj_t * pRoot, Vec_Ptr_t * vCone, Vec_Ptr_t * vLeaves, int nLutSize, int nMaxLuts, If_LibLut_t * pLutLib, Vec_Vec_t * vLevels, int * pnSaved, float * pfGain, int * pModeCnt )
{
    Abc_LutResynSol_t Sol;
    word * pStore, * pCube, ConeTruth[LUTRESYN_WORD_MAX];
    int pAlive[LUTRESYN_CONE_MAX];
    int n, nCone, nDead, nWords, i, fOk;
    int nNodesBefore, ReqLevel;
    float OldArea = 0.0, NewArea = 0.0;

    nCone = Vec_PtrSize( vCone );
    n = Vec_PtrSize( vLeaves );
    if ( nCone < 2 || n == 0 || n > LUTRESYN_LEAF_MAX )
        return 0;
    nWords = Abc_TtWordNum( n );
    pStore = ABC_ALLOC( word, (n + nCone) * nWords );
    pCube = ABC_ALLOC( word, nWords );
    fOk = Abc_LutResynTruthCone( pNtk, vCone, vLeaves, pStore, pCube, ConeTruth );
    ABC_FREE( pStore );
    ABC_FREE( pCube );
    if ( !fOk )
        return 0;
    ReqLevel = Abc_ObjRequiredLevel( pRoot );
    if ( !Abc_LutResynCompose( &Sol, ConeTruth, n, vLeaves, nLutSize, ReqLevel, nMaxLuts ) )
        return 0;
    Abc_LutResynConeAliveFlags( vCone, pAlive );
    nDead = 1;
    for ( i = 1; i < nCone; i++ )
        nDead += !pAlive[i];
    // a three-LUT rewrite must save at least two LUTs to be worth the perturbation
    if ( Sol.Mode == 3 && nDead - Sol.Mode < 2 )
        return 0;
    // without a LUT library, the only gain is a smaller LUT count
    if ( pLutLib == NULL && nDead <= Sol.Mode )
        return 0;
    if ( pLutLib )
    {
        for ( i = 0; i < nCone; i++ )
        {
            Abc_Obj_t * pObj = (Abc_Obj_t *)Vec_PtrEntry( vCone, i );
            if ( Abc_ObjFaninNum(pObj) > pLutLib->LutMax )
                return 0;
            if ( i == 0 || !pAlive[i] )
                OldArea += pLutLib->pLutAreas[Abc_ObjFaninNum(pObj)];
        }
        if ( Sol.Mode == 1 )
            NewArea = pLutLib->pLutAreas[Sol.nLeaves];
        else if ( Sol.Mode == 2 )
            NewArea = pLutLib->pLutAreas[Sol.nG] + pLutLib->pLutAreas[Sol.nH];
        else
            NewArea = pLutLib->pLutAreas[Sol.nG] + pLutLib->pLutAreas[Sol.nG2] + pLutLib->pLutAreas[Sol.nH];
        if ( OldArea <= NewArea + 1e-6 )
            return 0;
    }
    pModeCnt[Sol.Mode]++;
    nNodesBefore = Abc_NtkNodeNum( pNtk );
    Abc_LutResynCommit( pNtk, pRoot, vCone, vLeaves, &Sol, vLevels );
    *pnSaved = nNodesBefore - Abc_NtkNodeNum( pNtk );
    *pfGain = OldArea - NewArea;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Tries the greedy cone and the DFS candidates.]

  Description [Tries the greedy cone collected with the given budget,
  then a bounded number of alternative cones collected by the bounded
  DFS. A pipeline with nMaxExt > 0 is skipped when the greedy cone did
  not absorb a node with outside fanouts, because then it repeats the
  plain pipeline.]

***********************************************************************/
static int Abc_LutResynTryPipeline( Abc_Ntk_t * pNtk, Abc_Obj_t * pRoot, int nLutSize, int nMaxLuts, int nMaxExt, If_LibLut_t * pLutLib, Vec_Vec_t * vLevels, int * pnSaved, float * pfGain, int * pModeCnt, int * pnCutsTried, int * pnCutsUsed )
{
    Vec_Ptr_t * vCone = Vec_PtrAlloc( LUTRESYN_CONE_MAX );
    Vec_Ptr_t * vLeaves = Vec_PtrAlloc( LUTRESYN_LEAF_MAX );
    Abc_LutResynCone_t Cands[LUTRESYN_CUT_CAND_MAX];
    int nCands, i, k, nTried = 0, fOk = 0;
    if ( Abc_LutResynCollectCone( pRoot, nLutSize, nMaxExt, vCone, vLeaves ) &&
         ( nMaxExt == 0 || Abc_LutResynConeExtNum(vCone) > 0 ) &&
         Abc_LutResynTryCone( pNtk, pRoot, vCone, vLeaves, nLutSize, nMaxLuts, pLutLib, vLevels, pnSaved, pfGain, pModeCnt ) )
    {
        fOk = 1;
        goto cleanup;
    }
    nCands = Abc_LutResynCollectCuts( pRoot, nLutSize, nMaxExt, Cands );
    qsort( Cands, nCands, sizeof(Abc_LutResynCone_t), Abc_LutResynConeCompare );
    // keep only the largest cone for every leaf set
    for ( i = 0; i < nCands; i++ )
    {
        for ( k = 0; k < i; k++ )
            if ( Cands[k].vCone && Abc_LutResynConeSameLeaves( &Cands[i], &Cands[k] ) )
                break;
        if ( k < i )
        {
            Vec_PtrFree( Cands[i].vCone );
            Vec_PtrFree( Cands[i].vLeaves );
            Cands[i].vCone = NULL;
        }
    }
    for ( i = 0; i < nCands && nTried < LUTRESYN_CUT_TRY_MAX; i++ )
    {
        if ( Cands[i].vCone == NULL )
            continue;
        nTried++;
        if ( Abc_LutResynTryCone( pNtk, pRoot, Cands[i].vCone, Cands[i].vLeaves, nLutSize, nMaxLuts, pLutLib, vLevels, pnSaved, pfGain, pModeCnt ) )
        {
            fOk = 1;
            (*pnCutsUsed)++;
            break;
        }
    }
    *pnCutsTried += nTried;
    for ( i = 0; i < nCands; i++ )
        if ( Cands[i].vCone )
        {
            Vec_PtrFree( Cands[i].vCone );
            Vec_PtrFree( Cands[i].vLeaves );
        }
cleanup:
    Vec_PtrFree( vCone );
    Vec_PtrFree( vLeaves );
    return fOk;
}

/**Function*************************************************************

  Synopsis    [Tries to reduce the cone rooted at pRoot.]

  Description [Runs the plain pipeline first and repeats it with the
  outside-fanout budget only when the plain one fails, so the outside
  nodes never preempt a rewrite that the plain pipeline would accept.
  Returns 1 if the network was changed and the number of removed nodes
  is added to pnSaved with the area gain.]

***********************************************************************/
static int Abc_LutResynTryRoot( Abc_Ntk_t * pNtk, Abc_Obj_t * pRoot, int nLutSize, int nMaxLuts, int nMaxExt, If_LibLut_t * pLutLib, Vec_Vec_t * vLevels, int * pnSaved, float * pfGain, int * pModeCnt, int * pnCutsTried, int * pnCutsUsed )
{
    *pnSaved = 0;
    *pfGain = 0.0;
    if ( Abc_LutResynTryPipeline( pNtk, pRoot, nLutSize, nMaxLuts, 0, pLutLib, vLevels, pnSaved, pfGain, pModeCnt, pnCutsTried, pnCutsUsed ) )
        return 1;
    if ( nMaxExt > 0 && Abc_LutResynTryPipeline( pNtk, pRoot, nLutSize, nMaxLuts, nMaxExt, pLutLib, vLevels, pnSaved, pfGain, pModeCnt, pnCutsTried, pnCutsUsed ) )
        return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Reduces the LUT count by remapping fanout-free cones.]

  Description [Runs nRounds passes over the network in the reverse
  topological order. The timing is protected by the required levels,
  which allow LUTs to grow by at most nGrowthLevel levels. Up to
  nMaxExtLuts nodes with fanouts outside the cone can be absorbed into
  the cone; they stay in the network for their other fanouts. If a LUT
  library is given, the replacement must strictly reduce the total LUT
  area. Returns the number of removed nodes.]

***********************************************************************/
int Abc_NtkLutResyn( Abc_Ntk_t * pNtk, int nLutSize, int nRounds, int nGrowthLevel, int nMaxLuts, int nMaxExtLuts, int fVerbose, If_LibLut_t * pLutLib, float * pfAreaGain )
{
    Vec_Ptr_t * vNodes = NULL;
    Vec_Int_t * vIds;
    Vec_Vec_t * vLevels;
    Abc_Obj_t * pRoot;
    int i, r, nSaved, nRoundSaved, nTotal = 0;
    int nLevelMax, nCutsTried, nCutsUsed;
    int ModeCnt[4];
    float Gain, GainRound, GainTotal = 0.0;

    if ( pfAreaGain )
        *pfAreaGain = 0.0;
    assert( Abc_NtkIsLogic(pNtk) && Abc_NtkHasAig(pNtk) );
    vLevels = Vec_VecAlloc( 1000 );
    nLevelMax = Abc_NtkLevel( pNtk ) + nGrowthLevel;
    for ( r = 0; r < nRounds; r++ )
    {
        Abc_NtkStartReverseLevels( pNtk, nLevelMax - Abc_NtkLevel(pNtk) );
        vNodes = Abc_NtkDfsReverse( pNtk );
        vIds = Vec_IntAlloc( Vec_PtrSize(vNodes) );
        Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pRoot, i )
            Vec_IntPush( vIds, Abc_ObjId(pRoot) );
        Vec_PtrFree( vNodes );
        vNodes = NULL;

        nRoundSaved = 0;
        GainRound = 0.0;
        nCutsTried = nCutsUsed = 0;
        ModeCnt[0] = ModeCnt[1] = ModeCnt[2] = ModeCnt[3] = 0;
        for ( i = 0; i < Vec_IntSize(vIds); i++ )
        {
            pRoot = Abc_NtkObj( pNtk, Vec_IntEntry(vIds, i) );
            if ( pRoot == NULL || !Abc_ObjIsNode(pRoot) || pRoot->pData == NULL )
                continue;
            if ( Abc_ObjFaninNum(pRoot) < 2 )
                continue;
            if ( Abc_LutResynTryRoot( pNtk, pRoot, nLutSize, nMaxLuts, nMaxExtLuts, pLutLib, vLevels, &nSaved, &Gain, ModeCnt, &nCutsTried, &nCutsUsed ) )
            {
                nRoundSaved += nSaved;
                GainRound += Gain;
            }
        }
        Vec_IntFree( vIds );
        Abc_NtkStopReverseLevels( pNtk );
        if ( fVerbose )
        {
            if ( pLutLib )
                Abc_Print( 1, "Round %d: removed %d nodes, area gain %.2f (cones 1:%d 2:%d 3:%d).\n",
                    r + 1, nRoundSaved, GainRound, ModeCnt[1], ModeCnt[2], ModeCnt[3] );
            else
                Abc_Print( 1, "Round %d: removed %d nodes (cones 1:%d 2:%d 3:%d).\n",
                    r + 1, nRoundSaved, ModeCnt[1], ModeCnt[2], ModeCnt[3] );
            if ( nCutsTried )
                Abc_Print( 1, "    Extra cuts tried %d, accepted %d.\n", nCutsTried, nCutsUsed );
        }
        nTotal += nRoundSaved;
        GainTotal += GainRound;
        if ( nRoundSaved == 0 )
            break;
    }
    Vec_VecFree( vLevels );
    if ( pfAreaGain )
        *pfAreaGain = GainTotal;
    return nTotal;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END