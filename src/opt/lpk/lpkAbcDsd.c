/**CFile****************************************************************

  FileName    [lpkAbcDsd.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Fast Boolean matching for LUT structures.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: lpkAbcDsd.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "lpkInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns the variable whose cofs have min sum of supp sizes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Lpk_FunComputeMinSuppSizeVar( Lpk_Fun_t * p, unsigned ** ppTruths, int nTruths, unsigned ** ppCofs )
{
    int i, Var, VarBest, nSuppSize0, nSuppSize1, nSuppTotalMin, nSuppTotalCur, nSuppMaxMin, nSuppMaxCur;
    VarBest = -1;
    Lpk_SuppForEachVar( p->uSupp, Var )
    {
        nSuppMaxCur = 0;
        nSuppTotalCur = 0;
        for ( i = 0; i < nTruths; i++ )
        {
            Kit_TruthCofactor0New( ppCofs[2*i+0], ppTruths[i], p->nVars, Var );
            Kit_TruthCofactor1New( ppCofs[2*i+1], ppTruths[i], p->nVars, Var );
            nSuppSize0 = Kit_TruthSupportSize( ppCofs[2*i+0], p->nVars );
            nSuppSize1 = Kit_TruthSupportSize( ppCofs[2*i+1], p->nVars );
            nSuppMaxCur = ABC_MAX( nSuppMaxCur, nSuppSize0 );
            nSuppMaxCur = ABC_MAX( nSuppMaxCur, nSuppSize1 );
            nSuppTotalCur += nSuppSize0 + nSuppSize1;
        }
        if ( VarBest == -1 || nSuppTotalMin > nSuppTotalCur ||
             (nSuppTotalMin == nSuppTotalCur && nSuppMaxMin > nSuppMaxCur) )
        {
            VarBest = Var;
            nSuppMaxMin = nSuppMaxCur;
            nSuppTotalMin = nSuppTotalCur;
        }
    }
    // recompute cofactors for the best var
    for ( i = 0; i < nTruths; i++ )
    {
        Kit_TruthCofactor0New( ppCofs[2*i+0], ppTruths[i], p->nVars, VarBest );
        Kit_TruthCofactor1New( ppCofs[2*i+1], ppTruths[i], p->nVars, VarBest );
    }
    return VarBest;
}

/**Function*************************************************************

  Synopsis    [Recursively computes decomposable subsets.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned Lpk_ComputeBoundSets_rec( Kit_DsdNtk_t * p, int iLit, Vec_Int_t * vSets )
{
    unsigned i, iLitFanin, uSupport, uSuppCur;
    Kit_DsdObj_t * pObj;
    // consider the case of simple gate
    pObj = Kit_DsdNtkObj( p, Kit_DsdLit2Var(iLit) );
    if ( pObj == NULL )
        return (1 << Kit_DsdLit2Var(iLit));
    if ( pObj->Type == KIT_DSD_AND || pObj->Type == KIT_DSD_XOR )
    {
        unsigned uSupps[16], Limit, s;
        uSupport = 0;
        Kit_DsdObjForEachFanin( p, pObj, iLitFanin, i )
        {
            uSupps[i] = Lpk_ComputeBoundSets_rec( p, iLitFanin, vSets );
            uSupport |= uSupps[i];
        }
        // create all subsets, except empty and full
        Limit = (1 << pObj->nFans) - 1;
        for ( s = 1; s < Limit; s++ )
        {
            uSuppCur = 0;
            for ( i = 0; i < pObj->nFans; i++ )
                if ( s & (1 << i) )
                    uSuppCur |= uSupps[i];
            Vec_IntPush( vSets, uSuppCur );
        }
        return uSupport;
    }
    assert( pObj->Type == KIT_DSD_PRIME );
    // get the cumulative support of all fanins
    uSupport = 0;
    Kit_DsdObjForEachFanin( p, pObj, iLitFanin, i )
    {
        uSuppCur  = Lpk_ComputeBoundSets_rec( p, iLitFanin, vSets );
        uSupport |= uSuppCur;
        Vec_IntPush( vSets, uSuppCur );
    }
    return uSupport;
}

/**Function*************************************************************

  Synopsis    [Computes the set of subsets of decomposable variables.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Lpk_ComputeBoundSets( Kit_DsdNtk_t * p, int nSizeMax )
{
    Vec_Int_t * vSets;
    unsigned uSupport, Entry;
    int Number, i;
    assert( p->nVars <= 16 );
    vSets = Vec_IntAlloc( 100 );
    Vec_IntPush( vSets, 0 );
    if ( Kit_DsdNtkRoot(p)->Type == KIT_DSD_CONST1 )
        return vSets;
    if ( Kit_DsdNtkRoot(p)->Type == KIT_DSD_VAR )
    {
        uSupport = ( 1 << Kit_DsdLit2Var(Kit_DsdNtkRoot(p)->pFans[0]) );
        Vec_IntPush( vSets, uSupport );
        return vSets;
    }
    uSupport = Lpk_ComputeBoundSets_rec( p, p->Root, vSets );
    assert( (uSupport & 0xFFFF0000) == 0 );
    Vec_IntPush( vSets, uSupport );
    // set the remaining variables
    Vec_IntForEachEntry( vSets, Number, i )
    {
        Entry = Number;
        Vec_IntWriteEntry( vSets, i, Entry | ((uSupport & ~Entry) << 16) );
    }
    return vSets;
}

/**Function*************************************************************

  Synopsis    [Merges two bound sets.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Lpk_MergeBoundSets( Vec_Int_t * vSets0, Vec_Int_t * vSets1 )
{
    Vec_Int_t * vSets;
    int Entry0, Entry1, Entry;
    int i, k;
    vSets = Vec_IntAlloc( 100 );
    Vec_IntForEachEntry( vSets0, Entry0, i )
    Vec_IntForEachEntry( vSets1, Entry1, k )
    {
        Entry = Entry0 | Entry1;
        if ( (Entry & (Entry >> 16)) )
            continue;
        Vec_IntPush( vSets, Entry );
    }
    return vSets;
}

/**Function*************************************************************

  Synopsis    [Allocates truth tables for cofactors.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Lpk_FunAllocTruthTables( Lpk_Fun_t * p, int nCofDepth, unsigned * ppTruths[5][16] )
{
    int i;
    assert( nCofDepth <= 4 );
    ppTruths[0][0] = Lpk_FunTruth( p, 0 );
    if ( nCofDepth >= 1 )
    {
        ppTruths[1][0] = Lpk_FunTruth( p, 1 );
        ppTruths[1][1] = Lpk_FunTruth( p, 2 );
    }
    if ( nCofDepth >= 2 )
    {
        ppTruths[2][0] = ALLOC( unsigned, Kit_TruthWordNum(p->nVars) * 4 );
        for ( i = 1; i < 4; i++ )
            ppTruths[2][i] = ppTruths[2][0] + Kit_TruthWordNum(p->nVars) * i;
    }
    if ( nCofDepth >= 3 )
    {
        ppTruths[3][0] = ALLOC( unsigned, Kit_TruthWordNum(p->nVars) * 8 );
        for ( i = 1; i < 8; i++ )
            ppTruths[3][i] = ppTruths[3][0] + Kit_TruthWordNum(p->nVars) * i;
    }
    if ( nCofDepth >= 4 )
    {
        ppTruths[4][0] = ALLOC( unsigned, Kit_TruthWordNum(p->nVars) * 16 );
        for ( i = 1; i < 16; i++ )
            ppTruths[4][i] = ppTruths[4][0] + Kit_TruthWordNum(p->nVars) * i;
    }
}

/**Function*************************************************************

  Synopsis    [Allocates truth tables for cofactors.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Lpk_FunFreeTruthTables( Lpk_Fun_t * p, int nCofDepth, unsigned * ppTruths[5][16] )
{
    if ( nCofDepth >= 2 )
        free( ppTruths[2][0] );
    if ( nCofDepth >= 3 )
        free( ppTruths[3][0] );
    if ( nCofDepth >= 4 )
        free( ppTruths[4][0] );
}

/**Function*************************************************************

  Synopsis    [Performs DSD-based decomposition of the function.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Lpk_Res_t * Lpk_FunAnalizeDsd( Lpk_Fun_t * p, int nCofDepth )
{
    static Lpk_Res_t Res, * pRes = &Res;
    unsigned * ppTruths[5][16];
    Vec_Int_t * pvBSets[4][8];
    Kit_DsdNtk_t * pNtkDec, * pTemp;
    unsigned uBoundSet;
    int i, k, nVarsBS, nVarsRem, Delay, Area;
    Lpk_FunAllocTruthTables( p, nCofDepth, ppTruths );
    // find the best cofactors
    memset( pRes, 0, sizeof(Lpk_Res_t) );
    pRes->nCofVars = nCofDepth;
    for ( i = 0; i < nCofDepth; i++ )
        pRes->pCofVars[i] = Lpk_FunComputeMinSuppSizeVar( p, ppTruths[i], 1<<i, ppTruths[i+1] );
    // derive decomposed networks
    for ( i = 0; i < (1<<nCofDepth); i++ )
    {
        pNtkDec = Kit_DsdDecompose( ppTruths[nCofDepth][i], p->nVars );
        pNtkDec = Kit_DsdExpand( pTemp = pNtkDec );      Kit_DsdNtkFree( pTemp );
        pvBSets[nCofDepth][i] = Lpk_ComputeBoundSets( pNtkDec, p->nLutK - nCofDepth );
        Kit_DsdNtkFree( pNtkDec );
    }
    // derive the set of feasible boundsets
    for ( i = nCofDepth - 1; i >= 0; i-- )
        for ( k = 0; k < (1<<i); k++ )
            pvBSets[i][k] = Lpk_MergeBoundSets( pvBSets[i+1][2*k+0], pvBSets[i+1][2*k+1] );
    // compare the resulting boundsets
    Vec_IntForEachEntry( pvBSets[0][0], uBoundSet, i )
    {
        if ( uBoundSet == 0 )
            continue;
        assert( (uBoundSet & (uBoundSet >> 16)) == 0 );
        nVarsBS = Kit_WordCountOnes( uBoundSet & 0xFFFF );
        nVarsRem = p->nVars - nVarsBS + nCofDepth + 1;
        Delay = 1 + Lpk_SuppDelay( uBoundSet & 0xFFFF, p->pDelays );
        Area = 1 + Lpk_LutNumLuts( nVarsRem, p->nLutK );
        if ( Delay > (int)p->nDelayLim || Area > (int)p->nAreaLim )
            continue;
        if ( uBoundSet == 0 || pRes->DelayEst > Delay || pRes->DelayEst == Delay && pRes->nSuppSizeL > nVarsRem )
        {
            pRes->nBSVars = nVarsBS;
            pRes->BSVars = uBoundSet;
            pRes->nSuppSizeS = nVarsBS;
            pRes->nSuppSizeL = nVarsRem;
            pRes->DelayEst = Delay;
            pRes->AreaEst = Area;
        }
    }
    // free cofactor storage
    Lpk_FunFreeTruthTables( p, nCofDepth, ppTruths );
    return pRes;
}

/**Function*************************************************************

  Synopsis    [Splits the function into two subfunctions using DSD.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Lpk_Fun_t * Lpk_FunSplitDsd( Lpk_Fun_t * p, char * pCofVars, int nCofVars, unsigned uBoundSet )
{
    Kit_DsdMan_t * pDsdMan;
    Kit_DsdNtk_t * pNtkDec, * pTemp;
    unsigned * pTruth  = Lpk_FunTruth( p, 0 );
    unsigned * pTruth0 = Lpk_FunTruth( p, 1 );
    unsigned * pTruth1 = Lpk_FunTruth( p, 2 );
    Lpk_Fun_t * pNew;
    unsigned * ppTruths[5][16];
    char pBSVars[5];
    int i, k, nVars, nCofs;
    // get the bound set variables
    nVars = Lpk_SuppToVars( uBoundSet, pBSVars );
    // compute the cofactors
    Lpk_FunAllocTruthTables( p, nCofVars, ppTruths );
    for ( i = 0; i < nCofVars; i++ )
        for ( k = 0; k < (1<<i); k++ )
        {
            Kit_TruthCofactor0New( ppTruths[i+1][2*k+0], ppTruths[i][k], p->nVars, pCofVars[i] );
            Kit_TruthCofactor1New( ppTruths[i+1][2*k+1], ppTruths[i][k], p->nVars, pCofVars[i] );
        }
    // decompose each cofactor w.r.t. the bound set
    nCofs = (1<<nCofVars);
    pDsdMan = Kit_DsdManAlloc( p->nVars, p->nVars * 4 );
    for ( k = 0; k < nCofs; k++ )
    {
        pNtkDec = Kit_DsdDecompose( ppTruths[nCofVars][k], p->nVars );
        pNtkDec = Kit_DsdExpand( pTemp = pNtkDec );      Kit_DsdNtkFree( pTemp );
        Kit_DsdTruthPartialTwo( pDsdMan, pNtkDec, uBoundSet, pBSVars[0], ppTruths[nCofVars+1][k], ppTruths[nCofVars+1][nCofs+k] );
        Kit_DsdNtkFree( pNtkDec );
    }
    Kit_DsdManFree( pDsdMan );
    // compute the composition function
    for ( i = nCofVars - 1; i >= 1; i-- )
        for ( k = 0; k < (1<<i); k++ )
            Kit_TruthMuxVar( ppTruths[i][k], ppTruths[i+1][2*k+0], ppTruths[i+1][2*k+1], nVars, pCofVars[i] );
    // now the composition/decomposition functions are in pTruth0/pTruth1

    // derive the new component
    pNew = Lpk_FunDup( p, pTruth1 );
    // update the old component
    Kit_TruthCopy( pTruth, pTruth0, p->nVars );
    p->uSupp = Kit_TruthSupport( pTruth0, p->nVars );
    p->pFanins[pBSVars[0]] = pNew->Id;
    p->pDelays[pBSVars[0]] = Lpk_SuppDelay( pNew->uSupp, pNew->pDelays );
    // support minimize both
    Lpk_FunSuppMinimize( p );
    Lpk_FunSuppMinimize( pNew );
    // update delay and area requirements
    pNew->nDelayLim = p->nDelayLim - 1;
    pNew->nAreaLim = 1;
    p->nAreaLim = p->nAreaLim - 1;

    // free cofactor storage
    Lpk_FunFreeTruthTables( p, nCofVars, ppTruths );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


