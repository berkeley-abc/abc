/**CFile****************************************************************

  FileName    [lpkAbcDsd.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Fast Boolean matching for LUT structures.]

  Synopsis    [LUT-decomposition based on recursive DSD.]

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

  Synopsis    [Cofactors TTs w.r.t. all vars and finds the best var.]

  Description [The best variable is the variable with the minimum 
  sum total of the support sizes of all truth tables. This procedure 
  computes and returns cofactors w.r.t. the best variable.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Lpk_FunComputeMinSuppSizeVar( Lpk_Fun_t * p, unsigned ** ppTruths, int nTruths, unsigned ** ppCofs )
{
    int i, Var, VarBest, nSuppSize0, nSuppSize1, nSuppTotalMin, nSuppTotalCur, nSuppMaxMin, nSuppMaxCur;
    assert( nTruths > 0 );
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
unsigned Lpk_ComputeBoundSets_rec( Kit_DsdNtk_t * p, int iLit, Vec_Int_t * vSets, int nSizeMax )
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
            uSupps[i] = Lpk_ComputeBoundSets_rec( p, iLitFanin, vSets, nSizeMax );
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
            if ( Kit_WordCountOnes(uSuppCur) <= nSizeMax )
                Vec_IntPush( vSets, uSuppCur );
        }
        return uSupport;
    }
    assert( pObj->Type == KIT_DSD_PRIME );
    // get the cumulative support of all fanins
    uSupport = 0;
    Kit_DsdObjForEachFanin( p, pObj, iLitFanin, i )
    {
        uSuppCur  = Lpk_ComputeBoundSets_rec( p, iLitFanin, vSets, nSizeMax );
        uSupport |= uSuppCur;
        if ( Kit_WordCountOnes(uSuppCur) <= nSizeMax )
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
        if ( Kit_WordCountOnes(uSupport) <= nSizeMax )
            Vec_IntPush( vSets, uSupport );
        return vSets;
    }
    uSupport = Lpk_ComputeBoundSets_rec( p, p->Root, vSets, nSizeMax );
    assert( (uSupport & 0xFFFF0000) == 0 );
    // add the total support of the network
    if ( Kit_WordCountOnes(uSupport) <= nSizeMax )
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
Vec_Int_t * Lpk_MergeBoundSets( Vec_Int_t * vSets0, Vec_Int_t * vSets1, int nSizeMax )
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
        if ( Kit_WordCountOnes(Entry) <= nSizeMax )
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
void Lpk_DsdAnalizeOne( Lpk_Fun_t * p, int nCofDepth, Lpk_Res_t * pRes )
{
    unsigned * ppTruths[5][16];
    Vec_Int_t * pvBSets[4][8];
    Kit_DsdNtk_t * pNtkDec, * pTemp;
    unsigned uBoundSet;
    int i, k, nVarsBS, nVarsRem, Delay, Area;
    assert( nCofDepth >= 0 && nCofDepth < 4 );
    assert( nCofDepth < (int)p->nLutK - 1 );
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
            pvBSets[i][k] = Lpk_MergeBoundSets( pvBSets[i+1][2*k+0], pvBSets[i+1][2*k+1], p->nLutK - nCofDepth );
    // compare the resulting boundsets
    Vec_IntForEachEntry( pvBSets[0][0], uBoundSet, i )
    {
        if ( uBoundSet == 0 )
            continue;
        assert( (uBoundSet & (uBoundSet >> 16)) == 0 );
        nVarsBS = Kit_WordCountOnes( uBoundSet & 0xFFFF );
        assert( nVarsBS <= (int)p->nLutK - nCofDepth );
        nVarsRem = p->nVars - nVarsBS + nCofDepth + 1;
        Area = 1 + Lpk_LutNumLuts( nVarsRem, p->nLutK );
        Delay = 1 + Lpk_SuppDelay( uBoundSet & 0xFFFF, p->pDelays );
        if ( Area > (int)p->nAreaLim || Delay > (int)p->nDelayLim )
            continue;
        if ( pRes->BSVars == 0 || pRes->DelayEst > Delay || pRes->DelayEst == Delay && pRes->nSuppSizeL > nVarsRem )
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
}

/**Function*************************************************************

  Synopsis    [Performs DSD-based decomposition of the function.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Lpk_Res_t * Lpk_DsdAnalize( Lpk_Fun_t * p )
{
    static Lpk_Res_t Res0, * pRes0 = &Res0;
    static Lpk_Res_t Res1, * pRes1 = &Res1;
    static Lpk_Res_t Res2, * pRes2 = &Res2;
    static Lpk_Res_t Res3, * pRes3 = &Res3;
    memset( pRes0, 0, sizeof(Lpk_Res_t) );
    memset( pRes1, 0, sizeof(Lpk_Res_t) );
    memset( pRes2, 0, sizeof(Lpk_Res_t) );
    memset( pRes3, 0, sizeof(Lpk_Res_t) );
    assert( p->uSupp == Kit_BitMask(p->nVars) );

    // try decomposition without cofactoring
    Lpk_DsdAnalizeOne( p, 0, pRes0 );
    if ( pRes0->nBSVars == (int)p->nLutK && pRes0->AreaEst <= (int)p->nAreaLim && pRes0->DelayEst <= (int)p->nDelayLim )
        return pRes0;

    // cofactor 1 time
    if ( p->nLutK >= 3 ) 
        Lpk_DsdAnalizeOne( p, 1, pRes1 );
    assert( pRes1->nBSVars <= (int)p->nLutK - 1 );
    if ( pRes1->nBSVars == (int)p->nLutK - 1 && pRes1->AreaEst <= (int)p->nAreaLim && pRes1->DelayEst <= (int)p->nDelayLim )
        return pRes1;

    // cofactor 2 times
    if ( p->nLutK >= 4 ) 
        Lpk_DsdAnalizeOne( p, 2, pRes2 );
    assert( pRes2->nBSVars <= (int)p->nLutK - 2 );
    if ( pRes2->nBSVars == (int)p->nLutK - 2 && pRes2->AreaEst <= (int)p->nAreaLim && pRes2->DelayEst <= (int)p->nDelayLim )
        return pRes2;

    // cofactor 3 times
    if ( p->nLutK >= 5 ) 
        Lpk_DsdAnalizeOne( p, 3, pRes3 );
    assert( pRes3->nBSVars <= (int)p->nLutK - 3 );
    if ( pRes3->nBSVars == (int)p->nLutK - 3 && pRes3->AreaEst <= (int)p->nAreaLim && pRes3->DelayEst <= (int)p->nDelayLim )
        return pRes3;

    // choose the best under these conditions

    return NULL;
}

/**Function*************************************************************

  Synopsis    [Splits the function into two subfunctions using DSD.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Lpk_Fun_t * Lpk_DsdSplit( Lpk_Fun_t * p, char * pCofVars, int nCofVars, unsigned uBoundSet )
{
    Lpk_Fun_t * pNew;
    Kit_DsdMan_t * pDsdMan;
    Kit_DsdNtk_t * pNtkDec, * pTemp;
    unsigned * pTruth  = Lpk_FunTruth( p, 0 );
    unsigned * pTruth0 = Lpk_FunTruth( p, 1 );
    unsigned * pTruth1 = Lpk_FunTruth( p, 2 );
    unsigned * ppTruths[5][16];
    char pBSVars[5];
    int i, k, nVars, iVacVar, nCofs;
    // get the bound set variables
    nVars = Lpk_SuppToVars( uBoundSet, pBSVars );
    // get the vacuous variable
    iVacVar = pBSVars[0];
    // compute the cofactors
    Lpk_FunAllocTruthTables( p, nCofVars + 1, ppTruths );
    for ( i = 0; i < nCofVars; i++ )
        for ( k = 0; k < (1<<i); k++ )
        {
            Kit_TruthCofactor0New( ppTruths[i+1][2*k+0], ppTruths[i][k], p->nVars, pCofVars[i] );
            Kit_TruthCofactor1New( ppTruths[i+1][2*k+1], ppTruths[i][k], p->nVars, pCofVars[i] );
        }
    // decompose each cofactor w.r.t. the bound set
    nCofs = (1<<nCofVars);
    pDsdMan = Kit_DsdManAlloc( p->nVars, p->nVars * 2 );
    for ( k = 0; k < nCofs; k++ )
    {
        pNtkDec = Kit_DsdDecompose( ppTruths[nCofVars][k], p->nVars );
        pNtkDec = Kit_DsdExpand( pTemp = pNtkDec );      Kit_DsdNtkFree( pTemp );
        Kit_DsdTruthPartialTwo( pDsdMan, pNtkDec, uBoundSet, iVacVar, ppTruths[nCofVars+1][k], ppTruths[nCofVars+1][nCofs+k] );
        Kit_DsdNtkFree( pNtkDec );
    }
    Kit_DsdManFree( pDsdMan );
    // compute the composition/decomposition functions (they will be in pTruth0/pTruth1)
    for ( i = nCofVars; i >= 1; i-- )
        for ( k = 0; k < (1<<i); k++ )
            Kit_TruthMuxVar( ppTruths[i][k], ppTruths[i+1][2*k+0], ppTruths[i+1][2*k+1], nVars, pCofVars[i-1] );

    // derive the new component
    pNew = Lpk_FunDup( p, pTruth1 );
    // update the old component
    Kit_TruthCopy( pTruth, pTruth0, p->nVars );
    p->uSupp = Kit_TruthSupport( pTruth0, p->nVars );
    p->pFanins[iVacVar] = pNew->Id;
    p->pDelays[iVacVar] = Lpk_SuppDelay( pNew->uSupp, pNew->pDelays );
    // support minimize both
    Lpk_FunSuppMinimize( p );
    Lpk_FunSuppMinimize( pNew );
    // update delay and area requirements
    pNew->nDelayLim = p->pDelays[iVacVar];
    pNew->nAreaLim = 1;
    p->nAreaLim = p->nAreaLim - 1;

    // free cofactor storage
    Lpk_FunFreeTruthTables( p, nCofVars + 1, ppTruths );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


