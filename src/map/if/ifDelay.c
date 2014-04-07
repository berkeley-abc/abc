/**CFile****************************************************************

  FileName    [ifDelay.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [Delay balancing for cut functions.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: ifDelay.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "if.h"
#include "ifCount.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define IF_MAX_CUBES 70

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////
 
/**Function*************************************************************

  Synopsis    [Computes the SOP delay using balanced AND decomposition.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int If_CutMaxCubeSize( Vec_Int_t * vCover, int nVars )
{
    int i, k, Entry, Literal, Count, CountMax = 0;
    Vec_IntForEachEntry( vCover, Entry, i )
    {
        Count = 0;
        for ( k = 0; k < nVars; k++ )
        {
            Literal = (3 & (Entry >> (k << 1)));
            if ( Literal == 1 || Literal == 2 )
                Count++;
        }
        CountMax = Abc_MaxInt( CountMax, Count );
    }
    return CountMax;
}
int If_CutDelaySop( If_Man_t * p, If_Cut_t * pCut )
{
    // delay is calculated using 1+log2(NumFanins)
    static double GateDelays[20] = { 1.00, 1.00, 2.00, 2.58, 3.00, 3.32, 3.58, 3.81, 4.00, 4.17, 4.32, 4.46, 4.58, 4.70, 4.81, 4.91, 5.00, 5.09, 5.17, 5.25 };
    Vec_Int_t * vCover;
    If_Obj_t * pLeaf;
    int i, nLitMax, Delay, DelayMax;
    // mark cut as a user cut
    pCut->fUser = 1;
    if ( pCut->nLeaves == 0 )
        return 0;
    if ( pCut->nLeaves == 1 )
        return (int)If_ObjCutBest(If_CutLeaf(p, pCut, 0))->Delay;
    vCover = Vec_WecEntry( p->vTtIsops[pCut->nLeaves], Abc_Lit2Var(If_CutTruthLit(pCut)) );
    if ( Vec_IntSize(vCover) == 0 )
        return -1;
    // mark the output as complemented
//    vAnds = If_CutDelaySopAnds( p, pCut, p->vCover, RetValue ^ pCut->fCompl );
    if ( Vec_IntSize(p->vCover) > p->pPars->nGateSize )
        return ABC_INFINITY;
    // set the area cost
    assert( If_CutLeaveNum(pCut) >= 0 && If_CutLeaveNum(pCut) <= 16 );
    // compute the gate delay
    nLitMax = If_CutMaxCubeSize( p->vCover, If_CutLeaveNum(pCut) );
    if ( Vec_IntSize(p->vCover) < 2 )
    {
        pCut->Cost = Vec_IntSize(p->vCover);
        Delay = (int)(GateDelays[If_CutLeaveNum(pCut)] + 0.5);
        DelayMax = 0;
        If_CutForEachLeaf( p, pCut, pLeaf, i )
            DelayMax = Abc_MaxInt( DelayMax, If_ObjCutBest(pLeaf)->Delay + (pCut->pPerm[i] = (char)Delay) );
    }
    else
    {
        pCut->Cost = Vec_IntSize(p->vCover) + 1;
        Delay = (int)(GateDelays[If_CutLeaveNum(pCut)] + GateDelays[nLitMax] + 0.5);
        DelayMax = 0;
        If_CutForEachLeaf( p, pCut, pLeaf, i )
            DelayMax = Abc_MaxInt( DelayMax, If_ObjCutBest(pLeaf)->Delay + (pCut->pPerm[i] = (char)Delay) );
    }
    return DelayMax;
}


/**Function*************************************************************

  Synopsis    [Compute pin delays.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CutSopBalancePinDelaysInt( Vec_Int_t * vCover, int * pTimes, int nSuppAll, char * pPerm )
{
    word pPinDelsAnd[IF_MAX_FUNC_LUTSIZE], pPinDelsOr[IF_MAX_CUBES];
    int nCounterAnd, pCounterAnd[IF_MAX_FUNC_LUTSIZE];
    int nCounterOr,  pCounterOr[IF_MAX_CUBES];
    int i, k, Entry, Literal, Delay = 0;
    word ResAnd, ResOr;
    if ( Vec_IntSize(vCover) > IF_MAX_CUBES )
        return -1;
    nCounterOr = 0;
    Vec_IntForEachEntry( vCover, Entry, i )
    { 
        nCounterAnd = 0;
        for ( k = 0; k < nSuppAll; k++ )
        {
            Literal = 3 & (Entry >> (k << 1));
            if ( Literal == 1 || Literal == 2 ) // neg or pos literal
                Delay = If_LogCounterPinDelays( pCounterAnd, &nCounterAnd, pPinDelsAnd, pTimes[k], If_CutPinDelayInit(k), nSuppAll, 0 );
            else if ( Literal != 0 ) 
                assert( 0 );
        }
        assert( nCounterAnd > 0 );
        ResAnd = If_LogPinDelaysMulti( pPinDelsAnd, nCounterAnd, nSuppAll, 0 );
        Delay = If_LogCounterPinDelays( pCounterOr, &nCounterOr, pPinDelsOr, Delay, ResAnd, nSuppAll, 0 );
    }
    assert( nCounterOr > 0 );
    ResOr = If_LogPinDelaysMulti( pPinDelsOr, nCounterOr, nSuppAll, 0 );
    If_CutPinDelayTranslate( ResOr, nSuppAll, pPerm );
    return Delay;
}
int If_CutSopBalancePinDelays( If_Man_t * p, If_Cut_t * pCut, char * pPerm )
{
    if ( pCut->nLeaves == 0 ) // const
        return 0;
    if ( pCut->nLeaves == 1 ) // variable
    {
        pPerm[0] = 0;
        return (int)If_ObjCutBest(If_CutLeaf(p, pCut, 0))->Delay;
    }
    else
    {
        Vec_Int_t * vCover;
        int i, pTimes[IF_MAX_FUNC_LUTSIZE];
        vCover = Vec_WecEntry( p->vTtIsops[pCut->nLeaves], Abc_Lit2Var(If_CutTruthLit(pCut)) );
        if ( Vec_IntSize(vCover) == 0 )
            return -1;
        for ( i = 0; i < If_CutLeaveNum(pCut); i++ )
            pTimes[i] = (int)If_ObjCutBest(If_CutLeaf(p, pCut, i))->Delay; 
        return If_CutSopBalancePinDelaysInt( vCover, pTimes, If_CutLeaveNum(pCut), pPerm );
    }
}

/**Function*************************************************************

  Synopsis    [Evaluate delay using SOP balancing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CutSopBalanceEvalIntInt( Vec_Int_t * vCover, int * pTimes, Vec_Int_t * vAig, int * piRes, int nSuppAll, int * pArea )
{
    int nCounterAnd, pCounterAnd[IF_MAX_FUNC_LUTSIZE], pFaninLitsAnd[IF_MAX_FUNC_LUTSIZE];
    int nCounterOr,  pCounterOr[IF_MAX_CUBES],  pFaninLitsOr[IF_MAX_CUBES];
    int i, k, Entry, Literal, nLits, Delay = 0, iRes = 0;
    if ( Vec_IntSize(vCover) > IF_MAX_CUBES )
        return -1;
    nCounterOr = 0;
    Vec_IntForEachEntry( vCover, Entry, i )
    { 
        nCounterAnd = nLits = 0;
        for ( k = 0; k < nSuppAll; k++ )
        {
            Literal = 3 & (Entry >> (k << 1));
            if ( Literal == 1 ) // neg literal
                nLits++, Delay = If_LogCounterAddAig( pCounterAnd, &nCounterAnd, pFaninLitsAnd, pTimes[k], Abc_Var2Lit(k, 1), vAig, nSuppAll, 0 );
            else if ( Literal == 2 ) // pos literal
                nLits++, Delay = If_LogCounterAddAig( pCounterAnd, &nCounterAnd, pFaninLitsAnd, pTimes[k], Abc_Var2Lit(k, 0), vAig, nSuppAll, 0 );
            else if ( Literal != 0 ) 
                assert( 0 );
        }
        assert( nCounterAnd > 0 );
        assert( nLits > 0 );
        if ( vAig )
            iRes = If_LogCreateAndXorMulti( vAig, pFaninLitsAnd, nCounterAnd, nSuppAll, 0 );
        else
            *pArea += nLits == 1 ? 0 : nLits - 1;
        Delay = If_LogCounterAddAig( pCounterOr, &nCounterOr, pFaninLitsOr, Delay, Abc_LitNot(iRes), vAig, nSuppAll, 0 );
    }
    assert( nCounterOr > 0 );
    if ( vAig )
        *piRes = Abc_LitNot( If_LogCreateAndXorMulti( vAig, pFaninLitsOr, nCounterOr, nSuppAll, 0 ) );
    else       
        *pArea += Vec_IntSize(vCover) == 1 ? 0 : Vec_IntSize(vCover) - 1;
    return Delay;
}
int If_CutSopBalanceEvalInt( Vec_Int_t * vCover, int nLeaves, int * pTimes, Vec_Int_t * vAig, int fCompl, int * pArea ) 
{
    int iRes = 0, Res;
    if ( Vec_IntSize(vCover) == 0 )
        return -1;
    Res = If_CutSopBalanceEvalIntInt( vCover, pTimes, vAig, &iRes, nLeaves, pArea );
    if ( Res == -1 )
        return -1;
    assert( vAig == NULL || Abc_Lit2Var(iRes) == nLeaves + Abc_Lit2Var(Vec_IntSize(vAig)) - 1 );
    if ( vAig )
        Vec_IntPush( vAig, Abc_LitIsCompl(iRes) ^ fCompl );
    assert( vAig == NULL || (Vec_IntSize(vAig) & 1) );
    return Res;
}
int If_CutSopBalanceEval( If_Man_t * p, If_Cut_t * pCut, Vec_Int_t * vAig )
{
    pCut->fUser = 1;
    if ( vAig )
        Vec_IntClear( vAig );
    if ( pCut->nLeaves == 0 ) // const
    {
        assert( Abc_Lit2Var(If_CutTruthLit(pCut)) == 0 );
        if ( vAig )
            Vec_IntPush( vAig, Abc_LitIsCompl(If_CutTruthLit(pCut)) );
        return 0;
    }
    if ( pCut->nLeaves == 1 ) // variable
    {
        assert( Abc_Lit2Var(If_CutTruthLit(pCut)) == 1 );
        if ( vAig )
            Vec_IntPush( vAig, 0 );
        if ( vAig )
            Vec_IntPush( vAig, Abc_LitIsCompl(If_CutTruthLit(pCut)) );
        return (int)If_ObjCutBest(If_CutLeaf(p, pCut, 0))->Delay;
    }
    else
    {
        Vec_Int_t * vCover = Vec_WecEntry( p->vTtIsops[pCut->nLeaves], Abc_Lit2Var(If_CutTruthLit(pCut)) );
        int fCompl = Abc_LitIsCompl(If_CutTruthLit(pCut)) ^ ((vCover->nCap >> 16) & 1); // hack to remember complemented attribute
        int Delay, Area = 0;
        int i, pTimes[IF_MAX_FUNC_LUTSIZE];
        for ( i = 0; i < If_CutLeaveNum(pCut); i++ )
            pTimes[i] = (int)If_ObjCutBest(If_CutLeaf(p, pCut, i))->Delay; 
        Delay = If_CutSopBalanceEvalInt( vCover, If_CutLeaveNum(pCut), pTimes, vAig, fCompl, &Area );
        pCut->Cost = Area;
        return Delay;
    }
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

