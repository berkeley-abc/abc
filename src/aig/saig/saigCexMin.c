/**CFile****************************************************************

  FileName    [saigCexMin.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [CEX minimization.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: saigCexMin.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "saig.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns reasons for the property to fail.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManCexMinFindReason_rec( Aig_Man_t * p, Aig_Obj_t * pObj, Vec_Int_t * vPrios, Vec_Int_t * vReasonPis, Vec_Int_t * vReasonLis )
{
    if ( Aig_ObjIsTravIdCurrent(p, pObj) )
        return;
    Aig_ObjSetTravIdCurrent(p, pObj);
    if ( Saig_ObjIsPi(p, pObj) )
    {
        Vec_IntPush( vReasonPis, Aig_ObjPioNum(pObj) );
        return;
    }
    if ( Saig_ObjIsLo(p, pObj) )
    {
        Vec_IntPush( vReasonLis, Aig_ObjPioNum(pObj) - Aig_ManRegNum(p) );
        return;
    }
    assert( Aig_ObjIsNode(pObj) );
    if ( pObj->fPhase )
    {
        Saig_ManCexMinFindReason_rec( p, Aig_ObjFanin0(pObj), vPrios, vReasonPis, vReasonLis );
        Saig_ManCexMinFindReason_rec( p, Aig_ObjFanin1(pObj), vPrios, vReasonPis, vReasonLis );
    }
    else
    {
        int fPhase0 = Aig_ObjFaninC0(pObj) ^ Aig_ObjFanin0(pObj)->fPhase;
        int fPhase1 = Aig_ObjFaninC1(pObj) ^ Aig_ObjFanin1(pObj)->fPhase;
        assert( !fPhase0 || !fPhase1 );
        if ( !fPhase0 && fPhase1 )
            Saig_ManCexMinFindReason_rec( p, Aig_ObjFanin0(pObj), vPrios, vReasonPis, vReasonLis );
        else if ( fPhase0 && !fPhase1 )
            Saig_ManCexMinFindReason_rec( p, Aig_ObjFanin1(pObj), vPrios, vReasonPis, vReasonLis );
        else 
        {
            int iPrio0 = Vec_IntEntry( vPrios, Aig_ObjFaninId0(pObj) );
            int iPrio1 = Vec_IntEntry( vPrios, Aig_ObjFaninId1(pObj) );
            if ( iPrio0 >= iPrio1 )
                Saig_ManCexMinFindReason_rec( p, Aig_ObjFanin0(pObj), vPrios, vReasonPis, vReasonLis );
            else
                Saig_ManCexMinFindReason_rec( p, Aig_ObjFanin1(pObj), vPrios, vReasonPis, vReasonLis );
        }
    }
}

/**Function*************************************************************

  Synopsis    [Recursively sets phase and priority.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManCexMinComputePrio_rec( Aig_Man_t * pAig, Aig_Obj_t * pObj, Vec_Int_t * vPrios )
{
    if ( Aig_ObjIsTravIdCurrent(pAig, pObj) )
        return;
    Aig_ObjSetTravIdCurrent(pAig, pObj);
    if ( Aig_ObjIsPo(pObj) )
    {
        Saig_ManCexMinComputePrio_rec( pAig, Aig_ObjFanin0(pObj), vPrios );
        pObj->fPhase = Aig_ObjFaninC0(pObj) ^ Aig_ObjFanin0(pObj)->fPhase;
        Vec_IntWriteEntry( vPrios, Aig_ObjId(pObj), Vec_IntEntry( vPrios, Aig_ObjFaninId0(pObj) ) );
    }
    else if ( Aig_ObjIsNode(pObj) )
    {
        int fPhase0, fPhase1, iPrio0, iPrio1;
        Saig_ManCexMinComputePrio_rec( pAig, Aig_ObjFanin0(pObj), vPrios );
        Saig_ManCexMinComputePrio_rec( pAig, Aig_ObjFanin1(pObj), vPrios );
        fPhase0 = Aig_ObjFaninC0(pObj) ^ Aig_ObjFanin0(pObj)->fPhase;
        fPhase1 = Aig_ObjFaninC1(pObj) ^ Aig_ObjFanin1(pObj)->fPhase;
        iPrio0  = Vec_IntEntry( vPrios, Aig_ObjFaninId0(pObj) );
        iPrio1  = Vec_IntEntry( vPrios, Aig_ObjFaninId1(pObj) );
        pObj->fPhase = fPhase0 && fPhase1;
        if ( fPhase0 && fPhase1 ) // both are one
            Vec_IntWriteEntry( vPrios, Aig_ObjId(pObj), Abc_MinInt(iPrio0, iPrio1) );
        else if ( !fPhase0 && fPhase1 ) 
            Vec_IntWriteEntry( vPrios, Aig_ObjId(pObj), iPrio0 );
        else if ( fPhase0 && !fPhase1 )
            Vec_IntWriteEntry( vPrios, Aig_ObjId(pObj), iPrio1 );
        else // both are zero
            Vec_IntWriteEntry( vPrios, Aig_ObjId(pObj), Abc_MaxInt(iPrio0, iPrio1) );
    }
}

/**Function*************************************************************

  Synopsis    [Collect nodes in the unrolled timeframes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManCollectFrameTerms_rec( Aig_Man_t * pAig, Aig_Obj_t * pObj, Vec_Int_t * vFramePis, Vec_Int_t * vFrameLis )
{
    if ( Aig_ObjIsTravIdCurrent(pAig, pObj) )
        return;
    Aig_ObjSetTravIdCurrent(pAig, pObj);
    if ( Aig_ObjIsPo(pObj) )
        Saig_ManCollectFrameTerms_rec( pAig, Aig_ObjFanin0(pObj), vFramePis, vFrameLis );
    else if ( Aig_ObjIsNode(pObj) )
    {
        Saig_ManCollectFrameTerms_rec( pAig, Aig_ObjFanin0(pObj), vFramePis, vFrameLis );
        Saig_ManCollectFrameTerms_rec( pAig, Aig_ObjFanin1(pObj), vFramePis, vFrameLis );
    }
    if ( Saig_ObjIsPi( pAig, pObj ) )
        Vec_IntPush( vFramePis, Aig_ObjId(pObj) );
    if ( vFrameLis && Saig_ObjIsLo( pAig, pObj ) )
        Vec_IntPush( vFrameLis, Aig_ObjId( Saig_ObjLoToLi(pAig, pObj) ) );
}

/**Function*************************************************************

  Synopsis    [Derive unrolled timeframes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManCollectFrameTerms( Aig_Man_t * pAig, Abc_Cex_t * pCex, Vec_Vec_t * vFramePis, Vec_Vec_t * vFrameLis )
{
    Aig_Obj_t * pObj;
    int i, f, Entry;
    // sanity checks
    assert( Saig_ManPiNum(pAig) == pCex->nPis );
    assert( Saig_ManRegNum(pAig) == pCex->nRegs );
    assert( pCex->iPo >= 0 && pCex->iPo < Saig_ManPoNum(pAig) );
    // initialized the topmost frame
    pObj = Aig_ManPo( pAig, pCex->iPo );
    Vec_VecPushInt( vFrameLis, pCex->iFrame, Aig_ObjId(pObj) );
    for ( f = pCex->iFrame; f >= 0; f-- )
    {
        // collect nodes starting from the roots
        Aig_ManIncrementTravId( pAig );
        Vec_VecForEachEntryIntLevel( vFrameLis, Entry, i, f )
            Saig_ManCollectFrameTerms_rec( pAig, Aig_ManObj(pAig, Entry),
                Vec_VecEntryInt( vFramePis, f ),
                (Vec_Int_t *)(f ? Vec_VecEntry( vFrameLis, f-1 ) : NULL) );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManCexMinPhasePriority( Aig_Man_t * pAig, Abc_Cex_t * pCex, int f, 
    Vec_Vec_t * vFramePis, Vec_Vec_t * vFrameLis, Vec_Vec_t * vPrioPis, Vec_Vec_t * vPrioLis, Vec_Vec_t * vPhaseLis, Vec_Int_t * vPrios )
{
    Aig_Obj_t * pObj;
    int i, Entry;
    // set PI priority for this frame
    Vec_VecForEachEntryIntLevel( vFramePis, Entry, i, f )
    {
        pObj = Aig_ManObj( pAig, Entry );
        pObj->fPhase = Aig_InfoHasBit( pCex->pData, pCex->nRegs + pCex->nPis * f + i );
        Vec_IntWriteEntry( vPrios, Aig_ObjId(pObj), Vec_VecEntryEntryInt(vPrioPis, f, i) );
    }
    // set LO priority for this frame
    if ( f == 0 ) 
    {
        int nPiPrioStart = Vec_VecSizeSize(vFramePis);
        Saig_ManForEachLo( pAig, pObj, i )
            Vec_IntWriteEntry( vPrios, Aig_ObjId(pObj), nPiPrioStart + i );
    }
    else
    {
        Vec_Int_t * vPrioLiOne  = Vec_VecEntryInt( vPrioLis, f-1 );
        Vec_Int_t * vPhaseLiOne = Vec_VecEntryInt( vPhaseLis, f-1 );
        Vec_VecForEachEntryIntLevel( vFrameLis, Entry, i, f-1 )
        {
            pObj = Saig_ObjLiToLo( pAig, Aig_ManObj(pAig, Entry) );
            pObj->fPhase = Vec_IntEntry( vPhaseLiOne, i );
            Vec_IntWriteEntry( vPrios, Aig_ObjId(pObj), Vec_IntEntry(vPrioLiOne, i) );
        }
    }
    // traverse, set phase and priority for internal nodes
    Aig_ManIncrementTravId( pAig );
    Vec_VecForEachEntryIntLevel( vFrameLis, Entry, i, f )
        Saig_ManCexMinComputePrio_rec( pAig, Aig_ManObj(pAig, Entry), vPrios );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t * Saig_ManCexMinPerform( Aig_Man_t * pAig, Abc_Cex_t * pCex )
{
    Abc_Cex_t * pCexMin = NULL;
    Aig_Obj_t * pObj;
    Vec_Vec_t * vFramePis, * vFrameLis, * vPrioPis, * vPrioLis, * vPhaseLis, * vReasonPis, * vReasonLis;
    Vec_Int_t * vPrios;
    int f, i, Entry, nPiPrioStart;

    // collect PIs and LOs visited in each frame
    vFramePis = Vec_VecStart( pCex->iFrame+1 );
    vFrameLis = Vec_VecStart( pCex->iFrame+1 );
    Saig_ManCollectFrameTerms( pAig, pCex, vFramePis, vFrameLis );

    // set priority for the PIs
    nPiPrioStart = 0;
    vPrioPis  = Vec_VecStart( pCex->iFrame+1 );
    Vec_VecForEachEntryInt( vFramePis, Entry, f, i )
        Vec_VecPushInt( vPrioPis, f, nPiPrioStart++ );
    assert( nPiPrioStart == Vec_VecSizeSize(vFramePis) );

    // storage for priorities
    vPrios = Vec_IntStartFull( Aig_ManObjNumMax(pAig) );
    Vec_IntWriteEntry( vPrios, Aig_ObjId(Aig_ManConst1(pAig)), Vec_VecSizeSize(vFramePis) + Aig_ManRegNum(pAig) );

    // compute LO priority and phase
    vPrioLis  = Vec_VecStart( pCex->iFrame+1 );
    vPhaseLis = Vec_VecStart( pCex->iFrame+1 );
    for ( f = 0; f <= pCex->iFrame; f++ )
    {
        // set phase and polarity
        Saig_ManCexMinPhasePriority( pAig, pCex, f, vFramePis, vFrameLis, vPrioPis, vPrioLis, vPhaseLis, vPrios );
        // save phase and priority
        Vec_VecForEachEntryIntLevel( vFrameLis, Entry, i, f )
        {
            pObj = Aig_ManObj( pAig, Entry );
            Vec_VecPushInt( vPrioLis, f, Vec_IntEntry(vPrios, Aig_ObjId(pObj)) );
            Vec_VecPushInt( vPhaseLis, f, pObj->fPhase );
        }
    }
    // check the property output
    pObj = Aig_ManPo( pAig, pCex->iPo );
    assert( pObj->fPhase );

    // select reason for the property to fail
    vReasonPis = Vec_VecStart( pCex->iFrame+1 );
    vReasonLis = Vec_VecStart( pCex->iFrame+1 );
    for ( f = pCex->iFrame; f >= 0; f-- )
    {
        // set phase and polarity
        Saig_ManCexMinPhasePriority( pAig, pCex, f, vFramePis, vFrameLis, vPrioPis, vPrioLis, vPhaseLis, vPrios );
        // select reasons
        Aig_ManIncrementTravId( pAig );
        Vec_VecForEachEntryIntLevel( vFrameLis, Entry, i, f )
            Saig_ManCexMinFindReason_rec( pAig, Aig_ManObj(pAig, Entry), vPrios, 
                Vec_VecEntryInt( vReasonPis, f ),
                (Vec_Int_t *)(f ? Vec_VecEntry( vReasonLis, f-1 ) : NULL) );
    }

    // here are computes the reasons
    printf( "Total number of reason PIs = %d.\n", Vec_VecSizeSize(vReasonPis) );

    // clean up
    Vec_VecFree( vFramePis );
    Vec_VecFree( vFrameLis );
    Vec_VecFree( vPrioPis );
    Vec_VecFree( vPrioLis );
    Vec_VecFree( vPhaseLis );
    Vec_VecFree( vReasonPis );
    Vec_VecFree( vReasonLis );
    Vec_IntFree( vPrios );
    return pCexMin;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

