/**CFile****************************************************************

  FileName    [cgtAig.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Clock gating package.]

  Synopsis    [Creates AIG to compute clock-gating.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cgtAig.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cgtInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computes transitive fanout cone of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cgt_ManDetectCandidates_rec( Aig_Man_t * pAig, Aig_Obj_t * pObj, int nLevelMax, Vec_Ptr_t * vCands )
{
    if ( Aig_ObjIsTravIdCurrent(pAig, pObj) )
        return;
    Aig_ObjSetTravIdCurrent(pAig, pObj);
    if ( Aig_ObjIsNode(pObj) )
    {
        Cgt_ManDetectCandidates_rec( pAig, Aig_ObjFanin0(pObj), nLevelMax, vCands );
        Cgt_ManDetectCandidates_rec( pAig, Aig_ObjFanin1(pObj), nLevelMax, vCands );
    }
    if ( Aig_ObjLevel(pObj) <= nLevelMax )
        Vec_PtrPush( vCands, pObj );
}

/**Function*************************************************************

  Synopsis    [Computes transitive fanout cone of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cgt_ManDetectCandidates( Aig_Man_t * pAig, Aig_Obj_t * pObj, int nLevelMax, Vec_Ptr_t * vCands )
{
    Vec_PtrClear( vCands );
    if ( !Aig_ObjIsNode(Aig_ObjFanin0(pObj)) )
        return;
    Aig_ManIncrementTravId( pAig );
    Cgt_ManDetectCandidates_rec( pAig, pObj, nLevelMax, vCands );
}

/**Function*************************************************************

  Synopsis    [Computes transitive fanout cone of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cgt_ManDetectFanout_rec( Aig_Man_t * pAig, Aig_Obj_t * pObj, int nOdcMax, Vec_Ptr_t * vFanout )
{
    Aig_Obj_t * pFanout;
    int f, iFanout;
    if ( Aig_ObjIsPo(pObj) || Aig_ObjLevel(pObj) > nOdcMax )
        return;
    if ( Aig_ObjIsTravIdCurrent(pAig, pObj) )
        return;
    Aig_ObjSetTravIdCurrent(pAig, pObj);
    Vec_PtrPush( vFanout, pObj );
    Aig_ObjForEachFanout( pAig, pObj, pFanout, iFanout, f )
        Cgt_ManDetectFanout_rec( pAig, pFanout, nOdcMax, vFanout );
}

/**Function*************************************************************

  Synopsis    [Computes transitive fanout cone of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cgt_ManDetectFanout( Aig_Man_t * pAig, Aig_Obj_t * pObj, int nOdcMax, Vec_Ptr_t * vFanout )
{
    Aig_Obj_t * pFanout;
    int i, k, f, iFanout;
    // collect visited nodes
    Vec_PtrClear( vFanout );
    Aig_ManIncrementTravId( pAig );
    Cgt_ManDetectFanout_rec( pAig, pObj, nOdcMax, vFanout );
    // remove those nodes whose fanout is included
    k = 0;
    Vec_PtrForEachEntry( vFanout, pObj, i )
    {
        // go through the fanouts of this node
        Aig_ObjForEachFanout( pAig, pObj, pFanout, iFanout, f )
            if ( !Aig_ObjIsTravIdCurrent(pAig, pFanout) )
                break;
        if ( f == Aig_ObjRefs(pObj) ) // all fanouts are included
            continue;
        Vec_PtrWriteEntry( vFanout, k++, pObj );
    }
    Vec_PtrShrink( vFanout, k );
    Vec_PtrSort( vFanout, Aig_ObjCompareIdIncrease );
    assert( Vec_PtrSize(vFanout) > 0 );
}

/**Function*************************************************************

  Synopsis    [Derives miter for clock-gating.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Cgt_ManConstructMiter( Cgt_Man_t * p, Aig_Man_t * pNew, Aig_Obj_t * pObjLo )
{
    Aig_Obj_t * pMiter, * pRoot;
    int i;
    assert( Aig_ObjIsPi(pObjLo) );
    pMiter = Aig_ManConst0( pNew );
    Cgt_ManDetectFanout( p->pAig, pObjLo, p->pPars->nOdcMax, p->vFanout );
    Vec_PtrForEachEntry( p->vFanout, pRoot, i )
        pMiter = Aig_Or( pNew, pMiter, Aig_Exor(pNew, pRoot->pData, pRoot->pNext) );
    return pMiter;
}

/**Function*************************************************************

  Synopsis    [Derives AIG for clock-gating.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Cgt_ManDeriveAigForGating( Cgt_Man_t * p )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pObjLi, * pObjLo;
    int i;
    assert( Aig_ManRegNum(p->pAig) );
    Aig_ManCleanNext( p->pAig );
    pNew = Aig_ManStart( Aig_ManObjNumMax(p->pAig) );
    // build the first frame
    Aig_ManConst1(p->pAig)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachPi( p->pAig, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pNew );
    Aig_ManForEachNode( p->pAig, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
//    Saig_ManForEachPo( p->pAig, pObj, i )
//        pObj->pData = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    // build the second frame
    Aig_ManConst1(p->pAig)->pNext = Aig_ManConst1(pNew);
    Saig_ManForEachPi( p->pAig, pObj, i )
        pObj->pNext = Aig_ObjCreatePi( pNew );
    Saig_ManForEachLiLo( p->pAig, pObjLi, pObjLo, i )
        pObjLo->pNext = Aig_ObjChild0Copy(pObjLi);
    Aig_ManForEachNode( p->pAig, pObj, i )
        if ( Aig_ObjLevel(pObj) <= p->pPars->nOdcMax )
            pObj->pNext = Aig_And( pNew, Aig_ObjChild0Next(pObj), Aig_ObjChild1Next(pObj) );
    // construct clock-gating miters for each register input
    Saig_ManForEachLiLo( p->pAig, pObjLi, pObjLo, i )
        pObjLi->pData = Aig_ObjCreatePo( pNew, Cgt_ManConstructMiter(p, pNew, pObjLo) );
    Aig_ManCleanNext( p->pAig );
    Aig_ManSetPioNumbers( p->pAig );
    Aig_ManCleanup( pNew );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG recursively.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Cgt_ManDupPartition_rec( Aig_Man_t * pNew, Aig_Man_t * pAig, Aig_Obj_t * pObj )
{
    if ( Aig_ObjIsTravIdCurrent(pAig, pObj) )
        return pObj->pData;
    Aig_ObjSetTravIdCurrent(pAig, pObj);
    if ( Aig_ObjIsPi(pObj) )
        return pObj->pData = Aig_ObjCreatePi( pNew );
    Cgt_ManDupPartition_rec( pNew, pAig, Aig_ObjFanin0(pObj) );
    Cgt_ManDupPartition_rec( pNew, pAig, Aig_ObjFanin1(pObj) );
    return pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
}

/**Function*************************************************************

  Synopsis    [Duplicates register outputs starting from the given one.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Cgt_ManDupPartition( Aig_Man_t * pAig, int nVarsMin, int nFlopsMin, int iStart )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i;
    assert( Aig_ManRegNum(pAig) == 0 );
    pNew = Aig_ManStart( nVarsMin );
    Aig_ManIncrementTravId( pAig );
    Aig_ManConst1(pAig)->pData = Aig_ManConst1(pNew);
    Aig_ObjSetTravIdCurrent( pAig, Aig_ManConst1(pAig) );
    for ( i = iStart; i < iStart + nFlopsMin && i < Aig_ManPoNum(pAig); i++ )
    {
        pObj = Aig_ManPo( pAig, i );
        Cgt_ManDupPartition_rec( pNew, pAig, Aig_ObjFanin0(pObj) );
        pObj->pData = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    }
    for ( ; Aig_ManObjNum(pNew) < nVarsMin && i < Aig_ManPoNum(pAig); i++ )
    {
        pObj = Aig_ManPo( pAig, i );
        Cgt_ManDupPartition_rec( pNew, pAig, Aig_ObjFanin0(pObj) );
        pObj->pData = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    }
    assert( nFlopsMin >= Aig_ManPoNum(pAig) || Aig_ManPoNum(pNew) >= nFlopsMin );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Derives AIG after clock-gating.]

  Description [The array contains, for each flop, its gate if present.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Cgt_ManDeriveGatedAig( Aig_Man_t * pAig, Vec_Ptr_t * vGates )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pObjNew, * pObjLi, * pObjLo, * pGate, * pGateNew;
    int i;
    assert( Aig_ManRegNum(pAig) );
    pNew = Aig_ManStart( Aig_ManObjNumMax(pAig) );
    Aig_ManConst1(pAig)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachPi( pAig, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pNew );
    Aig_ManForEachNode( pAig, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    Saig_ManForEachPo( pAig, pObj, i )
        pObj->pData = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    Saig_ManForEachLiLo( pAig, pObjLi, pObjLo, i )
    {
        pGate = Vec_PtrEntry( vGates, i );
        if ( pGate == NULL )
            pObjNew = Aig_ObjChild0Copy(pObjLi);
        else
        {
            pGateNew = Aig_NotCond( Aig_Regular(pGate)->pData, Aig_IsComplement(pGate) );
            pObjNew = Aig_Mux( pNew, pGateNew, pObjLo->pData, Aig_ObjChild0Copy(pObjLi) );
        }
        pObjLi->pData = Aig_ObjCreatePo( pNew, pObjNew );
    }
    Aig_ManCleanup( pNew );
    Aig_ManSetRegNum( pNew, Aig_ManRegNum(pAig) );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


