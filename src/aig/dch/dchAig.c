/**CFile****************************************************************

  FileName    [dchAig.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Choice computation for tech-mapping.]

  Synopsis    [AIG manipulation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 29, 2008.]

  Revision    [$Id: dchAig.c,v 1.00 2008/07/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "dchInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Derives the cumulative AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dch_DeriveTotalAig_rec( Aig_Man_t * p, Aig_Obj_t * pObj )
{
    if ( pObj->pData )
        return;
    Dch_DeriveTotalAig_rec( p, Aig_ObjFanin0(pObj) );
    Dch_DeriveTotalAig_rec( p, Aig_ObjFanin1(pObj) );
    pObj->pData = Aig_And( p, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
}

/**Function*************************************************************

  Synopsis    [Derives the cumulative AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Dch_DeriveTotalAig( Vec_Ptr_t * vAigs )
{
    Aig_Man_t * pAig, * pAig2, * pAigTotal;
    Aig_Obj_t * pObj, * pObjPi, * pObjPo;
    int i, k, nNodes;
    assert( Vec_PtrSize(vAigs) > 0 );
    // make sure they have the same number of PIs/POs
    nNodes = 0;
    pAig = Vec_PtrEntry( vAigs, 0 );
    Vec_PtrForEachEntry( vAigs, pAig2, i )
    {
        assert( Aig_ManPiNum(pAig) == Aig_ManPiNum(pAig2) );
        assert( Aig_ManPoNum(pAig) == Aig_ManPoNum(pAig2) );
        nNodes += Aig_ManNodeNum(pAig);
        Aig_ManCleanData( pAig2 );
    }
    // map constant nodes
    pAigTotal = Aig_ManStart( nNodes );
    Vec_PtrForEachEntry( vAigs, pAig2, k )
        Aig_ManConst1(pAig2)->pData = Aig_ManConst1(pAigTotal);
    // map primary inputs
    Aig_ManForEachPi( pAig, pObj, i )
    {
        pObjPi = Aig_ObjCreatePi( pAigTotal );
        Vec_PtrForEachEntry( vAigs, pAig2, k )
            Aig_ManPi( pAig2, i )->pData = pObjPi;
    }
    // construct the AIG in the order of POs
    Aig_ManForEachPo( pAig, pObj, i )
    {
        Vec_PtrForEachEntry( vAigs, pAig2, k )
        {
            pObjPo = Aig_ManPo( pAig2, i );
            Dch_DeriveTotalAig_rec( pAigTotal, Aig_ObjFanin0(pObjPo) );
        }
        Aig_ObjCreatePo( pAigTotal, Aig_ObjChild0Copy(pObj) );
    }
    // mark the cone of the first AIG
    Aig_ManIncrementTravId( pAigTotal );
    Aig_ManForEachObj( pAig, pObj, i )
        if ( pObj->pData ) 
            Aig_ObjSetTravIdCurrent( pAigTotal, pObj->pData );
    // cleanup should not be done
    return pAigTotal;
}

/**Function*************************************************************

  Synopsis    [Derives the AIG with choices from representatives.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dch_DeriveChoiceAig_rec( Aig_Man_t * pNew, Aig_Man_t * pOld, Aig_Obj_t * pObj )
{
    Aig_Obj_t * pRepr, * pObjNew, * pReprNew;
    if ( pObj->pData )
        return;
    // construct AIG for the representative
    pRepr = pOld->pReprs[pObj->Id];
    if ( pRepr != NULL )
        Dch_DeriveChoiceAig_rec( pNew, pOld, pRepr );
    // skip choices with combinatinal loops
    if ( Aig_ObjCheckTfi( pOld, pObj, pRepr ) )
    {
        pOld->pReprs[pObj->Id] = NULL;
        return;
    }
    Dch_DeriveChoiceAig_rec( pNew, pOld, Aig_ObjFanin0(pObj) );
    Dch_DeriveChoiceAig_rec( pNew, pOld, Aig_ObjFanin1(pObj) );
    pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    if ( pRepr == NULL )
        return;
    // add choice
    assert( pObj->nRefs == 0 );
    pObjNew = pObj->pData;
    pReprNew = pRepr->pData;
    pNew->pEquivs[pObjNew->Id] = pNew->pEquivs[pReprNew->Id];
    pNew->pEquivs[pReprNew->Id] = pObjNew;
}

/**Function*************************************************************

  Synopsis    [Derives the AIG with choices from representatives.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Dch_DeriveChoiceAig( Aig_Man_t * pAig )
{
    Aig_Man_t * pChoices;
    Aig_Obj_t * pObj;
    int i;
    // start recording equivalences
    pChoices = Aig_ManStart( Aig_ManObjNumMax(pAig) );
    pChoices->pEquivs = CALLOC( Aig_Obj_t *, Aig_ManObjNumMax(pAig) );
    // map constants and PIs
    Aig_ManCleanData( pAig );
    Aig_ManConst1(pAig)->pData = Aig_ManConst1(pChoices);
    Aig_ManForEachPi( pAig, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pChoices );
     // construct choice nodes from the POs
    assert( pAig->pReprs != NULL );
    Aig_ManForEachPo( pAig, pObj, i )
    {
        Dch_DeriveChoiceAig_rec( pChoices, pAig, Aig_ObjFanin0(pObj) );
        Aig_ObjCreatePo( pChoices, Aig_ObjChild0Copy(pObj) );
    }
    // there is no need for cleanup
    return pChoices;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


