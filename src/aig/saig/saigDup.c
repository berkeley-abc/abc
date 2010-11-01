/**CFile****************************************************************

  FileName    [saigDup.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [Various duplication procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: saigDup.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

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

  Synopsis    [Duplicates while ORing the POs of sequential circuit.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Said_ManDupOrpos( Aig_Man_t * pAig )
{
    Aig_Man_t * pAigNew;
    Aig_Obj_t * pObj, * pMiter;
    int i;
    if ( pAig->nConstrs > 0 )
    {
        printf( "The AIG manager should have no constraints.\n" );
        return NULL;
    }
    // start the new manager
    pAigNew = Aig_ManStart( Aig_ManNodeNum(pAig) );
    pAigNew->pName = Aig_UtilStrsav( pAig->pName );
    pAigNew->nConstrs = pAig->nConstrs;
    // map the constant node
    Aig_ManConst1(pAig)->pData = Aig_ManConst1( pAigNew );
    // create variables for PIs
    Aig_ManForEachPi( pAig, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pAigNew );
    // add internal nodes of this frame
    Aig_ManForEachNode( pAig, pObj, i )
        pObj->pData = Aig_And( pAigNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    // create PO of the circuit
    pMiter = Aig_ManConst0( pAigNew );
    Saig_ManForEachPo( pAig, pObj, i )
        pMiter = Aig_Or( pAigNew, pMiter, Aig_ObjChild0Copy(pObj) );
    Aig_ObjCreatePo( pAigNew, pMiter );
    // transfer to register outputs
    Saig_ManForEachLi( pAig, pObj, i )
        Aig_ObjCreatePo( pAigNew, Aig_ObjChild0Copy(pObj) );
    Aig_ManCleanup( pAigNew );
    Aig_ManSetRegNum( pAigNew, Aig_ManRegNum(pAig) );
    return pAigNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager recursively.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Saig_ManAbstractionDfs_rec( Aig_Man_t * pNew, Aig_Obj_t * pObj )
{
    if ( pObj->pData )
        return (Aig_Obj_t *)pObj->pData;
    Saig_ManAbstractionDfs_rec( pNew, Aig_ObjFanin0(pObj) );
    Saig_ManAbstractionDfs_rec( pNew, Aig_ObjFanin1(pObj) );
    return (Aig_Obj_t *)(pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) ));
}

/**Function*************************************************************

  Synopsis    [Trims the model by removing PIs without fanout.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_ManTrimPis( Aig_Man_t * p )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i, fAllPisHaveNoRefs;
    // check the refs of PIs    
    fAllPisHaveNoRefs = 1;
    Saig_ManForEachPi( p, pObj, i )
        if ( pObj->nRefs )
            fAllPisHaveNoRefs = 0;
    // start the new manager
    pNew = Aig_ManStart( Aig_ManObjNum(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    pNew->nConstrs = p->nConstrs;
    // start mapping of the CI numbers
    pNew->vCiNumsOrig = Vec_IntAlloc( Aig_ManPiNum(p) );
    // map const and primary inputs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachPi( p, pObj, i )
        if ( fAllPisHaveNoRefs || pObj->nRefs || Saig_ObjIsLo(p, pObj) )
        {
            pObj->pData = Aig_ObjCreatePi( pNew );
            Vec_IntPush( pNew->vCiNumsOrig, Vec_IntEntry(p->vCiNumsOrig, i) );
        }
    Aig_ManForEachNode( p, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    Aig_ManForEachPo( p, pObj, i )
        pObj->pData = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    Aig_ManSetRegNum( pNew, Aig_ManRegNum(p) );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Performs abstraction of the AIG to preserve the included flops.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_ManDeriveAbstraction( Aig_Man_t * p, Vec_Int_t * vFlops )
{ 
    Aig_Man_t * pNew;//, * pTemp;
    Aig_Obj_t * pObj, * pObjLi, * pObjLo;
    int i, Entry;
    Aig_ManCleanData( p );
    // start the new manager
    pNew = Aig_ManStart( Aig_ManNodeNum(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    // map the constant node
    Aig_ManConst1(p)->pData = Aig_ManConst1( pNew );
    // label included flops
    Vec_IntForEachEntry( vFlops, Entry, i )
    {
        pObjLi = Saig_ManLi( p, Entry );
        assert( pObjLi->fMarkA == 0 );
        pObjLi->fMarkA = 1;
        pObjLo = Saig_ManLo( p, Entry );
        assert( pObjLo->fMarkA == 0 );
        pObjLo->fMarkA = 1;
    }
    // create variables for PIs
    assert( p->vCiNumsOrig == NULL );
    pNew->vCiNumsOrig = Vec_IntAlloc( Aig_ManPiNum(p) );
    Aig_ManForEachPi( p, pObj, i )
        if ( !pObj->fMarkA )
        {
            pObj->pData = Aig_ObjCreatePi( pNew );
            Vec_IntPush( pNew->vCiNumsOrig, i );
        }
    // create variables for LOs
    Aig_ManForEachPi( p, pObj, i )
        if ( pObj->fMarkA )
        {
            pObj->fMarkA = 0;
            pObj->pData = Aig_ObjCreatePi( pNew );
            Vec_IntPush( pNew->vCiNumsOrig, i );
        }
    // add internal nodes 
//    Aig_ManForEachNode( p, pObj, i )
//        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    // create POs
    Saig_ManForEachPo( p, pObj, i )
    {
        Saig_ManAbstractionDfs_rec( pNew, Aig_ObjFanin0(pObj) );
        Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    }
    // create LIs
    Aig_ManForEachPo( p, pObj, i )
        if ( pObj->fMarkA )
        {
            pObj->fMarkA = 0;
            Saig_ManAbstractionDfs_rec( pNew, Aig_ObjFanin0(pObj) );
            Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
        }
    Aig_ManSetRegNum( pNew, Vec_IntSize(vFlops) );
    Aig_ManSeqCleanup( pNew );
    // remove PIs without fanout
//    pNew = Saig_ManTrimPis( pTemp = pNew );
//    Aig_ManStop( pTemp );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

