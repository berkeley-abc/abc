/**CFile****************************************************************

  FileName    [mfxStrash.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [The good old minimization with complete don't-cares.]

  Synopsis    [Structural hashing of the window with ODCs.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: mfxStrash.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "mfxInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Construct BDDs and mark AIG nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nwk_ConvertHopToAig_rec( Hop_Obj_t * pObj, Aig_Man_t * pMan )
{
    assert( !Hop_IsComplement(pObj) );
    if ( !Hop_ObjIsNode(pObj) || Hop_ObjIsMarkA(pObj) )
        return;
    Nwk_ConvertHopToAig_rec( Hop_ObjFanin0(pObj), pMan ); 
    Nwk_ConvertHopToAig_rec( Hop_ObjFanin1(pObj), pMan );
    pObj->pData = Aig_And( pMan, (Aig_Obj_t *)Hop_ObjChild0Copy(pObj), (Aig_Obj_t *)Hop_ObjChild1Copy(pObj) ); 
    assert( !Hop_ObjIsMarkA(pObj) ); // loop detection
    Hop_ObjSetMarkA( pObj );
}

/**Function*************************************************************

  Synopsis    [Converts the network from AIG to BDD representation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nwk_ConvertHopToAig( Nwk_Obj_t * pObjOld, Aig_Man_t * pMan )
{
    Hop_Man_t * pHopMan;
    Hop_Obj_t * pRoot;
    Nwk_Obj_t * pFanin;
    int i;
    // get the local AIG
    pHopMan = pObjOld->pMan->pManHop;
    pRoot = pObjOld->pFunc;
    // check the case of a constant
    if ( Hop_ObjIsConst1( Hop_Regular(pRoot) ) )
    {
        pObjOld->pCopy = (Nwk_Obj_t *)Aig_NotCond( Aig_ManConst1(pMan), Hop_IsComplement(pRoot) );
        pObjOld->pNext = pObjOld->pCopy;
        return;
    }

    // assign the fanin nodes
    Nwk_ObjForEachFanin( pObjOld, pFanin, i )
        Hop_ManPi(pHopMan, i)->pData = pFanin->pCopy;
    // construct the AIG
    Nwk_ConvertHopToAig_rec( Hop_Regular(pRoot), pMan );
    pObjOld->pCopy = (Nwk_Obj_t *)Aig_NotCond( (Aig_Obj_t *)Hop_Regular(pRoot)->pData, Hop_IsComplement(pRoot) );  
    Hop_ConeUnmark_rec( Hop_Regular(pRoot) );

    // assign the fanin nodes
    Nwk_ObjForEachFanin( pObjOld, pFanin, i )
        Hop_ManPi(pHopMan, i)->pData = pFanin->pNext;
    // construct the AIG
    Nwk_ConvertHopToAig_rec( Hop_Regular(pRoot), pMan );
    pObjOld->pNext = (Nwk_Obj_t *)Aig_NotCond( (Aig_Obj_t *)Hop_Regular(pRoot)->pData, Hop_IsComplement(pRoot) );  
    Hop_ConeUnmark_rec( Hop_Regular(pRoot) );
}

/**Function*************************************************************

  Synopsis    [Computes the care set of the node under ODCs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Mfx_ConstructAig_rec( Mfx_Man_t * p, Nwk_Obj_t * pNode, Aig_Man_t * pMan )
{
    Aig_Obj_t * pRoot, * pExor;
    Nwk_Obj_t * pObj;
    int i;
    // assign AIG nodes to the leaves
    Vec_PtrForEachEntry( Nwk_Obj_t *, p->vSupp, pObj, i )
        pObj->pCopy = pObj->pNext = (Nwk_Obj_t *)Aig_ObjCreatePi( pMan );
    // strash intermediate nodes
    Nwk_ManIncrementTravId( pNode->pMan );
    Vec_PtrForEachEntry( Nwk_Obj_t *, p->vNodes, pObj, i )
    {
        Nwk_ConvertHopToAig( pObj, pMan );
        if ( pObj == pNode )
            pObj->pNext = Aig_Not((Aig_Obj_t *)pObj->pNext);
    }
    // create the observability condition
    pRoot = Aig_ManConst0(pMan);
    Vec_PtrForEachEntry( Nwk_Obj_t *, p->vRoots, pObj, i )
    {
        pExor = Aig_Exor( pMan, (Aig_Obj_t *)pObj->pCopy, (Aig_Obj_t *)pObj->pNext );
        pRoot = Aig_Or( pMan, pRoot, pExor );
    }
    return pRoot;
}

/**Function*************************************************************

  Synopsis    [Adds relevant constraints.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Mfx_ConstructCare_rec( Aig_Man_t * pCare, Aig_Obj_t * pObj, Aig_Man_t * pMan )
{
    Aig_Obj_t * pObj0, * pObj1;
    if ( Aig_ObjIsTravIdCurrent( pCare, pObj ) )
        return (Aig_Obj_t *)pObj->pData;
    Aig_ObjSetTravIdCurrent( pCare, pObj );
    if ( Aig_ObjIsPi(pObj) )
        return (Aig_Obj_t *)(pObj->pData = NULL);
    pObj0 = Mfx_ConstructCare_rec( pCare, Aig_ObjFanin0(pObj), pMan );
    if ( pObj0 == NULL )
        return (Aig_Obj_t *)(pObj->pData = NULL);
    pObj1 = Mfx_ConstructCare_rec( pCare, Aig_ObjFanin1(pObj), pMan );
    if ( pObj1 == NULL )
        return (Aig_Obj_t *)(pObj->pData = NULL);
    pObj0 = Aig_NotCond( pObj0, Aig_ObjFaninC0(pObj) );
    pObj1 = Aig_NotCond( pObj1, Aig_ObjFaninC1(pObj) );
    return (Aig_Obj_t *)(pObj->pData = Aig_And( pMan, pObj0, pObj1 ));
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nwk_ManVerifyManager( Nwk_Man_t * pNtk )
{
    Nwk_Obj_t * pObj;
    int i;
    Nwk_ManForEachObj( pNtk, pObj, i )
    {
        assert( pObj->pMan == pNtk );
    }
}

/**Function*************************************************************

  Synopsis    [Creates AIG for the window with constraints.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Mfx_ConstructAig( Mfx_Man_t * p, Nwk_Obj_t * pNode )
{
    Aig_Man_t * pMan;
    Nwk_Obj_t * pFanin;
    Aig_Obj_t * pObjAig, * pPi, * pPo;
    Vec_Int_t * vOuts;
    int i, k, iOut;
//    Nwk_ManVerifyManager( p->pNtk );
    // start the new manager
    pMan = Aig_ManStart( 1000 );
    // construct the root node's AIG cone
    pObjAig = Mfx_ConstructAig_rec( p, pNode, pMan );
//    assert( Aig_ManConst1(pMan) == pObjAig );
    Aig_ObjCreatePo( pMan, pObjAig );
    if ( p->pCare )
    {
        // mark the care set
        Aig_ManIncrementTravId( p->pCare );
        Vec_PtrForEachEntry( Nwk_Obj_t *, p->vSupp, pFanin, i )
        {
            pPi = Aig_ManPi( p->pCare, pFanin->PioId );
            Aig_ObjSetTravIdCurrent( p->pCare, pPi );
            pPi->pData = pFanin->pCopy;
        }
        // construct the constraints
        Vec_PtrForEachEntry( Nwk_Obj_t *, p->vSupp, pFanin, i )
        {
            vOuts = (Vec_Int_t *)Vec_PtrEntry( p->vSuppsInv, pFanin->PioId );
            Vec_IntForEachEntry( vOuts, iOut, k )
            {
                pPo = Aig_ManPo( p->pCare, iOut );
                if ( Aig_ObjIsTravIdCurrent( p->pCare, pPo ) )
                    continue;
                Aig_ObjSetTravIdCurrent( p->pCare, pPo );
                if ( Aig_ObjFanin0(pPo) == Aig_ManConst1(p->pCare) )
                    continue;
                pObjAig = Mfx_ConstructCare_rec( p->pCare, Aig_ObjFanin0(pPo), pMan );
                if ( pObjAig == NULL )
                    continue;
                pObjAig = Aig_NotCond( pObjAig, Aig_ObjFaninC0(pPo) );
                Aig_ObjCreatePo( pMan, pObjAig );
            }
        }
/*
        Aig_ManForEachPo( p->pCare, pPo, i )
        {
//            assert( Aig_ObjFanin0(pPo) != Aig_ManConst1(p->pCare) );
            if ( Aig_ObjFanin0(pPo) == Aig_ManConst1(p->pCare) )
                continue;
            pObjAig = Mfx_ConstructCare_rec( p->pCare, Aig_ObjFanin0(pPo), pMan );
            if ( pObjAig == NULL )
                continue;
            pObjAig = Aig_NotCond( pObjAig, Aig_ObjFaninC0(pPo) );
            Aig_ObjCreatePo( pMan, pObjAig );
        }
*/
    }
    if ( p->pPars->fResub )
    {
        // construct the node
        pObjAig = (Aig_Obj_t *)pNode->pCopy;
        Aig_ObjCreatePo( pMan, pObjAig );
        // construct the divisors
        Vec_PtrForEachEntry( Nwk_Obj_t *, p->vDivs, pFanin, i )
        {
            pObjAig = (Aig_Obj_t *)pFanin->pCopy;
            Aig_ObjCreatePo( pMan, pObjAig );
        }
    }
    else
    {
        // construct the fanins
        Nwk_ObjForEachFanin( pNode, pFanin, i )
        {
            pObjAig = (Aig_Obj_t *)pFanin->pCopy;
            Aig_ObjCreatePo( pMan, pObjAig );
        }
    }
    Aig_ManCleanup( pMan );
    return pMan;
}

/**Function*************************************************************

  Synopsis    [Creates AIG for the window with constraints.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Nwk_AigForConstraints( Mfx_Man_t * p, Nwk_Obj_t * pNode )
{
    Nwk_Obj_t * pFanin;
    Aig_Man_t * pMan;
    Aig_Obj_t * pPi, * pPo, * pObjAig, * pObjRoot;
    Vec_Int_t * vOuts;
    int i, k, iOut;
    if ( p->pCare == NULL )
        return NULL;
    pMan = Aig_ManStart( 1000 );
    // mark the care set
    Aig_ManIncrementTravId( p->pCare );
    Vec_PtrForEachEntry( Nwk_Obj_t *, p->vSupp, pFanin, i )
    {
        pPi = Aig_ManPi( p->pCare, pFanin->PioId );
        Aig_ObjSetTravIdCurrent( p->pCare, pPi );
        pPi->pData = Aig_ObjCreatePi(pMan);
    }
    // construct the constraints
    pObjRoot = Aig_ManConst1(pMan);
    Vec_PtrForEachEntry( Nwk_Obj_t *, p->vSupp, pFanin, i )
    {
        vOuts = (Vec_Int_t *)Vec_PtrEntry( p->vSuppsInv, pFanin->PioId );
        Vec_IntForEachEntry( vOuts, iOut, k )
        {
            pPo = Aig_ManPo( p->pCare, iOut );
            if ( Aig_ObjIsTravIdCurrent( p->pCare, pPo ) )
                continue;
            Aig_ObjSetTravIdCurrent( p->pCare, pPo );
            if ( Aig_ObjFanin0(pPo) == Aig_ManConst1(p->pCare) )
                continue;
            pObjAig = Mfx_ConstructCare_rec( p->pCare, Aig_ObjFanin0(pPo), pMan );
            if ( pObjAig == NULL )
                continue;
            pObjAig = Aig_NotCond( pObjAig, Aig_ObjFaninC0(pPo) );
            pObjRoot = Aig_And( pMan, pObjRoot, pObjAig );
        }
    }
    Aig_ObjCreatePo( pMan, pObjRoot );
    Aig_ManCleanup( pMan );
    return pMan;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

