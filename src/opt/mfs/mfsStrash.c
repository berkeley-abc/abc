/**CFile****************************************************************

  FileName    [mfsStrash.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [The good old minimization with complete don't-cares.]

  Synopsis    [Structural hashing of the window with ODCs.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: mfsStrash.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "mfsInt.h"

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
void Abc_MfsConvertHopToAig_rec( Hop_Obj_t * pObj, Aig_Man_t * pMan )
{
    assert( !Hop_IsComplement(pObj) );
    if ( !Hop_ObjIsNode(pObj) || Hop_ObjIsMarkA(pObj) )
        return;
    Abc_MfsConvertHopToAig_rec( Hop_ObjFanin0(pObj), pMan ); 
    Abc_MfsConvertHopToAig_rec( Hop_ObjFanin1(pObj), pMan );
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
void Abc_MfsConvertHopToAig( Abc_Obj_t * pObjOld, Aig_Man_t * pMan )
{
    Hop_Man_t * pHopMan;
    Hop_Obj_t * pRoot;
    Abc_Obj_t * pFanin;
    int i;
    // get the local AIG
    pHopMan = pObjOld->pNtk->pManFunc;
    pRoot = pObjOld->pData;
    // check the case of a constant
    if ( Hop_ObjIsConst1( Hop_Regular(pRoot) ) )
    {
        pObjOld->pCopy = (Abc_Obj_t *)Aig_NotCond( Aig_ManConst1(pMan), Hop_IsComplement(pRoot) );
        pObjOld->pNext = pObjOld->pCopy;
        return;
    }

    // assign the fanin nodes
    Abc_ObjForEachFanin( pObjOld, pFanin, i )
        Hop_ManPi(pHopMan, i)->pData = pFanin->pCopy;
    // construct the AIG
    Abc_MfsConvertHopToAig_rec( Hop_Regular(pRoot), pMan );
    pObjOld->pCopy = (Abc_Obj_t *)Aig_NotCond( Hop_Regular(pRoot)->pData, Hop_IsComplement(pRoot) );  
    Hop_ConeUnmark_rec( Hop_Regular(pRoot) );

    // assign the fanin nodes
    Abc_ObjForEachFanin( pObjOld, pFanin, i )
        Hop_ManPi(pHopMan, i)->pData = pFanin->pNext;
    // construct the AIG
    Abc_MfsConvertHopToAig_rec( Hop_Regular(pRoot), pMan );
    pObjOld->pNext = (Abc_Obj_t *)Aig_NotCond( Hop_Regular(pRoot)->pData, Hop_IsComplement(pRoot) );  
    Hop_ConeUnmark_rec( Hop_Regular(pRoot) );
}

/**Function*************************************************************

  Synopsis    [Computes the care set of the node under ODCs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Abc_NtkConstructAig_rec( Mfs_Man_t * p, Abc_Obj_t * pNode, Aig_Man_t * pMan )
{
    Aig_Obj_t * pRoot, * pExor;
    Abc_Obj_t * pObj;
    int i;
    // assign AIG nodes to the leaves
    Vec_PtrForEachEntry( p->vSupp, pObj, i )
        pObj->pCopy = pObj->pNext = (Abc_Obj_t *)Aig_ObjCreatePi( pMan );
    // strash intermediate nodes
    Abc_NtkIncrementTravId( pNode->pNtk );
    Vec_PtrForEachEntry( p->vNodes, pObj, i )
    {
        Abc_MfsConvertHopToAig( pObj, pMan );
        if ( pObj == pNode )
            pObj->pNext = Abc_ObjNot(pObj->pNext);
    }
    // create the observability condition
    pRoot = Aig_ManConst0(pMan);
    Vec_PtrForEachEntry( p->vRoots, pObj, i )
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
Aig_Obj_t * Abc_NtkConstructCare_rec( Aig_Man_t * pCare, Aig_Obj_t * pObj, Aig_Man_t * pMan )
{
    Aig_Obj_t * pObj0, * pObj1;
    if ( Aig_ObjIsTravIdCurrent( pCare, pObj ) )
        return pObj->pData;
    Aig_ObjSetTravIdCurrent( pCare, pObj );
    if ( Aig_ObjIsPi(pObj) )
        return pObj->pData = NULL;
    pObj0 = Abc_NtkConstructCare_rec( pCare, Aig_ObjFanin0(pObj), pMan );
    if ( pObj0 == NULL )
        return pObj->pData = NULL;
    pObj1 = Abc_NtkConstructCare_rec( pCare, Aig_ObjFanin1(pObj), pMan );
    if ( pObj1 == NULL )
        return pObj->pData = NULL;
    pObj0 = Aig_NotCond( pObj0, Aig_ObjFaninC0(pObj) );
    pObj1 = Aig_NotCond( pObj1, Aig_ObjFaninC1(pObj) );
    return pObj->pData = Aig_And( pMan, pObj0, pObj1 );
}

/**Function*************************************************************

  Synopsis    [Creates AIG for the window with constraints.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Abc_NtkConstructAig( Mfs_Man_t * p, Abc_Obj_t * pNode )
{
    Aig_Man_t * pMan;
    Abc_Obj_t * pFanin;
    Aig_Obj_t * pObjAig, * pPi, * pPo;
    int i;
    // start the new manager
    pMan = Aig_ManStart( 1000 );
    // construct the root node's AIG cone
    pObjAig = Abc_NtkConstructAig_rec( p, pNode, pMan );
//    assert( Aig_ManConst1(pMan) == pObjAig );
    Aig_ObjCreatePo( pMan, pObjAig );
    if ( p->pCare )
    {
        // mark the care set
        Aig_ManIncrementTravId( p->pCare );
        Vec_PtrForEachEntry( p->vSupp, pFanin, i )
        {
            pPi = Aig_ManPi( p->pCare, (int)pFanin->pData );
            Aig_ObjSetTravIdCurrent( p->pCare, pPi );
            pPi->pData = pFanin->pCopy;
        }
        // construct the constraints
        Aig_ManForEachPo( p->pCare, pPo, i )
        {
//            assert( Aig_ObjFanin0(pPo) != Aig_ManConst1(p->pCare) );
            if ( Aig_ObjFanin0(pPo) == Aig_ManConst1(p->pCare) )
                continue;
            pObjAig = Abc_NtkConstructCare_rec( p->pCare, Aig_ObjFanin0(pPo), pMan );
            if ( pObjAig == NULL )
                continue;
            pObjAig = Aig_NotCond( pObjAig, Aig_ObjFaninC0(pPo) );
            Aig_ObjCreatePo( pMan, pObjAig );
        }
    }
    if ( p->pPars->fResub )
    {
        // construct the node
        pObjAig = (Aig_Obj_t *)pNode->pCopy;
        Aig_ObjCreatePo( pMan, pObjAig );
        // construct the divisors
        Vec_PtrForEachEntry( p->vDivs, pFanin, i )
        {
            pObjAig = (Aig_Obj_t *)pFanin->pCopy;
            Aig_ObjCreatePo( pMan, pObjAig );
        }
    }
    else
    {
        // construct the fanins
        Abc_ObjForEachFanin( pNode, pFanin, i )
        {
            pObjAig = (Aig_Obj_t *)pFanin->pCopy;
            Aig_ObjCreatePo( pMan, pObjAig );
        }
    }
    Aig_ManCleanup( pMan );
    return pMan;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


