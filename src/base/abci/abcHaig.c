/**CFile****************************************************************

  FileName    [abcHaig.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Implements history AIG for combinational rewriting.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcHaig.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Start history AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkHaigStart( Abc_Ntk_t * pNtk )
{
    Hop_Man_t * p;
    Abc_Obj_t * pObj, * pTemp;
    int i;
    assert( Abc_NtkIsStrash(pNtk) );
    // check if the package is already started
    if ( pNtk->pHaig )
    {
        Abc_NtkHaigStop( pNtk );
        assert( pNtk->pHaig == NULL );
        printf( "Warning: Previous history AIG was removed.\n" );
    }
    // make sure the data is clean
    Abc_NtkForEachObj( pNtk, pObj, i )
        assert( pObj->pEquiv == NULL );
    // start the HOP package
    p = Hop_ManStart();
    p->vNodes = Vec_PtrAlloc( 4096 );
    Vec_PtrPush( p->vNodes, Hop_ManConst1(p) );
    // map the constant node
    Abc_AigConst1(pNtk)->pEquiv = Hop_ManConst1(p);
    // map the CIs
    Abc_NtkForEachCi( pNtk, pObj, i )
        pObj->pEquiv = Hop_ObjCreatePi(p);
    // map the internal nodes
    Abc_NtkForEachNode( pNtk, pObj, i )
        pObj->pEquiv = Hop_And( p, Abc_ObjChild0Equiv(pObj), Abc_ObjChild1Equiv(pObj) );
    // map the choice nodes
    if ( Abc_NtkGetChoiceNum( pNtk ) )
    {
        // print warning about choice nodes
        printf( "Warning: The choice nodes in the original AIG are converted into HAIG.\n" );
        Abc_NtkForEachNode( pNtk, pObj, i )
        {
            if ( !Abc_AigNodeIsChoice( pObj ) )
                continue;
            for ( pTemp = pObj->pData; pTemp; pTemp = pTemp->pData )
                Hop_ObjCreateChoice( pObj->pEquiv, pTemp->pEquiv );
        }
    }
    // make sure everything is okay
    if ( !Hop_ManCheck(p) )
    {
        printf( "Abc_NtkHaigStart: Check for History AIG has failed.\n" );
        Hop_ManStop(p);
        return 0;
    }
    pNtk->pHaig = p;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Stops history AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkHaigStop( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    int i;
    assert( Abc_NtkIsStrash(pNtk) );
    if ( pNtk->pHaig == NULL )
    {
        printf( "Warning: History AIG is not allocated.\n" );
        return 1;
    }
    Abc_NtkForEachObj( pNtk, pObj, i )
        pObj->pEquiv = NULL;
    Hop_ManStop( pNtk->pHaig );
    pNtk->pHaig = NULL;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Transfers the HAIG to the new network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkHaigTranfer( Abc_Ntk_t * pNtkOld, Abc_Ntk_t * pNtkNew )
{
    Abc_Obj_t * pObj;
    int i;
    if ( pNtkOld->pHaig == NULL )
        return;
    // transfer the package
    assert( pNtkNew->pHaig == NULL );
    pNtkNew->pHaig = pNtkOld->pHaig;
    pNtkOld->pHaig = NULL;
    // transfer constant pointer
    Abc_AigConst1(pNtkOld)->pCopy->pEquiv = Abc_AigConst1(pNtkOld)->pEquiv;
    // transfer the CI pointers
    Abc_NtkForEachCi( pNtkOld, pObj, i )
        pObj->pCopy->pEquiv = pObj->pEquiv;
}




/**Function*************************************************************

  Synopsis    [Collects the nodes in the classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkHaigCollectMembers( Hop_Man_t * p )
{
    Vec_Ptr_t * vNodes;
    Hop_Obj_t * pObj;
    int i;
    vNodes = Vec_PtrAlloc( 4098 );
    Vec_PtrForEachEntry( p->vNodes, pObj, i )
    {
        if ( pObj->pData == NULL )
            continue;
        pObj->pData = Hop_ObjRepr( pObj );
        Vec_PtrPush( vNodes, pObj );
    }
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Creates classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkHaigCreateClasses( Vec_Ptr_t * vMembers )
{
    Vec_Ptr_t * vClasses;
    Hop_Obj_t * pObj, * pRepr;
    int i;

    // count classes
    vClasses = Vec_PtrAlloc( 4098 );
    Vec_PtrForEachEntry( vMembers, pObj, i )
    {
        pRepr = pObj->pData;
        assert( pRepr->pData == NULL );
        if ( pRepr->fMarkA == 0 ) // new
        {
            pRepr->fMarkA = 1;
            Vec_PtrPush( vClasses, pRepr );
        }
    }

    // set representatives as representatives
    Vec_PtrForEachEntry( vClasses, pObj, i )
    {
        pObj->fMarkA = 0;
        pObj->pData = pObj;
    }

    // go through the members and update
    Vec_PtrForEachEntry( vMembers, pObj, i )
    {
        pRepr = pObj->pData;
        if ( ((Hop_Obj_t *)pRepr->pData)->Id > pObj->Id )
            pRepr->pData = pObj;
    }

    // change representatives of the class
    Vec_PtrForEachEntry( vMembers, pObj, i )
    {
        pRepr = pObj->pData;
        pObj->pData = pRepr->pData;
        assert( ((Hop_Obj_t *)pObj->pData)->Id <= pObj->Id );
    }

    // update classes
    Vec_PtrForEachEntry( vClasses, pObj, i )
    {
        pRepr = pObj->pData;
        assert( pRepr->pData == pRepr );
        pRepr->pData = NULL;
        Vec_PtrWriteEntry( vClasses, i, pRepr );
        Vec_PtrPush( vMembers, pObj );
    }
/*
    Vec_PtrForEachEntry( vMembers, pObj, i )
    {
        printf( "ObjId = %4d : ", pObj->Id );
        if ( pObj->pData == NULL )
        {
            printf( "NULL" );
        }
        else
        {
            printf( "%4d", ((Hop_Obj_t *)pObj->pData)->Id );
            assert( ((Hop_Obj_t *)pObj->pData)->Id <= pObj->Id );
        }
        printf( "\n" );
    }
*/
    return vClasses;
}


/**Function*************************************************************

  Synopsis    [Returns 1 if pOld is in the TFI of pNew.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkHaigCheckTfi_rec( Abc_Obj_t * pNode, Abc_Obj_t * pOld )
{
    if ( pNode == NULL )
        return 0;
    if ( pNode == pOld )
        return 1;
    // check the trivial cases
    if ( Abc_ObjIsPi(pNode) )
        return 0;
    assert( Abc_ObjIsNode(pNode) );
    // if this node is already visited, skip
    if ( Abc_NodeIsTravIdCurrent( pNode ) )
        return 0;
    // mark the node as visited
    Abc_NodeSetTravIdCurrent( pNode );
    // check the children
    if ( Abc_NtkHaigCheckTfi_rec( Abc_ObjFanin0(pNode), pOld ) )
        return 1;
    if ( Abc_NtkHaigCheckTfi_rec( Abc_ObjFanin1(pNode), pOld ) )
        return 1;
    // check equivalent nodes
    return Abc_NtkHaigCheckTfi_rec( pNode->pData, pOld );
}

/**Function*************************************************************

  Synopsis    [Returns 1 if pOld is in the TFI of pNew.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkHaigCheckTfi( Abc_Ntk_t * pNtk, Abc_Obj_t * pOld, Abc_Obj_t * pNew )
{
    assert( !Abc_ObjIsComplement(pOld) );
    assert( !Abc_ObjIsComplement(pNew) );
    Abc_NtkIncrementTravId(pNtk);
    return Abc_NtkHaigCheckTfi_rec( pNew, pOld );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Abc_Obj_t * Hop_ObjReprAbc( Hop_Obj_t * pObj )
{
    Hop_Obj_t * pRepr;
    Abc_Obj_t * pObjAbcThis, * pObjAbcRepr;
    assert( pObj->pNext != NULL );
    if ( pObj->pData == NULL )
        return (Abc_Obj_t *)pObj->pNext;
    pRepr = pObj->pData;
    assert( pRepr->pData == NULL );
    pObjAbcThis = (Abc_Obj_t *)pObj->pNext;
    pObjAbcRepr = (Abc_Obj_t *)pRepr->pNext;
    assert( !Abc_ObjIsComplement(pObjAbcThis) );
    assert( !Abc_ObjIsComplement(pObjAbcRepr) );
    return Abc_ObjNotCond( pObjAbcRepr, pObjAbcRepr->fPhase ^ pObjAbcThis->fPhase );
//    return (Abc_Obj_t *)pObj->pNext;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Abc_Obj_t * Hop_ObjChild0Abc( Hop_Obj_t * pObj ) { return Abc_ObjNotCond( Hop_ObjReprAbc(Hop_ObjFanin0(pObj)), Hop_ObjFaninC0(pObj) ); }
static inline Abc_Obj_t * Hop_ObjChild1Abc( Hop_Obj_t * pObj ) { return Abc_ObjNotCond( Hop_ObjReprAbc(Hop_ObjFanin1(pObj)), Hop_ObjFaninC1(pObj) ); }

/**Function*************************************************************

  Synopsis    [Stops history AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkHaigRecreateAig( Abc_Ntk_t * pNtk, Hop_Man_t * p )
{
    Abc_Ntk_t * pNtkAig;
    Abc_Obj_t * pObjAbcThis, * pObjAbcRepr;
    Abc_Obj_t * pObjOld, * pObjNew;
    Hop_Obj_t * pObj;
    int i;

    assert( p->nCreated == Vec_PtrSize(p->vNodes) );
    assert( Hop_ManPoNum(p) == 0 );

    // start the new network
    pNtkAig = Abc_NtkStartFrom( pNtk, ABC_NTK_STRASH, ABC_FUNC_AIG );

    // transfer new nodes to the PIs of HOP
    Hop_ManConst1(p)->pNext = (Hop_Obj_t *)Abc_AigConst1( pNtkAig );
    Hop_ManForEachPi( p, pObj, i )
        pObj->pNext = (Hop_Obj_t *)Abc_NtkPi( pNtkAig, i );

    // construct new nodes
    Vec_PtrForEachEntry( p->vNodes, pObj, i )
        if ( Hop_ObjIsNode(pObj) )
            pObj->pNext = (Hop_Obj_t *)Abc_AigAnd( pNtkAig->pManFunc, Hop_ObjChild0Abc(pObj), Hop_ObjChild1Abc(pObj) );

    // set the COs
    Abc_NtkForEachCo( pNtk, pObjOld, i )
    {
        pObjNew = Hop_ObjReprAbc( Abc_ObjFanin0(pObjOld)->pEquiv );
        pObjNew = Abc_ObjNotCond( pObjNew, Abc_ObjFaninC0(pObjOld) );
        Abc_ObjAddFanin( pObjOld->pCopy, pObjNew );
    }

    // create choice nodes
    Vec_PtrForEachEntry( p->vNodes, pObj, i )
    {
        Abc_Obj_t * pTemp;
        if ( pObj->pData == NULL )
            continue;

        pObjAbcThis = (Abc_Obj_t *)pObj->pNext;
        pObjAbcRepr = (Abc_Obj_t *)((Hop_Obj_t *)pObj->pData)->pNext;
        assert( !Abc_ObjIsComplement(pObjAbcThis) );
        assert( !Abc_ObjIsComplement(pObjAbcRepr) );

        // skip the case when the class is constant 1
        if ( pObjAbcRepr == Abc_AigConst1(pNtkAig) )
            continue;

        // skip the case when pObjAbcThis is part of the class already
        for ( pTemp = pObjAbcRepr; pTemp; pTemp = pTemp->pData )
            if ( pTemp == pObjAbcThis )
                break;
        if ( pTemp )
            continue;

//        assert( Abc_ObjFanoutNum(pObjAbcThis) == 0 );
        if ( Abc_ObjFanoutNum(pObjAbcThis) > 0 )
            continue;
//        assert( pObjAbcThis->pData == NULL );
        if ( pObjAbcThis->pData )
            continue;

        // do not create choices if there is a path from pObjAbcThis to pObjAbcRepr
        if ( !Abc_NtkHaigCheckTfi( pNtkAig, pObjAbcRepr, pObjAbcThis ) )
        {
            // find the last node in the class
            while ( pObjAbcRepr->pData )
                pObjAbcRepr = pObjAbcRepr->pData;
            // add the new node at the end of the list
            pObjAbcRepr->pData = pObjAbcThis;
        }
    }

    // finish the new network
//    Abc_NtkFinalize( pNtk, pNtkAig );
//    Abc_AigCleanup( pNtkAig->pManFunc );
    // check correctness of the network
    if ( !Abc_NtkCheck( pNtkAig ) )
    {
        printf( "Abc_NtkHaigUse: The network check has failed.\n" );
        Abc_NtkDelete( pNtkAig );
        return NULL;
    }
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Stops history AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkHaigUse( Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkAig;
    Vec_Ptr_t * vMembers, * vClasses;

    // check if HAIG is available
    assert( Abc_NtkIsStrash(pNtk) );
    if ( pNtk->pHaig == NULL )
    {
        printf( "Warning: History AIG is not available.\n" );
        return NULL;
    }
    // convert HOP package into AIG with choices

    // print HAIG stats
//    Hop_ManPrintStats( pNtk->pHaig ); // USES DATA!!!

    // collect members of the classes and make them point to reprs
    vMembers = Abc_NtkHaigCollectMembers( pNtk->pHaig );
    printf( "Collected %6d class members.\n", Vec_PtrSize(vMembers) );

    // create classes
    vClasses = Abc_NtkHaigCreateClasses( vMembers );
    printf( "Collected %6d classes. (Ave = %5.2f)\n", Vec_PtrSize(vClasses), 
        (float)(Vec_PtrSize(vMembers))/Vec_PtrSize(vClasses) );
    Vec_PtrFree( vMembers );
    Vec_PtrFree( vClasses );

    // traverse in the topological order and create new AIG
    pNtkAig = Abc_NtkHaigRecreateAig( pNtk, pNtk->pHaig );

    // free HAIG
    Abc_NtkHaigStop( pNtk );
    return pNtkAig;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


