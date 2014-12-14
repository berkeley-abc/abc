/**CFile****************************************************************

  FileName    [abcHieGia.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Procedures to handle hierarchy.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcHieGia.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Transfers the AIG from one manager into another.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeStrashToGia_rec( Gia_Man_t * pNew, Hop_Obj_t * pObj )
{
    assert( !Hop_IsComplement(pObj) );
    if ( !Hop_ObjIsNode(pObj) || Hop_ObjIsMarkA(pObj) )
        return;
    Abc_NodeStrashToGia_rec( pNew, Hop_ObjFanin0(pObj) ); 
    Abc_NodeStrashToGia_rec( pNew, Hop_ObjFanin1(pObj) );
    pObj->iData = Gia_ManHashAnd( pNew, Hop_ObjChild0CopyI(pObj), Hop_ObjChild1CopyI(pObj) );
    assert( !Hop_ObjIsMarkA(pObj) ); // loop detection
    Hop_ObjSetMarkA( pObj );
}
int Abc_NodeStrashToGia( Gia_Man_t * pNew, Abc_Obj_t * pNode )
{
    Hop_Man_t * pMan = (Hop_Man_t *)pNode->pNtk->pManFunc;
    Hop_Obj_t * pRoot = (Hop_Obj_t *)pNode->pData;
    Abc_Obj_t * pFanin;  int i;
    assert( Abc_ObjIsNode(pNode) );
    assert( Abc_NtkHasAig(pNode->pNtk) && !Abc_NtkIsStrash(pNode->pNtk) );
    // check the constant case
    if ( Abc_NodeIsConst(pNode) || Hop_Regular(pRoot) == Hop_ManConst1(pMan) )
        return Abc_LitNotCond( 1, Hop_IsComplement(pRoot) );
    // set elementary variables
    Abc_ObjForEachFanin( pNode, pFanin, i )
        assert( pFanin->iTemp != -1 );
    Abc_ObjForEachFanin( pNode, pFanin, i )
        Hop_IthVar(pMan, i)->iData = pFanin->iTemp;
    // strash the AIG of this node
    Abc_NodeStrashToGia_rec( pNew, Hop_Regular(pRoot) );
    Hop_ConeUnmark_rec( Hop_Regular(pRoot) );
    return Abc_LitNotCond( Hop_Regular(pRoot)->iData, Hop_IsComplement(pRoot) );
}


/**Function*************************************************************

  Synopsis    [Flattens the logic hierarchy of the netlist.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkFlattenHierarchyGia2_rec( Gia_Man_t * pNew, Abc_Ntk_t * pNtk, int * pCounter, Vec_Int_t * vBufs )
{
    Vec_Ptr_t * vDfs = (Vec_Ptr_t *)pNtk->pData;
    Abc_Obj_t * pObj, * pTerm; 
    int i, k; (*pCounter)++;
    //printf( "[%d:%d] ", Abc_NtkPiNum(pNtk), Abc_NtkPoNum(pNtk) );
    Vec_PtrForEachEntry( Abc_Obj_t *, vDfs, pObj, i )
    {
        if ( Abc_ObjIsNode(pObj) )
            Abc_ObjFanout0(pObj)->iTemp = Abc_NodeStrashToGia( pNew, pObj );
        else
        {
            int iBufStart = Gia_ManBufNum(pNew);
            Abc_Ntk_t * pModel = (Abc_Ntk_t *)pObj->pData;
            assert( !Abc_ObjIsLatch(pObj) );
            assert( Abc_NtkPiNum(pModel) == Abc_ObjFaninNum(pObj) );
            assert( Abc_NtkPoNum(pModel) == Abc_ObjFanoutNum(pObj) );
            Abc_NtkFillTemp( pModel );
            Abc_ObjForEachFanin( pObj, pTerm, k )
            {
                assert( Abc_ObjIsNet(Abc_ObjFanin0(pTerm)) );
                Abc_ObjFanout0(Abc_NtkPi(pModel, k))->iTemp = Abc_ObjFanin0(pTerm)->iTemp;
            }
            if ( vBufs )
                Abc_ObjForEachFanin( pObj, pTerm, k )
                    Abc_ObjFanout0(Abc_NtkPi(pModel, k))->iTemp = Gia_ManAppendBuf( pNew, Abc_ObjFanout0(Abc_NtkPi(pModel, k))->iTemp );
            Abc_NtkFlattenHierarchyGia2_rec( pNew, pModel, pCounter, vBufs );
            if ( vBufs )
                Abc_ObjForEachFanout( pObj, pTerm, k )
                    Abc_ObjFanin0(Abc_NtkPo(pModel, k))->iTemp = Gia_ManAppendBuf( pNew, Abc_ObjFanin0(Abc_NtkPo(pModel, k))->iTemp );
            Abc_ObjForEachFanout( pObj, pTerm, k )
            {
                assert( Abc_ObjIsNet(Abc_ObjFanout0(pTerm)) );
                Abc_ObjFanout0(pTerm)->iTemp = Abc_ObjFanin0(Abc_NtkPo(pModel, k))->iTemp;
            }
            // save buffers
            if ( vBufs == NULL )
                continue;
            Vec_IntPush( vBufs, iBufStart );
            Vec_IntPush( vBufs, Abc_NtkPiNum(pModel) );
            Vec_IntPush( vBufs, Gia_ManBufNum(pNew) - Abc_NtkPoNum(pModel) );
            Vec_IntPush( vBufs, Abc_NtkPoNum(pModel) );
        }
    }
}
Gia_Man_t * Abc_NtkFlattenHierarchyGia2( Abc_Ntk_t * pNtk )
{
    int fUseBufs = 1;
    int fUseInter = 0;
    Gia_Man_t * pNew, * pTemp; 
    Abc_Ntk_t * pModel;
    Abc_Obj_t * pTerm;
    int i, Counter = -1;
    assert( Abc_NtkIsNetlist(pNtk) );
//    Abc_NtkPrintBoxInfo( pNtk );
    Abc_NtkFillTemp( pNtk );

    // start the manager
    pNew = Gia_ManStart( Abc_NtkObjNumMax(pNtk) );
    pNew->pName = Abc_UtilStrsav(pNtk->pName);
    pNew->pSpec = Abc_UtilStrsav(pNtk->pSpec);
    if ( fUseBufs )
        pNew->vBarBufs = Vec_IntAlloc( 1000 );

    // create PIs and buffers
    Abc_NtkForEachPi( pNtk, pTerm, i )
        pTerm->iTemp = Gia_ManAppendCi( pNew );
    Abc_NtkForEachPi( pNtk, pTerm, i )
        Abc_ObjFanout0(pTerm)->iTemp = fUseInter ? Gia_ManAppendBuf(pNew, pTerm->iTemp) : pTerm->iTemp;

    // create DFS order of nets
    if ( !pNtk->pDesign )
        pNtk->pData = Abc_NtkDfsWithBoxes( pNtk );
    else
        Vec_PtrForEachEntry( Abc_Ntk_t *, pNtk->pDesign->vModules, pModel, i )
            pModel->pData = Abc_NtkDfsWithBoxes( pModel );

    // call recursively
    Gia_ManHashAlloc( pNew );
    Abc_NtkFlattenHierarchyGia2_rec( pNew, pNtk, &Counter, pNew->vBarBufs );
    Gia_ManHashStop( pNew );
    printf( "Hierarchy reader flattened %d instances of logic boxes.\n", Counter );

    // delete DFS order of nets
    if ( !pNtk->pDesign )
        Vec_PtrFreeP( (Vec_Ptr_t **)&pNtk->pData );
    else
        Vec_PtrForEachEntry( Abc_Ntk_t *, pNtk->pDesign->vModules, pModel, i )
            Vec_PtrFreeP( (Vec_Ptr_t **)&pModel->pData );

    // create buffers and POs
    Abc_NtkForEachPo( pNtk, pTerm, i )
        pTerm->iTemp = fUseInter ? Gia_ManAppendBuf(pNew, Abc_ObjFanin0(pTerm)->iTemp) : Abc_ObjFanin0(pTerm)->iTemp;
    Abc_NtkForEachPo( pNtk, pTerm, i )
        Gia_ManAppendCo( pNew, pTerm->iTemp );

    // save buffers
    if ( fUseInter )
    {
        Vec_IntPush( pNew->vBarBufs, 0 );
        Vec_IntPush( pNew->vBarBufs, Abc_NtkPiNum(pNtk) );
        Vec_IntPush( pNew->vBarBufs, Gia_ManBufNum(pNew) - Abc_NtkPoNum(pNtk) );
        Vec_IntPush( pNew->vBarBufs, Abc_NtkPoNum(pNtk) );
    }
    if ( fUseBufs )
        Vec_IntPrint( pNew->vBarBufs );

    // cleanup
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}


/**Function*************************************************************

  Synopsis    [Flattens the logic hierarchy of the netlist.]

  Description [This procedure requires that models are uniqified.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManFlattenLogicPrepare( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pTerm, * pBox; 
    int i, k;
    Abc_NtkFillTemp( pNtk );
    Abc_NtkForEachPi( pNtk, pTerm, i )
        pTerm->iData = i;
    Abc_NtkForEachPo( pNtk, pTerm, i )
        pTerm->iData = i;
    Abc_NtkForEachBox( pNtk, pBox, i )
    {
        assert( !Abc_ObjIsLatch(pBox) );
        Abc_ObjForEachFanin( pBox, pTerm, k )
            pTerm->iData = k;
        Abc_ObjForEachFanout( pBox, pTerm, k )
            pTerm->iData = k;
    }
    return Abc_NtkPiNum(pNtk) + Abc_NtkPoNum(pNtk);
}
int Abc_NtkFlattenHierarchyGia_rec( Gia_Man_t * pNew, Vec_Ptr_t * vSupers, Abc_Obj_t * pObj, Vec_Ptr_t * vBuffers )
{
    Abc_Ntk_t * pModel;
    Abc_Obj_t * pBox, * pFanin;  
    int iLit, i;
    if ( pObj->iTemp != -1 )
        return pObj->iTemp;
    if ( Abc_ObjIsNet(pObj) || Abc_ObjIsPo(pObj) || Abc_ObjIsBi(pObj) )
        return (pObj->iTemp = Abc_NtkFlattenHierarchyGia_rec(pNew, vSupers, Abc_ObjFanin0(pObj), vBuffers));
    if ( Abc_ObjIsPi(pObj) )
    {
        pBox   = (Abc_Obj_t *)Vec_PtrPop( vSupers );
        pModel = Abc_ObjModel(pBox);
        //printf( "   Exiting %s\n", Abc_NtkName(pModel) );
        assert( Abc_ObjFaninNum(pBox) == Abc_NtkPiNum(pModel) );
        assert( pObj->iData >= 0 && pObj->iData < Abc_NtkPiNum(pModel) );
        pFanin = Abc_ObjFanin( pBox, pObj->iData );
        iLit   = Abc_NtkFlattenHierarchyGia_rec( pNew, vSupers, pFanin, vBuffers );
        Vec_PtrPush( vSupers, pBox );
        //if ( vBuffers ) Vec_PtrPush( vBuffers, pFanin ); // save BI
        if ( vBuffers ) Vec_PtrPush( vBuffers, pObj );   // save PI
        return (pObj->iTemp = (vBuffers ? Gia_ManAppendBuf(pNew, iLit) : iLit));
    }
    if ( Abc_ObjIsBo(pObj) )
    {
        pBox   = Abc_ObjFanin0(pObj);
        assert( Abc_ObjIsBox(pBox) );
        Vec_PtrPush( vSupers, pBox );
        pModel = Abc_ObjModel(pBox);
        //printf( "Entering %s\n", Abc_NtkName(pModel) );
        assert( Abc_ObjFanoutNum(pBox) == Abc_NtkPoNum(pModel) );
        assert( pObj->iData >= 0 && pObj->iData < Abc_NtkPoNum(pModel) );
        pFanin = Abc_NtkPo( pModel, pObj->iData );
        iLit   = Abc_NtkFlattenHierarchyGia_rec( pNew, vSupers, pFanin, vBuffers );
        Vec_PtrPop( vSupers );
        //if ( vBuffers ) Vec_PtrPush( vBuffers, pObj );   // save BO
        if ( vBuffers ) Vec_PtrPush( vBuffers, pFanin ); // save PO
        return (pObj->iTemp = (vBuffers ? Gia_ManAppendBuf(pNew, iLit) : iLit));
    }
    assert( Abc_ObjIsNode(pObj) );
    Abc_ObjForEachFanin( pObj, pFanin, i )
        Abc_NtkFlattenHierarchyGia_rec( pNew, vSupers, pFanin, vBuffers );
    return (pObj->iTemp = Abc_NodeStrashToGia( pNew, pObj ));
}
Gia_Man_t * Abc_NtkFlattenHierarchyGia( Abc_Ntk_t * pNtk, Vec_Ptr_t ** pvBuffers, int fVerbose )
{
    int fUseBufs = 1;
    Gia_Man_t * pNew, * pTemp; 
    Abc_Ntk_t * pModel;
    Abc_Obj_t * pTerm;
    Vec_Ptr_t * vSupers;
    Vec_Ptr_t * vBuffers = fUseBufs ? Vec_PtrAlloc(1000) : NULL;
    int i, Counter = 0; 
    assert( Abc_NtkIsNetlist(pNtk) );
//    Abc_NtkPrintBoxInfo( pNtk );

    // set the PI/PO numbers
    Counter -= Abc_NtkPiNum(pNtk) + Abc_NtkPoNum(pNtk);
    if ( !pNtk->pDesign )
        Counter += Gia_ManFlattenLogicPrepare( pNtk );
    else
        Vec_PtrForEachEntry( Abc_Ntk_t *, pNtk->pDesign->vModules, pModel, i )
            Counter += Gia_ManFlattenLogicPrepare( pModel );

    // start the manager
    pNew = Gia_ManStart( Abc_NtkObjNumMax(pNtk) );
    pNew->pName = Abc_UtilStrsav(pNtk->pName);
    pNew->pSpec = Abc_UtilStrsav(pNtk->pSpec);

    // create PIs and buffers
    Abc_NtkForEachPi( pNtk, pTerm, i )
        pTerm->iTemp = Gia_ManAppendCi( pNew );

    // call recursively
    vSupers = Vec_PtrAlloc( 100 );
    Gia_ManHashAlloc( pNew );
    Abc_NtkForEachPo( pNtk, pTerm, i )
        Abc_NtkFlattenHierarchyGia_rec( pNew, vSupers, pTerm, vBuffers );
    Gia_ManHashStop( pNew );
    Vec_PtrFree( vSupers );
    printf( "Hierarchy reader flattened %d instances of boxes and added %d barbufs (out of %d).\n", 
        pNtk->pDesign ? Vec_PtrSize(pNtk->pDesign->vModules)-1 : 0, Vec_PtrSize(vBuffers), Counter );

    // create buffers and POs
    Abc_NtkForEachPo( pNtk, pTerm, i )
        Gia_ManAppendCo( pNew, pTerm->iTemp );

    if ( pvBuffers )
        *pvBuffers = vBuffers;
    else
        Vec_PtrFreeP( &vBuffers );

    // cleanup
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Inserts the result of mapping into logic hierarchy.]

  Description [When this procedure is called PIs/POs of pNtk
  point to the corresponding nodes in network with barbufs.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Gia_ManInsertOne_rec( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNew, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanin;  int i;
    if ( pObj == NULL )
        return Abc_NtkCreateNodeConst0( pNtk );
    assert( Abc_ObjNtk(pObj) == pNew );
    if ( pObj->pCopy )
        return pObj->pCopy;
    Abc_ObjForEachFanin( pObj, pFanin, i )
        Gia_ManInsertOne_rec( pNtk, pNew, pFanin );
    pObj->pCopy = Abc_NtkDupObj( pNtk, pObj, 0 );
    Abc_ObjForEachFanin( pObj, pFanin, i )
        Abc_ObjAddFanin( pObj, pFanin );
    return pObj->pCopy;
}
void Gia_ManInsertOne( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNew )
{
    Abc_Obj_t * pObj, * pBox;  int i, k;
    assert( !Abc_NtkHasMapping(pNtk) );
    assert( Abc_NtkHasMapping(pNew) );
    // check that PIs point to barbufs
    Abc_NtkForEachPi( pNtk, pObj, i )
        assert( !pObj->pCopy || Abc_ObjNtk(pObj->pCopy) == pNew );
    // make barbufs point to box outputs
    Abc_NtkForEachBox( pNtk, pBox, i )
        Abc_ObjForEachFanout( pBox, pObj, k )
        {
            pObj->pCopy = Abc_NtkPo(Abc_ObjModel(pBox), k)->pCopy;
            assert( !pObj->pCopy || Abc_ObjNtk(pObj->pCopy) == pNew );
        }
    // remove internal nodes
    Abc_NtkForEachNode( pNtk, pObj, i )
        Abc_NtkDeleteObj( pObj );
    // start traversal from box inputs
    Abc_NtkForEachBox( pNtk, pBox, i )
        Abc_ObjForEachFanin( pBox, pObj, k )
            if ( Abc_ObjFaninNum(pObj) == 0 )
                Abc_ObjAddFanin( pObj, Gia_ManInsertOne_rec(pNtk, pNew, Abc_NtkPi(Abc_ObjModel(pBox), k)->pCopy) );
    // start traversal from primary outputs
    Abc_NtkForEachPo( pNtk, pObj, i )
        if ( Abc_ObjFaninNum(pObj) == 0 )
            Abc_ObjAddFanin( pObj, Gia_ManInsertOne_rec(pNtk, pNew, pObj->pCopy) );
    // update the functionality manager
    pNtk->pManFunc = pNew->pManFunc;
    pNtk->ntkFunc  = pNew->ntkFunc;
    assert( Abc_NtkHasMapping(pNtk) );
}
void Abc_NtkInsertHierarchyGia( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNew, int fVerbose )
{
    Vec_Ptr_t * vBuffers;
    Gia_Man_t * pGia = Abc_NtkFlattenHierarchyGia( pNtk, &vBuffers, 0 );
    Abc_Ntk_t * pModel;  
    Abc_Obj_t * pObj; 
    int i;

    assert( Gia_ManPiNum(pGia) == Abc_NtkPiNum(pNtk) );
    assert( Gia_ManPiNum(pGia) == Abc_NtkPiNum(pNew) );
    assert( Gia_ManPoNum(pGia) == Abc_NtkPoNum(pNtk) );
    assert( Gia_ManPoNum(pGia) == Abc_NtkPoNum(pNew) );
    assert( Gia_ManBufNum(pGia) == Vec_PtrSize(vBuffers) );
    assert( Gia_ManBufNum(pGia) == pNew->nBarBufs2 );
    Gia_ManStop( pGia );

    // clean the networks
    if ( !pNtk->pDesign )
        Abc_NtkCleanCopy( pNtk );
    else
        Vec_PtrForEachEntry( Abc_Ntk_t *, pNtk->pDesign->vModules, pModel, i )
            Abc_NtkCleanCopy( pModel );

    // annotate PIs and POs of each network with barbufs
    Abc_NtkForEachPi( pNew, pObj, i )
        Abc_NtkPi(pNtk, i)->pCopy = pObj;
    Abc_NtkForEachPo( pNew, pObj, i )
        Abc_NtkPo(pNtk, i)->pCopy = pObj;
    Abc_NtkForEachBarBuf( pNew, pObj, i )
        ((Abc_Obj_t *)Vec_PtrEntry(vBuffers, i))->pCopy = pObj;
    Vec_PtrFree( vBuffers );

    // connect each model
    Abc_NtkCleanCopy( pNew );
    Gia_ManInsertOne( pNtk, pNew );
    if ( pNtk->pDesign )
        Vec_PtrForEachEntry( Abc_Ntk_t *, pNtk->pDesign->vModules, pModel, i )
            if ( pModel != pNtk )
                Gia_ManInsertOne( pModel, pNew );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

