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
void Gia_ManFlattenLogicHierarchy_rec( Gia_Man_t * pNew, Abc_Ntk_t * pNtk, int * pCounter, Vec_Int_t * vBufs )
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
            Gia_ManFlattenLogicHierarchy_rec( pNew, pModel, pCounter, vBufs );
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
Gia_Man_t * Gia_ManFlattenLogicHierarchy( Abc_Ntk_t * pNtk )
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
    Gia_ManFlattenLogicHierarchy_rec( pNew, pNtk, &Counter, pNew->vBarBufs );
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


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

