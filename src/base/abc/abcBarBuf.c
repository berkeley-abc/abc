/**CFile****************************************************************

  FileName    [abcHie.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Procedures to handle hierarchy.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcHie.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

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

  Synopsis    [Checks the the hie design has no duplicated networks.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkCheckSingleInstance( Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pTemp, * pModel;
    Abc_Obj_t * pBox;
    int i, k, RetValue = 1;
    if ( pNtk->pDesign == NULL )
        return 1;
    Vec_PtrForEachEntry( Abc_Ntk_t *, pNtk->pDesign->vModules, pTemp, i )
        pTemp->fHieVisited = 0;
    Vec_PtrForEachEntry( Abc_Ntk_t *, pNtk->pDesign->vModules, pTemp, i )
        Abc_NtkForEachBox( pTemp, pBox, k )
        {
            pModel = (Abc_Ntk_t *)pBox->pData;
            if ( pModel == NULL )
                continue;
            if ( Abc_NtkLatchNum(pModel) > 0 )
            {
                printf( "Network \"%s\" contains %d flops.\n",                     
                    Abc_NtkName(pNtk), Abc_NtkLatchNum(pModel) );
                RetValue = 0;
            }
            if ( pModel->fHieVisited )
            {
                printf( "Network \"%s\" contains box \"%s\" whose model \"%s\" is instantiated more than once.\n", 
                    Abc_NtkName(pNtk), Abc_ObjName(pBox), Abc_NtkName(pModel) );
                RetValue = 0;
            }
            pModel->fHieVisited = 1;
        }
    Vec_PtrForEachEntry( Abc_Ntk_t *, pNtk->pDesign->vModules, pTemp, i )
        pTemp->fHieVisited = 0;
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Collect PIs and POs of internal networks in the topo order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkCollectPiPos_rec( Abc_Obj_t * pNet, Vec_Ptr_t * vPiPos )
{
    extern void Abc_NtkCollectPiPos_int( Abc_Ntk_t * pNtk, Vec_Ptr_t * vPiPos, int fAdd );
    Abc_Obj_t * pObj, * pFanin; int i;
    assert( Abc_ObjIsNet(pNet) );
    if ( Abc_NodeIsTravIdCurrent( pNet ) )
        return;
    Abc_NodeSetTravIdCurrent( pNet );
    pObj = Abc_ObjFanin0(pNet);
    assert( Abc_ObjIsNode(pObj) || Abc_ObjIsBox(pObj) );
    Abc_ObjForEachFanin( pObj, pFanin, i )
        Abc_NtkCollectPiPos_rec( pFanin, vPiPos );
    if ( Abc_ObjIsBox(pObj) )
        Abc_NtkCollectPiPos_int( (Abc_Ntk_t *)pObj->pData, vPiPos, 1 );
}
void Abc_NtkCollectPiPos_int( Abc_Ntk_t * pNtk, Vec_Ptr_t * vPiPos, int fAdd )
{
    Abc_Obj_t * pObj; int i;
    // mark primary inputs
    Abc_NtkIncrementTravId( pNtk );
    Abc_NtkForEachPi( pNtk, pObj, i )
        Abc_NodeSetTravIdCurrent( Abc_ObjFanout0(pObj) );
    // add primary inputs
    if ( fAdd )
    Abc_NtkForEachPi( pNtk, pObj, i )
        Vec_PtrPush( vPiPos, pObj );
    // visit primary outputs
    Abc_NtkForEachPo( pNtk, pObj, i )
        Abc_NtkCollectPiPos_rec( Abc_ObjFanin0(pObj), vPiPos );
    // add primary outputs
    if ( fAdd )
    Abc_NtkForEachPo( pNtk, pObj, i )
        Vec_PtrPush( vPiPos, pObj );
}
Vec_Ptr_t * Abc_NtkCollectPiPos( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vPiPos = Vec_PtrAlloc( 1000 );
    Abc_NtkCollectPiPos_int( pNtk, vPiPos, 0 );
    return vPiPos;
}

/**Function*************************************************************

  Synopsis    [Derives logic network while introducing barbufs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkToBarBufs_rec( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pNet )
{
    Abc_Ntk_t * pModel;
    Abc_Obj_t * pObj, * pFanin, * pFanout, * pLatch;
    int i;
    assert( Abc_ObjIsNet(pNet) );
    if ( pNet->pCopy )
        return;
    pObj = Abc_ObjFanin0(pNet);
    assert( Abc_ObjIsNode(pObj) || Abc_ObjIsBox(pObj) );
    Abc_ObjForEachFanin( pObj, pFanin, i )
        Abc_NtkToBarBufs_rec( pNtkNew, pFanin );
    // create and connect object
    if ( Abc_ObjIsNode(pObj) )
    {
        pNet->pCopy = Abc_NtkDupObj( pNtkNew, pObj, 0 );
        Abc_ObjForEachFanin( pObj, pFanin, i )
            Abc_ObjAddFanin( pObj->pCopy, pFanin->pCopy );
        return;
    }
    pModel = Abc_ObjModel(pObj);
    Abc_NtkCleanCopy( pModel );
    Abc_ObjForEachFanin( pObj, pFanin, i )
    {
        pLatch = Abc_NtkAddLatch( pNtkNew, pFanin->pCopy, ABC_INIT_ZERO );
        Abc_ObjFanout0(Abc_NtkPi(pModel, i))->pCopy = Abc_ObjFanout0(pLatch);
    }
    Abc_NtkForEachPo( pModel, pObj, i )
        Abc_NtkToBarBufs_rec( pNtkNew, Abc_ObjFanin0(pObj) );
    Abc_ObjForEachFanout( pObj, pFanout, i )
    {
        pLatch = Abc_NtkAddLatch( pNtkNew, Abc_ObjFanin0(Abc_NtkPo(pModel, i))->pCopy, ABC_INIT_ZERO );
        pFanout->pCopy = Abc_ObjFanout0(pLatch);
    }
}
Abc_Ntk_t * Abc_NtkToBarBufs( Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pObj;
    int i;
    assert( Abc_NtkIsNetlist(pNtk) );
    if ( !Abc_NtkCheckSingleInstance(pNtk) )
        return NULL;
    Abc_NtkCleanCopy( pNtk );
    // start the network
    pNtkNew = Abc_NtkAlloc( ABC_NTK_LOGIC, pNtk->ntkFunc, 1 );
    pNtkNew->pName = Extra_UtilStrsav(pNtk->pName);
    pNtkNew->pSpec = Extra_UtilStrsav(pNtk->pSpec);
    // clone CIs/CIs/boxes
    Abc_NtkForEachPi( pNtk, pObj, i )
        Abc_ObjFanout0(pObj)->pCopy = Abc_NtkDupObj( pNtkNew, pObj, 1 );
    Abc_NtkForEachPo( pNtk, pObj, i )
        Abc_NtkDupObj( pNtkNew, pObj, 1 );
    // create logic 
    Abc_NtkForEachPo( pNtk, pObj, i )
    {
        Abc_NtkToBarBufs_rec( pNtkNew, Abc_ObjFanin0(pObj) );
        Abc_ObjAddFanin( pObj->pCopy, Abc_ObjFanin0(pObj)->pCopy );
    }
    pNtkNew->nBarBufs = Abc_NtkLatchNum(pNtkNew);
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Converts the logic with barbufs into a hierarchical network.]

  Description [The base network is the original hierarchical network. The
  second argument is the optimized network with barbufs.  This procedure
  reconstructs the original hierarcical network which adding logic from
  the optimized network.  It is assumed that the PIs/POs of the original
  network one-to-one mapping with the flops of the optimized network.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkFromBarBufs_rec( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanin; int i;
    if ( pObj->pCopy )
        return pObj->pCopy;
    Abc_NtkDupObj( pNtkNew, pObj, 0 );
    Abc_ObjForEachFanin( pObj, pFanin, i )
        Abc_ObjAddFanin( pObj->pCopy, Abc_NtkFromBarBufs_rec(pNtkNew, pFanin) );
    return pObj->pCopy;
}
Abc_Ntk_t * Abc_NtkFromBarBufsInt( Abc_Ntk_t * pNtkBase, Abc_Ntk_t * pNtk, int fRoot )
{
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pObj, * pTerm, * pLatch, * pNet;
    int i, k;
    // start the network
    pNtkNew = Abc_NtkAlloc( pNtk->ntkType, pNtk->ntkFunc, 1 );
    // clone CIs/CIs/boxes
    if ( fRoot )
    {
        pNtkNew->pName = Extra_UtilStrsav(pNtk->pName);
        pNtkNew->pSpec = Extra_UtilStrsav(pNtk->pSpec);
        Abc_NtkCleanCopy( pNtk );
        Abc_NtkForEachCi( pNtk, pObj, i )
            Abc_NtkDupObj( pNtkNew, pObj, 1 );
        Abc_NtkForEachCo( pNtk, pObj, i )
            Abc_NtkDupObj( pNtkNew, pObj, 1 );
    }
    else
    {
        pNtkNew->pName = Extra_UtilStrsav(pNtkBase->pName);
        pNtkNew->pSpec = Extra_UtilStrsav(pNtkBase->pSpec);
        Abc_NtkForEachCi( pNtkBase, pObj, i )
            Abc_NtkDupObj( pNtkNew, pObj, 1 );
        Abc_NtkForEachCo( pNtkBase, pObj, i )
            Abc_NtkDupObj( pNtkNew, pObj, 1 );
    }
    Abc_NtkForEachBox( pNtkBase, pObj, i )
    {
        Abc_NtkDupObj( pNtkNew, pObj, 1 );
        Abc_ObjForEachFanout( pObj, pTerm, k )
        {
            pNet = Abc_ObjFanout0(pTerm);
            assert( Abc_ObjIsNet(pNet) );
            Abc_NtkDupObj( pNtkNew, pNet, 0 );
            pLatch = Abc_NtkCi( Abc_ObjModel(pObj), k )->pNext;
            assert( Abc_ObjIsLatch(pLatch) );
            assert( Abc_ObjIsCi(Abc_ObjFanout0(pLatch)->pCopy) );
            Abc_ObjAddFanin( Abc_ObjFanout0(pLatch)->pCopy, pObj->pCopy );
            Abc_ObjAddFanin( pNet->pCopy, Abc_ObjFanout0(pLatch)->pCopy );
            assert( Abc_ObjFanout0(Abc_ObjFanout0(pLatch))->pCopy == NULL );
            Abc_ObjFanout0(Abc_ObjFanout0(pLatch))->pCopy = pNet->pCopy;
        }
    }
    // build PO cones
    if ( fRoot )
    {
        Abc_NtkForEachPo( pNtk, pObj, i )
            Abc_ObjAddFanin( pObj->pCopy, Abc_NtkFromBarBufs_rec(pNtkNew, Abc_ObjFanin0(pObj)) );
    }
    else
    {
        Abc_NtkForEachPo( pNtkBase, pObj, i )
        {
            pLatch = pObj->pNext;
            assert( Abc_ObjIsLatch(pLatch) );
            Abc_ObjAddFanin( pObj->pCopy, Abc_ObjFanin0(pLatch)->pCopy );
            Abc_ObjAddFanin( Abc_ObjFanin0(pLatch)->pCopy, Abc_NtkFromBarBufs_rec(pNtkNew, Abc_ObjFanin0(Abc_ObjFanin0(pLatch))) );
        }
    }
    // build BI cones
    Abc_NtkForEachBox( pNtkBase, pObj, i )
    {
        Abc_ObjForEachFanin( pObj, pTerm, k )
        {
            pNet = Abc_ObjFanin0(pTerm);
            assert( Abc_ObjIsNet(pNet) );
            pLatch = Abc_NtkCo( Abc_ObjModel(pObj), k )->pNext;
            assert( Abc_ObjIsLatch(pLatch) );
            assert( Abc_ObjIsCo(Abc_ObjFanin0(pLatch)->pCopy) );
            Abc_ObjAddFanin( pObj->pCopy, Abc_ObjFanin0(pLatch)->pCopy );
            Abc_ObjAddFanin( Abc_ObjFanin0(pLatch)->pCopy, Abc_NtkFromBarBufs_rec(pNtkNew, Abc_ObjFanin0(Abc_ObjFanin0(pLatch))) );
        }
    }
    return (pNtkBase->pCopy = pNtkNew);
}
Abc_Ntk_t * Abc_NtkFromBarBufs( Abc_Ntk_t * pNtkBase, Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkNew, * pTemp;
    Vec_Ptr_t * vPiPos;
    Abc_Obj_t * pObj;
    int i, k;
    assert( pNtkBase->pDesign != NULL );
    assert( Abc_NtkIsNetlist(pNtk) );
    assert( Abc_NtkIsNetlist(pNtkBase) );
    assert( Abc_NtkLatchNum(pNtkBase) == 0 );
    assert( Abc_NtkLatchNum(pNtk) == pNtk->nBarBufs );
    assert( Abc_NtkCiNum(pNtk) == Abc_NtkCiNum(pNtkBase) );
    assert( Abc_NtkCoNum(pNtk) == Abc_NtkCoNum(pNtkBase) );
    // annotate PIs/POs of base with flops from optimized network
    vPiPos = Abc_NtkCollectPiPos( pNtkBase );
    assert( Vec_PtrSize(vPiPos) == Abc_NtkLatchNum(pNtk) );
    Abc_NtkCleanCopy_rec( pNtkBase );
    Abc_NtkCleanNext_rec( pNtkBase );
    Vec_PtrForEachEntry( Abc_Obj_t *, vPiPos, pObj, i )
        pObj->pNext = Abc_NtkBox( pNtk, i );
    Vec_PtrFree( vPiPos );
    // duplicate the networks
    pNtkNew = Abc_NtkFromBarBufsInt( pNtkBase, pNtk, 1 );
    pNtkNew->pDesign = Abc_LibCreate( pNtkBase->pDesign->pName );
    Abc_LibAddModel( pNtkNew->pDesign, pNtkNew );
    Vec_PtrPush( pNtkNew->pDesign->vTops, pNtkNew );
    Vec_PtrForEachEntry( Abc_Ntk_t *, pNtkBase->pDesign->vModules, pTemp, i )
        if ( pTemp != pNtkBase )
        {
            pTemp = Abc_NtkFromBarBufsInt( pTemp, pNtk, 0 );
            Abc_LibAddModel( pNtkNew->pDesign, pTemp );
        }
    // set node models
    Vec_PtrForEachEntry( Abc_Ntk_t *, pNtkBase->pDesign->vModules, pTemp, i )
        Abc_NtkForEachBox( pTemp, pObj, k )
            pObj->pCopy->pData = Abc_ObjModel(pObj)->pCopy;
    return pNtkNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

