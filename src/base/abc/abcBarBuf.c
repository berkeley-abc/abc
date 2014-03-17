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

#define ABC_OBJ_VOID ((Abc_Obj_t *)(ABC_PTRINT_T)1)

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
void Abc_NtkCollectPiPos_rec( Abc_Obj_t * pNet, Vec_Ptr_t * vBiBos, Vec_Ptr_t * vPiPos )
{
    extern void Abc_NtkCollectPiPos_int( Abc_Obj_t * pBox, Abc_Ntk_t * pNtk, Vec_Ptr_t * vBiBos, Vec_Ptr_t * vPiPos );
    Abc_Obj_t * pObj, * pFanin; int i;
    assert( Abc_ObjIsNet(pNet) );
    if ( Abc_NodeIsTravIdCurrent( pNet ) )
        return;
    Abc_NodeSetTravIdCurrent( pNet );
    pObj = Abc_ObjFanin0(pNet);
    if ( Abc_ObjIsBo(pObj) )
        pObj = Abc_ObjFanin0(pObj);
    assert( Abc_ObjIsNode(pObj) || Abc_ObjIsBox(pObj) );
    Abc_ObjForEachFanin( pObj, pFanin, i )
        Abc_NtkCollectPiPos_rec( Abc_ObjIsNode(pObj) ? pFanin : Abc_ObjFanin0(pFanin), vBiBos, vPiPos );
    if ( Abc_ObjIsNode(pObj) )
        return;
    Abc_ObjForEachFanin( pObj, pFanin, i )
        Abc_NtkCollectPiPos_rec( Abc_ObjFanin0(pFanin), vBiBos, vPiPos );
    Abc_NtkCollectPiPos_int( pObj, Abc_ObjModel(pObj), vBiBos, vPiPos );
}
void Abc_NtkCollectPiPos_int( Abc_Obj_t * pBox, Abc_Ntk_t * pNtk, Vec_Ptr_t * vBiBos, Vec_Ptr_t * vPiPos )
{
    Abc_Obj_t * pObj; int i;
    // mark primary inputs
    Abc_NtkIncrementTravId( pNtk );
    Abc_NtkForEachPi( pNtk, pObj, i )
        Abc_NodeSetTravIdCurrent( Abc_ObjFanout0(pObj) );
    // add primary inputs
    if ( pBox )
    {
        Abc_ObjForEachFanin( pBox, pObj, i )
            Vec_PtrPush( vBiBos, pObj );
        Abc_NtkForEachPi( pNtk, pObj, i )
            Vec_PtrPush( vPiPos, pObj );
    }
    // visit primary outputs
    Abc_NtkForEachPo( pNtk, pObj, i )
        Abc_NtkCollectPiPos_rec( Abc_ObjFanin0(pObj), vBiBos, vPiPos );
    // add primary outputs
    if ( pBox )
    {
        Abc_ObjForEachFanout( pBox, pObj, i )
            Vec_PtrPush( vBiBos, pObj );
        Abc_NtkForEachPo( pNtk, pObj, i )
            Vec_PtrPush( vPiPos, pObj );
    }
}
void Abc_NtkCollectPiPos( Abc_Ntk_t * pNtk, Vec_Ptr_t ** pvBiBos, Vec_Ptr_t ** pvPiPos )
{
    assert( Abc_NtkIsNetlist(pNtk) );
    *pvBiBos = Vec_PtrAlloc( 1000 );
    *pvPiPos = Vec_PtrAlloc( 1000 );
    Abc_NtkCollectPiPos_int( NULL, pNtk, *pvBiBos, *pvPiPos );
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
    pNet->pCopy = ABC_OBJ_VOID;
    pObj = Abc_ObjFanin0(pNet);
    if ( Abc_ObjIsBo(pObj) )
        pObj = Abc_ObjFanin0(pObj);
    assert( Abc_ObjIsNode(pObj) || Abc_ObjIsBox(pObj) );
    Abc_ObjForEachFanin( pObj, pFanin, i )
        Abc_NtkToBarBufs_rec( pNtkNew, Abc_ObjIsNode(pObj) ? pFanin : Abc_ObjFanin0(pFanin) );
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
        pLatch = Abc_NtkAddLatch( pNtkNew, Abc_ObjFanin0(pFanin)->pCopy, ABC_INIT_ZERO );
        Abc_ObjFanout0(Abc_NtkPi(pModel, i))->pCopy = Abc_ObjFanout0(pLatch);
    }
    Abc_NtkForEachPo( pModel, pObj, i )
        Abc_NtkToBarBufs_rec( pNtkNew, Abc_ObjFanin0(pObj) );
    Abc_ObjForEachFanout( pObj, pFanout, i )
    {
        pLatch = Abc_NtkAddLatch( pNtkNew, Abc_ObjFanin0(Abc_NtkPo(pModel, i))->pCopy, ABC_INIT_ZERO );
        Abc_ObjFanout0(pFanout)->pCopy = Abc_ObjFanout0(pLatch);
    }
    assert( pNet->pCopy != ABC_OBJ_VOID );
}
Abc_Ntk_t * Abc_NtkToBarBufs( Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pObj;
    int i;
    assert( Abc_NtkIsNetlist(pNtk) );
    if ( !Abc_NtkCheckSingleInstance(pNtk) )
        return NULL;
    // start the network
    pNtkNew = Abc_NtkAlloc( ABC_NTK_LOGIC, pNtk->ntkFunc, 1 );
    pNtkNew->pName = Extra_UtilStrsav(pNtk->pName);
    pNtkNew->pSpec = Extra_UtilStrsav(pNtk->pSpec);
    // clone CIs/CIs/boxes
    Abc_NtkCleanCopy( pNtk );
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
Abc_Ntk_t * Abc_NtkFromBarBufsInt( Abc_Ntk_t * pNtkBase, Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pObj;  
    int i;
    // start the network
    pNtkNew = Abc_NtkStartFrom( pNtkBase, pNtk->ntkType, pNtk->ntkFunc );
    // move copy pointers
    Abc_NtkForEachCi( pNtkBase, pObj, i )
        pObj->pNext->pCopy = pObj->pCopy;
    Abc_NtkForEachCo( pNtkBase, pObj, i )
        pObj->pNext->pCopy = pObj->pCopy;
    // construct the network
    Abc_NtkForEachCo( pNtkBase, pObj, i )
        Abc_ObjAddFanin( pObj->pCopy, Abc_NtkFromBarBufs_rec(pNtkNew, Abc_ObjFanin0(pObj->pNext)) );
    return (pNtkBase->pCopy = pNtkNew);
}
Abc_Ntk_t * Abc_NtkFromBarBufs( Abc_Ntk_t * pNtkBase, Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkNew, * pTemp;
    Vec_Ptr_t * vBiBos, * vPiPos;
    Abc_Obj_t * pObj;
    int i, k;
    assert( pNtkBase->pDesign != NULL );
    assert( Abc_NtkIsNetlist(pNtk) );
    assert( Abc_NtkIsNetlist(pNtkBase) );
    assert( Abc_NtkLatchNum(pNtkBase) == 0 );
    assert( Abc_NtkLatchNum(pNtk) == pNtk->nBarBufs );
    assert( Abc_NtkPiNum(pNtk) == Abc_NtkPiNum(pNtkBase) );
    assert( Abc_NtkPoNum(pNtk) == Abc_NtkPoNum(pNtkBase) );
    assert( Abc_NtkCiNum(pNtk) == Abc_NtkCiNum(pNtkBase) );
    assert( Abc_NtkCoNum(pNtk) == Abc_NtkCoNum(pNtkBase) );
    // annotate PIs/POs of base with flops from optimized network
    Abc_NtkCollectPiPos( pNtkBase, &vBiBos, &vPiPos );
    assert( Vec_PtrSize(vBiBos) == Abc_NtkLatchNum(pNtk) );
    assert( Vec_PtrSize(vPiPos) == Abc_NtkLatchNum(pNtk) );
    Abc_NtkCleanCopy_rec( pNtkBase );
    Abc_NtkCleanNext_rec( pNtkBase );
    Abc_NtkForEachPi( pNtk, pObj, i )
        Abc_NtkPi(pNtkBase, i)->pNext = pObj;
    Abc_NtkForEachPo( pNtk, pObj, i )
        Abc_NtkPo(pNtkBase, i)->pNext = pObj;
    Abc_NtkForEachLatch( pNtk, pObj, i )
    {
        ((Abc_Obj_t *)Vec_PtrEntry(vBiBos, i))->pNext = Abc_ObjFanin0(pObj);
        ((Abc_Obj_t *)Vec_PtrEntry(vPiPos, i))->pNext = Abc_ObjFanout0(pObj);
    }
    Vec_PtrFree( vBiBos );
    Vec_PtrFree( vPiPos );
    // duplicate the networks
    pNtkNew = Abc_NtkFromBarBufsInt( pNtkBase, pNtk );
    // finalize the design
    pNtkNew->pDesign = Abc_LibCreate( pNtkBase->pDesign->pName );
    Abc_LibAddModel( pNtkNew->pDesign, pNtkNew );
    Vec_PtrPush( pNtkNew->pDesign->vTops, pNtkNew );
    Vec_PtrForEachEntry( Abc_Ntk_t *, pNtkBase->pDesign->vModules, pTemp, i )
        if ( pTemp != pNtkBase )
        {
            pTemp = Abc_NtkFromBarBufsInt( pTemp, pNtk );
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

