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

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern Abc_Ntk_t * Abc_NtkFlattenLogicHierarchy( Abc_Ntk_t * pNtk );
extern Abc_Ntk_t * Abc_NtkConvertBlackboxes( Abc_Ntk_t * pNtk );
extern void        Abc_NtkInsertNewLogic( Abc_Ntk_t * pNtkHie, Abc_Ntk_t * pNtk );

static void Abc_NtkFlattenLogicHierarchy_rec( Abc_Ntk_t * pNtkNew, Abc_Ntk_t * pNtkOld, int * pCounter );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Flattens the logic hierarchy of the netlist.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkFlattenLogicHierarchy( Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkNew; 
    Abc_Obj_t * pObj, * pNet;
    int i, Counter = 0;
    assert( Abc_NtkIsNetlist(pNtk) );
    // start the network
    pNtkNew = Abc_NtkAlloc( pNtk->ntkType, pNtk->ntkFunc, 1 );
    // duplicate the name and the spec
    pNtkNew->pName = Extra_UtilStrsav(pNtk->pName);
    pNtkNew->pSpec = Extra_UtilStrsav(pNtk->pSpec);
    // clean the node copy fields
    Abc_NtkCleanCopy( pNtk );
    // duplicate PIs/POs and their nets
    Abc_NtkForEachPi( pNtk, pObj, i )
    {
        Abc_NtkDupObj( pNtkNew, pObj, 0 );
        pNet = Abc_ObjFanout0( pObj );
        Abc_NtkDupObj( pNtkNew, pNet, 1 );
        Abc_ObjAddFanin( pNet->pCopy, pObj->pCopy );
    }
    Abc_NtkForEachPo( pNtk, pObj, i )
    {
        Abc_NtkDupObj( pNtkNew, pObj, 0 );
        pNet = Abc_ObjFanin0( pObj );
        pNet->pCopy = Abc_NtkFindOrCreateNet( pNtkNew, Abc_ObjName(pNet) );
        Abc_ObjAddFanin( pObj->pCopy, pNet->pCopy );
    }
    // recursively flatten hierarchy, create internal logic, add new PI/PO names if there are black boxes
    Abc_NtkFlattenLogicHierarchy_rec( pNtkNew, pNtk, &Counter );
    printf( "Abc_NtkFlattenLogicHierarchy(): Flattened %d logic boxes. Left %d block boxes.\n", 
        Counter - 1, Abc_NtkBlackboxNum(pNtkNew) );
    // copy the timing information
//    Abc_ManTimeDup( pNtk, pNtkNew );
    // duplicate EXDC 
    if ( pNtk->pExdc )
        printf( "EXDC is not transformed.\n" );
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkFlattenLogicHierarchy(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Recursively flattens the logic hierarchy of the netlist.]

  Description [When this procedure is called, the PI/PO nets of the netlist
  are already assigned.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkFlattenLogicHierarchy_rec( Abc_Ntk_t * pNtkNew, Abc_Ntk_t * pNtkOld, int * pCounter )
{
    Vec_Ptr_t * vNodes;
    Abc_Ntk_t * pNtkModel;
    Abc_Obj_t * pObj, * pTerm, * pFanin, * pNet;
    int i, k;
    (*pCounter)++;
    // collect nodes and boxes in topological order
    vNodes = Abc_NtkDfs( pNtkOld, 0 );
    // duplicate nodes and blackboxes, call recursively for logic boxes
    Vec_PtrForEachEntry( vNodes, pObj, i )
    {
        if ( Abc_ObjIsNode(pObj) )
        {
            // duplicate the node 
            Abc_NtkDupObj( pNtkNew, pObj, 0 );
            Abc_ObjForEachFanin( pObj, pNet, k )
                Abc_ObjAddFanin( pObj->pCopy, pNet->pCopy );
            // duplicate the net
            pNet = Abc_ObjFanout0( pObj );
            pNet->pCopy = Abc_NtkFindOrCreateNet( pNtkNew, Abc_ObjName(pNet) );
            Abc_ObjAddFanin( pNet->pCopy, pObj->pCopy );
            continue;
        }
        if ( Abc_ObjIsBlackbox(pObj) )
        {
            // duplicate the box 
            Abc_NtkDupObj( pNtkNew, pObj, 1 );
            // connect the fanins
            Abc_ObjForEachFanin( pObj, pNet, k )
                Abc_ObjAddFanin( pObj->pCopy, pNet->pCopy );
            // duplicate fanout nets and connect them
            Abc_ObjForEachFanout( pObj, pNet, i )
            {
                pNet->pCopy = Abc_NtkFindOrCreateNet( pNtkNew, Abc_ObjName(pNet) );
                Abc_ObjAddFanin( pNet->pCopy, pObj->pCopy );
            }
            continue;
        }
        assert( Abc_ObjIsBox(pObj) );
        pNtkModel = pObj->pData;
        assert( pNtkModel && !Abc_NtkHasBlackbox(pNtkModel) );
        // clean the node copy fields
        Abc_NtkCleanCopy( pNtkModel );
        // consider this blackbox
        // copy the PIs/POs of the box
        Abc_NtkForEachPi( pNtkModel, pTerm, k )
            Abc_ObjFanout(pTerm, k)->pCopy = Abc_ObjFanin(pObj, k);
        Abc_NtkForEachPo( pNtkModel, pTerm, k )
            Abc_ObjFanin(pTerm, k)->pCopy = Abc_ObjFanout(pObj, k);
        // call recursively
        Abc_NtkFlattenLogicHierarchy_rec( pNtkNew, pNtkModel, pCounter );
    }
    // connect the POs
    Abc_NtkForEachPo( pNtkOld, pTerm, k )
        pTerm->pCopy = Abc_ObjFanin0(pTerm)->pCopy;
    Vec_PtrFree( vNodes );
}

/**Function*************************************************************

  Synopsis    [Extracts blackboxes by making them into additional PIs/POs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkConvertBlackboxes( Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pObj, * pNet;
    int i, k;
    assert( Abc_NtkIsNetlist(pNtk) );
    assert( Abc_NtkBlackboxNum(pNtk) == Abc_NtkBoxNum(pNtk) - Abc_NtkLatchNum(pNtk) );
    // start the network
    pNtkNew = Abc_NtkAlloc( pNtk->ntkType, pNtk->ntkFunc, 1 );
    // duplicate the name and the spec
    pNtkNew->pName = Extra_UtilStrsav( pNtk->pName );
    pNtkNew->pSpec = Extra_UtilStrsav( pNtk->pSpec );
    // clean the node copy fields
    Abc_NtkCleanCopy( pNtk );
    // create PIs/POs for the box inputs outputs
    Abc_NtkForEachBlackbox( pNtk, pObj, i )
    {
        pObj->pCopy = pObj; // placeholder
        Abc_ObjForEachFanout( pObj, pNet, k )
        {
            if ( pNet->pCopy )
                continue;
            pNet->pCopy = Abc_NtkCreatePi( pNtkNew );
            Abc_ObjAssignName( pNet->pCopy, Abc_ObjName(pNet), NULL );
        }
        Abc_ObjForEachFanin( pObj, pNet, k )
        {
            if ( pNet->pCopy )
                continue;
            pNet->pCopy = Abc_NtkCreatePo( pNtkNew );
            Abc_ObjAssignName( pNet->pCopy, Abc_ObjName(pNet), NULL );
        }
    }
    // duplicate other objects
    Abc_NtkForEachObj( pNtk, pObj, i )
        if ( pObj->pCopy == NULL )
            Abc_NtkDupObj( pNtkNew, pObj, Abc_ObjIsNet(pObj) );
    // connect all objects





    // duplicate all objects besides the boxes
    Abc_NtkForEachObj( pNtk, pObj, i )
        if ( !Abc_ObjIsBlackbox(pObj) )
            Abc_NtkDupObj( pNtkNew, pObj, Abc_ObjIsNet(pObj) );
    // create PIs/POs for the nets belonging to the boxes
    Abc_NtkForEachBlackbox( pNtk, pObj, i )
    {
        Abc_ObjForEachFanin( pObj, pNet, k )
            if ( !Abc_ObjIsPi(Abc_ObjFanin0(pNet)) )
                Abc_NtkCreatePi(pNtkNew)

    }
    // connect all objects, besides blackboxes
    Abc_NtkForEachObj( pNtk, pObj, i )
    {
        if ( !Abc_ObjIsBlackbox(pObj) )
            continue;
        Abc_ObjForEachFanin( pObj, pNet, k )
            Abc_ObjAddFanin( pObj->pCopy, pNet->pCopy );
    }
    if ( !Abc_NtkCheck( pNtkHie ) )
        fprintf( stdout, "Abc_NtkInsertNewLogic(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Inserts blackboxes into the netlist.]

  Description [The first arg is the netlist with blackboxes without logic hierarchy.
  The second arg is a non-hierarchical netlist derived from logic network after processing.
  This procedure inserts the logic back into the original hierarhical netlist.
  The result is updated original hierarchical netlist.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkInsertNewLogic( Abc_Ntk_t * pNtkHie, Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj, * pNet, * pNetLogic;
    int i, k;
    assert( Abc_NtkIsNetlist(pNtkHie) );
    assert( Abc_NtkIsNetlist(pNtk) );
    assert( Abc_NtkBlackboxNum(pNtk) == 0 );
    Abc_NtkCleanCopy( pNtk );
    // mark PIs/POs/blackboxes and their nets
    // map the nets into the corresponding nets of the logic design
    Abc_NtkForEachPi( pNtkHie, pObj, i )
    {
        pObj->fMarkA = 1;
        pNet = Abc_ObjFanout0(pObj);
        pNet->fMarkA = 1;
        pNetLogic = Abc_NtkFindNet( pNtk, Abc_ObjName(pNet) );
        assert( pNetLogic );
        pNetLogic->pCopy = pNet;
    }
    Abc_NtkForEachPo( pNtkHie, pObj, i )
    {
        pObj->fMarkA = 1;
        pNet = Abc_ObjFanin0(pObj);
        pNet->fMarkA = 1;
        pNetLogic = Abc_NtkFindNet( pNtk, Abc_ObjName(pNet) );
        assert( pNetLogic );
        pNetLogic->pCopy = pNet;
    }
    Abc_NtkForEachBlackbox( pNtkHie, pObj, i )
    {
        pObj->fMarkA = 1;
        Abc_ObjForEachFanin( pObj, pNet, k )
        {
            pNet->fMarkA = 1;
            pNetLogic = Abc_NtkFindNet( pNtk, Abc_ObjName(pNet) );
            assert( pNetLogic );
            pNetLogic->pCopy = pNet;
        }
        Abc_ObjForEachFanout( pObj, pNet, k )
        {
            pNet->fMarkA = 1;
            pNetLogic = Abc_NtkFindNet( pNtk, Abc_ObjName(pNet) );
            assert( pNetLogic );
            pNetLogic->pCopy = pNet;
        }
    }
    // remove all other logic fro the hierarchical netlist
    Abc_NtkForEachObj( pNtkHie, pObj, i )
    {
        if ( pObj->fMarkA )
            pObj->fMarkA = 0;
        else
            Abc_NtkDeleteObj( pObj );
    }
    // mark PI/PO nets of the network
    Abc_NtkForEachPi( pNtk, pObj, i )
        Abc_ObjFanout0(pObj)->fMarkA = 1;
    Abc_NtkForEachPo( pNtk, pObj, i )
        Abc_ObjFanin0(pObj)->fMarkA = 1;
    // make sure only these nodes are assigned the copy
    Abc_NtkForEachObj( pNtk, pObj, i )
    {
        assert( pObj->fMarkA == (pObj->pCopy != NULL) );
        pObj->fMarkA = 0;
        if ( pObj->pCopy )
            continue;
        if ( Abc_ObjIsPi(pObj) || Abc_ObjIsPi(pObj) )
            continue;
        Abc_NtkDupObj( pNtkHie, pObj, 0 );
    }
    // connect all the nodes, except the PIs and POs
    Abc_NtkForEachObj( pNtk, pObj, i )
    {
        if ( Abc_ObjIsPi(pObj) || Abc_ObjIsPi(pObj) )
            continue;
        Abc_ObjForEachFanin( pObj, pNet, k )
            Abc_ObjAddFanin( pObj->pCopy, pNet->pCopy );
    }
    if ( !Abc_NtkCheck( pNtkHie ) )
    {
        fprintf( stdout, "Abc_NtkInsertNewLogic(): Network check has failed.\n" );
        return 0;
    }
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


