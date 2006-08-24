/**CFile****************************************************************

  FileName    [abcNetlist.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Transforms netlist into a logic network and vice versa.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcNetlist.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "seq.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Abc_Ntk_t * Abc_NtkNetlistToLogicHie( Abc_Ntk_t * pNtk );
static void Abc_NtkNetlistToLogicHie_rec( Abc_Ntk_t * pNtkNew, Abc_Ntk_t * pNtkOld, int * pCounter );
static void Abc_NtkAddPoBuffers( Abc_Ntk_t * pNtk );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Transform the netlist into a logic network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkNetlistToLogic( Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkNew; 
    Abc_Obj_t * pObj, * pFanin;
    int i, k;
    assert( Abc_NtkIsNetlist(pNtk) );
    // consider simple case when there is hierarchy
    if ( pNtk->tName2Model )
        return Abc_NtkNetlistToLogicHie( pNtk );
    // start the network
    if ( Abc_NtkHasMapping(pNtk) )
        pNtkNew = Abc_NtkStartFrom( pNtk, ABC_NTK_LOGIC, ABC_FUNC_MAP );
    else
        pNtkNew = Abc_NtkStartFrom( pNtk, ABC_NTK_LOGIC, pNtk->ntkFunc );
    // duplicate the nodes 
    Abc_NtkForEachNode( pNtk, pObj, i )
        Abc_NtkDupObj(pNtkNew, pObj, 0);
    // reconnect the internal nodes in the new network
    Abc_NtkForEachNode( pNtk, pObj, i )
        Abc_ObjForEachFanin( pObj, pFanin, k )
            Abc_ObjAddFanin( pObj->pCopy, Abc_ObjFanin0(pFanin)->pCopy );
    // collect the CO nodes
    Abc_NtkFinalize( pNtk, pNtkNew );
    // fix the problem with CO pointing directly to CIs
    Abc_NtkLogicMakeSimpleCos( pNtkNew, 0 );
    // duplicate EXDC 
    if ( pNtk->pExdc )
        pNtkNew->pExdc = Abc_NtkNetlistToLogic( pNtk->pExdc );
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkNetlistToLogic(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Transform the netlist into a logic network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkNetlistToLogicHie( Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkNew; 
    Abc_Obj_t * pObj;
    int i, Counter = 0;
    assert( Abc_NtkIsNetlist(pNtk) );
    // start the network
//    pNtkNew = Abc_NtkAlloc( Type, Func, 1 );
    if ( !Abc_NtkHasMapping(pNtk) )
        pNtkNew = Abc_NtkAlloc( ABC_NTK_LOGIC, ABC_FUNC_SOP, 1 );
    else
        pNtkNew = Abc_NtkAlloc( ABC_NTK_LOGIC, ABC_FUNC_MAP, 1 );
    // duplicate the name and the spec
    pNtkNew->pName = Extra_UtilStrsav(pNtk->pName);
    pNtkNew->pSpec = Extra_UtilStrsav(pNtk->pSpec);
    // clean the node copy fields
    Abc_NtkForEachNode( pNtk, pObj, i )
        pObj->pCopy = NULL;
    // clone PIs/POs/latches and make old nets point to new terminals; create names
    Abc_NtkForEachCi( pNtk, pObj, i )
    {
        Abc_ObjFanout0(pObj)->pCopy = Abc_NtkDupObj(pNtkNew, pObj, 0);
        Abc_ObjAssignName( pObj->pCopy, Abc_ObjName(Abc_ObjFanout0(pObj)), NULL );
    }
    Abc_NtkForEachPo( pNtk, pObj, i )
    {
        Abc_NtkDupObj(pNtkNew, pObj, 0);
        Abc_ObjAssignName( pObj->pCopy, Abc_ObjName(Abc_ObjFanin0(pObj)), NULL );
    }
    // recursively flatten hierarchy, create internal logic, add new PI/PO names if there are black boxes
    Abc_NtkNetlistToLogicHie_rec( pNtkNew, pNtk, &Counter );
    if ( Counter )
        printf( "Warning: The total of %d block boxes are transformed into PI/PO pairs.\n", Counter );
    // connect the CO nodes
    Abc_NtkForEachCo( pNtk, pObj, i )
        Abc_ObjAddFanin( pObj->pCopy, Abc_ObjFanin0(pObj)->pCopy );
    // copy the timing information
    Abc_ManTimeDup( pNtk, pNtkNew );
    // fix the problem with CO pointing directly to CIs
    Abc_NtkLogicMakeSimpleCos( pNtkNew, 0 );
    // duplicate EXDC 
    if ( pNtk->pExdc )
        pNtkNew->pExdc = Abc_NtkNetlistToLogic( pNtk->pExdc );
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkNetlistToLogic(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Transform the netlist into a logic network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkNetlistToLogicHie_rec( Abc_Ntk_t * pNtkNew, Abc_Ntk_t * pNtkOld, int * pCounter )
{
    char Prefix[1000];
    Vec_Ptr_t * vNodes;
    Abc_Ntk_t * pNtkModel;
    Abc_Obj_t * pNode, * pObj, * pFanin;
    int i, k;
    // collect nodes and boxes in topological order
    vNodes = Abc_NtkDfs( pNtkOld, 0 );
    // duplicate nodes, create PIs/POs corresponding to blackboxes
    // have to do it first if blackboxes break combinational loops
    // (current we do not allow whiteboxes to break combinational loops)
    Vec_PtrForEachEntry( vNodes, pNode, i )
    {
        if ( Abc_ObjIsNode(pNode) )
        {
            // duplicate the node and save it in the fanout net
            Abc_NtkDupObj( pNtkNew, pNode, 0 );
            Abc_ObjFanout0(pNode)->pCopy = pNode->pCopy;
            continue;
        }
        assert( Abc_ObjIsBox(pNode) );
        pNtkModel = pNode->pData;
        if ( !Abc_NtkHasBlackbox(pNtkModel) )
            continue;
        // consider this blockbox
        if ( pNtkNew->pBlackBoxes == NULL )
        {
            pNtkNew->pBlackBoxes = Vec_IntAlloc( 10 );
            Vec_IntPush( pNtkNew->pBlackBoxes, (Abc_NtkPiNum(pNtkNew) << 16) | Abc_NtkPoNum(pNtkNew) );
        }
        sprintf( Prefix, "%s_%d_", Abc_NtkName(pNtkModel), *pCounter );
        // create new PIs from the POs of the box
        Abc_NtkForEachPo( pNtkModel, pObj, k )
        {
            pObj->pCopy = Abc_NtkCreatePi( pNtkNew );
            Abc_ObjFanout(pNode, k)->pCopy = pObj->pCopy;
            Abc_ObjAssignName( pObj->pCopy, Prefix, Abc_ObjName(Abc_ObjFanin0(pObj)) );
        }
        // create new POs from the PIs of the box
        Abc_NtkForEachPi( pNtkModel, pObj, k )
        {
            pObj->pCopy = Abc_NtkCreatePo( pNtkNew );
//            Abc_ObjAddFanin( pObj->pCopy, Abc_ObjFanin(pNode, k)->pCopy );
            Abc_ObjAssignName( pObj->pCopy, Prefix, Abc_ObjName(Abc_ObjFanout0(pObj)) );
        }
        (*pCounter)++;
        Vec_IntPush( pNtkNew->pBlackBoxes, (Abc_NtkPiNum(pNtkNew) << 16) | Abc_NtkPoNum(pNtkNew) );
    }
    // connect nodes and boxes
    Vec_PtrForEachEntry( vNodes, pNode, i )
    {
        if ( Abc_ObjIsNode(pNode) )
        {
//            printf( "adding node %s\n", Abc_ObjName(Abc_ObjFanout0(pNode)) );
            Abc_ObjForEachFanin( pNode, pFanin, k )
                Abc_ObjAddFanin( pNode->pCopy, pFanin->pCopy );
            continue;
        }
        assert( Abc_ObjIsBox(pNode) );
        pNtkModel = pNode->pData;
//        printf( "adding model %s\n", Abc_NtkName(pNtkModel) );
        // consider the case of the black box
        if ( Abc_NtkHasBlackbox(pNtkModel) )
        {
            // create new POs from the PIs of the box
            Abc_NtkForEachPi( pNtkModel, pObj, k )
                Abc_ObjAddFanin( pObj->pCopy, Abc_ObjFanin(pNode, k)->pCopy );
            continue;
        }
        // transfer the nodes to the box inputs
        Abc_NtkForEachPi( pNtkModel, pObj, k )
            Abc_ObjFanout0(pObj)->pCopy = Abc_ObjFanin(pNode, k)->pCopy;
        // construct recursively
        Abc_NtkNetlistToLogicHie_rec( pNtkNew, pNtkModel, pCounter );
        // transfer the results back
        Abc_NtkForEachPo( pNtkModel, pObj, k )
            Abc_ObjFanout(pNode, k)->pCopy = Abc_ObjFanin0(pObj)->pCopy;    
    }
    Vec_PtrFree( vNodes );
}


/**Function*************************************************************

  Synopsis    [Transform the logic network into a netlist.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkLogicToNetlist( Abc_Ntk_t * pNtk, int fDirect )
{
    Abc_Ntk_t * pNtkNew, * pNtkTemp; 
    assert( Abc_NtkIsLogic(pNtk) || Abc_NtkIsStrash(pNtk) || Abc_NtkIsSeq(pNtk) );
    if ( Abc_NtkIsStrash(pNtk) )
    {
        pNtkTemp = Abc_NtkAigToLogicSop(pNtk);
        pNtkNew = Abc_NtkLogicSopToNetlist( pNtkTemp );
        Abc_NtkDelete( pNtkTemp );
    }
    else if ( Abc_NtkIsSeq(pNtk) )
    {
        pNtkTemp = Abc_NtkSeqToLogicSop(pNtk);
        pNtkNew = Abc_NtkLogicSopToNetlist( pNtkTemp );
        Abc_NtkDelete( pNtkTemp );
    }
    else if ( Abc_NtkIsBddLogic(pNtk) )
    {
        if ( !Abc_NtkBddToSop(pNtk, fDirect) )
            return NULL;
        pNtkNew = Abc_NtkLogicSopToNetlist( pNtk );
        Abc_NtkSopToBdd(pNtk);
    }
    else if ( Abc_NtkIsAigLogic(pNtk) )
    {
        if ( !Abc_NtkAigToBdd(pNtk) )
            return NULL;
        if ( !Abc_NtkBddToSop(pNtk, fDirect) )
            return NULL;
        pNtkNew = Abc_NtkLogicSopToNetlist( pNtk );
        Abc_NtkSopToAig(pNtk);
    }
    else if ( Abc_NtkIsSopLogic(pNtk) || Abc_NtkIsMappedLogic(pNtk) )
        pNtkNew = Abc_NtkLogicSopToNetlist( pNtk );
    else assert( 0 );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Converts the AIG into the netlist.]

  Description [This procedure does not copy the choices.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkLogicToNetlistBench( Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkNew, * pNtkTemp; 
    assert( Abc_NtkIsStrash(pNtk) );
    pNtkTemp = Abc_NtkAigToLogicSopBench( pNtk );
    pNtkNew = Abc_NtkLogicSopToNetlist( pNtkTemp );
    Abc_NtkDelete( pNtkTemp );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Transform the logic network into a netlist.]

  Description [The logic network given to this procedure should
  have exactly the same structure as the resulting netlist. The COs
  can only point to CIs if they have identical names. Otherwise, 
  they should have a node between them, even if this node is 
  inverter or buffer.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkLogicSopToNetlist( Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkNew; 
    Abc_Obj_t * pObj, * pNet, * pDriver, * pFanin;
    int i, k;

    assert( Abc_NtkIsLogic(pNtk) );
    assert( Abc_NtkLogicHasSimpleCos(pNtk) );
    if ( Abc_NtkIsBddLogic(pNtk) )
    {
        if ( !Abc_NtkBddToSop(pNtk,0) )
            return NULL;
    }

    // start the netlist by creating PI/PO/Latch objects
    pNtkNew = Abc_NtkStartFrom( pNtk, ABC_NTK_NETLIST, pNtk->ntkFunc );
    // create the CI nets and remember them in the new CI nodes
    Abc_NtkForEachCi( pNtk, pObj, i )
    {
        pNet = Abc_NtkFindOrCreateNet( pNtkNew, Abc_ObjName(pObj) );
        Abc_ObjAddFanin( pNet, pObj->pCopy );
        pObj->pCopy->pCopy = pNet;
    }
    // duplicate all nodes
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        if ( Abc_ObjFaninNum(pObj) == 0 && Abc_ObjFanoutNum(pObj) == 0 )
            continue;
        Abc_NtkDupObj(pNtkNew, pObj, 0);
    }
    // first add the nets to the CO drivers
    Abc_NtkForEachCo( pNtk, pObj, i )
    {
        pDriver = Abc_ObjFanin0(pObj);
        if ( Abc_ObjIsCi(pDriver) )
        {
            assert( !strcmp( Abc_ObjName(pDriver), Abc_ObjName(pObj) ) );
            Abc_ObjAddFanin( pObj->pCopy, pDriver->pCopy->pCopy );
            continue;
        }
        assert( Abc_ObjIsNode(pDriver) );
        // if the CO drive has no net, create it
        if ( pDriver->pCopy->pCopy == NULL )
        {
            // create the CO net and connect it to CO
            pNet = Abc_NtkFindOrCreateNet( pNtkNew, Abc_ObjName(pObj) );
            Abc_ObjAddFanin( pObj->pCopy, pNet );
            // connect the CO net to the new driver and remember it in the new driver
            Abc_ObjAddFanin( pNet, pDriver->pCopy );
            pDriver->pCopy->pCopy = pNet;
        }
        else
            assert( !strcmp( Abc_ObjName(pDriver->pCopy->pCopy), Abc_ObjName(pObj) ) );
    }
    // create the missing nets
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        if ( Abc_ObjFaninNum(pObj) == 0 && Abc_ObjFanoutNum(pObj) == 0 )
            continue;
        if ( pObj->pCopy->pCopy ) // the net of the new object is already created
            continue;
        // create the new net
        pNet = Abc_NtkFindOrCreateNet( pNtkNew, Abc_ObjName(pObj) );
        Abc_ObjAddFanin( pNet, pObj->pCopy );
        pObj->pCopy->pCopy = pNet;
    }
    // connect nodes to the fanins nets
    Abc_NtkForEachNode( pNtk, pObj, i )
        Abc_ObjForEachFanin( pObj, pFanin, k )
            Abc_ObjAddFanin( pObj->pCopy, pFanin->pCopy->pCopy );
    // duplicate EXDC 
    if ( pNtk->pExdc )
        pNtkNew->pExdc = Abc_NtkLogicToNetlist( pNtk->pExdc, 0 );
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkLogicSopToNetlist(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Converts the AIG into the logic network with SOPs.]

  Description [Correctly handles the case of choice nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkAigToLogicSop( Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkNew; 
    Abc_Obj_t * pObj, * pFanin, * pNodeNew;
    Vec_Int_t * vInts;
    int i, k;
    assert( Abc_NtkIsStrash(pNtk) );
    // start the network
    pNtkNew = Abc_NtkStartFrom( pNtk, ABC_NTK_LOGIC, ABC_FUNC_SOP );
    // if the constant node is used, duplicate it
    pObj = Abc_AigConst1(pNtk);
    if ( Abc_ObjFanoutNum(pObj) > 0 )
        pObj->pCopy = Abc_NodeCreateConst1(pNtkNew);
    // duplicate the nodes and create node functions
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        Abc_NtkDupObj(pNtkNew, pObj, 0);
        pObj->pCopy->pData = Abc_SopCreateAnd2( pNtkNew->pManFunc, Abc_ObjFaninC0(pObj), Abc_ObjFaninC1(pObj) );
    }
    // create the choice nodes
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        if ( !Abc_AigNodeIsChoice(pObj) )
            continue;
        // create an OR gate
        pNodeNew = Abc_NtkCreateNode(pNtkNew);
        // add fanins
        vInts = Vec_IntAlloc( 10 );
        for ( pFanin = pObj; pFanin; pFanin = pFanin->pData )
        {
            Vec_IntPush( vInts, (int)(pObj->fPhase != pFanin->fPhase) );
            Abc_ObjAddFanin( pNodeNew, pFanin->pCopy );
        }
        // create the logic function
        pNodeNew->pData = Abc_SopCreateOrMultiCube( pNtkNew->pManFunc, Vec_IntSize(vInts), Vec_IntArray(vInts) );
        // set the new node
        pObj->pCopy->pCopy = pNodeNew;
        Vec_IntFree( vInts );
    }
    // connect the internal nodes
    Abc_NtkForEachNode( pNtk, pObj, i )
        Abc_ObjForEachFanin( pObj, pFanin, k )
            if ( pFanin->pCopy->pCopy )
                Abc_ObjAddFanin( pObj->pCopy, pFanin->pCopy->pCopy );
            else
                Abc_ObjAddFanin( pObj->pCopy, pFanin->pCopy );
    // connect the COs
//    Abc_NtkFinalize( pNtk, pNtkNew );
    Abc_NtkForEachCo( pNtk, pObj, i )
    {
        pFanin = Abc_ObjFanin0(pObj);
        if ( pFanin->pCopy->pCopy )
            pNodeNew = Abc_ObjNotCond(pFanin->pCopy->pCopy, Abc_ObjFaninC0(pObj));
        else
            pNodeNew = Abc_ObjNotCond(pFanin->pCopy, Abc_ObjFaninC0(pObj));
        Abc_ObjAddFanin( pObj->pCopy, pNodeNew );
    }

    // fix the problem with complemented and duplicated CO edges
    Abc_NtkLogicMakeSimpleCos( pNtkNew, 0 );
    // duplicate the EXDC Ntk
    if ( pNtk->pExdc )
    {
        if ( Abc_NtkIsStrash(pNtk->pExdc) )
            pNtkNew->pExdc = Abc_NtkAigToLogicSop( pNtk->pExdc );
        else
            pNtkNew->pExdc = Abc_NtkDup( pNtk->pExdc );
    }
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkAigToLogicSop(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Converts the AIG into the logic network with SOPs for bench writing.]

  Description [This procedure does not copy the choices.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkAigToLogicSopBench( Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkNew; 
    Abc_Obj_t * pObj, * pFanin;
    Vec_Ptr_t * vNodes;
    int i, k;
    assert( Abc_NtkIsStrash(pNtk) );
    if ( Abc_NtkGetChoiceNum(pNtk) )
        printf( "Warning: Choice nodes are skipped.\n" );
    // start the network
    pNtkNew = Abc_NtkStartFrom( pNtk, ABC_NTK_LOGIC, ABC_FUNC_SOP );
    // collect the nodes to be used (marks all nodes with current TravId)
    vNodes = Abc_NtkDfs( pNtk, 0 );
    // create inverters for the CI and remember them
    pObj = Abc_AigConst1(pNtk);
    if ( Abc_AigNodeHasComplFanoutEdgeTrav(pObj) )
    {
        pObj->pCopy = Abc_NodeCreateConst1(pNtkNew);
        pObj->pCopy->pCopy = Abc_NodeCreateInv( pNtkNew, pObj->pCopy );
    }
    Abc_NtkForEachCi( pNtk, pObj, i )
        if ( Abc_AigNodeHasComplFanoutEdgeTrav(pObj) )
            pObj->pCopy->pCopy = Abc_NodeCreateInv( pNtkNew, pObj->pCopy );
    // duplicate the nodes, create node functions, and inverters
    Vec_PtrForEachEntry( vNodes, pObj, i )
    {
        Abc_NtkDupObj( pNtkNew, pObj, 0 );
        pObj->pCopy->pData = Abc_SopCreateAnd( pNtkNew->pManFunc, 2, NULL );
        if ( Abc_AigNodeHasComplFanoutEdgeTrav(pObj) )
            pObj->pCopy->pCopy = Abc_NodeCreateInv( pNtkNew, pObj->pCopy );
    }
    // connect the objects
    Vec_PtrForEachEntry( vNodes, pObj, i )
        Abc_ObjForEachFanin( pObj, pFanin, k )
        {
            if ( Abc_ObjFaninC( pObj, k ) )
                Abc_ObjAddFanin( pObj->pCopy, pFanin->pCopy->pCopy );
            else
                Abc_ObjAddFanin( pObj->pCopy, pFanin->pCopy );
        }
    Vec_PtrFree( vNodes );
    // connect the COs
    Abc_NtkForEachCo( pNtk, pObj, i )
    {
        pFanin = Abc_ObjFanin0(pObj);
        if ( Abc_ObjFaninC0( pObj ) )
            Abc_ObjAddFanin( pObj->pCopy, pFanin->pCopy->pCopy );
        else
            Abc_ObjAddFanin( pObj->pCopy, pFanin->pCopy );
    }
    // fix the problem with complemented and duplicated CO edges
    Abc_NtkLogicMakeSimpleCos( pNtkNew, 0 );
    // duplicate the EXDC Ntk
    if ( pNtk->pExdc )
        printf( "Warning: The EXDc network is skipped.\n" );
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkAigToLogicSopBench(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Adds buffers for each PO.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkAddPoBuffers( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj, * pFanin, * pFaninNew;
    int i;
    assert( Abc_NtkIsStrash(pNtk) );
    Abc_NtkForEachPo( pNtk, pObj, i )
    {
        pFanin = Abc_ObjChild0(pObj);
        pFaninNew = Abc_NtkCreateNode(pNtk);
        Abc_ObjAddFanin( pFaninNew, pFanin );
        Abc_ObjPatchFanin( pObj, pFanin, pFaninNew );
    }
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


