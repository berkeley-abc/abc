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

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
 
////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
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
    // start the network
    if ( !Abc_NtkHasMapping(pNtk) )
        pNtkNew = Abc_NtkStartFrom( pNtk, ABC_TYPE_LOGIC, ABC_FUNC_SOP );
    else
        pNtkNew = Abc_NtkStartFrom( pNtk, ABC_TYPE_LOGIC, ABC_FUNC_MAP );
    // duplicate the nodes 
    Abc_NtkForEachNode( pNtk, pObj, i )
        Abc_NtkDupObj(pNtkNew, pObj);
    // reconnect the internal nodes in the new network
    Abc_NtkForEachNode( pNtk, pObj, i )
        Abc_ObjForEachFanin( pObj, pFanin, k )
            Abc_ObjAddFanin( pObj->pCopy, Abc_ObjFanin0(pFanin)->pCopy );
    // collect the CO nodes
    Abc_NtkFinalize( pNtk, pNtkNew );
    // fix the problem with CO pointing directing to CIs
    Abc_NtkLogicMakeSimpleCos( pNtkNew, 0 );
    // duplicate EXDC 
    if ( pNtk->pExdc )
        pNtkNew->pExdc = Abc_NtkNetlistToLogic( pNtk->pExdc );
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkNetlistToLogic(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Transform the logic network into a netlist.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkLogicToNetlist( Abc_Ntk_t * pNtk )
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
        Abc_NtkBddToSop(pNtk);
        pNtkNew = Abc_NtkLogicSopToNetlist( pNtk );
        Abc_NtkSopToBdd(pNtk);
    }
    else 
        pNtkNew = Abc_NtkLogicSopToNetlist( pNtk );
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
    char * pNameCo;
    int i, k;

    assert( Abc_NtkIsLogic(pNtk) );
    assert( Abc_NtkLogicHasSimpleCos(pNtk) );

    if ( Abc_NtkIsBddLogic(pNtk) )
        Abc_NtkBddToSop(pNtk);

    // start the netlist by creating PI/PO/Latch objects
    if ( Abc_NtkIsSopLogic(pNtk) )
        pNtkNew = Abc_NtkStartFrom( pNtk, ABC_TYPE_NETLIST, ABC_FUNC_SOP );
    else
        pNtkNew = Abc_NtkStartFrom( pNtk, ABC_TYPE_NETLIST, ABC_FUNC_BDD );
    // create the CI nets and remember them in the new CI nodes
    Abc_NtkForEachCi( pNtk, pObj, i )
    {
        pNet = Abc_NtkFindOrCreateNet( pNtkNew, Abc_ObjName(pObj) );
        Abc_ObjAddFanin( pNet, pObj->pCopy );
        pObj->pCopy->pCopy = pNet;
    }
    // duplicate all nodes
    Abc_NtkForEachNode( pNtk, pObj, i )
        Abc_NtkDupObj(pNtkNew, pObj);
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
        // the driver is a node

        // get the CO name
        pNameCo = Abc_ObjIsPo(pObj)? Abc_ObjName(pObj) : Abc_ObjNameSuffix( pObj, "_in" );
        // make sure CO has a unique name
        assert( Abc_NtkFindNet( pNtkNew, pNameCo ) == NULL );
        // create the CO net and connect it to CO
        pNet = Abc_NtkFindOrCreateNet( pNtkNew, pNameCo );
        Abc_ObjAddFanin( pObj->pCopy, pNet );
        // connect the CO net to the new driver and remember it in the new driver
        Abc_ObjAddFanin( pNet, pDriver->pCopy );
        pDriver->pCopy->pCopy = pNet;
    }
    // create the missing nets
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
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
        pNtkNew->pExdc = Abc_NtkLogicToNetlist( pNtk->pExdc );
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
    int i, k;
    assert( Abc_NtkIsStrash(pNtk) );
    // start the network
    pNtkNew = Abc_NtkStartFrom( pNtk, ABC_TYPE_LOGIC, ABC_FUNC_SOP );
    // create the constant node
    Abc_NtkDupConst1( pNtk, pNtkNew );
    // duplicate the nodes and create node functions
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        if ( Abc_NodeIsConst(pObj) )
            continue;
        Abc_NtkDupObj(pNtkNew, pObj);
        pObj->pCopy->pData = Abc_SopCreateAnd2( pNtkNew->pManFunc, Abc_ObjFaninC0(pObj), Abc_ObjFaninC1(pObj) );
    }
    // create the choice nodes
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        if ( Abc_NodeIsConst(pObj) )
            continue;
        if ( !Abc_NodeIsAigChoice(pObj) )
            continue;
        // create an OR gate
        pNodeNew = Abc_NtkCreateNode(pNtkNew);
        // add fanins
        Vec_IntClear( pNtk->vIntTemp );
        for ( pFanin = pObj; pFanin; pFanin = pFanin->pData )
        {
            Vec_IntPush( pNtk->vIntTemp, (int)(pObj->fPhase != pFanin->fPhase) );
            Abc_ObjAddFanin( pNodeNew, pFanin->pCopy );
        }
        // create the logic function
        pNodeNew->pData = Abc_SopCreateOrMultiCube( pNtkNew->pManFunc, pNtk->vIntTemp->nSize, pNtk->vIntTemp->pArray );
        // set the new node
        pObj->pCopy->pCopy = pNodeNew;
    }
    // connect the internal nodes
    Abc_NtkForEachNode( pNtk, pObj, i )
        Abc_ObjForEachFanin( pObj, pFanin, k )
            if ( pFanin->pCopy->pCopy )
                Abc_ObjAddFanin( pObj->pCopy, pFanin->pCopy->pCopy );
            else
                Abc_ObjAddFanin( pObj->pCopy, pFanin->pCopy );
    // connect the COs
    Abc_NtkFinalize( pNtk, pNtkNew );
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
    pNtkNew = Abc_NtkStartFrom( pNtk, ABC_TYPE_LOGIC, ABC_FUNC_SOP );
    // create the constant node
    Abc_NtkDupConst1( pNtk, pNtkNew );
    // collect the nodes to be used (marks all nodes with current TravId)
    vNodes = Abc_NtkDfs( pNtk, 0 );
    // create inverters for the CI and remember them
    Abc_NtkForEachCi( pNtk, pObj, i )
        if ( Abc_AigNodeHasComplFanoutEdgeTrav(pObj) )
            pObj->pCopy->pCopy = Abc_NodeCreateInv( pNtkNew, pObj->pCopy );
    // duplicate the nodes, create node functions, and inverters
    Vec_PtrForEachEntry( vNodes, pObj, i )
    {
        if ( !Abc_NodeIsConst(pObj) )
        {
            Abc_NtkDupObj( pNtkNew, pObj );
            pObj->pCopy->pData = Abc_SopCreateAnd( pNtkNew->pManFunc, 2 );
        }
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

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


