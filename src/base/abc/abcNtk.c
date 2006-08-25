/**CFile****************************************************************

  FileName    [abcNtk.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Network creation/duplication/deletion procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcNtk.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "abcInt.h"
#include "main.h"
#include "mio.h"
#include "seqInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates a new Ntk.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkAlloc( Abc_NtkType_t Type, Abc_NtkFunc_t Func, int fUseMemMan )
{
    Abc_Ntk_t * pNtk;
    pNtk = ALLOC( Abc_Ntk_t, 1 );
    memset( pNtk, 0, sizeof(Abc_Ntk_t) );
    pNtk->ntkType     = Type;
    pNtk->ntkFunc     = Func;
    // start the object storage
    pNtk->vObjs       = Vec_PtrAlloc( 100 );
    pNtk->vAsserts    = Vec_PtrAlloc( 100 );
    pNtk->vPios       = Vec_PtrAlloc( 100 );
    pNtk->vPis        = Vec_PtrAlloc( 100 );
    pNtk->vPos        = Vec_PtrAlloc( 100 );
    pNtk->vCis        = Vec_PtrAlloc( 100 );
    pNtk->vCos        = Vec_PtrAlloc( 100 );
    pNtk->vCutSet     = Vec_PtrAlloc( 100 );
    pNtk->vBoxes      = Vec_PtrAlloc( 100 );
    pNtk->vSkews      = Vec_FltAlloc( 100 );
    // start the memory managers
    pNtk->pMmObj      = fUseMemMan? Extra_MmFixedStart( sizeof(Abc_Obj_t) ) : NULL;
    pNtk->pMmStep     = fUseMemMan? Extra_MmStepStart( ABC_NUM_STEPS ) : NULL;
    // get ready to assign the first Obj ID
    pNtk->nTravIds    = 1;
    // start the functionality manager
    if ( Abc_NtkIsStrash(pNtk) )
        pNtk->pManFunc = Abc_AigAlloc( pNtk );
    else if ( Abc_NtkIsSeq(pNtk) )
        pNtk->pManFunc = Seq_Create( pNtk );
    else if ( Abc_NtkHasSop(pNtk) )
        pNtk->pManFunc = Extra_MmFlexStart();
    else if ( Abc_NtkHasBdd(pNtk) )
        pNtk->pManFunc = Cudd_Init( 20, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );
    else if ( Abc_NtkHasAig(pNtk) )
        pNtk->pManFunc = Aig_ManStart();
    else if ( Abc_NtkHasMapping(pNtk) )
        pNtk->pManFunc = Abc_FrameReadLibGen();
    else if ( !Abc_NtkHasBlackbox(pNtk) )
        assert( 0 );
    // name manager
    pNtk->pManName = Nm_ManCreate( 200 );
    return pNtk;
}

/**Function*************************************************************

  Synopsis    [Starts a new network using existing network as a model.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkStartFrom( Abc_Ntk_t * pNtk, Abc_NtkType_t Type, Abc_NtkFunc_t Func )
{
    Abc_Ntk_t * pNtkNew; 
    Abc_Obj_t * pObj;
    int fCopyNames, i;
    if ( pNtk == NULL )
        return NULL;
    // decide whether to copy the names
    fCopyNames = ( Type != ABC_NTK_NETLIST );
    // start the network
    pNtkNew = Abc_NtkAlloc( Type, Func, 1 );
    // duplicate the name and the spec
    pNtkNew->pName = Extra_UtilStrsav(pNtk->pName);
    pNtkNew->pSpec = Extra_UtilStrsav(pNtk->pSpec);
    // clean the node copy fields
    Abc_NtkCleanCopy( pNtk );
    // map the constant nodes
    if ( Abc_NtkIsStrash(pNtk) && Abc_NtkIsStrash(pNtkNew) )
        Abc_AigConst1(pNtk)->pCopy = Abc_AigConst1(pNtkNew);
    // clone CIs/CIs/boxes
    Abc_NtkForEachPi( pNtk, pObj, i )
        Abc_NtkDupObj( pNtkNew, pObj, fCopyNames );
    Abc_NtkForEachPo( pNtk, pObj, i )
        Abc_NtkDupObj( pNtkNew, pObj, fCopyNames );
    Abc_NtkForEachAssert( pNtk, pObj, i )
        Abc_NtkDupObj( pNtkNew, pObj, fCopyNames );
    Abc_NtkForEachBox( pNtk, pObj, i )
        Abc_NtkDupBox( pNtkNew, pObj, fCopyNames );
    // transfer the names
//    Abc_NtkTrasferNames( pNtk, pNtkNew );
    Abc_ManTimeDup( pNtk, pNtkNew );
    // check that the CI/CO/latches are copied correctly
    assert( Abc_NtkCiNum(pNtk)    == Abc_NtkCiNum(pNtkNew) );
    assert( Abc_NtkCoNum(pNtk)    == Abc_NtkCoNum(pNtkNew) );
    assert( Abc_NtkLatchNum(pNtk) == Abc_NtkLatchNum(pNtkNew) );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Starts a new network using existing network as a model.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkStartFromNoLatches( Abc_Ntk_t * pNtk, Abc_NtkType_t Type, Abc_NtkFunc_t Func )
{
    Abc_Ntk_t * pNtkNew; 
    Abc_Obj_t * pObj;
    int i;
    if ( pNtk == NULL )
        return NULL;
    assert( Type != ABC_NTK_NETLIST );
    // start the network
    pNtkNew = Abc_NtkAlloc( Type, Func, 1 );
    // duplicate the name and the spec
    pNtkNew->pName = Extra_UtilStrsav(pNtk->pName);
    pNtkNew->pSpec = Extra_UtilStrsav(pNtk->pSpec);
    // clean the node copy fields
    Abc_NtkCleanCopy( pNtk );
    // map the constant nodes
    if ( Abc_NtkIsStrash(pNtk) && Abc_NtkIsStrash(pNtkNew) )
        Abc_AigConst1(pNtk)->pCopy = Abc_AigConst1(pNtkNew);
    // clone CIs/CIs/boxes
    Abc_NtkForEachPi( pNtk, pObj, i )
        Abc_NtkDupObj( pNtkNew, pObj, 1 );
    Abc_NtkForEachPo( pNtk, pObj, i )
        Abc_NtkDupObj( pNtkNew, pObj, 1 );
    Abc_NtkForEachAssert( pNtk, pObj, i )
        Abc_NtkDupObj( pNtkNew, pObj, 1 );
    Abc_NtkForEachBox( pNtk, pObj, i )
    {
        if ( Abc_ObjIsLatch(pObj) )
            continue;
        Abc_NtkDupBox(pNtkNew, pObj, 1);
    }
    // transfer the names
//    Abc_NtkTrasferNamesNoLatches( pNtk, pNtkNew );
    Abc_ManTimeDup( pNtk, pNtkNew );
    // check that the CI/CO/latches are copied correctly
    assert( Abc_NtkPiNum(pNtk) == Abc_NtkPiNum(pNtkNew) );
    assert( Abc_NtkPoNum(pNtk) == Abc_NtkPoNum(pNtkNew) );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Finalizes the network using the existing network as a model.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkFinalize( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkNew )
{
    Abc_Obj_t * pObj, * pDriver, * pDriverNew;
    int i;
    // set the COs of the strashed network
    Abc_NtkForEachCo( pNtk, pObj, i )
    {
        pDriver    = Abc_ObjFanin0Ntk( Abc_ObjFanin0(pObj) );
        pDriverNew = Abc_ObjNotCond(pDriver->pCopy, Abc_ObjFaninC0(pObj));
        Abc_ObjAddFanin( pObj->pCopy, pDriverNew );
    }
}

/**Function*************************************************************

  Synopsis    [Starts a new network using existing network as a model.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkStartRead( char * pName )
{
    Abc_Ntk_t * pNtkNew; 
    // allocate the empty network
    pNtkNew = Abc_NtkAlloc( ABC_NTK_NETLIST, ABC_FUNC_SOP, 1 );
    // set the specs
    pNtkNew->pName = Extra_FileNameGeneric(pName);
    pNtkNew->pSpec = Extra_UtilStrsav(pName);
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Finalizes the network using the existing network as a model.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkFinalizeRead( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pBox, * pObj;
    int i;
    if ( Abc_NtkHasBlackbox(pNtk) )
    {
        pBox = Abc_NtkCreateBlackbox(pNtk);
        Abc_NtkForEachPi( pNtk, pObj, i )
            Abc_ObjAddFanin( pBox, Abc_ObjFanout0(pObj) );
        Abc_NtkForEachPo( pNtk, pObj, i )
            Abc_ObjAddFanin( Abc_ObjFanin0(pObj), pBox );
        return;
    }
    assert( Abc_NtkIsNetlist(pNtk) );
    // fix the net drivers
    Abc_NtkFixNonDrivenNets( pNtk );
    // reorder the CI/COs to PI/POs first
    Abc_NtkOrderCisCos( pNtk );
}

/**Function*************************************************************

  Synopsis    [Duplicate the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDup( Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkNew; 
    Abc_Obj_t * pObj, * pFanin;
    int i, k;
    if ( pNtk == NULL )
        return NULL;
    // start the network
    pNtkNew = Abc_NtkStartFrom( pNtk, pNtk->ntkType, pNtk->ntkFunc );
    // copy the internal nodes
    if ( Abc_NtkIsStrash(pNtk) )
    {
        // copy the AND gates
        Abc_AigForEachAnd( pNtk, pObj, i )
            pObj->pCopy = Abc_AigAnd( pNtkNew->pManFunc, Abc_ObjChild0Copy(pObj), Abc_ObjChild1Copy(pObj) );
        // relink the choice nodes
        Abc_AigForEachAnd( pNtk, pObj, i )
            if ( pObj->pData )
                pObj->pCopy->pData = ((Abc_Obj_t *)pObj->pData)->pCopy;
        // relink the CO nodes
        Abc_NtkForEachCo( pNtk, pObj, i )
            Abc_ObjAddFanin( pObj->pCopy, Abc_ObjChild0Copy(pObj) );
        // get the number of nodes before and after
        if ( Abc_NtkNodeNum(pNtk) != Abc_NtkNodeNum(pNtkNew) )
            printf( "Warning: Structural hashing during duplication reduced %d nodes (this is a minor bug).\n",
                Abc_NtkNodeNum(pNtk) - Abc_NtkNodeNum(pNtkNew) );
    }
    else if ( Abc_NtkIsSeq(pNtk) )
    {
        // start the storage for initial states
        Seq_Resize( pNtkNew->pManFunc, Abc_NtkObjNumMax(pNtk) );
        // copy the nodes
        Abc_NtkForEachObj( pNtk, pObj, i )
            if ( pObj->pCopy == NULL )
            {
                Abc_NtkDupObj(pNtkNew, pObj, 0);
                pObj->pCopy->Level = pObj->Level;
                pObj->pCopy->fPhase = pObj->fPhase;
            }
        // connect the nodes
        Abc_NtkForEachObj( pNtk, pObj, i )
        {
            Abc_ObjForEachFanin( pObj, pFanin, k )
            {
                Abc_ObjAddFanin( pObj->pCopy, pFanin->pCopy );
                if ( Abc_ObjFaninC(pObj, k) )
                    Abc_ObjSetFaninC( pObj->pCopy, k );
                if ( Seq_ObjFaninL(pObj, k) )
                    Seq_NodeDupLats( pObj->pCopy, pObj, k );
            }
        }
        // relink the choice nodes
        Abc_AigForEachAnd( pNtk, pObj, i )
            if ( pObj->pData )
                pObj->pCopy->pData = ((Abc_Obj_t *)pObj->pData)->pCopy;
        // copy the cutset
        Abc_SeqForEachCutsetNode( pNtk, pObj, i )
            Vec_PtrPush( pNtkNew->vCutSet, pObj->pCopy );
    }
    else
    {
        // duplicate the nets and nodes (CIs/COs/latches already dupped)
        Abc_NtkForEachObj( pNtk, pObj, i )
            if ( pObj->pCopy == NULL )
                Abc_NtkDupObj(pNtkNew, pObj, 0);
        // reconnect all objects (no need to transfer attributes on edges)
        Abc_NtkForEachObj( pNtk, pObj, i )
            if ( !Abc_ObjIsBox(pObj) && !Abc_ObjIsBi(pObj) )
                Abc_ObjForEachFanin( pObj, pFanin, k )
                    Abc_ObjAddFanin( pObj->pCopy, pFanin->pCopy );
    }
    // duplicate the EXDC Ntk
    if ( pNtk->pExdc )
        pNtkNew->pExdc = Abc_NtkDup( pNtk->pExdc );
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkDup(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Creates the network composed of one logic cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkCreateCone( Abc_Ntk_t * pNtk, Abc_Obj_t * pNode, char * pNodeName, int fUseAllCis )
{
    Abc_Ntk_t * pNtkNew; 
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pObj, * pFanin, * pNodeCoNew;
    char Buffer[1000];
    int i, k;

    assert( Abc_NtkIsLogic(pNtk) || Abc_NtkIsStrash(pNtk) );
    assert( Abc_ObjIsNode(pNode) ); 
    
    // start the network
    pNtkNew = Abc_NtkAlloc( pNtk->ntkType, pNtk->ntkFunc, 1 );
    // set the name
    sprintf( Buffer, "%s_%s", pNtk->pName, pNodeName );
    pNtkNew->pName = Extra_UtilStrsav(Buffer);

    // establish connection between the constant nodes
    if ( Abc_NtkIsStrash(pNtk) )
        Abc_AigConst1(pNtk)->pCopy = Abc_AigConst1(pNtkNew);

    // collect the nodes in the TFI of the output (mark the TFI)
    vNodes = Abc_NtkDfsNodes( pNtk, &pNode, 1 );
    // create the PIs
    Abc_NtkForEachCi( pNtk, pObj, i )
    {
        if ( fUseAllCis || Abc_NodeIsTravIdCurrent(pObj) ) // TravId is set by DFS
        {
            pObj->pCopy = Abc_NtkCreatePi(pNtkNew);
            Abc_ObjAssignName( pObj->pCopy, Abc_ObjName(pObj), NULL );
        }
    }
    // add the PO corresponding to this output
    pNodeCoNew = Abc_NtkCreatePo( pNtkNew );
    Abc_ObjAssignName( pNodeCoNew, pNodeName, NULL );
    // copy the nodes
    Vec_PtrForEachEntry( vNodes, pObj, i )
    {
        // if it is an AIG, add to the hash table
        if ( Abc_NtkIsStrash(pNtk) )
        {
            pObj->pCopy = Abc_AigAnd( pNtkNew->pManFunc, Abc_ObjChild0Copy(pObj), Abc_ObjChild1Copy(pObj) );
        }
        else
        {
            Abc_NtkDupObj( pNtkNew, pObj, 0 );
            Abc_ObjForEachFanin( pObj, pFanin, k )
                Abc_ObjAddFanin( pObj->pCopy, pFanin->pCopy );
        }
    }
    // connect the internal nodes to the new CO
    Abc_ObjAddFanin( pNodeCoNew, pNode->pCopy );
    Vec_PtrFree( vNodes );

    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkCreateCone(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Creates the network composed of MFFC of one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkCreateMffc( Abc_Ntk_t * pNtk, Abc_Obj_t * pNode, char * pNodeName )
{
    Abc_Ntk_t * pNtkNew; 
    Abc_Obj_t * pObj, * pFanin, * pNodeCoNew;
    Vec_Ptr_t * vCone, * vSupp;
    char Buffer[1000];
    int i, k;

    assert( Abc_NtkIsLogic(pNtk) || Abc_NtkIsStrash(pNtk) );
    assert( Abc_ObjIsNode(pNode) ); 
    
    // start the network
    pNtkNew = Abc_NtkAlloc( pNtk->ntkType, pNtk->ntkFunc, 1 );
    // set the name
    sprintf( Buffer, "%s_%s", pNtk->pName, pNodeName );
    pNtkNew->pName = Extra_UtilStrsav(Buffer);

    // establish connection between the constant nodes
    if ( Abc_NtkIsStrash(pNtk) )
        Abc_AigConst1(pNtk)->pCopy = Abc_AigConst1(pNtkNew);

    // collect the nodes in MFFC
    vCone = Vec_PtrAlloc( 100 );
    vSupp = Vec_PtrAlloc( 100 );
    Abc_NodeDeref_rec( pNode );
    Abc_NodeMffsConeSupp( pNode, vCone, vSupp );
    Abc_NodeRef_rec( pNode );
    // create the PIs
    Vec_PtrForEachEntry( vSupp, pObj, i )
    {
        pObj->pCopy = Abc_NtkCreatePi(pNtkNew);
        Abc_ObjAssignName( pObj->pCopy, Abc_ObjName(pObj), NULL );
    }
    // create the PO
    pNodeCoNew = Abc_NtkCreatePo( pNtkNew );
    Abc_ObjAssignName( pNodeCoNew, pNodeName, NULL );
    // copy the nodes
    Vec_PtrForEachEntry( vCone, pObj, i )
    {
        // if it is an AIG, add to the hash table
        if ( Abc_NtkIsStrash(pNtk) )
        {
            pObj->pCopy = Abc_AigAnd( pNtkNew->pManFunc, Abc_ObjChild0Copy(pObj), Abc_ObjChild1Copy(pObj) );
        }
        else
        {
            Abc_NtkDupObj( pNtkNew, pObj, 0 );
            Abc_ObjForEachFanin( pObj, pFanin, k )
                Abc_ObjAddFanin( pObj->pCopy, pFanin->pCopy );
        }
    }
    // connect the topmost node
    Abc_ObjAddFanin( pNodeCoNew, pNode->pCopy );
    Vec_PtrFree( vCone );
    Vec_PtrFree( vSupp );

    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkCreateMffc(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Creates the miter composed of one multi-output cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkCreateTarget( Abc_Ntk_t * pNtk, Vec_Ptr_t * vRoots, Vec_Int_t * vValues )
{
    Vec_Ptr_t * vNodes;
    Abc_Ntk_t * pNtkNew; 
    Abc_Obj_t * pObj, * pFinal, * pOther, * pNodePo;
    int i;

    assert( Abc_NtkIsLogic(pNtk) );

    // convert the network into the AIG form
    if ( !Abc_NtkLogicToAig(pNtk) )
        return NULL;
    
    // start the network
    Abc_NtkCleanCopy( pNtk );
    pNtkNew = Abc_NtkAlloc( ABC_NTK_STRASH, ABC_FUNC_AIG, 1 );
    pNtkNew->pName = Extra_UtilStrsav(pNtk->pName);

    // collect the nodes in the TFI of the output
    vNodes = Abc_NtkDfsNodes( pNtk, (Abc_Obj_t **)vRoots->pArray, vRoots->nSize );
    // create the PIs
    Abc_NtkForEachCi( pNtk, pObj, i )
    {
        pObj->pCopy = Abc_NtkCreatePi(pNtkNew);
        Abc_ObjAssignName( pObj->pCopy, Abc_ObjName(pObj), NULL );
    }
    // copy the nodes
    Vec_PtrForEachEntry( vNodes, pObj, i )
        pObj->pCopy = Abc_NodeStrash( pNtkNew, pObj );
    Vec_PtrFree( vNodes );

    // add the PO
    pFinal = Abc_AigConst1( pNtkNew );
    Vec_PtrForEachEntry( vRoots, pObj, i )
    {
        if ( Abc_ObjIsCo(pObj) )
            pOther = Abc_ObjFanin0(pObj)->pCopy;
        else
            pOther = pObj->pCopy;
        if ( Vec_IntEntry(vValues, i) == 0 )
            pOther = Abc_ObjNot(pOther);
        pFinal = Abc_AigAnd( pNtkNew->pManFunc, pFinal, pOther );
    }

    // add the PO corresponding to this output
    pNodePo = Abc_NtkCreatePo( pNtkNew );
    Abc_ObjAddFanin( pNodePo, pFinal );
    Abc_ObjAssignName( pNodePo, "miter", NULL );
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkCreateTarget(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Creates the network composed of one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkCreateFromNode( Abc_Ntk_t * pNtk, Abc_Obj_t * pNode )
{    
    Abc_Ntk_t * pNtkNew; 
    Abc_Obj_t * pFanin, * pNodePo;
    int i;
    // start the network
    pNtkNew = Abc_NtkAlloc( pNtk->ntkType, pNtk->ntkFunc, 1 );
    pNtkNew->pName = Extra_UtilStrsav(Abc_ObjName(pNode));
    // add the PIs corresponding to the fanins of the node
    Abc_ObjForEachFanin( pNode, pFanin, i )
    {
        pFanin->pCopy = Abc_NtkCreatePi( pNtkNew );
        Abc_ObjAssignName( pFanin->pCopy, Abc_ObjName(pFanin), NULL );
    }
    // duplicate and connect the node
    pNode->pCopy = Abc_NtkDupObj( pNtkNew, pNode, 0 );
    Abc_ObjForEachFanin( pNode, pFanin, i )
        Abc_ObjAddFanin( pNode->pCopy, pFanin->pCopy );
    // create the only PO
    pNodePo = Abc_NtkCreatePo( pNtkNew );
    Abc_ObjAddFanin( pNodePo, pNode->pCopy );
    Abc_ObjAssignName( pNodePo, Abc_ObjName(pNode), NULL );
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkCreateFromNode(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Creates the network composed of one node with the given SOP.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkCreateWithNode( char * pSop )
{    
    Abc_Ntk_t * pNtkNew; 
    Abc_Obj_t * pFanin, * pNode, * pNodePo;
    Vec_Ptr_t * vNames;
    int i, nVars;
    // start the network
    pNtkNew = Abc_NtkAlloc( ABC_NTK_LOGIC, ABC_FUNC_SOP, 1 );
    pNtkNew->pName = Extra_UtilStrsav("ex");
    // create PIs
    Vec_PtrPush( pNtkNew->vObjs, NULL );
    nVars = Abc_SopGetVarNum( pSop );
    vNames = Abc_NodeGetFakeNames( nVars );
    for ( i = 0; i < nVars; i++ )
        Abc_ObjAssignName( Abc_NtkCreatePi(pNtkNew), Vec_PtrEntry(vNames, i), NULL );
    Abc_NodeFreeNames( vNames );
    // create the node, add PIs as fanins, set the function
    pNode = Abc_NtkCreateNode( pNtkNew );
    Abc_NtkForEachPi( pNtkNew, pFanin, i )
        Abc_ObjAddFanin( pNode, pFanin );
    pNode->pData = Abc_SopRegister( pNtkNew->pManFunc, pSop );
    // create the only PO
    pNodePo = Abc_NtkCreatePo(pNtkNew);
    Abc_ObjAddFanin( pNodePo, pNode );
    Abc_ObjAssignName( pNodePo, "F", NULL );
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkCreateWithNode(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Deletes the Ntk.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkDelete( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    int TotalMemory, i;
    int LargePiece = (4 << ABC_NUM_STEPS);
    if ( pNtk == NULL )
        return;
    // free EXDC Ntk
    if ( pNtk->pExdc )
        Abc_NtkDelete( pNtk->pExdc );
    // dereference the BDDs
    if ( Abc_NtkHasBdd(pNtk) )
    {
        Abc_NtkForEachNode( pNtk, pObj, i )
            Cudd_RecursiveDeref( pNtk->pManFunc, pObj->pData );
    }
    // make sure all the marks are clean
    Abc_NtkForEachObj( pNtk, pObj, i )
    {
        // free large fanout arrays
        if ( pNtk->pMmObj && pObj->vFanouts.nCap * 4 > LargePiece )
            FREE( pObj->vFanouts.pArray );
        // these flags should be always zero
        // if this is not true, something is wrong somewhere
        assert( pObj->fMarkA == 0 );
        assert( pObj->fMarkB == 0 );
        assert( pObj->fMarkC == 0 );
    }
    // free the nodes
    if ( pNtk->pMmStep == NULL )
    {
        Abc_NtkForEachObj( pNtk, pObj, i )
        {
            FREE( pObj->vFanouts.pArray );
            FREE( pObj->vFanins.pArray );
        }
    }
    if ( pNtk->pMmObj == NULL )
    {
        Abc_NtkForEachObj( pNtk, pObj, i )
            free( pObj );
    }
        
    FREE( pNtk->pName );
    FREE( pNtk->pSpec );
    // free the arrays
    Vec_PtrFree( pNtk->vPios );
    Vec_PtrFree( pNtk->vPis );
    Vec_PtrFree( pNtk->vPos );
    Vec_PtrFree( pNtk->vCis );
    Vec_PtrFree( pNtk->vCos );
    Vec_PtrFree( pNtk->vAsserts );
    Vec_PtrFree( pNtk->vObjs );
    Vec_PtrFree( pNtk->vCutSet );
    Vec_PtrFree( pNtk->vBoxes );
    Vec_FltFree( pNtk->vSkews );
    if ( pNtk->pModel ) free( pNtk->pModel );
    TotalMemory  = 0;
    TotalMemory += pNtk->pMmObj? Extra_MmFixedReadMemUsage(pNtk->pMmObj)  : 0;
    TotalMemory += pNtk->pMmStep? Extra_MmStepReadMemUsage(pNtk->pMmStep) : 0;
//    fprintf( stdout, "The total memory allocated internally by the network = %0.2f Mb.\n", ((double)TotalMemory)/(1<<20) );
    // free the storage 
    if ( pNtk->pMmObj )
        Extra_MmFixedStop( pNtk->pMmObj,   0 );
    if ( pNtk->pMmStep )
        Extra_MmStepStop ( pNtk->pMmStep,  0 );
    // name manager
    Nm_ManFree( pNtk->pManName );
    // free the timing manager
    if ( pNtk->pManTime )
        Abc_ManTimeStop( pNtk->pManTime );
    // start the functionality manager
    if ( Abc_NtkIsStrash(pNtk) )
        Abc_AigFree( pNtk->pManFunc );
    else if ( Abc_NtkIsSeq(pNtk) )
        Seq_Delete( pNtk->pManFunc );
    else if ( Abc_NtkHasSop(pNtk) )
        Extra_MmFlexStop( pNtk->pManFunc, 0 );
    else if ( Abc_NtkHasBdd(pNtk) )
        Extra_StopManager( pNtk->pManFunc );
    else if ( Abc_NtkHasAig(pNtk) )
        { if ( pNtk->pManFunc ) Aig_ManStop( pNtk->pManFunc ); }
    else if ( Abc_NtkHasMapping(pNtk) )
        pNtk->pManFunc = NULL;
    else if ( !Abc_NtkHasBlackbox(pNtk) )
        assert( 0 );
    // free the hierarchy
    if ( Abc_NtkIsNetlist(pNtk) && pNtk->tName2Model )
    {
        stmm_generator * gen;
        Abc_Ntk_t * pNtkTemp;
        char * pName;
        stmm_foreach_item( pNtk->tName2Model, gen, &pName, (char **)&pNtkTemp )
            Abc_NtkDelete( pNtkTemp );
        stmm_free_table( pNtk->tName2Model );
    }
    if ( pNtk->pBlackBoxes ) 
        Vec_IntFree( pNtk->pBlackBoxes );
    free( pNtk );
}

/**Function*************************************************************

  Synopsis    [Reads the verilog file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkFixNonDrivenNets( Abc_Ntk_t * pNtk )
{ 
    Vec_Ptr_t * vNets;
    Abc_Obj_t * pNet, * pNode;
    int i;

    if ( Abc_NtkNodeNum(pNtk) == 0 )
    {
        pNtk->ntkFunc = ABC_FUNC_BLACKBOX;
        return;
    }

    // check for non-driven nets
    vNets = Vec_PtrAlloc( 100 );
    Abc_NtkForEachNet( pNtk, pNet, i )
    {
        if ( Abc_ObjFaninNum(pNet) > 0 )
            continue;
        // add the constant 0 driver
        pNode = Abc_NodeCreateConst0( pNtk );
        // add the fanout net
        Abc_ObjAddFanin( pNet, pNode );
        // add the net to those for which the warning will be printed
        Vec_PtrPush( vNets, pNet->pData );
    }

    // print the warning
    if ( vNets->nSize > 0 )
    {
        printf( "Constant-zero drivers were added to %d non-driven nets in network %s:\n", vNets->nSize, pNtk->pName );
        for ( i = 0; i < vNets->nSize; i++ )
        {
            if ( i == 0 )
                printf( "%s", vNets->pArray[i] );
            else if ( i == 1 )
                printf( ", %s", vNets->pArray[i] );
            else if ( i == 2 )
            {
                printf( ", %s, etc.", vNets->pArray[i] );
                break;
            }
        }
        printf( "\n" );
    }
    Vec_PtrFree( vNets );
}




////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


