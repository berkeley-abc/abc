/**CFile****************************************************************

  FileName    [abcCreate.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Creation/duplication/deletion procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcCreate.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "main.h"
#include "mio.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define ABC_NUM_STEPS  10

static Abc_Obj_t *   Abc_ObjAlloc( Abc_Ntk_t * pNtk, Abc_ObjType_t Type );
static void          Abc_ObjRecycle( Abc_Obj_t * pObj );
static void          Abc_ObjAdd( Abc_Obj_t * pObj );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates a new Ntk.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkAlloc( Abc_NtkType_t Type )
{
    Abc_Ntk_t * pNtk;
    pNtk = ALLOC( Abc_Ntk_t, 1 );
    memset( pNtk, 0, sizeof(Abc_Ntk_t) );
    pNtk->Type        = Type;
    // start the object storage
    pNtk->vObjs       = Vec_PtrAlloc( 100 );
    pNtk->vLats       = Vec_PtrAlloc( 100 );
    pNtk->vCis        = Vec_PtrAlloc( 100 );
    pNtk->vCos        = Vec_PtrAlloc( 100 );
    pNtk->vPtrTemp    = Vec_PtrAlloc( 100 );
    pNtk->vIntTemp    = Vec_IntAlloc( 100 );
    pNtk->vStrTemp    = Vec_StrAlloc( 100 );
    // start the hash table
    pNtk->tName2Net   = stmm_init_table(strcmp, stmm_strhash);
    pNtk->tObj2Name   = stmm_init_table(stmm_ptrcmp, stmm_ptrhash);
    // start the memory managers
    pNtk->pMmNames    = Extra_MmFlexStart();
    pNtk->pMmObj      = Extra_MmFixedStart( sizeof(Abc_Obj_t) );
    pNtk->pMmStep     = Extra_MmStepStart( ABC_NUM_STEPS );
    // get ready to assign the first Obj ID
    pNtk->nTravIds    = 1;
    // start the functionality manager
    if ( Abc_NtkIsSop(pNtk) )
        pNtk->pManFunc = Extra_MmFlexStart();
    else if ( Abc_NtkIsLogicBdd(pNtk) )
        pNtk->pManFunc = Cudd_Init( 20, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );
    else if ( Abc_NtkIsAig(pNtk) || Abc_NtkIsSeq(pNtk) )
        pNtk->pManFunc = Abc_AigAlloc( pNtk );
    else if ( Abc_NtkIsMapped(pNtk) )
        pNtk->pManFunc = Abc_FrameReadLibGen(Abc_FrameGetGlobalFrame());
    else
        assert( 0 );
    return pNtk;
}

/**Function*************************************************************

  Synopsis    [Starts a new network using existing network as a model.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkStartFrom( Abc_Ntk_t * pNtk, Abc_NtkType_t Type )
{
    Abc_Ntk_t * pNtkNew; 
    Abc_Obj_t * pObj, * pObjNew;
    int i;
    if ( pNtk == NULL )
        return NULL;
    // start the network
    pNtkNew = Abc_NtkAlloc( Type );
    // duplicate the name and the spec
    pNtkNew->pName = util_strsav(pNtk->pName);
    pNtkNew->pSpec = util_strsav(pNtk->pSpec);
    // clone the PIs/POs/latches
    Abc_NtkForEachPi( pNtk, pObj, i )
        Abc_NtkDupObj(pNtkNew, pObj);
    Abc_NtkForEachPo( pNtk, pObj, i )
        Abc_NtkDupObj(pNtkNew, pObj);
    Abc_NtkForEachLatch( pNtk, pObj, i )
    {
        pObjNew = Abc_NtkDupObj(pNtkNew, pObj);
        Vec_PtrPush( pNtkNew->vCis, pObjNew );
        Vec_PtrPush( pNtkNew->vCos, pObjNew );
    }
    // clean the node copy fields
    Abc_NtkForEachNode( pNtk, pObj, i )
        pObj->pCopy = NULL;
    // transfer the names
    Abc_NtkDupCioNamesTable( pNtk, pNtkNew );
    Abc_ManTimeDup( pNtk, pNtkNew );
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

  Synopsis    [Finalizes the network adding latches to CI/CO lists and creates their names.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkFinalizeLatches( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pLatch;
    int i;
    // set the COs of the strashed network
    Abc_NtkForEachLatch( pNtk, pLatch, i )
    {
        Vec_PtrPush( pNtk->vCis, pLatch );
        Vec_PtrPush( pNtk->vCos, pLatch );
        Abc_NtkLogicStoreName( pLatch, Abc_ObjNameSuffix(pLatch, "L") );
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
    pNtkNew = Abc_NtkAlloc( ABC_NTK_NETLIST_SOP );
    // set the specs
    pNtkNew->pName = util_strsav( pName );
    pNtkNew->pSpec = util_strsav( pName );
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
    Abc_Obj_t * pLatch;
    int i;
    assert( Abc_NtkIsNetlist(pNtk) );
    // fix the net drivers
    Abc_NtkFixNonDrivenNets( pNtk );
    // create the names table
    Abc_NtkCreateCioNamesTable( pNtk );
    // add latches to the CI/CO arrays
    Abc_NtkForEachLatch( pNtk, pLatch, i )
    {
        Vec_PtrPush( pNtk->vCis, pLatch );
        Vec_PtrPush( pNtk->vCos, pLatch );
    }
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
    pNtkNew = Abc_NtkStartFrom( pNtk, pNtk->Type );
    // copy the internal nodes
    if ( Abc_NtkIsAig(pNtk) )
        Abc_AigDup( pNtk->pManFunc, pNtkNew->pManFunc );
    else
    {
        // duplicate the nets and nodes (CIs/COs/latches already dupped)
        Abc_NtkForEachObj( pNtk, pObj, i )
            if ( pObj->pCopy == NULL )
                Abc_NtkDupObj(pNtkNew, pObj);
        // reconnect all objects (no need to transfer attributes on edges)
        Abc_NtkForEachObj( pNtk, pObj, i )
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

  Synopsis    [Creates the network composed of one output.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkSplitOutput( Abc_Ntk_t * pNtk, Abc_Obj_t * pNode, int fUseAllCis )
{
    Vec_Ptr_t * vNodes;
    Abc_Ntk_t * pNtkNew; 
    Abc_Obj_t * pObj, * pFanin;
    char Buffer[1000];
    int i, k;

    assert( Abc_NtkIsLogic(pNtk) || Abc_NtkIsAig(pNtk) );
    assert( Abc_ObjIsCo(pNode) ); 
    
    // start the network
    pNtkNew = Abc_NtkAlloc( pNtk->Type );
    // set the name
    sprintf( Buffer, "%s_%s", pNtk->pName, Abc_ObjName(pNode) );
    pNtkNew->pName = util_strsav(Buffer);

    // collect the nodes in the TFI of the output
    vNodes = Abc_NtkDfsNodes( pNtk, &pNode, 1 );
    // create the PIs
    Abc_NtkForEachCi( pNtk, pObj, i )
    {
        if ( fUseAllCis || Abc_NodeIsTravIdCurrent(pObj) ) // TravId is set by DFS
        {
            pObj->pCopy = Abc_NtkCreatePi(pNtkNew);
            Abc_NtkLogicStoreName( pObj->pCopy, Abc_ObjName(pObj) );
        }
    }
    // establish connection between the constant nodes
    if ( Abc_NtkIsAig(pNtk) )
        Abc_AigConst1(pNtk->pManFunc)->pCopy = Abc_AigConst1(pNtkNew->pManFunc);

    // copy the nodes
    Vec_PtrForEachEntry( vNodes, pObj, i )
    {
        // if it is an AIG, add to the hash table
        if ( Abc_NtkIsAig(pNtk) )
        {
            pObj->pCopy = Abc_AigAnd( pNtkNew->pManFunc, Abc_ObjChild0Copy(pObj), Abc_ObjChild1Copy(pObj) );
        }
        else
        {
            Abc_NtkDupObj( pNtkNew, pObj );
            Abc_ObjForEachFanin( pObj, pFanin, k )
                Abc_ObjAddFanin( pObj->pCopy, pFanin->pCopy );
        }
    }
    Vec_PtrFree( vNodes );

    // add the PO corresponding to this output
    pNode->pCopy = Abc_NtkCreatePo( pNtkNew );
    Abc_ObjAddFanin( pNode->pCopy, Abc_ObjFanin0(pNode)->pCopy );
    Abc_NtkLogicStoreName( pNode->pCopy, Abc_ObjName(pNode) );

    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkSplitOutput(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Creates the network composed of one output.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkCreateCone( Abc_Ntk_t * pNtk, Vec_Ptr_t * vRoots, Vec_Int_t * vValues )
{
    Vec_Ptr_t * vNodes;
    Abc_Ntk_t * pNtkNew; 
    Abc_Obj_t * pObj, * pFinal, * pOther, * pNodePo;
    int i;

    assert( Abc_NtkIsLogic(pNtk) );
    
    // start the network
    Abc_NtkCleanCopy( pNtk );
    pNtkNew = Abc_NtkAlloc( ABC_NTK_AIG );
    pNtkNew->pName = util_strsav(pNtk->pName);

    // collect the nodes in the TFI of the output
    vNodes = Abc_NtkDfsNodes( pNtk, (Abc_Obj_t **)vRoots->pArray, vRoots->nSize );
    // create the PIs
    Abc_NtkForEachCi( pNtk, pObj, i )
    {
        pObj->pCopy = Abc_NtkCreatePi(pNtkNew);
        Abc_NtkLogicStoreName( pObj->pCopy, Abc_ObjName(pObj) );
    }
    // copy the nodes
    Vec_PtrForEachEntry( vNodes, pObj, i )
        pObj->pCopy = Abc_NodeStrash( pNtkNew->pManFunc, pObj );
    Vec_PtrFree( vNodes );

    // add the PO
    pFinal = Abc_AigConst1( pNtkNew->pManFunc );
    Vec_PtrForEachEntry( vRoots, pObj, i )
    {
        pOther = pObj->pCopy;
        if ( Vec_IntEntry(vValues, i) == 0 )
            pOther = Abc_ObjNot(pOther);
        pFinal = Abc_AigAnd( pNtkNew->pManFunc, pFinal, pOther );
    }

    // add the PO corresponding to this output
    pNodePo = Abc_NtkCreatePo( pNtkNew );
    Abc_ObjAddFanin( pNodePo, pFinal );
    Abc_NtkLogicStoreName( pNodePo, "miter" );
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkCreateCone(): Network check has failed.\n" );
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
    // make sure all the marks are clean
    Abc_NtkForEachObj( pNtk, pObj, i )
    {
        // free large fanout arrays
        if ( pObj->vFanouts.nCap * 4 > LargePiece )
            FREE( pObj->vFanouts.pArray );
        // check that the other things are okay
        assert( pObj->fMarkA == 0 );
        assert( pObj->fMarkB == 0 );
        assert( pObj->fMarkC == 0 );
    }

    // dereference the BDDs
    if ( Abc_NtkIsLogicBdd(pNtk) )
        Abc_NtkForEachNode( pNtk, pObj, i )
            Cudd_RecursiveDeref( pNtk->pManFunc, pObj->pData );
        
    FREE( pNtk->pName );
    FREE( pNtk->pSpec );
    // copy the EXDC Ntk
    if ( pNtk->pExdc )
        Abc_NtkDelete( pNtk->pExdc );
    // free the arrays
    Vec_PtrFree( pNtk->vObjs );
    Vec_PtrFree( pNtk->vLats );
    Vec_PtrFree( pNtk->vCis );
    Vec_PtrFree( pNtk->vCos );
    Vec_PtrFree( pNtk->vPtrTemp );
    Vec_IntFree( pNtk->vIntTemp );
    Vec_StrFree( pNtk->vStrTemp );
    // free the hash table of Obj name into Obj ID
    stmm_free_table( pNtk->tName2Net );
    stmm_free_table( pNtk->tObj2Name );
    TotalMemory  = 0;
    TotalMemory += Extra_MmFlexReadMemUsage(pNtk->pMmNames);
    TotalMemory += Extra_MmFixedReadMemUsage(pNtk->pMmObj);
    TotalMemory += Extra_MmStepReadMemUsage(pNtk->pMmStep);
//    fprintf( stdout, "The total memory allocated internally by the network = %0.2f Mb.\n", ((double)TotalMemory)/(1<<20) );
    // free the storage 
    Extra_MmFlexStop ( pNtk->pMmNames, 0 );
    Extra_MmFixedStop( pNtk->pMmObj,   0 );
    Extra_MmStepStop ( pNtk->pMmStep,  0 );
    // free the timing manager
    if ( pNtk->pManTime )
        Abc_ManTimeStop( pNtk->pManTime );
    // start the functionality manager
    if ( Abc_NtkIsSop(pNtk) )
        Extra_MmFlexStop( pNtk->pManFunc, 0 );
    else if ( Abc_NtkIsLogicBdd(pNtk) )
        Extra_StopManager( pNtk->pManFunc );
    else if ( Abc_NtkIsAig(pNtk) || Abc_NtkIsSeq(pNtk) )
        Abc_AigFree( pNtk->pManFunc );
    else if ( !Abc_NtkIsMapped(pNtk) )
        assert( 0 );
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

    // check for non-driven nets
    vNets = Vec_PtrAlloc( 100 );
    Abc_NtkForEachNet( pNtk, pNet, i )
    {
        if ( Abc_ObjFaninNum(pNet) > 0 )
            continue;
        // add the constant 0 driver
        pNode = Abc_NtkCreateNode( pNtk );
        // set the constant function
        Abc_ObjSetData( pNode, Abc_SopRegister(pNtk->pManFunc, " 0\n") );
        // add the fanout net
        Abc_ObjAddFanin( pNet, pNode );
        // add the net to those for which the warning will be printed
        Vec_PtrPush( vNets, pNet->pData );
    }

    // print the warning
    if ( vNets->nSize > 0 )
    {
        printf( "Constant-zero drivers were added to %d non-driven nets:\n", vNets->nSize );
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




/**Function*************************************************************

  Synopsis    [Creates a new Obj.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_ObjAlloc( Abc_Ntk_t * pNtk, Abc_ObjType_t Type )
{
    Abc_Obj_t * pObj;
    pObj = (Abc_Obj_t *)Extra_MmFixedEntryFetch( pNtk->pMmObj );
    memset( pObj, 0, sizeof(Abc_Obj_t) );
    pObj->Id   = -1;
    pObj->pNtk = pNtk;
    pObj->Type = Type;
    return pObj;
}

/**Function*************************************************************

  Synopsis    [Recycles the Obj.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ObjRecycle( Abc_Obj_t * pObj )
{
    Abc_Ntk_t * pNtk = pObj->pNtk;
    memset( pObj, 0, sizeof(Abc_Obj_t) );
    Extra_MmFixedEntryRecycle( pNtk->pMmObj, (char *)pObj );
}

/**Function*************************************************************

  Synopsis    [Adds the node to the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ObjAdd( Abc_Obj_t * pObj )
{
    Abc_Ntk_t * pNtk = pObj->pNtk;
    assert( !Abc_ObjIsComplement(pObj) );
    // add to the array of objects
    pObj->Id = pNtk->vObjs->nSize;
    Vec_PtrPush( pNtk->vObjs, pObj );
    pNtk->nObjs++;
    // perform specialized operations depending on the object type
    if ( Abc_ObjIsNet(pObj) )
    {
        // add the name to the table
        if ( pObj->pData && stmm_insert( pNtk->tName2Net, pObj->pData, (char *)pObj ) )
        {
            printf( "Error: The net is already in the table...\n" );
            assert( 0 );
        }
        pNtk->nNets++;
    }
    else if ( Abc_ObjIsNode(pObj) )
    {
        pNtk->nNodes++;
    }
    else if ( Abc_ObjIsLatch(pObj) )
    {
        Vec_PtrPush( pNtk->vLats, pObj );
        pNtk->nLatches++;
    }
    else if ( Abc_ObjIsPi(pObj) )
    {
        Vec_PtrPush( pNtk->vCis, pObj );
        pNtk->nPis++;
    }
    else if ( Abc_ObjIsPo(pObj) )
    {
        Vec_PtrPush( pNtk->vCos, pObj );
        pNtk->nPos++;
    }
    else
    {
        assert( 0 );
    }
    assert( pObj->Id >= 0 );
}

/**Function*************************************************************

  Synopsis    [Duplicate the Obj.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkDupObj( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pObjNew;
    pObjNew = Abc_ObjAlloc( pNtkNew, pObj->Type );
    if ( Abc_ObjIsNode(pObj) ) // copy the function if network is the same type
    {
        if ( pNtkNew->Type == pObj->pNtk->Type || Abc_NtkIsNetlist(pObj->pNtk) || Abc_NtkIsNetlist(pNtkNew) ) 
        {
            if ( Abc_NtkIsSop(pNtkNew) )
                pObjNew->pData = Abc_SopRegister( pNtkNew->pManFunc, pObj->pData );
            else if ( Abc_NtkIsLogicBdd(pNtkNew) )
                pObjNew->pData = Cudd_bddTransfer(pObj->pNtk->pManFunc, pNtkNew->pManFunc, pObj->pData), Cudd_Ref(pObjNew->pData);
            else if ( Abc_NtkIsMapped(pNtkNew) )
                pObjNew->pData = pObj->pData;
            else if ( !Abc_NtkIsAig(pNtkNew) && !Abc_NtkIsSeq(pNtkNew) )
                assert( 0 );
        }
    }
    else if ( Abc_ObjIsNet(pObj) ) // copy the name
        pObjNew->pData = Abc_NtkRegisterName( pNtkNew, pObj->pData );
    else if ( Abc_ObjIsLatch(pObj) ) // copy the reset value
        pObjNew->pData = pObj->pData;
    pObj->pCopy = pObjNew;
    // add the object to the network
    Abc_ObjAdd( pObjNew );
    return pObjNew;
}

/**Function*************************************************************

  Synopsis    [Creates a new constant node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkDupConst1( Abc_Ntk_t * pNtkAig, Abc_Ntk_t * pNtkNew )  
{ 
    Abc_Obj_t * pConst1;
    assert( Abc_NtkIsAig(pNtkAig) || Abc_NtkIsSeq(pNtkAig) );
    assert( Abc_NtkIsLogicSop(pNtkNew) );
    pConst1 = Abc_AigConst1(pNtkAig->pManFunc);
    if ( Abc_ObjFanoutNum(pConst1) > 0 )
        pConst1->pCopy = Abc_NodeCreateConst1( pNtkNew );
    return pConst1->pCopy; 
} 

/**Function*************************************************************

  Synopsis    [Creates a new constant node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkDupReset( Abc_Ntk_t * pNtkAig, Abc_Ntk_t * pNtkNew )  
{ 
    Abc_Obj_t * pReset, * pConst1;
    assert( Abc_NtkIsAig(pNtkAig) || Abc_NtkIsSeq(pNtkAig) );
    assert( Abc_NtkIsLogicSop(pNtkNew) );
    pReset = Abc_AigReset(pNtkAig->pManFunc);
    if ( Abc_ObjFanoutNum(pReset) > 0 )
    {
        // create new latch with reset value 0
        pReset->pCopy = Abc_NtkCreateLatch( pNtkNew );
        // add constant node fanin to the latch
        pConst1 = Abc_NodeCreateConst1( pNtkNew );
        Abc_ObjAddFanin( pReset->pCopy, pConst1 );
    }
    return pReset->pCopy; 
} 

/**Function*************************************************************

  Synopsis    [Deletes the object from the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkDeleteObj( Abc_Obj_t * pObj )
{
    Vec_Ptr_t * vNodes = pObj->pNtk->vPtrTemp;
    Abc_Ntk_t * pNtk = pObj->pNtk;
    int i;

    assert( !Abc_ObjIsComplement(pObj) );

    // delete fanins and fanouts
    Abc_NodeCollectFanouts( pObj, vNodes );
    for ( i = 0; i < vNodes->nSize; i++ )
        Abc_ObjDeleteFanin( vNodes->pArray[i], pObj );
    Abc_NodeCollectFanins( pObj, vNodes );
    for ( i = 0; i < vNodes->nSize; i++ )
        Abc_ObjDeleteFanin( pObj, vNodes->pArray[i] );

    // remove from the list of objects
    Vec_PtrWriteEntry( pNtk->vObjs, pObj->Id, NULL );
    pObj->Id = (1<<26)-1;
    pNtk->nObjs--;

    // perform specialized operations depending on the object type
    if ( Abc_ObjIsNet(pObj) )
    {
        // remove the net from the hash table of nets
        if ( pObj->pData && !stmm_delete( pNtk->tName2Net, (char **)&pObj->pData, (char **)&pObj ) )
        {
            printf( "Error: The net is not in the table...\n" );
            assert( 0 );
        }
        pObj->pData = NULL;
        pNtk->nNets--;
    }
    else if ( Abc_ObjIsNode(pObj) )
    {
        pNtk->nNodes--;
    }
    else if ( Abc_ObjIsLatch(pObj) )
    {
        pNtk->nLatches--;
    }
    else 
        assert( 0 );
    // recycle the net itself
    Abc_ObjRecycle( pObj );
}





/**Function*************************************************************

  Synopsis    [Returns the net with the given name.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkFindNode( Abc_Ntk_t * pNtk, char * pName )
{
    Abc_Obj_t * pObj, * pDriver;
    int i, Num;
    // check if the node is among CIs
    Abc_NtkForEachCi( pNtk, pObj, i )
    {
        if ( strcmp( Abc_ObjName(pObj), pName ) == 0 )
        {
            if ( i < Abc_NtkPiNum(pNtk) )
                printf( "Node \"%s\" is a primary input.\n", pName );
            else
                printf( "Node \"%s\" is a latch output.\n", pName );
            return NULL;
        }
    }
    // search the node among COs
    Abc_NtkForEachCo( pNtk, pObj, i )
    {
        if ( strcmp( Abc_ObjName(pObj), pName ) == 0 )
        {
            pDriver = Abc_ObjFanin0(pObj);
            if ( !Abc_ObjIsNode(pDriver) )
            {
                printf( "Node \"%s\" does not have logic associated with it.\n", pName );
                return NULL;
            }
            return pDriver;
        }
    }
    // find the internal node
    if ( pName[0] != '[' || pName[strlen(pName)-1] != ']' )
    {
        printf( "Node \"%s\" has non-standard name (expected name is \"[integer]\").\n", pName );
        return NULL;
    }
    Num = atoi( pName + 1 );
    if ( Num < 0 || Num >= Abc_NtkObjNumMax(pNtk) )
    {
        printf( "The node \"%s\" with ID %d is not in the current network.\n", pName, Num );
        return NULL;
    }
    pObj = Abc_NtkObj( pNtk, Num );
    if ( pObj == NULL )
    {
        printf( "The node \"%s\" with ID %d has been removed from the current network.\n", pName, Num );
        return NULL;
    }
    if ( !Abc_ObjIsNode(pObj) )
    {
        printf( "Object with ID %d is not a node.\n", Num );
        return NULL;
    }
    return pObj;
}

/**Function*************************************************************

  Synopsis    [Returns the net with the given name.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkFindCo( Abc_Ntk_t * pNtk, char * pName )
{
    Abc_Obj_t * pNode;
    int i;
    // search the node among COs
    Abc_NtkForEachCo( pNtk, pNode, i )
    {
        if ( strcmp( Abc_ObjName(pNode), pName ) == 0 )
            return pNode;
    }
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Returns the net with the given name.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkFindNet( Abc_Ntk_t * pNtk, char * pName )
{
    Abc_Obj_t * pNet;
    assert( Abc_NtkIsNetlist(pNtk) );
    if ( stmm_lookup( pNtk->tName2Net, pName, (char**)&pNet ) )
        return pNet;
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Finds or creates the net.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkFindOrCreateNet( Abc_Ntk_t * pNtk, char * pName )
{
    Abc_Obj_t * pNet;
    assert( Abc_NtkIsNetlist(pNtk) );
    if ( pNet = Abc_NtkFindNet( pNtk, pName ) )
        return pNet;
    // create a new net
    pNet = Abc_ObjAlloc( pNtk, ABC_OBJ_NET );
    pNet->pData = Abc_NtkRegisterName( pNtk, pName );
    Abc_ObjAdd( pNet );
    return pNet;
}
    
/**Function*************************************************************

  Synopsis    [Create the new node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkCreateNode( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    pObj = Abc_ObjAlloc( pNtk, ABC_OBJ_NODE );     
    Abc_ObjAdd( pObj );
    return pObj;
}
    
/**Function*************************************************************

  Synopsis    [Create the new node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkCreatePi( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    pObj = Abc_ObjAlloc( pNtk, ABC_OBJ_PI );     
    Abc_ObjAdd( pObj );
    return pObj;
}
    
/**Function*************************************************************

  Synopsis    [Create the new node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkCreatePo( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    pObj = Abc_ObjAlloc( pNtk, ABC_OBJ_PO );     
    Abc_ObjAdd( pObj );
    return pObj;
}

/**Function*************************************************************

  Synopsis    [Create the new node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkCreateLatch( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    pObj = Abc_ObjAlloc( pNtk, ABC_OBJ_LATCH );     
    Abc_ObjAdd( pObj );
    return pObj;
}

/**Function*************************************************************

  Synopsis    [Creates inverter.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeCreateConst0( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    pNode = Abc_NtkCreateNode( pNtk );   
    if ( Abc_NtkIsSop(pNtk) )
        pNode->pData = Abc_SopRegister( pNtk->pManFunc, " 0\n" );
    else if ( Abc_NtkIsLogicBdd(pNtk) )
        pNode->pData = Cudd_ReadLogicZero(pNtk->pManFunc), Cudd_Ref( pNode->pData );
    else if ( Abc_NtkIsMapped(pNtk) )
        pNode->pData = Mio_LibraryReadConst0(Abc_FrameReadLibGen(Abc_FrameGetGlobalFrame()));
    else
        assert( 0 );
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Creates inverter.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeCreateConst1( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    if ( Abc_NtkIsAig(pNtk) || Abc_NtkIsSeq(pNtk) )
        return Abc_AigConst1(pNtk->pManFunc);
    pNode = Abc_NtkCreateNode( pNtk );   
    if ( Abc_NtkIsSop(pNtk) )
        pNode->pData = Abc_SopRegister( pNtk->pManFunc, " 1\n" );
    else if ( Abc_NtkIsLogicBdd(pNtk) )
        pNode->pData = Cudd_ReadOne(pNtk->pManFunc), Cudd_Ref( pNode->pData );
    else if ( Abc_NtkIsMapped(pNtk) )
        pNode->pData = Mio_LibraryReadConst1(Abc_FrameReadLibGen(Abc_FrameGetGlobalFrame()));
    else
        assert( 0 );
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Creates inverter.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeCreateInv( Abc_Ntk_t * pNtk, Abc_Obj_t * pFanin )
{
    Abc_Obj_t * pNode;
    assert( Abc_NtkIsLogic(pNtk) || Abc_NtkIsNetlist(pNtk) );
    pNode = Abc_NtkCreateNode( pNtk );   
    Abc_ObjAddFanin( pNode, pFanin );
    if ( Abc_NtkIsSop(pNtk) )
        pNode->pData = Abc_SopRegister( pNtk->pManFunc, "0 1\n" );
    else if ( Abc_NtkIsLogicBdd(pNtk) )
        pNode->pData = Cudd_Not(Cudd_bddIthVar(pNtk->pManFunc,0)), Cudd_Ref( pNode->pData );
    else if ( Abc_NtkIsMapped(pNtk) )
        pNode->pData = Mio_LibraryReadInv(Abc_FrameReadLibGen(Abc_FrameGetGlobalFrame()));
    else
        assert( 0 );
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Creates buffer.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeCreateBuf( Abc_Ntk_t * pNtk, Abc_Obj_t * pFanin )
{
    Abc_Obj_t * pNode;
    assert( Abc_NtkIsLogic(pNtk) || Abc_NtkIsNetlist(pNtk) );
    pNode = Abc_NtkCreateNode( pNtk );   
    Abc_ObjAddFanin( pNode, pFanin );
    if ( Abc_NtkIsSop(pNtk) )
        pNode->pData = Abc_SopRegister( pNtk->pManFunc, "1 1\n" );
    else if ( Abc_NtkIsLogicBdd(pNtk) )
        pNode->pData = Cudd_bddIthVar(pNtk->pManFunc,0), Cudd_Ref( pNode->pData );
    else if ( Abc_NtkIsMapped(pNtk) )
        pNode->pData = Mio_LibraryReadBuf(Abc_FrameReadLibGen(Abc_FrameGetGlobalFrame()));
    else
        assert( 0 );
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Creates inverter.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeCreateAnd( Abc_Ntk_t * pNtk, Vec_Ptr_t * vFanins )
{
    Abc_Obj_t * pNode;
    int i;
    assert( Abc_NtkIsLogic(pNtk) );
    pNode = Abc_NtkCreateNode( pNtk );   
    for ( i = 0; i < vFanins->nSize; i++ )
        Abc_ObjAddFanin( pNode, vFanins->pArray[i] );
    if ( Abc_NtkIsSop(pNtk) )
    {
        char * pSop;
        pSop = Extra_MmFlexEntryFetch( pNtk->pManFunc, vFanins->nSize + 4 );
        for ( i = 0; i < vFanins->nSize; i++ )
            pSop[i] = '1';
        pSop[i++] = ' ';
        pSop[i++] = '1';
        pSop[i++] = '\n';
        pSop[i++] = 0;
        assert( i == vFanins->nSize + 4 );
        pNode->pData = pSop;
    }
    else if ( Abc_NtkIsLogicBdd(pNtk) )
    {
        DdManager * dd = pNtk->pManFunc;
        DdNode * bFunc, * bTemp;
        bFunc = Cudd_ReadOne(dd); Cudd_Ref( bFunc );
        for ( i = 0; i < vFanins->nSize; i++ )
        {
            bFunc = Cudd_bddAnd( dd, bTemp = bFunc, Cudd_bddIthVar(pNtk->pManFunc,i) );  Cudd_Ref( bFunc );
            Cudd_RecursiveDeref( dd, bTemp );
        }
        pNode->pData = bFunc;
    }
    else
        assert( 0 );
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Creates inverter.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeCreateOr( Abc_Ntk_t * pNtk, Vec_Ptr_t * vFanins )
{
    Abc_Obj_t * pNode;
    int i;
    assert( Abc_NtkIsLogic(pNtk) );
    pNode = Abc_NtkCreateNode( pNtk );   
    for ( i = 0; i < vFanins->nSize; i++ )
        Abc_ObjAddFanin( pNode, vFanins->pArray[i] );
    if ( Abc_NtkIsSop(pNtk) )
    {
        char * pSop;
        pSop = Extra_MmFlexEntryFetch( pNtk->pManFunc, vFanins->nSize + 4 );
        for ( i = 0; i < vFanins->nSize; i++ )
            pSop[i] = '0';
        pSop[i++] = ' ';
        pSop[i++] = '0';
        pSop[i++] = '\n';
        pSop[i++] = 0;
        assert( i == vFanins->nSize + 4 );
        pNode->pData = pSop;
    }
    else if ( Abc_NtkIsLogicBdd(pNtk) )
    {
        DdManager * dd = pNtk->pManFunc;
        DdNode * bFunc, * bTemp;
        bFunc = Cudd_ReadLogicZero(dd); Cudd_Ref( bFunc );
        for ( i = 0; i < vFanins->nSize; i++ )
        {
            bFunc = Cudd_bddOr( dd, bTemp = bFunc, Cudd_bddIthVar(pNtk->pManFunc,i) );  Cudd_Ref( bFunc );
            Cudd_RecursiveDeref( dd, bTemp );
        }
        pNode->pData = bFunc;
    }
    else
        assert( 0 );
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Creates inverter.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeCreateMux( Abc_Ntk_t * pNtk, Abc_Obj_t * pNodeC, Abc_Obj_t * pNode1, Abc_Obj_t * pNode0 )
{
    Abc_Obj_t * pNode;
    assert( Abc_NtkIsLogic(pNtk) );
    pNode = Abc_NtkCreateNode( pNtk );   
    Abc_ObjAddFanin( pNode, pNodeC );
    Abc_ObjAddFanin( pNode, pNode1 );
    Abc_ObjAddFanin( pNode, pNode0 );
    if ( Abc_NtkIsSop(pNtk) )
        pNode->pData = Abc_SopRegister( pNtk->pManFunc, "11- 1\n0-1 1\n" );
    else if ( Abc_NtkIsLogicBdd(pNtk) )
        pNode->pData = Cudd_bddIte(pNtk->pManFunc,Cudd_bddIthVar(pNtk->pManFunc,0),Cudd_bddIthVar(pNtk->pManFunc,1),Cudd_bddIthVar(pNtk->pManFunc,2)), Cudd_Ref( pNode->pData );
    else
        assert( 0 );
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Clones the given node but does not assign the function.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeClone( Abc_Obj_t * pNode )
{
    Abc_Obj_t * pClone, * pFanin;
    int i;
    assert( Abc_ObjIsNode(pNode) );
    pClone = Abc_NtkCreateNode( pNode->pNtk );   
    Abc_ObjForEachFanin( pNode, pFanin, i )
        Abc_ObjAddFanin( pClone, pFanin );
    return pClone;
}



/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NodeIsConst0( Abc_Obj_t * pNode )    
{ 
    Abc_Ntk_t * pNtk = pNode->pNtk;
    assert(Abc_ObjIsNode(pNode));      
    assert(Abc_NodeIsConst(pNode));
    if ( Abc_NtkIsSop(pNtk) )
        return Abc_SopIsConst0(pNode->pData);
    if ( Abc_NtkIsLogicBdd(pNtk) )
        return Cudd_IsComplement(pNode->pData);
    if ( Abc_NtkIsAig(pNtk) )
        return Abc_ObjNot(pNode) == Abc_AigConst1(pNode->pNtk->pManFunc);
    if ( Abc_NtkIsMapped(pNtk) )
        return pNode->pData == Mio_LibraryReadConst0(Abc_FrameReadLibSuper(Abc_FrameGetGlobalFrame()));
    assert( 0 );
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NodeIsConst1( Abc_Obj_t * pNode )    
{ 
    Abc_Ntk_t * pNtk = pNode->pNtk;
    assert(Abc_ObjIsNode(pNode));      
    assert(Abc_NodeIsConst(pNode));
    if ( Abc_NtkIsSop(pNtk) )
        return Abc_SopIsConst1(pNode->pData);
    if ( Abc_NtkIsLogicBdd(pNtk) )
        return !Cudd_IsComplement(pNode->pData);
    if ( Abc_NtkIsAig(pNtk) )
        return pNode == Abc_AigConst1(pNode->pNtk->pManFunc);
    if ( Abc_NtkIsMapped(pNtk) )
        return pNode->pData == Mio_LibraryReadConst1(Abc_FrameReadLibSuper(Abc_FrameGetGlobalFrame()));
    assert( 0 );
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NodeIsBuf( Abc_Obj_t * pNode )    
{ 
    Abc_Ntk_t * pNtk = pNode->pNtk;
    assert(Abc_ObjIsNode(pNode)); 
    if ( Abc_ObjFaninNum(pNode) != 1 )
        return 0;
    if ( Abc_NtkIsSop(pNtk) )
        return Abc_SopIsBuf(pNode->pData);
    if ( Abc_NtkIsLogicBdd(pNtk) )
        return !Cudd_IsComplement(pNode->pData);
    if ( Abc_NtkIsAig(pNtk) )
        return 0;
    if ( Abc_NtkIsMapped(pNtk) )
        return pNode->pData == Mio_LibraryReadBuf(Abc_FrameReadLibSuper(Abc_FrameGetGlobalFrame()));
    assert( 0 );
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NodeIsInv( Abc_Obj_t * pNode )    
{ 
    Abc_Ntk_t * pNtk = pNode->pNtk;
    assert(Abc_ObjIsNode(pNode)); 
    if ( Abc_ObjFaninNum(pNode) != 1 )
        return 0;
    if ( Abc_NtkIsSop(pNtk) )
        return Abc_SopIsInv(pNode->pData);
    if ( Abc_NtkIsLogicBdd(pNtk) )
        return Cudd_IsComplement(pNode->pData);
    if ( Abc_NtkIsAig(pNtk) )
        return 0;
    if ( Abc_NtkIsMapped(pNtk) )
        return pNode->pData == Mio_LibraryReadInv(Abc_FrameReadLibSuper(Abc_FrameGetGlobalFrame()));
    assert( 0 );
    return 0;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


