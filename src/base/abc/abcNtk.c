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
#include "main.h"
#include "mio.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define ABC_NUM_STEPS  10

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates a new Ntk.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkAlloc( Abc_NtkType_t Type, Abc_NtkFunc_t Func )
{
    Abc_Ntk_t * pNtk;
    pNtk = ALLOC( Abc_Ntk_t, 1 );
    memset( pNtk, 0, sizeof(Abc_Ntk_t) );
    pNtk->ntkType     = Type;
    pNtk->ntkFunc     = Func;
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
    if ( Abc_NtkHasSop(pNtk) )
        pNtk->pManFunc = Extra_MmFlexStart();
    else if ( Abc_NtkHasBdd(pNtk) )
        pNtk->pManFunc = Cudd_Init( 20, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );
    else if ( Abc_NtkHasAig(pNtk) )
        pNtk->pManFunc = Abc_AigAlloc( pNtk );
    else if ( Abc_NtkHasMapping(pNtk) )
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
Abc_Ntk_t * Abc_NtkStartFrom( Abc_Ntk_t * pNtk, Abc_NtkType_t Type, Abc_NtkFunc_t Func )
{
    Abc_Ntk_t * pNtkNew; 
    Abc_Obj_t * pObj, * pObjNew;
    int i;
    if ( pNtk == NULL )
        return NULL;
    // start the network
    pNtkNew = Abc_NtkAlloc( Type, Func );
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

  Synopsis    [Finalizes the network using the existing network as a model.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkFinalizeRegular( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkNew )
{
    Abc_Obj_t * pObj, * pDriver, * pDriverNew;
    int i;
    // set the COs of the strashed network
    Abc_NtkForEachCo( pNtk, pObj, i )
    {
        pDriver    = Abc_ObjFanin0Ntk( Abc_ObjFanin0(pObj) );
        pDriverNew = pDriver->pCopy;
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
    pNtkNew = Abc_NtkAlloc( ABC_TYPE_NETLIST, ABC_FUNC_SOP );
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
    pNtkNew = Abc_NtkStartFrom( pNtk, pNtk->ntkType, pNtk->ntkFunc );
    // copy the internal nodes
    if ( Abc_NtkHasAig(pNtk) )
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

    assert( Abc_NtkIsLogic(pNtk) || Abc_NtkIsStrash(pNtk) );
    assert( Abc_ObjIsCo(pNode) ); 
    
    // start the network
    pNtkNew = Abc_NtkAlloc( pNtk->ntkType, pNtk->ntkFunc );
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
    if ( Abc_NtkIsStrash(pNtk) )
        Abc_AigConst1(pNtk->pManFunc)->pCopy = Abc_AigConst1(pNtkNew->pManFunc);

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
    pNtkNew = Abc_NtkAlloc( ABC_TYPE_STRASH, ABC_FUNC_AIG );
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
Abc_Ntk_t * Abc_NtkSplitNode( Abc_Ntk_t * pNtk, Abc_Obj_t * pNode )
{    
    Abc_Ntk_t * pNtkNew; 
    Abc_Obj_t * pFanin, * pNodePo;
    int i;
    // start the network
    pNtkNew = Abc_NtkAlloc( pNtk->ntkType, pNtk->ntkFunc );
    pNtkNew->pName = util_strsav(Abc_ObjName(pNode));
    // add the PIs corresponding to the fanins of the node
    Abc_ObjForEachFanin( pNode, pFanin, i )
    {
        pFanin->pCopy = Abc_NtkCreatePi( pNtkNew );
        Abc_NtkLogicStoreName( pFanin->pCopy, Abc_ObjName(pFanin) );
    }
    // duplicate and connect the node
    pNode->pCopy = Abc_NtkDupObj( pNtkNew, pNode );
    Abc_ObjForEachFanin( pNode, pFanin, i )
        Abc_ObjAddFanin( pNode->pCopy, pFanin->pCopy );
    // create the only PO
    pNodePo = Abc_NtkCreatePo( pNtkNew );
    Abc_ObjAddFanin( pNodePo, pNode->pCopy );
    Abc_NtkLogicStoreName( pNodePo, Abc_ObjName(pNode) );
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkSplitNode(): Network check has failed.\n" );
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
    if ( Abc_NtkHasBdd(pNtk) )
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
    if ( Abc_NtkHasSop(pNtk) )
        Extra_MmFlexStop( pNtk->pManFunc, 0 );
    else if ( Abc_NtkHasBdd(pNtk) )
        Extra_StopManager( pNtk->pManFunc );
    else if ( Abc_NtkHasAig(pNtk) )
        Abc_AigFree( pNtk->pManFunc );
    else if ( !Abc_NtkHasMapping(pNtk) )
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




////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


