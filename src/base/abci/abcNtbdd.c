/**CFile****************************************************************

  FileName    [abcNtbdd.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Procedures to translate between the BDD and the network.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcNtbdd.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void        Abc_NtkBddToMuxesPerform( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkNew );
static Abc_Obj_t * Abc_NodeBddToMuxes( Abc_Obj_t * pNodeOld, Abc_Ntk_t * pNtkNew );
static Abc_Obj_t * Abc_NodeBddToMuxes_rec( DdManager * dd, DdNode * bFunc, Abc_Ntk_t * pNtkNew, st_table * tBdd2Node );
static DdNode *    Abc_NodeGlobalBdds_rec( DdManager * dd, Abc_Obj_t * pNode );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Constructs the network isomorphic to the given BDD.]

  Description [Assumes that the BDD depends on the variables whose indexes
  correspond to the names in the array (pNamesPi). Otherwise, returns NULL.
  The resulting network comes with one node, whose functionality is
  equal to the given BDD. To decompose this BDD into the network of
  multiplexers use Abc_NtkBddToMuxes(). To decompose this BDD into
  an And-Inverter Graph, use Abc_NtkStrash().]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDeriveFromBdd( DdManager * dd, DdNode * bFunc, char * pNamePo, Vec_Ptr_t * vNamesPi )
{
    Abc_Ntk_t * pNtk; 
    Vec_Ptr_t * vNamesPiFake = NULL;
    Abc_Obj_t * pNode, * pNodePi, * pNodePo;
    DdNode * bSupp, * bTemp;
    char * pName;
    int i;

    // supply fake names if real names are not given
    if ( pNamePo == NULL )
        pNamePo = "F";
    if ( vNamesPi == NULL )
    {
        vNamesPiFake = Abc_NodeGetFakeNames( dd->size );
        vNamesPi = vNamesPiFake;
    }

    // make sure BDD depends on the variables whose index 
    // does not exceed the size of the array with PI names
    bSupp = Cudd_Support( dd, bFunc );   Cudd_Ref( bSupp );
    for ( bTemp = bSupp; bTemp != Cudd_ReadOne(dd); bTemp = cuddT(bTemp) )
        if ( (int)Cudd_NodeReadIndex(bTemp) >= Vec_PtrSize(vNamesPi) )
            break;
    Cudd_RecursiveDeref( dd, bSupp );
    if ( bTemp != Cudd_ReadOne(dd) )
        return NULL;

    // start the network
    pNtk = Abc_NtkAlloc( ABC_NTK_LOGIC, ABC_FUNC_BDD );
    pNtk->pName = util_strsav(pNamePo);
    // make sure the new manager has enough inputs
    Cudd_bddIthVar( pNtk->pManFunc, Vec_PtrSize(vNamesPi) );
    // add the PIs corresponding to the names
    Vec_PtrForEachEntry( vNamesPi, pName, i )
        Abc_NtkLogicStoreName( Abc_NtkCreatePi(pNtk), pName );
    // create the node
    pNode = Abc_NtkCreateNode( pNtk );
    pNode->pData = Cudd_bddTransfer( dd, pNtk->pManFunc, bFunc ); Cudd_Ref(pNode->pData);
    Abc_NtkForEachPi( pNtk, pNodePi, i )
        Abc_ObjAddFanin( pNode, pNodePi );
    // create the only PO
    pNodePo = Abc_NtkCreatePo( pNtk );
    Abc_ObjAddFanin( pNodePo, pNode );
    Abc_NtkLogicStoreName( pNodePo, pNamePo );
    // make the network minimum base
    Abc_NtkMinimumBase( pNtk );
    if ( vNamesPiFake )
        Abc_NodeFreeNames( vNamesPiFake );
    if ( !Abc_NtkCheck( pNtk ) )
        fprintf( stdout, "Abc_NtkDeriveFromBdd(): Network check has failed.\n" );
    return pNtk;
}



/**Function*************************************************************

  Synopsis    [Creates the network isomorphic to the union of local BDDs of the nodes.]

  Description [The nodes of the local BDDs are converted into the network nodes 
  with logic functions equal to the MUX.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkBddToMuxes( Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkNew;
    assert( Abc_NtkIsBddLogic(pNtk) );
    pNtkNew = Abc_NtkStartFrom( pNtk, ABC_NTK_LOGIC, ABC_FUNC_SOP );
    Abc_NtkBddToMuxesPerform( pNtk, pNtkNew );
    Abc_NtkFinalize( pNtk, pNtkNew );
    // make sure everything is okay
    if ( !Abc_NtkCheck( pNtkNew ) )
    {
        printf( "Abc_NtkBddToMuxes: The network check has failed.\n" );
        Abc_NtkDelete( pNtkNew );
        return NULL;
    }
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Converts the network to MUXes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkBddToMuxesPerform( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkNew )
{
    ProgressBar * pProgress;
    DdManager * dd = pNtk->pManFunc;
    Abc_Obj_t * pNode, * pNodeNew;
    Vec_Ptr_t * vNodes;
    int i;
    // perform conversion in the topological order
    vNodes = Abc_NtkDfs( pNtk, 0 );
    pProgress = Extra_ProgressBarStart( stdout, vNodes->nSize );
    Vec_PtrForEachEntry( vNodes, pNode, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        // convert one node
        assert( Abc_ObjIsNode(pNode) );
        pNodeNew = Abc_NodeBddToMuxes( pNode, pNtkNew );
        // mark the old node with the new one
        assert( pNode->pCopy == NULL );
        pNode->pCopy = pNodeNew;
    }
    Vec_PtrFree( vNodes );
    Extra_ProgressBarStop( pProgress );
}

/**Function*************************************************************

  Synopsis    [Converts the node to MUXes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeBddToMuxes( Abc_Obj_t * pNodeOld, Abc_Ntk_t * pNtkNew )
{
    DdManager * dd = pNodeOld->pNtk->pManFunc;
    DdNode * bFunc = pNodeOld->pData;
    Abc_Obj_t * pFaninOld, * pNodeNew;
    st_table * tBdd2Node;
    int i;
    // create the table mapping BDD nodes into the ABC nodes
    tBdd2Node = st_init_table( st_ptrcmp, st_ptrhash );
    // add the constant and the elementary vars
    st_insert( tBdd2Node, (char *)b1, (char *)Abc_NtkConst1(pNtkNew) );
    Abc_ObjForEachFanin( pNodeOld, pFaninOld, i )
        st_insert( tBdd2Node, (char *)Cudd_bddIthVar(dd, i), (char *)pFaninOld->pCopy );
    // create the new nodes recursively
    pNodeNew = Abc_NodeBddToMuxes_rec( dd, Cudd_Regular(bFunc), pNtkNew, tBdd2Node );
    st_free_table( tBdd2Node );
    if ( Cudd_IsComplement(bFunc) )
        pNodeNew = Abc_NodeCreateInv( pNtkNew, pNodeNew );
    return pNodeNew;
}

/**Function*************************************************************

  Synopsis    [Converts the node to MUXes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeBddToMuxes_rec( DdManager * dd, DdNode * bFunc, Abc_Ntk_t * pNtkNew, st_table * tBdd2Node )
{
    Abc_Obj_t * pNodeNew, * pNodeNew0, * pNodeNew1, * pNodeNewC;
    assert( !Cudd_IsComplement(bFunc) );
    if ( st_lookup( tBdd2Node, (char *)bFunc, (char **)&pNodeNew ) )
        return pNodeNew;
    // solve for the children nodes
    pNodeNew0 = Abc_NodeBddToMuxes_rec( dd, Cudd_Regular(cuddE(bFunc)), pNtkNew, tBdd2Node );
    if ( Cudd_IsComplement(cuddE(bFunc)) )
        pNodeNew0 = Abc_NodeCreateInv( pNtkNew, pNodeNew0 );
    pNodeNew1 = Abc_NodeBddToMuxes_rec( dd, cuddT(bFunc), pNtkNew, tBdd2Node );
    if ( !st_lookup( tBdd2Node, (char *)Cudd_bddIthVar(dd, bFunc->index), (char **)&pNodeNewC ) )
        assert( 0 );
    // create the MUX node
    pNodeNew = Abc_NodeCreateMux( pNtkNew, pNodeNewC, pNodeNew1, pNodeNew0 );
    st_insert( tBdd2Node, (char *)bFunc, (char *)pNodeNew );
    return pNodeNew;
}


/**Function*************************************************************

  Synopsis    [Derives global BDDs for the COs of the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdManager * Abc_NtkGlobalBdds( Abc_Ntk_t * pNtk, int fLatchOnly )
{
    int fReorder = 1;
    ProgressBar * pProgress;
    Vec_Ptr_t * vFuncsGlob;
    Abc_Obj_t * pNode;
    DdNode * bFunc;
    DdManager * dd;
    int i;

    // start the manager
    assert( pNtk->pManGlob == NULL );
    dd = Cudd_Init( Abc_NtkCiNum(pNtk), 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );
    if ( fReorder )
        Cudd_AutodynEnable( dd, CUDD_REORDER_SYMM_SIFT );

    // set the elementary variables
    Abc_NtkCleanCopy( pNtk );
    Abc_NtkForEachCi( pNtk, pNode, i )
        pNode->pCopy = (Abc_Obj_t *)dd->vars[i]; 
    // assign the constant node BDD
    pNode = Abc_NtkConst1( pNtk );
    pNode->pCopy = (Abc_Obj_t *)dd->one;   Cudd_Ref( dd->one );

    // collect the global functions of the COs
    vFuncsGlob = Vec_PtrAlloc( 100 );
    if ( fLatchOnly )
    {
        // construct the BDDs
        pProgress = Extra_ProgressBarStart( stdout, Abc_NtkLatchNum(pNtk) );
        Abc_NtkForEachLatch( pNtk, pNode, i )
        {
            Extra_ProgressBarUpdate( pProgress, i, NULL );
            bFunc = Abc_NodeGlobalBdds_rec( dd, Abc_ObjFanin0(pNode) );
            if ( bFunc == NULL )
            {
                printf( "Constructing global BDDs timed out.\n" );
                Extra_ProgressBarStop( pProgress );
                Cudd_Quit( dd );
                return NULL;
            }
            bFunc = Cudd_NotCond( bFunc, Abc_ObjFaninC0(pNode) );   Cudd_Ref( bFunc );
            Vec_PtrPush( vFuncsGlob, bFunc );
        }
        Extra_ProgressBarStop( pProgress );
    }
    else
    {
        // construct the BDDs
        pProgress = Extra_ProgressBarStart( stdout, Abc_NtkCoNum(pNtk) );
        Abc_NtkForEachCo( pNtk, pNode, i )
        {
            Extra_ProgressBarUpdate( pProgress, i, NULL );
            bFunc = Abc_NodeGlobalBdds_rec( dd, Abc_ObjFanin0(pNode) );
            if ( bFunc == NULL )
            {
                printf( "Constructing global BDDs timed out.\n" );
                Extra_ProgressBarStop( pProgress );
                Cudd_Quit( dd );
                return NULL;
            }
            bFunc = Cudd_NotCond( bFunc, Abc_ObjFaninC0(pNode) );   Cudd_Ref( bFunc );
            Vec_PtrPush( vFuncsGlob, bFunc );
        }
        Extra_ProgressBarStop( pProgress );
    }

    // derefence the intermediate BDDs
    Abc_NtkForEachNode( pNtk, pNode, i )
        if ( pNode->pCopy ) 
        {
            Cudd_RecursiveDeref( dd, (DdNode *)pNode->pCopy );
            pNode->pCopy = NULL;
        }
    // reorder one more time
    if ( fReorder )
    {
        Cudd_ReduceHeap( dd, CUDD_REORDER_SYMM_SIFT, 1 );
        Cudd_AutodynDisable( dd );
    }
    pNtk->pManGlob = dd;
    pNtk->vFuncsGlob = vFuncsGlob;
    return dd;
}

/**Function*************************************************************

  Synopsis    [Derives the global BDD for one AIG node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdNode * Abc_NodeGlobalBdds_rec( DdManager * dd, Abc_Obj_t * pNode )
{
    DdNode * bFunc, * bFunc0, * bFunc1;
    assert( !Abc_ObjIsComplement(pNode) );
    if ( Cudd_ReadKeys(dd) > 5000000 )
        return NULL;
    // if the result is available return
    if ( pNode->pCopy )
        return (DdNode *)pNode->pCopy;
    // compute the result for both branches
    bFunc0 = Abc_NodeGlobalBdds_rec( dd, Abc_ObjFanin(pNode,0) ); 
    if ( bFunc0 == NULL )
        return NULL;
    Cudd_Ref( bFunc0 );
    bFunc1 = Abc_NodeGlobalBdds_rec( dd, Abc_ObjFanin(pNode,1) ); 
    if ( bFunc1 == NULL )
        return NULL;
    Cudd_Ref( bFunc1 );
    bFunc0 = Cudd_NotCond( bFunc0, Abc_ObjFaninC0(pNode) );
    bFunc1 = Cudd_NotCond( bFunc1, Abc_ObjFaninC1(pNode) );
    // get the final result
    bFunc = Cudd_bddAnd( dd, bFunc0, bFunc1 );   Cudd_Ref( bFunc );
    Cudd_RecursiveDeref( dd, bFunc0 );
    Cudd_RecursiveDeref( dd, bFunc1 );
    // set the result
    assert( pNode->pCopy == NULL );
    pNode->pCopy = (Abc_Obj_t *)bFunc;
    return bFunc;
}

/**Function*************************************************************

  Synopsis    [Dereferences global BDDs of the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkFreeGlobalBdds( Abc_Ntk_t * pNtk )
{
    DdNode * bFunc;
    int i;
    assert( pNtk->pManGlob );
    assert( pNtk->vFuncsGlob );
    Vec_PtrForEachEntry( pNtk->vFuncsGlob, bFunc, i )
        Cudd_RecursiveDeref( pNtk->pManGlob, bFunc );
    Vec_PtrFree( pNtk->vFuncsGlob );
    pNtk->vFuncsGlob = NULL;
}

/**Function*************************************************************

  Synopsis    [Computes the BDD of the logic cone of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
double Abc_NtkSpacePercentage( Abc_Obj_t * pNode )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pObj, * pNodeR;
    DdManager * dd;
    DdNode * bFunc;
    double Result;
    int i;
    pNodeR = Abc_ObjRegular(pNode);
    assert( Abc_NtkIsStrash(pNodeR->pNtk) );
    Abc_NtkCleanCopy( pNodeR->pNtk );
    // get the CIs in the support of the node
    vNodes = Abc_NtkNodeSupport( pNodeR->pNtk, &pNodeR, 1 );
    // start the manager
    dd = Cudd_Init( Vec_PtrSize(vNodes), 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );
    Cudd_AutodynEnable( dd, CUDD_REORDER_SYMM_SIFT );
    // assign elementary BDDs for the CIs
    Vec_PtrForEachEntry( vNodes, pObj, i )
        pObj->pCopy = (Abc_Obj_t *)dd->vars[i];
    // build the BDD of the cone
    bFunc = Abc_NodeGlobalBdds_rec( dd, pNodeR );  Cudd_Ref( bFunc );
    bFunc = Cudd_NotCond( bFunc, pNode != pNodeR );
    // count minterms
    Result = Cudd_CountMinterm( dd, bFunc, dd->size );
    // get the percentagle
    Result *= 100.0;
    for ( i = 0; i < dd->size; i++ )
        Result /= 2;
    // clean up
    Cudd_Quit( dd );
    Vec_PtrFree( vNodes );
    return Result;
}



#include "reo.h"

/**Function*************************************************************

  Synopsis    [Reorders BDD of the local function of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeBddReorder( reo_man * p, Abc_Obj_t * pNode )
{
    Abc_Obj_t * pFanin;
    DdNode * bFunc;
    int * pOrder, i;
    // create the temporary array for the variable order
    pOrder = ALLOC( int, Abc_ObjFaninNum(pNode) );
    for ( i = 0; i < Abc_ObjFaninNum(pNode); i++ )
        pOrder[i] = -1;
    // reorder the BDD
    bFunc = Extra_Reorder( p, pNode->pNtk->pManFunc, pNode->pData, pOrder ); Cudd_Ref( bFunc );
    Cudd_RecursiveDeref( pNode->pNtk->pManFunc, pNode->pData );
    pNode->pData = bFunc;
    // update the fanin order
    Abc_ObjForEachFanin( pNode, pFanin, i )
        pOrder[i] = pNode->vFanins.pArray[ pOrder[i] ];
    Abc_ObjForEachFanin( pNode, pFanin, i )
        pNode->vFanins.pArray[i] = pOrder[i];
    free( pOrder );
}

/**Function*************************************************************

  Synopsis    [Reorders BDDs of the local functions.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkBddReorder( Abc_Ntk_t * pNtk, int fVerbose )
{
    reo_man * p;
    Abc_Obj_t * pNode;
    int i;
    p = Extra_ReorderInit( Abc_NtkGetFaninMax(pNtk), 100 );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        if ( Abc_ObjFaninNum(pNode) < 3 )
            continue;
        if ( fVerbose )
            fprintf( stdout, "%10s: ", Abc_ObjName(pNode) );
        if ( fVerbose )
            fprintf( stdout, "Before = %5d  BDD nodes.  ", Cudd_DagSize(pNode->pData) );
        Abc_NodeBddReorder( p, pNode );
        if ( fVerbose )
            fprintf( stdout, "After = %5d  BDD nodes.\n", Cudd_DagSize(pNode->pData) );
    }
    Extra_ReorderQuit( p );
}



/**Function*************************************************************

  Synopsis    [Experiment with BDD-based representation of implications.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkBddImplicationTest()
{
    DdManager * dd;
    DdNode * bImp, * bSum, * bTemp;
    int nVars = 200;
    int nImps = 200;
    int i, clk;
clk = clock();
    dd = Cudd_Init( nVars, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );
    Cudd_AutodynEnable( dd, CUDD_REORDER_SIFT );
    bSum = b0;   Cudd_Ref( bSum );
    for ( i = 0; i < nImps; i++ )
    {
        printf( "." );
        bImp = Cudd_bddAnd( dd, dd->vars[rand()%nVars], dd->vars[rand()%nVars] );  Cudd_Ref( bImp );
        bSum = Cudd_bddOr( dd, bTemp = bSum, bImp );     Cudd_Ref( bSum );
        Cudd_RecursiveDeref( dd, bTemp );
        Cudd_RecursiveDeref( dd, bImp );
    }
    printf( "The BDD before = %d.\n", Cudd_DagSize(bSum) );
    Cudd_ReduceHeap( dd, CUDD_REORDER_SIFT, 1 );
    printf( "The BDD after  = %d.\n", Cudd_DagSize(bSum) );
PRT( "Time", clock() - clk );
    Cudd_RecursiveDeref( dd, bSum );
    Cudd_Quit( dd );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


