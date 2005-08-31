/**CFile****************************************************************

  FileName    [abcCollapse.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Collapsing the network into two-levels.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcCollapse.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static DdNode *    Abc_NtkGlobalBdds_rec( DdManager * dd, Abc_Obj_t * pNode );
static Abc_Ntk_t * Abc_NtkFromGlobalBdds( Abc_Ntk_t * pNtk );
static Abc_Obj_t * Abc_NodeFromGlobalBdds( Abc_Ntk_t * pNtkNew, DdManager * dd, DdNode * bFunc );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Collapses the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkCollapse( Abc_Ntk_t * pNtk, int fVerbose )
{
    int fCheck = 1;
    Abc_Ntk_t * pNtkNew;

    assert( Abc_NtkIsStrash(pNtk) );

    // compute the global BDDs
    if ( Abc_NtkGlobalBdds(pNtk, 0) == NULL )
        return NULL;
    if ( fVerbose )
        printf( "The shared BDD size is %d nodes.\n", Cudd_ReadKeys(pNtk->pManGlob) - Cudd_ReadDead(pNtk->pManGlob) );

    // create the new network
    pNtkNew = Abc_NtkFromGlobalBdds( pNtk );
    Abc_NtkFreeGlobalBdds( pNtk );
    if ( pNtkNew == NULL )
    {
        Cudd_Quit( pNtk->pManGlob );
        pNtk->pManGlob = NULL;
        return NULL;
    }
    Extra_StopManager( pNtk->pManGlob );
    pNtk->pManGlob = NULL;

    // make the network minimum base
    Abc_NtkMinimumBase( pNtkNew );

    // make sure that everything is okay
    if ( fCheck && !Abc_NtkCheck( pNtkNew ) )
    {
        printf( "Abc_NtkCollapse: The network check has failed.\n" );
        Abc_NtkDelete( pNtkNew );
        return NULL;
    }
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Derives global BDDs for the node function.]

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
    pNode = Abc_AigConst1( pNtk->pManFunc );
    pNode->pCopy = (Abc_Obj_t *)dd->one;   Cudd_Ref( dd->one );

    vFuncsGlob = Vec_PtrAlloc( 100 );
    if ( fLatchOnly )
    {
        // construct the BDDs
        pProgress = Extra_ProgressBarStart( stdout, Abc_NtkLatchNum(pNtk) );
        Abc_NtkForEachLatch( pNtk, pNode, i )
        {
            Extra_ProgressBarUpdate( pProgress, i, NULL );
            bFunc = Abc_NtkGlobalBdds_rec( dd, Abc_ObjFanin0(pNode) );
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
            bFunc = Abc_NtkGlobalBdds_rec( dd, Abc_ObjFanin0(pNode) );
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

  Synopsis    [Derives the global BDD of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdNode * Abc_NtkGlobalBdds_rec( DdManager * dd, Abc_Obj_t * pNode )
{
    DdNode * bFunc, * bFunc0, * bFunc1;
    assert( !Abc_ObjIsComplement(pNode) );
    if ( Cudd_ReadKeys(dd) > 500000 )
        return NULL;
    // if the result is available return
    if ( pNode->pCopy )
        return (DdNode *)pNode->pCopy;
    // compute the result for both branches
    bFunc0 = Abc_NtkGlobalBdds_rec( dd, Abc_ObjFanin(pNode,0) ); 
    if ( bFunc0 == NULL )
        return NULL;
    Cudd_Ref( bFunc0 );
    bFunc1 = Abc_NtkGlobalBdds_rec( dd, Abc_ObjFanin(pNode,1) ); 
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

  Synopsis    [Derives the network with the given global BDD.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkFromGlobalBdds( Abc_Ntk_t * pNtk )
{
    ProgressBar * pProgress;
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pNode, * pNodeNew;
    DdManager * dd = pNtk->pManGlob;
    int i;
    // start the new network
    pNtkNew = Abc_NtkStartFrom( pNtk, ABC_TYPE_LOGIC, ABC_FUNC_BDD );
    // make sure the new manager has the same number of inputs
    Cudd_bddIthVar( pNtkNew->pManFunc, dd->size-1 );
    // process the POs
    pProgress = Extra_ProgressBarStart( stdout, Abc_NtkCoNum(pNtk) );
    Abc_NtkForEachCo( pNtk, pNode, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        pNodeNew = Abc_NodeFromGlobalBdds( pNtkNew, dd, Vec_PtrEntry(pNtk->vFuncsGlob, i) );
        Abc_ObjAddFanin( pNode->pCopy, pNodeNew );
    }
    Extra_ProgressBarStop( pProgress );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Derives the network with the given global BDD.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeFromGlobalBdds( Abc_Ntk_t * pNtkNew, DdManager * dd, DdNode * bFunc )
{
    Abc_Obj_t * pNodeNew, * pTemp;
    int i;
    // create a new node
    pNodeNew = Abc_NtkCreateNode( pNtkNew );
    // add the fanins in the order, in which they appear in the reordered manager
    Abc_NtkForEachCi( pNtkNew, pTemp, i )
        Abc_ObjAddFanin( pNodeNew, Abc_NtkCi(pNtkNew, dd->invperm[i]) );
    // transfer the function
    pNodeNew->pData = Extra_TransferLevelByLevel( dd, pNtkNew->pManFunc, bFunc );  Cudd_Ref( pNodeNew->pData );
    return pNodeNew;
}

/**Function*************************************************************

  Synopsis    [Dereferences global functions of the network.]

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


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


