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

#include "base/abc/abc.h"

#ifdef ABC_USE_CUDD
#include "misc/extra/extraBdd.h"
#endif

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#ifdef ABC_USE_CUDD

static Abc_Ntk_t * Abc_NtkFromGlobalBdds( Abc_Ntk_t * pNtk );
static Abc_Obj_t * Abc_NodeFromGlobalBdds( Abc_Ntk_t * pNtkNew, DdManager * dd, DdNode * bFunc );

extern int Abc_NodeSupport( DdNode * bFunc, Vec_Str_t * vSupport, int nVars );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Makes nodes minimum base.]

  Description [Returns the number of changed nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeMinimumBase2( Abc_Obj_t * pNode )
{
    Vec_Str_t * vSupport;
    Vec_Ptr_t * vFanins;
    DdNode * bTemp;
    int i, nVars;

    assert( Abc_NtkIsBddLogic(pNode->pNtk) );
    assert( Abc_ObjIsNode(pNode) );

    // compute support
    vSupport = Vec_StrAlloc( 10 );
    nVars = Abc_NodeSupport( Cudd_Regular(pNode->pData), vSupport, Abc_ObjFaninNum(pNode) );
    if ( nVars == Abc_ObjFaninNum(pNode) )
    {
        Vec_StrFree( vSupport );
        return 0;
    }

    // add fanins
    vFanins = Vec_PtrAlloc( Abc_ObjFaninNum(pNode) );
    Abc_NodeCollectFanins( pNode, vFanins );
    Vec_IntClear( &pNode->vFanins );
    for ( i = 0; i < vFanins->nSize; i++ )
        if ( vSupport->pArray[i] != 0 ) // useful
            Vec_IntPush( &pNode->vFanins, Abc_ObjId((Abc_Obj_t *)vFanins->pArray[i]) );
    assert( nVars == Abc_ObjFaninNum(pNode) );

    // update the function of the node
    pNode->pData = Extra_bddRemapUp( (DdManager *)pNode->pNtk->pManFunc, bTemp = (DdNode *)pNode->pData );   Cudd_Ref( (DdNode *)pNode->pData );
    Cudd_RecursiveDeref( (DdManager *)pNode->pNtk->pManFunc, bTemp );
    Vec_PtrFree( vFanins );
    Vec_StrFree( vSupport );
    return 1;
}
int Abc_NtkMinimumBase2( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode, * pFanin;
    int i, k, Counter;
    assert( Abc_NtkIsBddLogic(pNtk) );
    // remove all fanouts
    Abc_NtkForEachObj( pNtk, pNode, i )
        Vec_IntClear( &pNode->vFanouts );
    // add useful fanins
    Counter = 0;
    Abc_NtkForEachNode( pNtk, pNode, i )
        Counter += Abc_NodeMinimumBase2( pNode );
    // add fanouts
    Abc_NtkForEachObj( pNtk, pNode, i )
        Abc_ObjForEachFanin( pNode, pFanin, k )
            Vec_IntPush( &pFanin->vFanouts, Abc_ObjId(pNode) );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Collapses the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkCollapse( Abc_Ntk_t * pNtk, int fBddSizeMax, int fDualRail, int fReorder, int fVerbose )
{
    Abc_Ntk_t * pNtkNew;
    abctime clk = Abc_Clock();

    assert( Abc_NtkIsStrash(pNtk) );
    // compute the global BDDs
    if ( Abc_NtkBuildGlobalBdds(pNtk, fBddSizeMax, 1, fReorder, fVerbose) == NULL )
        return NULL;
    if ( fVerbose )
    {
        DdManager * dd = (DdManager *)Abc_NtkGlobalBddMan( pNtk );
        printf( "Shared BDD size = %6d nodes.  ", Cudd_ReadKeys(dd) - Cudd_ReadDead(dd) );
        ABC_PRT( "BDD construction time", Abc_Clock() - clk );
    }

    // create the new network
    pNtkNew = Abc_NtkFromGlobalBdds( pNtk );
//    Abc_NtkFreeGlobalBdds( pNtk );
    Abc_NtkFreeGlobalBdds( pNtk, 1 );
    if ( pNtkNew == NULL )
    {
//        Cudd_Quit( pNtk->pManGlob );
//        pNtk->pManGlob = NULL;
        return NULL;
    }
//    Extra_StopManager( pNtk->pManGlob );
//    pNtk->pManGlob = NULL;

    // make the network minimum base
    Abc_NtkMinimumBase2( pNtkNew );

    if ( pNtk->pExdc )
        pNtkNew->pExdc = Abc_NtkDup( pNtk->pExdc );

    // make sure that everything is okay
    if ( !Abc_NtkCheck( pNtkNew ) )
    {
        printf( "Abc_NtkCollapse: The network check has failed.\n" );
        Abc_NtkDelete( pNtkNew );
        return NULL;
    }
    return pNtkNew;
}


//int runtime1, runtime2;

/**Function*************************************************************

  Synopsis    [Derives the network with the given global BDD.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkFromGlobalBdds( Abc_Ntk_t * pNtk )
{
//    extern void Extra_ShuffleTest( reo_man * p, DdManager * dd, DdNode * Func );
//    reo_man * pReo;

    ProgressBar * pProgress;
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pNode, * pDriver, * pNodeNew;
//    DdManager * dd = pNtk->pManGlob;
    DdManager * dd = (DdManager *)Abc_NtkGlobalBddMan( pNtk );
    int i;

    // extract don't-care and compute ISOP
    if ( pNtk->pExdc )
    {
        DdManager * ddExdc = NULL;
        DdNode * bBddMin, * bBddDc, * bBddL, * bBddU;
        assert( Abc_NtkIsStrash(pNtk->pExdc) );
        assert( Abc_NtkCoNum(pNtk->pExdc) == 1 );
        // compute the global BDDs
        if ( Abc_NtkBuildGlobalBdds(pNtk->pExdc, 10000000, 1, 1, 0) == NULL )
            return NULL;
        // transfer tot the same manager
        ddExdc = (DdManager *)Abc_NtkGlobalBddMan( pNtk->pExdc );
        bBddDc = (DdNode *)Abc_ObjGlobalBdd(Abc_NtkCo(pNtk->pExdc, 0));
        bBddDc = Cudd_bddTransfer( ddExdc, dd, bBddDc );  Cudd_Ref( bBddDc );
        Abc_NtkFreeGlobalBdds( pNtk->pExdc, 1 );
        // minimize the output
        Abc_NtkForEachCo( pNtk, pNode, i )
        {
            bBddMin = (DdNode *)Abc_ObjGlobalBdd(pNode);
            // derive lower and uppwer bound
            bBddL = Cudd_bddAnd( dd, bBddMin,           Cudd_Not(bBddDc) );  Cudd_Ref( bBddL );
            bBddU = Cudd_bddAnd( dd, Cudd_Not(bBddMin), Cudd_Not(bBddDc) );  Cudd_Ref( bBddU );
            Cudd_RecursiveDeref( dd, bBddMin );
            // compute new one
            bBddMin = Cudd_bddIsop( dd, bBddL, Cudd_Not(bBddU) );            Cudd_Ref( bBddMin );
            Cudd_RecursiveDeref( dd, bBddL );
            Cudd_RecursiveDeref( dd, bBddU );
            // update global BDD
            Abc_ObjSetGlobalBdd( pNode, bBddMin );
            //Extra_bddPrint( dd, bBddMin ); printf( "\n" );
        }
        Cudd_RecursiveDeref( dd, bBddDc );
    }

//    pReo = Extra_ReorderInit( Abc_NtkCiNum(pNtk), 1000 );
//    runtime1 = runtime2 = 0;

    // start the new network
    pNtkNew = Abc_NtkStartFrom( pNtk, ABC_NTK_LOGIC, ABC_FUNC_BDD );
    // make sure the new manager has the same number of inputs
    Cudd_bddIthVar( (DdManager *)pNtkNew->pManFunc, dd->size-1 );
    // process the POs
    pProgress = Extra_ProgressBarStart( stdout, Abc_NtkCoNum(pNtk) );
    Abc_NtkForEachCo( pNtk, pNode, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        pDriver = Abc_ObjFanin0(pNode);
        if ( Abc_ObjIsCi(pDriver) && !strcmp(Abc_ObjName(pNode), Abc_ObjName(pDriver)) )
        {
            Abc_ObjAddFanin( pNode->pCopy, pDriver->pCopy );
            continue;
        }
//        pNodeNew = Abc_NodeFromGlobalBdds( pNtkNew, dd, Vec_PtrEntry(pNtk->vFuncsGlob, i) );
        pNodeNew = Abc_NodeFromGlobalBdds( pNtkNew, dd, (DdNode *)Abc_ObjGlobalBdd(pNode) );
        Abc_ObjAddFanin( pNode->pCopy, pNodeNew );

//        Extra_ShuffleTest( pReo, dd, Abc_ObjGlobalBdd(pNode) );

    }
    Extra_ProgressBarStop( pProgress );

//    Extra_ReorderQuit( pReo );
//ABC_PRT( "Reo ", runtime1 );
//ABC_PRT( "Cudd", runtime2 );

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
    pNodeNew->pData = Extra_TransferLevelByLevel( dd, (DdManager *)pNtkNew->pManFunc, bFunc );  Cudd_Ref( (DdNode *)pNodeNew->pData );
    return pNodeNew;
}

#else

Abc_Ntk_t * Abc_NtkCollapse( Abc_Ntk_t * pNtk, int fBddSizeMax, int fDualRail, int fReorder, int fVerbose )
{
    return NULL;
}

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

