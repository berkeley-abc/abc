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
#include "aig/gia/gia.h"

#ifdef ABC_USE_CUDD
#include "bdd/extrab/extraBdd.h"
#endif

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#ifdef ABC_USE_CUDD

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
Abc_Ntk_t * Abc_NtkFromGlobalBdds( Abc_Ntk_t * pNtk )
{
    ProgressBar * pProgress;
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pNode, * pDriver, * pNodeNew;
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
        pNodeNew = Abc_NodeFromGlobalBdds( pNtkNew, dd, (DdNode *)Abc_ObjGlobalBdd(pNode) );
        Abc_ObjAddFanin( pNode->pCopy, pNodeNew );

    }
    Extra_ProgressBarStop( pProgress );
    return pNtkNew;
}
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
    Abc_NtkFreeGlobalBdds( pNtk, 1 );
    if ( pNtkNew == NULL )
        return NULL;

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


#else

Abc_Ntk_t * Abc_NtkCollapse( Abc_Ntk_t * pNtk, int fBddSizeMax, int fDualRail, int fReorder, int fVerbose )
{
    return NULL;
}

#endif



/**Function*************************************************************

  Synopsis    [Derives GIA for the cone of one output and computes its SOP.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkClpOneGia_rec( Gia_Man_t * pNew, Abc_Obj_t * pNode )
{
    int iLit0, iLit1;
    if ( Abc_NodeIsTravIdCurrent(pNode) || Abc_ObjFaninNum(pNode) == 0 )
        return pNode->iTemp;
    assert( Abc_ObjIsNode( pNode ) );
    Abc_NodeSetTravIdCurrent( pNode );
    iLit0 = Abc_NtkClpOneGia_rec( pNew, Abc_ObjFanin0(pNode) );
    iLit1 = Abc_NtkClpOneGia_rec( pNew, Abc_ObjFanin1(pNode) );
    iLit0 = Abc_LitNotCond( iLit0, Abc_ObjFaninC0(pNode) );
    iLit1 = Abc_LitNotCond( iLit1, Abc_ObjFaninC1(pNode) );
    return (pNode->iTemp = Gia_ManHashAnd(pNew, iLit0, iLit1));
}
Gia_Man_t * Abc_NtkClpOneGia( Abc_Ntk_t * pNtk, int iCo, Vec_Int_t * vSupp )
{
    int i, iCi, iLit;
    Abc_Obj_t * pNode;
    Gia_Man_t * pNew, * pTemp;
    pNew = Gia_ManStart( 1000 );
    pNew->pName = Abc_UtilStrsav( pNtk->pName );
    pNew->pSpec = Abc_UtilStrsav( pNtk->pSpec );
    Gia_ManHashStart( pNew );
    // primary inputs
    Abc_AigConst1(pNtk)->iTemp = 1;
    Vec_IntForEachEntry( vSupp, iCi, i )
        Abc_NtkCi(pNtk, iCi)->iTemp = Gia_ManAppendCi(pNew);
    // create the first cone
    Abc_NtkIncrementTravId( pNtk );
    pNode = Abc_NtkCo( pNtk, iCo );
    iLit = Abc_NtkClpOneGia_rec( pNew, Abc_ObjFanin0(pNode) );
    iLit = Abc_LitNotCond( iLit, Abc_ObjFaninC0(pNode) );
    Gia_ManAppendCo( pNew, iLit );
    // perform cleanup
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}
Vec_Str_t * Abc_NtkClpOne( Abc_Ntk_t * pNtk, int iCo, int nCubeLim, int nBTLimit, int fVerbose, int fCanon, Vec_Int_t ** pvSupp )
{
    extern Vec_Int_t * Abc_NtkNodeSupportInt( Abc_Ntk_t * pNtk, int iCo );
    extern Vec_Str_t * Bmc_CollapseOne( Gia_Man_t * p, int nCubeLim, int nBTLimit, int fCanon, int fVerbose );
    Vec_Int_t * vSupp = Abc_NtkNodeSupportInt( pNtk, iCo );
    Gia_Man_t * pGia  = Abc_NtkClpOneGia( pNtk, iCo, vSupp );
    Vec_Str_t * vSop;
    if ( fVerbose )
        printf( "Output %d:\n", iCo );
    vSop = Bmc_CollapseOne( pGia, nCubeLim, nBTLimit, fCanon, fVerbose );
    Gia_ManStop( pGia );
    *pvSupp = vSupp;
    if ( vSop == NULL )
        Vec_IntFree(vSupp);
    else if ( Vec_StrSize(vSop) == 4 ) // constant
        Vec_IntClear(vSupp);
    return vSop; 
}

/**Function*************************************************************

  Synopsis    [SAT-based collapsing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkFromSopsOne( Abc_Ntk_t * pNtkNew, Abc_Ntk_t * pNtk, int iCo, int nCubeLim, int nBTLimit, int fCanon, int fVerbose )
{
    Abc_Obj_t * pNodeNew;
    Vec_Int_t * vSupp;
    Vec_Str_t * vSop;
    int i, iCi;
    // compute SOP of the node
    vSop = Abc_NtkClpOne( pNtk, iCo, nCubeLim, nBTLimit, fVerbose, fCanon, &vSupp );
    if ( vSop == NULL )
        return NULL;
    // create a new node
    pNodeNew = Abc_NtkCreateNode( pNtkNew );
    // add fanins
    Vec_IntForEachEntry( vSupp, iCi, i )
        Abc_ObjAddFanin( pNodeNew, Abc_NtkCi(pNtkNew, iCi) );
    Vec_IntFree( vSupp );
    // transfer the function
    pNodeNew->pData = Abc_SopRegister( (Mem_Flex_t *)pNtkNew->pManFunc, Vec_StrArray(vSop) );
    Vec_StrFree( vSop );
    return pNodeNew;
}
Abc_Ntk_t * Abc_NtkFromSops( Abc_Ntk_t * pNtk, int nCubeLim, int nBTLimit, int fCanon, int fVerbose )
{
    ProgressBar * pProgress;
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pNode, * pDriver, * pNodeNew;
    int i;
    // start the new network
    pNtkNew = Abc_NtkStartFrom( pNtk, ABC_NTK_LOGIC, ABC_FUNC_SOP );
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
/*
        if ( Abc_ObjIsCi(pDriver) )
        {
            pNodeNew = Abc_NtkCreateNode( pNtkNew );
            Abc_ObjAddFanin( pNodeNew, pDriver->pCopy ); // pDriver->pCopy is removed by GIA construction...
            pNodeNew->pData = Abc_SopRegister( (Mem_Flex_t *)pNtkNew->pManFunc, Abc_ObjFaninC0(pNode) ? "0 1\n" : "1 1\n" );
            continue;
        }
*/
        if ( pDriver == Abc_AigConst1(pNtk) )
        {
            pNodeNew = Abc_NtkCreateNode( pNtkNew );
            pNodeNew->pData = Abc_SopRegister( (Mem_Flex_t *)pNtkNew->pManFunc, Abc_ObjFaninC0(pNode) ? " 0\n" : " 1\n" );
            Abc_ObjAddFanin( pNode->pCopy, pNodeNew );
            continue;
        }
        pNodeNew = Abc_NtkFromSopsOne( pNtkNew, pNtk, i, nCubeLim, nBTLimit, fCanon, fVerbose );
        if ( pNodeNew == NULL )
        {
            Abc_NtkDelete( pNtkNew );
            pNtkNew = NULL;
            break;
        }
        Abc_ObjAddFanin( pNode->pCopy, pNodeNew );
    }
    Extra_ProgressBarStop( pProgress );
    return pNtkNew;
}
Abc_Ntk_t * Abc_NtkCollapseSat( Abc_Ntk_t * pNtk, int nCubeLim, int nBTLimit, int fCanon, int fVerbose )
{
    Abc_Ntk_t * pNtkNew;
    assert( Abc_NtkIsStrash(pNtk) );
    // create the new network
    pNtkNew = Abc_NtkFromSops( pNtk, nCubeLim, nBTLimit, fCanon, fVerbose );
    if ( pNtkNew == NULL )
        return NULL;
    if ( pNtk->pExdc )
        pNtkNew->pExdc = Abc_NtkDup( pNtk->pExdc );
    // make sure that everything is okay
    if ( !Abc_NtkCheck( pNtkNew ) )
    {
        printf( "Abc_NtkCollapseSat: The network check has failed.\n" );
        Abc_NtkDelete( pNtkNew );
        return NULL;
    }
    return pNtkNew;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

