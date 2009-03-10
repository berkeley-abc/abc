/**CFile****************************************************************

  FileName    [abcLutmin.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Minimization of the number of LUTs.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcLutmin.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Converts the node to MUXes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkCreateNodeLut( Abc_Ntk_t * pNtkNew, DdManager * dd, DdNode * bFunc, Abc_Obj_t * pNode, int nLutSize )
{
    DdNode * bFuncNew;
    Abc_Obj_t * pNodeNew;
    int i, nStart = ABC_MIN( 0, Abc_ObjFaninNum(pNode) - nLutSize );
    // create a new node
    pNodeNew = Abc_NtkCreateNode( pNtkNew );
    // add the fanins in the order, in which they appear in the reordered manager
    for ( i = nStart; i < Abc_ObjFaninNum(pNode); i++ )
        Abc_ObjAddFanin( pNodeNew, Abc_ObjFanin(pNode, i)->pCopy );
    // transfer the function
    bFuncNew = Extra_bddMove( dd, bFunc, nStart );  Cudd_Ref( bFuncNew );
    assert( Cudd_SupportSize(dd, bFuncNew) <= nLutSize );
    pNodeNew->pData = Extra_TransferLevelByLevel( dd, pNtkNew->pManFunc, bFuncNew );  Cudd_Ref( pNodeNew->pData );
    Cudd_RecursiveDeref( dd, bFuncNew );
    return pNodeNew;
}

/**Function*************************************************************

  Synopsis    [Converts the node to MUXes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeBddToMuxesLut_rec( DdManager * dd, DdNode * bFunc, Abc_Ntk_t * pNtkNew, st_table * tBdd2Node, Abc_Obj_t * pNode, int nLutSize )
{
    Abc_Obj_t * pNodeNew, * pNodeNew0, * pNodeNew1, * pNodeNewC;
    assert( !Cudd_IsComplement(bFunc) );
    if ( bFunc == b1 )
        return Abc_NtkCreateNodeConst1(pNtkNew);
    if ( st_lookup( tBdd2Node, (char *)bFunc, (char **)&pNodeNew ) )
        return pNodeNew;
    if ( dd->perm[bFunc->index] >= Abc_ObjFaninNum(pNode) - nLutSize )
    {
        pNodeNew = Abc_NtkCreateNodeLut( pNtkNew, dd, bFunc, pNode, nLutSize );
        st_insert( tBdd2Node, (char *)bFunc, (char *)pNodeNew );
        return pNodeNew;
    }
    // solve for the children nodes
    pNodeNew0 = Abc_NodeBddToMuxesLut_rec( dd, Cudd_Regular(cuddE(bFunc)), pNtkNew, tBdd2Node, pNode, nLutSize );
    if ( Cudd_IsComplement(cuddE(bFunc)) )
        pNodeNew0 = Abc_NtkCreateNodeInv( pNtkNew, pNodeNew0 );
    pNodeNew1 = Abc_NodeBddToMuxesLut_rec( dd, cuddT(bFunc), pNtkNew, tBdd2Node, pNode, nLutSize );
    if ( !st_lookup( tBdd2Node, (char *)Cudd_bddIthVar(dd, bFunc->index), (char **)&pNodeNewC ) )
        assert( 0 );
    // create the MUX node
    pNodeNew = Abc_NtkCreateNodeMux( pNtkNew, pNodeNewC, pNodeNew1, pNodeNew0 );
    st_insert( tBdd2Node, (char *)bFunc, (char *)pNodeNew );
    return pNodeNew;
}

/**Function*************************************************************

  Synopsis    [Converts the node to MUXes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeBddToMuxesLut( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pNodeOld, int nLutSize )
{
    DdManager * dd = pNodeOld->pNtk->pManFunc;
    DdNode * bFunc = pNodeOld->pData;
    Abc_Obj_t * pFaninOld, * pNodeNew;
    st_table * tBdd2Node;
    int i;
    // create the table mapping BDD nodes into the ABC nodes
    tBdd2Node = st_init_table( st_ptrcmp, st_ptrhash );
    // add the constant and the elementary vars
    Abc_ObjForEachFanin( pNodeOld, pFaninOld, i )
        st_insert( tBdd2Node, (char *)Cudd_bddIthVar(dd, i), (char *)pFaninOld->pCopy );
    // create the new nodes recursively
    pNodeNew = Abc_NodeBddToMuxesLut_rec( dd, Cudd_Regular(bFunc), pNtkNew, tBdd2Node, pNodeOld, nLutSize );
    st_free_table( tBdd2Node );
    if ( Cudd_IsComplement(bFunc) )
        pNodeNew = Abc_NtkCreateNodeInv( pNtkNew, pNodeNew );
    return pNodeNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkLutminConstruct( Abc_Ntk_t * pNtkClp, Abc_Ntk_t * pNtkDec, int nLutSize )
{
    Abc_Obj_t * pObj, * pDriver;
    int i;
    Abc_NtkForEachCo( pNtkClp, pObj, i )
    {
        pDriver = Abc_ObjFanin0( pObj );
        if ( !Abc_ObjIsNode(pDriver) )
            continue;
        if ( Abc_ObjFaninNum(pDriver) == 0 )
            pDriver->pCopy = Abc_NtkDupObj( pNtkDec, pDriver, 0 );
        else
            pDriver->pCopy = Abc_NodeBddToMuxesLut( pNtkDec, pDriver, nLutSize );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkLutmin( Abc_Ntk_t * pNtk, int nLutSize, int fVerbose )
{
    extern void Abc_NtkBddReorder( Abc_Ntk_t * pNtk, int fVerbose );
    Abc_Ntk_t * pNtkDec, * pNtkClp, * pTemp;
    // collapse the network and reorder BDDs
    if ( Abc_NtkIsStrash(pNtk) )
        pTemp = Abc_NtkDup( pNtk );
    else
        pTemp = Abc_NtkStrash( pNtk, 0, 1, 0 );
    pNtkClp = Abc_NtkCollapse( pTemp, 10000, 0, 1, 0 );
    Abc_NtkDelete( pTemp );
    if ( pNtkClp == NULL )
        return NULL;
    if ( !Abc_NtkIsBddLogic(pNtkClp) )
        Abc_NtkToBdd( pNtkClp );
    Abc_NtkBddReorder( pNtkClp, fVerbose );
    // decompose one output at a time
    pNtkDec = Abc_NtkStartFrom( pNtkClp, ABC_NTK_LOGIC, ABC_FUNC_BDD );
    // make sure the new manager has enough inputs
    Cudd_bddIthVar( pNtkDec->pManFunc, nLutSize );
    // put the results into the new network (save new CO drivers in old CO drivers)
    Abc_NtkLutminConstruct( pNtkClp, pNtkDec, nLutSize );
    // finalize the new network
    Abc_NtkFinalize( pNtkClp, pNtkDec );
    Abc_NtkDelete( pNtkClp );
    // make the network minimum base
    Abc_NtkMinimumBase( pNtkDec );
    // fix the problem with complemented and duplicated CO edges
    Abc_NtkLogicMakeSimpleCos( pNtkDec, 0 );
    // make sure everything is okay
    if ( !Abc_NtkCheck( pNtkDec ) )
    {
        printf( "Abc_NtkLutmin: The network check has failed.\n" );
        return 0;
    }
    return pNtkDec;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


