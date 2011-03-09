/**CFile****************************************************************

  FileName    [abcCascade.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Collapsing the network into two-levels.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcCollapse.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "reo.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define BDD_FUNC_MAX 256

//extern void Abc_NodeShowBddOne( DdManager * dd, DdNode * bFunc );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Find the constant node corresponding to the encoded output value.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdNode * Abc_NtkBddFindAddConst( DdManager * dd, DdNode * bFunc, int nOuts )
{
    int i, TermMask = 0;
    DdNode * bFunc0, * bFunc1, * bConst0, * bConst1;
    bConst0 = Cudd_ReadLogicZero( dd );
    bConst1 = Cudd_ReadOne( dd );
    for ( i = 0; i < nOuts; i++ )
    {
        if ( Cudd_IsComplement(bFunc) )
        {
            bFunc0 = Cudd_Not(Cudd_E(bFunc));
            bFunc1 = Cudd_Not(Cudd_T(bFunc));
        }
        else
        {
            bFunc0 = Cudd_E(bFunc);
            bFunc1 = Cudd_T(bFunc);
        }
        assert( bFunc0 == bConst0 || bFunc1 == bConst0 );
        if ( bFunc0 == bConst0 )
        {
            TermMask ^= (1 << i);
            bFunc = bFunc1;
        }
        else
            bFunc = bFunc0;
    }
    assert( bFunc == bConst1 );
    return Cudd_addConst( dd, TermMask );
}

/**Function*************************************************************

  Synopsis    [Recursively construct ADD for BDD.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdNode * Abc_NtkBddToAdd_rec( DdManager * dd, DdNode * bFunc, int nOuts, stmm_table * tTable, int fCompl )
{
    DdNode * aFunc0, * aFunc1, * aFunc;
    DdNode ** ppSlot;
    assert( !Cudd_IsComplement(bFunc) );
    if ( stmm_find_or_add( tTable, (char *)bFunc, (char ***)&ppSlot ) )
        return *ppSlot;
    if ( (int)bFunc->index >= Cudd_ReadSize(dd) - nOuts )
    {
        assert( Cudd_ReadPerm(dd, bFunc->index) >= Cudd_ReadSize(dd) - nOuts );
        aFunc = Abc_NtkBddFindAddConst( dd, Cudd_NotCond(bFunc, fCompl), nOuts ); Cudd_Ref( aFunc );
    }
    else
    {
        aFunc0 = Abc_NtkBddToAdd_rec( dd, Cudd_Regular(cuddE(bFunc)), nOuts, tTable, fCompl ^ Cudd_IsComplement(cuddE(bFunc)) );
        aFunc1 = Abc_NtkBddToAdd_rec( dd, cuddT(bFunc), nOuts, tTable, fCompl );                                                
        aFunc  = Cudd_addIte( dd, Cudd_addIthVar(dd, bFunc->index), aFunc1, aFunc0 );  Cudd_Ref( aFunc );
    }
    return (*ppSlot = aFunc);
}

/**Function*************************************************************

  Synopsis    [R]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdNode * Abc_NtkBddToAdd( DdManager * dd, DdNode * bFunc, int nOuts )
{
    DdNode * aFunc, * aTemp, * bTemp;
    stmm_table * tTable;
    stmm_generator * gen;
    tTable = stmm_init_table( st_ptrcmp, st_ptrhash );
    aFunc = Abc_NtkBddToAdd_rec( dd, Cudd_Regular(bFunc), nOuts, tTable, Cudd_IsComplement(bFunc) );  
    stmm_foreach_item( tTable, gen, (char **)&bTemp, (char **)&aTemp )
        Cudd_RecursiveDeref( dd, aTemp );
    stmm_free_table( tTable );
    Cudd_Deref( aFunc );
    return aFunc;
}

/**Function*************************************************************

  Synopsis    [Computes the characteristic function.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdNode * Abc_NtkBddDecCharFunc( DdManager * dd, DdNode ** pFuncs, int nOuts, int Mask, int nBits )
{
    DdNode * bFunc, * bTemp, * bExor, * bVar;
    int i, Count = 0;
    bFunc = Cudd_ReadOne( dd );  Cudd_Ref( bFunc );
    for ( i = 0; i < nOuts; i++ )
    {
        if ( (Mask & (1 << i)) == 0 )
            continue;
        Count++;
        bVar  = Cudd_bddIthVar( dd, dd->size - nOuts + i );
        bExor = Cudd_bddXor( dd, pFuncs[i], bVar );                  Cudd_Ref( bExor );
        bFunc = Cudd_bddAnd( dd, bTemp = bFunc, Cudd_Not(bExor) );   Cudd_Ref( bFunc );
        Cudd_RecursiveDeref( dd, bTemp );
        Cudd_RecursiveDeref( dd, bExor );
    }
    Cudd_Deref( bFunc );
    assert( Count == nBits );
    return bFunc;
}

/**Function*************************************************************

  Synopsis    [Evaluate Sasao's decomposition.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkBddDecTry( reo_man * pReo, DdManager * dd, DdNode ** pFuncs, int nOuts, int Mask, int nBits )
{
    DdNode * bFunc, * aFunc, * aFuncNew;
    // drive the characteristic function
    bFunc = Abc_NtkBddDecCharFunc( dd, pFuncs, nOuts, Mask, nBits );    Cudd_Ref( bFunc );
//Abc_NodeShowBddOne( dd, bFunc );
    // transfer to ADD
    aFunc = Abc_NtkBddToAdd( dd, bFunc, nOuts );                        Cudd_Ref( aFunc );
    Cudd_RecursiveDeref( dd, bFunc );
//Abc_NodeShowBddOne( dd, aFunc );
    // perform reordering for BDD width
    aFuncNew = Extra_Reorder( pReo, dd, aFunc, NULL );                  Cudd_Ref( aFuncNew );
printf( "Before = %d.  After = %d.\n", Cudd_DagSize(aFunc), Cudd_DagSize(aFuncNew) );
//Abc_NodeShowBddOne( dd, aFuncNew );
    Cudd_RecursiveDeref( dd, aFuncNew );
    Cudd_RecursiveDeref( dd, aFunc );
    // print the result
//    reoProfileWidthPrint( pReo );
}

/**Function*************************************************************

  Synopsis    [Evaluate Sasao's decomposition.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkBddDecInt( reo_man * pReo, DdManager * dd, DdNode ** pFuncs, int nOuts )
{
/*
    int i, k;
    for ( i = 1; i <= nOuts; i++ )
    {
        for ( k = 0; k < (1<<nOuts); k++ )
            if ( Extra_WordCountOnes(k) == i )
            {
                Extra_PrintBinary( stdout, (unsigned *)&k, nOuts );
                Abc_NtkBddDecTry( pReo, dd, pFuncs, nOuts, k, i );
                printf( "\n" );
            }
    }
*/
    Abc_NtkBddDecTry( pReo, dd, pFuncs, nOuts, ~(1<<(32-nOuts)), nOuts );

}

/**Function*************************************************************

  Synopsis    [Evaluate Sasao's decomposition.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkBddDec( Abc_Ntk_t * pNtk, int fVerbose )
{
    int nBddSizeMax   = 1000000;
    int fDropInternal =       0;
    int fReorder      =       1;
    reo_man * pReo;
    DdManager * dd;
    DdNode * pFuncs[BDD_FUNC_MAX];
    Abc_Obj_t * pNode;
    int i;
    assert( Abc_NtkIsStrash(pNtk) );
    assert( Abc_NtkCoNum(pNtk) <= BDD_FUNC_MAX );
    dd = (DdManager *)Abc_NtkBuildGlobalBdds( pNtk, nBddSizeMax, fDropInternal, fReorder, fVerbose );
    if ( dd == NULL )
    {
        Abc_Print( -1, "Construction of global BDDs has failed.\n" );
        return;
    }

    assert( dd->size == Abc_NtkCiNum(pNtk) );
    // create new variables at the bottom
    for ( i = 0; i < Abc_NtkCoNum(pNtk); i++ )
        Cudd_addNewVarAtLevel( dd, dd->size );
    // create terminals of MTBDD
//    for ( i = 0; i < (1 << Abc_NtkCoNum(pNtk)); i++ )
//        Cudd_addConst( dd, i );
    // collect global BDDs
    Abc_NtkForEachCo( pNtk, pNode, i )
        pFuncs[i] = (DdNode *)Abc_ObjGlobalBdd(pNode);

    pReo = Extra_ReorderInit( Abc_NtkCiNum(pNtk), 1000 );
    Extra_ReorderSetMinimizationType( pReo, REO_MINIMIZE_WIDTH );
//    Extra_ReorderSetVerification( pReo, 1 );
    Extra_ReorderSetVerbosity( pReo, 1 );

    Abc_NtkBddDecInt( pReo, dd, pFuncs, Abc_NtkCoNum(pNtk) );
    Extra_ReorderQuit( pReo );

    Abc_NtkFreeGlobalBdds( pNtk, 1 );
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


