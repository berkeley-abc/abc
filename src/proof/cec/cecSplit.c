/**CFile****************************************************************

  FileName    [cecSplit.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [Cofactoring for combinational miters.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cecSplit.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig/gia/gia.h"
#include "bdd/cudd/cuddInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Permute primary inputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdManager * Gia_ManBuildBdd( Gia_Man_t * p, Vec_Ptr_t ** pvNodes, int nSkip )
{
    abctime clk = Abc_Clock();
    DdManager * dd;
    DdNode * bBdd, * bBdd0, * bBdd1;
    Vec_Ptr_t * vNodes;
    Gia_Obj_t * pObj;
    int i;
    vNodes = Vec_PtrStart( Gia_ManObjNum(p) );
    dd = Cudd_Init( Gia_ManPiNum(p), 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );
//    Cudd_AutodynEnable( dd,  CUDD_REORDER_SYMM_SIFT );
    bBdd = Cudd_ReadLogicZero(dd); Cudd_Ref( bBdd );
    Vec_PtrWriteEntry( vNodes, 0, bBdd );  
    Gia_ManForEachPi( p, pObj, i )
    {
        bBdd = i > nSkip ? Cudd_bddIthVar(dd, i) : Cudd_ReadLogicZero(dd); Cudd_Ref( bBdd );
        Vec_PtrWriteEntry( vNodes, Gia_ObjId(p, pObj), bBdd );
    }
    Gia_ManForEachAnd( p, pObj, i )
    {
        bBdd0 = Cudd_NotCond( (DdNode *)Vec_PtrEntry(vNodes, Gia_ObjFaninId0(pObj, i)), Gia_ObjFaninC0(pObj) );
        bBdd1 = Cudd_NotCond( (DdNode *)Vec_PtrEntry(vNodes, Gia_ObjFaninId1(pObj, i)), Gia_ObjFaninC1(pObj) );
        bBdd = Cudd_bddAnd( dd, bBdd0, bBdd1 ); Cudd_Ref( bBdd );
        Vec_PtrWriteEntry( vNodes, Gia_ObjId(p, pObj), bBdd );
        if ( i % 10 == 0 )
            printf( "%d ", i );
//        if ( i == 3000 )
//            break;
    }
    printf( "\n" );
    Gia_ManForEachPo( p, pObj, i )
    {
        bBdd = Cudd_NotCond( (DdNode *)Vec_PtrEntry(vNodes, Gia_ObjFaninId0(pObj, Gia_ObjId(p, pObj))), Gia_ObjFaninC0(pObj) );  Cudd_Ref( bBdd );
        Vec_PtrWriteEntry( vNodes, Gia_ObjId(p, pObj), bBdd );
    }
    if ( bBdd == Cudd_ReadLogicZero(dd) )
        printf( "Equivalent!\n" );
    else
        printf( "Not tquivalent!\n" );
    if ( pvNodes )
        *pvNodes = vNodes;
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    return dd;
}
void Gia_ManDerefBdd( DdManager * dd, Vec_Ptr_t * vNodes )
{
    DdNode * bBdd;
    int i;
    Vec_PtrForEachEntry( DdNode *, vNodes, bBdd, i )
        if ( bBdd )
            Cudd_RecursiveDeref( dd, bBdd );
    if ( Cudd_CheckZeroRef(dd) > 0 )
        printf( "The number of referenced nodes = %d\n", Cudd_CheckZeroRef(dd) );
    Cudd_PrintInfo( dd, stdout );
    Cudd_Quit( dd );
}
void Gia_ManBuildBddTest( Gia_Man_t * p )
{
    Vec_Ptr_t * vNodes;
    DdManager * dd = Gia_ManBuildBdd( p, &vNodes, 50 );
    Gia_ManDerefBdd( dd, vNodes );
}

/**Function*************************************************************

  Synopsis    [Permute primary inputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_PermuteSpecial( Gia_Man_t * p )
{
    Vec_Int_t * vPerm;
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i, * pOrder;
    Gia_ManCreateRefs( p );
    vPerm = Vec_IntAlloc( Gia_ManPiNum(p) );
    Gia_ManForEachPi( p, pObj, i )
        Vec_IntPush( vPerm, Gia_ObjRefNum(p, pObj) );
    pOrder = Abc_QuickSortCost( Vec_IntArray(vPerm), Vec_IntSize(vPerm), 1 );
    Vec_IntFree( vPerm );
    vPerm = Vec_IntAllocArray( pOrder, Gia_ManPiNum(p) );
    pNew = Gia_ManDupPerm( p, vPerm );
    Vec_IntFree( vPerm );
    return pNew;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_GiaSplitExplore( Gia_Man_t * p )
{
    Gia_Obj_t * pObj, * pFan0, * pFan1;
    int i, Counter = 0;
    assert( p->pMuxes == NULL );
    ABC_FREE( p->pRefs );
    Gia_ManCreateRefs( p ); 
    Gia_ManForEachAnd( p, pObj, i )
    {
        if ( !Gia_ObjRecognizeExor(pObj, &pFan0, &pFan1) )
            continue;
        if ( Gia_ObjRefNum(p, Gia_ObjFanin0(pObj)) > 1 && 
             Gia_ObjRefNum(p, Gia_ObjFanin1(pObj)) > 1 )
             continue;
        printf( "%5d : ", Counter++ );
        printf( "%2d %2d    ", Gia_ObjRefNum(p, Gia_Regular(pFan0)),  Gia_ObjRefNum(p, Gia_Regular(pFan1)) );
        printf( "%2d %2d  \n", Gia_ObjRefNum(p, Gia_ObjFanin0(pObj)), Gia_ObjRefNum(p, Gia_ObjFanin1(pObj)) );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Cec_GiaSplitTest( Gia_Man_t * p )
{
    Gia_Man_t * pNew;
//    Gia_Man_t * pMuxes;
    Gia_Man_t * pCof;
    Gia_Obj_t * pObj;
    int i;
    pNew = Gia_PermuteSpecial( p );
    Gia_ManCreateRefs( pNew );
    Gia_ManForEachPi( pNew, pObj, i )
        printf( "%d ", Gia_ObjRefNum(pNew, pObj) );
    printf( "\n" );
//    Cec_GiaSplitExplore( pNew );
//    Gia_ManBuildBddTest( p );
/*
    // derive muxes
    pMuxes = Gia_ManDupMuxes( pNew );
    printf( "GIA manager has %d ANDs, %d XORs, %d MUXes.\n", 
        Gia_ManAndNum(pMuxes) - Gia_ManXorNum(pMuxes) - Gia_ManMuxNum(pMuxes), Gia_ManXorNum(pMuxes), Gia_ManMuxNum(pMuxes) ); 
    Gia_ManStop( pMuxes );
*/
    pCof = Gia_ManDupDfsRehash( pNew, 20 );
    Gia_ManStop( pNew );
    return pCof;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

