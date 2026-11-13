/**CFile****************************************************************

  FileName    [imcRwr.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Interpolation-based model checking.]

  Synopsis    [Bounded BDD and SAT simplification of interpolants.]

  Author      [ABC contributors]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 23, 2026.]

  Revision    [$Id: imcRwr.c,v 1.00 2026/10/23 00:00:00 alanmi Exp $]

***********************************************************************/

#include "imcInt.h"
#include "proof/dch/dch.h"
#ifdef ABC_USE_CUDD
#include "bdd/extrab/extraBdd.h"
#include "misc/st/st.h"
#endif

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

#ifdef ABC_USE_CUDD

/**Function*************************************************************

  Synopsis    [Converts a BDD to a hashed GIA using memoized node literals.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_BddToGia_rec( Gia_Man_t * p, DdNode * bFunc, st__table * tNodes, Vec_Int_t * vVars )
{
    DdNode * bNode = Cudd_Regular(bFunc);
    char * pEntry;
    int Lit;
    if ( st__lookup(tNodes, (char *)bNode, &pEntry) )
        return Abc_Ptr2Int(pEntry) ^ Cudd_IsComplement(bFunc);
    Lit = Gia_ManHashMux( p, Gia_Obj2Lit(p, Gia_ManCi(p, Vec_IntEntry(vVars, Cudd_NodeReadIndex(bNode)))),
        Imc_BddToGia_rec(p, Cudd_T(bNode), tNodes, vVars),
        Imc_BddToGia_rec(p, Cudd_E(bNode), tNodes, vVars) );
    st__insert( tNodes, (char *)bNode, (char *)Abc_Int2Ptr(Lit) );
    return Lit ^ Cudd_IsComplement(bFunc);
}

/**Function*************************************************************

  Synopsis    [Releases a BDD value after its last AIG reference is consumed.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Imc_BddDeref( Gia_Man_t * p, DdManager * dd, Vec_Ptr_t * vNodes, int Id )
{
    if ( Gia_ObjRefDecId(p, Id) )
        return;
    Cudd_RecursiveDeref( dd, (DdNode *)Vec_PtrEntry(vNodes, Id) );
    Vec_PtrWriteEntry( vNodes, Id, NULL );
}

#endif

/**Function*************************************************************

  Synopsis    [Returns an equivalent smaller AIG, or NULL.]

  Description [Limits both BDD growth and the time spent on a frontier.
  Failure leaves the original interpolant available for AIG rewriting.]

  SideEffects [Uses the AIG reference counts.]

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Imc_ManRewriteBdd( Gia_Man_t * p, int nLimit, abctime TimeStop )
{
#ifdef ABC_USE_CUDD
    DdManager * dd;
    DdNode * bFunc, * bFunc0, * bFunc1;
    Gia_Man_t * pNew = NULL, * pResult = NULL;
    Gia_Obj_t * pObj;
    Vec_Ptr_t * vNodes;
    Vec_Int_t * vVars;
    st__table * tNodes;
    abctime TimeBdd = TimeStop;
    int i, k, Headroom, * pRefsSave;
    if ( nLimit <= 4 || Gia_ManAndNum(p) < 100 )
        return NULL;
    pRefsSave = p->pRefs;
    p->pRefs = NULL;
    Gia_ManCreateRefs( p );
    vVars = Vec_IntAlloc( 64 );
    Gia_ManForEachCi( p, pObj, i )
        if ( Gia_ObjRefNum(p, pObj) )
            Vec_IntPush( vVars, i );
    // Interpolants retain the full register interface, although a frontier
    // often depends on only a few registers. Bound the actual support.
    if ( nLimit <= Vec_IntSize(vVars) + 4 || Vec_IntSize(vVars) > 512 )
        goto free_refs;
    dd = Cudd_Init( Vec_IntSize(vVars), 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );
    Cudd_SetMaxLive( dd, nLimit );
    Cudd_SetSiftMaxSwap( dd, 10000 );
    // This bundled CUDD predates Cudd_SetTimeLimit. Its recursive AND
    // checks TimeStop. Reordering has no equivalent bound in this version.
    dd->TimeStop = TimeBdd;
    Cudd_AutodynDisable( dd );
    vNodes = Vec_PtrStart( Gia_ManObjNum(p) );
    Vec_PtrWriteEntry( vNodes, 0, Cudd_ReadLogicZero(dd) );
    Cudd_Ref( Cudd_ReadLogicZero(dd) );
    Vec_IntForEachEntry( vVars, i, k )
    {
        pObj = Gia_ManCi(p, i);
        bFunc = Cudd_bddIthVar( dd, k );
        Cudd_Ref( bFunc );
        Vec_PtrWriteEntry( vNodes, Gia_ObjId(p, pObj), bFunc );
    }
    Gia_ManForEachAnd( p, pObj, i )
    {
        if ( Imc_ManCheckStop(TimeBdd) )
            goto finish;
        bFunc0 = Cudd_NotCond( (DdNode *)Vec_PtrEntry(vNodes, Gia_ObjFaninId0(pObj, i)), Gia_ObjFaninC0(pObj) );
        bFunc1 = Cudd_NotCond( (DdNode *)Vec_PtrEntry(vNodes, Gia_ObjFaninId1(pObj, i)), Gia_ObjFaninC1(pObj) );
        Headroom = nLimit - (int)(dd->keys - dd->dead + dd->keysZ - dd->deadZ);
        if ( Headroom < 0 )
            goto finish;
        bFunc = Cudd_bddAndLimit( dd, bFunc0, bFunc1, Headroom );
        if ( bFunc == NULL )
            goto finish;
        Cudd_Ref( bFunc );
        Vec_PtrWriteEntry( vNodes, i, bFunc );
        // Bundled CUDD checks maxLive when refilling its allocation block.
        // Also enforce the aggregate cap before releasing either operand;
        // otherwise a short-lived peak can disappear between AND calls.
        if ( (word)(dd->keys - dd->dead + dd->keysZ - dd->deadZ) > (word)nLimit )
            goto finish;
        Imc_BddDeref( p, dd, vNodes, Gia_ObjFaninId0(pObj, i) );
        Imc_BddDeref( p, dd, vNodes, Gia_ObjFaninId1(pObj, i) );
    }
    Cudd_AutodynDisable( dd );
    pObj = Gia_ManCo( p, 0 );
    bFunc = Cudd_NotCond( (DdNode *)Vec_PtrEntry(vNodes, Gia_ObjFaninId0p(p, pObj)), Gia_ObjFaninC0(pObj) );
    if ( Cudd_DagSize(bFunc) >= Gia_ManAndNum(p) )
        goto finish;
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    Gia_ManHashStart( pNew );
    Gia_ManForEachCi( p, pObj, i )
        Gia_ManAppendCi( pNew );
    tNodes = st__init_table( st__ptrcmp, st__ptrhash );
    st__insert( tNodes, (char *)Cudd_ReadOne(dd), (char *)Abc_Int2Ptr(1) );
    Gia_ManAppendCo( pNew, Imc_BddToGia_rec(pNew, bFunc, tNodes, vVars) );
    st__free_table( tNodes );
    Gia_ManHashStop( pNew );
    pResult = Gia_ManCleanup( pNew );
    if ( Gia_ManAndNum(pResult) >= Gia_ManAndNum(p) )
        Gia_ManStopP( &pResult );
finish:
    Gia_ManStopP( &pNew );
    Vec_PtrForEachEntry( DdNode *, vNodes, bFunc, i )
        if ( bFunc )
            Cudd_RecursiveDeref( dd, bFunc );
    Vec_PtrFree( vNodes );
    Cudd_Quit( dd );
free_refs:
    Vec_IntFree( vVars );
    ABC_FREE( p->pRefs );
    p->pRefs = pRefsSave;
    return pResult;
#else
    return NULL;
#endif
}

/**Function*************************************************************

  Synopsis    [Returns a smaller equivalent AIG using bounded SAT sweeping.]

  Description [Only proven equivalences are used, including when the
  sweeping deadline expires partway through the graph.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Imc_ManRewriteSat( Gia_Man_t * p, abctime TimeStop )
{
    Dch_Pars_t Pars;
    Aig_Man_t * pAig = Gia_ManToAigSimple( p ), * pTemp;
    Gia_Man_t * pResult;
    Dch_ManSetDefaultParams( &Pars );
    Pars.nBTLimit = 100;
    Pars.nWords = 4;
    // Deterministic conflict and simulation limits select the work. Only
    // the caller's overall deadline may interrupt an otherwise equal run.
    pAig->Time2Quit = TimeStop;
    Dch_ComputeEquivalences( pAig, &Pars );
    pTemp = Aig_ManDupRepr( pAig, 0 );
    pResult = Gia_ManFromAigSimple( pTemp );
    Aig_ManStop( pTemp );
    Aig_ManStop( pAig );
    if ( Gia_ManAndNum(pResult) >= Gia_ManAndNum(p) )
        Gia_ManStopP( &pResult );
    return pResult;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
