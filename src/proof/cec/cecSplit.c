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

#include <math.h>
#include "aig/gia/gia.h"
#include "aig/gia/giaAig.h"
//#include "bdd/cudd/cuddInt.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"
#include "misc/util/utilTruth.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

#if 0 // BDD code

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

#endif // BDD code

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

  Synopsis    [Find cofactoring variable.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_SplitCofVar( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i, iBest = -1, CostBest = -1;
    if ( p->pRefs == NULL )
        Gia_ManCreateRefs( p );
    Gia_ManForEachPi( p, pObj, i )
        if ( CostBest < Gia_ObjRefNum(p, pObj) )
            iBest = i, CostBest = Gia_ObjRefNum(p, pObj);
    assert( iBest >= 0 );
    return iBest;
}
int * Gia_PermuteSpecialOrder( Gia_Man_t * p )
{
    Vec_Int_t * vPerm;
    Gia_Obj_t * pObj;
    int i, * pOrder;
    Gia_ManCreateRefs( p );
    vPerm = Vec_IntAlloc( Gia_ManPiNum(p) );
    Gia_ManForEachPi( p, pObj, i )
        Vec_IntPush( vPerm, Gia_ObjRefNum(p, pObj) );
    pOrder = Abc_QuickSortCost( Vec_IntArray(vPerm), Vec_IntSize(vPerm), 1 );
    Vec_IntFree( vPerm );
    return pOrder;
}
Gia_Man_t * Gia_PermuteSpecial( Gia_Man_t * p )
{
    Gia_Man_t * pNew;
    Vec_Int_t * vPerm;
    int * pOrder = Gia_PermuteSpecialOrder( p );
    vPerm = Vec_IntAllocArray( pOrder, Gia_ManPiNum(p) );
    pNew = Gia_ManDupPerm( p, vPerm );
    Vec_IntFree( vPerm );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Find cofactoring variable.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_SplitCofVar2( Gia_Man_t * p )
{
    Gia_Man_t * pPart;
    int * pOrder = Gia_PermuteSpecialOrder( p );
    int Cost0, Cost1, CostBest = ABC_INFINITY;
    int i, iBest = -1, LookAhead = 10;
    for ( i = 0; i < LookAhead; i++ )
    {
        pPart = Gia_ManDupCofactor( p, pOrder[i], 0 );
        Cost0 = Gia_ManAndNum(pPart);
        Gia_ManStop( pPart );

        pPart = Gia_ManDupCofactor( p, pOrder[i], 1 );
        Cost1 = Gia_ManAndNum(pPart);
        Gia_ManStop( pPart );

        if ( CostBest > Cost0 + Cost1 )
            CostBest = Cost0 + Cost1, iBest = pOrder[i];
    }
    ABC_FREE( pOrder );
    assert( iBest >= 0 );
    return iBest;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Cnf_Dat_t * Cec_GiaDeriveGiaRemapped( Gia_Man_t * p )
{
    Cnf_Dat_t * pCnf;
    Aig_Man_t * pAig = Gia_ManToAigSimple( p );
    pAig->nRegs = 0;
    pCnf = Cnf_Derive( pAig, 0 );//Aig_ManCoNum(pAig) );
    Aig_ManStop( pAig );
    return pCnf;
}
static inline sat_solver * Cec_GiaDeriveSolver( Gia_Man_t * p, int nTimeOut )
{
    sat_solver * pSat;
    Cnf_Dat_t * pCnf;
    int i;
    pCnf = Cec_GiaDeriveGiaRemapped( p );
    pSat = sat_solver_new();
    sat_solver_setnvars( pSat, pCnf->nVars );
    for ( i = 0; i < pCnf->nClauses; i++ )
        if ( !sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ) )
            assert( 0 );
    sat_solver_set_runtime_limit( pSat, nTimeOut ? nTimeOut * CLOCKS_PER_SEC + Abc_Clock(): 0 );
    Cnf_DataFree( pCnf );
    return pSat;
}
static inline int Cnf_GiaSolveOne( Gia_Man_t * p, int nTimeOut, int fVerbose, int * pnVars, int * pnConfs )
{
    sat_solver * pSat = Cec_GiaDeriveSolver( p, nTimeOut );
    int status = sat_solver_solve( pSat, NULL, NULL, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
    *pnVars    = sat_solver_nvars( pSat );
    *pnConfs   = sat_solver_nconflicts( pSat );
    sat_solver_delete( pSat );
    if ( status == l_Undef )
        return -1;
    if ( status == l_False )
        return 1;
    return 0;
/*
    // get pattern
    Vec_IntClear( vLits );
    for ( i = 0; i < nFuncVars; i++ )
        Vec_IntPush( vLits, Vec_IntEntry(vTests, Iter*nFuncVars + i) );
    Gia_ManFaultAddOne( pM, pCnf, pSat, vLits, nFuncVars );
    if ( pPars->fVerbose )
    {
        printf( "Iter%6d : ",       Iter );
        printf( "Var =%10d  ",      sat_solver_nvars(pSat) );
        printf( "Clause =%10d  ",   sat_solver_nclauses(pSat) );
        printf( "Conflict =%10d  ", sat_solver_nconflicts(pSat) );
        //Abc_PrintTime( 1, "Time", clkSat );
        ABC_PRTr( "Solver time", clkSat );
    }
*/
}
static inline int Cnf_GiaCheckOne( Vec_Ptr_t * vStack, Gia_Man_t * p, int nTimeOut, int fVerbose, int * pnVars, int * pnConfs )
{
    int status = Cnf_GiaSolveOne( p, nTimeOut, fVerbose, pnVars, pnConfs );
    if ( status == -1 )
    {
        Vec_PtrPush( vStack, p );
        return 1;
    }
    Gia_ManStop( p );
    if ( status == 1 )
        return 1;
    // satisfiable
    return 0;
}
static inline void Cec_GiaSplitClean( Vec_Ptr_t * vStack )
{
    Gia_Man_t * pNew;
    int i;
    Vec_PtrForEachEntry( Gia_Man_t *, vStack, pNew, i )
        Gia_ManStop( pNew );
    Vec_PtrFree( vStack );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_GiaSplitPrint( int nIter, int Depth, int nVars, int nConfs, int fSatUnsat, double Prog, abctime clk )
{
    printf( "%6d : ",            nIter );
    printf( "Depth =%3d  ",      Depth );
    printf( "SatVar =%7d  ",     nVars );
    printf( "SatConf =%7d   ",   nConfs );
    printf( "%s   ",             fSatUnsat ? "UNSAT    " : "UNDECIDED" );
    printf( "Progress = %.10f   ", Prog );
    Abc_PrintTime( 1, "Time", clk );
    //ABC_PRTr( "Time", Abc_Clock()-clk );
}
void Cec_GiaSplitPrintRefs( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i;
    if ( p->pRefs == NULL )
        Gia_ManCreateRefs( p ); 
    Gia_ManForEachPi( p, pObj, i )
        printf( "%d ", Gia_ObjRefNum(p, pObj) );
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_GiaSplitTest( Gia_Man_t * p, int nTimeOut, int nIterMax, int fVerbose )
{
    abctime clk, clkTotal = Abc_Clock();
    Gia_Man_t * pPart0, * pPart1, * pLast;
    Vec_Ptr_t * vStack;
    int nSatVars, nSatConfs, fSatUnsat;
    int nIter, iVar, Depth, RetValue = -1;
    double Progress = 0;
    // create local copy
    p = Gia_ManDup( p );
    // start cofactored variables
    assert( p->vCofVars == NULL );
    p->vCofVars = Vec_IntAlloc( 100 );
    // start with the current problem
    vStack = Vec_PtrAlloc( 1000 );
    clk = Abc_Clock();
    if ( !Cnf_GiaCheckOne(vStack, p, nTimeOut, fVerbose, &nSatVars, &nSatConfs) )
        RetValue = 0;
    else
    {
        if ( fVerbose )
            Cec_GiaSplitPrint( 0, 0, nSatVars, nSatConfs, 0, 0, Abc_Clock() - clk );
        for ( nIter = 1; Vec_PtrSize(vStack) > 0; nIter++ )
        {
            // get the last AIG
            pLast = (Gia_Man_t *)Vec_PtrPop( vStack );
            // determine cofactoring variable
            Depth = Vec_IntSize(pLast->vCofVars);
            iVar = Gia_SplitCofVar2( pLast );
            // cofactor
            pPart0 = Gia_ManDupCofactor( pLast, iVar, 0 );
            // create variable
            pPart0->vCofVars = Vec_IntAlloc( Vec_IntSize(pLast->vCofVars) + 1 );
            Vec_IntAppend( pPart0->vCofVars, pLast->vCofVars );
            Vec_IntPush( pPart0->vCofVars, Abc_Var2Lit(iVar, 1) );
            // check this AIG
            fSatUnsat = Vec_PtrSize(vStack);
            clk = Abc_Clock();
            if ( !Cnf_GiaCheckOne(vStack, pPart0, nTimeOut, fVerbose, &nSatVars, &nSatConfs) )
            {
                Gia_ManStop( pLast );
                RetValue = 0;
                break;
            }
            fSatUnsat = (fSatUnsat == Vec_PtrSize(vStack));
            if ( fSatUnsat )
                Progress += 1.0 / pow(2, Depth + 1);
            if ( fVerbose ) 
                Cec_GiaSplitPrint( nIter, Depth, nSatVars, nSatConfs, fSatUnsat, Progress, Abc_Clock() - clk );
            // cofactor
            pPart1 = Gia_ManDupCofactor( pLast, iVar, 1 );
            // create variable
            pPart1->vCofVars = Vec_IntAlloc( Vec_IntSize(pLast->vCofVars) + 1 );
            Vec_IntAppend( pPart1->vCofVars, pLast->vCofVars );
            Vec_IntPush( pPart1->vCofVars, Abc_Var2Lit(iVar, 0) );
            Gia_ManStop( pLast );
            // check this AIG
            fSatUnsat = Vec_PtrSize(vStack);
            clk = Abc_Clock();
            if ( !Cnf_GiaCheckOne(vStack, pPart1, nTimeOut, fVerbose, &nSatVars, &nSatConfs) )
            {
                RetValue = 0;
                break;
            }
            fSatUnsat = (fSatUnsat == Vec_PtrSize(vStack));
            if ( fSatUnsat )
                Progress += 1.0 / pow(2, Depth + 1);
            if ( fVerbose )
                Cec_GiaSplitPrint( nIter, Depth, nSatVars, nSatConfs, fSatUnsat, Progress, Abc_Clock() - clk );
            if ( nIterMax && Vec_PtrSize(vStack) >= nIterMax )
                break;
        }
        if ( Vec_PtrSize(vStack) == 0 )
            RetValue = 1;
    }
    Cec_GiaSplitClean( vStack );
    if ( RetValue == 0 )
        printf( "Problem is SAT " );
    else if ( RetValue == 1 )
        printf( "Problem is UNSAT " );
    else if ( RetValue == -1 )
        printf( "Problem is UNDECIDED " );
    else assert( 0 );
    printf( "after %d case-splits.  ", nIter );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clkTotal );
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

