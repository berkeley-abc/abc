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
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"
#include "misc/util/utilTruth.h"
//#include "bdd/cudd/cuddInt.h"

//#ifdef ABC_USE_PTHREADS

#ifdef _WIN32
#include "../lib/pthread.h"
#else
#include <pthread.h>
#include <unistd.h>
#endif

//#endif

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
int Gia_SplitCofVar2( Gia_Man_t * p, int LookAhead )
{
    Gia_Man_t * pPart;
    int * pOrder = Gia_PermuteSpecialOrder( p );
    int Cost0, Cost1, CostBest = ABC_INFINITY;
    int i, iBest = -1;
    LookAhead = Abc_MinInt( LookAhead, Gia_ManPiNum(p) );
    for ( i = 0; i < LookAhead; i++ )
    {
        pPart = Gia_ManDupCofactor( p, pOrder[i], 0 );
        Cost0 = Gia_ManAndNum(pPart);
        Gia_ManStop( pPart );

        pPart = Gia_ManDupCofactor( p, pOrder[i], 1 );
        Cost1 = Gia_ManAndNum(pPart);
        Gia_ManStop( pPart );

/*
        pPart = Gia_ManDupExist( p, pOrder[i] );
        printf( "%2d : Var = %4d  Refs = %3d  %6d %6d -> %6d    %6d -> %6d\n", 
            i, pOrder[i], Gia_ObjRefNum(p, Gia_ManPi(p, pOrder[i])), 
            Cost0, Cost1, Cost0+Cost1, Gia_ManAndNum(p), Gia_ManAndNum(pPart) );
        Gia_ManStop( pPart );
*/

//        printf( "%2d : Var = %4d  Refs = %3d  %6d %6d -> %6d\n", 
//            i, pOrder[i], Gia_ObjRefNum(p, Gia_ManPi(p, pOrder[i])), 
//            Cost0, Cost1, Cost0+Cost1 );

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
static inline sat_solver * Cec_GiaDeriveSolver( Gia_Man_t * p, Cnf_Dat_t * pCnf, int nTimeOut )
{
    sat_solver * pSat;
    int i, fDerive = (pCnf == NULL);
    if ( pCnf == NULL )
        pCnf = Cec_GiaDeriveGiaRemapped( p );
    pSat = sat_solver_new();
    sat_solver_setnvars( pSat, pCnf->nVars );
    for ( i = 0; i < pCnf->nClauses; i++ )
        if ( !sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ) )
        {
            // the problem is UNSAT
            sat_solver_delete( pSat );
            Cnf_DataFree( pCnf );
            return NULL;
        }
    sat_solver_set_runtime_limit( pSat, nTimeOut ? nTimeOut * CLOCKS_PER_SEC + Abc_Clock(): 0 );
    if ( fDerive )
        Cnf_DataFree( pCnf );
    return pSat;
}
static inline int Cnf_GiaSolveOne( Gia_Man_t * p, Cnf_Dat_t * pCnf, int nTimeOut, int * pnVars, int * pnConfs )
{
    int status;
    sat_solver * pSat = Cec_GiaDeriveSolver( p, pCnf, nTimeOut );
    if ( pSat == NULL )
    {
        *pnVars = 0;
        *pnConfs = 0;
        return 1;
    }
    status   = sat_solver_solve( pSat, NULL, NULL, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
    *pnVars  = sat_solver_nvars( pSat );
    *pnConfs = sat_solver_nconflicts( pSat );
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
static inline int Cnf_GiaCheckOne( Vec_Ptr_t * vStack, Gia_Man_t * p, Cnf_Dat_t * pCnf, int nTimeOut, int * pnVars, int * pnConfs )
{
    int status = Cnf_GiaSolveOne( p, pCnf, nTimeOut, pnVars, pnConfs );
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
void Cec_GiaSplitPrint( int nIter, int Depth, int nVars, int nConfs, int fStatus, double Prog, abctime clk )
{
    printf( "%6d : ",            nIter );
    printf( "Depth =%3d  ",      Depth );
    printf( "SatVar =%7d  ",     nVars );
    printf( "SatConf =%7d   ",   nConfs );
    printf( "%s   ",             fStatus ? (fStatus == 1 ? "UNSAT    " : "UNDECIDED") : "SAT      " );
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
int Cec_GiaSplitTest2( Gia_Man_t * p, int nProcs, int nTimeOut, int nIterMax, int LookAhead, int fVerbose )
{
    abctime clkTotal = Abc_Clock();
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
    if ( !Cnf_GiaCheckOne(vStack, p, NULL, nTimeOut, &nSatVars, &nSatConfs) )
        RetValue = 0;
    else
    {
        if ( fVerbose )
            Cec_GiaSplitPrint( 0, 0, nSatVars, nSatConfs, -1, Progress, Abc_Clock() - clkTotal );
        for ( nIter = 1; Vec_PtrSize(vStack) > 0; nIter++ )
        {
            // get the last AIG
            pLast = (Gia_Man_t *)Vec_PtrPop( vStack );
            // determine cofactoring variable
            Depth = Vec_IntSize(pLast->vCofVars);
            iVar = Gia_SplitCofVar2( pLast, LookAhead );
            // cofactor
            pPart0 = Gia_ManDupCofactor( pLast, iVar, 0 );
            // create variable
            pPart0->vCofVars = Vec_IntAlloc( Vec_IntSize(pLast->vCofVars) + 1 );
            Vec_IntAppend( pPart0->vCofVars, pLast->vCofVars );
            Vec_IntPush( pPart0->vCofVars, Abc_Var2Lit(iVar, 1) );
            // check this AIG
            fSatUnsat = Vec_PtrSize(vStack);
            if ( !Cnf_GiaCheckOne(vStack, pPart0, NULL, nTimeOut, &nSatVars, &nSatConfs) )
            {
                Gia_ManStop( pLast );
                RetValue = 0;
                break;
            }
            fSatUnsat = (fSatUnsat == Vec_PtrSize(vStack));
            if ( fSatUnsat )
                Progress += 1.0 / pow(2, Depth + 1);
            if ( fVerbose ) 
                Cec_GiaSplitPrint( nIter, Depth, nSatVars, nSatConfs, fSatUnsat?1:-1, Progress, Abc_Clock() - clkTotal );
            // cofactor
            pPart1 = Gia_ManDupCofactor( pLast, iVar, 1 );
            // create variable
            pPart1->vCofVars = Vec_IntAlloc( Vec_IntSize(pLast->vCofVars) + 1 );
            Vec_IntAppend( pPart1->vCofVars, pLast->vCofVars );
            Vec_IntPush( pPart1->vCofVars, Abc_Var2Lit(iVar, 0) );
            Gia_ManStop( pLast );
            // check this AIG
            fSatUnsat = Vec_PtrSize(vStack);
            if ( !Cnf_GiaCheckOne(vStack, pPart1, NULL, nTimeOut, &nSatVars, &nSatConfs) )
            {
                RetValue = 0;
                break;
            }
            fSatUnsat = (fSatUnsat == Vec_PtrSize(vStack));
            if ( fSatUnsat )
                Progress += 1.0 / pow(2, Depth + 1);
            if ( fVerbose )
                Cec_GiaSplitPrint( nIter, Depth, nSatVars, nSatConfs, fSatUnsat?1:-1, Progress, Abc_Clock() - clkTotal );
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

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
#define PAR_THR_MAX 100
typedef struct Par_ThData_t_
{
    Gia_Man_t * p;
    Cnf_Dat_t * pCnf;
    int         iThread;
    int         nTimeOut;
    int         fWorking;
    int         Result;
    int         nVars;
    int         nConfs;
} Par_ThData_t;
void * Cec_GiaSplitWorkerThread( void * pArg )
{
    Par_ThData_t * pThData = (Par_ThData_t *)pArg;
    volatile int * pPlace = &pThData->fWorking;
    while ( 1 )
    {
        while ( *pPlace == 0 );
        assert( pThData->fWorking );
        if ( pThData->p == NULL )
        {
            pthread_exit( NULL );
            assert( 0 );
            return NULL;
        }
        pThData->Result = Cnf_GiaSolveOne( pThData->p, pThData->pCnf, pThData->nTimeOut, &pThData->nVars, &pThData->nConfs );
        pThData->fWorking = 0;
    }
    assert( 0 );
    return NULL;
}
int Cec_GiaSplitTest( Gia_Man_t * p, int nProcs, int nTimeOut, int nIterMax, int LookAhead, int fVerbose )
{
    abctime clkTotal = Abc_Clock();
    Par_ThData_t ThData[PAR_THR_MAX];
    pthread_t WorkerThread[PAR_THR_MAX];
    Vec_Ptr_t * vStack;
    double Progress = 0;
    int i, status, nSatVars, nSatConfs;
    int nIter = 0, RetValue = -1, fWorkToDo = 1;
    if ( fVerbose )
        printf( "Solving CEC problem by cofactoring with the following parameters:\n" );
    if ( fVerbose )
        printf( "Processes = %d   TimeOut = %d sec   MaxIter = %d   LookAhead = %d   Verbose = %d.\n", nProcs, nTimeOut, nIterMax, LookAhead, fVerbose );
    if ( nProcs == 1 )
        return Cec_GiaSplitTest2( p, nProcs, nTimeOut, nIterMax, LookAhead, fVerbose );
    // subtract manager thread
    nProcs--;
    assert( nProcs >= 1 && nProcs <= PAR_THR_MAX );
    // check the problem
    status = Cnf_GiaSolveOne( p, NULL, nTimeOut, &nSatVars, &nSatConfs );
    if ( fVerbose )
        Cec_GiaSplitPrint( 0, 0, nSatVars, nSatConfs, status, Progress, Abc_Clock() - clkTotal );
    if ( status == 0 )
    {
        printf( "The problem is SAT without cofactoring.\n" );
        return 0;
    }
    if ( status == 1 )
    {
        printf( "The problem is UNSAT without cofactoring.\n" );
        return 1;
    }
    assert( status == -1 );
    // create local copy
    p = Gia_ManDup( p );
    vStack = Vec_PtrAlloc( 1000 );
    Vec_PtrPush( vStack, p );
    // start cofactored variables
    assert( p->vCofVars == NULL );
    p->vCofVars = Vec_IntAlloc( 100 );
    // start threads
    for ( i = 0; i < nProcs; i++ )
    {
        ThData[i].p        = NULL;
        ThData[i].pCnf     = NULL;
        ThData[i].iThread  = i;
        ThData[i].nTimeOut = nTimeOut;
        ThData[i].fWorking = 0;
        ThData[i].Result   = -1;
        ThData[i].nVars    = -1;
        ThData[i].nConfs   = -1;
        status = pthread_create( WorkerThread + i, NULL,Cec_GiaSplitWorkerThread, (void *)(ThData + i) );  assert( status == 0 );
    }
    // look at the threads
    while ( fWorkToDo )
    {
        fWorkToDo = (int)(Vec_PtrSize(vStack) > 0);
        for ( i = 0; i < nProcs; i++ )
        {
            // check if this thread is working
            if ( ThData[i].fWorking )
            {
                fWorkToDo = 1;
                continue;
            }
            // check if this thread has recently finished
            if ( ThData[i].p != NULL )
            {
                Gia_Man_t * pLast = ThData[i].p;
                int Depth = Vec_IntSize(pLast->vCofVars);
                if ( fVerbose )
                    Cec_GiaSplitPrint( i, Depth, ThData[i].nVars, ThData[i].nConfs, ThData[i].Result, Progress, Abc_Clock() - clkTotal );
                if ( ThData[i].Result == 0 ) // SAT
                {
                    RetValue = 0;
                    goto finish;
                }
                if ( ThData[i].Result == -1 ) // UNDEC
                {
                    // determine cofactoring variable
                    int iVar = Gia_SplitCofVar2( pLast, LookAhead );
                    // cofactor
                    Gia_Man_t * pPart = Gia_ManDupCofactor( pLast, iVar, 0 );
                    pPart->vCofVars = Vec_IntAlloc( Vec_IntSize(pLast->vCofVars) + 1 );
                    Vec_IntAppend( pPart->vCofVars, pLast->vCofVars );
                    Vec_IntPush( pPart->vCofVars, Abc_Var2Lit(iVar, 1) );
                    Vec_PtrPush( vStack, pPart );
                    // cofactor
                    pPart = Gia_ManDupCofactor( pLast, iVar, 1 );
                    pPart->vCofVars = Vec_IntAlloc( Vec_IntSize(pLast->vCofVars) + 1 );
                    Vec_IntAppend( pPart->vCofVars, pLast->vCofVars );
                    Vec_IntPush( pPart->vCofVars, Abc_Var2Lit(iVar, 1) );
                    Vec_PtrPush( vStack, pPart );
                    // keep working
                    fWorkToDo = 1;
                    nIter++;
                }
                else
                    Progress += 1.0 / pow(2, Depth);
                Gia_ManStopP( &ThData[i].p );
                if ( ThData[i].pCnf == NULL )
                    continue;
                Cnf_DataFree( ThData[i].pCnf );
                ThData[i].pCnf = NULL;
            }
            if ( Vec_PtrSize(vStack) == 0 )
                continue;
            // start a new thread
            assert( ThData[i].p == NULL );
            ThData[i].p = Vec_PtrPop( vStack );
            ThData[i].pCnf = Cec_GiaDeriveGiaRemapped( ThData[i].p );
            ThData[i].fWorking = 1;
        }
        if ( nIterMax && nIter >= nIterMax )
            break;
    }
    if ( !fWorkToDo )
        RetValue = 1;
finish:
    // wait till threads finish
    for ( i = 0; i < nProcs; i++ )
        if ( ThData[i].fWorking )
            i = 0;
    // stop threads
    for ( i = 0; i < nProcs; i++ )
    {
        assert( !ThData[i].fWorking );
        // cleanup
        Gia_ManStopP( &ThData[i].p );
        if ( ThData[i].pCnf == NULL )
            continue;
        Cnf_DataFree( ThData[i].pCnf );
        ThData[i].pCnf = NULL;
        // stop
        ThData[i].p = NULL;
        ThData[i].fWorking = 1;
    }
    // finish
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

