/**CFile****************************************************************

  FileName    [giaSatMap.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaSatMap.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "sat/bsat/satStore.h"
#include "misc/vec/vecWec.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////


// operation manager
typedef struct Sbm_Man_t_ Sbm_Man_t;
struct Sbm_Man_t_
{
    sat_solver *     pSat;      // SAT solver
    Vec_Int_t *      vCardVars; // candinality variables
    int              LogN;      // max vars
    int              FirstVar;  // first variable to be used
    int              LitShift;  // shift in terms of literals (2*Gia_ManCiNum(pGia)+2)
    // window
    Vec_Int_t *      vRoots;    // output drivers to be mapped (root -> lit)
    Vec_Wec_t *      vCuts;     // cuts (cut -> node lit + fanin lits)
    Vec_Wec_t *      vObjCuts;  // cuts (obj -> node lit + cut lits)
    Vec_Int_t *      vSolCuts;  // current solution (index -> cut)
    Vec_Int_t *      vCutGates; // gates (cut -> gate)
    // solver
    Vec_Int_t *      vAssump;   // assumptions (root nodes)
    Vec_Int_t *      vPolar;    // polarity of nodes and cuts
    // timing
    Vec_Int_t *      vArrs;     // arrivals for the inputs (input -> time)
    Vec_Int_t *      vReqs;     // required for the outputs (root -> time)
    // internal
    Vec_Int_t *      vLit2Used; // current solution (lit -> used)
    Vec_Int_t *      vDelays;   // node arrivals (lit -> time)
    Vec_Int_t *      vReason;   // timing reasons (lit -> cut)
};

/*
    Cuts in p->vCuts have 0-based numbers and are expressed in terms of object literals.
    Cuts in p->vObjCuts are expressed in terms of the obj-lit + cut-lits (i + p->FirstVar)
    Unit cuts for each polarity are ordered in the end.
*/

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Verify solution. Create polarity and assumptions.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sbm_ManCheckSol( Sbm_Man_t * p, Vec_Int_t * vSol )
{
    int K = Vec_IntSize(vSol) - 1;
    int i, j, Lit, Cut;
    int RetValue = 1;
    Vec_Int_t * vCut;
    // clear polarity and assumptions
    Vec_IntClear( p->vPolar );
    Vec_IntClear( p->vAssump );
    Vec_IntPush( p->vAssump, Abc_Var2Lit(Vec_IntEntry(p->vCardVars, K), 1) );
    // mark used literals
    Vec_IntFill( p->vLit2Used, Vec_WecSize(p->vObjCuts), 0 );
    Vec_IntForEachEntry( p->vSolCuts, Cut, i )
    {
        vCut = Vec_WecEntry( p->vCuts, Cut );
        Lit = Vec_IntEntry( vCut, 0 ) - p->LitShift; // obj literal
        if ( Vec_IntEntry(p->vLit2Used, Lit) )
            continue;
        Vec_IntWriteEntry( p->vLit2Used, Lit, 1 );
        Vec_IntPush( p->vPolar, Lit ); // literal variable
    }
    // check that the output literals are used
    Vec_IntForEachEntry( p->vRoots, Lit, i )
    {
        if ( Vec_IntEntry(p->vLit2Used, Lit) == 0 )
            printf( "Output literal %d has no cut.\n", Lit ), RetValue = 0;
        // create assumption
        Vec_IntPush( p->vAssump, Abc_Var2Lit(Lit, 0) );
    }
    // check internal nodes
    Vec_IntForEachEntry( p->vSolCuts, Cut, i )
    {
        vCut = Vec_WecEntry( p->vCuts, Cut );
        Vec_IntForEachEntryStart( vCut, Lit, j, 1 )
            if ( Vec_IntEntry(p->vLit2Used, Lit - p->LitShift) == 0 )
                printf( "Internal literal %d of cut %d is not mapped.\n", Lit - p->LitShift, Cut ), RetValue = 0;
        // create polarity
        Vec_IntPush( p->vPolar, p->FirstVar + Cut ); // cut variable
    }
    return RetValue;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sbm_ManCreateCnf( Sbm_Man_t * p )
{
    int i, k, Lit, Lits[2], value;
    Vec_Int_t * vLits;
    // sat_solver_rollback( p->Sat );
    if ( !Sbm_ManCheckSol(p, p->vSolCuts) )
        return 0;
    // increase var count
    assert( p->FirstVar == sat_solver_nvars(p->pSat) );
    sat_solver_setnvars( p->pSat, sat_solver_nvars(p->pSat) + Vec_WecSize(p->vCuts) );
    // iterate over arrays containing obj-lit cuts (neg-obj-lit cut-lits followed by pos-obj-lit cut-lits)
    Vec_WecForEachLevel( p->vObjCuts, vLits, i )
    {
        assert( Vec_IntSize(vLits) >= 2 );
        value = sat_solver_addclause( p->pSat, Vec_IntArray(vLits), Vec_IntLimit(vLits)  );
        assert( value );
        // for each cut, add implied nodes
        Lits[0] = Abc_LitNot( Vec_IntEntry(vLits, 0) );
        assert( Lits[0] < 2*p->FirstVar );
        Vec_IntForEachEntryStart( vLits, Lit, k, 1 )
        {
            assert( Lit >= 2*p->FirstVar );
            Lits[1] = Abc_LitNot( Lit );
            value = sat_solver_addclause( p->pSat, Lits, Lits + 2 );
            assert( value );
            //printf( "Adding clause %d + %d.\n", Lits[0], Lits[1]-2*p->FirstVar );
        }
        //printf( "\n" );
        // create invertor exclusivity clause
        if ( i & 1 )
        {
            Lits[0] = Abc_LitNot( Vec_IntEntry(vLits, Vec_IntSize(vLits)-1) );
            Lits[1] = Abc_LitNot( Vec_IntEntry(vLits, Vec_IntSize(vLits)-2) );
            value = sat_solver_addclause( p->pSat, Lits, Lits + 2 );
            assert( value );
            //printf( "Adding exclusivity clause %d + %d.\n", Lits[0]-2*p->FirstVar, Lits[1]-2*p->FirstVar );
        }
    }
    sat_solver_set_polarity( p->pSat, Vec_IntArray(p->vPolar), Vec_IntSize(p->vPolar) );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int sat_solver_add_and1( sat_solver * pSat, int iVar, int iVar0, int iVar1, int fCompl0, int fCompl1, int fCompl )
{
    lit Lits[3];
    int Cid;

    Lits[0] = toLitCond( iVar, !fCompl );
    Lits[1] = toLitCond( iVar0, fCompl0 );
    Cid = sat_solver_addclause( pSat, Lits, Lits + 2 );
    assert( Cid );

    Lits[0] = toLitCond( iVar, !fCompl );
    Lits[1] = toLitCond( iVar1, fCompl1 );
    Cid = sat_solver_addclause( pSat, Lits, Lits + 2 );
    assert( Cid );
/*
    Lits[0] = toLitCond( iVar, fCompl );
    Lits[1] = toLitCond( iVar0, !fCompl0 );
    Lits[2] = toLitCond( iVar1, !fCompl1 );
    Cid = sat_solver_addclause( pSat, Lits, Lits + 3 );
    assert( Cid );
*/
    return 3;
}

static inline int sat_solver_add_and2( sat_solver * pSat, int iVar, int iVar0, int iVar1, int fCompl0, int fCompl1, int fCompl )
{
    lit Lits[3];
    int Cid;
/*
    Lits[0] = toLitCond( iVar, !fCompl );
    Lits[1] = toLitCond( iVar0, fCompl0 );
    Cid = sat_solver_addclause( pSat, Lits, Lits + 2 );
    assert( Cid );

    Lits[0] = toLitCond( iVar, !fCompl );
    Lits[1] = toLitCond( iVar1, fCompl1 );
    Cid = sat_solver_addclause( pSat, Lits, Lits + 2 );
    assert( Cid );
*/
    Lits[0] = toLitCond( iVar, fCompl );
    Lits[1] = toLitCond( iVar0, !fCompl0 );
    Lits[2] = toLitCond( iVar1, !fCompl1 );
    Cid = sat_solver_addclause( pSat, Lits, Lits + 3 );
    assert( Cid );
    return 3;
}

/**Function*************************************************************

  Synopsis    [Adds a general cardinality constraint in terms of vVars.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Sbm_AddSorter( sat_solver * p, int * pVars, int i, int k, int * pnVars )
{
    int iVar1 = (*pnVars)++;
    int iVar2 = (*pnVars)++;
    int fVerbose = 0;
    if ( fVerbose )
    {
        int v;
        for ( v = 0; v < i; v++ )
            printf( " " );
        printf( "<" );
        for ( v = i+1; v < k; v++ )
            printf( "-" );
        printf( ">" );
        for ( v = k+1; v < 8; v++ )
            printf( " " );
        printf( "    " );
        printf( "[%3d :%3d ] -> [%3d :%3d ]\n", pVars[i], pVars[k], iVar1, iVar2 );
    }
//    sat_solver_add_and1( p, iVar1, pVars[i], pVars[k], 1, 1, 1 );
//    sat_solver_add_and2( p, iVar2, pVars[i], pVars[k], 0, 0, 0 );
    sat_solver_add_half_sorter( p, iVar1, iVar2, pVars[i], pVars[k] );
    pVars[i] = iVar1;
    pVars[k] = iVar2;
}
static inline void Sbm_AddCardinConstrMerge( sat_solver * p, int * pVars, int lo, int hi, int r, int * pnVars )
{
    int i, step = r * 2;
    if ( step < hi - lo )
    {
        Sbm_AddCardinConstrMerge( p, pVars, lo, hi-r, step, pnVars );
        Sbm_AddCardinConstrMerge( p, pVars, lo+r, hi, step, pnVars );
        for ( i = lo+r; i < hi-r; i += step )
            Sbm_AddSorter( p, pVars, i, i+r, pnVars );
    }
}
static inline void Sbm_AddCardinConstrRange( sat_solver * p, int * pVars, int lo, int hi, int * pnVars )
{
    if ( hi - lo >= 1 )
    {
        int i, mid = lo + (hi - lo) / 2;
        for ( i = lo; i <= mid; i++ )
            Sbm_AddSorter( p, pVars, i, i + (hi - lo + 1) / 2, pnVars );
        Sbm_AddCardinConstrRange( p, pVars, lo, mid, pnVars );
        Sbm_AddCardinConstrRange( p, pVars, mid+1, hi, pnVars );
        Sbm_AddCardinConstrMerge( p, pVars, lo, hi, 1, pnVars );
    }
}
int Sbm_AddCardinConstrPairWise( sat_solver * p, Vec_Int_t * vVars, int K )
{
    int nVars = Vec_IntSize(vVars);
    Sbm_AddCardinConstrRange( p, Vec_IntArray(vVars), 0, nVars - 1, &nVars );
    sat_solver_bookmark( p );
    return nVars;
}
sat_solver * Sbm_AddCardinSolver( int LogN, Vec_Int_t ** pvVars )
{
    int nVars = 1 << LogN;
    int nVarsAlloc = nVars + 2 * (nVars * LogN * (LogN-1) / 4 + nVars - 1), nVarsReal;
    Vec_Int_t * vVars = Vec_IntStartNatural( nVars );
    sat_solver * pSat = sat_solver_new();
    sat_solver_setnvars( pSat, nVarsAlloc );
    nVarsReal = Sbm_AddCardinConstrPairWise( pSat, vVars, 2 );
    assert( nVarsReal == nVarsAlloc );
    *pvVars = vVars;
    return pSat;
}

void Sbm_AddCardinConstrTest()
{
/*
    int Lit, LogN = 3, nVars = 1 << LogN, K = 2, Count = 1;
    int nVarsAlloc = nVars + 2 * (nVars * LogN * (LogN-1) / 4 + nVars - 1), nVarsReal;
    Vec_Int_t * vVars = Vec_IntStartNatural( nVars );
    sat_solver * pSat = sat_solver_new();
    sat_solver_setnvars( pSat, nVarsAlloc );
    nVarsReal = Sbm_AddCardinConstrPairWise( pSat, vVars, 2 );
    assert( nVarsReal == nVarsAlloc );
*/
    int LogN = 3, nVars = 1 << LogN, K = 2, Count = 1;
    Vec_Int_t * vVars, * vLits = Vec_IntAlloc( nVars );
    sat_solver * pSat = Sbm_AddCardinSolver( LogN, &vVars );
    int nVarsReal = sat_solver_nvars( pSat );

    int Lit = Abc_Var2Lit( Vec_IntEntry(vVars, K), 1 );
    printf( "LogN = %d. N = %3d.   Vars = %5d. Clauses = %6d.  Comb = %d.\n", LogN, nVars, nVarsReal, sat_solver_nclauses(pSat), nVars * (nVars-1)/2 + nVars + 1 );

    while ( 1 )
    {
        int i, status = sat_solver_solve( pSat, &Lit, &Lit+1, 0, 0, 0, 0 );
        if ( status != l_True )
            break;
        Vec_IntClear( vLits );
        printf( "%3d : ", Count++ );
        for ( i = 0; i < nVars; i++ )
        {
            Vec_IntPush( vLits, Abc_Var2Lit(i, sat_solver_var_value(pSat, i)) );
            printf( "%d", sat_solver_var_value(pSat, i) );
        }
        printf( "\n" );
        status = sat_solver_addclause( pSat, Vec_IntArray(vLits), Vec_IntArray(vLits) + nVars );
        if ( status == 0 )
            break;
    }

    sat_solver_delete( pSat );
    Vec_IntFree( vVars );
    Vec_IntFree( vLits );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Sbm_Man_t * Sbm_ManAlloc( int LogN )
{
    Sbm_Man_t * p = ABC_CALLOC( Sbm_Man_t, 1 );
    p->pSat = Sbm_AddCardinSolver( LogN, &p->vCardVars );
    p->LogN = LogN;
    p->FirstVar  = sat_solver_nvars( p->pSat );
    // window
    p->vRoots    = Vec_IntAlloc( 100 );
    p->vCuts     = Vec_WecAlloc( 1000 );
    p->vObjCuts  = Vec_WecAlloc( 1000 );
    p->vSolCuts  = Vec_IntAlloc( 100 );
    p->vCutGates = Vec_IntAlloc( 100 );
    // solver
    p->vAssump   = Vec_IntAlloc( 100 );
    p->vPolar    = Vec_IntAlloc( 100 );
    // timing
    p->vArrs     = Vec_IntAlloc( 100 );
    p->vReqs     = Vec_IntAlloc( 100 );
    // internal
    p->vLit2Used = Vec_IntAlloc( 100 );
    p->vDelays   = Vec_IntAlloc( 100 );
    p->vReason   = Vec_IntAlloc( 100 );
    return p;
}

void Sbm_ManStop( Sbm_Man_t * p )
{
    sat_solver_delete( p->pSat );
    Vec_IntFree( p->vCardVars );
    // internal
    Vec_IntFree( p->vRoots );
    Vec_WecFree( p->vCuts );
    Vec_WecFree( p->vObjCuts );
    Vec_IntFree( p->vSolCuts );
    Vec_IntFree( p->vCutGates );
    // internal
    Vec_IntFree( p->vAssump );
    Vec_IntFree( p->vPolar );
    // internal
    Vec_IntFree( p->vArrs );
    Vec_IntFree( p->vReqs );
    // internal
    Vec_IntFree( p->vLit2Used );
    Vec_IntFree( p->vDelays );
    Vec_IntFree( p->vReason );
}

int Sbm_ManTestSat( void * pMan )
{
    abctime clk = Abc_Clock(), clk2;
    int i, LogN = 4, nVars = 1 << LogN, status, Root;
    Sbm_Man_t * p = Sbm_ManAlloc( LogN );
    // derive window
    extern int Nf_ManExtractWindow( void * pMan, Vec_Int_t * vRoots, Vec_Wec_t * vCuts, Vec_Wec_t * vObjCuts, Vec_Int_t * vSolCuts, Vec_Int_t * vCutGates, int StartVar );
    p->LitShift = Nf_ManExtractWindow( pMan, p->vRoots, p->vCuts, p->vObjCuts, p->vSolCuts, p->vCutGates, p->FirstVar );
    assert( Vec_WecSize(p->vObjCuts) <= nVars );

    // print-out
//    Vec_WecPrint( p->vCuts, 0 );
//    printf( "\n" );
    Vec_WecPrint( p->vObjCuts, 0 );
    printf( "\n" );
    Vec_IntPrint( p->vSolCuts );

    // creating CNF
    if ( !Sbm_ManCreateCnf(p) )
        return 0;

    // create assumptions
    // cardinality
    Vec_IntClear( p->vAssump );
//    for ( i = 0; i < Vec_IntSize(p->vSolCuts); i++ )
//        Vec_IntPush( p->vAssump, Abc_Var2Lit(Vec_IntEntry(p->vCardVars, i), 1) );
    Vec_IntPush( p->vAssump, Abc_Var2Lit(Vec_IntEntry(p->vCardVars, Vec_IntSize(p->vSolCuts)), 1) );
    // unused variables
    for ( i = Vec_WecSize(p->vObjCuts); i < nVars; i++ )
        Vec_IntPush( p->vAssump, Abc_Var2Lit(i, 1) );
    // root variables
    Vec_IntForEachEntry( p->vRoots, Root, i )
        Vec_IntPush( p->vAssump, Abc_Var2Lit(Root, 0) );
//    Vec_IntPrint( p->vAssump );

    // solve the problem
    clk2 = Abc_Clock();
    status = sat_solver_solve( p->pSat, Vec_IntArray(p->vAssump), Vec_IntLimit(p->vAssump), 0, 0, 0, 0 );
    if ( status == l_False )
        printf( "UNSAT " );
    else if ( status == l_True )
        printf( "SAT   " );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk2 );

    if ( status == l_True )
    {
        for ( i = 0; i < nVars; i++ )
            printf( "%d", sat_solver_var_value(p->pSat, i) );
        printf( "\n" );
        for ( i = p->FirstVar; i < sat_solver_nvars(p->pSat); i++ )
            printf( "%d ", sat_solver_var_value(p->pSat, i) );
        printf( "\n" );
        for ( i = p->FirstVar; i < sat_solver_nvars(p->pSat); i++ )
            printf( "%d=%d ", i-p->FirstVar, sat_solver_var_value(p->pSat, i) );
        printf( "\n" );
    }

    Sbm_ManStop( p );
    return 1;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

