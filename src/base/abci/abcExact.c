/**CFile****************************************************************

  FileName    [abcExact.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Find minimum size networks with a SAT solver.]

  Author      [Mathias Soeken]

  Affiliation [EPFL]

  Date        [Ver. 1.0. Started - July 15, 2016.]

  Revision    [$Id: abcFanio.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

/* This implementation is based on Exercises 477 and 478 in
 * Donald E. Knuth TAOCP Fascicle 6 (Satisfiability) Section 7.2.2.2
 */

#include "base/abc/abc.h"

#include "misc/util/utilTruth.h"
#include "misc/vec/vecInt.h"
#include "misc/vec/vecPtr.h"
#include "sat/bsat/satSolver.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Ses_Man_t_ Ses_Man_t;
struct Ses_Man_t_
{
    sat_solver * pSat;          /* SAT solver */

    word *       pSpec;         /* specification */
    int          bSpecInv;      /* remembers whether spec was inverted for normalization */
    int          nSpecVars;     /* number of variables in specification */
    int          nSpecFunc;     /* number of functions to synthesize */
    int          nRows;         /* number of rows in the specification (without 0) */
    int          fVerbose;      /* be verbose */
    int          fVeryVerbose;  /* be very verbose */

    int          nGates;        /* number of gates */

    int          nSimVars;      /* number of simulation vars x(i, t) */
    int          nOutputVars;   /* number of output variables g(h, i) */
    int          nGateVars;     /* number of gate variables f(i, p, q) */
    int          nSelectVars;   /* number of select variables s(i, j, k ) */

    int          nOutputOffset; /* offset where output variables start */
    int          nGateOffset;   /* offset where gate variables start */
    int          nSelectOffset; /* offset where select variables start */

    abctime      timeSat;       /* SAT runtime */
    abctime      timeSatSat;    /* SAT runtime (sat instance) */
    abctime      timeSatUnsat;  /* SAT runtime (unsat instance) */
    abctime      timeTotal;     /* all runtime */
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

static inline Ses_Man_t * Ses_ManAlloc( word * pTruth, int nVars, int nFunc, int fVerbose )
{
    int h;

    Ses_Man_t * p = ABC_CALLOC( Ses_Man_t, 1 );
    p->pSat       = NULL;
    p->bSpecInv   = 0;
    for ( h = 0; h < nFunc; ++h )
        if ( pTruth[h] & 1 )
        {
            pTruth[h] = ~pTruth[h];
            p->bSpecInv |= ( 1 << h );
        }
    p->pSpec        = pTruth;
    p->nSpecVars    = nVars;
    p->nSpecFunc    = nFunc;
    p->nRows        = ( 1 << nVars ) - 1;
    p->fVerbose     = fVerbose;
    p->fVeryVerbose = 0;

    return p;
}

static inline void Ses_ManClean( Ses_Man_t * pSes )
{
    int h;
    for ( h = 0; h < pSes->nSpecFunc; ++h )
        if ( ( pSes->bSpecInv >> h ) & 1 )
            pSes->pSpec[h] = ~( pSes->pSpec[h] );

    if ( pSes->pSat )
        sat_solver_delete( pSes->pSat );
    
    ABC_FREE( pSes );
}

/**Function*************************************************************

  Synopsis    [Access variables based on indexes.]

***********************************************************************/
static inline int Ses_ManSimVar( Ses_Man_t * pSes, int i, int t )
{
    assert( i < pSes->nGates );
    assert( t < pSes->nRows );

    return pSes->nRows * i + t;
}

static inline int Ses_ManOutputVar( Ses_Man_t * pSes, int h, int i )
{
    assert( h < pSes->nSpecFunc );
    assert( i < pSes->nGates );

    return pSes->nOutputOffset + pSes->nGates * h + i;
}

static inline int Ses_ManGateVar( Ses_Man_t * pSes, int i, int p, int q )
{
    assert( i < pSes->nGates );
    assert( p < 2 );
    assert( q < 2 );
    assert( p > 0 || q > 0 );

    return pSes->nGateOffset + i * 3 + ( p << 1 ) + q - 1;
}

static inline int Ses_ManSelectVar( Ses_Man_t * pSes, int i, int j, int k )
{
    int a;
    int offset;

    assert( i < pSes->nGates );
    assert( k < pSes->nSpecVars + i );
    assert( j < k );

    offset = pSes->nSelectOffset;
    for ( a = pSes->nSpecVars; a < pSes->nSpecVars + i; ++a )
        offset += a * ( a - 1 ) / 2;

    return offset + ( -j * ( 1 + j - 2 * ( pSes->nSpecVars + i ) ) ) / 2 + ( k - j - 1 );
}

/**Function*************************************************************

  Synopsis    [Setup variables to find network with nGates gates.]

***********************************************************************/
static void Ses_ManCreateVars( Ses_Man_t * pSes, int nGates )
{
    int i;

    if ( pSes->fVerbose )
    {
        printf( "create variables for network with %d functions over %d variables and %d gates\n", pSes->nSpecFunc, pSes->nSpecVars, nGates );
    }

    pSes->nGates      = nGates;
    pSes->nSimVars    = nGates * pSes->nRows;
    pSes->nOutputVars = pSes->nSpecFunc * nGates;
    pSes->nGateVars   = nGates * 3;
    pSes->nSelectVars = 0;
    for ( i = pSes->nSpecVars; i < pSes->nSpecVars + nGates; ++i )
        pSes->nSelectVars += ( i * ( i - 1 ) ) / 2;

    pSes->nOutputOffset = pSes->nSimVars;
    pSes->nGateOffset   = pSes->nSimVars + pSes->nOutputVars;
    pSes->nSelectOffset = pSes->nSimVars + pSes->nOutputVars + pSes->nGateVars;

    if ( pSes->pSat )
        sat_solver_delete( pSes->pSat );
    pSes->pSat = sat_solver_new();
    sat_solver_setnvars( pSes->pSat, pSes->nSimVars + pSes->nOutputVars + pSes->nGateVars + pSes->nSelectVars );
}

/**Function*************************************************************

  Synopsis    [Create clauses.]

***********************************************************************/
static inline void Ses_ManCreateMainClause( Ses_Man_t * pSes, int t, int i, int j, int k, int a, int b, int c )
{
    int pLits[5], ctr = 0, value;

    pLits[ctr++] = Abc_Var2Lit( Ses_ManSelectVar( pSes, i, j, k ), 1 );
    pLits[ctr++] = Abc_Var2Lit( Ses_ManSimVar( pSes, i, t ), a );

    if ( j < pSes->nSpecVars )
    {
        if ( ( ( s_Truths6[j] >> ( t + 1 ) ) & 1 ) != b ) /* 1 in clause, we can omit the clause */
            return;
    }
    else
        pLits[ctr++] = Abc_Var2Lit( Ses_ManSimVar( pSes, j - pSes->nSpecVars, t ), b );

    if ( k < pSes->nSpecVars )
    {
        if ( ( ( s_Truths6[k] >> ( t + 1 ) ) & 1 ) != c ) /* 1 in clause, we can omit the clause */
            return;
    }
    else
        pLits[ctr++] = Abc_Var2Lit( Ses_ManSimVar( pSes, k - pSes->nSpecVars, t ), c );

    if ( b > 0 || c > 0 )
        pLits[ctr++] = Abc_Var2Lit( Ses_ManGateVar( pSes, i, b, c ), 1 - a );

    value = sat_solver_addclause( pSes->pSat, pLits, pLits + ctr );
    assert( value );
}

static void Ses_ManCreateClauses( Ses_Man_t * pSes )
{
    extern int Extra_TruthVarsSymm( unsigned * pTruth, int nVars, int iVar0, int iVar1 );

    int h, i, j, k, t, ii, jj, kk, p, q;
    int pLits[2];
    Vec_Int_t * vLits;

    for ( t = 0; t < pSes->nRows; ++t )
        for ( i = 0; i < pSes->nGates; ++i )
        {
            /* main clauses */
            for ( j = 0; j < pSes->nSpecVars + i; ++j )
                for ( k = j + 1; k < pSes->nSpecVars + i; ++k )
                {
                    Ses_ManCreateMainClause( pSes, t, i, j, k, 0, 0, 1 );
                    Ses_ManCreateMainClause( pSes, t, i, j, k, 0, 1, 0 );
                    Ses_ManCreateMainClause( pSes, t, i, j, k, 0, 1, 1 );
                    Ses_ManCreateMainClause( pSes, t, i, j, k, 1, 0, 0 );
                    Ses_ManCreateMainClause( pSes, t, i, j, k, 1, 0, 1 );
                    Ses_ManCreateMainClause( pSes, t, i, j, k, 1, 1, 0 );
                    Ses_ManCreateMainClause( pSes, t, i, j, k, 1, 1, 1 );
                }

            /* output clauses */
            for ( h = 0; h < pSes->nSpecFunc; ++h )
            {
                pLits[0] = Abc_Var2Lit( Ses_ManOutputVar( pSes, h, i ), 1 );
                pLits[1] = Abc_Var2Lit( Ses_ManSimVar( pSes, i, t ), 1 - (int)( ( pSes->pSpec[h] >> ( t + 1 ) ) & 1 ) );
                assert( sat_solver_addclause( pSes->pSat, pLits, pLits + 2 ) );
            }
        }

    /* some output is selected */
    for ( h = 0; h < pSes->nSpecFunc; ++h )
    {
        vLits = Vec_IntAlloc( pSes->nGates );
        for ( i = 0; i < pSes->nGates; ++i )
            Vec_IntPush( vLits, Abc_Var2Lit( Ses_ManOutputVar( pSes, h, i ), 0 ) );
        assert( sat_solver_addclause( pSes->pSat, Vec_IntArray( vLits ), Vec_IntLimit( vLits ) ) );
        Vec_IntFree( vLits );
    }

    /* each gate has two operands */
    for ( i = 0; i < pSes->nGates; ++i )
    {
        vLits = Vec_IntAlloc( ( ( pSes->nSpecVars + i ) * ( pSes->nSpecVars + i - 1 ) ) / 2 );
        for ( j = 0; j < pSes->nSpecVars + i; ++j )
            for ( k = j + 1; k < pSes->nSpecVars + i; ++k )
                Vec_IntPush( vLits, Abc_Var2Lit( Ses_ManSelectVar( pSes, i, j, k ), 0 ) );
        assert( sat_solver_addclause( pSes->pSat, Vec_IntArray( vLits ), Vec_IntLimit( vLits ) ) );
        Vec_IntFree( vLits );
    }

    /* EXTRA clauses: use gate i at least once */
    for ( i = 0; i < pSes->nGates; ++i )
    {
        vLits = Vec_IntAlloc( 0 );
        for ( h = 0; h < pSes->nSpecFunc; ++h )
            Vec_IntPush( vLits, Abc_Var2Lit( Ses_ManOutputVar( pSes, h, i ), 0 ) );
        for ( ii = i + 1; ii < pSes->nGates; ++ii )
        {
            for ( j = 0; j < pSes->nSpecVars + i; ++j )
                Vec_IntPush( vLits, Abc_Var2Lit( Ses_ManSelectVar( pSes, ii, j, pSes->nSpecVars + i ), 0 ) );
            for ( j = pSes->nSpecVars + i + 1; j < pSes->nSpecVars + ii; ++j )
                Vec_IntPush( vLits, Abc_Var2Lit( Ses_ManSelectVar( pSes, ii, pSes->nSpecVars + i, j ), 0 ) );
        }
        assert( sat_solver_addclause( pSes->pSat, Vec_IntArray( vLits ), Vec_IntLimit( vLits ) ) );
        Vec_IntFree( vLits );
    }

    /* EXTRA clauses: co-lexicographic order */
    for ( i = 0; i < pSes->nGates - 1; ++i )
    {
        for ( k = 2; k < pSes->nSpecVars + i; ++k )
        {
            for ( j = 1; j < k; ++j )
                for ( jj = 0; jj < j; ++jj )
                {
                    pLits[0] = Abc_Var2Lit( Ses_ManSelectVar( pSes, i, j, k ), 1 );
                    pLits[1] = Abc_Var2Lit( Ses_ManSelectVar( pSes, i + 1, jj, k ), 1 );
                }

            for ( j = 0; j < k; ++j )
                for ( kk = 1; kk < k; ++kk )
                    for ( jj = 0; jj < kk; ++jj )
                    {
                        pLits[0] = Abc_Var2Lit( Ses_ManSelectVar( pSes, i, j, k ), 1 );
                        pLits[1] = Abc_Var2Lit( Ses_ManSelectVar( pSes, i + 1, jj, kk ), 1 );
                    }
        }
    }

    /* EXTRA clauses: symmetric variables */
    if ( pSes->nSpecFunc == 1 ) /* only check if there is one output function */
        for ( q = 1; q < pSes->nSpecVars; ++q )
            for ( p = 0; p < q; ++p )
                if ( Extra_TruthVarsSymm( (unsigned*)pSes->pSpec, pSes->nSpecVars, p, q ) )
                {
                    if ( pSes->fVeryVerbose )
                        printf( "variables %d and %d are symmetric\n", p, q );
                    for ( i = 0; i < pSes->nGates; ++i )
                        for ( j = 0; j < q; ++j )
                        {
                            if ( j == p ) continue;

                            vLits = Vec_IntAlloc( 0 );
                            Vec_IntPush( vLits, Abc_Var2Lit( Ses_ManSelectVar( pSes, i, j, q ), 1 ) );
                            for ( ii = 0; ii < i; ++ii )
                                for ( kk = 1; kk < pSes->nSpecVars + ii; ++kk )
                                    for ( jj = 0; jj < kk; ++jj )
                                        if ( jj == p || kk == p )
                                            Vec_IntPush( vLits, Abc_Var2Lit( Ses_ManSelectVar( pSes, ii, jj, kk ), 0 ) );
                            assert( sat_solver_addclause( pSes->pSat, Vec_IntArray( vLits ), Vec_IntLimit( vLits ) ) );
                            Vec_IntFree( vLits );
                        }
                }
}

/**Function*************************************************************

  Synopsis    [Solve.]

***********************************************************************/
static inline int Ses_ManSolve( Ses_Man_t * pSes )
{
    int status;
    abctime timeStart, timeDelta;

    // if ( pSes->fVerbose )
    // {
    //     printf( "solve SAT instance with %d clauses and %d variables\n", sat_solver_nclauses( pSes->pSat ), sat_solver_nvars( pSes->pSat ) );
    // }

    timeStart = Abc_Clock();
    status = sat_solver_solve( pSes->pSat, NULL, NULL, 0, 0, 0, 0 );
    timeDelta = Abc_Clock() - timeStart;

    pSes->timeSat += timeDelta;

    if ( status == l_True )
    {
        pSes->timeSatSat += timeDelta;
        return 1;
    }
    else if ( status == l_False )
    {
        pSes->timeSatUnsat += timeDelta;
        return 0;
    }
    else
    {
        if ( pSes->fVerbose )
        {
            printf( "undefined\n" );
        }
        return 0;
    }
}

/**Function*************************************************************

  Synopsis    [Extract solution.]

***********************************************************************/
static Abc_Ntk_t * Ses_ManExtractSolution( Ses_Man_t * pSes )
{
    int h, i, j, k;
    Abc_Ntk_t * pNtk;
    Abc_Obj_t * pObj;
    Vec_Ptr_t * pGates, * vNames;
    char pGateTruth[5];
    char * pSopCover;

    pNtk = Abc_NtkAlloc( ABC_NTK_LOGIC, ABC_FUNC_SOP, 1 );
    pNtk->pName = Extra_UtilStrsav( "exact" );
    pGates = Vec_PtrAlloc( pSes->nSpecVars + pSes->nGates );
    pGateTruth[3] = '0';
    pGateTruth[4] = '\0';
    vNames = Abc_NodeGetFakeNames( pSes->nSpecVars + pSes->nSpecFunc );

    /* primary inputs */
    Vec_PtrPush( pNtk->vObjs, NULL );
    for ( i = 0; i < pSes->nSpecVars; ++i )
    {
        pObj = Abc_NtkCreatePi( pNtk );
        Abc_ObjAssignName( pObj, (char*)Vec_PtrEntry( vNames, i ), NULL );
        Vec_PtrPush( pGates, pObj );
    }

    /* gates */
    for ( i = 0; i < pSes->nGates; ++i )
    {
        pGateTruth[2] = '0' + sat_solver_var_value( pSes->pSat, Ses_ManGateVar( pSes, i, 0, 1 ) );
        pGateTruth[1] = '0' + sat_solver_var_value( pSes->pSat, Ses_ManGateVar( pSes, i, 1, 0 ) );
        pGateTruth[0] = '0' + sat_solver_var_value( pSes->pSat, Ses_ManGateVar( pSes, i, 1, 1 ) );

        if ( pSes->fVeryVerbose )
        {
            printf( "gate %d has truth table %s", pSes->nSpecVars + i, pGateTruth );
        }

        pSopCover = Abc_SopFromTruthBin( pGateTruth );
        pObj = Abc_NtkCreateNode( pNtk );
        pObj->pData = Abc_SopRegister( (Mem_Flex_t*)pNtk->pManFunc, pSopCover );
        Vec_PtrPush( pGates, pObj );
        ABC_FREE( pSopCover );

        for ( k = 0; k < pSes->nSpecVars + i; ++k )
            for ( j = 0; j < k; ++j )
                if ( sat_solver_var_value( pSes->pSat, Ses_ManSelectVar( pSes, i, j, k ) ) )
                {
                    if ( pSes->fVeryVerbose )
                        printf( " with children %d and %d\n", j, k );
                    Abc_ObjAddFanin( pObj, (Abc_Obj_t *)Vec_PtrEntry( pGates, j ) );
                    Abc_ObjAddFanin( pObj, (Abc_Obj_t *)Vec_PtrEntry( pGates, k ) );
                    break;
                }
    }

    /* outputs */
    for ( h = 0; h < pSes->nSpecFunc; ++h )
    {
        pObj = Abc_NtkCreatePo( pNtk );
        Abc_ObjAssignName( pObj, (char*)Vec_PtrEntry( vNames, pSes->nSpecVars + h ), NULL );
        for ( i = 0; i < pSes->nGates; ++i )
        {
            if ( sat_solver_var_value( pSes->pSat, Ses_ManOutputVar( pSes, h, i ) ) )
            {
                /* if output has been inverted, we need to add an inverter */
                if ( ( pSes->bSpecInv >> h ) & 1 )
                    Abc_ObjAddFanin( pObj, Abc_NtkCreateNodeInv( pNtk, (Abc_Obj_t *)Vec_PtrEntry( pGates, pSes->nSpecVars + i ) ) );
                else
                    Abc_ObjAddFanin( pObj, (Abc_Obj_t *)Vec_PtrEntry( pGates, pSes->nSpecVars + i ) );
            }
        }
    }
    Abc_NodeFreeNames( vNames );

    Vec_PtrFree( pGates );

    if ( !Abc_NtkCheck( pNtk ) )
        printf( "Ses_ManExtractSolution(): Network check has failed.\n" );


    return pNtk;
}

/**Function*************************************************************

  Synopsis    [Synthesis algorithm.]

***********************************************************************/
static Abc_Ntk_t * Ses_ManFindMinimumSize( Ses_Man_t * pSes )
{
    int nGates = 0;
    abctime timeStart;
    Abc_Ntk_t * pNtk;

    timeStart = Abc_Clock();

    while ( true )
    {
        ++nGates;
        Ses_ManCreateVars( pSes, nGates );
        Ses_ManCreateClauses( pSes );
        if ( Ses_ManSolve( pSes ) )
        {
            pNtk = Ses_ManExtractSolution( pSes );
            pSes->timeTotal = Abc_Clock() - timeStart;
            return pNtk;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Debug.]

***********************************************************************/
static void Ses_ManPrintRuntime( Ses_Man_t * pSes )
{
    printf( "Runtime breakdown:\n" );
    ABC_PRTP( "Sat   ", pSes->timeSat,      pSes->timeTotal );
    ABC_PRTP( " Sat  ", pSes->timeSatSat,   pSes->timeTotal );
    ABC_PRTP( " Unsat", pSes->timeSatUnsat, pSes->timeTotal );
    ABC_PRTP( "ALL   ", pSes->timeTotal,    pSes->timeTotal );
}

static inline void Ses_ManPrintVars( Ses_Man_t * pSes )
{
    int h, i, j, k, p, q, t;

    for ( i = 0; i < pSes->nGates; ++i )
        for ( t = 0; t < pSes->nRows; ++t )
            printf( "x(%d, %d) : %d\n", i, t, Ses_ManSimVar( pSes, i, t ) );

    for ( h = 0; h < pSes->nSpecFunc; ++h )
        for ( i = 0; i < pSes->nGates; ++i )
            printf( "h(%d, %d) : %d\n", h, i, Ses_ManOutputVar( pSes, h, i ) );

    for ( i = 0; i < pSes->nGates; ++i )
        for ( p = 0; p <= 1; ++p )
            for ( q = 0; q <= 1; ++ q)
            {
                if ( p == 0 && q == 0 ) { continue; }
                printf( "f(%d, %d, %d) : %d\n", i, p, q, Ses_ManGateVar( pSes, i, p, q ) );
            }

    for ( i = 0; i < pSes->nGates; ++i )
        for ( j = 0; j < pSes->nSpecVars + i; ++j )
            for ( k = j + 1; k < pSes->nSpecVars + i; ++k )
                printf( "s(%d, %d, %d) : %d\n", i, j, k, Ses_ManSelectVar( pSes, i, j, k ) );

}

/**Function*************************************************************

  Synopsis    [Find minimum size networks with a SAT solver.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkFindExact( word * pTruth, int nVars, int nFunc, int fVerbose )
{
    int i, j;
    Ses_Man_t * pSes;
    Abc_Ntk_t * pNtk;

    /* some checks */
    assert( nVars >= 2 && nVars <= 6 );

    if ( fVerbose )
    {
        printf( "find optimum circuit for %d %d-variable functions:\n", nFunc, nVars );
        for ( i = 0; i < nFunc; ++i )
        {
            printf( "  func %d: ", i + 1 );
            for ( j = 0; j < ( 1 << nVars ); ++j )
                printf( "%lu", ( pTruth[i] >> j ) & 1 );
            printf( "\n" );
        }
    }

    pSes = Ses_ManAlloc( pTruth, nVars, nFunc, fVerbose );
    pNtk = Ses_ManFindMinimumSize( pSes );

    if ( fVerbose )
        Ses_ManPrintRuntime( pSes );

    /* cleanup */
    Ses_ManClean( pSes );

    return pNtk;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
