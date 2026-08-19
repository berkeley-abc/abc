/**CFile****************************************************************

  FileName    [fm_camus.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ForMACE CaDiCaL-backed CAMUS-style MUS support.]

  Synopsis    [In-process CaDiCaL-backed guarded constraint-group API.]

***********************************************************************/

#include "fm_camus.h"
#include "sat/cadical/cadicalSolver.h"
#include <string.h>

ABC_NAMESPACE_IMPL_START

enum { FM_CAMUS_UNSAT = -1, FM_CAMUS_UNDEF = 0, FM_CAMUS_SAT = 1 };

struct Fm_CamusMan_t_
{
    cadical_solver * pSat;
    int            nVars;
    int            nGroups;
    int            fInvalid;
    int            fRootUnsat;
    ABC_INT64_T    nConfLimit;
    abctime        nTimeOut;
    Fm_CamusOptions_t Options;
    Fm_CamusStats_t   Stats;
};

static Vec_Int_t * Fm_CamusNormalizeGroups( Fm_CamusMan_t * p, Vec_Int_t * vEnabled )
{
    Vec_Int_t * vGroups;
    int i, iGroup;

    if ( p == NULL || vEnabled == NULL )
        return NULL;
    vGroups = Vec_IntDup( vEnabled );
    Vec_IntSort( vGroups, 0 );
    Vec_IntForEachEntry( vGroups, iGroup, i )
        if ( iGroup < 0 || iGroup >= p->nGroups || (i && iGroup == Vec_IntEntry(vGroups, i - 1)) )
        {
            Vec_IntFree( vGroups );
            return NULL;
        }
    return vGroups;
}

const char * Fm_CamusBackendName( void )
{
    return cadical_solver_signature();
}

void Fm_CamusOptionsDefault( Fm_CamusOptions_t * pOptions )
{
    if ( pOptions == NULL )
        return;
    memset( pOptions, 0, sizeof(*pOptions) );
    pOptions->fUseCoreShrink = 1;
    pOptions->fUseMusSeed = 1;
    pOptions->fMinimizeSeed = 1;
    pOptions->fUseModelAbsorb = 1;
    pOptions->fGrowMcs = 1;
    pOptions->fBinaryMapBounds = 1;
    pOptions->fUseCadicalTuning = 1;
    pOptions->fUseCadicalPlain = 1;
    pOptions->fUseCadicalIlb = 1;
    pOptions->fUseCadicalStableOnly = 1;
}

void Fm_CamusGetStats( Fm_CamusMan_t * p, Fm_CamusStats_t * pStats )
{
    if ( pStats == NULL )
        return;
    if ( p == NULL )
        memset( pStats, 0, sizeof(*pStats) );
    else
        *pStats = p->Stats;
}

Fm_CamusMan_t * Fm_CamusStartWithOptions( int nVars, int nGroups, const Fm_CamusOptions_t * pOptions )
{
    Fm_CamusMan_t * p;
    if ( nVars < 0 || nGroups < 0 )
        return NULL;
    p = ABC_CALLOC( Fm_CamusMan_t, 1 );
    if ( pOptions == NULL )
        Fm_CamusOptionsDefault( &p->Options );
    else
        p->Options = *pOptions;
    p->pSat = cadical_solver_new();
    if ( p->pSat == NULL ||
         (p->Options.fUseCadicalTuning && p->Options.fUseCadicalPlain &&
          !cadical_solver_configure(p->pSat, "plain")) ||
         (p->Options.fUseCadicalTuning && p->Options.fUseCadicalIlb &&
          !cadical_solver_set_option(p->pSat, "ilb", 2)) ||
         (p->Options.fUseCadicalTuning && p->Options.fUseCadicalStableOnly &&
          !cadical_solver_set_option(p->pSat, "stabilizeonly", 1)) ||
         !cadical_solver_set_option(p->pSat, "checkassumptions", 0) ||
         !cadical_solver_set_option(p->pSat, "checkconstraint", 0) ||
         !cadical_solver_set_option(p->pSat, "checkfailed", 0) )
    {
        if ( p->pSat )
            cadical_solver_delete( p->pSat );
        ABC_FREE( p );
        return NULL;
    }
    p->nVars = nVars;
    p->nGroups = nGroups;
    cadical_solver_setnvars( p->pSat, nVars + nGroups );
    return p;
}

Fm_CamusMan_t * Fm_CamusStart( int nVars, int nGroups )
{
    return Fm_CamusStartWithOptions( nVars, nGroups, NULL );
}

void Fm_CamusStop( Fm_CamusMan_t * p )
{
    if ( p == NULL )
        return;
    cadical_solver_delete( p->pSat );
    ABC_FREE( p );
}

void Fm_CamusSetLimits( Fm_CamusMan_t * p, ABC_INT64_T nConfLimit, abctime nTimeOut )
{
    if ( p == NULL )
        return;
    p->nConfLimit = nConfLimit;
    p->nTimeOut = nTimeOut;
    cadical_solver_set_runtime_limit( p->pSat, nTimeOut );
}

int Fm_CamusAddBackground( Fm_CamusMan_t * p, int * pLits, int nLits )
{
    int * pLimit;
    int i;
    if ( p == NULL || p->fInvalid || nLits < 0 || (nLits && pLits == NULL) )
        return 0;
    for ( i = 0; i < nLits; i++ )
        if ( pLits[i] < 0 || Abc_Lit2Var(pLits[i]) >= p->nVars )
        {
            p->fInvalid = 1;
            return 0;
        }
    pLimit = nLits ? pLits + nLits : pLits;
    if ( !cadical_solver_addclause(p->pSat, pLits, pLimit) )
        p->fRootUnsat = 1;
    return 1;
}

int Fm_CamusAddGroup( Fm_CamusMan_t * p, int iGroup, int * pLits, int nLits )
{
    int * pClause;
    int i, RetValue;
    if ( p == NULL || p->fInvalid || iGroup < 0 || iGroup >= p->nGroups || nLits < 0 || (nLits && pLits == NULL) )
        return 0;
    for ( i = 0; i < nLits; i++ )
        if ( pLits[i] < 0 || Abc_Lit2Var(pLits[i]) >= p->nVars )
        {
            p->fInvalid = 1;
            return 0;
        }
    pClause = ABC_ALLOC( int, nLits + 1 );
    pClause[0] = Abc_Var2Lit( p->nVars + iGroup, 1 );
    for ( i = 0; i < nLits; i++ )
        pClause[i + 1] = pLits[i];
    RetValue = cadical_solver_addclause( p->pSat, pClause, pClause + nLits + 1 );
    ABC_FREE( pClause );
    if ( !RetValue )
        p->fRootUnsat = 1;
    return 1;
}

int Fm_CamusSolve( Fm_CamusMan_t * p, Vec_Int_t * vEnabled )
{
    Vec_Int_t * vGroups, * vAssumps;
    int i, iGroup, RetValue;
    if ( p == NULL || p->fInvalid )
        return FM_CAMUS_UNDEF;
    if ( p->fRootUnsat )
        return FM_CAMUS_UNSAT;
    vGroups = Fm_CamusNormalizeGroups( p, vEnabled );
    if ( vGroups == NULL )
        return FM_CAMUS_UNDEF;
    vAssumps = Vec_IntAlloc( Vec_IntSize(vGroups) );
    Vec_IntForEachEntry( vGroups, iGroup, i )
        Vec_IntPush( vAssumps, Abc_Var2Lit(p->nVars + iGroup, 0) );
    RetValue = cadical_solver_solve( p->pSat, Vec_IntArray(vAssumps), Vec_IntLimit(vAssumps), p->nConfLimit, 0, 0, 0 );
    Vec_IntFree( vGroups );
    Vec_IntFree( vAssumps );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Returns CaDiCaL's failed-assumption UNSAT core as groups.]

***********************************************************************/
static Vec_Int_t * Fm_CamusExtractCore( Fm_CamusMan_t * p )
{
    Vec_Int_t * vCore;
    int * pCoreLits = NULL;
    int i, iGroup, nCore;
    if ( p->fRootUnsat )
        return Vec_IntAlloc( 0 );
    nCore = cadical_solver_final( p->pSat, &pCoreLits );
    vCore = Vec_IntAlloc( nCore );
    for ( i = 0; i < nCore; i++ )
    {
        iGroup = Abc_Lit2Var(pCoreLits[i]) - p->nVars;
        if ( iGroup < 0 || iGroup >= p->nGroups )
        {
            Vec_IntFree( vCore );
            return NULL;
        }
        Vec_IntPush( vCore, iGroup );
    }
    Vec_IntSort( vCore, 0 );
    return vCore;
}

static Vec_Int_t * Fm_CamusFindMusInternal( Fm_CamusMan_t * p, Vec_Int_t * vEnabled,
                                            int fMinimize )
{
    Vec_Int_t * vMus, * vCore;
    int i, iGroup, RetValue;
    vMus = Fm_CamusNormalizeGroups( p, vEnabled );
    if ( vMus == NULL )
        return NULL;
    p->Stats.nSeedInput = Vec_IntSize( vMus );
    p->Stats.nSeedSolves++;
    if ( Fm_CamusSolve(p, vMus) != FM_CAMUS_UNSAT )
    {
        Vec_IntFree( vMus );
        return NULL;
    }
    if ( p->Options.fUseCoreShrink )
    {
        vCore = Fm_CamusExtractCore( p );
        if ( vCore == NULL )
        {
            Vec_IntFree( vMus );
            return NULL;
        }
        if ( Vec_IntSize(vCore) < Vec_IntSize(vMus) )
        {
            p->Stats.nCoreShrinks++;
            p->Stats.nCoreGroupsRemoved += Vec_IntSize(vMus) - Vec_IntSize(vCore);
            Vec_IntFree( vMus );
            vMus = vCore;
        }
        else
            Vec_IntFree( vCore );
    }
    if ( !fMinimize )
    {
        p->Stats.nSeedResult = Vec_IntSize( vMus );
        return vMus;
    }
    for ( i = 0; i < Vec_IntSize(vMus); )
    {
        iGroup = Vec_IntEntry( vMus, i );
        Vec_IntDrop( vMus, i );
        p->Stats.nSeedSolves++;
        RetValue = Fm_CamusSolve( p, vMus );
        if ( RetValue == FM_CAMUS_UNSAT )
        {
            if ( p->Options.fUseCoreShrink )
            {
                vCore = Fm_CamusExtractCore( p );
                if ( vCore == NULL )
                {
                    Vec_IntFree( vMus );
                    return NULL;
                }
                if ( Vec_IntSize(vCore) < Vec_IntSize(vMus) )
                {
                    p->Stats.nCoreShrinks++;
                    p->Stats.nCoreGroupsRemoved += Vec_IntSize(vMus) - Vec_IntSize(vCore);
                    Vec_IntFree( vMus );
                    vMus = vCore;
                    i = 0;
                }
                else
                    Vec_IntFree( vCore );
            }
            continue;
        }
        if ( RetValue != FM_CAMUS_SAT )
        {
            Vec_IntFree( vMus );
            return NULL;
        }
        Vec_IntInsert( vMus, i, iGroup );
        i++;
    }
    p->Stats.nSeedResult = Vec_IntSize( vMus );
    return vMus;
}

Vec_Int_t * Fm_CamusFindMus( Fm_CamusMan_t * p, Vec_Int_t * vEnabled )
{
    return Fm_CamusFindMusInternal( p, vEnabled, 1 );
}

/**Function*************************************************************

  Synopsis    [Adds a sequential-counter AtMost constraint to the map solver.]

***********************************************************************/
static int Fm_CamusMapAddAtMost( cadical_solver * pSat, Fm_CamusMan_t * p,
                                 Vec_Int_t * vCandidates, int Bound )
{
    int Lits[3], i, j, n, Width, Columns, PrevColumns;
    n = Vec_IntSize( vCandidates );
    if ( Bound >= n )
        return 1;
    Width = Bound + 1;
    for ( i = 0; i < n; i++ )
    {
        Columns = Abc_MinInt( i + 1, Width );
        Lits[0] = Abc_Var2Lit( Vec_IntEntry(vCandidates, i), 1 );
        Lits[1] = Abc_Var2Lit( p->nGroups + i * Width, 0 );
        if ( !cadical_solver_addclause(pSat, Lits, Lits + 2) )
            return 0;
        if ( i == 0 )
            continue;
        PrevColumns = Abc_MinInt( i, Width );
        for ( j = 0; j < PrevColumns && j < Columns; j++ )
        {
            Lits[0] = Abc_Var2Lit( p->nGroups + (i - 1) * Width + j, 1 );
            Lits[1] = Abc_Var2Lit( p->nGroups + i * Width + j, 0 );
            if ( !cadical_solver_addclause(pSat, Lits, Lits + 2) )
                return 0;
        }
        for ( j = 1; j < Columns; j++ )
        {
            Lits[0] = Abc_Var2Lit( Vec_IntEntry(vCandidates, i), 1 );
            Lits[1] = Abc_Var2Lit( p->nGroups + (i - 1) * Width + j - 1, 1 );
            Lits[2] = Abc_Var2Lit( p->nGroups + i * Width + j, 0 );
            if ( !cadical_solver_addclause(pSat, Lits, Lits + 3) )
                return 0;
        }
    }
    Lits[0] = Abc_Var2Lit( p->nGroups + (n - 1) * Width + Width - 1, 1 );
    return cadical_solver_addclause( pSat, Lits, Lits + 1 );
}

/**Function*************************************************************

  Synopsis    [Solves one bounded hitting-set map problem with CaDiCaL.]

***********************************************************************/
static Vec_Int_t * Fm_CamusMapSolve( Fm_CamusMan_t * p, Vec_Int_t * vCandidates,
                                     Vec_Ptr_t * vMcses, int Bound, int * pStatus )
{
    abctime clk = Abc_Clock();
    cadical_solver * pMap = cadical_solver_new();
    Vec_Int_t * vMcs, * vResult = NULL;
    int * pClause;
    int i, k, iGroup, RetValue = FM_CAMUS_UNSAT;
    p->Stats.nMapSolves++;
    p->Stats.nSolverConstructions++;
    if ( pMap == NULL ||
         !cadical_solver_set_option(pMap, "checkassumptions", 0) ||
         !cadical_solver_set_option(pMap, "checkconstraint", 0) ||
         !cadical_solver_set_option(pMap, "checkfailed", 0) )
    {
        RetValue = FM_CAMUS_UNDEF;
        goto finish;
    }
    cadical_solver_set_runtime_limit( pMap, p->nTimeOut );
    cadical_solver_setnvars( pMap, p->nGroups + Vec_IntSize(vCandidates) * (Bound + 1) );
    Vec_PtrForEachEntry( Vec_Int_t *, vMcses, vMcs, i )
    {
        pClause = ABC_ALLOC( int, Vec_IntSize(vMcs) );
        Vec_IntForEachEntry( vMcs, iGroup, k )
            pClause[k] = Abc_Var2Lit( iGroup, 0 );
        RetValue = cadical_solver_addclause( pMap, pClause, pClause + Vec_IntSize(vMcs) );
        ABC_FREE( pClause );
        if ( !RetValue )
        {
            RetValue = FM_CAMUS_UNSAT;
            goto finish;
        }
    }
    if ( !Fm_CamusMapAddAtMost(pMap, p, vCandidates, Bound) )
    {
        RetValue = FM_CAMUS_UNSAT;
        goto finish;
    }
    RetValue = cadical_solver_solve( pMap, NULL, NULL, p->nConfLimit, 0, 0, 0 );
    if ( RetValue == FM_CAMUS_SAT )
    {
        vResult = Vec_IntAlloc( Bound );
        Vec_IntForEachEntry( vCandidates, iGroup, i )
            if ( cadical_solver_get_var_value(pMap, iGroup) )
                Vec_IntPush( vResult, iGroup );
    }

finish:
    if ( pMap )
        cadical_solver_delete( pMap );
    p->Stats.timeMap += Abc_Clock() - clk;
    if ( RetValue == FM_CAMUS_SAT )
        p->Stats.nMapSat++;
    else if ( RetValue == FM_CAMUS_UNSAT )
        p->Stats.nMapUnsat++;
    *pStatus = RetValue;
    return vResult;
}

/**Function*************************************************************

  Synopsis    [Computes a minimum hitting set with bounded map queries.]

***********************************************************************/
static Vec_Int_t * Fm_CamusMinimumHit( Fm_CamusMan_t * p, Vec_Int_t * vCandidates,
                                      Vec_Ptr_t * vMcses, Vec_Int_t * vUpper )
{
    Vec_Int_t * vBest = Vec_IntDup( vUpper );
    Vec_Int_t * vTrial;
    int Low = 0, High = Vec_IntSize(vUpper) - 1, Bound, Status;
    if ( !p->Options.fBinaryMapBounds )
    {
        for ( Bound = Low; Bound <= High; Bound++ )
        {
            vTrial = Fm_CamusMapSolve( p, vCandidates, vMcses, Bound, &Status );
            if ( Status == FM_CAMUS_SAT )
            {
                Vec_IntFree( vBest );
                return vTrial;
            }
            if ( Status != FM_CAMUS_UNSAT )
            {
                Vec_IntFree( vBest );
                return NULL;
            }
        }
        return vBest;
    }
    while ( Low <= High )
    {
        Bound = Low + (High - Low) / 2;
        vTrial = Fm_CamusMapSolve( p, vCandidates, vMcses, Bound, &Status );
        if ( Status == FM_CAMUS_SAT )
        {
            Vec_IntFree( vBest );
            vBest = vTrial;
            High = Bound - 1;
        }
        else if ( Status == FM_CAMUS_UNSAT )
            Low = Bound + 1;
        else
        {
            Vec_IntFree( vBest );
            return NULL;
        }
    }
    return vBest;
}

/**Function*************************************************************

  Synopsis    [Grows a SAT hitting set to an MSS and returns its MCS.]

***********************************************************************/
static Vec_Int_t * Fm_CamusGrowMcs( Fm_CamusMan_t * p, Vec_Int_t * vCandidates, Vec_Int_t * vHit )
{
    Vec_Int_t * vMss = Vec_IntDup( vHit );
    Vec_Int_t * vSelected = Vec_IntStart( p->nGroups );
    Vec_Int_t * vDone = Vec_IntStart( p->nGroups );
    Vec_Int_t * vMcs = NULL;
    int i, k, iGroup, Status, fHaveModel = 1;
    Vec_IntForEachEntry( vMss, iGroup, i )
    {
        Vec_IntWriteEntry( vSelected, iGroup, 1 );
        Vec_IntWriteEntry( vDone, iGroup, 1 );
    }
    while ( 1 )
    {
        if ( fHaveModel && p->Options.fUseModelAbsorb )
        {
            Vec_IntForEachEntry( vCandidates, iGroup, i )
                if ( !Vec_IntEntry(vSelected, iGroup) &&
                     cadical_solver_get_var_value(p->pSat, p->nVars + iGroup) )
                {
                    Vec_IntWriteEntry( vSelected, iGroup, 1 );
                    Vec_IntWriteEntry( vDone, iGroup, 1 );
                    Vec_IntPush( vMss, iGroup );
                    p->Stats.nModelGroupsAdded++;
                }
            fHaveModel = 0;
        }
        Vec_IntForEachEntry( vCandidates, iGroup, i )
            if ( !Vec_IntEntry(vDone, iGroup) )
                break;
        if ( i == Vec_IntSize(vCandidates) )
            break;
        Vec_IntWriteEntry( vSelected, iGroup, 1 );
        Vec_IntWriteEntry( vDone, iGroup, 1 );
        Vec_IntPush( vMss, iGroup );
        p->Stats.nExplicitGroupsTried++;
        p->Stats.nGrowthSolves++;
        Status = Fm_CamusSolve( p, vMss );
        if ( Status == FM_CAMUS_SAT )
            fHaveModel = 1;
        else if ( Status == FM_CAMUS_UNSAT )
        {
            Vec_IntPop( vMss );
            Vec_IntWriteEntry( vSelected, iGroup, 0 );
        }
        else
            goto finish;
    }
    vMcs = Vec_IntAlloc( Vec_IntSize(vCandidates) - Vec_IntSize(vMss) );
    Vec_IntForEachEntry( vCandidates, iGroup, k )
        if ( !Vec_IntEntry(vSelected, iGroup) )
            Vec_IntPush( vMcs, iGroup );

finish:
    Vec_IntFree( vDone );
    Vec_IntFree( vSelected );
    Vec_IntFree( vMss );
    return vMcs;
}

/** Returns a valid (not necessarily minimal) correction set for a SAT set. */
static Vec_Int_t * Fm_CamusMakeCorrectionSet( Fm_CamusMan_t * p,
                                              Vec_Int_t * vCandidates,
                                              Vec_Int_t * vSat )
{
    Vec_Int_t * vSelected = Vec_IntStart( p->nGroups );
    Vec_Int_t * vCorrection = Vec_IntAlloc( Vec_IntSize(vCandidates) - Vec_IntSize(vSat) );
    int i, iGroup;
    Vec_IntForEachEntry( vSat, iGroup, i )
        Vec_IntWriteEntry( vSelected, iGroup, 1 );
    Vec_IntForEachEntry( vCandidates, iGroup, i )
        if ( !Vec_IntEntry(vSelected, iGroup) )
            Vec_IntPush( vCorrection, iGroup );
    Vec_IntFree( vSelected );
    return vCorrection;
}

Vec_Int_t * Fm_CamusFindMinimumMus( Fm_CamusMan_t * p, Vec_Int_t * vEnabled )
{
    Vec_Int_t * vCandidates = NULL, * vBest = NULL, * vHit, * vMcs;
    Vec_Ptr_t * vMcses = NULL;
    abctime clkTotal, clkPhase;
    int i, Status;

    if ( p == NULL )
        return NULL;
    memset( &p->Stats, 0, sizeof(p->Stats) );
    p->Stats.nSeedResult = -1;
    p->Stats.nResult = -1;
    p->Stats.nSolverConstructions = 1;
    clkTotal = Abc_Clock();
    vCandidates = Fm_CamusNormalizeGroups( p, vEnabled );
    if ( vCandidates == NULL )
        goto finish;
    clkPhase = Abc_Clock();
    if ( p->Options.fUseMusSeed )
        vBest = Fm_CamusFindMusInternal( p, vCandidates, p->Options.fMinimizeSeed );
    else
    {
        p->Stats.nSeedInput = Vec_IntSize( vCandidates );
        p->Stats.nSeedSolves++;
        Status = Fm_CamusSolve( p, vCandidates );
        if ( Status == FM_CAMUS_UNSAT )
        {
            vBest = Vec_IntDup( vCandidates );
            p->Stats.nSeedResult = Vec_IntSize( vBest );
        }
    }
    p->Stats.timeSeed += Abc_Clock() - clkPhase;
    if ( vBest == NULL )
        goto finish;
    if ( Vec_IntSize(vBest) == 0 )
        goto finish;
    vMcses = Vec_PtrAlloc( 16 );
    while ( 1 )
    {
        vHit = Fm_CamusMinimumHit( p, vCandidates, vMcses, vBest );
        if ( vHit == NULL )
        {
            Vec_IntFree( vBest );
            vBest = NULL;
            break;
        }
        clkPhase = Abc_Clock();
        p->Stats.nValidationSolves++;
        Status = Fm_CamusSolve( p, vHit );
        p->Stats.timeValidation += Abc_Clock() - clkPhase;
        if ( Status == FM_CAMUS_UNSAT )
        {
            Vec_IntFree( vBest );
            vBest = vHit;
            break;
        }
        if ( Status != FM_CAMUS_SAT )
        {
            Vec_IntFree( vHit );
            Vec_IntFree( vBest );
            vBest = NULL;
            break;
        }
        p->Stats.nRefinements++;
        if ( p->Options.fGrowMcs )
        {
            clkPhase = Abc_Clock();
            vMcs = Fm_CamusGrowMcs( p, vCandidates, vHit );
            p->Stats.timeGrowth += Abc_Clock() - clkPhase;
        }
        else
            vMcs = Fm_CamusMakeCorrectionSet( p, vCandidates, vHit );
        Vec_IntFree( vHit );
        if ( vMcs == NULL || Vec_IntSize(vMcs) == 0 )
        {
            Vec_IntFreeP( &vMcs );
            Vec_IntFree( vBest );
            vBest = NULL;
            break;
        }
        p->Stats.nCorrectionSets++;
        Vec_PtrPush( vMcses, vMcs );
    }

finish:
    if ( vMcses )
    {
        Vec_PtrForEachEntry( Vec_Int_t *, vMcses, vMcs, i )
            Vec_IntFree( vMcs );
        Vec_PtrFree( vMcses );
    }
    Vec_IntFreeP( &vCandidates );
    p->Stats.nResult = vBest == NULL ? -1 : Vec_IntSize( vBest );
    p->Stats.timeTotal = Abc_Clock() - clkTotal;
    return vBest;
}

ABC_NAMESPACE_IMPL_END
