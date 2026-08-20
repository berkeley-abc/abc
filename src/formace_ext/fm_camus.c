/**CFile****************************************************************

  FileName    [fm_camus.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ForMACE CaDiCaL-backed CAMUS-style MUS support.]

  Synopsis    [In-process CaDiCaL-backed guarded constraint-group API.]

***********************************************************************/

#include "fm_camus.h"
#include "sat/cadical/cadicalSolver.h"
#include <stdlib.h>
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
    pOptions->fUseCadicalPlain = 0;
    pOptions->fUseCadicalIlb = 1;
    pOptions->fUseCadicalStableOnly = 0;
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

typedef struct Fm_CamusMap_t_
{
    cadical_solver * pSat;
    Fm_CamusMan_t  * pCamus;
    Vec_Int_t      * vCandidates;
    int              nWidth;
} Fm_CamusMap_t;

/**Function*************************************************************

  Synopsis    [Adds one reusable sequential counter to the map solver.]

  Description [Counter column j represents at least j+1 selected groups.
  An AtMost(Bound) query assumes the negation of the last-row Bound column.]

***********************************************************************/
static int Fm_CamusMapAddCounter( cadical_solver * pSat, Fm_CamusMan_t * p,
                                  Vec_Int_t * vCandidates, int Width )
{
    int Lits[3], i, j, n, Columns, PrevColumns;
    n = Vec_IntSize( vCandidates );
    assert( Width > 0 && Width <= n );
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
    return 1;
}

/**Function*************************************************************

  Synopsis    [Starts one incremental hitting-set map solver.]

***********************************************************************/
static Fm_CamusMap_t * Fm_CamusMapStart( Fm_CamusMan_t * p,
                                         Vec_Int_t * vCandidates, int Width )
{
    abctime clk = Abc_Clock();
    Fm_CamusMap_t * pMap = ABC_CALLOC( Fm_CamusMap_t, 1 );
    if ( pMap == NULL )
        return NULL;
    pMap->pCamus = p;
    pMap->vCandidates = vCandidates;
    pMap->nWidth = Width;
    pMap->pSat = cadical_solver_new();
    p->Stats.nSolverConstructions++;
    if ( pMap->pSat == NULL ||
         (p->Options.fUseCadicalTuning && p->Options.fUseCadicalPlain &&
          !cadical_solver_configure(pMap->pSat, "plain")) ||
         (p->Options.fUseCadicalTuning && p->Options.fUseCadicalIlb &&
          !cadical_solver_set_option(pMap->pSat, "ilb", 2)) ||
         (p->Options.fUseCadicalTuning && p->Options.fUseCadicalStableOnly &&
          !cadical_solver_set_option(pMap->pSat, "stabilizeonly", 1)) ||
         !cadical_solver_set_option(pMap->pSat, "phase", 0) ||
         !cadical_solver_set_option(pMap->pSat, "forcephase", 1) ||
         !cadical_solver_set_option(pMap->pSat, "checkassumptions", 0) ||
         !cadical_solver_set_option(pMap->pSat, "checkconstraint", 0) ||
         !cadical_solver_set_option(pMap->pSat, "checkfailed", 0) )
        goto fail;
    cadical_solver_set_runtime_limit( pMap->pSat, p->nTimeOut );
    cadical_solver_setnvars( pMap->pSat,
        p->nGroups + Vec_IntSize(vCandidates) * Width );
    if ( !Fm_CamusMapAddCounter(pMap->pSat, p, vCandidates, Width) )
        goto fail;
    p->Stats.timeMap += Abc_Clock() - clk;
    return pMap;

fail:
    if ( pMap->pSat )
        cadical_solver_delete( pMap->pSat );
    ABC_FREE( pMap );
    p->Stats.timeMap += Abc_Clock() - clk;
    return NULL;
}

static void Fm_CamusMapStop( Fm_CamusMap_t * pMap )
{
    if ( pMap == NULL )
        return;
    cadical_solver_delete( pMap->pSat );
    ABC_FREE( pMap );
}

/** Adds one newly discovered correction-set clause to the persistent map. */
static int Fm_CamusMapAddMcs( Fm_CamusMap_t * pMap, Vec_Int_t * vMcs )
{
    abctime clk = Abc_Clock();
    int * pClause = ABC_ALLOC( int, Vec_IntSize(vMcs) );
    int i, iGroup, RetValue;
    Vec_IntForEachEntry( vMcs, iGroup, i )
        pClause[i] = Abc_Var2Lit( iGroup, 0 );
    RetValue = cadical_solver_addclause( pMap->pSat,
        pClause, pClause + Vec_IntSize(vMcs) );
    ABC_FREE( pClause );
    pMap->pCamus->Stats.timeMap += Abc_Clock() - clk;
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Solves one bounded query in the incremental map solver.]

***********************************************************************/
static Vec_Int_t * Fm_CamusMapSolve( Fm_CamusMap_t * pMap,
                                     int Bound, int * pStatus )
{
    Fm_CamusMan_t * p = pMap->pCamus;
    Vec_Int_t * vResult = NULL;
    abctime clk = Abc_Clock();
    int i, iGroup, Lit, RetValue;
    assert( Bound >= 0 && Bound < pMap->nWidth );
    Lit = Abc_Var2Lit( p->nGroups +
        (Vec_IntSize(pMap->vCandidates) - 1) * pMap->nWidth + Bound, 1 );
    p->Stats.nMapSolves++;
    RetValue = cadical_solver_solve( pMap->pSat, &Lit, &Lit + 1,
        p->nConfLimit, 0, 0, 0 );
    if ( RetValue == FM_CAMUS_SAT )
    {
        vResult = Vec_IntAlloc( Bound );
        Vec_IntForEachEntry( pMap->vCandidates, iGroup, i )
            if ( cadical_solver_get_var_value(pMap->pSat, iGroup) )
                Vec_IntPush( vResult, iGroup );
    }
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
static Vec_Int_t * Fm_CamusMinimumHit( Fm_CamusMan_t * p, Fm_CamusMap_t * pMap,
                                      Vec_Int_t * vUpper, int * pLower )
{
    Vec_Int_t * vBest = Vec_IntSize(pMap->vCandidates) < Vec_IntSize(vUpper) ?
        Vec_IntDup(pMap->vCandidates) : Vec_IntDup(vUpper);
    Vec_Int_t * vTrial;
    int Low = *pLower;
    int High = Vec_IntSize(vBest) - 1;
    int Bound, Status;
    if ( !p->Options.fBinaryMapBounds )
    {
        for ( Bound = Low; Bound <= High; Bound++ )
        {
            vTrial = Fm_CamusMapSolve( pMap, Bound, &Status );
            if ( Status == FM_CAMUS_SAT )
            {
                Vec_IntFree( vBest );
                *pLower = Vec_IntSize( vTrial );
                return vTrial;
            }
            if ( Status != FM_CAMUS_UNSAT )
            {
                Vec_IntFree( vBest );
                return NULL;
            }
        }
        *pLower = Vec_IntSize( vBest );
        return vBest;
    }
    while ( Low <= High )
    {
        Bound = Low + (High - Low) / 2;
        vTrial = Fm_CamusMapSolve( pMap, Bound, &Status );
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
    *pLower = Vec_IntSize( vBest );
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

/** Returns true iff sorted set A is a subset of sorted set B. */
static int Fm_CamusSetIsSubset( Vec_Int_t * vA, Vec_Int_t * vB )
{
    int i = 0, k = 0;
    while ( i < Vec_IntSize(vA) && k < Vec_IntSize(vB) )
    {
        int A = Vec_IntEntry( vA, i );
        int B = Vec_IntEntry( vB, k );
        if ( A == B )
            i++, k++;
        else if ( A > B )
            k++;
        else
            return 0;
    }
    return i == Vec_IntSize(vA);
}

/**
 * Inserts one correction set into the inclusion-minimal antichain.
 * Supersets are redundant hitting-set clauses and are removed from the
 * canonical collection.  Clauses already present in a persistent SAT map do
 * not need deletion: once a subset is added, every removed clause is implied.
 */
static int Fm_CamusRememberMcs( Vec_Ptr_t * vMcses, Vec_Int_t * vMcs,
                                int * pnSubsumed )
{
    Vec_Int_t * vStored;
    int i;
    Vec_IntSort( vMcs, 0 );
    Vec_PtrForEachEntry( Vec_Int_t *, vMcses, vStored, i )
        if ( Fm_CamusSetIsSubset(vStored, vMcs) )
        {
            if ( pnSubsumed )
                (*pnSubsumed)++;
            return 0;
        }
    for ( i = Vec_PtrSize(vMcses) - 1; i >= 0; i-- )
    {
        vStored = (Vec_Int_t *)Vec_PtrEntry( vMcses, i );
        if ( Fm_CamusSetIsSubset(vMcs, vStored) )
        {
            Vec_IntFree( vStored );
            Vec_PtrDrop( vMcses, i );
            if ( pnSubsumed )
                (*pnSubsumed)++;
        }
    }
    Vec_PtrPush( vMcses, Vec_IntDup(vMcs) );
    return 1;
}

typedef struct Fm_CamusPackItem_t_
{
    int      Index;
    unsigned Key;
} Fm_CamusPackItem_t;

static int Fm_CamusPackItemCompare( const void * pA, const void * pB )
{
    const Fm_CamusPackItem_t * pItemA = (const Fm_CamusPackItem_t *)pA;
    const Fm_CamusPackItem_t * pItemB = (const Fm_CamusPackItem_t *)pB;
    if ( pItemA->Key < pItemB->Key )
        return -1;
    if ( pItemA->Key > pItemB->Key )
        return 1;
    return pItemA->Index - pItemB->Index;
}

/**
 * Returns a certified hitting-set lower bound: the largest pairwise-disjoint
 * correction-set packing found by deterministic multi-start greedy orders.
 * Every accepted packing is a proof, even though the maximum packing itself
 * is not computed exactly.
 */
static int Fm_CamusDisjointLower( Vec_Ptr_t * vMcses, int nGroups,
                                  int nAttempts )
{
    Fm_CamusPackItem_t * pItems;
    unsigned char * pUsed;
    Vec_Int_t * vMcs;
    int Attempt, i, k, iGroup, nPack, nBest = 0;
    int nMcses = Vec_PtrSize( vMcses );
    if ( nMcses == 0 || nGroups == 0 )
        return 0;
    pItems = ABC_ALLOC( Fm_CamusPackItem_t, nMcses );
    pUsed = ABC_CALLOC( unsigned char, nGroups );
    if ( pItems == NULL || pUsed == NULL )
    {
        ABC_FREE( pItems );
        ABC_FREE( pUsed );
        return 0;
    }
    for ( Attempt = 0; Attempt < nAttempts; Attempt++ )
    {
        memset( pUsed, 0, (size_t)nGroups );
        Vec_PtrForEachEntry( Vec_Int_t *, vMcses, vMcs, i )
        {
            unsigned Hash = (unsigned)(i + 1) * 2654435761u ^
                            (unsigned)(Attempt + 1) * 2246822519u;
            pItems[i].Index = i;
            pItems[i].Key = Attempt == 0 ? (unsigned)Vec_IntSize(vMcs) :
                (unsigned)Vec_IntSize(vMcs) * 256u + (Hash & 1023u);
        }
        qsort( pItems, (size_t)nMcses, sizeof(Fm_CamusPackItem_t),
               Fm_CamusPackItemCompare );
        nPack = 0;
        for ( i = 0; i < nMcses; i++ )
        {
            vMcs = (Vec_Int_t *)Vec_PtrEntry( vMcses, pItems[i].Index );
            Vec_IntForEachEntry( vMcs, iGroup, k )
                if ( pUsed[iGroup] )
                    break;
            if ( k < Vec_IntSize(vMcs) )
                continue;
            Vec_IntForEachEntry( vMcs, iGroup, k )
                pUsed[iGroup] = 1;
            nPack++;
        }
        nBest = Abc_MaxInt( nBest, nPack );
    }
    ABC_FREE( pItems );
    ABC_FREE( pUsed );
    return nBest;
}

Vec_Int_t * Fm_CamusFindMinimumMus( Fm_CamusMan_t * p, Vec_Int_t * vEnabled )
{
    Vec_Int_t * vCandidates = NULL, * vBest = NULL, * vHit, * vMcs;
    Vec_Int_t * vDisjoint = NULL;
    Vec_Ptr_t * vMcses = NULL;
    Fm_CamusMap_t * pMap = NULL;
    abctime clkTotal, clkPhase;
    int MapLower = 0, Status;

    if ( p == NULL )
        return NULL;
    memset( &p->Stats, 0, sizeof(p->Stats) );
    p->Stats.nSeedResult = -1;
    p->Stats.nResult = -1;
    p->Stats.nSolverConstructions = 1;
    clkTotal = Abc_Clock();
    vCandidates = Fm_CamusNormalizeGroups( p, vEnabled );
    vMcses = Vec_PtrAlloc( 128 );
    if ( vCandidates == NULL || vMcses == NULL )
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
    pMap = Fm_CamusMapStart( p, vCandidates, Vec_IntSize(vBest) );
    if ( pMap == NULL )
    {
        Vec_IntFree( vBest );
        vBest = NULL;
        goto finish;
    }

    // Enumerate a greedy maximal family of pairwise-disjoint MCSes before the
    // main SMUS loop.  Their count is a certified lower bound and their clauses
    // immediately bootstrap the persistent map solver.
    vDisjoint = Vec_IntAlloc( p->nGroups );
    while ( p->Stats.nDisjointLower < Vec_IntSize(vBest) )
    {
        int nSubsumed = 0;
        clkPhase = Abc_Clock();
        p->Stats.nGrowthSolves++;
        Status = Fm_CamusSolve( p, vDisjoint );
        p->Stats.timeGrowth += Abc_Clock() - clkPhase;
        if ( Status == FM_CAMUS_UNSAT )
            break;
        if ( Status != FM_CAMUS_SAT )
            goto bootstrap_fail;
        clkPhase = Abc_Clock();
        vMcs = p->Options.fGrowMcs ?
            Fm_CamusGrowMcs( p, vCandidates, vDisjoint ) :
            Fm_CamusMakeCorrectionSet( p, vCandidates, vDisjoint );
        p->Stats.timeGrowth += Abc_Clock() - clkPhase;
        if ( vMcs == NULL || Vec_IntSize(vMcs) == 0 )
        {
            Vec_IntFreeP( &vMcs );
            goto bootstrap_fail;
        }
        if ( !Fm_CamusRememberMcs(vMcses, vMcs, &nSubsumed) ||
             !Fm_CamusMapAddMcs(pMap, vMcs) )
        {
            p->Stats.nCorrectionSetsSubsumed += nSubsumed;
            Vec_IntFree( vMcs );
            goto bootstrap_fail;
        }
        p->Stats.nCorrectionSets++;
        p->Stats.nCorrectionSetsSubsumed += nSubsumed;
        Vec_IntAppend( vDisjoint, vMcs );
        Vec_IntFree( vMcs );
        p->Stats.nDisjointLower++;
    }
    MapLower = p->Stats.nDisjointLower;
    Vec_IntFreeP( &vDisjoint );
    while ( 1 )
    {
        vHit = Fm_CamusMinimumHit( p, pMap, vBest, &MapLower );
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
        {
            int nSubsumed = 0;
            if ( !Fm_CamusRememberMcs(vMcses, vMcs, &nSubsumed) )
            {
                p->Stats.nCorrectionSetsSubsumed += nSubsumed;
                Vec_IntFree( vMcs );
                Vec_IntFree( vBest );
                vBest = NULL;
                break;
            }
            p->Stats.nCorrectionSets++;
            p->Stats.nCorrectionSetsSubsumed += nSubsumed;
        }
        if ( !Fm_CamusMapAddMcs(pMap, vMcs) )
        {
            Vec_IntFree( vMcs );
            Vec_IntFree( vBest );
            vBest = NULL;
            break;
        }
        Vec_IntFree( vMcs );
        p->Stats.nDisjointLower = Abc_MaxInt( p->Stats.nDisjointLower,
            Fm_CamusDisjointLower(vMcses, p->nGroups, 8) );
        MapLower = Abc_MaxInt( MapLower, p->Stats.nDisjointLower );
    }
    goto finish;

bootstrap_fail:
    Vec_IntFreeP( &vBest );

finish:
    Fm_CamusMapStop( pMap );
    Vec_IntFreeP( &vCandidates );
    Vec_IntFreeP( &vDisjoint );
    if ( vMcses )
    {
        Vec_Int_t * vStored;
        Vec_PtrForEachEntry( Vec_Int_t *, vMcses, vStored, Status )
            Vec_IntFree( vStored );
        Vec_PtrFree( vMcses );
    }
    p->Stats.nResult = vBest == NULL ? -1 : Vec_IntSize( vBest );
    p->Stats.timeTotal = Abc_Clock() - clkTotal;
    return vBest;
}

/** Returns true iff vEnabled is UNSAT in every manager. */
static int Fm_CamusSolveAll( Fm_CamusMan_t ** ppMans, int nMans,
    Vec_Int_t * vEnabled, Fm_CamusMan_t ** ppSatMan, int * piSatMan )
{
    int i, Status;
    if ( ppSatMan )
        *ppSatMan = NULL;
    if ( piSatMan )
        *piSatMan = -1;
    for ( i = 0; i < nMans; i++ )
    {
        Status = Fm_CamusSolve( ppMans[i], vEnabled );
        if ( Status == FM_CAMUS_SAT )
        {
            if ( ppSatMan )
                *ppSatMan = ppMans[i];
            if ( piSatMan )
                *piSatMan = i;
            return 0;
        }
        if ( Status != FM_CAMUS_UNSAT )
            return -1;
    }
    return 1;
}

/**
 * Grows a set that is SAT in at least one manager to an MSS of the combined
 * OR oracle.  The satisfying branch may change during growth.  Its complement
 * is therefore a correction set for (B_0 OR ... OR B_k) AND Eq_S.
 */
static Vec_Int_t * Fm_CamusGrowCommonMcs( Fm_CamusMan_t * p,
    Fm_CamusMan_t ** ppMans, int nMans, Vec_Int_t * vCandidates,
    Vec_Int_t * vHit )
{
    Vec_Int_t * vMss = Vec_IntDup( vHit );
    Vec_Int_t * vSelected = Vec_IntStart( p->nGroups );
    Vec_Int_t * vDone = Vec_IntStart( p->nGroups );
    Vec_Int_t * vMcs = NULL;
    Fm_CamusMan_t * pSatMan = NULL;
    int i, k, iGroup, Status, fHaveModel = 0;
    Vec_IntForEachEntry( vMss, iGroup, i )
    {
        Vec_IntWriteEntry( vSelected, iGroup, 1 );
        Vec_IntWriteEntry( vDone, iGroup, 1 );
    }
    p->Stats.nGrowthSolves++;
    Status = Fm_CamusSolveAll( ppMans, nMans, vMss, &pSatMan, NULL );
    if ( Status != 0 )
        goto finish;
    fHaveModel = 1;
    while ( 1 )
    {
        if ( fHaveModel && p->Options.fUseModelAbsorb )
        {
            Vec_IntForEachEntry( vCandidates, iGroup, i )
                if ( !Vec_IntEntry(vSelected, iGroup) &&
                     cadical_solver_get_var_value(pSatMan->pSat,
                         pSatMan->nVars + iGroup) )
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
        Status = Fm_CamusSolveAll( ppMans, nMans, vMss, &pSatMan, NULL );
        if ( Status == 0 )
            fHaveModel = 1;
        else if ( Status == 1 )
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

/** Returns a deterministic alternative growth order for MCS diversification. */
static Vec_Int_t * Fm_CamusGrowthOrder( Vec_Int_t * vCandidates,
    int iPass, int iMan )
{
    Vec_Int_t * vOrder = Vec_IntAlloc( Vec_IntSize(vCandidates) );
    int i, n = Vec_IntSize( vCandidates );
    int Offset = n ? ((iPass / 2) * Abc_MaxInt(1, n / 4) + 37 * iMan) % n : 0;
    for ( i = 0; i < n; i++ )
    {
        int Index = (iPass & 1) ? (Offset + n - i) % n : (Offset + i) % n;
        Vec_IntPush( vOrder, Vec_IntEntry(vCandidates, Index) );
    }
    return vOrder;
}

/**
 * Returns one divisor representative per distinct nonzero correction-set
 * incidence pattern.  The quotient is rebuilt after every refinement, so a
 * new correction set can split classes that were previously equivalent.
 */
static Vec_Int_t * Fm_CamusMapRepresentatives( Fm_CamusMan_t * p,
    Vec_Int_t * vCandidates, Vec_Ptr_t * vMcses )
{
    Vec_Int_t * vResult = Vec_IntAlloc( Vec_IntSize(vCandidates) );
    Vec_Int_t * vTable;
    Vec_Int_t * vMcs;
    unsigned char * pSigs;
    int i, k, iGroup, iMcs, nBytes, nTable = 1;
    if ( Vec_PtrSize(vMcses) == 0 )
        return vResult;
    nBytes = (Vec_PtrSize(vMcses) + 7) / 8;
    pSigs = ABC_CALLOC( unsigned char, p->nGroups * nBytes );
    if ( pSigs == NULL )
    {
        Vec_IntFree( vResult );
        return NULL;
    }
    Vec_PtrForEachEntry( Vec_Int_t *, vMcses, vMcs, iMcs )
        Vec_IntForEachEntry( vMcs, iGroup, k )
            pSigs[iGroup * nBytes + iMcs / 8] |= (unsigned char)(1u << (iMcs & 7));
    while ( nTable < 2 * Vec_IntSize(vCandidates) )
        nTable <<= 1;
    vTable = Vec_IntStartFull( nTable );
    Vec_IntForEachEntry( vCandidates, iGroup, i )
    {
        unsigned char * pSig = pSigs + iGroup * nBytes;
        unsigned Hash = 2166136261u;
        int j, Slot, iOther;
        for ( j = 0; j < nBytes; j++ )
            Hash = (Hash ^ pSig[j]) * 16777619u;
        for ( j = 0; j < nBytes && pSig[j] == 0; j++ ) {}
        if ( j == nBytes )
            continue;
        Slot = (int)(Hash & (unsigned)(nTable - 1));
        while ( (iOther = Vec_IntEntry(vTable, Slot)) >= 0 )
        {
            if ( !memcmp(pSig, pSigs + iOther * nBytes, (size_t)nBytes) )
                break;
            Slot = (Slot + 1) & (nTable - 1);
        }
        if ( iOther >= 0 )
            continue;
        Vec_IntWriteEntry( vTable, Slot, iGroup );
        Vec_IntPush( vResult, iGroup );
    }
    // A pattern whose learned-clause coverage is a strict subset of another
    // pattern is dynamically dominated.  Replacing it by the superset
    // representative never increases the size of a current hitting set.  The
    // test is recomputed after every new MCS, so future distinctions are kept.
    {
        Vec_Int_t * vKeep = Vec_IntStartFull( Vec_IntSize(vResult) );
        int a, b, iGroupA, iGroupB, nKeep = 0;
        Vec_IntFill( vKeep, Vec_IntSize(vResult), 1 );
        Vec_IntForEachEntry( vResult, iGroupA, a )
        {
            unsigned char * pSigA = pSigs + iGroupA * nBytes;
            Vec_IntForEachEntry( vResult, iGroupB, b )
            {
                unsigned char * pSigB;
                int Byte;
                if ( a == b )
                    continue;
                pSigB = pSigs + iGroupB * nBytes;
                for ( Byte = 0; Byte < nBytes; Byte++ )
                    if ( pSigA[Byte] & (unsigned char)~pSigB[Byte] )
                        break;
                if ( Byte == nBytes )
                {
                    Vec_IntWriteEntry( vKeep, a, 0 );
                    break;
                }
            }
        }
        Vec_IntForEachEntry( vResult, iGroup, i )
            if ( Vec_IntEntry(vKeep, i) )
                Vec_IntWriteEntry( vResult, nKeep++, iGroup );
        Vec_IntShrink( vResult, nKeep );
        Vec_IntFree( vKeep );
    }
    Vec_IntFree( vTable );
    ABC_FREE( pSigs );
    return vResult;
}

/**
 * Heuristically finds a hitting set at an already-proven lower bound.  The
 * result is used only when it hits every learned MCS; otherwise the exact map
 * solver remains responsible for finding a candidate or raising the bound.
 */
static Vec_Int_t * Fm_CamusGreedyLowerHit( Fm_CamusMan_t * p,
    Vec_Int_t * vRepresentatives, Vec_Ptr_t * vMcses, int Bound,
    unsigned Seed )
{
    Vec_Int_t * vResult = NULL;
    Vec_Int_t * vRepMap = NULL;
    Vec_Int_t * vMcs;
    unsigned char * pIncidence = NULL;
    unsigned char * pCovered = NULL;
    unsigned char * pSelected = NULL;
    int i, k, iMcs, iGroup, nReps = Vec_IntSize(vRepresentatives);
    int nMcses = Vec_PtrSize(vMcses), nCovered = 0, Attempt;
    int nAttempts = Bound >= 6 ? 4096 : 64;
    if ( Bound <= 0 || nReps == 0 || nMcses == 0 )
        return NULL;
    vResult = Vec_IntAlloc( Bound );
    vRepMap = Vec_IntStartFull( p->nGroups );
    pIncidence = ABC_CALLOC( unsigned char, nReps * nMcses );
    pCovered = ABC_CALLOC( unsigned char, nMcses );
    pSelected = ABC_CALLOC( unsigned char, nReps );
    if ( vResult == NULL || vRepMap == NULL || pIncidence == NULL ||
         pCovered == NULL || pSelected == NULL )
        goto fail;
    Vec_IntForEachEntry( vRepresentatives, iGroup, i )
        Vec_IntWriteEntry( vRepMap, iGroup, i );
    Vec_PtrForEachEntry( Vec_Int_t *, vMcses, vMcs, iMcs )
        Vec_IntForEachEntry( vMcs, iGroup, k )
        {
            int iRep = Vec_IntEntry( vRepMap, iGroup );
            if ( iRep >= 0 )
                pIncidence[iRep * nMcses + iMcs] = 1;
        }
    for ( Attempt = 0; Attempt < nAttempts; Attempt++ )
    {
        Vec_IntClear( vResult );
        memset( pCovered, 0, (size_t)nMcses );
        memset( pSelected, 0, (size_t)nReps );
        nCovered = 0;
        while ( Vec_IntSize(vResult) < Bound && nCovered < nMcses )
        {
            int iBest = -1, BestCount = -1;
            unsigned BestScore = 0;
            for ( i = 0; i < nReps; i++ )
            {
                int Count = 0;
                unsigned Tie, Score;
                if ( pSelected[i] )
                    continue;
                for ( iMcs = 0; iMcs < nMcses; iMcs++ )
                    Count += !pCovered[iMcs] && pIncidence[i * nMcses + iMcs];
                Tie = ((unsigned)Vec_IntEntry(vRepresentatives, i) * 2654435761u) ^
                      (Seed + 2246822519u * (unsigned)Vec_IntSize(vResult) +
                       3266489917u * (unsigned)Attempt);
                Score = (unsigned)Count * (Attempt ? 1024u : 2048u) +
                        (Tie & (Attempt ? 2047u : 1023u));
                if ( iBest < 0 || Score > BestScore )
                    iBest = i, BestCount = Count, BestScore = Score;
            }
            if ( iBest < 0 || BestCount <= 0 )
                break;
            pSelected[iBest] = 1;
            Vec_IntPush( vResult, Vec_IntEntry(vRepresentatives, iBest) );
            for ( iMcs = 0; iMcs < nMcses; iMcs++ )
                if ( !pCovered[iMcs] && pIncidence[iBest * nMcses + iMcs] )
                    pCovered[iMcs] = 1, nCovered++;
        }
        if ( nCovered == nMcses && Vec_IntSize(vResult) == Bound )
            break;
    }
    if ( nCovered != nMcses || Vec_IntSize(vResult) != Bound )
        Vec_IntFreeP( &vResult );
    else
        Vec_IntSort( vResult, 0 );
    goto finish;

fail:
    Vec_IntFreeP( &vResult );

finish:
    Vec_IntFreeP( &vRepMap );
    ABC_FREE( pIncidence );
    ABC_FREE( pCovered );
    ABC_FREE( pSelected );
    return vResult;
}

/** Tries direct and bounded local-search repairs at the proven lower bound. */
static Vec_Int_t * Fm_CamusRepairLowerHit( Fm_CamusMan_t * p,
    Vec_Int_t * vCandidates, Vec_Ptr_t * vMcses, Vec_Int_t * vPrevious,
    int Bound )
{
    Vec_Int_t * vMcs;
    Vec_Int_t * vResult = NULL;
    unsigned char * pIncidence = NULL;
    unsigned char * pSelected = NULL;
    int * pHitCounts = NULL;
    word * pSignatures = NULL, * pNeed = NULL;
    int i, j, k, m, iMcs, iGroup, iAdd, nMcses = Vec_PtrSize(vMcses);
    int nWords = (nMcses + 63) / 64;
    if ( vPrevious == NULL || Vec_IntSize(vPrevious) != Bound || Bound <= 0 )
        return NULL;
    pIncidence = ABC_CALLOC( unsigned char, p->nGroups * nMcses );
    pSelected = ABC_CALLOC( unsigned char, p->nGroups );
    pHitCounts = ABC_CALLOC( int, nMcses );
    pSignatures = ABC_CALLOC( word, p->nGroups * nWords );
    pNeed = ABC_CALLOC( word, nWords );
    if ( pIncidence == NULL || pSelected == NULL || pHitCounts == NULL ||
         pSignatures == NULL || pNeed == NULL )
        goto finish;
    Vec_PtrForEachEntry( Vec_Int_t *, vMcses, vMcs, iMcs )
        Vec_IntForEachEntry( vMcs, iGroup, k )
        {
            pIncidence[iGroup * nMcses + iMcs] = 1;
            pSignatures[iGroup * nWords + iMcs / 64] |= (word)1 << (iMcs & 63);
        }
    Vec_IntForEachEntry( vPrevious, iGroup, i )
    {
        pSelected[iGroup] = 1;
        for ( iMcs = 0; iMcs < nMcses; iMcs++ )
            pHitCounts[iMcs] += pIncidence[iGroup * nMcses + iMcs];
    }
    Vec_IntForEachEntry( vPrevious, iGroup, i )
        Vec_IntForEachEntry( vCandidates, iAdd, k )
        {
            if ( pSelected[iAdd] )
                continue;
            for ( iMcs = 0; iMcs < nMcses; iMcs++ )
                if ( pHitCounts[iMcs] - pIncidence[iGroup * nMcses + iMcs] +
                     pIncidence[iAdd * nMcses + iMcs] <= 0 )
                    break;
            if ( iMcs < nMcses )
                continue;
            vResult = Vec_IntDup( vPrevious );
            Vec_IntWriteEntry( vResult, i, iAdd );
            Vec_IntSort( vResult, 0 );
            goto finish;
        }
    // If one replacement is insufficient, search two removals/two additions
    // using packed learned-MCS incidence signatures.
    for ( i = 0; i < Vec_IntSize(vPrevious); i++ )
        for ( j = i + 1; j < Vec_IntSize(vPrevious); j++ )
        {
            int iRemove0 = Vec_IntEntry( vPrevious, i );
            int iRemove1 = Vec_IntEntry( vPrevious, j );
            memset( pNeed, 0, sizeof(word) * (size_t)nWords );
            for ( iMcs = 0; iMcs < nMcses; iMcs++ )
                if ( pHitCounts[iMcs] - pIncidence[iRemove0 * nMcses + iMcs] -
                     pIncidence[iRemove1 * nMcses + iMcs] <= 0 )
                    pNeed[iMcs / 64] |= (word)1 << (iMcs & 63);
            Vec_IntForEachEntry( vCandidates, iAdd, k )
            {
                int iAdd1;
                if ( pSelected[iAdd] )
                    continue;
                Vec_IntForEachEntryStart( vCandidates, iAdd1, m, k + 1 )
                {
                    if ( pSelected[iAdd1] )
                        continue;
                    for ( iMcs = 0; iMcs < nWords; iMcs++ )
                        if ( pNeed[iMcs] &
                             ~(pSignatures[iAdd * nWords + iMcs] |
                               pSignatures[iAdd1 * nWords + iMcs]) )
                            break;
                    if ( iMcs < nWords )
                        continue;
                    vResult = Vec_IntDup( vPrevious );
                    Vec_IntWriteEntry( vResult, i, iAdd );
                    Vec_IntWriteEntry( vResult, j, iAdd1 );
                    Vec_IntSort( vResult, 0 );
                    goto finish;
                }
            }
        }

    // Direct one/two swaps only accept a move that solves the whole hitting
    // problem immediately.  When several corrections interact, walk through
    // intermediate size-Bound sets instead.  Every returned set is checked by
    // the maintained exact hit counts; failure simply falls back to the map.
    {
        Vec_Int_t * vWalk = Vec_IntDup( vPrevious );
        int Restart, Step;
        for ( Restart = 0; Restart < 8 && vResult == NULL; Restart++ )
        {
            memset( pSelected, 0, (size_t)p->nGroups );
            memset( pHitCounts, 0, sizeof(int) * (size_t)nMcses );
            Vec_IntClear( vWalk );
            Vec_IntAppend( vWalk, vPrevious );
            Vec_IntForEachEntry( vWalk, iGroup, i )
            {
                pSelected[iGroup] = 1;
                for ( iMcs = 0; iMcs < nMcses; iMcs++ )
                    pHitCounts[iMcs] += pIncidence[iGroup * nMcses + iMcs];
            }
            for ( Step = 0; Step < 4096; Step++ )
            {
                Vec_Int_t * vUncovered;
                int iChosenMcs, nUncovered = 0;
                int iBestAdd = -1, iBestRemovePos = -1;
                int BestMake = -1, BestBreak = nMcses + 1;
                unsigned BestTie = 0;
                for ( iMcs = 0; iMcs < nMcses; iMcs++ )
                    nUncovered += pHitCounts[iMcs] == 0;
                if ( nUncovered == 0 )
                {
                    vResult = Vec_IntDup( vWalk );
                    Vec_IntSort( vResult, 0 );
                    break;
                }
                iChosenMcs = (int)(((unsigned)Step * 2654435761u +
                    (unsigned)Restart * 2246822519u) % (unsigned)nUncovered);
                for ( iMcs = 0, k = 0; iMcs < nMcses; iMcs++ )
                    if ( pHitCounts[iMcs] == 0 && k++ == iChosenMcs )
                        break;
                vUncovered = (Vec_Int_t *)Vec_PtrEntry( vMcses, iMcs );

                Vec_IntForEachEntry( vUncovered, iAdd, k )
                {
                    int Make = 0;
                    unsigned Tie;
                    if ( pSelected[iAdd] )
                        continue;
                    for ( iMcs = 0; iMcs < nMcses; iMcs++ )
                        Make += pHitCounts[iMcs] == 0 &&
                                pIncidence[iAdd * nMcses + iMcs];
                    Tie = (unsigned)iAdd * 3266489917u ^
                          (unsigned)(Step + 1) * 668265263u ^
                          (unsigned)(Restart + 1) * 374761393u;
                    if ( (Step & 15) == 15 )
                        Make = 0;
                    if ( iBestAdd < 0 || Make > BestMake ||
                         (Make == BestMake && Tie > BestTie) )
                        iBestAdd = iAdd, BestMake = Make, BestTie = Tie;
                }
                if ( iBestAdd < 0 )
                    break;

                BestTie = 0;
                Vec_IntForEachEntry( vWalk, iGroup, i )
                {
                    int Break = 0;
                    unsigned Tie = (unsigned)iGroup * 2654435761u ^
                                   (unsigned)(Step + Restart + 1) * 2246822519u;
                    for ( iMcs = 0; iMcs < nMcses; iMcs++ )
                        Break += pHitCounts[iMcs] -
                                 pIncidence[iGroup * nMcses + iMcs] +
                                 pIncidence[iBestAdd * nMcses + iMcs] == 0;
                    if ( (Step & 31) == 31 )
                        Break = (int)(Tie & 7u);
                    if ( iBestRemovePos < 0 || Break < BestBreak ||
                         (Break == BestBreak && Tie > BestTie) )
                        iBestRemovePos = i, BestBreak = Break, BestTie = Tie;
                }
                iGroup = Vec_IntEntry( vWalk, iBestRemovePos );
                pSelected[iGroup] = 0;
                pSelected[iBestAdd] = 1;
                Vec_IntWriteEntry( vWalk, iBestRemovePos, iBestAdd );
                for ( iMcs = 0; iMcs < nMcses; iMcs++ )
                    pHitCounts[iMcs] +=
                        pIncidence[iBestAdd * nMcses + iMcs] -
                        pIncidence[iGroup * nMcses + iMcs];
            }
        }
        Vec_IntFree( vWalk );
    }

finish:
    ABC_FREE( pIncidence );
    ABC_FREE( pSelected );
    ABC_FREE( pHitCounts );
    ABC_FREE( pSignatures );
    ABC_FREE( pNeed );
    return vResult;
}

Vec_Int_t * Fm_CamusFindMinimumCommonMus( Fm_CamusMan_t ** ppMans,
    int nMans, Vec_Int_t * vCandidatesIn, Vec_Int_t * vSeedCommon,
    int fVerbose )
{
    Fm_CamusMan_t * p;
    Fm_CamusMap_t * pMap = NULL;
    Vec_Int_t * vCandidates = NULL, * vBest = NULL, * vHit, * vMcs;
    Vec_Int_t * vSatMans = NULL;
    Vec_Int_t * vMapCandidates = NULL;
    Vec_Int_t * vPreviousHit = NULL, * vDisjoint = NULL;
    Vec_Ptr_t * vMcses = NULL;
    abctime clkTotal, clkPhase;
    int i, k, m, iGroup, iSatMan, nHit = 0, MapLower = 0, Status;

    if ( ppMans == NULL || nMans <= 0 || ppMans[0] == NULL )
        return NULL;
    p = ppMans[0];
    for ( i = 1; i < nMans; i++ )
        if ( ppMans[i] == NULL || ppMans[i]->nGroups != p->nGroups )
            return NULL;
    memset( &p->Stats, 0, sizeof(p->Stats) );
    p->Stats.nSeedResult = -1;
    p->Stats.nResult = -1;
    p->Stats.nSolverConstructions = nMans;
    clkTotal = Abc_Clock();
    vCandidates = Fm_CamusNormalizeGroups( p, vCandidatesIn );
    vBest = Fm_CamusNormalizeGroups( p, vSeedCommon );
    vSatMans = Vec_IntAlloc( nMans );
    vMcses = Vec_PtrAlloc( 128 );
    if ( vCandidates == NULL || vBest == NULL || vSatMans == NULL || vMcses == NULL )
        goto fail;
    p->Stats.nSeedInput = Vec_IntSize( vBest );
    clkPhase = Abc_Clock();
    p->Stats.nSeedSolves++;
    Status = Fm_CamusSolveAll( ppMans, nMans, vBest, NULL, NULL );
    if ( Status != 1 )
        goto fail;

    // Deletion-minimize the supplied common upper bound.  The expected seed
    // is the small support union from the reference trajectory, not the full
    // candidate universe.
    for ( i = 0; i < Vec_IntSize(vBest); )
    {
        iGroup = Vec_IntEntry( vBest, i );
        Vec_IntDrop( vBest, i );
        p->Stats.nSeedSolves++;
        Status = Fm_CamusSolveAll( ppMans, nMans, vBest, NULL, NULL );
        if ( Status == 1 )
            continue;
        if ( Status < 0 )
            goto fail;
        Vec_IntInsert( vBest, i, iGroup );
        i++;
    }
    p->Stats.nSeedResult = Vec_IntSize( vBest );
    p->Stats.timeSeed += Abc_Clock() - clkPhase;
    if ( Vec_IntSize(vBest) == 0 )
        goto finish;

    // Bootstrap the hitting-set lower bound with pairwise-disjoint correction
    // sets, as proposed for SMUS extraction.  vDisjoint is mandatory during
    // each global grow, so every newly returned complement is disjoint from
    // all preceding complements.
    vDisjoint = Vec_IntAlloc( p->nGroups );
    while ( Vec_PtrSize(vMcses) < Vec_IntSize(vBest) )
    {
        int nSubsumed = 0;
        clkPhase = Abc_Clock();
        p->Stats.nGrowthSolves++;
        Status = Fm_CamusSolveAll( ppMans, nMans, vDisjoint, NULL, NULL );
        p->Stats.timeGrowth += Abc_Clock() - clkPhase;
        if ( Status == 1 )
            break;
        if ( Status < 0 )
            goto fail;
        clkPhase = Abc_Clock();
        vMcs = Fm_CamusGrowCommonMcs( p, ppMans, nMans,
                                      vCandidates, vDisjoint );
        p->Stats.timeGrowth += Abc_Clock() - clkPhase;
        if ( vMcs == NULL || Vec_IntSize(vMcs) == 0 )
        {
            Vec_IntFreeP( &vMcs );
            goto fail;
        }
        if ( !Fm_CamusRememberMcs(vMcses, vMcs, &nSubsumed) )
        {
            p->Stats.nCorrectionSetsSubsumed += nSubsumed;
            Vec_IntFree( vMcs );
            goto fail;
        }
        p->Stats.nCorrectionSets++;
        p->Stats.nCorrectionSetsSubsumed += nSubsumed;
        Vec_IntAppend( vDisjoint, vMcs );
        Vec_IntFree( vMcs );
    }
    p->Stats.nDisjointLower = Vec_PtrSize( vMcses );
    MapLower = p->Stats.nDisjointLower;
    Vec_IntFreeP( &vDisjoint );
    while ( 1 )
    {
        int nCorrectionMin = p->nGroups + 1;
        int nCorrectionMax = 0;
        int nLearned = 0;
        int nGrowthPasses;
        int CandidateSource = 0;
        Fm_CamusMapStop( pMap );
        pMap = NULL;
        Vec_IntFreeP( &vMapCandidates );
        vMapCandidates = Fm_CamusMapRepresentatives( p, vCandidates, vMcses );
        if ( vMapCandidates == NULL )
            goto fail;
        if ( Vec_PtrSize(vMcses) == 0 )
            vHit = Vec_IntAlloc( 0 );
        else
        {
            Vec_Int_t * vStored;
            Vec_Int_t * vRepBits = Vec_IntStart( p->nGroups );
            int iStored;
            int iRep, iLit;
            int Width = Abc_MinInt( Vec_IntSize(vBest), Vec_IntSize(vMapCandidates) );
            if ( Width <= 0 )
            {
                Vec_IntFree( vRepBits );
                goto fail;
            }
            Vec_IntForEachEntry( vMapCandidates, iRep, iStored )
                Vec_IntWriteEntry( vRepBits, iRep, 1 );
            vHit = Fm_CamusRepairLowerHit( p, vCandidates, vMcses,
                vPreviousHit, MapLower );
            if ( vHit )
                CandidateSource = 2;
            else
                vHit = Fm_CamusGreedyLowerHit( p, vMapCandidates, vMcses,
                    MapLower, (unsigned)p->Stats.nRefinements + 1u );
            if ( vHit && CandidateSource == 0 )
                CandidateSource = 1;
            if ( vHit == NULL )
            {
                pMap = Fm_CamusMapStart( p, vMapCandidates, Width );
                if ( pMap == NULL )
                {
                    Vec_IntFree( vRepBits );
                    goto fail;
                }
                Vec_PtrForEachEntry( Vec_Int_t *, vMcses, vStored, iStored )
                {
                    Vec_Int_t * vQuotient = Vec_IntAlloc( Vec_IntSize(vStored) );
                    Vec_IntForEachEntry( vStored, iLit, iRep )
                        if ( Vec_IntEntry(vRepBits, iLit) )
                            Vec_IntPush( vQuotient, iLit );
                    if ( Vec_IntSize(vQuotient) == 0 ||
                         !Fm_CamusMapAddMcs(pMap, vQuotient) )
                    {
                        Vec_IntFree( vQuotient );
                        Vec_IntFree( vRepBits );
                        goto fail;
                    }
                    Vec_IntFree( vQuotient );
                }
                vHit = Fm_CamusMinimumHit( p, pMap, vBest, &MapLower );
                if ( vHit == NULL )
                {
                    Vec_IntFree( vRepBits );
                    goto fail;
                }
            }
            Vec_IntFree( vRepBits );
        }
        clkPhase = Abc_Clock();
        p->Stats.nValidationSolves++;
        Vec_IntClear( vSatMans );
        Status = 1;
        for ( i = 0; i < nMans; i++ )
        {
            int StatusOne = Fm_CamusSolve( ppMans[i], vHit );
            if ( StatusOne == FM_CAMUS_SAT )
            {
                Vec_IntPush( vSatMans, i );
                Status = 0;
            }
            else if ( StatusOne != FM_CAMUS_UNSAT )
            {
                Status = -1;
                break;
            }
        }
        p->Stats.timeValidation += Abc_Clock() - clkPhase;
        if ( Status == 1 )
        {
            Vec_IntFree( vBest );
            vBest = vHit;
            break;
        }
        if ( Status < 0 || Vec_IntSize(vSatMans) == 0 )
        {
            Vec_IntFree( vHit );
            goto fail;
        }
        p->Stats.nRefinements++;
        nHit = Vec_IntSize( vHit );
        Vec_IntFreeP( &vPreviousHit );
        vPreviousHit = Vec_IntDup( vHit );
        nGrowthPasses = nMans > 1 && Vec_IntSize(vCandidates) > 100 ? 2 : 1;

        // Learn one correction set from the combined OR oracle before the
        // branch-local batch.  Global growth can switch its satisfying target
        // while adding equalities and often yields a stronger constraint than
        // committing to one initially SAT branch.
        if ( nMans > 1 )
        {
            int nSubsumed = 0;
            clkPhase = Abc_Clock();
            vMcs = Fm_CamusGrowCommonMcs( p, ppMans, nMans,
                                          vCandidates, vHit );
            p->Stats.timeGrowth += Abc_Clock() - clkPhase;
            if ( vMcs == NULL || Vec_IntSize(vMcs) == 0 )
            {
                Vec_IntFreeP( &vMcs );
                Vec_IntFree( vHit );
                goto fail;
            }
            nCorrectionMin = Abc_MinInt( nCorrectionMin, Vec_IntSize(vMcs) );
            nCorrectionMax = Abc_MaxInt( nCorrectionMax, Vec_IntSize(vMcs) );
            if ( Fm_CamusRememberMcs(vMcses, vMcs, &nSubsumed) )
            {
                p->Stats.nCorrectionSets++;
                nLearned++;
            }
            p->Stats.nCorrectionSetsSubsumed += nSubsumed;
            Vec_IntFree( vMcs );
        }
        Vec_IntForEachEntry( vSatMans, iSatMan, k )
        {
            Fm_CamusMan_t * pSatMan = ppMans[iSatMan];
            for ( m = 0; m < nGrowthPasses; m++ )
            {
                Vec_Int_t * vGrowCandidates = vCandidates;
                ABC_INT64_T nGrowthSolves = pSatMan->Stats.nGrowthSolves;
                ABC_INT64_T nExplicit = pSatMan->Stats.nExplicitGroupsTried;
                ABC_INT64_T nModel = pSatMan->Stats.nModelGroupsAdded;
                if ( m )
                {
                    if ( Fm_CamusSolve(pSatMan, vHit) != FM_CAMUS_SAT )
                    {
                        Vec_IntFree( vHit );
                        goto fail;
                    }
                    vGrowCandidates = Fm_CamusGrowthOrder( vCandidates, m, iSatMan );
                }
                clkPhase = Abc_Clock();
                vMcs = p->Options.fGrowMcs ?
                    Fm_CamusGrowMcs( pSatMan, vGrowCandidates, vHit ) :
                    Fm_CamusMakeCorrectionSet( pSatMan, vGrowCandidates, vHit );
                p->Stats.timeGrowth += Abc_Clock() - clkPhase;
                if ( m )
                    Vec_IntFree( vGrowCandidates );
                if ( pSatMan != p )
                {
                    p->Stats.nGrowthSolves += pSatMan->Stats.nGrowthSolves - nGrowthSolves;
                    p->Stats.nExplicitGroupsTried += pSatMan->Stats.nExplicitGroupsTried - nExplicit;
                    p->Stats.nModelGroupsAdded += pSatMan->Stats.nModelGroupsAdded - nModel;
                }
                if ( vMcs == NULL || Vec_IntSize(vMcs) == 0 )
                {
                    Vec_IntFreeP( &vMcs );
                    Vec_IntFree( vHit );
                    goto fail;
                }
                nCorrectionMin = Abc_MinInt( nCorrectionMin, Vec_IntSize(vMcs) );
                nCorrectionMax = Abc_MaxInt( nCorrectionMax, Vec_IntSize(vMcs) );
                {
                    int nSubsumed = 0;
                    if ( !Fm_CamusRememberMcs(vMcses, vMcs, &nSubsumed) )
                    {
                        p->Stats.nCorrectionSetsSubsumed += nSubsumed;
                        Vec_IntFree( vMcs );
                        continue;
                    }
                    p->Stats.nCorrectionSetsSubsumed += nSubsumed;
                }
                p->Stats.nCorrectionSets++;
                nLearned++;
                Vec_IntFree( vMcs );
            }
        }
        Vec_IntFree( vHit );
        p->Stats.nDisjointLower = Abc_MaxInt( p->Stats.nDisjointLower,
            Fm_CamusDisjointLower(vMcses, p->nGroups, 64) );
        MapLower = Abc_MaxInt( MapLower, p->Stats.nDisjointLower );
        if ( fVerbose )
        {
            printf( "ForMACE common CAMUS refinement %lld: lower=%d packing=%d upper=%d candidate=%d source=%s map_classes=%d sat_targets=%d learned=%d active_corrections=%d corrections=%d..%d map=%.6f validation=%.6f growth=%.6f seconds.\n",
                (long long)p->Stats.nRefinements, MapLower,
                p->Stats.nDisjointLower, Vec_IntSize(vBest), nHit,
                CandidateSource == 2 ? "repair-lower" :
                      (CandidateSource == 1 ? "greedy-lower" : "exact-map"),
                Vec_IntSize(vMapCandidates), Vec_IntSize(vSatMans), nLearned,
                Vec_PtrSize(vMcses), nCorrectionMin, nCorrectionMax,
                (double)p->Stats.timeMap / (double)CLOCKS_PER_SEC,
                (double)p->Stats.timeValidation / (double)CLOCKS_PER_SEC,
                (double)p->Stats.timeGrowth / (double)CLOCKS_PER_SEC );
            fflush( stdout );
        }
    }
    goto finish;

fail:
    Vec_IntFreeP( &vBest );

finish:
    Fm_CamusMapStop( pMap );
    Vec_IntFreeP( &vCandidates );
    Vec_IntFreeP( &vSatMans );
    Vec_IntFreeP( &vMapCandidates );
    Vec_IntFreeP( &vPreviousHit );
    Vec_IntFreeP( &vDisjoint );
    if ( vMcses )
    {
        Vec_Int_t * vStored;
        Vec_PtrForEachEntry( Vec_Int_t *, vMcses, vStored, i )
            Vec_IntFree( vStored );
        Vec_PtrFree( vMcses );
    }
    p->Stats.nResult = vBest == NULL ? -1 : Vec_IntSize( vBest );
    p->Stats.timeTotal = Abc_Clock() - clkTotal;
    return vBest;
}

ABC_NAMESPACE_IMPL_END
