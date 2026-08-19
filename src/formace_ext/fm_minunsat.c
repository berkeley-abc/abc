#define _GNU_SOURCE

/**CFile****************************************************************

  FileName    [fm_minunsat.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ForMACE minimum-UNSAT shell command.]

  Synopsis    [Reads DIMACS CNF and computes an exact minimum UNSAT set.]

***********************************************************************/

#include "fm_minunsat.h"
#include "fm_camus.h"
#include "base/main/mainInt.h"
#include "misc/extra/extra.h"
#include <ctype.h>
#include <errno.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

ABC_NAMESPACE_IMPL_START

typedef struct Fm_MinUnsatCnf_t_
{
    int         nVars;
    int         nClauses;
    Vec_Int_t * vOffsets;
    Vec_Int_t * vLits;
} Fm_MinUnsatCnf_t;

static void Fm_MinUnsatCnfFree( Fm_MinUnsatCnf_t * p )
{
    if ( p == NULL )
        return;
    Vec_IntFreeP( &p->vOffsets );
    Vec_IntFreeP( &p->vLits );
    ABC_FREE( p );
}

/** Reads general token-oriented DIMACS, including clauses split across lines. */
static Fm_MinUnsatCnf_t * Fm_MinUnsatCnfRead( FILE * pErr, const char * pFileName )
{
    Fm_MinUnsatCnf_t * p = NULL;
    FILE * pFile = fopen( pFileName, "r" );
    Vec_Int_t * vOffsets = NULL, * vLits = NULL;
    char * pLine = NULL, * pCur, * pEnd;
    char Type[16], Extra;
    size_t nCap = 0;
    long nVars = -1, nClauses = -1, Lit;
    int iLine = 0, fHeader = 0, fClauseOpen = 0, nScan;
    if ( pFile == NULL )
    {
        fprintf( pErr, "fm_minunsat: cannot open CNF file \"%s\".\n", pFileName );
        return NULL;
    }
    while ( getline(&pLine, &nCap, pFile) >= 0 )
    {
        iLine++;
        pCur = pLine;
        while ( isspace((unsigned char)*pCur) )
            pCur++;
        if ( *pCur == '\0' || *pCur == 'c' )
            continue;
        if ( *pCur == 'p' )
        {
            nScan = sscanf( pCur, "p %15s %ld %ld %c", Type, &nVars, &nClauses, &Extra );
            if ( fHeader || nScan != 3 || strcmp(Type, "cnf") ||
                 nVars < 0 || nVars > INT_MAX || nClauses < 0 || nClauses > INT_MAX )
            {
                fprintf( pErr, "fm_minunsat: invalid DIMACS header at %s:%d.\n", pFileName, iLine );
                goto fail;
            }
            fHeader = 1;
            vOffsets = Vec_IntAlloc( (int)nClauses + 1 );
            vLits = Vec_IntAlloc( (int)nClauses );
            Vec_IntPush( vOffsets, 0 );
            continue;
        }
        if ( !fHeader )
        {
            fprintf( pErr, "fm_minunsat: clause data precedes the DIMACS header at %s:%d.\n", pFileName, iLine );
            goto fail;
        }
        while ( *pCur )
        {
            while ( isspace((unsigned char)*pCur) )
                pCur++;
            if ( *pCur == '\0' )
                break;
            errno = 0;
            Lit = strtol( pCur, &pEnd, 10 );
            if ( pEnd == pCur || errno == ERANGE || Lit < -nVars || Lit > nVars )
            {
                fprintf( pErr, "fm_minunsat: invalid literal at %s:%d.\n", pFileName, iLine );
                goto fail;
            }
            pCur = pEnd;
            if ( Lit == 0 )
            {
                Vec_IntPush( vOffsets, Vec_IntSize(vLits) );
                fClauseOpen = 0;
                if ( Vec_IntSize(vOffsets) - 1 > nClauses )
                {
                    fprintf( pErr, "fm_minunsat: CNF contains more than %ld declared clauses.\n", nClauses );
                    goto fail;
                }
            }
            else
            {
                Vec_IntPush( vLits, Abc_Var2Lit((int)(Lit < 0 ? -Lit : Lit) - 1, Lit < 0) );
                fClauseOpen = 1;
            }
        }
    }
    if ( !fHeader )
    {
        fprintf( pErr, "fm_minunsat: no DIMACS 'p cnf' header in \"%s\".\n", pFileName );
        goto fail;
    }
    if ( fClauseOpen )
    {
        fprintf( pErr, "fm_minunsat: final DIMACS clause has no zero terminator.\n" );
        goto fail;
    }
    if ( Vec_IntSize(vOffsets) - 1 != nClauses )
    {
        fprintf( pErr, "fm_minunsat: CNF declares %ld clauses but contains %d.\n",
                 nClauses, Vec_IntSize(vOffsets) - 1 );
        goto fail;
    }
    p = ABC_CALLOC( Fm_MinUnsatCnf_t, 1 );
    p->nVars = (int)nVars;
    p->nClauses = (int)nClauses;
    p->vOffsets = vOffsets;
    p->vLits = vLits;
    free( pLine );
    fclose( pFile );
    return p;

fail:
    free( pLine );
    fclose( pFile );
    Vec_IntFreeP( &vOffsets );
    Vec_IntFreeP( &vLits );
    return NULL;
}

/** One data line is one group; the first data line is hard/background. */
static int * Fm_MinUnsatGroupsRead( FILE * pErr, const char * pFileName,
                                    int nClauses, int * pnGroups, int * pnHard )
{
    FILE * pFile = fopen( pFileName, "r" );
    char * pLine = NULL, * pCur, * pEnd;
    size_t nCap = 0;
    int * pGroups;
    int i, iLine = 0, iGroup = 0, nEntries, fEmpty;
    long iClause;
    if ( pFile == NULL )
    {
        fprintf( pErr, "fm_minunsat: cannot open group file \"%s\".\n", pFileName );
        return NULL;
    }
    pGroups = ABC_ALLOC( int, nClauses );
    for ( i = 0; i < nClauses; i++ )
        pGroups[i] = -1;
    while ( getline(&pLine, &nCap, pFile) >= 0 )
    {
        iLine++;
        pCur = pLine;
        while ( isspace((unsigned char)*pCur) )
            pCur++;
        if ( *pCur == '\0' || *pCur == 'c' || *pCur == '#' )
            continue;
        nEntries = 0;
        fEmpty = 0;
        while ( *pCur )
        {
            while ( isspace((unsigned char)*pCur) )
                pCur++;
            if ( *pCur == '\0' )
                break;
            errno = 0;
            iClause = strtol( pCur, &pEnd, 10 );
            if ( pEnd == pCur || errno == ERANGE || iClause < 0 || iClause > nClauses )
            {
                fprintf( pErr, "fm_minunsat: invalid clause ID at %s:%d.\n", pFileName, iLine );
                goto fail;
            }
            pCur = pEnd;
            if ( iClause == 0 )
            {
                if ( nEntries != 0 || fEmpty )
                {
                    fprintf( pErr, "fm_minunsat: 0 must be the only entry on a group line (%s:%d).\n", pFileName, iLine );
                    goto fail;
                }
                fEmpty = 1;
            }
            else
            {
                if ( fEmpty || pGroups[iClause - 1] != -1 )
                {
                    fprintf( pErr, "fm_minunsat: duplicate or mixed clause ID at %s:%d.\n", pFileName, iLine );
                    goto fail;
                }
                pGroups[iClause - 1] = iGroup;
                nEntries++;
            }
        }
        iGroup++;
    }
    if ( iGroup == 0 )
    {
        fprintf( pErr, "fm_minunsat: group file has no groups.\n" );
        goto fail;
    }
    for ( i = 0; i < nClauses; i++ )
        if ( pGroups[i] < 0 )
        {
            fprintf( pErr, "fm_minunsat: clause %d is not assigned to a group.\n", i + 1 );
            goto fail;
        }
    *pnGroups = iGroup;
    *pnHard = 0;
    for ( i = 0; i < nClauses; i++ )
        *pnHard += pGroups[i] == 0;
    free( pLine );
    fclose( pFile );
    return pGroups;

fail:
    free( pLine );
    fclose( pFile );
    ABC_FREE( pGroups );
    return NULL;
}

static int Fm_MinUnsatLoad( Fm_CamusMan_t * pMan, Fm_MinUnsatCnf_t * pCnf,
                            int * pGroups, int fGrouped )
{
    int i, Beg, End, * pLits;
    for ( i = 0; i < pCnf->nClauses; i++ )
    {
        Beg = Vec_IntEntry( pCnf->vOffsets, i );
        End = Vec_IntEntry( pCnf->vOffsets, i + 1 );
        pLits = End > Beg ? Vec_IntArray(pCnf->vLits) + Beg : NULL;
        if ( fGrouped && pGroups[i] == 0 )
        {
            if ( !Fm_CamusAddBackground(pMan, pLits, End - Beg) )
                return 0;
        }
        else if ( !Fm_CamusAddGroup(pMan, fGrouped ? pGroups[i] - 1 : i, pLits, End - Beg) )
            return 0;
    }
    return 1;
}

static int Fm_MinUnsatParseLimit( const char * pText, ABC_INT64_T * pValue )
{
    char * pEnd;
    long long Value;
    errno = 0;
    Value = strtoll( pText, &pEnd, 10 );
    if ( errno == ERANGE || pEnd == pText || *pEnd != '\0' || Value < 0 )
        return 0;
    *pValue = (ABC_INT64_T)Value;
    return 1;
}

static int Fm_MinUnsatSelectVariant( const char * pName, Fm_CamusOptions_t * pOptions )
{
    Fm_CamusOptionsDefault( pOptions );
    if ( !strcmp(pName, "full") )
        return 1;
    if ( !strcmp(pName, "no-core-shrink") )
        pOptions->fUseCoreShrink = 0;
    else if ( !strcmp(pName, "no-mus-seed") )
        pOptions->fUseMusSeed = 0;
    else if ( !strcmp(pName, "core-only-seed") )
        pOptions->fMinimizeSeed = 0;
    else if ( !strcmp(pName, "no-model-absorb") )
        pOptions->fUseModelAbsorb = 0;
    else if ( !strcmp(pName, "no-mss-growth") )
        pOptions->fGrowMcs = 0;
    else if ( !strcmp(pName, "linear-map-bounds") )
        pOptions->fBinaryMapBounds = 0;
    else if ( !strcmp(pName, "default-cadical") )
    {
        pOptions->fUseCadicalTuning = 0;
        pOptions->fUseCadicalPlain = 0;
        pOptions->fUseCadicalIlb = 0;
        pOptions->fUseCadicalStableOnly = 0;
    }
    else if ( !strcmp(pName, "cadical-preprocessing") )
        pOptions->fUseCadicalPlain = 0;
    else if ( !strcmp(pName, "cadical-no-ilb") )
        pOptions->fUseCadicalIlb = 0;
    else if ( !strcmp(pName, "cadical-default-phases") )
        pOptions->fUseCadicalStableOnly = 0;
    else if ( !strcmp(pName, "cadical-preprocessing-no-ilb") )
    {
        pOptions->fUseCadicalPlain = 0;
        pOptions->fUseCadicalIlb = 0;
    }
    else if ( !strcmp(pName, "cadical-preprocessing-default-phases") )
    {
        pOptions->fUseCadicalPlain = 0;
        pOptions->fUseCadicalStableOnly = 0;
    }
    else if ( !strcmp(pName, "cadical-no-ilb-default-phases") )
    {
        pOptions->fUseCadicalIlb = 0;
        pOptions->fUseCadicalStableOnly = 0;
    }
    else
        return 0;
    return 1;
}

static const char * Fm_MinUnsatSeedName( const char * pVariant )
{
    if ( !strcmp(pVariant, "core-only-seed") )
        return "raw-core";
    if ( !strcmp(pVariant, "no-mus-seed") )
        return "all-candidates";
    return "deletion-minimized-mus";
}

static void Fm_MinUnsatPrintStats( FILE * pOut, Fm_CamusMan_t * pMan )
{
    Fm_CamusStats_t Stats;
    Fm_CamusGetStats( pMan, &Stats );
    fprintf( pOut,
             "fm_minunsat stats: seconds=%.6f seed=%d->%d seed_solves=%lld "
             "map_solves=%lld validation_solves=%lld growth_solves=%lld refinements=%lld\n",
             (double)Stats.timeTotal / (double)CLOCKS_PER_SEC,
             Stats.nSeedInput, Stats.nSeedResult, (long long)Stats.nSeedSolves,
             (long long)Stats.nMapSolves, (long long)Stats.nValidationSolves,
             (long long)Stats.nGrowthSolves, (long long)Stats.nRefinements );
}

static void Fm_MinUnsatPrintJson( FILE * pOut, Fm_CamusMan_t * pMan,
                                  const char * pVariant, const char * pMode,
                                  Fm_MinUnsatCnf_t * pCnf, int nHard, int nGroups,
                                  Vec_Int_t * vMinimum, Fm_CamusOptions_t * pOptions )
{
    Fm_CamusStats_t Stats;
    int i, Entry;
    Fm_CamusGetStats( pMan, &Stats );
    fprintf( pOut,
             "{\"backend\":\"%s\",\"variant\":\"%s\","
             "\"seed_strategy\":\"%s\",\"status\":\"ok\","
             "\"mode\":\"%s\",\"variables\":%d,\"clauses\":%d,"
             "\"hard_clauses\":%d,\"candidates\":%d,\"minimum\":%d,\"selected\":[",
             Fm_CamusBackendName(), pVariant, Fm_MinUnsatSeedName(pVariant), pMode,
             pCnf->nVars, pCnf->nClauses, nHard, nGroups, Vec_IntSize(vMinimum) );
    Vec_IntForEachEntry( vMinimum, Entry, i )
        fprintf( pOut, "%s%d", i ? "," : "", Entry + 1 );
    fprintf( pOut,
             "],\"features\":{\"core_shrink\":%d,\"mus_seed\":%d,"
             "\"minimize_seed\":%d,\"model_absorb\":%d,\"mss_growth\":%d,"
             "\"binary_map_bounds\":%d,\"cadical_tuning\":%d,"
             "\"cadical_plain\":%d,\"cadical_ilb\":%d,"
             "\"cadical_stable_only\":%d},\"stats\":{"
             "\"total_seconds\":%.6f,\"seed_seconds\":%.6f,"
             "\"map_seconds\":%.6f,\"validation_seconds\":%.6f,"
             "\"growth_seconds\":%.6f,\"seed_input\":%d,\"seed_result\":%d,"
             "\"seed_solves\":%lld,\"map_solves\":%lld,\"map_sat\":%lld,"
             "\"map_unsat\":%lld,\"validation_solves\":%lld,"
             "\"growth_solves\":%lld,\"refinements\":%lld,"
             "\"correction_sets\":%lld,\"core_shrinks\":%lld,"
             "\"core_groups_removed\":%lld,\"model_groups_added\":%lld,"
             "\"explicit_groups_tried\":%lld,\"solver_constructions\":%lld}}\n",
             pOptions->fUseCoreShrink, pOptions->fUseMusSeed,
             pOptions->fMinimizeSeed, pOptions->fUseModelAbsorb,
             pOptions->fGrowMcs, pOptions->fBinaryMapBounds,
             pOptions->fUseCadicalTuning,
             pOptions->fUseCadicalTuning && pOptions->fUseCadicalPlain,
             pOptions->fUseCadicalTuning && pOptions->fUseCadicalIlb,
             pOptions->fUseCadicalTuning && pOptions->fUseCadicalStableOnly,
             (double)Stats.timeTotal / (double)CLOCKS_PER_SEC,
             (double)Stats.timeSeed / (double)CLOCKS_PER_SEC,
             (double)Stats.timeMap / (double)CLOCKS_PER_SEC,
             (double)Stats.timeValidation / (double)CLOCKS_PER_SEC,
             (double)Stats.timeGrowth / (double)CLOCKS_PER_SEC,
             Stats.nSeedInput, Stats.nSeedResult,
             (long long)Stats.nSeedSolves, (long long)Stats.nMapSolves,
             (long long)Stats.nMapSat, (long long)Stats.nMapUnsat,
             (long long)Stats.nValidationSolves, (long long)Stats.nGrowthSolves,
             (long long)Stats.nRefinements, (long long)Stats.nCorrectionSets,
             (long long)Stats.nCoreShrinks, (long long)Stats.nCoreGroupsRemoved,
             (long long)Stats.nModelGroupsAdded, (long long)Stats.nExplicitGroupsTried,
             (long long)Stats.nSolverConstructions );
}

int Fm_CommandMinUnsat( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Fm_MinUnsatCnf_t * pCnf = NULL;
    Fm_CamusMan_t * pMan = NULL;
    Fm_CamusOptions_t Options;
    Vec_Int_t * vAll = NULL, * vMinimum = NULL;
    const char * pGroupFile = NULL, * pCnfFile, * pVariant = "full";
    int * pGroups = NULL;
    ABC_INT64_T nConfLimit = 0, nSeconds = 0;
    abctime nDeadline = 0;
    int c, i, Entry, nGroupLines = 0, nGroups = 0, nHard = 0;
    int fRawCore = 0, fNoSeed = 0, fVerbose = 0, fJson = 0, fVariantSet = 0;
    int Status, RetValue = 1;

    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "g:A:C:T:rujvh")) != EOF )
    {
        switch ( c )
        {
        case 'g': pGroupFile = globalUtilOptarg; break;
        case 'A': pVariant = globalUtilOptarg; fVariantSet = 1; break;
        case 'C':
            if ( !Fm_MinUnsatParseLimit(globalUtilOptarg, &nConfLimit) )
                goto usage;
            break;
        case 'T':
            if ( !Fm_MinUnsatParseLimit(globalUtilOptarg, &nSeconds) || nSeconds > INT_MAX )
                goto usage;
            break;
        case 'r': fRawCore ^= 1; break;
        case 'u': fNoSeed ^= 1; break;
        case 'j': fJson ^= 1; break;
        case 'v': fVerbose ^= 1; break;
        case 'h': goto usage;
        default: goto usage;
        }
    }
    if ( argc != globalUtilOptind + 1 || fRawCore + fNoSeed + fVariantSet > 1 )
        goto usage;
    if ( fRawCore )
        pVariant = "core-only-seed";
    else if ( fNoSeed )
        pVariant = "no-mus-seed";
    if ( !Fm_MinUnsatSelectVariant(pVariant, &Options) )
    {
        fprintf( pAbc->Err, "fm_minunsat: unknown ablation variant \"%s\".\n", pVariant );
        goto usage;
    }
    pCnfFile = argv[globalUtilOptind];
    pCnf = Fm_MinUnsatCnfRead( pAbc->Err, pCnfFile );
    if ( pCnf == NULL )
        goto finish;
    if ( pGroupFile )
    {
        pGroups = Fm_MinUnsatGroupsRead( pAbc->Err, pGroupFile, pCnf->nClauses,
                                         &nGroupLines, &nHard );
        if ( pGroups == NULL )
            goto finish;
        nGroups = nGroupLines - 1;
    }
    else
        nGroups = pCnf->nClauses;

    pMan = Fm_CamusStartWithOptions( pCnf->nVars, nGroups, &Options );
    if ( pMan == NULL || !Fm_MinUnsatLoad(pMan, pCnf, pGroups, pGroupFile != NULL) )
    {
        fprintf( pAbc->Err, "fm_minunsat: failed to construct the grouped SAT instance.\n" );
        goto finish;
    }
    if ( nSeconds )
        nDeadline = Abc_Clock() + (abctime)nSeconds * CLOCKS_PER_SEC;
    Fm_CamusSetLimits( pMan, nConfLimit, nDeadline );
    vAll = Vec_IntStartNatural( nGroups );
    Status = Fm_CamusSolve( pMan, vAll );
    if ( Status == 1 )
    {
        if ( fJson )
            fprintf( pAbc->Out, "{\"variant\":\"%s\",\"status\":\"sat-input\"}\n", pVariant );
        else
            fprintf( pAbc->Err, "fm_minunsat: status=SAT; no UNSAT subset exists.\n" );
        goto finish;
    }
    if ( Status != -1 )
    {
        if ( fJson )
            fprintf( pAbc->Out, "{\"variant\":\"%s\",\"status\":\"unknown\"}\n", pVariant );
        else
            fprintf( pAbc->Err, "fm_minunsat: status=UNKNOWN; resource limit reached or solver failed.\n" );
        goto finish;
    }
    vMinimum = Fm_CamusFindMinimumMus( pMan, vAll );
    if ( vMinimum == NULL )
    {
        if ( fJson )
            fprintf( pAbc->Out, "{\"variant\":\"%s\",\"status\":\"unknown\"}\n", pVariant );
        else
            fprintf( pAbc->Err, "fm_minunsat: exact search failed or reached a resource limit.\n" );
        goto finish;
    }
    if ( fJson )
        Fm_MinUnsatPrintJson( pAbc->Out, pMan, pVariant,
                              pGroupFile ? "groups" : "clauses",
                              pCnf, nHard, nGroups, vMinimum, &Options );
    else
    {
        fprintf( pAbc->Out,
                 "fm_minunsat: status=UNSAT mode=%s vars=%d clauses=%d hard=%d candidates=%d minimum=%d backend=%s\n",
                 pGroupFile ? "groups" : "clauses", pCnf->nVars, pCnf->nClauses,
                 nHard, nGroups, Vec_IntSize(vMinimum), Fm_CamusBackendName() );
        fprintf( pAbc->Out, "%s=", pGroupFile ? "selected_groups" : "selected_clauses" );
        Vec_IntForEachEntry( vMinimum, Entry, i )
            fprintf( pAbc->Out, "%s%d", i ? " " : "", Entry + 1 );
        fprintf( pAbc->Out, "\n" );
    }
    if ( fVerbose && !fJson )
        Fm_MinUnsatPrintStats( pAbc->Out, pMan );
    RetValue = 0;

finish:
    Vec_IntFreeP( &vMinimum );
    Vec_IntFreeP( &vAll );
    Fm_CamusStop( pMan );
    Fm_MinUnsatCnfFree( pCnf );
    ABC_FREE( pGroups );
    return RetValue;

usage:
    fprintf( pAbc->Err, "usage: fm_minunsat [-g groups_file] [-A variant] [-C conflicts] [-T seconds] [-rujvh] input.cnf\n" );
    fprintf( pAbc->Err, "\t-g file : group clauses; first data line is hard, remaining lines are optional\n" );
    fprintf( pAbc->Err, "\t-A name : ablation variant: full, no-core-shrink, no-mus-seed, core-only-seed,\n" );
    fprintf( pAbc->Err, "\t          no-model-absorb, no-mss-growth, linear-map-bounds, default-cadical,\n" );
    fprintf( pAbc->Err, "\t          cadical-preprocessing, cadical-no-ilb, or cadical-default-phases\n" );
    fprintf( pAbc->Err, "\t          plus pairwise cadical-preprocessing-no-ilb,\n" );
    fprintf( pAbc->Err, "\t          cadical-preprocessing-default-phases, and cadical-no-ilb-default-phases\n" );
    fprintf( pAbc->Err, "\t-C num  : conflict limit for each SAT query [default = unlimited]\n" );
    fprintf( pAbc->Err, "\t-T num  : total wall-clock limit in seconds [default = unlimited]\n" );
    fprintf( pAbc->Err, "\t-r      : use the raw UNSAT core as the initial upper bound\n" );
    fprintf( pAbc->Err, "\t-u      : use all candidates as the initial upper bound\n" );
    fprintf( pAbc->Err, "\t-j      : print one machine-readable JSON result\n" );
    fprintf( pAbc->Err, "\t-v      : print search statistics\n" );
    fprintf( pAbc->Err, "\t-h      : print this command usage\n" );
    fprintf( pAbc->Err, "Without -g, every DIMACS clause is one optional unit-cost group.\n" );
    return 1;
}

ABC_NAMESPACE_IMPL_END
