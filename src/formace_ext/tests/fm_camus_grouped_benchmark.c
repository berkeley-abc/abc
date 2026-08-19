#define _GNU_SOURCE

#include "formace_ext/fm_camus.h"
#include <ctype.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int Fm_ReadHeader( const char * pFileName, int * pnVars, int * pnClauses )
{
    FILE * pFile = fopen( pFileName, "r" );
    char * pLine = NULL;
    size_t nCap = 0;
    int RetValue = 0;
    if ( pFile == NULL )
        return 0;
    while ( getline(&pLine, &nCap, pFile) >= 0 )
        if ( sscanf(pLine, "p cnf %d %d", pnVars, pnClauses) == 2 )
        {
            RetValue = *pnVars >= 0 && *pnClauses >= 0;
            break;
        }
    free( pLine );
    fclose( pFile );
    return RetValue;
}

static int * Fm_ReadGroups( const char * pFileName, int nClauses, int * pnGroups )
{
    FILE * pFile = fopen( pFileName, "r" );
    char * pLine = NULL, * pCur, * pEnd;
    size_t nCap = 0;
    int * pGroups, i, iGroup = 0;
    long iClause;
    if ( pFile == NULL )
        return NULL;
    pGroups = ABC_ALLOC( int, nClauses );
    for ( i = 0; i < nClauses; i++ )
        pGroups[i] = -1;
    while ( getline(&pLine, &nCap, pFile) >= 0 )
    {
        pCur = pLine;
        while ( isspace((unsigned char)*pCur) )
            pCur++;
        if ( *pCur == '\0' || *pCur == 'c' )
            continue;
        while ( *pCur )
        {
            errno = 0;
            iClause = strtol( pCur, &pEnd, 10 );
            if ( pEnd == pCur )
            {
                if ( isspace((unsigned char)*pCur) )
                {
                    pCur++;
                    continue;
                }
                goto fail;
            }
            if ( errno || iClause <= 0 || iClause > nClauses || pGroups[iClause - 1] != -1 )
                goto fail;
            pGroups[iClause - 1] = iGroup;
            pCur = pEnd;
        }
        iGroup++;
    }
    for ( i = 0; i < nClauses; i++ )
        if ( pGroups[i] < 0 )
            goto fail;
    free( pLine );
    fclose( pFile );
    *pnGroups = iGroup;
    return pGroups;

fail:
    free( pLine );
    fclose( pFile );
    ABC_FREE( pGroups );
    return NULL;
}

static int Fm_LoadCnf( Fm_CamusMan_t * p, const char * pFileName, int * pGroups, int nVars, int nClauses )
{
    FILE * pFile = fopen( pFileName, "r" );
    Vec_Int_t * vLits = Vec_IntAlloc( 16 );
    char * pLine = NULL, * pCur, * pEnd;
    size_t nCap = 0;
    int iClause = 0, RetValue = 0;
    long Lit;
    if ( pFile == NULL )
        goto finish;
    while ( getline(&pLine, &nCap, pFile) >= 0 )
    {
        pCur = pLine;
        while ( isspace((unsigned char)*pCur) )
            pCur++;
        if ( *pCur == '\0' || *pCur == 'c' || *pCur == 'p' )
            continue;
        Vec_IntClear( vLits );
        while ( 1 )
        {
            errno = 0;
            Lit = strtol( pCur, &pEnd, 10 );
            if ( pEnd == pCur || errno || Lit > nVars || Lit < -nVars )
                goto finish;
            pCur = pEnd;
            if ( Lit == 0 )
                break;
            Vec_IntPush( vLits, Abc_Var2Lit(abs((int) Lit) - 1, Lit < 0) );
        }
        if ( iClause >= nClauses )
            goto finish;
        if ( pGroups[iClause] == 0 )
            RetValue = Fm_CamusAddBackground( p, Vec_IntArray(vLits), Vec_IntSize(vLits) );
        else
            RetValue = Fm_CamusAddGroup( p, pGroups[iClause] - 1, Vec_IntArray(vLits), Vec_IntSize(vLits) );
        if ( !RetValue )
            goto finish;
        iClause++;
    }
    RetValue = iClause == nClauses;

finish:
    free( pLine );
    if ( pFile )
        fclose( pFile );
    Vec_IntFree( vLits );
    return RetValue;
}

static int Fm_SelectAblation( const char * pName, Fm_CamusOptions_t * pOptions )
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
        pOptions->fUseCadicalTuning = 0;
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

static void Fm_PrintAblationJson( Fm_CamusMan_t * p, const char * pVariant,
                                 Vec_Int_t * vAll, Vec_Int_t * vMinimum )
{
    Fm_CamusStats_t Stats;
    int i, iGroup;
    Fm_CamusGetStats( p, &Stats );
    printf( "{\"backend\":\"%s\",\"variant\":\"%s\",\"status\":\"ok\","
            "\"candidates\":%d,\"minimum\":%d,\"selected\":[",
            Fm_CamusBackendName(), pVariant, Vec_IntSize(vAll), Vec_IntSize(vMinimum) );
    Vec_IntForEachEntry( vMinimum, iGroup, i )
        printf( "%s%d", i ? "," : "", iGroup + 1 );
    printf( "],\"stats\":{"
            "\"total_seconds\":%.6f,\"seed_seconds\":%.6f,"
            "\"map_seconds\":%.6f,\"validation_seconds\":%.6f,"
            "\"growth_seconds\":%.6f,\"seed_input\":%d,\"seed_result\":%d,"
            "\"seed_solves\":%lld,\"map_solves\":%lld,\"map_sat\":%lld,"
            "\"map_unsat\":%lld,\"validation_solves\":%lld,"
            "\"growth_solves\":%lld,\"refinements\":%lld,"
            "\"correction_sets\":%lld,\"core_shrinks\":%lld,"
            "\"core_groups_removed\":%lld,\"model_groups_added\":%lld,"
            "\"explicit_groups_tried\":%lld,\"solver_constructions\":%lld}}\n",
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

int main( int argc, char ** argv )
{
    Fm_CamusMan_t * p = NULL;
    Vec_Int_t * vAll = NULL, * vMus = NULL, * vMinimum = NULL;
    Fm_CamusOptions_t Options;
    int * pGroups = NULL;
    int nVars, nClauses, nGroups, fMinimumMus, fMinimumAll, fAblation, i, iGroup, RetValue = 1;
    abctime clk;
    if ( argc != 3 && argc != 4 && argc != 5 )
    {
        fprintf( stderr, "usage: %s FILE.cnf FILE.groups [minimum-mus|minimum-all|ablation VARIANT]\n", argv[0] );
        return 2;
    }
    fMinimumMus = argc == 4 && !strcmp( argv[3], "minimum-mus" );
    fMinimumAll = argc == 4 && !strcmp( argv[3], "minimum-all" );
    fAblation = argc == 5 && !strcmp( argv[3], "ablation" );
    if ( (argc == 4 && !fMinimumMus && !fMinimumAll) || (argc == 5 && !fAblation) )
    {
        fprintf( stderr, "unknown mode: %s\n", argv[3] );
        return 2;
    }
    Fm_CamusOptionsDefault( &Options );
    if ( fAblation && !Fm_SelectAblation(argv[4], &Options) )
    {
        fprintf( stderr, "unknown ablation variant: %s\n", argv[4] );
        return 2;
    }
    if ( !Fm_ReadHeader(argv[1], &nVars, &nClauses) ||
         (pGroups = Fm_ReadGroups(argv[2], nClauses, &nGroups)) == NULL || nGroups < 1 )
    {
        fprintf( stderr, "could not read the grouped CNF\n" );
        goto finish;
    }
    p = Fm_CamusStartWithOptions( nVars, nGroups - 1, &Options );
    if ( p == NULL || !Fm_LoadCnf(p, argv[1], pGroups, nVars, nClauses) )
    {
        fprintf( stderr, "could not load the grouped CNF\n" );
        goto finish;
    }
    vAll = Vec_IntStartNatural( nGroups - 1 );
    if ( fAblation )
    {
        vMinimum = Fm_CamusFindMinimumMus( p, vAll );
        if ( vMinimum == NULL )
        {
            fprintf( stderr, "the grouped formula is SAT or the ablation search failed\n" );
            goto finish;
        }
        Fm_PrintAblationJson( p, argv[4], vAll, vMinimum );
        RetValue = 0;
        goto finish;
    }
    if ( fMinimumAll )
    {
        clk = Abc_Clock();
        vMinimum = Fm_CamusFindMinimumMus( p, vAll );
        if ( vMinimum == NULL )
        {
            fprintf( stderr, "the grouped formula is SAT or the exact minimum search failed\n" );
            goto finish;
        }
        printf( "backend=%s candidates=%d seed-mus=internal minimum=%d seconds=%.6f\n", Fm_CamusBackendName(),
                Vec_IntSize(vAll), Vec_IntSize(vMinimum),
                (double)(Abc_Clock() - clk) / (double)CLOCKS_PER_SEC );
        printf( "selected=" );
        Vec_IntForEachEntry( vMinimum, iGroup, i )
            printf( "%s%d", i ? "," : "", iGroup + 1 );
        printf( "\n" );
        RetValue = 0;
        goto finish;
    }
    clk = Abc_Clock();
    vMus = Fm_CamusFindMus( p, vAll );
    if ( vMus == NULL )
    {
        fprintf( stderr, "the grouped formula is SAT or the MUS search failed\n" );
        goto finish;
    }
    if ( fMinimumMus )
    {
        clk = Abc_Clock();
        vMinimum = Fm_CamusFindMinimumMus( p, vMus );
        if ( vMinimum == NULL )
        {
            fprintf( stderr, "the exact minimum search failed\n" );
            goto finish;
        }
        printf( "backend=%s candidates=%d seed-mus=%d minimum=%d seconds=%.6f\n", Fm_CamusBackendName(),
                Vec_IntSize(vMus),
                Vec_IntSize(vMus), Vec_IntSize(vMinimum),
                (double)(Abc_Clock() - clk) / (double)CLOCKS_PER_SEC );
        printf( "selected=" );
        Vec_IntForEachEntry( vMinimum, iGroup, i )
            printf( "%s%d", i ? "," : "", iGroup + 1 );
        printf( "\n" );
    }
    else
        printf( "backend=%s groups=%d mus=%d seconds=%.6f\n", Fm_CamusBackendName(),
                nGroups - 1, Vec_IntSize(vMus),
                (double)(Abc_Clock() - clk) / (double)CLOCKS_PER_SEC );
    RetValue = 0;

finish:
    Vec_IntFreeP( &vMinimum );
    Vec_IntFreeP( &vMus );
    Vec_IntFreeP( &vAll );
    Fm_CamusStop( p );
    ABC_FREE( pGroups );
    return RetValue;
}
