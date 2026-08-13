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

int main( int argc, char ** argv )
{
    Fm_CamusMan_t * p = NULL;
    Vec_Int_t * vAll = NULL, * vMus = NULL, * vMinimum = NULL;
    int * pGroups = NULL;
    int nVars, nClauses, nGroups, fMinimumMus, fMinimumAll, RetValue = 1;
    abctime clk;
    if ( argc != 3 && argc != 4 )
    {
        fprintf( stderr, "usage: %s FILE.cnf FILE.groups [minimum-mus|minimum-all]\n", argv[0] );
        return 2;
    }
    fMinimumMus = argc == 4 && !strcmp( argv[3], "minimum-mus" );
    fMinimumAll = argc == 4 && !strcmp( argv[3], "minimum-all" );
    if ( argc == 4 && !fMinimumMus && !fMinimumAll )
    {
        fprintf( stderr, "unknown mode: %s\n", argv[3] );
        return 2;
    }
    if ( !Fm_ReadHeader(argv[1], &nVars, &nClauses) ||
         (pGroups = Fm_ReadGroups(argv[2], nClauses, &nGroups)) == NULL || nGroups < 1 )
    {
        fprintf( stderr, "could not read the grouped CNF\n" );
        goto finish;
    }
    p = Fm_CamusStart( nVars, nGroups - 1 );
    if ( p == NULL || !Fm_LoadCnf(p, argv[1], pGroups, nVars, nClauses) )
    {
        fprintf( stderr, "could not load the grouped CNF\n" );
        goto finish;
    }
    vAll = Vec_IntStartNatural( nGroups - 1 );
    clk = Abc_Clock();
    vMus = Fm_CamusFindMus( p, vAll );
    if ( vMus == NULL )
    {
        fprintf( stderr, "the grouped formula is SAT or the MUS search failed\n" );
        goto finish;
    }
    if ( fMinimumMus || fMinimumAll )
    {
        clk = Abc_Clock();
        vMinimum = Fm_CamusFindMinimumMus( p, fMinimumMus ? vMus : vAll );
        if ( vMinimum == NULL )
        {
            fprintf( stderr, "the exact minimum search failed\n" );
            goto finish;
        }
        printf( "backend=%s candidates=%d seed-mus=%d minimum=%d seconds=%.6f\n", Fm_CamusBackendName(),
                fMinimumMus ? Vec_IntSize(vMus) : Vec_IntSize(vAll),
                Vec_IntSize(vMus), Vec_IntSize(vMinimum),
                (double)(Abc_Clock() - clk) / (double)CLOCKS_PER_SEC );
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
