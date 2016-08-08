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

#include "aig/gia/gia.h"
#include "bool/kit/kit.h"
#include "misc/util/utilTruth.h"
#include "misc/vec/vecInt.h"
#include "misc/vec/vecPtr.h"
#include "proof/cec/cec.h"
#include "sat/bsat/satSolver.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static word s_Truths8[32] = {
    ABC_CONST(0xAAAAAAAAAAAAAAAA), ABC_CONST(0xAAAAAAAAAAAAAAAA), ABC_CONST(0xAAAAAAAAAAAAAAAA), ABC_CONST(0xAAAAAAAAAAAAAAAA),
    ABC_CONST(0xCCCCCCCCCCCCCCCC), ABC_CONST(0xCCCCCCCCCCCCCCCC), ABC_CONST(0xCCCCCCCCCCCCCCCC), ABC_CONST(0xCCCCCCCCCCCCCCCC),
    ABC_CONST(0xF0F0F0F0F0F0F0F0), ABC_CONST(0xF0F0F0F0F0F0F0F0), ABC_CONST(0xF0F0F0F0F0F0F0F0), ABC_CONST(0xF0F0F0F0F0F0F0F0),
    ABC_CONST(0xFF00FF00FF00FF00), ABC_CONST(0xFF00FF00FF00FF00), ABC_CONST(0xFF00FF00FF00FF00), ABC_CONST(0xFF00FF00FF00FF00),
    ABC_CONST(0xFFFF0000FFFF0000), ABC_CONST(0xFFFF0000FFFF0000), ABC_CONST(0xFFFF0000FFFF0000), ABC_CONST(0xFFFF0000FFFF0000),
    ABC_CONST(0xFFFFFFFF00000000), ABC_CONST(0xFFFFFFFF00000000), ABC_CONST(0xFFFFFFFF00000000), ABC_CONST(0xFFFFFFFF00000000),
    ABC_CONST(0x0000000000000000), ABC_CONST(0xFFFFFFFFFFFFFFFF), ABC_CONST(0x0000000000000000), ABC_CONST(0xFFFFFFFFFFFFFFFF),
    ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000), ABC_CONST(0xFFFFFFFFFFFFFFFF), ABC_CONST(0xFFFFFFFFFFFFFFFF)
};

#define ABC_EXACT_SOL_NVARS  0
#define ABC_EXACT_SOL_NFUNC  1
#define ABC_EXACT_SOL_NGATES 2

typedef struct Ses_Man_t_ Ses_Man_t;
struct Ses_Man_t_
{
    sat_solver * pSat;            /* SAT solver */

    word *       pSpec;           /* specification */
    int          bSpecInv;        /* remembers whether spec was inverted for normalization */
    int          nSpecVars;       /* number of variables in specification */
    int          nSpecFunc;       /* number of functions to synthesize */
    int          nRows;           /* number of rows in the specification (without 0) */
    int          nMaxDepth;       /* maximum depth (-1 if depth is not constrained) */
    int *        pArrTimeProfile; /* arrival times of inputs (NULL if arrival times are ignored) */
    int          nArrTimeDelta;   /* delta to the original arrival times (arrival times are normalized to have 0 as minimum element) */
    int          nArrTimeMax;     /* maximum normalized arrival time */
    int          nBTLimit;        /* conflict limit */
    int          fMakeAIG;        /* create AIG instead of general network */
    int          fVerbose;        /* be verbose */
    int          fVeryVerbose;    /* be very verbose */

    int          nGates;          /* number of gates */

    int          nSimVars;        /* number of simulation vars x(i, t) */
    int          nOutputVars;     /* number of output variables g(h, i) */
    int          nGateVars;       /* number of gate variables f(i, p, q) */
    int          nSelectVars;     /* number of select variables s(i, j, k) */
    int          nDepthVars;      /* number of depth variables d(i, j) */

    int          nOutputOffset;   /* offset where output variables start */
    int          nGateOffset;     /* offset where gate variables start */
    int          nSelectOffset;   /* offset where select variables start */
    int          nDepthOffset;    /* offset where depth variables start */

    abctime      timeSat;         /* SAT runtime */
    abctime      timeSatSat;      /* SAT runtime (sat instance) */
    abctime      timeSatUnsat;    /* SAT runtime (unsat instance) */
    abctime      timeTotal;       /* all runtime */
};

/***********************************************************************

  Synopsis    [Store truth tables based on normalized arrival times.]

***********************************************************************/

// The hash table is a list of pointers to Ses_TruthEntry_t elements, which
// are arranged in a linked list, each of which pointing to a linked list
// of Ses_TimesEntry_t elements which contain the char* representation of the
// optimum netlist according to then normalized arrival times:

typedef struct Ses_TimesEntry_t_ Ses_TimesEntry_t;
struct Ses_TimesEntry_t_
{
    int                pArrTimeProfile[8]; /* normalized arrival time profile */
    Ses_TimesEntry_t * next;               /* linked list pointer */
    char *             pNetwork;           /* pointer to char array representation of optimum network */
};

typedef struct Ses_TruthEntry_t_ Ses_TruthEntry_t;
struct Ses_TruthEntry_t_
{
    word               pTruth[4]; /* truth table for comparison */
    int                nVars;     /* number of variables */
    Ses_TruthEntry_t * next;      /* linked list pointer */
    Ses_TimesEntry_t * head;      /* pointer to head of sub list with arrival times */
};

#define SES_STORE_TABLE_SIZE 1024
typedef struct Ses_Store_t_ Ses_Store_t;
struct Ses_Store_t_
{
    int                fMakeAIG;                       /* create AIG instead of general network */
    int                fVerbose;                       /* be verbose */
    int                nBTLimit;                       /* conflict limit */
    int                nEntriesCount;                  /* number of entries */
    Ses_TruthEntry_t * pEntries[SES_STORE_TABLE_SIZE]; /* hash table for truth table entries */

    unsigned long      nCutCount;
    unsigned long      pCutCount[9];
    unsigned long      nCacheHit;
};

static Ses_Store_t * s_pSesStore = NULL;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

static int Abc_NormalizeArrivalTimes( int * pArrTimeProfile, int nVars, int * maxNormalized )
{
    int * p = pArrTimeProfile, * pEnd = pArrTimeProfile + nVars;
    int delta = *p;

    while ( ++p < pEnd )
        if ( *p < delta )
            delta = *p;

    *maxNormalized = 0;
    p = pArrTimeProfile;
    while ( p < pEnd )
    {
        *p -= delta;
        if ( *p > *maxNormalized )
            *maxNormalized = *p;
        ++p;
    }

    *maxNormalized += 1;

    return delta;
}

static inline void Abc_UnnormalizeArrivalTimes( int * pArrTimeProfile, int nVars, int nDelta )
{
    int l;

    for ( l = 0; l < nVars; ++l )
        pArrTimeProfile[l] += nDelta;
}

static inline Ses_Store_t * Ses_StoreAlloc( int nBTLimit, int fMakeAIG, int fVerbose )
{
    Ses_Store_t * pStore = ABC_CALLOC( Ses_Store_t, 1 );
    pStore->fMakeAIG      = fMakeAIG;
    pStore->fVerbose      = fVerbose;
    pStore->nBTLimit      = nBTLimit;
    pStore->nEntriesCount = 0;
    memset( pStore->pEntries, 0, SES_STORE_TABLE_SIZE );

    pStore->nCutCount = 0;
    memset( pStore->pCutCount, 0, 9 );
    pStore->nCacheHit = 0;

    return pStore;
}

static inline void Ses_StoreClean( Ses_Store_t * pStore )
{
    int i;
    Ses_TruthEntry_t * pTEntry, * pTEntry2;
    Ses_TimesEntry_t * pTiEntry, * pTiEntry2;

    for ( i = 0; i < SES_STORE_TABLE_SIZE; ++i )
        if ( pStore->pEntries[i] )
        {
            pTEntry = pStore->pEntries[i];

            while ( pTEntry )
            {
                pTiEntry = pTEntry->head;
                while ( pTiEntry )
                {
                    ABC_FREE( pTiEntry->pNetwork );
                    pTiEntry2 = pTiEntry;
                    pTiEntry = pTiEntry->next;
                    ABC_FREE( pTiEntry2 );
                }
                pTEntry2 = pTEntry;
                pTEntry = pTEntry->next;
                ABC_FREE( pTEntry2 );
            }
        }

    ABC_FREE( pStore );
}

static inline int Ses_StoreTableHash( word * pTruth, int nVars )
{
    static int s_Primes[4] = { 1291, 1699, 1999, 2357 };
    int i;
    unsigned uHash = 0;
    for ( i = 0; i < Kit_TruthWordNum( nVars ); ++i )
        uHash ^= pTruth[i] * s_Primes[i & 0xf];
    return (int)(uHash % SES_STORE_TABLE_SIZE );
}

static inline int Ses_StoreTruthEqual( Ses_TruthEntry_t * pEntry, word * pTruth, int nVars )
{
    int i;

    if ( pEntry->nVars != nVars )
        return 0;

    for ( i = 0; i < Kit_TruthWordNum( nVars ); ++i )
        if ( pEntry->pTruth[i] != pTruth[i] )
            return 0;
    return 1;
}

static inline void Ses_StoreTruthCopy( Ses_TruthEntry_t * pEntry, word * pTruthSrc, int nVars )
{
    int i;
    pEntry->nVars = nVars;
    for ( i = 0; i < Kit_TruthWordNum( nVars ); ++i )
        pEntry->pTruth[i] = pTruthSrc[i];
}

static inline int Ses_StoreTimesEqual( int * pTimes1, int * pTimes2, int nVars )
{
    int i;
    for ( i = 0; i < nVars; ++i )
        if ( pTimes1[i] != pTimes2[i] )
            return 0;
    return 1;
}

static inline void Ses_StoreTimesCopy( int * pTimesDest, int * pTimesSrc, int nVars )
{
    int i;
    for ( i = 0; i < nVars; ++i )
        pTimesDest[i] = pTimesSrc[i];
}

// pArrTimeProfile is not normalized
// returns 1 if and only if a new TimesEntry has been created
int Ses_StoreAddEntry( Ses_Store_t * pStore, word * pTruth, int nVars, int * pArrTimeProfile, char * pSol )
{
    int key, fAdded;
    Ses_TruthEntry_t * pTEntry;
    Ses_TimesEntry_t * pTiEntry;

    key = Ses_StoreTableHash( pTruth, nVars );
    pTEntry = pStore->pEntries[key];

    /* does truth table already exist? */
    while ( pTEntry )
    {
        if ( Ses_StoreTruthEqual( pTEntry, pTruth, nVars ) )
            break;
        else
            pTEntry = pTEntry->next;
    }

    /* entry does not yet exist, so create new one and enqueue */
    if ( !pTEntry )
    {
        pTEntry = ABC_CALLOC( Ses_TruthEntry_t, 1 );
        Ses_StoreTruthCopy( pTEntry, pTruth, nVars );
        pTEntry->next = pStore->pEntries[key];
        pStore->pEntries[key] = pTEntry;
    }

    /* does arrival time already exist? */
    pTiEntry = pTEntry->head;
    while ( pTiEntry )
    {
        if ( Ses_StoreTimesEqual( pArrTimeProfile, pTiEntry->pArrTimeProfile, nVars ) )
            break;
        else
            pTiEntry = pTiEntry->next;
    }

    /* entry does not yet exist, so create new one and enqueue */
    if ( !pTiEntry )
    {
        pTiEntry = ABC_CALLOC( Ses_TimesEntry_t, 1 );
        Ses_StoreTimesCopy( pTiEntry->pArrTimeProfile, pArrTimeProfile, nVars );
        pTiEntry->pNetwork = pSol;
        pTiEntry->next = pTEntry->head;
        pTEntry->head = pTiEntry;

        /* item has been added */
        fAdded = 1;
        pStore->nEntriesCount++;
    }
    else
        /* item was already present */
        fAdded = 0;

    return fAdded;
}

// pArrTimeProfile is not normalized
// returns 0 if no solution was found
char * Ses_StoreGetEntry( Ses_Store_t * pStore, word * pTruth, int nVars, int * pArrTimeProfile )
{
    int key;
    Ses_TruthEntry_t * pTEntry;
    Ses_TimesEntry_t * pTiEntry;

    key = Ses_StoreTableHash( pTruth, nVars );
    pTEntry = pStore->pEntries[key];

    /* find truth table entry */
    while ( pTEntry )
    {
        if ( Ses_StoreTruthEqual( pTEntry, pTruth, nVars ) )
            break;
        else
            pTEntry = pTEntry->next;
    }

    /* no entry found? */
    if ( !pTEntry )
        return 0;

    /* find times entry */
    pTiEntry = pTEntry->head;
    while ( pTiEntry )
    {
        if ( Ses_StoreTimesEqual( pArrTimeProfile, pTiEntry->pArrTimeProfile, nVars ) )
            break;
        else
            pTiEntry = pTiEntry->next;
    }

    /* no entry found? */
    if ( !pTiEntry )
        return 0;

    return pTiEntry->pNetwork;
}

static void Ses_StoreWrite( Ses_Store_t * pStore, const char * pFilename )
{
    int i;
    Ses_TruthEntry_t * pTEntry;
    Ses_TimesEntry_t * pTiEntry;
    FILE * pFile;

    pFile = fopen( pFilename, "wb" );
    if (pFile == NULL)
    {
        printf( "cannot open file \"%s\" for writing\n", pFilename );
        return;
    }

    fwrite( &pStore->nEntriesCount, sizeof( int ), 1, pFile );

    for ( i = 0; i < SES_STORE_TABLE_SIZE; ++i )
        if ( pStore->pEntries[i] )
        {
            pTEntry = pStore->pEntries[i];

            while ( pTEntry )
            {
                pTiEntry = pTEntry->head;
                while ( pTiEntry )
                {
                    fwrite( pTEntry->pTruth, sizeof( word ), 4, pFile );
                    fwrite( &pTEntry->nVars, sizeof( int ), 1, pFile );
                    fwrite( pTiEntry->pArrTimeProfile, sizeof( int ), 8, pFile );
                    fwrite( pTiEntry->pNetwork, sizeof( char ), 3 + 4 * pTiEntry->pNetwork[ABC_EXACT_SOL_NGATES] + 2 + pTiEntry->pNetwork[ABC_EXACT_SOL_NVARS], pFile );
                    pTiEntry = pTiEntry->next;
                }
                pTEntry = pTEntry->next;
            }
        }


    fclose( pFile );
}

static void Ses_StoreRead( Ses_Store_t * pStore, const char * pFilename )
{
    int i, nEntries;
    word pTruth[4];
    int nVars;
    int pArrTimeProfile[8];
    char pHeader[3];
    char * pNetwork;
    FILE * pFile;
    int value;

    pFile = fopen( pFilename, "rb" );
    if (pFile == NULL)
    {
        printf( "cannot open file \"%s\" for reading\n", pFilename );
        return;
    }

    value = fread( &nEntries, sizeof( int ), 1, pFile );

    for ( i = 0; i < nEntries; ++i )
    {
        value = fread( pTruth, sizeof( word ), 4, pFile );
        value = fread( &nVars, sizeof( int ), 1, pFile );
        value = fread( pArrTimeProfile, sizeof( int ), 8, pFile );
        value = fread( pHeader, sizeof( char ), 3, pFile );

        pNetwork = ABC_CALLOC( char, 3 + 4 * pHeader[ABC_EXACT_SOL_NGATES] + 2 + pHeader[ABC_EXACT_SOL_NVARS] );
        pNetwork[0] = pHeader[0];
        pNetwork[1] = pHeader[1];
        pNetwork[2] = pHeader[2];

        value = fread( pNetwork + 3, sizeof( char ), 4 * pHeader[ABC_EXACT_SOL_NGATES] + 2 + pHeader[ABC_EXACT_SOL_NVARS], pFile );

        Ses_StoreAddEntry( pStore, pTruth, nVars, pArrTimeProfile, pNetwork );
    }

    fclose( pFile );
}

static inline Ses_Man_t * Ses_ManAlloc( word * pTruth, int nVars, int nFunc, int nMaxDepth, int * pArrTimeProfile, int fMakeAIG, int fVerbose )
{
    int h, i;

    Ses_Man_t * p = ABC_CALLOC( Ses_Man_t, 1 );
    p->pSat       = NULL;
    p->bSpecInv   = 0;
    for ( h = 0; h < nFunc; ++h )
        if ( pTruth[h << 2] & 1 )
        {
            for ( i = 0; i < 4; ++i )
                pTruth[(h << 2) + i] = ~pTruth[(h << 2) + i];
            p->bSpecInv |= ( 1 << h );
        }
    p->pSpec         = pTruth;
    p->nSpecVars     = nVars;
    p->nSpecFunc     = nFunc;
    p->nRows         = ( 1 << nVars ) - 1;
    p->nMaxDepth     = nMaxDepth;
    p->pArrTimeProfile = nMaxDepth >= 0 ? pArrTimeProfile : NULL;
    if ( p->pArrTimeProfile )
        p->nArrTimeDelta = Abc_NormalizeArrivalTimes( p->pArrTimeProfile, nVars, &p->nArrTimeMax );
    else
        p->nArrTimeDelta = p->nArrTimeMax = 0;
    p->fMakeAIG      = fMakeAIG;
    p->nBTLimit      = nMaxDepth >= 0 ? 50000 : 0;
    p->fVerbose      = fVerbose;
    p->fVeryVerbose  = 0;

    return p;
}

static inline void Ses_ManClean( Ses_Man_t * pSes )
{
    int h, i;
    for ( h = 0; h < pSes->nSpecFunc; ++h )
        if ( ( pSes->bSpecInv >> h ) & 1 )
            for ( i = 0; i < 4; ++i )
                pSes->pSpec[(h << 2) + i] = ~( pSes->pSpec[(h << 2) + i] );

    if ( pSes->pArrTimeProfile )
        for ( i = 0; i < pSes->nSpecVars; ++i )
            pSes->pArrTimeProfile[i] += pSes->nArrTimeDelta;

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

static inline int Ses_ManDepthVar( Ses_Man_t * pSes, int i, int j )
{
    assert( i < pSes->nGates );
    assert( j <= pSes->nArrTimeMax + i );

    return pSes->nDepthOffset + i * pSes->nArrTimeMax + ( ( i * ( i + 1 ) ) / 2 ) + j;
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
    pSes->nDepthVars = pSes->nMaxDepth > 0 ? nGates * pSes->nArrTimeMax + ( nGates * ( nGates + 1 ) ) / 2 : 0;

    pSes->nOutputOffset = pSes->nSimVars;
    pSes->nGateOffset   = pSes->nSimVars + pSes->nOutputVars;
    pSes->nSelectOffset = pSes->nSimVars + pSes->nOutputVars + pSes->nGateVars;
    pSes->nDepthOffset  = pSes->nSimVars + pSes->nOutputVars + pSes->nGateVars + pSes->nSelectVars;

    if ( pSes->pSat )
        sat_solver_delete( pSes->pSat );
    pSes->pSat = sat_solver_new();
    sat_solver_setnvars( pSes->pSat, pSes->nSimVars + pSes->nOutputVars + pSes->nGateVars + pSes->nSelectVars + pSes->nDepthVars );
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
        if ( Abc_TtGetBit( s_Truths8 + ( j << 2 ), t + 1 ) != b ) /* 1 in clause, we can omit the clause */
            return;
    }
    else
        pLits[ctr++] = Abc_Var2Lit( Ses_ManSimVar( pSes, j - pSes->nSpecVars, t ), b );

    if ( k < pSes->nSpecVars )
    {
        if ( Abc_TtGetBit( s_Truths8 + ( k << 2 ), t + 1 ) != c ) /* 1 in clause, we can omit the clause */
            return;
    }
    else
        pLits[ctr++] = Abc_Var2Lit( Ses_ManSimVar( pSes, k - pSes->nSpecVars, t ), c );

    if ( b > 0 || c > 0 )
        pLits[ctr++] = Abc_Var2Lit( Ses_ManGateVar( pSes, i, b, c ), 1 - a );

    value = sat_solver_addclause( pSes->pSat, pLits, pLits + ctr );
    assert( value );
}

static int Ses_ManCreateClauses( Ses_Man_t * pSes )
{
    extern int Extra_TruthVarsSymm( unsigned * pTruth, int nVars, int iVar0, int iVar1 );

    int h, i, j, k, t, ii, jj, kk, p, q, d;
    int pLits[3];
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
                pLits[1] = Abc_Var2Lit( Ses_ManSimVar( pSes, i, t ), 1 - Abc_TtGetBit( &pSes->pSpec[h << 2], t + 1 ) );
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

    /* only AIG */
    if ( pSes->fMakeAIG )
    {
        for ( i = 0; i < pSes->nGates; ++i )
        {
            /* not 2 ones */
            pLits[0] = Abc_Var2Lit( Ses_ManGateVar( pSes, i, 0, 1 ), 1 );
            pLits[1] = Abc_Var2Lit( Ses_ManGateVar( pSes, i, 1, 0 ), 1 );
            pLits[2] = Abc_Var2Lit( Ses_ManGateVar( pSes, i, 1, 1 ), 0 );
            assert( sat_solver_addclause( pSes->pSat, pLits, pLits + 3 ) );

            pLits[0] = Abc_Var2Lit( Ses_ManGateVar( pSes, i, 0, 1 ), 1 );
            pLits[1] = Abc_Var2Lit( Ses_ManGateVar( pSes, i, 1, 0 ), 0 );
            pLits[2] = Abc_Var2Lit( Ses_ManGateVar( pSes, i, 1, 1 ), 1 );
            assert( sat_solver_addclause( pSes->pSat, pLits, pLits + 3 ) );

            pLits[0] = Abc_Var2Lit( Ses_ManGateVar( pSes, i, 0, 1 ), 0 );
            pLits[1] = Abc_Var2Lit( Ses_ManGateVar( pSes, i, 1, 0 ), 1 );
            pLits[2] = Abc_Var2Lit( Ses_ManGateVar( pSes, i, 1, 1 ), 1 );
            assert( sat_solver_addclause( pSes->pSat, pLits, pLits + 3 ) );
        }
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
    if ( pSes->nMaxDepth == -1 && pSes->nSpecFunc == 1 ) /* only check if there is one output function */
        for ( q = 1; q < pSes->nSpecVars; ++q )
            for ( p = 0; p < q; ++p )
                if ( Extra_TruthVarsSymm( (unsigned*)( &pSes->pSpec[h << 2] ), pSes->nSpecVars, p, q ) )
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

    /* DEPTH clauses */
    if ( pSes->nMaxDepth > 0 )
    {
        for ( i = 0; i < pSes->nGates; ++i )
        {
            /* propagate depths from children */
            for ( k = 1; k < i; ++k )
                for ( j = 0; j < k; ++j )
                {
                    pLits[0] = Abc_Var2Lit( Ses_ManSelectVar( pSes, i, pSes->nSpecVars + j, pSes->nSpecVars + k ), 1 );
                    for ( jj = 0; jj <= pSes->nArrTimeMax + j; ++jj )
                    {
                        pLits[1] = Abc_Var2Lit( Ses_ManDepthVar( pSes, j, jj ), 1 );
                        pLits[2] = Abc_Var2Lit( Ses_ManDepthVar( pSes, i, jj + 1 ), 0 );
                        assert( sat_solver_addclause( pSes->pSat, pLits, pLits + 3 ) );
                    }
                }

            for ( k = 0; k < i; ++k )
                for ( j = 0; j < pSes->nSpecVars + k; ++j )
                {
                    pLits[0] = Abc_Var2Lit( Ses_ManSelectVar( pSes, i, j, pSes->nSpecVars + k ), 1 );
                    for ( kk = 0; kk <= pSes->nArrTimeMax + k; ++kk )
                    {
                        pLits[1] = Abc_Var2Lit( Ses_ManDepthVar( pSes, k, kk ), 1 );
                        pLits[2] = Abc_Var2Lit( Ses_ManDepthVar( pSes, i, kk + 1 ), 0 );
                        assert( sat_solver_addclause( pSes->pSat, pLits, pLits + 3 ) );
                    }
                }

            /* propagate depths from arrival times at PIs */
            if ( pSes->pArrTimeProfile )
            {
                for ( k = 1; k < pSes->nSpecVars + i; ++k )
                    for ( j = 0; j < ( ( k < pSes->nSpecVars ) ? k : pSes->nSpecVars ); ++j )
                    {
                        d = pSes->pArrTimeProfile[j];
                        if ( k < pSes->nSpecVars && pSes->pArrTimeProfile[k] > d )
                            d = pSes->pArrTimeProfile[k];

                        pLits[0] = Abc_Var2Lit( Ses_ManSelectVar( pSes, i, j, k ), 1 );
                        pLits[1] = Abc_Var2Lit( Ses_ManDepthVar( pSes, i, d + 1 ), 0 );
                        assert( sat_solver_addclause( pSes->pSat, pLits, pLits + 2 ) );
                    }
            }
            else
            {
                /* arrival times are 0 */
                pLits[0] = Abc_Var2Lit( Ses_ManDepthVar( pSes, i, 0 ), 0 );
                assert( sat_solver_addclause( pSes->pSat, pLits, pLits + 1 ) );
            }

            /* reverse order encoding of depth variables */
            for ( j = 1; j <= pSes->nArrTimeMax + i; ++j )
            {
                pLits[0] = Abc_Var2Lit( Ses_ManDepthVar( pSes, i, j ), 1 );
                pLits[1] = Abc_Var2Lit( Ses_ManDepthVar( pSes, i, j - 1 ), 0 );
                assert( sat_solver_addclause( pSes->pSat, pLits, pLits + 2 ) );
            }

            /* constrain maximum depth */
            if ( pSes->nMaxDepth < pSes->nArrTimeMax + i )
                for ( h = 0; h < pSes->nSpecFunc; ++h )
                {
                    pLits[0] = Abc_Var2Lit( Ses_ManOutputVar( pSes, h, i ), 1 );
                    pLits[1] = Abc_Var2Lit( Ses_ManDepthVar( pSes, i, pSes->nMaxDepth ), 1 );
                    if ( !sat_solver_addclause( pSes->pSat, pLits, pLits + 2 ) )
                        return 0;
                }
        }
    }

    return 1;
}

/**Function*************************************************************

  Synopsis    [Solve.]

***********************************************************************/
static inline int Ses_ManSolve( Ses_Man_t * pSes )
{
    int status;
    abctime timeStart, timeDelta;

    if ( pSes->fVeryVerbose )
    {
        printf( "solve SAT instance with %d clauses and %d variables\n", sat_solver_nclauses( pSes->pSat ), sat_solver_nvars( pSes->pSat ) );
    }

    timeStart = Abc_Clock();
    status = sat_solver_solve( pSes->pSat, NULL, NULL, pSes->nBTLimit, 0, 0, 0 );
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
            printf( "resource limit reached\n" );
        }
        return 2;
    }
}

/**Function*************************************************************

  Synopsis    [Extract solution.]

***********************************************************************/
// char is an array of short integers that stores the synthesized network
// using the following format
// | nvars | nfunc | ngates | gate[1] | ... | gate[ngates] | func[1] | .. | func[nfunc] |
// nvars:       integer with number of variables
// nfunc:       integer with number of functions
// ngates:      integer with number of gates
// gate[i]:     | op | nfanin | fanin[1] | ... | fanin[nfanin] |
//   op:        integer of gate's truth table (divided by 2, because gate is normal)
//   nfanin[i]: integer with number of fanins
//   fanin:     integer to primary input or other gate
// func[i]:     | fanin | delay | pin[1] | ... | pin[nvars] |
//   fanin:     integer as literal to some gate (not primary input), can be complemented
//   delay:     maximum delay to output (taking arrival times into account, not normalized) or 0 if not specified
//   pin[i]:    pin to pin delay to input i or 0 if not specified or if there is no connection to input i
// NOTE: since outputs can only point to gates, delay and pin-to-pin times cannot be 0
static char * Ses_ManExtractSolution( Ses_Man_t * pSes )
{
    int nSol, h, i, j, k, l, aj, ak, d, nOp;
    char * pSol, * p;
    int * pPerm = NULL; /* will be a 2d array [i][l] where is is gate id and l is PI id */

    /* compute length of solution, for now all gates have 2 inputs */
    nSol = 3 + pSes->nGates * 4 + pSes->nSpecFunc * ( 2 + pSes->nSpecVars );

    p = pSol = ABC_CALLOC( char, nSol );

    /* header */
    *p++ = pSes->nSpecVars;
    *p++ = pSes->nSpecFunc;
    *p++ = pSes->nGates;

    /* gates */
    for ( i = 0; i < pSes->nGates; ++i )
    {
        nOp  = sat_solver_var_value( pSes->pSat, Ses_ManGateVar( pSes, i, 0, 1 ) );
        nOp |= sat_solver_var_value( pSes->pSat, Ses_ManGateVar( pSes, i, 1, 0 ) ) << 1;
        nOp |= sat_solver_var_value( pSes->pSat, Ses_ManGateVar( pSes, i, 1, 1 ) ) << 2;

        *p++ = nOp;
        *p++ = 2;

        if ( pSes->fVeryVerbose )
            printf( "add gate %d with operation %d", pSes->nSpecVars + i, nOp );

        for ( k = 0; k < pSes->nSpecVars + i; ++k )
            for ( j = 0; j < k; ++j )
                if ( sat_solver_var_value( pSes->pSat, Ses_ManSelectVar( pSes, i, j, k ) ) )
                {
                    if ( pSes->fVeryVerbose )
                        printf( " and operands %d and %d", j, k );
                    *p++ = j;
                    *p++ = k;
                    break;
                }

        if ( pSes->fVeryVerbose )
        {
            if ( pSes->nMaxDepth > 0 )
            {
                printf( " and depth vector " );
                for ( j = 0; j <= pSes->nArrTimeMax + i; ++j )
                    printf( "%d", sat_solver_var_value( pSes->pSat, Ses_ManDepthVar( pSes, i, j ) ) );
            }
            printf( "\n" );
        }
    }

    /* pin-to-pin delay */
    if ( pSes->nMaxDepth != -1 )
    {
        pPerm = ABC_CALLOC( int, pSes->nGates * pSes->nSpecVars );
        for ( i = 0; i < pSes->nGates; ++i )
        {
            /* since all gates are binary for now */
            j = pSol[3 + i * 4 + 2];
            k = pSol[3 + i * 4 + 3];

            for ( l = 0; l < pSes->nSpecVars; ++l )
            {
                /* pin-to-pin delay to input l of child nodes */
                aj = j < pSes->nSpecVars ? 0 : pPerm[(j - pSes->nSpecVars) * pSes->nSpecVars + l];
                ak = k < pSes->nSpecVars ? 0 : pPerm[(k - pSes->nSpecVars) * pSes->nSpecVars + l];

                if ( aj == 0 && ak == 0 )
                    pPerm[i * pSes->nSpecVars + l] = ( l == j || l == k ) ? 1 : 0;
                else
                    pPerm[i * pSes->nSpecVars + l] = Abc_MaxInt( aj, ak ) + 1;
            }
        }
    }

    /* outputs */
    for ( h = 0; h < pSes->nSpecFunc; ++h )
        for ( i = 0; i < pSes->nGates; ++i )
            if ( sat_solver_var_value( pSes->pSat, Ses_ManOutputVar( pSes, h, i ) ) )
            {
                *p++ = Abc_Var2Lit( i, ( pSes->bSpecInv >> h ) & 1 );
                d = 0;
                if ( pSes->nMaxDepth != -1 )
                    /* while ( d < pSes->nArrTimeMax + i && sat_solver_var_value( pSes->pSat, Ses_ManDepthVar( pSes, i, d ) ) ) */
                    /*     ++d; */
                    for ( l = 0; l < pSes->nSpecVars; ++l )
                        d = Abc_MaxInt( d, pSes->pArrTimeProfile[l] + pPerm[i * pSes->nSpecVars + l] );
                *p++ = d;
                if ( pSes->fVeryVerbose )
                    printf( "output %d points to %d and has normalized delay %d (nArrTimeDelta = %d)\n", h, i, d, pSes->nArrTimeDelta );
                for ( l = 0; l < pSes->nSpecVars; ++l )
                {
                    d = ( pSes->nMaxDepth != -1 ) ? pPerm[i * pSes->nSpecVars + l] : 0;
                    if ( pSes->fVeryVerbose )
                        printf( "  pin-to-pin arrival time from input %d is %d (pArrTimeProfile = %d)\n", l, d, pSes->pArrTimeProfile[l] );
                    *p++ = d;
                }
            }

    /* pin-to-pin delays */
    if ( pSes->nMaxDepth != -1 )
        ABC_FREE( pPerm );

    /* have we used all the fields? */
    assert( ( p - pSol ) == nSol );

    return pSol;
}

static Abc_Ntk_t * Ses_ManExtractNtk( char const * pSol )
{
    int h, i;
    char const * p;
    Abc_Ntk_t * pNtk;
    Abc_Obj_t * pObj;
    Vec_Ptr_t * pGates, * vNames;
    char pGateTruth[5];
    char * pSopCover;

    pNtk = Abc_NtkAlloc( ABC_NTK_LOGIC, ABC_FUNC_SOP, 1 );
    pNtk->pName = Extra_UtilStrsav( "exact" );
    pGates = Vec_PtrAlloc( pSol[ABC_EXACT_SOL_NVARS] + pSol[ABC_EXACT_SOL_NGATES] );
    pGateTruth[3] = '0';
    pGateTruth[4] = '\0';
    vNames = Abc_NodeGetFakeNames( pSol[ABC_EXACT_SOL_NVARS] + pSol[ABC_EXACT_SOL_NFUNC] );

    /* primary inputs */
    Vec_PtrPush( pNtk->vObjs, NULL );
    for ( i = 0; i < pSol[ABC_EXACT_SOL_NVARS]; ++i )
    {
        pObj = Abc_NtkCreatePi( pNtk );
        Abc_ObjAssignName( pObj, (char*)Vec_PtrEntry( vNames, i ), NULL );
        Vec_PtrPush( pGates, pObj );
    }

    /* gates */
    p = pSol + 3;
    for ( i = 0; i < pSol[ABC_EXACT_SOL_NGATES]; ++i )
    {
        pGateTruth[2] = '0' + ( *p & 1 );
        pGateTruth[1] = '0' + ( ( *p >> 1 ) & 1 );
        pGateTruth[0] = '0' + ( ( *p >> 2 ) & 1 );
        ++p;

        assert( *p == 2 ); /* binary gate */
        ++p;

        pSopCover = Abc_SopFromTruthBin( pGateTruth );
        pObj = Abc_NtkCreateNode( pNtk );
        pObj->pData = Abc_SopRegister( (Mem_Flex_t*)pNtk->pManFunc, pSopCover );
        Vec_PtrPush( pGates, pObj );
        ABC_FREE( pSopCover );

        Abc_ObjAddFanin( pObj, (Abc_Obj_t *)Vec_PtrEntry( pGates, *p++ ) );
        Abc_ObjAddFanin( pObj, (Abc_Obj_t *)Vec_PtrEntry( pGates, *p++ ) );
    }

    /* outputs */
    for ( h = 0; h < pSol[ABC_EXACT_SOL_NFUNC]; ++h )
    {
        pObj = Abc_NtkCreatePo( pNtk );
        Abc_ObjAssignName( pObj, (char*)Vec_PtrEntry( vNames, pSol[ABC_EXACT_SOL_NVARS] + h ), NULL );
        if ( Abc_LitIsCompl( *p ) )
            Abc_ObjAddFanin( pObj, Abc_NtkCreateNodeInv( pNtk, (Abc_Obj_t *)Vec_PtrEntry( pGates, pSol[ABC_EXACT_SOL_NVARS] + Abc_Lit2Var( *p ) ) ) );
        else
            Abc_ObjAddFanin( pObj, (Abc_Obj_t *)Vec_PtrEntry( pGates, pSol[ABC_EXACT_SOL_NVARS] + Abc_Lit2Var( *p ) ) );
        p += ( 2 + pSol[ABC_EXACT_SOL_NVARS] );
    }
    Abc_NodeFreeNames( vNames );

    Vec_PtrFree( pGates );

    if ( !Abc_NtkCheck( pNtk ) )
        printf( "Ses_ManExtractSolution(): Network check has failed.\n" );

    return pNtk;
}

static Gia_Man_t * Ses_ManExtractGia( char const * pSol )
{
    int h, i;
    char const * p;
    Gia_Man_t * pGia;
    Vec_Int_t * pGates;
    Vec_Ptr_t * vNames;
    int nObj, nChild1, nChild2, fChild1Comp, fChild2Comp;

    pGia = Gia_ManStart( pSol[ABC_EXACT_SOL_NVARS] + pSol[ABC_EXACT_SOL_NGATES] + pSol[ABC_EXACT_SOL_NFUNC] + 1 );
    pGia->nConstrs = 0;
    pGia->pName = Extra_UtilStrsav( "exact" );

    pGates = Vec_IntAlloc( pSol[ABC_EXACT_SOL_NVARS] + pSol[ABC_EXACT_SOL_NGATES] );
    vNames = Abc_NodeGetFakeNames( pSol[ABC_EXACT_SOL_NVARS] + pSol[ABC_EXACT_SOL_NFUNC] );

    /* primary inputs */
    pGia->vNamesIn = Vec_PtrStart( pSol[ABC_EXACT_SOL_NVARS] );
    for ( i = 0; i < pSol[ABC_EXACT_SOL_NVARS]; ++i )
    {
        nObj = Gia_ManAppendCi( pGia );
        Vec_IntPush( pGates, nObj );
        Vec_PtrSetEntry( pGia->vNamesIn, i, Extra_UtilStrsav( Vec_PtrEntry( vNames, i ) ) );
    }

    /* gates */
    p = pSol + 3;
    for ( i = 0; i < pSol[ABC_EXACT_SOL_NGATES]; ++i )
    {
        assert( p[1] == 2 );
        nChild1 = Vec_IntEntry( pGates, p[2] );
        nChild2 = Vec_IntEntry( pGates, p[3] );
        fChild1Comp = fChild2Comp = 0;

        if ( *p & 1 )
        {
            nChild1 = Abc_LitNot( nChild1 );
            fChild1Comp = 1;
        }
        if ( ( *p >> 1 ) & 1 )
        {
            nChild2 = Abc_LitNot( nChild2 );
            fChild2Comp = 1;
        }
        nObj = Gia_ManAppendAnd( pGia, nChild1, nChild2 );
        if ( fChild1Comp && fChild2Comp )
        {
            assert( ( *p >> 2 ) & 1 );
            nObj = Abc_LitNot( nObj );
        }

        Vec_IntPush( pGates, nObj );

        p += 4;
    }

    /* outputs */
    pGia->vNamesOut = Vec_PtrStart( pSol[ABC_EXACT_SOL_NFUNC] );
    for ( h = 0; h < pSol[ABC_EXACT_SOL_NFUNC]; ++h )
    {
        nObj = Vec_IntEntry( pGates, pSol[ABC_EXACT_SOL_NVARS] + Abc_Lit2Var( *p ) );
        if ( Abc_LitIsCompl( *p ) )
            nObj = Abc_LitNot( nObj );
        Gia_ManAppendCo( pGia, nObj );
        Vec_PtrSetEntry( pGia->vNamesOut, h, Extra_UtilStrsav( Vec_PtrEntry( vNames, pSol[ABC_EXACT_SOL_NVARS] + h ) ) );
        p += ( 2 + pSol[ABC_EXACT_SOL_NVARS] );
    }
    Abc_NodeFreeNames( vNames );

    Vec_IntFree( pGates );

    return pGia;
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

static inline void Ses_ManPrintFuncs( Ses_Man_t * pSes )
{
    int h;

    printf( "find optimum circuit for %d %d-variable functions:\n", pSes->nSpecFunc, pSes->nSpecVars );
    for ( h = 0; h < pSes->nSpecFunc; ++h )
    {
        printf( "  func %d: ", h + 1 );
        Abc_TtPrintHexRev( stdout, &pSes->pSpec[h >> 2], pSes->nSpecVars );
        printf( "\n" );
    }
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

    if ( pSes->nMaxDepth > 0 )
        for ( i = 0; i < pSes->nGates; ++i )
            for ( j = 0; j <= i; ++j )
                printf( "d(%d, %d) : %d\n", i, j, Ses_ManDepthVar( pSes, i, j ) );

}

/**Function*************************************************************

  Synopsis    [Synthesis algorithm.]

***********************************************************************/
static int Ses_ManFindMinimumSize( Ses_Man_t * pSes )
{
    int nGates = 0;

    while ( true )
    {
        ++nGates;

        /* give up if number of gates is impossible for given depth */
        if ( pSes->nMaxDepth != -1 && nGates >= ( 1 << pSes->nMaxDepth ) )
            return 0;

        Ses_ManCreateVars( pSes, nGates );
        if ( !Ses_ManCreateClauses( pSes ) )
            return 0; /* proven UNSAT while creating clauses */

        switch ( Ses_ManSolve( pSes ) )
        {
        case 1: return 1; /* SAT */
        case 2: return 0; /* resource limit */
        }
    }

    return 0;
}

/**Function*************************************************************

  Synopsis    [Find minimum size networks with a SAT solver.]

  Description [If nMaxDepth is -1, then depth constraints are ignored.
               If nMaxDepth is not -1, one can set pArrTimeProfile which should have the length of nVars.
               One can ignore pArrTimeProfile by setting it to NULL.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkFindExact( word * pTruth, int nVars, int nFunc, int nMaxDepth, int * pArrTimeProfile, int fVerbose )
{
    Ses_Man_t * pSes;
    char * pSol;
    Abc_Ntk_t * pNtk = NULL;
    abctime timeStart;

    /* some checks */
    assert( nVars >= 2 && nVars <= 8 );

    timeStart = Abc_Clock();

    pSes = Ses_ManAlloc( pTruth, nVars, nFunc, nMaxDepth, pArrTimeProfile, 0, fVerbose );
    if ( fVerbose )
        Ses_ManPrintFuncs( pSes );

    if ( Ses_ManFindMinimumSize( pSes ) )
    {
        pSol = Ses_ManExtractSolution( pSes );
        pNtk = Ses_ManExtractNtk( pSol );
        ABC_FREE( pSol );
    }

    pSes->timeTotal = Abc_Clock() - timeStart;

    if ( fVerbose )
        Ses_ManPrintRuntime( pSes );

    /* cleanup */
    Ses_ManClean( pSes );

    return pNtk;
}

Gia_Man_t * Gia_ManFindExact( word * pTruth, int nVars, int nFunc, int nMaxDepth, int * pArrTimeProfile, int fVerbose )
{
    Ses_Man_t * pSes;
    char * pSol;
    Gia_Man_t * pGia = NULL;
    abctime timeStart;

    /* some checks */
    assert( nVars >= 2 && nVars <= 8 );

    timeStart = Abc_Clock();

    pSes = Ses_ManAlloc( pTruth, nVars, nFunc, nMaxDepth, pArrTimeProfile, 1, fVerbose );
    if ( fVerbose )
        Ses_ManPrintFuncs( pSes );

    if ( Ses_ManFindMinimumSize( pSes ) )
    {
        pSol = Ses_ManExtractSolution( pSes );
        pGia = Ses_ManExtractGia( pSol );
        ABC_FREE( pSol );
    }

    pSes->timeTotal = Abc_Clock() - timeStart;

    if ( fVerbose )
        Ses_ManPrintRuntime( pSes );

    /* cleanup */
    Ses_ManClean( pSes );

    return pGia;
}

/**Function*************************************************************

  Synopsis    [Some test cases.]

***********************************************************************/

Abc_Ntk_t * Abc_NtkFromTruthTable( word * pTruth, int nVars )
{
    Abc_Ntk_t * pNtk;
    Mem_Flex_t * pMan;
    char * pSopCover;

    pMan = Mem_FlexStart();
    pSopCover = Abc_SopCreateFromTruth( pMan, nVars, (unsigned*)pTruth );
    pNtk = Abc_NtkCreateWithNode( pSopCover );
    Abc_NtkShortNames( pNtk );
    Mem_FlexStop( pMan, 0 );

    return pNtk;
}

void Abc_ExactTestSingleOutput( int fVerbose )
{
    extern void Abc_NtkCecSat( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nConfLimit, int nInsLimit );

    word pTruth[4] = {0xcafe, 0, 0, 0};
    Abc_Ntk_t * pNtk, * pNtk2, * pNtk3, * pNtk4;
    int pArrTimeProfile[4] = {6, 2, 8, 5};

    pNtk = Abc_NtkFromTruthTable( pTruth, 4 );

    pNtk2 = Abc_NtkFindExact( pTruth, 4, 1, -1, NULL, fVerbose );
    Abc_NtkShortNames( pNtk2 );
    Abc_NtkCecSat( pNtk, pNtk2, 10000, 0 );
    assert( pNtk2 );
    assert( Abc_NtkNodeNum( pNtk2 ) == 6 );
    Abc_NtkDelete( pNtk2 );

    pNtk3 = Abc_NtkFindExact( pTruth, 4, 1, 3, NULL, fVerbose );
    Abc_NtkShortNames( pNtk3 );
    Abc_NtkCecSat( pNtk, pNtk3, 10000, 0 );
    assert( pNtk3 );
    assert( Abc_NtkLevel( pNtk3 ) <= 3 );
    Abc_NtkDelete( pNtk3 );

    pNtk4 = Abc_NtkFindExact( pTruth, 4, 1, 9, pArrTimeProfile, fVerbose );
    Abc_NtkShortNames( pNtk4 );
    Abc_NtkCecSat( pNtk, pNtk4, 10000, 0 );
    assert( pNtk4 );
    assert( Abc_NtkLevel( pNtk4 ) <= 9 );
    Abc_NtkDelete( pNtk4 );

    assert( !Abc_NtkFindExact( pTruth, 4, 1, 2, NULL, fVerbose ) );

    assert( !Abc_NtkFindExact( pTruth, 4, 1, 8, pArrTimeProfile, fVerbose ) );

    Abc_NtkDelete( pNtk );
}

void Abc_ExactTestSingleOutputAIG( int fVerbose )
{
    word pTruth[4] = {0xcafe, 0, 0, 0};
    Abc_Ntk_t * pNtk;
    Gia_Man_t * pGia, * pGia2, * pGia3, * pGia4, * pMiter;
    Cec_ParCec_t ParsCec, * pPars = &ParsCec;
    int pArrTimeProfile[4] = {6, 2, 8, 5};

    Cec_ManCecSetDefaultParams( pPars );

    pNtk = Abc_NtkFromTruthTable( pTruth, 4 );
    Abc_NtkToAig( pNtk );
    pGia = Abc_NtkAigToGia( pNtk, 1 );

    pGia2 = Gia_ManFindExact( pTruth, 4, 1, -1, NULL, fVerbose );
    pMiter = Gia_ManMiter( pGia, pGia2, 0, 1, 0, 0, 1 );
    assert( pMiter );
    Cec_ManVerify( pMiter, pPars );
    Gia_ManStop( pMiter );

    pGia3 = Gia_ManFindExact( pTruth, 4, 1, 3, NULL, fVerbose );
    pMiter = Gia_ManMiter( pGia, pGia3, 0, 1, 0, 0, 1 );
    assert( pMiter );
    Cec_ManVerify( pMiter, pPars );
    Gia_ManStop( pMiter );

    pGia4 = Gia_ManFindExact( pTruth, 4, 1, 9, pArrTimeProfile, fVerbose );
    pMiter = Gia_ManMiter( pGia, pGia4, 0, 1, 0, 0, 1 );
    assert( pMiter );
    Cec_ManVerify( pMiter, pPars );
    Gia_ManStop( pMiter );

    assert( !Gia_ManFindExact( pTruth, 4, 1, 2, NULL, fVerbose ) );

    assert( !Gia_ManFindExact( pTruth, 4, 1, 8, pArrTimeProfile, fVerbose ) );

    Gia_ManStop( pGia );
    Gia_ManStop( pGia2 );
    Gia_ManStop( pGia3 );
    Gia_ManStop( pGia4 );
}

void Abc_ExactTest( int fVerbose )
{
    Abc_ExactTestSingleOutput( fVerbose );
    Abc_ExactTestSingleOutputAIG( fVerbose );

    printf( "\n" );
}


/**Function*************************************************************

  Synopsis    [APIs for integraging with the mapper.]

***********************************************************************/
// may need to have a static pointer to the SAT-based synthesis engine and/or loaded library
// this procedure should return 1, if the engine/library are available, and 0 otherwise
int Abc_ExactIsRunning()
{
    return s_pSesStore != NULL;
}
// this procedure returns the number of inputs of the library
// for example, somebody may try to map into 10-cuts while the library only contains 8-functions
int Abc_ExactInputNum()
{
    return 8;
}
// start exact store manager
void Abc_ExactStart( int nBTLimit, int fMakeAIG, int fVerbose, const char * pFilename )
{
    if ( !s_pSesStore )
    {
        s_pSesStore = Ses_StoreAlloc( nBTLimit, fMakeAIG, fVerbose );
        if ( pFilename )
            Ses_StoreRead( s_pSesStore, pFilename );
    }
    else
        printf( "BMS manager already started\n" );
}
// stop exact store manager
void Abc_ExactStop( const char * pFilename )
{
    if ( s_pSesStore )
    {
        if ( pFilename )
            Ses_StoreWrite( s_pSesStore, pFilename );
        Ses_StoreClean( s_pSesStore );
    }
    else
        printf( "BMS manager has not been started\n" );
}
// show statistics about store manager
void Abc_ExactStats()
{
    int i;

    if ( !s_pSesStore )
    {
        printf( "BMS manager has not been started\n" );
        return;
    }

    printf( "number of considered cuts :" );
    for ( i = 2; i < 9; ++i )
        printf( " %d = %lu  ", i, s_pSesStore->pCutCount[i] );
    printf( " total = %lu\n", s_pSesStore->nCutCount );
    printf( "cache hits                : %lu\n", s_pSesStore->nCacheHit );
    printf( "number of entries         : %d\n", s_pSesStore->nEntriesCount );
}
// this procedure takes TT and input arrival times (pArrTimeProfile) and return the smallest output arrival time;
// it also returns the pin-to-pin delays (pPerm) between each cut leaf and the cut output and the cut area cost (Cost)
// the area cost should not exceed 2048, if the cut is implementable; otherwise, it should be ABC_INFINITY
int Abc_ExactDelayCost( word * pTruth, int nVars, int * pArrTimeProfile, char * pPerm, int * Cost, int AigLevel )
{
    int i, nDelta, nMaxArrival, l, fExists = 0;
    Ses_Man_t * pSes = NULL;
    char * pSol = NULL, * p;
    int Delay = ABC_INFINITY, nMaxDepth;
    abctime timeStart;

    /* some checks */
    if ( nVars < 0 || nVars > 8 )
    {
        printf( "invalid truth table size %d\n", nVars );
        assert( 0 );
    }

    if ( nVars == 0 )
    {
        *Cost = 0;
        return 0;
    }

    if ( nVars == 1 )
    {
        *Cost = 0;
        pPerm[0] = (char)0;
        return pArrTimeProfile[0];
    }

    nDelta = Abc_NormalizeArrivalTimes( pArrTimeProfile, nVars, &nMaxArrival );

    if ( s_pSesStore->fVerbose )
    {
        printf( "compute delay for nontrivial truth table " );
        Abc_TtPrintHexRev( stdout, pTruth, nVars );
        printf( " with arrival times" );
        for ( l = 0; l < nVars; ++l )
            printf( " %d", pArrTimeProfile[l] );
        printf( "\n" );
    }

    /* statistics */
    s_pSesStore->nCutCount++;
    s_pSesStore->pCutCount[nVars]++;

    pSol = Ses_StoreGetEntry( s_pSesStore, pTruth, nVars, pArrTimeProfile );
    if ( pSol )
    {
        if ( s_pSesStore->fVerbose )
            printf( "  truth table already in store\n" );
        s_pSesStore->nCacheHit++;
        fExists = 1;
    }
    else
    {
        nMaxDepth = pArrTimeProfile[0];
        for ( i = 1; i < nVars; ++i )
            nMaxDepth = Abc_MaxInt( nMaxDepth, pArrTimeProfile[i] );
        nMaxDepth = Abc_MinInt( AigLevel, nMaxDepth + nVars + 1 );

        timeStart = Abc_Clock();

        *Cost = ABC_INFINITY;

        pSes = Ses_ManAlloc( pTruth, nVars, 1 /* fSpecFunc */, nMaxDepth, pArrTimeProfile, s_pSesStore->fMakeAIG, s_pSesStore->fVerbose );
        pSes->nBTLimit = s_pSesStore->nBTLimit;
        pSes->fVeryVerbose = 0;

        while ( 1 ) /* there is improvement */
        {
            if ( Ses_ManFindMinimumSize( pSes ) )
            {
                if ( pSol )
                    ABC_FREE( pSol );
                pSol = Ses_ManExtractSolution( pSes );
                pSes->nMaxDepth--;
            }
            else
                break;
        }

        pSes->timeTotal = Abc_Clock() - timeStart;

        /* cleanup */
        Ses_ManClean( pSes );
    }

    if ( pSol )
    {
        *Cost = pSol[ABC_EXACT_SOL_NGATES];
        p = pSol + 3 + 4 * pSol[ABC_EXACT_SOL_NGATES] + 1;
        Delay = *p++;
        for ( l = 0; l < nVars; ++l )
            pPerm[l] = *p++;

        /* store solution */
        if ( !fExists )
            Ses_StoreAddEntry( s_pSesStore, pTruth, nVars, pArrTimeProfile, pSol );
    }

    //for ( l = 0; l < nVars; ++l )
    //    printf( "pArrTimeProfile[%d] = %d\n", l, pArrTimeProfile[l] );

    if ( pSol )
    {
        int Delay2 = 0;
        for ( l = 0; l < nVars; ++l )
        {
            //printf( "%d ", pPerm[l] );
            Delay2 = Abc_MaxInt( Delay2, pArrTimeProfile[l] + pPerm[l] );
        }
        //printf( "  output arrival = %d    recomputed = %d\n", Delay, Delay2 );
        if ( Delay != Delay2 )
        {
            printf( "^--- BUG!\n" );
            assert( 0 );
        }
        //Delay = Delay2;
    }

    Abc_UnnormalizeArrivalTimes( pArrTimeProfile, nVars, nDelta );

    return nDelta + Delay;
}
// this procedure returns a new node whose output in terms of the given fanins
// has the smallest possible arrival time (in agreement with the above Abc_ExactDelayCost)
Abc_Obj_t * Abc_ExactBuildNode( word * pTruth, int nVars, int * pArrTimeProfile, Abc_Obj_t ** pFanins, Abc_Ntk_t * pNtk )
{
    char * pSol;
    int i, j, nDelta, nMaxArrival;
    char const * p;
    Abc_Obj_t * pObj;
    Vec_Ptr_t * pGates;
    char pGateTruth[5];
    char * pSopCover;

    if ( nVars == 0 )
        return (pTruth[0] & 1) ? Abc_NtkCreateNodeConst1(pNtk) : Abc_NtkCreateNodeConst0(pNtk);
    if ( nVars == 1 )
        return (pTruth[0] & 1) ? Abc_NtkCreateNodeInv(pNtk, pFanins[0]) : Abc_NtkCreateNodeBuf(pNtk, pFanins[0]);

    nDelta = Abc_NormalizeArrivalTimes( pArrTimeProfile, nVars, &nMaxArrival );
    pSol = Ses_StoreGetEntry( s_pSesStore, pTruth, nVars, pArrTimeProfile );
    Abc_UnnormalizeArrivalTimes( pArrTimeProfile, nVars, nDelta );
    if ( !pSol )
        return NULL;

    assert( pSol[ABC_EXACT_SOL_NVARS] == nVars );
    assert( pSol[ABC_EXACT_SOL_NFUNC] == 1 );

    pGates = Vec_PtrAlloc( nVars + pSol[ABC_EXACT_SOL_NGATES] );
    pGateTruth[3] = '0';
    pGateTruth[4] = '\0';

    /* primary inputs */
    for ( i = 0; i < nVars; ++i )
    {
        Vec_PtrPush( pGates, pFanins[i] );
    }

    /* gates */
    p = pSol + 3;
    for ( i = 0; i < pSol[ABC_EXACT_SOL_NGATES]; ++i )
    {
        pGateTruth[2] = '0' + ( *p & 1 );
        pGateTruth[1] = '0' + ( ( *p >> 1 ) & 1 );
        pGateTruth[0] = '0' + ( ( *p >> 2 ) & 1 );
        ++p;

        assert( *p == 2 ); /* binary gate */
        ++p;

        /* invert truth table if we are last gate and inverted */
        if ( i + 1 == pSol[ABC_EXACT_SOL_NGATES] && Abc_LitIsCompl( *( p + 2 ) ) )
            for ( j = 0; j < 4; ++j )
                pGateTruth[j] = ( pGateTruth[j] == '0' ) ? '1' : '0';

        pSopCover = Abc_SopFromTruthBin( pGateTruth );
        pObj = Abc_NtkCreateNode( pNtk );
        pObj->pData = Abc_SopRegister( (Mem_Flex_t*)pNtk->pManFunc, pSopCover );
        Vec_PtrPush( pGates, pObj );
        ABC_FREE( pSopCover );

        Abc_ObjAddFanin( pObj, (Abc_Obj_t *)Vec_PtrEntry( pGates, *p++ ) );
        Abc_ObjAddFanin( pObj, (Abc_Obj_t *)Vec_PtrEntry( pGates, *p++ ) );
    }

    /* output */
    pObj = (Abc_Obj_t *)Vec_PtrEntry( pGates, nVars + Abc_Lit2Var( *p ) );

    Vec_PtrFree( pGates );

    return pObj;
}

void Abc_ExactStoreTest( int fVerbose )
{
    int i;
    word pTruth[4] = {0xcafe, 0, 0, 0};
    int pArrTimeProfile[4] = {6, 2, 8, 5};
    Abc_Ntk_t * pNtk;
    Abc_Obj_t * pFanins[4];
    Vec_Ptr_t * vNames;
    char pPerm[4];
    int Cost;

    pNtk = Abc_NtkAlloc( ABC_NTK_LOGIC, ABC_FUNC_SOP, 1 );
    pNtk->pName = Extra_UtilStrsav( "exact" );
    vNames = Abc_NodeGetFakeNames( 4u );

    /* primary inputs */
    Vec_PtrPush( pNtk->vObjs, NULL );
    for ( i = 0; i < 4; ++i )
    {
        pFanins[i] = Abc_NtkCreatePi( pNtk );
        Abc_ObjAssignName( pFanins[i], (char*)Vec_PtrEntry( vNames, i ), NULL );
    }
    Abc_NodeFreeNames( vNames );

    Abc_ExactStart( 10000, 1, fVerbose, NULL );

    assert( !Abc_ExactBuildNode( pTruth, 4, pArrTimeProfile, pFanins, pNtk ) );

    assert( Abc_ExactDelayCost( pTruth, 4, pArrTimeProfile, pPerm, &Cost, 12 ) == 1 );

    assert( Abc_ExactBuildNode( pTruth, 4, pArrTimeProfile, pFanins, pNtk ) );

    (*pArrTimeProfile)++;
    assert( !Abc_ExactBuildNode( pTruth, 4, pArrTimeProfile, pFanins, pNtk ) );
    (*pArrTimeProfile)--;

    Abc_ExactStop( NULL );

    Abc_NtkDelete( pNtk );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
