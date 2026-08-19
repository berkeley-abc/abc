/**CFile****************************************************************

  FileName    [fm_camus_api_test.c]

  Synopsis    [Direct in-process API test for ForMACE CAMUS-style MUS support.]

***********************************************************************/

#include "formace_ext/fm_camus.h"
#include "sat/bsat/satSolver.h"
#include <string.h>

static int Fm_TestIsMus( Fm_CamusMan_t * p, Vec_Int_t * vMus )
{
    Vec_Int_t * vTrial;
    int i;
    if ( vMus == NULL || Fm_CamusSolve(p, vMus) != l_False )
        return 0;
    for ( i = 0; i < Vec_IntSize(vMus); i++ )
    {
        vTrial = Vec_IntDup( vMus );
        Vec_IntDrop( vTrial, i );
        if ( Fm_CamusSolve(p, vTrial) != l_True )
        {
            Vec_IntFree( vTrial );
            return 0;
        }
        Vec_IntFree( vTrial );
    }
    return 1;
}

static int Fm_TestRootUnsat( void )
{
    Fm_CamusMan_t * p = Fm_CamusStart( 1, 1 );
    Vec_Int_t * vAll = NULL, * vMus = NULL, * vMinimum = NULL;
    int RetValue = 0;
    if ( p == NULL || !Fm_CamusAddBackground(p, NULL, 0) )
        goto finish;
    vAll = Vec_IntStartNatural( 1 );
    if ( Fm_CamusSolve(p, vAll) != l_False )
        goto finish;
    vMus = Fm_CamusFindMus( p, vAll );
    vMinimum = Fm_CamusFindMinimumMus( p, vAll );
    RetValue = vMus != NULL && Vec_IntSize(vMus) == 0 &&
               vMinimum != NULL && Vec_IntSize(vMinimum) == 0;
finish:
    Vec_IntFreeP( &vMinimum );
    Vec_IntFreeP( &vMus );
    Vec_IntFreeP( &vAll );
    Fm_CamusStop( p );
    return RetValue;
}

static int Fm_TestInvalidLiteral( void )
{
    Fm_CamusMan_t * p = Fm_CamusStart( 1, 1 );
    int Lit = -1;
    int RetValue = p != NULL && !Fm_CamusAddBackground(p, &Lit, 1);
    Fm_CamusStop( p );
    return RetValue;
}

static int Fm_TestPopCount( unsigned Mask )
{
    int Count = 0;
    while ( Mask )
        Count += Mask & 1, Mask >>= 1;
    return Count;
}

static int Fm_TestMinimumAgainstBruteForce( void )
{
    Fm_CamusMan_t * p = NULL;
    Vec_Int_t * vAll = NULL, * vTrial = NULL, * vMinimum = NULL;
    int Lits[6], Unit, i, k, Case, ClauseSize, Best, RetValue = 0;
    unsigned Mask;
    for ( Case = 0; Case < 16; Case++ )
    {
        ClauseSize = 2 + Case % 4;
        p = Fm_CamusStart( 6, 6 );
        if ( p == NULL )
            goto finish;
        for ( k = 0; k < 3; k++ )
        {
            for ( i = 0; i < ClauseSize; i++ )
                Lits[i] = toLitCond( (i + 2 * k + Case) % 6, 1 );
            if ( !Fm_CamusAddBackground(p, Lits, ClauseSize) )
                goto finish;
        }
        for ( i = 0; i < 6; i++ )
        {
            Unit = toLit( i );
            if ( !Fm_CamusAddGroup(p, i, &Unit, 1) )
                goto finish;
        }
        vAll = Vec_IntStartNatural( 6 );
        Best = 7;
        for ( Mask = 0; Mask < (1u << 6); Mask++ )
        {
            if ( Fm_TestPopCount(Mask) >= Best )
                continue;
            vTrial = Vec_IntAlloc( 6 );
            for ( i = 0; i < 6; i++ )
                if ( Mask & (1u << i) )
                    Vec_IntPush( vTrial, i );
            if ( Fm_CamusSolve(p, vTrial) == l_False )
                Best = Vec_IntSize( vTrial );
            Vec_IntFree( vTrial );
            vTrial = NULL;
        }
        vMinimum = Fm_CamusFindMinimumMus( p, vAll );
        if ( vMinimum == NULL || Vec_IntSize(vMinimum) != Best || !Fm_TestIsMus(p, vMinimum) )
            goto finish;
        Vec_IntFree( vMinimum );
        Vec_IntFree( vAll );
        Fm_CamusStop( p );
        vMinimum = vAll = NULL;
        p = NULL;
    }
    RetValue = 1;

finish:
    Vec_IntFreeP( &vMinimum );
    Vec_IntFreeP( &vTrial );
    Vec_IntFreeP( &vAll );
    Fm_CamusStop( p );
    return RetValue;
}

#define FM_TEST_MAX_VARS    5
#define FM_TEST_MAX_GROUPS  7
#define FM_TEST_MAX_CLAUSES 24
#define FM_TEST_MAX_LITS    3

typedef struct Fm_TestClause_t_
{
    int iGroup;
    int nLits;
    int Lits[FM_TEST_MAX_LITS];
} Fm_TestClause_t;

typedef struct Fm_TestFormula_t_
{
    int nVars;
    int nGroups;
    int nClauses;
    Fm_TestClause_t Clauses[FM_TEST_MAX_CLAUSES];
} Fm_TestFormula_t;

static unsigned Fm_TestRandom( unsigned * pState )
{
    *pState = *pState * 1664525u + 1013904223u;
    return *pState;
}

/** Evaluates the grouped formula exhaustively, without using either SAT API. */
static int Fm_TestFormulaIsSat( Fm_TestFormula_t * p, unsigned GroupMask )
{
    unsigned Assignment;
    int c, i;
    for ( Assignment = 0; Assignment < (1u << p->nVars); Assignment++ )
    {
        for ( c = 0; c < p->nClauses; c++ )
        {
            Fm_TestClause_t * pClause = &p->Clauses[c];
            int fSatisfied = 0;
            if ( pClause->iGroup >= 0 && !(GroupMask & (1u << pClause->iGroup)) )
                continue;
            for ( i = 0; i < pClause->nLits; i++ )
            {
                int Lit = pClause->Lits[i];
                int Value = (Assignment >> Abc_Lit2Var(Lit)) & 1;
                if ( Value != Abc_LitIsCompl(Lit) )
                {
                    fSatisfied = 1;
                    break;
                }
            }
            if ( !fSatisfied )
                break;
        }
        if ( c == p->nClauses )
            return 1;
    }
    return 0;
}

static int Fm_TestAddRandomClause( Fm_TestFormula_t * p, Fm_CamusMan_t * pCamus,
                                   int iGroup, int nLits, unsigned * pState )
{
    Fm_TestClause_t * pClause;
    int i;
    if ( p->nClauses == FM_TEST_MAX_CLAUSES )
        return 0;
    pClause = &p->Clauses[p->nClauses++];
    pClause->iGroup = iGroup;
    pClause->nLits = nLits;
    for ( i = 0; i < nLits; i++ )
        pClause->Lits[i] = Abc_Var2Lit( Fm_TestRandom(pState) % p->nVars,
                                       Fm_TestRandom(pState) & 1 );
    return iGroup < 0 ?
        Fm_CamusAddBackground( pCamus, pClause->Lits, pClause->nLits ) :
        Fm_CamusAddGroup( pCamus, iGroup, pClause->Lits, pClause->nLits );
}

/**
 * Cross-checks CAMUS minimum cardinality against an independent exhaustive
 * truth-assignment/subset oracle.  Candidate vectors are intentionally sparse
 * to exercise the non-contiguous group IDs used after runeco accumulates old
 * support.
 */
static int Fm_TestRandomMinimumAgainstIndependentOracle( const Fm_CamusOptions_t * pOptions,
                                                          const char * pVariant )
{
    unsigned State = 0x5170811u;
    int Case;
    for ( Case = 0; Case < 512; Case++ )
    {
        Fm_TestFormula_t Formula = {0};
        Fm_CamusMan_t * pCamus = NULL;
        Vec_Int_t * vCandidates = NULL, * vMinimum = NULL;
        unsigned CandidateMask = 0, ResultMask = 0, SubMask;
        int nBackground, i, k, Best, RetValue = 0;

        Formula.nVars = 1 + Fm_TestRandom(&State) % FM_TEST_MAX_VARS;
        Formula.nGroups = 1 + Fm_TestRandom(&State) % FM_TEST_MAX_GROUPS;
        pCamus = Fm_CamusStartWithOptions( Formula.nVars, Formula.nGroups, pOptions );
        vCandidates = Vec_IntAlloc( Formula.nGroups );
        if ( pCamus == NULL )
            goto case_finish;

        nBackground = Fm_TestRandom(&State) % 4;
        for ( i = 0; i < nBackground; i++ )
            if ( !Fm_TestAddRandomClause(&Formula, pCamus, -1,
                    1 + Fm_TestRandom(&State) % FM_TEST_MAX_LITS, &State) )
                goto case_finish;
        for ( i = 0; i < Formula.nGroups; i++ )
        {
            int nGroupClauses = 1 + Fm_TestRandom(&State) % 2;
            for ( k = 0; k < nGroupClauses; k++ )
                if ( !Fm_TestAddRandomClause(&Formula, pCamus, i,
                        1 + Fm_TestRandom(&State) % FM_TEST_MAX_LITS, &State) )
                    goto case_finish;
            if ( Fm_TestRandom(&State) & 1 )
                CandidateMask |= 1u << i;
        }
        if ( CandidateMask == 0 && (Fm_TestRandom(&State) & 1) )
            CandidateMask = 1u << (Fm_TestRandom(&State) % Formula.nGroups);
        for ( i = 0; i < Formula.nGroups; i++ )
            if ( CandidateMask & (1u << i) )
                Vec_IntPush( vCandidates, i );

        Best = Formula.nGroups + 1;
        SubMask = CandidateMask;
        while ( 1 )
        {
            if ( Fm_TestPopCount(SubMask) < Best && !Fm_TestFormulaIsSat(&Formula, SubMask) )
                Best = Fm_TestPopCount( SubMask );
            if ( SubMask == 0 )
                break;
            SubMask = (SubMask - 1) & CandidateMask;
        }

        vMinimum = Fm_CamusFindMinimumMus( pCamus, vCandidates );
        if ( Best > Formula.nGroups )
        {
            if ( vMinimum != NULL )
                goto case_finish;
        }
        else
        {
            if ( vMinimum == NULL || Vec_IntSize(vMinimum) != Best )
                goto case_finish;
            Vec_IntForEachEntry( vMinimum, i, k )
            {
                if ( !(CandidateMask & (1u << i)) )
                    goto case_finish;
                ResultMask |= 1u << i;
            }
            if ( Fm_TestFormulaIsSat(&Formula, ResultMask) )
                goto case_finish;
        }
        RetValue = 1;

case_finish:
        Vec_IntFreeP( &vMinimum );
        Vec_IntFreeP( &vCandidates );
        Fm_CamusStop( pCamus );
        if ( !RetValue )
        {
            fprintf( stderr, "independent minimum-cardinality oracle failed for %s on random case %d\n",
                     pVariant, Case );
            return 0;
        }
    }
    return 1;
}

int main( void )
{
    Fm_CamusMan_t * p;
    Vec_Int_t * vAll = NULL, * vMus = NULL, * vMinimum = NULL, * vOne = NULL;
    int vBackgroundSmall[2] = { toLitCond(0, 1), toLitCond(1, 1) };
    int vBackgroundLarge[3] = { toLitCond(2, 1), toLitCond(3, 1), toLitCond(4, 1) };
    int vGroupA[1] = { toLit(0) };
    int vGroupB[1] = { toLit(1) };
    int vGroupC[1] = { toLit(2) };
    int vGroupD[1] = { toLit(3) };
    int vGroupE[1] = { toLit(4) };
    /* Deliberately exceeds 32 bits: verifies the ABC_INT64_T limit path. */
    ABC_INT64_T nConfLimit = (ABC_INT64_T)ABC_CONST(4294967296);
    const char * pVariants[] = { "full", "no-core-shrink", "no-mus-seed",
        "core-only-seed", "no-model-absorb", "no-mss-growth", "linear-map-bounds",
        "default-cadical", "cadical-preprocessing", "cadical-no-ilb",
        "cadical-default-phases", "cadical-preprocessing-no-ilb",
        "cadical-preprocessing-default-phases", "cadical-no-ilb-default-phases" };
    int nVariants = sizeof(pVariants) / sizeof(pVariants[0]);
    int RetValue = 1, Variant;

    if ( strncmp(Fm_CamusBackendName(), "cadical-", 8) )
        return 1;
    if ( !Fm_TestInvalidLiteral() )
        return 1;
    if ( !Fm_TestMinimumAgainstBruteForce() )
        return 1;
    for ( Variant = 0; Variant < nVariants; Variant++ )
    {
        Fm_CamusOptions_t Options;
        Fm_CamusOptionsDefault( &Options );
        if ( !strcmp(pVariants[Variant], "no-core-shrink") )
            Options.fUseCoreShrink = 0;
        else if ( !strcmp(pVariants[Variant], "no-mus-seed") )
            Options.fUseMusSeed = 0;
        else if ( !strcmp(pVariants[Variant], "core-only-seed") )
            Options.fMinimizeSeed = 0;
        else if ( !strcmp(pVariants[Variant], "no-model-absorb") )
            Options.fUseModelAbsorb = 0;
        else if ( !strcmp(pVariants[Variant], "no-mss-growth") )
            Options.fGrowMcs = 0;
        else if ( !strcmp(pVariants[Variant], "linear-map-bounds") )
            Options.fBinaryMapBounds = 0;
        else if ( !strcmp(pVariants[Variant], "default-cadical") )
            Options.fUseCadicalTuning = 0;
        else if ( !strcmp(pVariants[Variant], "cadical-preprocessing") )
            Options.fUseCadicalPlain = 0;
        else if ( !strcmp(pVariants[Variant], "cadical-no-ilb") )
            Options.fUseCadicalIlb = 0;
        else if ( !strcmp(pVariants[Variant], "cadical-default-phases") )
            Options.fUseCadicalStableOnly = 0;
        else if ( !strcmp(pVariants[Variant], "cadical-preprocessing-no-ilb") )
        {
            Options.fUseCadicalPlain = 0;
            Options.fUseCadicalIlb = 0;
        }
        else if ( !strcmp(pVariants[Variant], "cadical-preprocessing-default-phases") )
        {
            Options.fUseCadicalPlain = 0;
            Options.fUseCadicalStableOnly = 0;
        }
        else if ( !strcmp(pVariants[Variant], "cadical-no-ilb-default-phases") )
        {
            Options.fUseCadicalIlb = 0;
            Options.fUseCadicalStableOnly = 0;
        }
        if ( !Fm_TestRandomMinimumAgainstIndependentOracle(&Options, pVariants[Variant]) )
            return 1;
    }
    p = Fm_CamusStart( 5, 5 );
    if ( p == NULL ||
         !Fm_CamusAddBackground(p, vBackgroundSmall, 2) ||
         !Fm_CamusAddBackground(p, vBackgroundLarge, 3) ||
         !Fm_CamusAddGroup(p, 0, vGroupA, 1) ||
         !Fm_CamusAddGroup(p, 1, vGroupB, 1) ||
         !Fm_CamusAddGroup(p, 2, vGroupC, 1) ||
         !Fm_CamusAddGroup(p, 3, vGroupD, 1) ||
         !Fm_CamusAddGroup(p, 4, vGroupE, 1) )
        goto finish;
    Fm_CamusSetLimits( p, nConfLimit, 0 );

    vAll = Vec_IntStartNatural( 5 );
    if ( Fm_CamusSolve(p, vAll) != l_False )
        goto finish_all;
    vMus = Fm_CamusFindMus( p, vAll );
    if ( !Fm_TestIsMus(p, vMus) || Vec_IntSize(vMus) != 2 )
        goto finish_mus;
    vMinimum = Fm_CamusFindMinimumMus( p, vAll );
    if ( !Fm_TestIsMus(p, vMinimum) || Vec_IntSize(vMinimum) != 2 )
        goto finish_minimum;

    vOne = Vec_IntAlloc( 1 );
    Vec_IntPush( vOne, 0 );
    Fm_CamusSetLimits( p, nConfLimit, Abc_Clock() - 1 );
    if ( Fm_CamusSolve(p, vOne) != l_Undef )
        goto finish_one;
    Fm_CamusSetLimits( p, nConfLimit, 0 );
    if ( Fm_CamusSolve(p, vOne) != l_True )
        goto finish_one;
    if ( !Fm_TestRootUnsat() )
        goto finish_one;
    Vec_IntWriteEntry( vOne, 0, 1 );
    if ( Fm_CamusSolve(p, vOne) != l_True )
        goto finish_one;

    printf( "fm_camus direct API test passed with backend %s, %d variants x 512 independent exhaustive-oracle cases, 64-bit conflict/timeout/root-UNSAT checks: MUS size = %d; minimum MUS size = %d.\n",
            Fm_CamusBackendName(), nVariants, Vec_IntSize(vMus), Vec_IntSize(vMinimum) );
    RetValue = 0;

finish_one:
    Vec_IntFree( vOne );
finish_minimum:
    Vec_IntFree( vMinimum );
finish_mus:
    Vec_IntFree( vMus );
finish_all:
    Vec_IntFree( vAll );
finish:
    Fm_CamusStop( p );
    return RetValue;
}
