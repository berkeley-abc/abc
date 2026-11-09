/**CFile****************************************************************

  FileName    [bmcCas.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based bounded model checking.]

  Synopsis    [Exact synthesis of single-rail LUT cascades.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 26, 2026.]

  Revision    [$Id: bmcCas.c,v 1.00 2026/10/26 00:00:00 alanmi Exp $]

***********************************************************************/

#include "bmc.h"
#include "bmcExact.h"
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/cmd/cmd.h"
#include "misc/extra/extra.h"
#include "misc/util/utilTruth.h"
#include "sat/kissat/kissat.h"
#include "sat/cadical/ccadical.h"
#include <errno.h>
#include <limits.h>

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define CAS_MAX_VARS  14
#define CAS_MAX_LUT    8
#define CAS_MAX_NODES 64
#define CAS_SAT       10
#define CAS_UNSAT     20

typedef struct Bmc_CasMan_t_ Bmc_CasMan_t;
struct Bmc_CasMan_t_
{
    Bmc_EsPar_t * pPars;
    int nVars, nNodes, nLutSize, nMints, nRows, nWords, fCompl, fFixed;
    int iNext;
    int fDirectFinal;
    unsigned nConfLimit;                 // nonzero only for internal template probes
    int Select[CAS_MAX_NODES][CAS_MAX_VARS];
    int CofBase[CAS_MAX_NODES][2];
    int ValBase[CAS_MAX_NODES];
    int Fixed[CAS_MAX_NODES][CAS_MAX_LUT]; // ascending PI positions; -1 = free
    int Fans[CAS_MAX_NODES][CAS_MAX_LUT];  // pin 0 is the rail after stage 0
    word Truths[CAS_MAX_NODES][4];        // normalized local LUT functions
    word * pTruth;                       // normalized specification
    int * pCanon;                       // canonical input by symmetry class
    int * pRows;                        // representative global minterms
    int * pRowIds;                      // dense row IDs for representative inputs
    int * pCofIds[CAS_MAX_NODES];         // dense indices of local representatives
    kissat * pSat;
    CCaDiCaL * pCadical;
    abctime timeStop;
    word nClauses, nLiterals;
};

typedef struct Bmc_CasProbe_t_ Bmc_CasProbe_t;
struct Bmc_CasProbe_t_
{
    int fBackwardTried, nFound, fRanked, nRank;
    int Fans[CAS_MAX_NODES*CAS_MAX_LUT], Masks[8];
    word Tables[CAS_MAX_NODES*4];
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Starts the selected bundled solver without changing global options.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_CasSolverStart( Bmc_CasMan_t * p )
{
    if ( p->pPars->fCadical )
    {
        p->pCadical = ccadical_init();
        ccadical_set_option(p->pCadical, "seed", p->pPars->Seed);
    }
    else p->pSat = kissat_init();
}

/**Function*************************************************************

  Synopsis    [Reserves the current variable range in the selected solver.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_CasReserve( Bmc_CasMan_t * p )
{
    if ( p->pCadical ) ccadical_resize(p->pCadical, p->iNext);
    else kissat_reserve(p->pSat, p->iNext);
}

/**Function*************************************************************

  Synopsis    [Releases the selected solver.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_CasSolverStop( Bmc_CasMan_t * p )
{
    if ( p->pCadical ) ccadical_release(p->pCadical);
    else kissat_release(p->pSat);
}

/**Function*************************************************************

  Synopsis    [Adds a clause after simplifying constants and duplicate literals.]

  Description [Internal literals 0 and 1 are constants. SAT variable 0 is unused.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_CasClause( Bmc_CasMan_t * p, const int * pLits, int nLits )
{
    int Lits[CAS_MAX_NODES], n = 0, i, j;
    assert( nLits <= CAS_MAX_NODES );
    for ( i = 0; i < nLits; ++i )
    {
        if ( pLits[i] == 1 ) return;
        if ( pLits[i] == 0 ) continue;
        for ( j = 0; j < n; ++j )
        {
            if ( Lits[j] == (pLits[i] ^ 1) ) return;
            if ( Lits[j] == pLits[i] ) break;
        }
        if ( j == n ) Lits[n++] = pLits[i];
    }
    for ( i = 0; i < n; ++i )
    {
        int Lit = (Lits[i] & 1) ? -(Abc_Lit2Var(Lits[i])+1) : Abc_Lit2Var(Lits[i])+1;
        if ( p->pCadical ) ccadical_add(p->pCadical, Lit);
        else kissat_add(p->pSat, Lit);
    }
    if ( p->pCadical ) ccadical_add(p->pCadical, 0);
    else kissat_add(p->pSat, 0);
    p->nClauses++;
    p->nLiterals += n;
}

/**Function*************************************************************

  Synopsis    [Adds a unit clause.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_CasUnit( Bmc_CasMan_t * p, int a )
{
    Bmc_CasClause( p, &a, 1 );
}

/**Function*************************************************************

  Synopsis    [Adds a binary clause.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_CasBinary( Bmc_CasMan_t * p, int a, int b )
{
    int Lits[2] = { a, b };
    Bmc_CasClause( p, Lits, 2 );
}

/**Function*************************************************************

  Synopsis    [Adds a ternary clause.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_CasTernary( Bmc_CasMan_t * p, int a, int b, int c )
{
    int Lits[3] = { a, b, c };
    Bmc_CasClause( p, Lits, 3 );
}

/**Function*************************************************************

  Synopsis    [Computes the local truth-table address for a fixed PI assignment.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasFixedAddress( Bmc_CasMan_t * p, int i, int x )
{
    int k, Address = 0;
    for ( k = 0; k < p->nLutSize-(i > 0); ++k )
        Address = (Address << 1) | ((x >> p->Fixed[i][k]) & 1);
    return Address;
}

/**Function*************************************************************

  Synopsis    [Returns a fixed-template cofactor literal.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasFixedCofactor( Bmc_CasMan_t * p, int i, int b, int x )
{
    int Address;
    if ( p->pCanon ) x = p->pCanon[x];
    Address = Bmc_CasFixedAddress(p, i, x);
    if ( p->pCofIds[i] ) Address = p->pCofIds[i][Address];
    return Abc_Var2Lit(p->CofBase[i][b]+Address, 0);
}

/**Function*************************************************************

  Synopsis    [Returns a stage output literal or the specified final output.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasValue( Bmc_CasMan_t * p, int i, int x )
{
    if ( i == p->nNodes-1 ) return Abc_TtGetBit(p->pTruth, x);
    if ( p->fFixed && i == 0 ) return Bmc_CasFixedCofactor(p, i, 0, x);
    return Abc_Var2Lit(p->ValBase[i]+(p->pRowIds ? p->pRowIds[x] : x), 0);
}

/**Function*************************************************************

  Synopsis    [Returns a stage cofactor literal.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasCofactor( Bmc_CasMan_t * p, int i, int b, int x )
{
    if ( (p->fFixed || (p->fDirectFinal && i == p->nNodes-1)) && (i || p->nNodes > 1) ) return Bmc_CasFixedCofactor(p, i, b, x);
    return i == 0 ? Bmc_CasValue(p, i, x) : Abc_Var2Lit(p->CofBase[i][b]+x, 0);
}

/**Function*************************************************************

  Synopsis    [Constrains a stage to select exactly the required number of PIs.]

  Description [Prefix thresholds C[i,j] <=> at least j of the first i PI selectors.
               C[i,j] = C[i-1,j] OR (C[i-1,j-1] AND S[i-1]).
               A fixed PI at position r additionally requires exactly r preceding PIs.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_CasExactly( Bmc_CasMan_t * p, int iStage, int k )
{
    int Prev[CAS_MAX_LUT+2] = {1}, Next[CAS_MAX_LUT+2];
    int i, j, r, a, b, c, v;
    for ( i = 0; i < p->nVars; ++i )
    {
        v = Abc_Var2Lit(p->Select[iStage][i], 0);
        for ( r = 0; r < k; ++r )
            if ( p->Fixed[iStage][r] == i )
            {
                Bmc_CasUnit(p, v);
                Bmc_CasUnit(p, Prev[r]);
                Bmc_CasUnit(p, Prev[r+1] ^ 1);
            }
        Next[0] = 1;
        for ( j = 1; j <= k+1; ++j )
        {
            if ( j > i+1 ) { Next[j] = 0; continue; }
            a = Prev[j]; b = Prev[j-1];
            c = Next[j] = Abc_Var2Lit(p->iNext++, 0);
            Bmc_CasBinary(p, a ^ 1, c);
            Bmc_CasTernary(p, b ^ 1, v ^ 1, c);
            Bmc_CasTernary(p, c ^ 1, a, b);
            Bmc_CasTernary(p, c ^ 1, a, v);
        }
        for ( j = 0; j <= k+1; ++j ) Prev[j] = Next[j];
    }
    Bmc_CasUnit(p, Prev[k]);
    Bmc_CasUnit(p, Prev[k+1] ^ 1);
}

/**Function*************************************************************

  Synopsis    [Orders interchangeable PI selector columns lexicographically.]

  Description [Symmetric PIs may be renamed if each template is preserved. In a stage,
               two PIs are interchangeable if both are fixed, or if both lie in the same
               interval between fixed PIs. Order the selector columns within each such
               class lexicographically, removing equivalent input renamings without
               restricting the possible cascade functions.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_CasOrderInputs( Bmc_CasMan_t * p )
{
    int Codes[CAS_MAX_VARS][CAS_MAX_NODES];
    int i, j, l, k, Code, a, b, Prefix, Next;
    if ( !p->pPars->pSymStr ) return;
    for ( j = 0; j < p->nVars; ++j )
    for ( i = 0; i < p->nNodes; ++i )
    {
        Code = 0;
        for ( k = 0; k < p->nLutSize-(i > 0); ++k )
        {
            if ( p->Fixed[i][k] < 0 ) continue;
            if ( p->Fixed[i][k] == j ) { Code = CAS_MAX_LUT+1; break; }
            if ( p->Fixed[i][k] < j ) Code++;
        }
        Codes[j][i] = Code;
    }
    for ( j = 1; j < p->nVars; ++j )
    {
        for ( l = j-1; l >= 0; --l )
        {
            for ( i = 0; i < p->nNodes; ++i )
                if ( Codes[j][i] != Codes[l][i] ) break;
            if ( i == p->nNodes ) break;
        }
        if ( l < 0 ) continue;
        Prefix = 1;
        for ( i = 0; i < p->nNodes; ++i )
        {
            a = Abc_Var2Lit(p->Select[i][l], 0);
            b = Abc_Var2Lit(p->Select[i][j], 0);
            Bmc_CasTernary(p, Prefix ^ 1, a, b ^ 1);
            if ( i == p->nNodes-1 ) break;
            Next = Abc_Var2Lit(p->iNext++, 0);
            // Equal prefixes must stay active. After a > b, Next may be false.
            Bmc_CasTernary(p, Prefix ^ 1, a, Next);
            Bmc_CasTernary(p, Prefix ^ 1, b ^ 1, Next);
            Prefix = Next;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Eliminates the mux relation at a fixed final-stage PI set.]

  Description [A nonconstant target cofactor forces the two final LUT
               cofactors to differ, and fixes the incoming rail up to their
               common phase. A constant target cofactor can set both LUT
               cofactors to that constant without constraining the prefix.
               The decoder still reads the original LUT-cofactor variables.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasDirectFinal( Bmc_CasMan_t * p, int i )
{
    int Seen[1 << (CAS_MAX_LUT-1)] = {0};
    int Done[1 << (CAS_MAX_LUT-1)] = {0};
    int k, x, r, Address, F, a, b, Rail;
    if ( !p->fDirectFinal || i != p->nNodes-1 || i == 0 ) return 0;
    for ( k = 0; k < p->nLutSize-1; ++k )
        if ( p->Fixed[i][k] < 0 ) return 0;
    for ( x = 0; x < p->nMints; ++x )
        Seen[Bmc_CasFixedAddress(p, i, x)] |= 1 << Abc_TtGetBit(p->pTruth, x);
    for ( r = 0; r < p->nRows; ++r )
    {
        x = p->pRows ? p->pRows[r] : r;
        Address = Bmc_CasFixedAddress(p, i, x);
        F = Abc_TtGetBit(p->pTruth, x);
        a = Bmc_CasCofactor(p, i, 0, x);
        b = Bmc_CasCofactor(p, i, 1, x);
        if ( !Done[Address] )
        {
            if ( Seen[Address] == 3 )
            {
                Bmc_CasBinary(p, a, b);
                Bmc_CasBinary(p, a ^ 1, b ^ 1);
            }
            else
            {
                Bmc_CasUnit(p, a ^ !F);
                Bmc_CasUnit(p, b ^ !F);
            }
        }
        Done[Address] = 1;
        if ( Seen[Address] != 3 ) continue;
        Rail = Bmc_CasValue(p, i-1, x);
        Bmc_CasBinary(p, Rail ^ 1, a ^ F);
        Bmc_CasBinary(p, Rail, a ^ F ^ 1);
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Connects stage cofactors through the incoming rail.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_CasMuxes( Bmc_CasMan_t * p, int i )
{
    int r, x, a, c, d, z;
    if ( Bmc_CasDirectFinal(p, i) ) return;
    // z_i(x) = z_(i-1)(x) ? h_i^1(x) : h_i^0(x).
    for ( r = 0; r < p->nRows; ++r )
    {
        x = p->pRows ? p->pRows[r] : r;
        a = Bmc_CasValue(p, i-1, x);
        c = Bmc_CasCofactor(p, i, 0, x);
        d = Bmc_CasCofactor(p, i, 1, x);
        z = Bmc_CasValue(p, i, x);
        Bmc_CasTernary(p, a ^ 1, d ^ 1, z);
        Bmc_CasTernary(p, a ^ 1, d, z ^ 1);
        Bmc_CasTernary(p, a, c ^ 1, z);
        Bmc_CasTernary(p, a, c, z ^ 1);
        if ( p->fFixed )
        {
            // Consensus clauses propagate when the two cofactors agree,
            // even before the incoming rail has a value.
            Bmc_CasTernary(p, c ^ 1, d ^ 1, z);
            Bmc_CasTernary(p, c, d, z ^ 1);
        }
    }
}

/**Function*************************************************************

  Synopsis    [Adds optional consensus clauses for the rail multiplexers.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_CasMuxConsensus( Bmc_CasMan_t * p )
{
    int i, r, x, c, d, z;
    // The fixed symmetric encoding already includes these clauses.
    if ( p->fFixed ) return;
    for ( i = 1; i < p->nNodes; ++i )
    for ( r = 0; r < p->nRows; ++r )
    {
        x = p->pRows ? p->pRows[r] : r;
        c = Bmc_CasCofactor(p, i, 0, x);
        d = Bmc_CasCofactor(p, i, 1, x);
        z = Bmc_CasValue(p, i, x);
        // Equal cofactors determine the output without knowing the rail.
        Bmc_CasTernary(p, c ^ 1, d ^ 1, z);
        Bmc_CasTernary(p, c, d, z ^ 1);
    }
}

/**Function*************************************************************

  Synopsis    [Canonicalizes input assignments for fixed symmetric templates.]

  Description [For a symmetric specification, PIs present in exactly the same stages can
               be replaced by a canonical assignment of the same weight within each class.
               Every LUT sees either a whole class or none of it, so this substitution is
               consistent across all stages and preserves the specification. Conversely,
               decoding canonicalizes every local LUT input. Thus this reduction preserves
               both SAT and UNSAT; it does not assume arbitrary internal LUTs are symmetric.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_CasSymmetry( Bmc_CasMan_t * p )
{
    word Signatures[CAS_MAX_VARS] = {0}, Classes[CAS_MAX_VARS];
    unsigned Masks[CAS_MAX_VARS] = {0}, Bits, Mask, Low, Canon;
    int i, j, k, x, Count, nClasses = 0;
    if ( !p->pPars->pSymStr ) return;
    for ( i = 0; i < p->nNodes; ++i )
        for ( k = 0; k < p->nLutSize-(i > 0); ++k )
            Signatures[p->Fixed[i][k]] |= (word)1 << i;
    for ( j = 0; j < p->nVars; ++j )
    {
        for ( i = 0; i < nClasses; ++i )
            if ( Classes[i] == Signatures[j] ) break;
        if ( i == nClasses ) Classes[nClasses++] = Signatures[j];
        Masks[i] |= 1u << j;
    }
    if ( nClasses == p->nVars ) return;
    p->pCanon = ABC_ALLOC(int, p->nMints);
    p->pRows = ABC_ALLOC(int, p->nMints);
    p->pRowIds = ABC_ALLOC(int, p->nMints);
    p->nRows = 0;
    for ( x = 0; x < p->nMints; ++x )
    {
        Canon = 0;
        for ( i = 0; i < nClasses; ++i )
        {
            Count = 0;
            for ( Bits = x & Masks[i]; Bits; Bits &= Bits-1 ) Count++;
            Mask = Masks[i];
            while ( Count-- )
            {
                Low = Mask & (0u-Mask);
                Canon |= Low;
                Mask ^= Low;
            }
        }
        p->pCanon[x] = Canon;
        if ( Canon == (unsigned)x )
        {
            p->pRowIds[x] = p->nRows;
            p->pRows[p->nRows++] = x;
        }
    }
    for ( x = 0; x < p->nMints; ++x ) p->pRowIds[x] = p->pRowIds[p->pCanon[x]];
}

/**Function*************************************************************

  Synopsis    [Numbers the local cofactor representatives of a fixed stage.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasLocalMap( Bmc_CasMan_t * p, int i )
{
    int Canon[1 << CAS_MAX_LUT], nPis = p->nLutSize-(i > 0);
    int m, k, x, Count = 0;
    if ( !p->pCanon ) return 1 << nPis;
    p->pCofIds[i] = ABC_ALLOC(int, 1 << nPis);
    for ( m = 0; m < (1 << nPis); ++m )
    {
        x = 0;
        for ( k = 0; k < nPis; ++k )
            if ( (m >> (nPis-1-k)) & 1 ) x |= 1 << p->Fixed[i][k];
        Canon[m] = Bmc_CasFixedAddress(p, i, p->pCanon[x]);
        p->pCofIds[i][m] = (Canon[m] == m) ? Count++ : -1;
    }
    for ( m = 0; m < (1 << nPis); ++m )
        p->pCofIds[i][m] = p->pCofIds[i][Canon[m]];
    return Count;
}

/**Function*************************************************************

  Synopsis    [Builds the compact CNF for a fully fixed symmetric template.]

  Description [With a fully specified template, each cofactor can be indexed directly by
               its selected PIs. No selector, cardinality, or cube-edge variables are needed.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_CasBuildFixed( Bmc_CasMan_t * p )
{
    int i, k, b, nLocal, Used = 0;
    p->iNext = 1;
    for ( i = 0; i < p->nNodes; ++i )
        for ( k = 0; k < p->nLutSize-(i > 0); ++k )
            Used |= 1 << p->Fixed[i][k];
    if ( Used != (1 << p->nVars)-1 )
    {
        Bmc_CasClause(p, NULL, 0);
        return;
    }
    Bmc_CasSymmetry(p);
    if ( p->nNodes > 1 )
        for ( i = 0; i < p->nNodes; ++i )
        {
            nLocal = Bmc_CasLocalMap(p, i);
            for ( b = 0; b < 1+(i > 0); ++b )
            {
                p->CofBase[i][b] = p->iNext;
                p->iNext += nLocal;
            }
        }
    for ( i = 1; i < p->nNodes-1; ++i )
    {
        p->ValBase[i] = p->iNext;
        p->iNext += p->nRows;
    }
    for ( i = 0; i < p->nNodes; ++i )
    {
        Bmc_CasUnit(p, Bmc_CasCofactor(p, i, 0, 0) ^ 1);
        if ( i ) Bmc_CasMuxes(p, i);
    }
    Bmc_CasReserve(p);
}

/**Function*************************************************************

  Synopsis    [Builds the support/cofactor encoding of a single-rail cascade.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_CasBuild( Bmc_CasMan_t * p )
{
    int i, j, k, b, x, n, a, c, d, FixedMask, Lits[CAS_MAX_NODES];
    // The extra ranked probe indexes its fixed final stage by local PIs.
    // The ordinary probes and the complete fallback keep their original CNF.
    if ( p->fDirectFinal )
    {
        assert( p->nNodes > 1 );
        for ( j = 0; j < p->nLutSize-1; ++j )
            assert( p->Fixed[p->nNodes-1][j] >= 0 );
    }
    p->fFixed = p->nConfLimit || p->pPars->pSymStr != NULL;
    for ( i = 0; i < p->nNodes; ++i )
        for ( j = 0; j < p->nLutSize-(i > 0); ++j )
            if ( p->Fixed[i][j] < 0 ) p->fFixed = 0;
    if ( p->fFixed ) { Bmc_CasBuildFixed(p); return; }
    p->iNext = 1;
    for ( i = 0; i < p->nNodes; ++i )
        for ( j = 0; j < p->nVars; ++j )
            p->Select[i][j] = p->iNext++;
    for ( i = 0; i < p->nNodes; ++i )
    {
        p->ValBase[i] = -1;
        if ( i < p->nNodes-1 )
        {
            p->ValBase[i] = p->iNext;
            p->iNext += p->nMints;
        }
        if ( i )
            for ( b = 0; b < 1+(i > 0); ++b )
            {
                p->CofBase[i][b] = p->iNext;
                p->iNext += (p->fDirectFinal && i == p->nNodes-1) ? (1 << (p->nLutSize-1)) : p->nMints;
            }
    }
    for ( i = 0; i < p->nNodes; ++i )
        Bmc_CasExactly(p, i, p->nLutSize-(i > 0));
    Bmc_CasOrderInputs(p);
    // As in lutexact, every PI must be selected somewhere in the cascade.
    for ( j = 0; j < p->nVars; ++j )
    {
        n = 0;
        for ( i = 0; i < p->nNodes; ++i )
            Lits[n++] = Abc_Var2Lit(p->Select[i][j], 0);
        Bmc_CasClause(p, Lits, n);
    }
    for ( i = 0; i < p->nNodes; ++i )
    {
        Bmc_CasUnit(p, Bmc_CasCofactor(p, i, 0, 0) ^ 1);
        FixedMask = 0;
        for ( k = 0; k < p->nLutSize-(i > 0); ++k )
            if ( p->Fixed[i][k] >= 0 ) FixedMask |= 1 << p->Fixed[i][k];
        // An unselected PI cannot change either cofactor along any cube edge.
        // The cofactors share selectors, so their union uses at most K-1 PIs.
        for ( j = 0; !(p->fDirectFinal && i == p->nNodes-1) && j < p->nVars; ++j )
        {
            // Bmc_CasExactly already forces these selectors true, making
            // all their independence clauses tautologies. Unselected PIs
            // still need the equality constraints below.
            if ( (FixedMask >> j) & 1 ) continue;
            for ( b = 0; b < 1+(i > 0); ++b )
            for ( x = 0; x < p->nMints; ++x )
            {
                if ( (x >> j) & 1 ) continue;
                a = Abc_Var2Lit(p->Select[i][j], 0);
                c = Bmc_CasCofactor(p, i, b, x);
                d = Bmc_CasCofactor(p, i, b, x | (1 << j));
                Bmc_CasTernary(p, a, c ^ 1, d);
                Bmc_CasTernary(p, a, c, d ^ 1);
            }
        }
        if ( i ) Bmc_CasMuxes(p, i);
    }
    Bmc_CasReserve(p);
}

/**Function*************************************************************

  Synopsis    [Adds optional backward distinguishability clauses at the last stage.]

  Description [Opposite target values on a PI edge must be distinguished by the last LUT.
               If that PI is not selected, the incoming rail must differ on the two rows:
               Select[i][j] OR (Value[i-1][x] XOR Value[i-1][y]).]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_CasBackward( Bmc_CasMan_t * p )
{
    int i = p->nNodes-1, r, x, y, j, k, a, c, d, Used = 0;
    // A single LUT has no incoming rail. An uncovered fixed template is
    // already UNSAT and returns from construction before allocating cofactors.
    if ( !i || (p->fFixed && p->iNext == 1) ) return;
    if ( p->fFixed )
        for ( k = 0; k < p->nLutSize-1; ++k ) Used |= 1 << p->Fixed[i][k];
    for ( r = 0; r < p->nRows; ++r )
    {
        int Seen[CAS_MAX_VARS], nSeen = 0;
        x = p->pRows ? p->pRows[r] : r;
        for ( j = 0; j < p->nVars; ++j )
        {
            if ( (x | Used) & (1 << j) ) continue;
            y = x | (1 << j);
            if ( p->pCanon ) y = p->pCanon[y];
            if ( Abc_TtGetBit(p->pTruth, x) == Abc_TtGetBit(p->pTruth, y) ) continue;
            if ( p->fFixed )
            {
                for ( k = 0; k < nSeen; ++k ) if ( Seen[k] == y ) break;
                if ( k < nSeen ) continue;
                Seen[nSeen++] = y;
            }
            a = p->fFixed ? 0 : Abc_Var2Lit(p->Select[i][j], 0);
            c = Bmc_CasValue(p, i-1, x);
            d = Bmc_CasValue(p, i-1, y);
            Bmc_CasTernary(p, a, c, d);
            Bmc_CasTernary(p, a, c ^ 1, d ^ 1);
        }
    }
}

/**Function*************************************************************

  Synopsis    [Returns a selector, including fixed-template constants.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasSelectLiteral( Bmc_CasMan_t * p, int i, int j )
{
    int k;
    if ( !p->fFixed ) return Abc_Var2Lit(p->Select[i][j], 0);
    for ( k = 0; k < p->nLutSize-(i > 0); ++k )
        if ( p->Fixed[i][k] == j ) return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Normalizes a rail under functions of adjacent shared inputs.]

  Description [For adjacent stages i and i+1 with shared PI set S, replace
               rail_i by rail_i XOR g(S) and swap the next LUT's rail cofactors
               wherever g is one. Both LUTs still fit their selected inputs.
               Choose g to be h_i^0 with every nonshared PI zero. This makes
               h_i^0 zero on that subspace. Apply left to right; normalization
               of the all-zero row is preserved because g(0) is zero.
               Under unknown selectors, guard each row by selection of its
               set bits in the next stage. Bits absent from the current stage
               already have no effect on its cofactor.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_CasSharedPhase( Bmc_CasMan_t * p )
{
    int i, j, r, x, Bits, Count, Limit, n, b;
    int Lits[CAS_MAX_VARS+1];
    word Added = p->nClauses;
    if ( p->nNodes < 2 || (p->fFixed && p->iNext == 1) ) return;
    Limit = p->nLutSize-1;
    for ( i = 0; i < p->nNodes-1; ++i )
    for ( r = 1; r < p->nRows; ++r )
    {
        x = p->pRows ? p->pRows[r] : r;
        Count = 0;
        for ( Bits = x; Bits; Bits &= Bits-1 ) Count++;
        if ( Count > Limit ) continue;
        n = 0;
        for ( j = 0; j < p->nVars; ++j )
        {
            if ( !((x >> j) & 1) ) continue;
            b = Bmc_CasSelectLiteral(p, i+1, j);
            if ( !b ) break;
            Lits[n++] = b ^ 1;
        }
        if ( j < p->nVars ) continue;
        Lits[n++] = Bmc_CasCofactor(p, i, 0, x) ^ 1;
        Bmc_CasClause(p, Lits, n);
    }
    if ( p->pPars->fVerbose && !p->pPars->fSilent )
        printf("Shared-input phase normalization: %llu clauses.\n", (unsigned long long)(p->nClauses-Added));
}

/**Function*************************************************************

  Synopsis    [Reads the Boolean value of an internal literal from the SAT model.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasModelValue( Bmc_CasMan_t * p, int Lit )
{
    if ( Lit < 2 ) return Lit;
    return ((p->pCadical ? ccadical_val(p->pCadical, Abc_Lit2Var(Lit)+1) :
        kissat_value(p->pSat, Abc_Lit2Var(Lit)+1)) > 0) ^ (Lit & 1);
}

/**Function*************************************************************

  Synopsis    [Decodes selected inputs and LUT truth tables from the SAT model.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_CasDecode( Bmc_CasMan_t * p )
{
    int i, j, k, m, x, b, n;
    for ( i = 0; i < p->nNodes; ++i )
    {
        n = 0;
        if ( i ) p->Fans[i][n++] = p->nVars+i-1;
        if ( p->fFixed )
            for ( j = p->nLutSize-(i > 0)-1; j >= 0; --j )
                p->Fans[i][n++] = p->Fixed[i][j];
        else for ( j = p->nVars-1; j >= 0; --j )
            if ( Bmc_CasModelValue(p, Abc_Var2Lit(p->Select[i][j], 0)) )
            {
                assert( n < p->nLutSize );
                p->Fans[i][n++] = j;
            }
        assert( n == p->nLutSize );
        for ( m = 0; m < (1 << p->nLutSize); ++m )
        {
            x = 0;
            for ( k = (i > 0); k < n; ++k )
                if ( (m >> k) & 1 ) x |= 1 << p->Fans[i][k];
            b = i ? (m & 1) : 0;
            if ( Bmc_CasModelValue(p, Bmc_CasCofactor(p, i, b, x)) )
                Abc_TtSetBit(p->Truths[i], m);
        }
        assert( !Abc_TtGetBit(p->Truths[i], 0) );
    }
}

/**Function*************************************************************

  Synopsis    [Exhaustively verifies the decoded cascade against the specification.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasVerify( Bmc_CasMan_t * p )
{
    int x, i, k, m, Value;
    for ( x = 0; x < p->nMints; ++x )
    {
        Value = 0;
        for ( i = 0; i < p->nNodes; ++i )
        {
            m = i ? Value : 0;
            for ( k = (i > 0); k < p->nLutSize; ++k )
                m |= ((x >> p->Fans[i][k]) & 1) << k;
            Value = Abc_TtGetBit(p->Truths[i], m);
        }
        if ( Value != Abc_TtGetBit(p->pTruth, x) )
            return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Derives the verified cascade as an AIG in original PI order.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Bmc_CasDerive( Bmc_CasMan_t * p )
{
    Gia_Man_t * pGia = Gia_ManStart(1000), * pClean;
    int Values[CAS_MAX_VARS+CAS_MAX_NODES], Fans[CAS_MAX_LUT], i, k;
    pGia->pName = Abc_UtilStrsav((char *)"casexact");
    for ( i = 0; i < p->nVars; ++i ) Values[i] = Gia_ManAppendCi(pGia);
    Gia_ManHashStart(pGia);
    for ( i = 0; i < p->nNodes; ++i )
    {
        for ( k = 0; k < p->nLutSize; ++k ) Fans[k] = Values[p->Fans[i][k]];
        Values[p->nVars+i] = Bmc_ExactLut(pGia, p->Truths[i], Fans, p->nLutSize, 0);
    }
    Gia_ManAppendCo(pGia, Abc_LitNotCond(Values[p->nVars+p->nNodes-1], p->fCompl));
    Gia_ManHashStop(pGia);
    pClean = Gia_ManCleanup(pGia);
    Gia_ManStop(pGia);
    return pClean;
}

/**Function*************************************************************

  Synopsis    [Prints a cascade node name.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_CasPrintNode( FILE * pFile, int i )
{
    if ( i < 26 ) fprintf(pFile, "%c", 'A'+i);
    else          fprintf(pFile, "n%d", i);
}

/**Function*************************************************************

  Synopsis    [Reads a LUT bit with the final output polarity restored.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasLutBit( Bmc_CasMan_t * p, int i, int m )
{
    return Abc_TtGetBit(p->Truths[i], m) ^ (p->fCompl && i == p->nNodes-1);
}

/**Function*************************************************************

  Synopsis    [Prints a LUT truth table in binary notation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_CasPrintTruth( FILE * pFile, Bmc_CasMan_t * p, int i )
{
    int m;
    fprintf(pFile, "%d'b", 1 << p->nLutSize);
    for ( m = (1 << p->nLutSize)-1; m >= 0; --m )
        fprintf(pFile, "%d", Bmc_CasLutBit(p, i, m));
}

/**Function*************************************************************

  Synopsis    [Prints the verified cascade and its input permutation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_CasPrint( Bmc_CasMan_t * p )
{
    int i, k, Fan;
    // Fans[] is LSB-first; printed pins are MSB-first, with the rail last (LSB).
    printf("Realization of given %d-input function using %d %d-input LUTs:\n", p->nVars, p->nNodes, p->nLutSize);
    for ( i = p->nNodes-1; i >= 0; --i )
    {
        Bmc_CasPrintNode(stdout, i);
        printf(" = ");
        Bmc_CasPrintTruth(stdout, p, i);
        printf("(");
        for ( k = p->nLutSize-1; k >= 0; --k )
        {
            Fan = p->Fans[i][k];
            printf(" ");
            if ( Fan < p->nVars ) printf("%c", 'a'+Fan);
            else Bmc_CasPrintNode(stdout, Fan-p->nVars);
        }
        printf(" )\n");
    }
    printf("The variable permutation is \"");
    for ( i = 0; i < p->nNodes; ++i )
    {
        if ( i ) printf("_");
        for ( k = p->nLutSize-1; k >= (i > 0); --k )
            printf("%c", 'a'+p->Fans[i][k]);
    }
    printf("\".\n");
}

/**Function*************************************************************

  Synopsis    [Writes the verified cascade in BLIF and Verilog formats.]

  Description [Portable BLIF and Verilog, including K > 6 and complemented outputs.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasDump( Bmc_CasMan_t * p )
{
    char Base[128], Blif[140], Verilog[140];
    FILE * pBlif, * pVerilog;
    word Hash = ABC_CONST(0xcbf29ce484222325), Value;
    int i, k, m, Fan;
    for ( i = 0; i < p->nWords; ++i )
    {
        Value = p->fCompl ? ~p->pTruth[i] : p->pTruth[i];
        for ( k = 0; k < 8; ++k )
            Hash = (Hash ^ ((Value >> (8*k)) & 255)) * ABC_CONST(0x100000001b3);
    }
    snprintf(Base, sizeof(Base), "casexact_N%d_K%d_M%d_%016llx", p->nVars, p->nLutSize, p->nNodes, (unsigned long long)Hash);
    snprintf(Blif, sizeof(Blif), "%s.blif", Base);
    snprintf(Verilog, sizeof(Verilog), "%s.v", Base);
    pBlif = fopen(Blif, "wb");
    if ( !pBlif ) { Abc_Print(-1, "Cannot write %s.\n", Blif); return 0; }
    pVerilog = fopen(Verilog, "wb");
    if ( !pVerilog ) { fclose(pBlif); Abc_Print(-1, "Cannot write %s.\n", Verilog); return 0; }
    fprintf(pBlif, ".model %s\n.inputs", Base);
    for ( i = 0; i < p->nVars; ++i ) fprintf(pBlif, " %c", 'a'+i);
    fprintf(pBlif, "\n.outputs F\n");
    fprintf(pVerilog, "module %s (input wire [%d:0] x, output wire y);\n", Base, p->nVars-1);
    for ( i = 0; i < p->nVars; ++i )
        fprintf(pVerilog, "  wire p%d;\n  assign p%d = x[%d];\n", i, i, i);
    for ( i = 0; i < p->nNodes; ++i )
    {
        fprintf(pBlif, ".names");
        for ( k = 0; k < p->nLutSize; ++k )
        {
            Fan = p->Fans[i][k];
            if ( Fan < p->nVars ) fprintf(pBlif, " %c", 'a'+Fan);
            else fprintf(pBlif, " n%d", Fan-p->nVars);
        }
        if ( i == p->nNodes-1 ) fprintf(pBlif, " F\n");
        else fprintf(pBlif, " n%d\n", i);
        for ( m = 0; m < (1 << p->nLutSize); ++m )
            if ( Bmc_CasLutBit(p, i, m) )
            {
                for ( k = 0; k < p->nLutSize; ++k ) fprintf(pBlif, "%d", (m >> k) & 1);
                fprintf(pBlif, " 1\n");
            }
        fprintf(pVerilog, "  wire [%d:0] lut%d = ", (1 << p->nLutSize)-1, i);
        Bmc_CasPrintTruth(pVerilog, p, i);
        fprintf(pVerilog, ";\n  wire [%d:0] addr%d;\n  assign addr%d = {", p->nLutSize-1, i, i);
        for ( k = p->nLutSize-1; k >= 0; --k )
        {
            if ( k != p->nLutSize-1 ) fprintf(pVerilog, ", ");
            Fan = p->Fans[i][k];
            if ( Fan < p->nVars ) fprintf(pVerilog, "p%d", Fan);
            else fprintf(pVerilog, "n%d", Fan-p->nVars);
        }
        fprintf(pVerilog, "};\n  wire [%d:0] sel%d;\n  assign sel%d = lut%d >> addr%d;\n", (1 << p->nLutSize)-1, i, i, i, i);
        fprintf(pVerilog, "  wire n%d;\n  assign n%d = sel%d[0];\n", i, i, i);
    }
    fprintf(pBlif, ".end\n");
    fprintf(pVerilog, "  assign y = n%d;\nendmodule\n", p->nNodes-1);
    i = ferror(pBlif) || ferror(pVerilog);
    if ( fclose(pBlif) ) i = 1;
    if ( fclose(pVerilog) ) i = 1;
    if ( i ) { Abc_Print(-1, "Error writing cascade files.\n"); return 0; }
    if ( !p->pPars->fSilent ) printf("Wrote %s and %s.\n", Blif, Verilog);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Checks the solver time limit.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasTerminate( void * pData )
{
    Bmc_CasMan_t * p = (Bmc_CasMan_t *)pData;
    return p->timeStop && Abc_Clock() > p->timeStop;
}

/**Function*************************************************************

  Synopsis    [Solves with the per-query deadline and optional probe conflict limit.]

  Description [Both bundled solvers return 10 for SAT, 20 for UNSAT, and 0 otherwise.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasSolverSolve( Bmc_CasMan_t * p, unsigned nConfLimit )
{
    if ( p->pCadical )
    {
        assert( nConfLimit <= INT_MAX );
        ccadical_set_terminate(p->pCadical, p, Bmc_CasTerminate);
        if ( nConfLimit ) ccadical_limit(p->pCadical, "conflicts", (int)nConfLimit);
        return ccadical_solve(p->pCadical);
    }
    kissat_set_terminate(p->pSat, p, Bmc_CasTerminate);
    if ( nConfLimit ) kissat_set_conflict_limit(p->pSat, nConfLimit);
    return kissat_solve(p->pSat);
}

/**Function*************************************************************

  Synopsis    [Orders free placements under verified input permutations.]

  Description [Cofactor counts propose permutations; the entire truth table
               verifies each one. The lexicographically greatest placement
               in every orbit satisfies these constraints. Caller bindings
               are excluded, and symmetric targets use their existing rule.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_CasGroupSymmetry( Bmc_CasMan_t * p )
{
    int Key[CAS_MAX_VARS][3] = {{0}}, Id[CAS_MAX_VARS], Group[CAS_MAX_VARS], Perm[CAS_MAX_VARS];
    int Saved[CAS_MAX_VARS+1][CAS_MAX_VARS], nSaved = 0, nClasses = 0;
    int i, j, k, x, y, c, t, n, Good, Changed, Prefix, Next, a, b;
    if ( p->pPars->pSymStr || p->nVars > 10 ) return;
    for ( i = 0; i < p->nNodes; ++i )
        for ( k = 0; k < p->nLutSize-(i > 0); ++k )
            if ( p->Fixed[i][k] >= 0 ) return;
    for ( i = 0; i < p->nVars; ++i )
    {
        for ( x = 0; x < p->nMints; ++x )
        {
            t = (x >> i) & 1;
            Key[i][t] += Abc_TtGetBit(p->pTruth, x);
            if ( !t ) Key[i][2] += Abc_TtGetBit(p->pTruth, x) != Abc_TtGetBit(p->pTruth, x | (1 << i));
        }
        for ( j = 0; j < i; ++j )
            if ( !memcmp(Key[i], Key[j], sizeof(Key[i])) ) break;
        Id[i] = j < i ? Id[j] : nClasses++;
    }
    for ( c = -1; c < nClasses; ++c )
    {
        for ( i = 0; i < p->nVars; ++i ) Perm[i] = i;
        for ( k = 0; k < nClasses; ++k )
            if ( c < 0 || c == k )
            {
                n = 0;
                for ( i = 0; i < p->nVars; ++i ) if ( Id[i] == k ) Group[n++] = i;
                for ( i = 0; i < n; ++i ) Perm[Group[i]] = Group[n-1-i];
            }
        Changed = 0;
        for ( i = 0; i < p->nVars; ++i ) Changed |= Perm[i] != i;
        if ( !Changed ) continue;
        for ( i = 0; i < nSaved; ++i ) if ( !memcmp(Saved[i], Perm, sizeof(int)*p->nVars) ) break;
        if ( i < nSaved ) continue;
        Good = 1;
        for ( x = 0; x < p->nMints && Good; ++x )
        {
            y = 0;
            for ( i = 0; i < p->nVars; ++i ) y |= ((x >> i) & 1) << Perm[i];
            Good = Abc_TtGetBit(p->pTruth, x) == Abc_TtGetBit(p->pTruth, y);
        }
        if ( !Good ) continue;
        memcpy(Saved[nSaved++], Perm, sizeof(int)*p->nVars);
        Prefix = 1;
        for ( i = 0; i < p->nNodes; ++i )
        for ( j = 0; j < p->nVars; ++j )
            if ( Perm[j] != j )
            {
                a = Abc_Var2Lit(p->Select[i][j], 0);
                b = Abc_Var2Lit(p->Select[i][Perm[j]], 0);
                Bmc_CasTernary(p, Prefix ^ 1, a, b ^ 1);
                Next = Abc_Var2Lit(p->iNext++, 0);
                Bmc_CasTernary(p, Prefix ^ 1, a, Next);
                Bmc_CasTernary(p, Prefix ^ 1, b ^ 1, Next);
                Prefix = Next;
            }
    }
    if ( nSaved && !p->pPars->fSilent ) printf("Verified input-block symmetries: %d.\n", nSaved);
}

/**Function*************************************************************

  Synopsis    [Propagates input influence across a prefix or a suffix.]

  Description [A PI absent from a prefix cannot affect its output rail.
               If a PI is absent from a suffix, opposite target values
               require different rails at the entrance to the suffix.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_CasLongEdges( Bmc_CasMan_t * p )
{
    int i, j, k, r, x, y, a, b, n, Skip, Lits[CAS_MAX_NODES+2];
    if ( p->nVars > 10 || p->nNodes > 16 || p->nNodes < 2 || (p->fFixed && p->iNext == 1) ) return;
    for ( i = 0; i < p->nNodes-1; ++i )
    for ( j = 0; j < p->nVars; ++j )
    {
        {
            n = Skip = 0;
            for ( k = i+1; k < p->nNodes; ++k )
            {
                a = Bmc_CasSelectLiteral(p, k, j);
                if ( a == 1 ) { Skip = 1; break; }
                if ( a ) Lits[n++] = a;
            }
            if ( !Skip && n+2 <= CAS_MAX_NODES )
                for ( r = 0; r < p->nRows; ++r )
                {
                    x = p->pRows ? p->pRows[r] : r;
                    if ( (x >> j) & 1 ) continue;
                    y = x | (1 << j);
                    if ( Abc_TtGetBit(p->pTruth, x) == Abc_TtGetBit(p->pTruth, y) ) continue;
                    a = Bmc_CasValue(p, i, x);
                    b = Bmc_CasValue(p, i, y);
                    Lits[n] = a; Lits[n+1] = b;
                    Bmc_CasClause(p, Lits, n+2);
                    Lits[n] ^= 1; Lits[n+1] ^= 1;
                    Bmc_CasClause(p, Lits, n+2);
                }
        }
        {
            n = Skip = 0;
            for ( k = 0; k <= i; ++k )
            {
                a = Bmc_CasSelectLiteral(p, k, j);
                if ( a == 1 ) { Skip = 1; break; }
                if ( a ) Lits[n++] = a;
            }
            if ( !Skip && n+2 <= CAS_MAX_NODES )
                for ( r = 0; r < p->nRows; ++r )
                {
                    x = p->pRows ? p->pRows[r] : r;
                    if ( (x >> j) & 1 ) continue;
                    y = x | (1 << j);
                    a = Bmc_CasValue(p, i, x);
                    b = Bmc_CasValue(p, i, y);
                    Lits[n] = a ^ 1; Lits[n+1] = b;
                    Bmc_CasClause(p, Lits, n+2);
                    Lits[n] ^= 1; Lits[n+1] ^= 1;
                    Bmc_CasClause(p, Lits, n+2);
                }
        }
    }
}

typedef struct Bmc_CasMatrix_t_ Bmc_CasMatrix_t;
struct Bmc_CasMatrix_t_
{
    unsigned Values[8];
    unsigned * pKeys;
    int * pChoices;
    int nRows, nCols, nHalf, nEntries, nCalls, fStop;
    abctime timeStop;
};

/**Function*************************************************************

  Synopsis    [Canonicalizes one cared row or column up to complementation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static unsigned Bmc_CasMatrixSignature( unsigned * pValues, int nRows,
    unsigned Rows, unsigned Cols, int Index, int fColumn )
{
    unsigned Value = 0, Mask = fColumn ? Rows : Cols;
    int r;
    if ( !fColumn ) Value = pValues[Index] & Cols;
    else
        for ( r = 0; r < nRows; ++r )
            if ( (Rows >> r) & 1 ) Value |= ((pValues[r] >> Index) & 1) << r;
    return Value < (Value ^ Mask) ? Value : (Value ^ Mask);
}

/**Function*************************************************************

  Synopsis    [Tests whether the first LUT can ignore the remaining B inputs.]

  Description [The first LUT sees A and one distinguished input of B.
               Within either value of this input, all remaining columns
               must agree up to a column complement. The preceding backward
               peel is free to choose these column phases.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasMatrixEndpoint( Bmc_CasMatrix_t * p, unsigned Rows, unsigned Cols )
{
    unsigned First, Value;
    int h, c, Found;
    for ( h = 0; h < 2; ++h )
    {
        First = 0; Found = 0;
        for ( c = h*p->nHalf; c < (h+1)*p->nHalf; ++c )
            if ( (Cols >> c) & 1 )
            {
                Value = Bmc_CasMatrixSignature(p->Values, p->nRows, Rows, Cols, c, 1);
                if ( Found && Value != First ) return 0;
                First = Value; Found = 1;
            }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Bounds the number of remaining row/column eliminations by rank.]

  Description [Border the cared matrix with an all-one row and column and a
               zero corner. Its GF(2) rank is unchanged by row/column phases.
               Removing one equal-or-complement class lowers rank by at most
               one, since all removed augmented vectors agree modulo the
               border vector. At the endpoint the two distinguished-input
               groups give at most two column classes, so the rank is at
               most three. Stage remaining removals therefore require rank
               at most Stage+3.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasMatrixRank( Bmc_CasMatrix_t * p, unsigned Rows, unsigned Cols )
{
    word Basis[2*CAS_MAX_LUT] = {0}, Value;
    int Rank = 0, r, b;
    for ( r = -1; r < p->nRows; ++r )
    {
        if ( r >= 0 && !((Rows >> r) & 1) ) continue;
        Value = r < 0 ? (word)Cols : ((word)(p->Values[r] & Cols) | ((word)1 << p->nCols));
        for ( b = p->nCols; b >= 0; --b )
            if ( (Value >> b) & 1 )
            {
                if ( Basis[b] ) Value ^= Basis[b];
                else { Basis[b] = Value; Rank++; break; }
            }
    }
    return Rank;
}

/**Function*************************************************************

  Synopsis    [Finds an alternating sequence of row/column class removals.]

  Description [A row-stage LUT is constant, the incoming rail, or its
               complement for each local input. A constant row removes all
               its care; a mixed row leaves a freely chosen row phase.
               At the next column stage, these phases can make precisely
               one class of equal/complement columns constant. Removing the
               whole class dominates retaining any of it. Alternating this
               argument leaves the original matrix up to row/column phases,
               with rectangular care. Thus only the remaining rows, columns,
               and stage number belong in the memoization key.
               Returns 1 for SAT, -1 for UNSAT, and 0 on resource limits.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasMatrixSearch( Bmc_CasMatrix_t * p, unsigned Rows, unsigned Cols,
    int Stage, int * pChoice )
{
    unsigned Key, Signatures[16], Masks[16], Value, Active, Swap;
    int Reps[16], Counts[16], nClasses = 0, i, j, k, Pos, Result, Next, Temp;
    if ( !Rows || !Cols ) return 1;
    if ( !Stage ) return Bmc_CasMatrixEndpoint(p, Rows, Cols) ? 1 : -1;
    if ( p->fStop ) return 0;
    if ( !(p->nCalls++ & 255) && Abc_Clock() >= p->timeStop )
        { p->fStop = 1; return 0; }
    Key = Rows | (Cols << 8) | ((unsigned)Stage << 22);
    Pos = (Key * 12582917u) & 65535;
    while ( p->pKeys[Pos] && p->pKeys[Pos] != Key ) Pos = (Pos+1) & 65535;
    if ( p->pKeys[Pos] )
    {
        if ( p->pChoices[Pos] < 0 ) return -1;
        *pChoice = p->pChoices[Pos];
        return 1;
    }
    // Skip the rank computation when the full dimensions cannot exceed
    // Stage+3, including the border row/column. This only prunes candidates.
    if ( Stage+2 < p->nRows && Stage+2 < p->nCols &&
         Bmc_CasMatrixRank(p, Rows, Cols) > Stage+3 ) return -1;
    Active = Stage & 1 ? Cols : Rows;
    for ( i = 0; i < ((Stage & 1) ? p->nCols : p->nRows); ++i )
        if ( (Active >> i) & 1 )
        {
            Value = Bmc_CasMatrixSignature(p->Values, p->nRows, Rows, Cols, i, Stage & 1);
            for ( j = 0; j < nClasses; ++j ) if ( Signatures[j] == Value ) break;
            if ( j == nClasses )
                Signatures[j] = Value, Masks[j] = 0, Reps[j] = i, Counts[j] = 0, nClasses++;
            Masks[j] |= 1u << i; Counts[j]++;
        }
    // Try larger removable classes first; retain the natural order on ties.
    for ( i = 1; i < nClasses; ++i )
        for ( j = i; j > 0 && Counts[j] > Counts[j-1]; --j )
        {
            Swap = Masks[j]; Masks[j] = Masks[j-1]; Masks[j-1] = Swap;
            Temp = Reps[j]; Reps[j] = Reps[j-1]; Reps[j-1] = Temp;
            Temp = Counts[j]; Counts[j] = Counts[j-1]; Counts[j-1] = Temp;
        }
    Result = -1;
    for ( k = 0; k < nClasses; ++k )
    {
        Next = 0;
        Result = Bmc_CasMatrixSearch(p, (Stage & 1) ? Rows : Rows & ~Masks[k],
            (Stage & 1) ? Cols & ~Masks[k] : Cols, Stage-1, &Next);
        if ( Result == 0 ) return 0;
        if ( Result > 0 ) { *pChoice = Reps[k]; break; }
    }
    if ( p->nEntries >= 32768 ) { p->fStop = 1; return 0; }
    // Recursive insertions can occupy the slot found before the search.
    Pos = (Key * 12582917u) & 65535;
    while ( p->pKeys[Pos] && p->pKeys[Pos] != Key ) Pos = (Pos+1) & 65535;
    if ( !p->pKeys[Pos] ) p->nEntries++;
    p->pKeys[Pos] = Key;
    p->pChoices[Pos] = Result > 0 ? *pChoice : -1;
    return Result;
}

/**Function*************************************************************

  Synopsis    [Reconstructs concrete LUTs from a successful matrix search.]

  Description [Restores actual phases while peeling backwards. Independent
               exhaustive circuit verification still follows before printing.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasMatrixContext( Bmc_CasMatrix_t * p, int nNodes,
    unsigned char Local[][16][2] )
{
    unsigned Values[8], Rows = (1u << p->nRows)-1, Cols = (1u << p->nCols)-1;
    unsigned Active, Opposite, Removed;
    int Stage, Side, j, k, r, c, Phase, Choice = 0, Result;
    memcpy(Values, p->Values, sizeof(Values));
    memset(Local, 0, sizeof(unsigned char)*CAS_MAX_NODES*16*2);
    for ( Stage = nNodes-1; Stage > 0; --Stage )
    {
        Side = Stage & 1;
        Active = Side ? Cols : Rows;
        Opposite = Side ? Rows : Cols;
        Removed = 0;
        for ( j = 0; j < (Side ? p->nCols : p->nRows); ++j )
            if ( (Active >> j) & 1 )
            {
                if ( Bmc_CasMatrixSignature(Values, p->nRows, Rows, Cols, j, Side) ) continue;
                for ( k = 0; k < 16 && !((Opposite >> k) & 1); ++k ) {}
                Phase = k == 16 ? 0 : (int)(((Side ? Values[k] : Values[j]) >> (Side ? j : k)) & 1);
                Local[Stage][j][0] = Local[Stage][j][1] = (unsigned char)Phase;
                Removed |= 1u << j;
            }
        if ( Side ) Cols &= ~Removed;
        else        Rows &= ~Removed;
        Result = Bmc_CasMatrixSearch(p, Rows, Cols, Stage-1, &Choice);
        if ( Result <= 0 ) return Result;
        if ( !Rows || !Cols ) break;
        for ( j = 0; j < (Side ? p->nCols : p->nRows); ++j )
            if ( ((Side ? Cols : Rows) >> j) & 1 )
            {
                if ( Stage == 1 )
                {
                    for ( r = 0; !((Rows >> r) & 1); ++r ) {}
                    for ( c = (j/p->nHalf)*p->nHalf; !((Cols >> c) & 1); ++c ) {}
                    Phase = (int)(((Values[r] >> j) ^ (Values[r] >> c)) & 1);
                }
                else Phase = (int)(((Side ? Values[Choice] : Values[j]) >> (Side ? j : Choice)) & 1);
                Local[Stage][j][0] = (unsigned char)Phase;
                Local[Stage][j][1] = (unsigned char)(Phase ^ 1);
                if ( Side )
                {
                    for ( r = 0; r < p->nRows; ++r )
                        if ( ((Rows >> r) & 1) && Phase ) Values[r] ^= 1u << j;
                }
                else if ( Phase ) Values[j] ^= Cols;
            }
    }
    for ( r = 0; r < p->nRows; ++r )
        if ( (Rows >> r) & 1 )
            for ( c = 0; c < p->nCols; ++c )
                if ( (Cols >> c) & 1 ) Local[0][r][c/p->nHalf] = (unsigned char)((Values[r] >> c) & 1);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Solves symmetric alternating templates by matrix elimination.]

  Description [Only complete templates A+h, B, A, B, ... are recognized,
               with h in B but not A and A union B covering all PIs.
               Fixing shared inputs separates independent contexts. PIs
               occurring in identical stage sets may be replaced by their
               weight because the target is symmetric. The first B input h
               remains separate. A failed search, including rank pruning,
               is only a failed candidate, never an UNSAT proof. Temporary
               tables are committed only when every context succeeds.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasMatrix( Bmc_CasMan_t * pCas )
{
    Bmc_CasMatrix_t * p;
    unsigned Masks[CAS_MAX_NODES], A, B, Common, U, V, Extra, Inputs;
    unsigned char Local[CAS_MAX_NODES][16][2];
    word Tables[CAS_MAX_NODES][4] = {{0}}, Temp[4];
    int Fans[CAS_MAX_NODES][CAS_MAX_LUT] = {{0}};
    int i, j, k, h = -1, r, c, Weight, nShared, Address, Index, Result = 0;
    int Phase = 0, NextPhase, nNodes = pCas->nNodes, K = pCas->nLutSize;
    if ( !pCas->pPars->pSymStr || nNodes < 2 ) return 0;
    for ( i = 0; i < nNodes; ++i )
    {
        Masks[i] = 0;
        for ( j = 0; j < K-(i > 0); ++j )
        {
            if ( pCas->Fixed[i][j] < 0 ) return 0;
            Masks[i] |= 1u << pCas->Fixed[i][j];
        }
    }
    B = Masks[1];
    if ( nNodes == 2 )
    {
        for ( j = 0; j < pCas->nVars; ++j ) if ( ((Masks[0] & B) >> j) & 1 ) h = j;
        if ( h < 0 ) return 0;
        A = Masks[0] & ~(1u << h);
    }
    else A = Masks[2];
    Extra = Masks[0] & ~A;
    if ( !Extra || (Extra & (Extra-1)) || Masks[0] != (A | Extra) ||
         !(B & Extra) || (A | B) != (1u << pCas->nVars)-1 ) return 0;
    for ( i = 1; i < nNodes; ++i ) if ( Masks[i] != ((i & 1) ? B : A) ) return 0;
    Common = A & B; U = A & ~B; V = B & ~A;
    nShared = Abc_TtCountOnes(Common);
    p = ABC_CALLOC(Bmc_CasMatrix_t, 1);
    p->nRows = Abc_TtCountOnes(U)+1;
    p->nHalf = Abc_TtCountOnes(V);
    p->nCols = 2*p->nHalf;
    p->pKeys = ABC_CALLOC(unsigned, 65536);
    p->pChoices = ABC_ALLOC(int, 65536);
    p->timeStop = Abc_Clock()+CLOCKS_PER_SEC/10;
    for ( i = 0; i < nNodes; ++i )
    {
        k = 0;
        if ( i ) Fans[i][k++] = pCas->nVars+i-1;
        for ( j = pCas->nVars-1; j >= 0; --j ) if ( (Masks[i] >> j) & 1 ) Fans[i][k++] = j;
        assert( k == K );
    }
    for ( Weight = 0; Weight <= nShared; ++Weight )
    {
        memset(p->Values, 0, sizeof(p->Values));
        memset(p->pKeys, 0, sizeof(unsigned)*65536);
        p->nEntries = p->nCalls = 0;
        for ( r = 0; r < p->nRows; ++r )
            for ( c = 0; c < p->nCols; ++c )
                if ( (pCas->pPars->pSymStr[r+c/p->nHalf+c%p->nHalf+Weight]-'0') ^ pCas->fCompl )
                    p->Values[r] |= 1u << c;
        Result = Bmc_CasMatrixContext(p, nNodes, Local);
        if ( Result <= 0 ) break;
        for ( i = 0; i < nNodes; ++i )
            for ( Address = 0; Address < (1 << K); ++Address )
            {
                Inputs = 0;
                for ( j = i > 0; j < K; ++j )
                    if ( (Address >> j) & 1 ) Inputs |= 1u << Fans[i][j];
                if ( Abc_TtCountOnes(Inputs & Common) != Weight ) continue;
                if ( !i )
                    Index = Local[0][Abc_TtCountOnes(Inputs & U)][(Inputs & Extra) != 0];
                else
                {
                    Index = (i & 1) ? ((Inputs & Extra) != 0)*p->nHalf + Abc_TtCountOnes(Inputs & V & ~Extra) : Abc_TtCountOnes(Inputs & U);
                    Index = Local[i][Index][Address & 1];
                }
                if ( Index ) Abc_TtSetBit(Tables[i], Address);
            }
    }
    if ( Result > 0 )
    {
        // Normalize rail phases, preserving the existing printed convention.
        for ( i = 0; i < nNodes; ++i )
        {
            memset(Temp, 0, sizeof(Temp));
            NextPhase = Abc_TtGetBit(Tables[i], i ? Phase : 0);
            for ( Address = 0; Address < (1 << K); ++Address )
                if ( Abc_TtGetBit(Tables[i], Address ^ (i ? Phase : 0)) ^ NextPhase ) Abc_TtSetBit(Temp, Address);
            memcpy(Tables[i], Temp, sizeof(Temp));
            Phase = NextPhase;
        }
        if ( Phase ) Result = 0;
        else
        {
            memcpy(pCas->Fans, Fans, sizeof(Fans));
            memcpy(pCas->Truths, Tables, sizeof(Tables));
        }
    }
    ABC_FREE(p->pKeys);
    ABC_FREE(p->pChoices);
    ABC_FREE(p);
    return Result > 0 ? CAS_SAT : 0;
}

/**Function*************************************************************

  Synopsis    [Solves and verifies a cascade with a fixed number of LUTs.]

  Description [Returns the solver's SAT/UNSAT/UNKNOWN result, or -1 for an internal/I/O error.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasSolve( Bmc_EsPar_t * pPars, word * pSpec, int nNodes, int Fixed[][CAS_MAX_LUT], int fMuxConsensus, int fBackward, int fPhase, int fDirectFinal, unsigned nConfLimit, abctime clkTotal, int fInputSymmetry, int fMatrix, abctime timeProbe, Gia_Man_t ** ppGia )
{
    Bmc_CasMan_t * p = ABC_CALLOC(Bmc_CasMan_t, 1);
    abctime clk = Abc_Clock(), clkSolve;
    int Status, i, fMatrixAnswer;
    p->pPars = pPars;
    p->nConfLimit = nConfLimit;
    p->fDirectFinal = fDirectFinal;
    p->nVars = pPars->nVars;
    p->nNodes = nNodes;
    p->nLutSize = pPars->nLutSize;
    p->nMints = 1 << p->nVars;
    p->nRows = p->nMints;
    p->nWords = Abc_TtWordNum(p->nVars);
    p->pTruth = ABC_ALLOC(word, p->nWords);
    Abc_TtCopy(p->pTruth, pSpec, p->nWords, 0);
    p->fCompl = (int)(p->pTruth[0] & 1);
    if ( p->fCompl ) Abc_TtNot(p->pTruth, p->nWords);
    memcpy(p->Fixed, Fixed, sizeof(p->Fixed));
    Bmc_CasSolverStart(p);
    Status = fMatrix ? Bmc_CasMatrix(p) : 0;
    fMatrixAnswer = Status == CAS_SAT && Bmc_CasVerify(p);
    if ( Status == CAS_SAT && !fMatrixAnswer )
    {
        if ( !pPars->fSilent )
            Abc_Print(-1, "Matrix candidate failed verification; continuing with SAT.\n");
        memset(p->Fans, 0, sizeof(p->Fans));
        memset(p->Truths, 0, sizeof(p->Truths));
    }
    if ( !pPars->fSilent )
        printf("Running exact cascade synthesis for %d-input function with %d %d-input LUTs (%s)...\n", p->nVars, p->nNodes, p->nLutSize, fMatrixAnswer ? "matrix" : pPars->fCadical ? "CaDiCaL" : "Kissat");
    if ( !fMatrixAnswer )
    {
        Bmc_CasBuild(p);
        // Append after the base CNF to retain the benchmarked clause order.
        if ( fPhase || nConfLimit ) Bmc_CasSharedPhase(p);
        if ( fBackward ) Bmc_CasBackward(p);
        if ( fMuxConsensus ) Bmc_CasMuxConsensus(p);
        if ( fInputSymmetry )
        {
            Bmc_CasGroupSymmetry(p);
            Bmc_CasLongEdges(p);
        }
        if ( !pPars->fSilent && p->nRows < p->nMints )
            printf("Symmetry: %d representatives of %d input assignments.\n", p->nRows, p->nMints);
        if ( !pPars->fSilent )
            printf("CNF: %d variables, %llu clauses, %llu literals.\n", p->iNext, (unsigned long long)p->nClauses, (unsigned long long)p->nLiterals);
        clkSolve = Abc_Clock();
        if ( pPars->RuntimeLim )
            p->timeStop = clkSolve + (abctime)pPars->RuntimeLim * CLOCKS_PER_SEC;
        if ( timeProbe && (!p->timeStop || timeProbe < p->timeStop) ) p->timeStop = timeProbe;
        Status = Bmc_CasTerminate(p) ? 0 : Bmc_CasSolverSolve(p, nConfLimit);
        if ( pPars->fVerbose && !pPars->fSilent )
        {
            Abc_PrintTime(1, "CNF construction", clkSolve-clk);
            Abc_PrintTime(1, pPars->fCadical ? "CaDiCaL solving" : "Kissat solving", Abc_Clock()-clkSolve);
        }
    }
    else if ( !pPars->fSilent )
        printf("Symmetry: solved by alternating count-matrix elimination.\n");
    if ( Status == CAS_SAT )
    {
        if ( !fMatrixAnswer ) Bmc_CasDecode(p);
        if ( !Bmc_CasVerify(p) )
        {
            Abc_Print(-1, "Internal error: cascade failed exhaustive verification.\n");
            Status = -1;
        }
        else
        {
            Bmc_CasPrint(p);
            if ( pPars->fDumpBlif && !Bmc_CasDump(p) ) Status = -1;
            if ( Status == CAS_SAT ) *ppGia = Bmc_CasDerive(p);
        }
    }
    else if ( Status == CAS_UNSAT && !pPars->fSilent )
        printf("The problem has no solution.\n");
    else if ( Status == 0 && !pPars->fSilent )
        printf("Unknown: SAT solver stopped before deciding the problem.\n");
    if ( !pPars->fSilent ) Abc_PrintTime(1, "Total runtime", Abc_Clock()-(clkTotal ? clkTotal : clk));
    Bmc_CasSolverStop(p);
    ABC_FREE(p->pTruth);
    ABC_FREE(p->pCanon);
    ABC_FREE(p->pRows);
    ABC_FREE(p->pRowIds);
    for ( i = 0; i < p->nNodes; ++i ) ABC_FREE(p->pCofIds[i]);
    ABC_FREE(p);
    return Status;
}

/**Function*************************************************************

  Synopsis    [Advances the reproducible pseudo-random generator.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static unsigned Bmc_CasRandom( unsigned * pState )
{
    unsigned x = *pState;
    x ^= x << 13; x ^= x >> 17; x ^= x << 5;
    return *pState = x;
}

/**Function*************************************************************

  Synopsis    [Derives and checks the requested input template.]

  Description [Parse ordered PI positions, including '*' wildcards. The previous rail is
               implicit, so groups have lengths K, K-1, ..., separated by underscores.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasInputs( Bmc_EsPar_t * pPars, int Fixed[][CAS_MAX_LUT], unsigned * pRandom )
{
    int i, j, k, r, n, Last, Temp, Pos = 0, nCandidates;
    int Order[CAS_MAX_VARS], Counts[CAS_MAX_VARS] = {0};
    int Candidates[CAS_MAX_NODES*CAS_MAX_LUT];
    memset(Fixed, 0xff, sizeof(int)*CAS_MAX_NODES*CAS_MAX_LUT);
    if ( pPars->pPermStr )
    {
        if ( strlen(pPars->pPermStr) != (size_t)pPars->nLutSize*pPars->nNodes )
        {
            Abc_Print(-1, "Input permutation must have K*M = %d characters (including underscores).\n", pPars->nLutSize*pPars->nNodes);
            return 0;
        }
        for ( i = 0; i < pPars->nNodes; ++i )
        {
            if ( i && pPars->pPermStr[Pos++] != '_' )
            {
                Abc_Print(-1, "Input permutation needs an underscore before stage %d.\n", i+1);
                return 0;
            }
            n = pPars->nLutSize-(i > 0);
            Last = -1;
            for ( k = 0; k < n; ++k )
            {
                char c = pPars->pPermStr[Pos++];
                if ( c == '*' ) { Last++; }
                else if ( c >= 'a' && c < 'a'+pPars->nVars )
                {
                    j = c-'a';
                    if ( j <= Last )
                    {
                        Abc_Print(-1, "Stage %d has no strictly increasing completion of its PI positions.\n", i+1);
                        return 0;
                    }
                    Fixed[i][k] = Last = j;
                }
                else
                {
                    Abc_Print(-1, "Stage %d expects PI letters a..%c or '*'.\n", i+1, 'a'+pPars->nVars-1);
                    return 0;
                }
                if ( Last >= pPars->nVars-(n-1-k) )
                {
                    Abc_Print(-1, "Stage %d has no strictly increasing completion of its PI positions.\n", i+1);
                    return 0;
                }
            }
        }
    }
    else if ( pPars->fUsePerm )
    {
        for ( i = 0; i < pPars->nNodes; ++i )
        for ( k = 0; k < pPars->nLutSize-(i > 0); ++k )
            Fixed[i][k] = (i & 1) ? pPars->nVars-(pPars->nLutSize-1)+k : k;
    }
    else if ( pPars->fLutInFixed )
    {
        // Pick distinct inputs per stage, then repair coverage without retries.
        for ( i = 0; i < pPars->nNodes; ++i )
        {
            for ( j = 0; j < pPars->nVars; ++j ) Order[j] = j;
            for ( k = 0; k < pPars->nLutSize-(i > 0); ++k )
            {
                j = k + Bmc_CasRandom(pRandom) % (pPars->nVars-k);
                Temp = Order[k]; Order[k] = Order[j]; Order[j] = Temp;
                Fixed[i][k] = Order[k];
                Counts[Order[k]]++;
            }
        }
        for ( j = 0; j < pPars->nVars; ++j )
            if ( Counts[j] == 0 )
            {
                nCandidates = 0;
                for ( i = 0; i < pPars->nNodes; ++i )
                for ( k = 0; k < pPars->nLutSize-(i > 0); ++k )
                    if ( Counts[Fixed[i][k]] > 1 )
                        Candidates[nCandidates++] = i*CAS_MAX_LUT+k;
                assert( nCandidates );
                Temp = Candidates[Bmc_CasRandom(pRandom) % nCandidates];
                i = Temp/CAS_MAX_LUT; k = Temp%CAS_MAX_LUT;
                Counts[Fixed[i][k]]--;
                Fixed[i][k] = j;
                Counts[j]++;
            }
        for ( i = 0; i < pPars->nNodes; ++i )
        for ( k = 1; k < pPars->nLutSize-(i > 0); ++k )
        for ( r = k; r > 0 && Fixed[i][r] < Fixed[i][r-1]; --r )
        {
            Temp = Fixed[i][r]; Fixed[i][r] = Fixed[i][r-1]; Fixed[i][r-1] = Temp;
        }
    }
    if ( !pPars->fSilent && (pPars->pPermStr || pPars->fLutInFixed || pPars->fUsePerm) )
    {
        printf("Input template: ");
        for ( i = 0; i < pPars->nNodes; ++i )
        {
            if ( i ) printf("_");
            for ( k = 0; k < pPars->nLutSize-(i > 0); ++k )
                printf("%c", Fixed[i][k] < 0 ? '*' : 'a'+Fixed[i][k]);
        }
        printf("\n");
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Ranks candidate final PI groups by residual-function diversity.]

  Description [Use only the specification. Prefer few distinct cofactors up
               to complementation, then few nonconstant rows. This is a search
               heuristic, never a proof rule. The bounded implementation handles
               at most ten inputs; larger functions retain the existing probes.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasRankLast( Bmc_EsPar_t * pPars, word * pSpec, int Masks[8], abctime timeStop )
{
    word Tables[1 << (CAS_MAX_LUT-1)][8], WordMask, Any;
    int Scores[8], Representatives[1 << (CAS_MAX_LUT-1)];
    int Mask, Bits, Count, nRows, nBits, nWords, x, j, a, b, na, nb;
    int Unique, Nonconstant, Score, Pos, nFound = 0;
    if ( pPars->pSymStr || pPars->nVars > 10 ) return 0;
    nRows = 1 << (pPars->nLutSize-1);
    nBits = 1 << (pPars->nVars-pPars->nLutSize+1);
    nWords = (nBits+63)/64;
    WordMask = nBits < 64 ? (((word)1 << nBits)-1) : ~(word)0;
    for ( j = 0; j < 8; ++j ) { Scores[j] = INT_MAX; Masks[j] = 0; }
    for ( Mask = 1; Mask < (1 << pPars->nVars); ++Mask )
    {
        if ( timeStop && Abc_Clock() >= timeStop ) break;
        Count = 0;
        for ( Bits = Mask; Bits; Bits &= Bits-1 ) Count++;
        if ( Count != pPars->nLutSize-1 ) continue;
        memset(Tables, 0, sizeof(Tables));
        for ( x = 0; x < (1 << pPars->nVars); ++x )
        {
            a = b = na = nb = 0;
            for ( j = 0; j < pPars->nVars; ++j )
                if ( (Mask >> j) & 1 ) a |= ((x >> j) & 1) << na++;
                else                      b |= ((x >> j) & 1) << nb++;
            if ( Abc_TtGetBit(pSpec, x) ) Tables[a][b >> 6] |= (word)1 << (b & 63);
        }
        Unique = Nonconstant = 0;
        for ( a = 0; a < nRows; ++a )
        {
            if ( Tables[a][0] & 1 )
                for ( j = 0; j < nWords; ++j ) Tables[a][j] = ~Tables[a][j] & WordMask;
            Any = 0;
            for ( j = 0; j < nWords; ++j ) Any |= Tables[a][j];
            Nonconstant += Any != 0;
            for ( b = 0; b < Unique; ++b )
                if ( !memcmp(Tables[a], Tables[Representatives[b]], nWords*sizeof(word)) ) break;
            if ( b == Unique ) Representatives[Unique++] = a;
        }
        Score = Unique*65536 + (Unique-(Nonconstant < nRows))*256 + Nonconstant;
        for ( Pos = 0; Pos < 8; ++Pos )
            if ( Score < Scores[Pos] ) break;
        if ( Pos == 8 ) continue;
        for ( j = 7; j > Pos; --j ) { Scores[j] = Scores[j-1]; Masks[j] = Masks[j-1]; }
        Scores[Pos] = Score;
        Masks[Pos] = Mask;
        if ( nFound < 8 ) nFound++;
    }
    return nFound;
}

/**Function*************************************************************

  Synopsis    [Maps an alternating placement into the caller's partial template.]

  Description [The small selector-only problem enforces the original fixed
               positions. A and B cover all PIs; C drops one PI from A, and
               later groups alternate B and C. Where A and B overlap, the
               dropped PI belongs to their intersection, as in the original
               low/high construction. This only proposes an input placement.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasMapAlternating( Bmc_EsPar_t * pPars, int nNodes,
    int Fixed[][CAS_MAX_LUT], int Probe[][CAS_MAX_LUT], abctime timeStop )
{
    Bmc_CasMan_t * p;
    int i, j, k, a, b, c, Status;
    if ( !pPars->pSymStr || nNodes < 2 || pPars->nVars > 2*pPars->nLutSize-1 ) return 0;
    p = ABC_CALLOC(Bmc_CasMan_t, 1);
    p->pPars = pPars;
    p->nVars = pPars->nVars;
    p->nLutSize = pPars->nLutSize;
    p->nNodes = nNodes;
    p->iNext = 1;
    Bmc_CasSolverStart(p);
    memcpy(p->Fixed, Fixed, sizeof(p->Fixed));
    for ( i = 0; i < nNodes; ++i )
    for ( j = 0; j < p->nVars; ++j ) p->Select[i][j] = p->iNext++;
    for ( i = 0; i < nNodes; ++i ) Bmc_CasExactly(p, i, p->nLutSize-(i > 0));
    for ( j = 0; j < p->nVars; ++j )
    {
        a = Abc_Var2Lit(p->Select[0][j], 0);
        b = Abc_Var2Lit(p->Select[1][j], 0);
        Bmc_CasBinary(p, a, b);
        if ( nNodes <= 2 ) continue;
        c = Abc_Var2Lit(p->Select[2][j], 0);
        Bmc_CasBinary(p, c ^ 1, a);
        if ( p->nVars < 2*p->nLutSize-1 ) Bmc_CasTernary(p, a ^ 1, c, b);
        for ( i = 3; i < nNodes; ++i )
        {
            a = Abc_Var2Lit(p->Select[i][j], 0);
            b = Abc_Var2Lit(p->Select[(i & 1) ? 1 : 2][j], 0);
            Bmc_CasBinary(p, a ^ 1, b);
            Bmc_CasBinary(p, a, b ^ 1);
        }
    }
    Bmc_CasReserve(p);
    p->timeStop = Abc_Clock()+CLOCKS_PER_SEC;
    if ( timeStop && timeStop < p->timeStop ) p->timeStop = timeStop;
    Status = Bmc_CasTerminate(p) ? 0 : Bmc_CasSolverSolve(p, 1000);
    if ( Status == CAS_SAT )
    {
        memset(Probe, 0xff, sizeof(int)*CAS_MAX_NODES*CAS_MAX_LUT);
        for ( i = 0; i < nNodes; ++i )
        {
            k = 0;
            for ( j = 0; j < p->nVars; ++j )
                if ( Bmc_CasModelValue(p, Abc_Var2Lit(p->Select[i][j], 0)) ) Probe[i][k++] = j;
            assert( k == p->nLutSize-(i > 0) );
            for ( j = 0; j < k; ++j ) assert( Fixed[i][j] < 0 || Fixed[i][j] == Probe[i][j] );
        }
    }
    Bmc_CasSolverStop(p);
    ABC_FREE(p);
    return Status == CAS_SAT;
}

/**Function*************************************************************

  Synopsis    [Tries an independently verified backward-decomposition candidate.]

  Description [Used only without caller input bindings. Derive once at the
               maximum count and retain the candidate across minimum-search
               counts. A failed attempt is not a lower bound. Pad unused pins
               and, if needed, append identity LUTs to match the requested
               dimensions. Preserve the coverage rule, normalize every rail,
               and verify the full truth table before reporting SAT. Failure
               to derive or pad a candidate says nothing about feasibility.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasBackwardCandidate( Bmc_EsPar_t * pPars, word * pSpec,
    int nNodes, abctime Begin, abctime timeStop, Bmc_CasProbe_t * pCache, Gia_Man_t ** ppGia )
{
    Bmc_CasMan_t * p = ABC_CALLOC(Bmc_CasMan_t, 1);
    int * pFans, nFound, Status = 0, i, j, k, t, m, n, Mask, Used = 0;
    int Address, Phase = 0, NextPhase, K = pPars->nLutSize;
    int nWords = Abc_TtWordNum(K);
    word * pTables;
    p->pPars = pPars;
    p->nVars = pPars->nVars;
    p->nNodes = nNodes;
    p->nLutSize = K;
    p->nMints = 1 << p->nVars;
    p->nWords = Abc_TtWordNum(p->nVars);
    p->pTruth = ABC_ALLOC(word, p->nWords);
    Abc_TtCopy(p->pTruth, pSpec, p->nWords, 0);
    p->fCompl = Abc_TtGetBit(p->pTruth, 0);
    if ( p->fCompl ) Abc_TtNot(p->pTruth, p->nWords);
    pFans = ABC_ALLOC(int, nNodes*K);
    pTables = ABC_ALLOC(word, nNodes*nWords);
    if ( !pCache->fBackwardTried )
    {
        pCache->fBackwardTried = 1;
        pCache->nFound = Bmc_Cas2Derive(p->pTruth, p->nVars, K, pPars->nNodes, 1,
            timeStop, pPars->Seed, pCache->Fans, pCache->Tables);
        if ( pPars->fVerbose && !pPars->fSilent )
            printf("Backward decomposition through M = %d: %d LUTs; cached for this function.\n",
                pPars->nNodes, Abc_MaxInt(0, pCache->nFound));
    }
    nFound = pCache->nFound;
    if ( nFound <= 0 ) { Status = nFound; goto finish; }
    if ( nFound > nNodes ) goto finish;
    memset(pFans, 0xff, sizeof(int)*nNodes*K);
    memset(pTables, 0, sizeof(word)*nNodes*nWords);
    memcpy(pFans, pCache->Fans, sizeof(int)*nFound*K);
    memcpy(pTables, pCache->Tables, sizeof(word)*nFound*nWords);
    for ( i = nFound; i < nNodes; ++i )
    {
        pFans[i*K] = p->nVars+i-1;
        Abc_TtSetBit(pTables+i*nWords, 1);
    }
    for ( i = 0; i < nNodes*K; ++i )
        if ( pFans[i] >= 0 && pFans[i] < p->nVars ) Used |= 1 << pFans[i];
    for ( i = 0; i < nNodes; ++i )
    {
        Mask = 0;
        n = i > 0;
        for ( k = i > 0; k < K && pFans[i*K+k] >= 0; ++k )
            Mask |= 1 << pFans[i*K+k], n++;
        while ( n < K )
        {
            for ( j = 0; j < p->nVars; ++j )
                if ( !(Used & (1 << j)) ) break;
            if ( j == p->nVars )
                for ( j = 0; j < p->nVars; ++j )
                    if ( !(Mask & (1 << j)) ) break;
            assert( j < p->nVars );
            Mask |= 1 << j;
            Used |= 1 << j;
            n++;
        }
        k = 0;
        if ( i ) p->Fans[i][k++] = p->nVars+i-1;
        for ( j = p->nVars-1; j >= 0; --j )
            if ( Mask & (1 << j) ) p->Fans[i][k++] = j;
        assert( k == K );
        NextPhase = Abc_TtGetBit(pTables+i*nWords, i ? Phase : 0);
        for ( m = 0; m < (1 << K); ++m )
        {
            Address = i ? ((m & 1) ^ Phase) : 0;
            for ( k = i > 0; k < K && pFans[i*K+k] >= 0; ++k )
            {
                for ( t = i > 0; t < K; ++t )
                    if ( p->Fans[i][t] == pFans[i*K+k] ) break;
                assert( t < K );
                Address |= ((m >> t) & 1) << k;
            }
            if ( Abc_TtGetBit(pTables+i*nWords, Address) ^ NextPhase )
                Abc_TtSetBit(p->Truths[i], m);
        }
        Phase = NextPhase;
    }
    // A smaller-support candidate can consume too many slots on repeated
    // inputs to meet the separate PI-coverage requirement. Fall back to SAT.
    if ( Used != (1 << p->nVars)-1 ) goto finish;
    if ( Phase || !Bmc_CasVerify(p) )
    {
        Abc_Print(-1, "Internal error: backward cascade failed verification.\n");
        Status = -1;
        goto finish;
    }
    Bmc_CasPrint(p);
    Status = CAS_SAT;
    if ( pPars->fDumpBlif && !Bmc_CasDump(p) ) Status = -1;
    if ( Status == CAS_SAT ) *ppGia = Bmc_CasDerive(p);
    if ( !pPars->fSilent )
    {
        printf("Cascade witness found by backward decomposition.\n");
        Abc_PrintTime(1, "Total runtime", Abc_Clock()-Begin);
    }
finish:
    ABC_FREE(pTables);
    ABC_FREE(pFans);
    ABC_FREE(p->pTruth);
    ABC_FREE(p);
    return Status;
}

/**Function*************************************************************

  Synopsis    [Tries bounded internal placements before the complete synthesis problem.]

  Description [Proposals preserve any input constraints supplied by the caller.
               Only the specification and constraints guide their selection.
               A SAT probe is a valid witness for the original problem. UNSAT
               or UNKNOWN probes do not establish a bound; only the original
               full search can prove UNSAT for this count. A bounded minimum
               search may skip an undecided count without proving a minimum.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasProbeFree( Bmc_EsPar_t * pPars, word * pSpec, int nNodes,
    int Fixed[][CAS_MAX_LUT], int fMuxConsensus, int fBackward, int fPhase,
    int nProbeSeconds, Bmc_CasProbe_t * pCache, Gia_Man_t ** ppGia )
{
    Bmc_EsPar_t Trial = *pPars, Final = *pPars;
    int Probe[CAS_MAX_NODES][CAS_MAX_LUT], Retry[CAS_MAX_NODES][CAS_MAX_LUT];
    int i, j, k, Status, nRank = 0, nTrials = 8, fPartial, fRetry = 0, RetryTime;
    unsigned Random = (unsigned)pPars->Seed ^ 0x9e3779b9u;
    abctime Begin = Abc_Clock(), Deadline = pPars->RuntimeLim ?
        Begin + (abctime)pPars->RuntimeLim * CLOCKS_PER_SEC : 0;
    abctime timeProbe = nProbeSeconds >= 0 ? Begin + (abctime)nProbeSeconds*CLOCKS_PER_SEC : Deadline;
    if ( Deadline && (!timeProbe || Deadline < timeProbe) ) timeProbe = Deadline;
    // Symmetric specifications benefit from conditional rail normalization.
    // An explicit -e also enables it for arbitrary functions.
    fPhase |= pPars->pSymStr != NULL;
    fPartial = pPars->pPermStr && strchr(pPars->pPermStr, '*');
    if ( (pPars->pPermStr && (!fPartial || !pPars->pSymStr)) ||
         pPars->fLutInFixed || pPars->fUsePerm || pPars->nVars < 7 ||
         nNodes < 2 || pPars->RuntimeLim == 1 ||
         pPars->nVars > 1+nNodes*(pPars->nLutSize-1) )
        return Bmc_CasSolve(pPars, pSpec, nNodes, Fixed, fMuxConsensus, fBackward, fPhase, 0, 0, 0, 0, 1, 0, ppGia);
    if ( !fPartial && !pPars->pSymStr &&
         (!timeProbe || Abc_Clock() < timeProbe) )
    {
        Status = Bmc_CasBackwardCandidate(pPars, pSpec, nNodes, Begin, timeProbe, pCache, ppGia);
        if ( Status ) return Status;
    }
    if ( fPartial )
    {
        if ( (timeProbe && Abc_Clock() >= timeProbe) || !Bmc_CasMapAlternating(pPars, nNodes, Fixed, Probe, timeProbe) )
            nTrials = 0;
        else
            nTrials = 1;
    }
    else
    {
        // Rankings depend on the function and K, not the number of stages.
        // SAT outcomes of restricted placements do depend on that count and
        // are never reused as lower bounds for another synthesis problem.
        if ( !pCache->fRanked && (!timeProbe || Abc_Clock() < timeProbe) )
        {
            pCache->nRank = Bmc_CasRankLast(pPars, pSpec, pCache->Masks, timeProbe);
            pCache->fRanked = 1;
        }
        nRank = pCache->nRank;
        if ( nRank ) nTrials = nRank;
    }
    Trial.nNodes = nNodes;
    Trial.fSilent = 1;
    Trial.fVerbose = 0;
    Trial.RuntimeLim = nRank ? 4 : 1;
    // Negative probes never establish a lower bound. The original complete
    // search follows, retaining the caller's input constraints and time limit.
    for ( i = 0; i < nTrials; ++i )
    {
        if ( timeProbe && Abc_Clock() >= timeProbe ) break;
        if ( nProbeSeconds < 0 && Deadline && Abc_Clock()+(abctime)Trial.RuntimeLim*CLOCKS_PER_SEC >= Deadline ) break;
        if ( nRank )
        {
            memset(Probe, 0xff, sizeof(Probe));
            k = 0;
            for ( j = 0; j < pPars->nVars; ++j )
                if ( (pCache->Masks[i] >> j) & 1 ) Probe[nNodes-1][k++] = j;
        }
        else if ( !fPartial )
        {
            Trial.fUsePerm = i == 0 && pPars->nVars <= 2*pPars->nLutSize-1;
            Trial.fLutInFixed = !Trial.fUsePerm;
            if ( !Bmc_CasInputs(&Trial, Probe, &Random) ) return -1;
        }
        Status = Bmc_CasSolve(&Trial, pSpec, nNodes, Probe, fMuxConsensus, fBackward, fPhase, 0, nRank ? 50000 : 1000, 0, 0, 1, timeProbe, ppGia);
        if ( Status < 0 ) return Status;
        // Retain the original probe first. If its budget is exhausted, try
        // the same placement with compact stages and direct final-rail
        // constraints. A proved-infeasible placement needs no second solve.
        if ( nRank && Status == 0 &&
             (!timeProbe || Abc_Clock() < timeProbe) &&
             (nProbeSeconds >= 0 || !Deadline || Abc_Clock()+CLOCKS_PER_SEC < Deadline) )
        {
            Bmc_EsPar_t Quick = Trial;
            Quick.RuntimeLim = 1;
            Status = Bmc_CasSolve(&Quick, pSpec, nNodes, Probe,
                fMuxConsensus, fBackward, fPhase, 1, 25000, 0, 0, 1, timeProbe, ppGia);
            if ( Status < 0 ) return Status;
        }
        if ( i == 0 && Status == 0 && !fPartial && pPars->pSymStr &&
             pPars->nVars >= 11 && pPars->nVars <= 2*pPars->nLutSize-1 )
        {
            memcpy(Retry, Probe, sizeof(Retry));
            fRetry = 1;
        }
        if ( pPars->fVerbose && !pPars->fSilent )
            printf("Internal probe %d: status %d after %.3f seconds.\n", i+1, Status, (double)(Abc_Clock()-Begin)/CLOCKS_PER_SEC);
        if ( Status == CAS_SAT )
        {
            if ( !pPars->fSilent )
            {
                printf("Cascade witness found by internal template probe %d.\n", i+1);
                Abc_PrintTime(1, "Total runtime", Abc_Clock()-Begin);
            }
            return Status;
        }
    }
    // The initial conflict cap is cheap but can abandon a useful fixed
    // placement before solving starts in earnest. Retry only after all
    // quick probes fail, using at most five percent of the original budget.
    RetryTime = pPars->RuntimeLim ? Abc_MinInt(10, pPars->RuntimeLim/20) : 10;
    if ( fRetry && RetryTime > 0 &&
         (!timeProbe || Abc_Clock() < timeProbe) &&
         (nProbeSeconds >= 0 || !Deadline || Abc_Clock()+(abctime)RetryTime*CLOCKS_PER_SEC < Deadline) )
    {
        Trial.RuntimeLim = RetryTime;
        Status = Bmc_CasSolve(&Trial, pSpec, nNodes, Retry,
            fMuxConsensus, fBackward, fPhase, 0, 0, 0, 0, 1, timeProbe, ppGia);
        if ( Status < 0 ) return Status;
        if ( pPars->fVerbose && !pPars->fSilent )
            printf("Canonical placement retry: status %d after %.3f seconds.\n",
                Status, (double)(Abc_Clock()-Begin)/CLOCKS_PER_SEC);
        if ( Status == CAS_SAT )
        {
            if ( !pPars->fSilent )
            {
                printf("Cascade witness found by canonical placement retry.\n");
                Abc_PrintTime(1, "Total runtime", Abc_Clock()-Begin);
            }
            return Status;
        }
        // This is still a restricted placement. Its UNSAT result does not
        // prove the unrestricted problem; continue with the full encoding.
    }
    if ( Deadline )
    {
        abctime Remaining = Deadline-Abc_Clock();
        if ( Remaining <= 0 )
        {
            if ( !pPars->fSilent )
            {
                printf("Unknown: cascade time limit exhausted during internal probes.\n");
                Abc_PrintTime(1, "Total runtime", Abc_Clock()-Begin);
            }
            return 0;
        }
        // Retain a fractional final second; the absolute deadline below
        // clips the solver call, so rounding up does not extend -T.
        Final.RuntimeLim = 1+(int)((Remaining-1)/CLOCKS_PER_SEC);
    }
    if ( pPars->fVerbose && nProbeSeconds >= 0 && !pPars->fSilent )
        printf("Candidate probes used %.3f seconds; continuing with exact SAT.\n", (double)(Abc_Clock()-Begin)/CLOCKS_PER_SEC);
    return Bmc_CasSolve(&Final, pSpec, nNodes, Fixed, fMuxConsensus, fBackward, fPhase, 0, 0, Begin, 1, nProbeSeconds < 0, Deadline, ppGia);
}

/**Function*************************************************************

  Synopsis    [Synthesizes one function, optionally minimizing the LUT count.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasRun( Bmc_EsPar_t * pPars, word * pSpec, unsigned * pRandom, int fMuxConsensus, int fBackward, int fPhase, int fProbe, int nProbeSeconds, Gia_Man_t ** ppGia )
{
    Bmc_CasProbe_t Cache;
    int Fixed[CAS_MAX_NODES][CAS_MAX_LUT];
    int n, Status = CAS_UNSAT, FirstUnknown = -1;
    int nMin = pPars->fMinNodes ? (pPars->nVars-2)/(pPars->nLutSize-1)+1 : pPars->nNodes;
    int fConstrained = pPars->pPermStr || pPars->fLutInFixed || pPars->fUsePerm;
    if ( !Bmc_CasInputs(pPars, Fixed, pRandom) ) return -1;
    memset(&Cache, 0, sizeof(Cache));
    for ( n = nMin; n <= pPars->nNodes; ++n )
    {
        if ( pPars->fMinNodes && !pPars->fSilent ) printf("\nTrying M = %d:\n", n);
        Status = fProbe && nProbeSeconds != 0 ? Bmc_CasProbeFree(pPars, pSpec, n, Fixed, fMuxConsensus, fBackward, fPhase, nProbeSeconds, &Cache, ppGia) :
            Bmc_CasSolve(pPars, pSpec, n, Fixed, fMuxConsensus, fBackward, fPhase, 0, 0, 0, 0, 0, 0, ppGia);
        if ( !Bmc_ExactContinue(Status, pPars->fMinNodes, pPars->RuntimeLim, n, &FirstUnknown) ) break;
    }
    if ( pPars->fMinNodes && !pPars->fSilent )
        Bmc_ExactReport(Status, FirstUnknown, n, pPars->nNodes, "LUT",
            fConstrained ? " within the input-template prefixes" : "");
    return Status == CAS_UNSAT && FirstUnknown >= 0 ? 0 : Status;
}

/**Function*************************************************************

  Synopsis    [Generates a random truth table with optional fixed density.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_CasRandomTruth( word * pTruth, int nVars, int nOnes, unsigned * pRandom )
{
    int i, j, Temp, nMints = 1 << nVars, nWords = Abc_TtWordNum(nVars);
    if ( nOnes < 0 )
        for ( i = 0; i < nWords; ++i )
        {
            word Low = Bmc_CasRandom(pRandom);
            pTruth[i] = Low | ((word)Bmc_CasRandom(pRandom) << 32);
        }
    else
    {
        int * pMints = ABC_ALLOC(int, nMints);
        Abc_TtClear(pTruth, nWords);
        for ( i = 0; i < nMints; ++i ) pMints[i] = i;
        for ( i = 0; i < nOnes; ++i )
        {
            j = i + Bmc_CasRandom(pRandom) % (nMints-i);
            Temp = pMints[i]; pMints[i] = pMints[j]; pMints[j] = Temp;
            Abc_TtSetBit(pTruth, pMints[i]);
        }
        ABC_FREE(pMints);
    }
    if ( nVars < 6 ) pTruth[0] = Abc_Tt6Stretch(pTruth[0], nVars);
}

/**Function*************************************************************

  Synopsis    [Reads and validates a nonnegative numeric option.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasReadNumber( int argc, char ** argv, int c, int * pValue )
{
    char * pEnd;
    long Value;
    if ( globalUtilOptind >= argc )
    {
        Abc_Print(-1, "Option -%c requires an integer.\n", c);
        return 0;
    }
    errno = 0;
    Value = strtol(argv[globalUtilOptind], &pEnd, 10);
    if ( errno || pEnd == argv[globalUtilOptind] || *pEnd || Value < 0 || Value > INT_MAX )
    {
        Abc_Print(-1, "Option -%c requires an integer in [0, %d].\n", c, INT_MAX);
        return 0;
    }
    globalUtilOptind++;
    *pValue = (int)Value;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Prints command usage.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_CasUsage( void )
{
    Abc_Print(-2, "usage: casexact [-NMKTFUSB <num>] [-Y string] [-P string] [-fmdpjckebqsvh] [hex]\n");
    Abc_Print(-2, "\t          exact synthesis of a single-rail LUT cascade; Kissat by default\n");
    Abc_Print(-2, "\t-N <num> : number of PIs, 2..14 [infer from truth table, -Y, or network]\n");
    Abc_Print(-2, "\t-M <num> : LUT count, 1..64; upper bound with -m [required, or infer from -P]\n");
    Abc_Print(-2, "\t-K <num> : LUT size, 2..8, no larger than N [default = 2]\n");
    Abc_Print(-2, "\t-T <num> : solver time limit per LUT count, in seconds [default = 0: unlimited]\n");
    Abc_Print(-2, "\t-B <num> : candidate seconds per count with -q; 0 disables [default = automatic]\n");
    Abc_Print(-2, "\t           within -T; failed probes still fall through to exact SAT\n");
    Abc_Print(-2, "\t           positive -B skips the matrix shortcut in the final SAT fallback\n");
    Abc_Print(-2, "\t-P <str> : ordered PI positions, e.g. abcd_aef or a*cd_*** for K=4, M=2\n");
    Abc_Print(-2, "\t           K letters for stage 1, then K-1 per stage; '_' separates stages\n");
    Abc_Print(-2, "\t           letters a..n name PIs in order; '*' leaves that position free\n");
    Abc_Print(-2, "\t-f       : toggle fixing a random template covering all PIs [default = no]\n");
    Abc_Print(-2, "\t-S <num> : random seed, 0..2000000000 [default = 0]\n");
    Abc_Print(-2, "\t           applies to -f/-F/-q and CaDiCaL; Kissat has fixed internal options\n");
    Abc_Print(-2, "\t-m       : toggle minimum LUT-count search through M [default = no]\n");
    Abc_Print(-2, "\t           inputs are free unless -P/-f/-p is given; templates use prefixes\n");
    Abc_Print(-2, "\t           -T skips undecided counts; a later SAT answer is only an upper bound\n");
    Abc_Print(-2, "\t-p       : toggle fixed alternating low/high PI groups [default = no]\n");
    Abc_Print(-2, "\t           requires -m and N <= 2*K-1; -P, -f, and -p are mutually exclusive\n");
    Abc_Print(-2, "\t-Y <str> : N+1 binary values for a symmetric function, by increasing weight\n");
    Abc_Print(-2, "\t-F <num> : synthesize this many random functions [requires -N]\n");
    Abc_Print(-2, "\t           each successful function replaces the current network\n");
    Abc_Print(-2, "\t-U <num> : exactly this many 1-minterms with -F [default = random density]\n");
    Abc_Print(-2, "\t-c       : toggle using CaDiCaL instead of Kissat [default = no]\n");
    Abc_Print(-2, "\t-k       : toggle explicit Kissat selection [default = no]\n");
    Abc_Print(-2, "\t           -c and -k are mutually exclusive\n");
    Abc_Print(-2, "\t-j       : toggle two consensus clauses per 2:1 rail mux [default = no]\n");
    Abc_Print(-2, "\t           already included for fully fixed symmetric templates\n");
    Abc_Print(-2, "\t-e       : toggle shared-input rail phase normalization [default = no]\n");
    Abc_Print(-2, "\t-q       : toggle guided cascade and input-placement probes [default = no]\n");
    Abc_Print(-2, "\t           retain caller constraints; enable rail normalization with -Y\n");
    Abc_Print(-2, "\t           try verified matrix witnesses for symmetric alternating templates\n");
    Abc_Print(-2, "\t           try backward decomposition without bindings; failed probes resume SAT\n");
    Abc_Print(-2, "\t           with -m, reuse backward decomposition and PI rankings across counts\n");
    Abc_Print(-2, "\t-b       : toggle final-stage backward distinguishability clauses [default = no]\n");
    Abc_Print(-2, "\t-d       : toggle solution dumps to casexact_*.blif and .v [default = no]\n");
    Abc_Print(-2, "\t-s       : toggle printing only solutions and the -F summary [default = no]\n");
    Abc_Print(-2, "\t-v       : toggle CNF construction and solver timings [default = no]\n");
    Abc_Print(-2, "\t-h       : print the command usage\n");
    Abc_Print(-2, "\t[hex]    : truth table, least significant bit = all-zero input\n");
    Abc_Print(-2, "\t           without hex/-Y/-F, use the current single-output combinational network\n");
    Abc_Print(-2, "\tStage 1 uses K distinct PIs; later stages use the previous rail and K-1 PIs.\n");
    Abc_Print(-2, "\tEvery PI is selected somewhere. LUTs may ignore selected pins.\n");
    Abc_Print(-2, "\tVerified solutions replace the current network; &-space is unchanged.\n");
}

/**Function*************************************************************

  Synopsis    [Implements the casexact command.]

  Description [Keep the command and its implementation here; lutexact is independent.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCasExact( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Bmc_EsPar_t Pars, * p = &Pars;
    word * pTruth = NULL;
    char * pHex = NULL;
    Gia_Man_t * pGia = NULL;
    Bmc_Exact_t Target = {0};
    unsigned RandomFuncs, RandomPins;
    int c, Value, i, n, Status, Ret = 1, nResults[3] = {0};
    int fN = 0, fM = 0, fF = 0, fMuxConsensus = 0, fBackward = 0, fPhase = 0, fProbe = 0;
    int nProbeSeconds = -1;
    Bmc_EsParSetDefault(p);
    p->nMintNum = -1;
    p->fLutCascade = 1;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "NMKTFUSBYPfmdpjckebqsvh")) != EOF )
    {
        switch ( c )
        {
        case 'N': case 'M': case 'K': case 'T': case 'F': case 'U': case 'S': case 'B':
            if ( !Bmc_CasReadNumber(argc, argv, c, &Value) ) goto finish;
            if      ( c == 'N' ) { p->nVars = Value; fN = 1; }
            else if ( c == 'M' ) { p->nNodes = Value; fM = 1; }
            else if ( c == 'K' ) p->nLutSize = Value;
            else if ( c == 'T' ) p->RuntimeLim = Value;
            else if ( c == 'B' ) nProbeSeconds = Value;
            else if ( c == 'F' ) { p->nRandFuncs = Value; fF = 1; }
            else if ( c == 'U' ) p->nMintNum = Value;
            else                p->Seed = Value;
            break;
        case 'Y': case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print(-1, "Option -%c requires a string.\n", c);
                goto finish;
            }
            if ( c == 'Y' ) p->pSymStr = argv[globalUtilOptind++];
            else            p->pPermStr = argv[globalUtilOptind++];
            break;
        case 'f': p->fLutInFixed ^= 1; break;
        case 'm': p->fMinNodes ^= 1; break;
        case 'd': p->fDumpBlif ^= 1; break;
        case 'p': p->fUsePerm ^= 1; break;
        case 'j': fMuxConsensus ^= 1; break;
        case 'c': p->fCadical ^= 1; break;
        case 'k': p->fKissat ^= 1; break;
        case 'b': fBackward ^= 1; break;
        case 'e': fPhase ^= 1; break;
        case 'q': fProbe ^= 1; break;
        case 's': p->fSilent ^= 1; break;
        case 'v': p->fVerbose ^= 1; break;
        case 'h': Bmc_CasUsage(); goto finish;
        default:  Bmc_CasUsage(); goto finish;
        }
    }
    if ( p->fCadical && p->fKissat )
    {
        Abc_Print(-1, "Options -c and -k cannot be combined.\n");
        goto finish;
    }
    if ( p->Seed > 2000000000 )
    {
        Abc_Print(-1, "The random seed must be in 0..2000000000.\n");
        goto finish;
    }
    if ( argc > globalUtilOptind+1 )
    {
        Abc_Print(-1, "Expected at most one hexadecimal truth table.\n");
        goto finish;
    }
    if ( argc == globalUtilOptind+1 ) p->pTtStr = argv[globalUtilOptind];
    if ( (int)(p->pTtStr != NULL) + (int)(p->pSymStr != NULL) + fF > 1 )
    {
        Abc_Print(-1, "Choose one of a hexadecimal truth table, -Y, and -F.\n");
        goto finish;
    }
    if ( p->nLutSize < 2 || p->nLutSize > CAS_MAX_LUT ||
         (fN && (p->nVars < 2 || p->nVars > CAS_MAX_VARS)) ||
         (fM && (p->nNodes < 1 || p->nNodes > CAS_MAX_NODES)) || (fF && p->nRandFuncs < 1) )
    {
        Abc_Print(-1, "Expected N in 2..14, K in 2..8, M in 1..64, and a positive -F count.\n");
        goto finish;
    }
    if ( p->pSymStr )
    {
        n = (int)strlen(p->pSymStr)-1;
        if ( n < 2 || n > CAS_MAX_VARS || (fN && p->nVars != n) )
        {
            Abc_Print(-1, "Symmetric function needs N+1 values with N in 2..14.\n");
            goto finish;
        }
        for ( i = 0; i <= n; ++i )
            if ( p->pSymStr[i] != '0' && p->pSymStr[i] != '1' )
            {
                Abc_Print(-1, "Symmetric function values must be 0 or 1.\n");
                goto finish;
            }
        p->nVars = n;
    }
    else if ( !fF )
    {
        if ( !Bmc_ExactRead(pAbc, p->pTtStr, fN ? p->nVars : -1, CAS_MAX_VARS, &Target) ) goto finish;
        p->nVars = Target.nVars;
    }
    if ( p->nVars < 2 || p->nVars > CAS_MAX_VARS || p->nLutSize > p->nVars )
    {
        Abc_Print(-1, "Require 2 <= K <= N <= 14 (use -N for random functions).\n");
        goto finish;
    }
    if ( !fM && p->pPermStr && strlen(p->pPermStr) <= (size_t)(CAS_MAX_NODES*p->nLutSize) )
        p->nNodes = (int)strlen(p->pPermStr)/p->nLutSize;
    if ( p->nNodes < 1 || p->nNodes > CAS_MAX_NODES )
    {
        Abc_Print(-1, "Specify -M in 1..64, or a complete -P template.\n");
        goto finish;
    }
    if ( p->nVars > p->nNodes*(p->nLutSize-1)+1 )
    {
        Abc_Print(-1, "M LUTs have too few PI positions to cover all N inputs.\n");
        goto finish;
    }
    if ( (int)(p->pPermStr != NULL) + p->fLutInFixed + p->fUsePerm > 1 )
    {
        Abc_Print(-1, "-P, -f, and -p are mutually exclusive.\n");
        goto finish;
    }
    if ( p->fUsePerm && (!p->fMinNodes || p->nVars > 2*p->nLutSize-1) )
    {
        Abc_Print(-1, "-p requires -m and N <= 2*K-1.\n");
        goto finish;
    }
    if ( p->nMintNum >= 0 && (!fF || p->nMintNum > (1 << p->nVars)) )
    {
        Abc_Print(-1, "-U requires -F and a count in 0..2^N.\n");
        goto finish;
    }
    RandomFuncs = (unsigned)p->Seed ^ 0x9e3779b9u;
    RandomPins  = (unsigned)p->Seed ^ 0x85ebca6bu;
    if ( !Target.pTruth )
        Target.pTruth = p->pSymStr ? Abc_TtSymFunGenerate(p->pSymStr, p->nVars) : ABC_CALLOC(word, Abc_TtWordNum(p->nVars));
    Target.nVars = p->nVars;
    pTruth = Target.pTruth;
    if ( p->nVars < 6 ) pTruth[0] = Abc_Tt6Stretch(pTruth[0], p->nVars);
    if ( fF ) pHex = ABC_ALLOC(char, (1 << (p->nVars-2))+1);
    for ( i = 0; i < (fF ? p->nRandFuncs : 1); ++i )
    {
        if ( fF )
        {
            Bmc_CasRandomTruth(pTruth, p->nVars, p->nMintNum, &RandomFuncs);
            if ( !p->fSilent ) printf("\nFunction %d:\n", i+1);
            if ( p->fVerbose && !p->fSilent )
            {
                Extra_PrintHexadecimalString(pHex, (unsigned *)pTruth, p->nVars);
                printf("Truth table: %s\n", pHex);
            }
        }
        Status = Bmc_CasRun(p, pTruth, &RandomPins, fMuxConsensus, fBackward, fPhase, fProbe, nProbeSeconds, &pGia);
        if ( Status < 0 ) goto finish;
        if ( Status == CAS_SAT )
        {
            if ( !Bmc_ExactInstall(pAbc, pGia, &Target) ) goto finish;
            pGia = NULL;
        }
        nResults[Status == CAS_SAT ? 1 : Status == CAS_UNSAT ? 2 : 0]++;
    }
    if ( fF ) printf("Random functions: SAT = %d, UNSAT = %d, UNKNOWN = %d (total %d).\n", nResults[1], nResults[2], nResults[0], p->nRandFuncs);
    Ret = 0;
finish:
    if ( pGia ) Gia_ManStop(pGia);
    ABC_FREE(Target.pTruth);
    ABC_FREE(pHex);
    return Ret;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
