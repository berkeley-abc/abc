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
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/cmd/cmd.h"
#include "misc/extra/extra.h"
#include "misc/util/utilTruth.h"
#include "sat/kissat/kissat.h"
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
    abctime timeStop;
    word nClauses, nLiterals;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

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
        kissat_add( p->pSat, (Lits[i] & 1) ? -(Abc_Lit2Var(Lits[i])+1) : Abc_Lit2Var(Lits[i])+1 );
    kissat_add( p->pSat, 0 );
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
    if ( p->fFixed && (i || p->nNodes > 1) ) return Bmc_CasFixedCofactor(p, i, b, x);
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

  Synopsis    [Connects stage cofactors through the incoming rail.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_CasMuxes( Bmc_CasMan_t * p, int i )
{
    int r, x, a, c, d, z;
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
    kissat_reserve(p->pSat, p->iNext);
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
    p->fFixed = p->pPars->pSymStr != NULL;
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
            for ( b = 0; b < 2; ++b )
            {
                p->CofBase[i][b] = p->iNext;
                p->iNext += p->nMints;
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
        for ( j = 0; j < p->nVars; ++j )
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
    kissat_reserve(p->pSat, p->iNext);
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

  Synopsis    [Reads the Boolean value of an internal literal from the SAT model.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasModelValue( Bmc_CasMan_t * p, int Lit )
{
    if ( Lit < 2 ) return Lit;
    return (kissat_value(p->pSat, Abc_Lit2Var(Lit)+1) > 0) ^ (Lit & 1);
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

  Synopsis    [Solves and verifies a cascade with a fixed number of LUTs.]

  Description [Returns Kissat's SAT/UNSAT/UNKNOWN result, or -1 for an internal/I/O error.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasSolve( Bmc_EsPar_t * pPars, word * pSpec, int nNodes, int Fixed[][CAS_MAX_LUT], int fMuxConsensus, int fBackward )
{
    Bmc_CasMan_t * p = ABC_CALLOC(Bmc_CasMan_t, 1);
    abctime clk = Abc_Clock(), clkSolve;
    int Status, i;
    p->pPars = pPars;
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
    p->pSat = kissat_init();
    if ( !pPars->fSilent )
        printf("Running exact cascade synthesis for %d-input function with %d %d-input LUTs (Kissat)...\n", p->nVars, p->nNodes, p->nLutSize);
    Bmc_CasBuild(p);
    // Append after the base CNF to retain the benchmarked clause order.
    if ( fBackward ) Bmc_CasBackward(p);
    if ( fMuxConsensus ) Bmc_CasMuxConsensus(p);
    if ( !pPars->fSilent && p->nRows < p->nMints )
        printf("Symmetry: %d representatives of %d input assignments.\n", p->nRows, p->nMints);
    if ( !pPars->fSilent )
        printf("CNF: %d variables, %llu clauses, %llu literals.\n", p->iNext, (unsigned long long)p->nClauses, (unsigned long long)p->nLiterals);
    clkSolve = Abc_Clock();
    if ( pPars->RuntimeLim )
        p->timeStop = clkSolve + (abctime)pPars->RuntimeLim * CLOCKS_PER_SEC;
    kissat_set_terminate(p->pSat, p, Bmc_CasTerminate);
    Status = kissat_solve(p->pSat);
    if ( pPars->fVerbose && !pPars->fSilent )
    {
        Abc_PrintTime(1, "CNF construction", clkSolve-clk);
        Abc_PrintTime(1, "Kissat solving", Abc_Clock()-clkSolve);
    }
    if ( Status == CAS_SAT )
    {
        Bmc_CasDecode(p);
        if ( !Bmc_CasVerify(p) )
        {
            Abc_Print(-1, "Internal error: cascade failed exhaustive verification.\n");
            Status = -1;
        }
        else
        {
            Bmc_CasPrint(p);
            if ( pPars->fDumpBlif && !Bmc_CasDump(p) ) Status = -1;
        }
    }
    else if ( Status == CAS_UNSAT && !pPars->fSilent )
        printf("The problem has no solution.\n");
    else if ( Status == 0 && !pPars->fSilent )
        printf("Unknown: Kissat stopped after reaching the %d-second solver limit.\n", pPars->RuntimeLim);
    if ( !pPars->fSilent ) Abc_PrintTime(1, "Total runtime", Abc_Clock()-clk);
    kissat_release(p->pSat);
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

  Synopsis    [Synthesizes one function, optionally minimizing the LUT count.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_CasRun( Bmc_EsPar_t * pPars, word * pSpec, unsigned * pRandom, int fMuxConsensus, int fBackward )
{
    int Fixed[CAS_MAX_NODES][CAS_MAX_LUT];
    int n, Status = CAS_UNSAT;
    int nMin = pPars->fMinNodes ? (pPars->nVars-2)/(pPars->nLutSize-1)+1 : pPars->nNodes;
    int fConstrained = pPars->pPermStr || pPars->fLutInFixed || pPars->fUsePerm;
    if ( !Bmc_CasInputs(pPars, Fixed, pRandom) ) return -1;
    for ( n = nMin; n <= pPars->nNodes; ++n )
    {
        if ( pPars->fMinNodes && !pPars->fSilent ) printf("\nTrying M = %d:\n", n);
        Status = Bmc_CasSolve(pPars, pSpec, n, Fixed, fMuxConsensus, fBackward);
        if ( Status != CAS_UNSAT ) break;
    }
    if ( pPars->fMinNodes && !pPars->fSilent )
    {
        if ( Status == CAS_SAT )
            printf("Minimum LUT count%s = %d.\n", fConstrained ? " within the input-template prefixes" : "", n);
        else if ( Status == 0 )
            printf("Search stopped at M = %d; the minimum is unknown.\n", n);
        else if ( Status == CAS_UNSAT )
            printf("No solution with at most %d LUTs%s.\n", pPars->nNodes, fConstrained ? " within the input-template prefixes" : "");
    }
    return Status;
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
    Abc_Print(-2, "usage: casexact [-NMKTFUS <num>] [-Y string] [-P string] [-fmdpcbsvh] [hex]\n");
    Abc_Print(-2, "           exact synthesis of a single-rail LUT cascade using ABC's Kissat\n");
    Abc_Print(-2, " -N <num> : number of PIs, 2..14 [infer from truth table, -Y, or network]\n");
    Abc_Print(-2, " -M <num> : LUT count, 1..64; upper bound with -m [required, or infer from -P]\n");
    Abc_Print(-2, " -K <num> : LUT size, 2..8, no larger than N [default = 2]\n");
    Abc_Print(-2, " -T <num> : solver time limit per LUT count, in seconds [default = 0: unlimited]\n");
    Abc_Print(-2, " -P <str> : ordered PI positions, e.g. abcd_aef or a*cd_*** for K=4, M=2\n");
    Abc_Print(-2, "            K letters for stage 1, then K-1 per stage; '_' separates stages\n");
    Abc_Print(-2, "            letters a..n name PIs in order; '*' leaves that position free\n");
    Abc_Print(-2, " -f       : fix a random input template that covers all PIs [default = no]\n");
    Abc_Print(-2, " -S <num> : reproducible random seed for -f and -F [default = 0]\n");
    Abc_Print(-2, " -m       : search the minimum LUT count through M [default = no]\n");
    Abc_Print(-2, "            inputs are free unless -P/-f/-p is given; templates use prefixes\n");
    Abc_Print(-2, "            stop on UNKNOWN, without claiming a minimum\n");
    Abc_Print(-2, " -p       : with -m, fix alternating low/high PI groups [requires N <= 2*K-1]\n");
    Abc_Print(-2, "            -P, -f, and -p are mutually exclusive\n");
    Abc_Print(-2, " -Y <str> : N+1 binary values for a symmetric function, by increasing weight\n");
    Abc_Print(-2, " -F <num> : synthesize this many random functions [requires -N]\n");
    Abc_Print(-2, " -U <num> : exactly this many 1-minterms with -F [default = random density]\n");
    Abc_Print(-2, " -c       : add two consensus clauses per 2:1 rail mux [default = no]\n");
    Abc_Print(-2, "            already included for fully fixed symmetric templates\n");
    Abc_Print(-2, " -b       : add backward distinguishability clauses at the final stage [default = no]\n");
    Abc_Print(-2, " -d       : dump each solution to casexact_*.blif and portable Verilog .v\n");
    Abc_Print(-2, " -s       : print only solutions (and the -F summary)\n");
    Abc_Print(-2, " -v       : print CNF construction and solver timings\n");
    Abc_Print(-2, " -h       : print this help\n");
    Abc_Print(-2, " [hex]    : truth table, least significant bit = all-zero input\n");
    Abc_Print(-2, "            without hex/-Y/-F, use the current single-output combinational network\n");
    Abc_Print(-2, " Stage 1 uses K distinct PIs; later stages use the previous rail and K-1 PIs.\n");
    Abc_Print(-2, " Every PI is selected somewhere. LUTs may ignore selected pins.\n");
}

/**Function*************************************************************

  Synopsis    [Implements the casexact command.]

  Description [Keep the command and its implementation here; lutexact is independent.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCasExact( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern char * Abc_NtkReadTruth( Abc_Ntk_t * pNtk );
    Bmc_EsPar_t Pars, * p = &Pars;
    word * pTruth = NULL;
    char * pOwnedTruth = NULL, * pHex = NULL;
    unsigned RandomFuncs, RandomPins;
    int c, Value, i, n, Status, Ret = 1, nResults[3] = {0};
    int fN = 0, fM = 0, fF = 0, fMuxConsensus = 0, fBackward = 0;
    Bmc_EsParSetDefault(p);
    p->nMintNum = -1;
    p->fKissat = p->fLutCascade = 1;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "NMKTFUSYPfmdpcbsvh")) != EOF )
    {
        switch ( c )
        {
        case 'N': case 'M': case 'K': case 'T': case 'F': case 'U': case 'S':
            if ( !Bmc_CasReadNumber(argc, argv, c, &Value) ) goto finish;
            if      ( c == 'N' ) { p->nVars = Value; fN = 1; }
            else if ( c == 'M' ) { p->nNodes = Value; fM = 1; }
            else if ( c == 'K' ) p->nLutSize = Value;
            else if ( c == 'T' ) p->RuntimeLim = Value;
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
        case 'c': fMuxConsensus ^= 1; break;
        case 'b': fBackward ^= 1; break;
        case 's': p->fSilent ^= 1; break;
        case 'v': p->fVerbose ^= 1; break;
        case 'h': Bmc_CasUsage(); goto finish;
        default:  Bmc_CasUsage(); goto finish;
        }
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
    else if ( !p->pTtStr && !fF )
    {
        Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
        Abc_Ntk_t * pAig;
        if ( !pNtk || Abc_NtkLatchNum(pNtk) || Abc_NtkCoNum(pNtk) != 1 ||
             Abc_NtkCiNum(pNtk) < 2 || Abc_NtkCiNum(pNtk) > CAS_MAX_VARS )
        {
            Abc_Print(-1, "Provide hex/-Y/-F or a single-output combinational network with 2..14 inputs.\n");
            goto finish;
        }
        if ( fN && p->nVars != Abc_NtkCiNum(pNtk) )
        {
            Abc_Print(-1, "-N disagrees with the current network's input count.\n");
            goto finish;
        }
        p->nVars = Abc_NtkCiNum(pNtk);
        pAig = Abc_NtkIsStrash(pNtk) ? pNtk : Abc_NtkStrash(pNtk, 0, 0, 0);
        if ( !pAig ) { Abc_Print(-1, "Could not strash the current network.\n"); goto finish; }
        p->pTtStr = pOwnedTruth = Abc_NtkReadTruth(pAig);
        if ( pAig != pNtk ) Abc_NtkDelete(pAig);
        if ( !pOwnedTruth ) { Abc_Print(-1, "Could not derive the network's truth table.\n"); goto finish; }
    }
    if ( p->pTtStr )
    {
        if ( p->pTtStr[0] == '0' && (p->pTtStr[1] == 'x' || p->pTtStr[1] == 'X') ) p->pTtStr += 2;
        n = (int)strlen(p->pTtStr);
        if ( n < 1 || n > (1 << (CAS_MAX_VARS-2)) || (n & (n-1)) )
        {
            Abc_Print(-1, "Truth table needs 2^(N-2) hex digits, for N in 2..14.\n");
            goto finish;
        }
        for ( i = 0; i < n; ++i )
            if ( !Abc_TtIsHexDigit(p->pTtStr[i]) )
            {
                Abc_Print(-1, "Truth table contains a non-hexadecimal character.\n");
                goto finish;
            }
        n = 2 + (n == 1 ? 0 : Abc_Base2Log(n));
        if ( p->nVars && p->nVars != n )
        {
            Abc_Print(-1, "Truth table length disagrees with N.\n");
            goto finish;
        }
        p->nVars = n;
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
    pTruth = p->pSymStr ? Abc_TtSymFunGenerate(p->pSymStr, p->nVars) : ABC_CALLOC(word, Abc_TtWordNum(p->nVars));
    if ( p->pTtStr ) Abc_TtReadHex(pTruth, p->pTtStr);
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
        Status = Bmc_CasRun(p, pTruth, &RandomPins, fMuxConsensus, fBackward);
        if ( Status < 0 ) goto finish;
        nResults[Status == CAS_SAT ? 1 : Status == CAS_UNSAT ? 2 : 0]++;
    }
    if ( fF ) printf("Random functions: SAT = %d, UNSAT = %d, UNKNOWN = %d (total %d).\n", nResults[1], nResults[2], nResults[0], p->nRandFuncs);
    Ret = 0;
finish:
    ABC_FREE(pTruth);
    ABC_FREE(pOwnedTruth);
    ABC_FREE(pHex);
    return Ret;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
