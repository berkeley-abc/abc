/**CFile****************************************************************

  FileName    [bmcLut2.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based bounded model checking.]

  Synopsis    [Exact synthesis of general LUT networks and cascades.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 8, 2026.]

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

#define LUT2_MAX_VARS  14
#define LUT2_MAX_LUT    8
#define LUT2_MAX_NODES 64
#define LUT2_MAX_OBJS  (LUT2_MAX_VARS + LUT2_MAX_NODES)
#define LUT2_MAX_LITS  128

typedef struct Bmc_Lut2Par_t_ Bmc_Lut2Par_t;
struct Bmc_Lut2Par_t_
{
    int nInputs, nNodes, nLutSize, nSeconds, nConflicts, nSeed, Encoding, nProbeSeconds;
    int fCadical, fMinimum, fSymmetry, fBackward, fConsensus, fNoFastElim;
    int fPrefix, fDirect, fThree, fGroups, fCascade, fVerbose, fSilent, fDump;
};

typedef int Bmc_Lut2Pins_t[LUT2_MAX_OBJS];
typedef struct Bmc_Lut2Man_t_ Bmc_Lut2Man_t;
struct Bmc_Lut2Man_t_
{
    Bmc_Lut2Par_t * pPars;
    int nVars, nNodes, nWords, nMints, nNext, fCompl, fStopped, fResource;
    int Map[LUT2_MAX_VARS];
    int Select[LUT2_MAX_NODES][LUT2_MAX_OBJS];
    Bmc_Lut2Pins_t * pPins[LUT2_MAX_NODES];
    int Funcs[LUT2_MAX_NODES][1 << LUT2_MAX_LUT];
    int Expanded[LUT2_MAX_NODES], * pCofs[LUT2_MAX_NODES], * pValues;
    int Fans[LUT2_MAX_NODES][LUT2_MAX_LUT], nFans[LUT2_MAX_NODES];
    word Truths[LUT2_MAX_NODES][4];
    word * pTruth, * pCare, nClauses, nLiterals;
    int iRailInput;
    unsigned nTimeChecks;
    abctime timeStop, timeCandidates;
    kissat * pKissat;
    CCaDiCaL * pCadical;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Tests the CPU deadline, including formula construction.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Lut2Stop( void * pData )
{
    Bmc_Lut2Man_t * p = (Bmc_Lut2Man_t *)pData;
    if ( p->timeStop && (abctime)clock() >= p->timeStop ) p->fStopped = 1;
    return p->fStopped;
}

/**Function*************************************************************

  Synopsis    [Amortizes CPU-clock queries in the solver's frequent callback.]

  Description [Construction checks the deadline directly.  During search,
  checking every 1024 callbacks avoids a system call in the propagation loop.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Lut2Terminate( void * pData )
{
    Bmc_Lut2Man_t * p = (Bmc_Lut2Man_t *)pData;
    return (++p->nTimeChecks & 1023) ? p->fStopped : Bmc_Lut2Stop(p);
}

/**Function*************************************************************

  Synopsis    [Allocates a DIMACS variable; literals 1 and -1 are constants.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Lut2Var( Bmc_Lut2Man_t * p )
{
    if ( p->nNext >= 5000000 ) p->fResource = p->fStopped = 1;
    return p->fStopped ? -1 : ++p->nNext;
}

/**Function*************************************************************

  Synopsis    [Adds a clause after simplifying constants and repetitions.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Lut2Clause( Bmc_Lut2Man_t * p, const int * pLits, int nLits )
{
    int Lits[LUT2_MAX_LITS], i, j, n = 0, Temp;
    assert( nLits <= LUT2_MAX_LITS );
    if ( p->fStopped ) return;
    for ( i = 0; i < nLits; ++i )
    {
        if ( pLits[i] == 1 ) return;
        if ( pLits[i] == -1 ) continue;
        assert( pLits[i] );
        for ( j = 0; j < n; ++j )
        {
            if ( Lits[j] == -pLits[i] ) return;
            if ( Lits[j] == pLits[i] ) break;
        }
        if ( j == n ) Lits[n++] = pLits[i];
    }
    for ( i = 1; i < n; ++i )
        for ( j = i; j > 0 && abs(Lits[j-1]) > abs(Lits[j]); --j )
        {
            Temp = Lits[j]; Lits[j] = Lits[j-1]; Lits[j-1] = Temp;
        }
    for ( i = 0; i < n; ++i )
        if ( p->pCadical ) ccadical_add(p->pCadical, Lits[i]);
        else kissat_add(p->pKissat, Lits[i]);
    if ( p->pCadical ) ccadical_add(p->pCadical, 0);
    else kissat_add(p->pKissat, 0);
    p->nClauses++;
    p->nLiterals += n;
    if ( p->nClauses >= 20000000 ) p->fResource = p->fStopped = 1;
    if ( (p->nClauses & 4095) == 0 ) Bmc_Lut2Stop(p);
}

/**Function*************************************************************

  Synopsis    [Adds short clauses.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Lut2Unit( Bmc_Lut2Man_t * p, int a )
{
    Bmc_Lut2Clause(p, &a, 1);
}
static void Bmc_Lut2Binary( Bmc_Lut2Man_t * p, int a, int b )
{
    int Lits[2] = {a, b};
    Bmc_Lut2Clause(p, Lits, 2);
}
static void Bmc_Lut2Ternary( Bmc_Lut2Man_t * p, int a, int b, int c )
{
    int Lits[3] = {a, b, c};
    Bmc_Lut2Clause(p, Lits, 3);
}

/**Function*************************************************************

  Synopsis    [Encodes conjunction, exclusive OR, and a two-input multiplexer.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Lut2And( Bmc_Lut2Man_t * p, int a, int b )
{
    int y;
    if ( a == -1 || b == -1 || a == -b ) return -1;
    if ( a == 1 ) return b;
    if ( b == 1 || a == b ) return a;
    y = Bmc_Lut2Var(p);
    Bmc_Lut2Binary(p, -y, a);
    Bmc_Lut2Binary(p, -y, b);
    Bmc_Lut2Ternary(p, y, -a, -b);
    return y;
}
static int Bmc_Lut2Xor( Bmc_Lut2Man_t * p, int a, int b )
{
    int y;
    if ( a == b ) return -1;
    if ( a == -b ) return 1;
    if ( a == 1 ) return -b;
    if ( b == 1 ) return -a;
    if ( a == -1 ) return b;
    if ( b == -1 ) return a;
    y = Bmc_Lut2Var(p);
    Bmc_Lut2Ternary(p, a, b, -y);
    Bmc_Lut2Ternary(p, -a, -b, -y);
    Bmc_Lut2Ternary(p, a, -b, y);
    Bmc_Lut2Ternary(p, -a, b, y);
    return y;
}
static int Bmc_Lut2Mux( Bmc_Lut2Man_t * p, int s, int a, int b )
{
    int y;
    if ( s == 1 ) return b;
    if ( s == -1 ) return a;
    if ( a == b ) return a;
    y = Bmc_Lut2Var(p);
    Bmc_Lut2Ternary(p, s, -a, y);
    Bmc_Lut2Ternary(p, s, a, -y);
    Bmc_Lut2Ternary(p, -s, -b, y);
    Bmc_Lut2Ternary(p, -s, b, -y);
    if ( p->pPars->fConsensus )
    {
        Bmc_Lut2Ternary(p, -a, -b, y);
        Bmc_Lut2Ternary(p, a, b, -y);
    }
    return y;
}

/**Function*************************************************************

  Synopsis    [Builds equivalent prefix thresholds and enforces exact cardinality.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Lut2Exactly( Bmc_Lut2Man_t * p, int * pLits, int nLits, int k )
{
    int Old[LUT2_MAX_LUT+2], New[LUT2_MAX_LUT+2], i, j, a, b, y;
    Old[0] = New[0] = 1;
    for ( j = 1; j <= k+1; ++j ) Old[j] = -1;
    for ( i = 0; i < nLits; ++i )
    {
        for ( j = 1; j <= k+1; ++j )
        {
            a = Old[j]; b = Old[j-1];
            if ( a == 1 ) y = 1;
            else if ( a == -1 ) y = Bmc_Lut2And(p, pLits[i], b);
            else
            {
                y = Bmc_Lut2Var(p);
                Bmc_Lut2Binary(p, -a, y);
                Bmc_Lut2Ternary(p, -pLits[i], -b, y);
                Bmc_Lut2Ternary(p, -y, a, pLits[i]);
                Bmc_Lut2Ternary(p, -y, a, b);
            }
            New[j] = y;
        }
        memcpy(Old, New, sizeof(int)*(k+2));
    }
    Bmc_Lut2Unit(p, Old[k]);
    Bmc_Lut2Unit(p, -Old[k+1]);
}

/**Function*************************************************************

  Synopsis    [Orders Boolean vectors lexicographically without dominance constraints.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Lut2Lex( Bmc_Lut2Man_t * p, int * a, int * b, int n )
{
    int Equal = 1, Next, i, Lits[4];
    for ( i = 0; i < n; ++i )
    {
        Bmc_Lut2Ternary(p, -Equal, -a[i], b[i]);
        Next = i+1 < n ? Bmc_Lut2Var(p) : 1;
        Lits[0] = -Equal; Lits[1] = a[i]; Lits[2] = b[i]; Lits[3] = Next;
        Bmc_Lut2Clause(p, Lits, 4);
        Lits[1] = -a[i]; Lits[2] = -b[i];
        Bmc_Lut2Clause(p, Lits, 4);
        Equal = Next;
    }
}

typedef struct Bmc_Lut2Group_t_ Bmc_Lut2Group_t;
struct Bmc_Lut2Group_t_
{
    Bmc_Lut2Man_t * p;
    int Perm[LUT2_MAX_VARS], Sig[LUT2_MAX_VARS][2];
    int Swap[LUT2_MAX_VARS][LUT2_MAX_VARS], * pImages;
    int nChecked, nFound;
};

/**Function*************************************************************

  Synopsis    [Verifies a proposed input permutation against the entire function.]

  Description [Signatures only filter candidates; they never authorize a constraint.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Lut2GroupCheck( Bmc_Lut2Group_t * p )
{
    int t, j, Bit;
    if ( p->p->iRailInput && p->Perm[p->p->iRailInput-1] != p->p->iRailInput-1 ) return 0;
    p->pImages[0] = 0;
    for ( t = 1; t < p->p->nMints; ++t )
    {
        for ( j = 0; !(t & (1 << j)); ++j ) {}
        Bit = 1 << j;
        p->pImages[t] = p->pImages[t ^ Bit] | (1 << p->Perm[j]);
        if ( p->p->pCare && Abc_TtGetBit(p->p->pCare, t) != Abc_TtGetBit(p->p->pCare, p->pImages[t]) ) return 0;
        if ( Abc_TtGetBit(p->p->pTruth, t) != Abc_TtGetBit(p->p->pTruth, p->pImages[t]) ) return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Enumerates simultaneous disjoint input swaps with a bounded effort.]

  Description [The adjacency matrix is compared in node order, with high PI
  indices first.  A lexicographically least representative under all valid
  input renamings and topological node orders satisfies these constraints
  together with the individual input and fanin-set ordering constraints.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Lut2Groups_rec( Bmc_Lut2Group_t * p, int Used, int nSwaps )
{
    int i, j, k, n, A[LUT2_MAX_VARS*LUT2_MAX_NODES], B[LUT2_MAX_VARS*LUT2_MAX_NODES];
    if ( p->nChecked >= 4096 || p->nFound >= 16 || Bmc_Lut2Stop(p->p) ) return;
    if ( Used == p->p->nMints-1 )
    {
        if ( nSwaps < 2 ) return;
        p->nChecked++;
        if ( !Bmc_Lut2GroupCheck(p) ) return;
        p->nFound++;
        n = 0;
        for ( i = 0; i < p->p->nNodes; ++i )
            for ( j = p->p->nVars-1; j >= 0; --j )
            {
                A[n] = p->p->Select[i][j];
                B[n++] = p->p->Select[i][p->Perm[j]];
            }
        Bmc_Lut2Lex(p->p, A, B, n);
        return;
    }
    for ( i = 0; (Used >> i) & 1; ++i ) {}
    Bmc_Lut2Groups_rec(p, Used | (1 << i), nSwaps);
    for ( k = i+1; k < p->p->nVars; ++k )
    {
        if ( ((Used >> k) & 1) || p->Swap[i][k] ||
            p->Sig[i][0] != p->Sig[k][0] || p->Sig[i][1] != p->Sig[k][1] ) continue;
        p->Perm[i] = k; p->Perm[k] = i;
        Bmc_Lut2Groups_rec(p, Used | (1 << i) | (1 << k), nSwaps+1);
        p->Perm[i] = i; p->Perm[k] = k;
    }
}

/**Function*************************************************************

  Synopsis    [Adds verified simultaneous-input-swap symmetry constraints.]

  Description [This also detects operand exchange in arithmetic functions,
  without recognizing a multiplier or assuming a particular input order.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Lut2Groups( Bmc_Lut2Man_t * pMan )
{
    Bmc_Lut2Group_t * p;
    int i, j, t, a, b;
    if ( !pMan->pPars->fGroups || pMan->fStopped ) return;
    p = ABC_CALLOC(Bmc_Lut2Group_t, 1);
    p->p = pMan;
    p->pImages = ABC_ALLOC(int, pMan->nMints);
    for ( i = 0; i < pMan->nVars; ++i )
    {
        p->Perm[i] = i;
        for ( t = 0; t < pMan->nMints; ++t ) if ( (t >> i) & 1 )
        {
            a = Abc_TtGetBit(pMan->pTruth, t); b = Abc_TtGetBit(pMan->pTruth, t ^ (1 << i));
            p->Sig[i][0] += a; p->Sig[i][1] += a != b;
        }
    }
    for ( i = 0; i < pMan->nVars && !Bmc_Lut2Stop(pMan); ++i )
        for ( j = i+1; j < pMan->nVars; ++j )
        {
            if ( p->Sig[i][0] != p->Sig[j][0] || p->Sig[i][1] != p->Sig[j][1] ) continue;
            p->Perm[i] = j; p->Perm[j] = i;
            p->Swap[i][j] = Bmc_Lut2GroupCheck(p);
            p->Perm[i] = i; p->Perm[j] = j;
        }
    Bmc_Lut2Groups_rec(p, 0, 0);
    if ( pMan->pPars->fVerbose ) printf("Verified input-group symmetries = %d (%d candidates).\n", p->nFound, p->nChecked);
    ABC_FREE(p->pImages);
    ABC_FREE(p);
}

/**Function*************************************************************

  Synopsis    [Builds general-DAG selectors and verified symmetry reductions.]

  Description [Equal fanin sets remain allowed: different LUT functions may share them.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Lut2Structure( Bmc_Lut2Man_t * p )
{
    Bmc_Lut2Par_t * q = p->pPars;
    int Lits[LUT2_MAX_LITS], A[LUT2_MAX_OBJS], B[LUT2_MAX_OBJS];
    int i, j, k, h, a, b, n, t, u, Size, Width, fSame;
    for ( i = 0; i < p->nNodes && !p->fStopped; ++i )
    {
        Size = p->nVars+i;
        Width = q->fCascade ? p->nVars+(i != 0) : Size;
        // Expanded functions propagate well on early nodes.  Limit their
        // table size and estimated clause overhead before switching to pins.
        p->Expanded[i] = q->Encoding == 2 || (q->Encoding == 0 && q->fCascade) || (q->Encoding == 0 && i < 4 && Size <= 16 &&
            (1 << i)*(Size+4)-4 <= 4*(q->nLutSize*(p->nVars+2*i-q->nLutSize+1)+(2 << q->nLutSize)));
        if ( p->Expanded[i] && Width > 20 )
        {
            p->fResource = p->fStopped = 1;
            break;
        }
        for ( j = 0; j < Size; ++j )
            p->Select[i][j] = p->iRailInput && j == p->iRailInput-1 ? (i == 0 ? 1 : -1) : q->fCascade && j >= p->nVars ? (j == Size-1 ? 1 : -1) : Bmc_Lut2Var(p);
        if ( p->Expanded[i] )
            Bmc_Lut2Exactly(p, p->Select[i], Size, q->nLutSize);
        else
        {
            p->pPins[i] = ABC_CALLOC(Bmc_Lut2Pins_t, q->nLutSize);
            for ( k = 0; k < q->nLutSize; ++k )
            {
                n = 0;
                for ( j = k; j < Size-q->nLutSize+1+k; ++j )
                    Lits[n++] = p->pPins[i][k][j] = Bmc_Lut2Var(p);
                Bmc_Lut2Clause(p, Lits, n);
                for ( a = 0; a < n; ++a )
                    for ( b = a+1; b < n; ++b ) Bmc_Lut2Binary(p, -Lits[a], -Lits[b]);
            }
            for ( k = 0; k+1 < q->nLutSize; ++k )
                for ( j = 0; j < Size; ++j ) if ( p->pPins[i][k][j] )
                    for ( h = 0; h <= j; ++h ) if ( p->pPins[i][k+1][h] )
                        Bmc_Lut2Binary(p, -p->pPins[i][k][j], -p->pPins[i][k+1][h]);
            for ( j = 0; j < Size; ++j )
            {
                n = 0; Lits[n++] = -p->Select[i][j];
                for ( k = 0; k < q->nLutSize; ++k ) if ( p->pPins[i][k][j] ) Lits[n++] = p->pPins[i][k][j];
                Bmc_Lut2Clause(p, Lits, n);
                for ( k = 1; k < n; ++k ) Bmc_Lut2Binary(p, p->Select[i][j], -Lits[k]);
            }
            p->Funcs[i][0] = -1;
            for ( t = 1; t < (1 << q->nLutSize); ++t ) p->Funcs[i][t] = Bmc_Lut2Var(p);
        }
    }
    for ( j = 0; j < p->nVars+p->nNodes-1; ++j )
    {
        n = 0;
        for ( i = 0; i < p->nNodes; ++i ) if ( j < p->nVars+i ) Lits[n++] = p->Select[i][j];
        Bmc_Lut2Clause(p, Lits, n);
    }
    if ( !q->fSymmetry || p->fStopped ) return;
    for ( a = 0; a < p->nVars; ++a )
    for ( b = a+1; b < p->nVars; ++b )
    {
        if ( p->iRailInput && (a == p->iRailInput-1 || b == p->iRailInput-1) ) continue;
        fSame = 1;
        for ( t = 0; t < p->nMints; ++t )
        {
            u = t ^ ((((t >> a) ^ (t >> b)) & 1)*((1 << a)|(1 << b)));
            if ( p->pCare && Abc_TtGetBit(p->pCare, t) != Abc_TtGetBit(p->pCare, u) ) { fSame = 0; break; }
            if ( Abc_TtGetBit(p->pTruth, t) != Abc_TtGetBit(p->pTruth, u) ) { fSame = 0; break; }
        }
        if ( !fSame ) continue;
        for ( i = 0; i < p->nNodes; ++i ) { A[i] = -p->Select[i][a]; B[i] = -p->Select[i][b]; }
        Bmc_Lut2Lex(p, A, B, p->nNodes);
    }
    for ( i = 0; i+1 < p->nNodes; ++i )
    {
        n = 0;
        for ( j = p->nVars+i; j >= 0; --j )
        {
            A[n] = j == p->nVars+i ? -1 : p->Select[i][j];
            B[n++] = p->Select[i+1][j];
        }
        Bmc_Lut2Lex(p, A, B, n);
    }
}

/**Function*************************************************************

  Synopsis    [Constrains expanded functions to depend only on selected fanins.]

  Description [The truth-table arguments include every PI and every earlier LUT.
  In cascade mode only the immediate predecessor is an additional argument.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Lut2Cofactors( Bmc_Lut2Man_t * p )
{
    int i, j, t, Count, Width, a, b, s;
    for ( i = 0; i < p->nNodes && !p->fStopped; ++i ) if ( p->Expanded[i] )
    {
        Width = p->nVars + (p->pPars->fCascade ? (i != 0) : i);
        Count = 1 << Width;
        p->pCofs[i] = ABC_ALLOC(int, Count);
        p->pCofs[i][0] = -1;
        for ( t = 1; t < Count; ++t ) p->pCofs[i][t] = Bmc_Lut2Var(p);
        for ( j = 0; j < Width && !p->fStopped; ++j )
        {
            s = p->pPars->fCascade && j == p->nVars ? 1 : p->Select[i][j];
            if ( s == 1 ) continue;
            for ( t = 0; t < Count && !p->fStopped; ++t ) if ( !(t & (1 << j)) )
            {
                a = p->pCofs[i][t]; b = p->pCofs[i][t | (1 << j)];
                Bmc_Lut2Ternary(p, s, -a, b);
                Bmc_Lut2Ternary(p, s, a, -b);
            }
        }
    }
}

/**Function*************************************************************

  Synopsis    [Connects function values to the actual DAG for every input assignment.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Lut2Function( Bmc_Lut2Man_t * p )
{
    Bmc_Lut2Par_t * q = p->pPars;
    int Values[LUT2_MAX_OBJS], Inputs[LUT2_MAX_LUT], Lits[LUT2_MAX_LUT+2];
    int i, j, k, t, a, n, y, Target, Count, MaxCount = 1, * pLeaves;
    assert( !Abc_TtGetBit(p->pTruth, 0) );
    p->pValues = ABC_ALLOC(int, p->nNodes*p->nMints);
    if ( p->pCare ) for ( i = 0; i < p->nNodes*p->nMints; ++i ) p->pValues[i] = -1;
    for ( i = 0; i < p->nNodes; ++i ) if ( p->Expanded[i] )
        MaxCount = Abc_MaxInt(MaxCount, 1 << (q->fCascade ? (i != 0) : i));
    pLeaves = ABC_ALLOC(int, MaxCount);
    for ( t = 0; t < p->nMints && !p->fStopped; ++t )
    {
        if ( p->pCare && !Abc_TtGetBit(p->pCare, t) ) continue;
        for ( j = 0; j < p->nVars; ++j ) Values[j] = (t >> j) & 1 ? 1 : -1;
        Target = Abc_TtGetBit(p->pTruth, t) ? 1 : -1;
        for ( i = 0; i < p->nNodes && !p->fStopped; ++i )
        {
            if ( p->Expanded[i] )
            {
                Count = 1 << (q->fCascade ? (i != 0) : i);
                for ( a = 0; a < Count; ++a ) pLeaves[a] = p->pCofs[i][t+(a << p->nVars)];
                for ( j = q->fCascade && i ? i-1 : 0; j < i; ++j )
                {
                    for ( a = 0; a < Count; a += 2 )
                        if ( q->fCascade && i == p->nNodes-1 && Count == 2 )
                        {
                            // Clamp the final mux directly instead of creating
                            // a variable that is immediately assigned by a unit.
                            int Lit0 = Target == 1 ? pLeaves[a] : -pLeaves[a];
                            int Lit1 = Target == 1 ? pLeaves[a+1] : -pLeaves[a+1];
                            if ( Lit0 == Lit1 ) Bmc_Lut2Unit(p, Lit0);
                            else
                            {
                                Bmc_Lut2Binary(p, Values[p->nVars+j], Lit0);
                                Bmc_Lut2Binary(p, -Values[p->nVars+j], Lit1);
                                if ( q->fConsensus ) Bmc_Lut2Binary(p, Lit0, Lit1);
                            }
                            pLeaves[a/2] = Target;
                        }
                        else pLeaves[a/2] = Bmc_Lut2Mux(p, Values[p->nVars+j], pLeaves[a], pLeaves[a+1]);
                    Count /= 2;
                }
                y = pLeaves[0];
                if ( i == p->nNodes-1 ) Bmc_Lut2Unit(p, Target == 1 ? y : -y);
            }
            else
            {
                for ( k = 0; k < q->nLutSize; ++k )
                {
                    Inputs[k] = Bmc_Lut2Var(p);
                    for ( j = 0; j < p->nVars+i; ++j ) if ( p->pPins[i][k][j] )
                    {
                        Bmc_Lut2Ternary(p, -p->pPins[i][k][j], -Inputs[k], Values[j]);
                        Bmc_Lut2Ternary(p, -p->pPins[i][k][j], Inputs[k], -Values[j]);
                    }
                }
                y = i == p->nNodes-1 ? Target : t ? Bmc_Lut2Var(p) : -1;
                for ( a = 0; a < (1 << q->nLutSize); ++a )
                {
                    n = 0;
                    for ( k = 0; k < q->nLutSize; ++k ) Lits[n++] = (a >> k) & 1 ? -Inputs[k] : Inputs[k];
                    Lits[n++] = -p->Funcs[i][a]; Lits[n++] = y;
                    Bmc_Lut2Clause(p, Lits, n);
                    Lits[n-2] = p->Funcs[i][a]; Lits[n-1] = -y;
                    Bmc_Lut2Clause(p, Lits, n);
                }
            }
            p->pValues[i*p->nMints+t] = Values[p->nVars+i] = y;
        }
    }
    ABC_FREE(pLeaves);
}

/**Function*************************************************************

  Synopsis    [Requires opposite target rows to differ on a selected output fanin.]

  Description [Only cube edges are needed for this redundant clause family.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Lut2Backward( Bmc_Lut2Man_t * p )
{
    int i, j, t, u, d, n, Lits[LUT2_MAX_NODES];
    if ( !p->pPars->fBackward ) return;
    for ( t = 0; t < p->nMints && !p->fStopped; ++t )
    for ( j = 0; j < p->nVars && !p->fStopped; ++j )
    {
        u = t ^ (1 << j);
        if ( p->pCare && (!Abc_TtGetBit(p->pCare, t) || !Abc_TtGetBit(p->pCare, u)) ) continue;
        if ( t >= u || Abc_TtGetBit(p->pTruth, t) == Abc_TtGetBit(p->pTruth, u) ) continue;
        n = 0; Lits[n++] = p->Select[p->nNodes-1][j];
        for ( i = 0; i+1 < p->nNodes; ++i )
        {
            d = Bmc_Lut2Xor(p, p->pValues[i*p->nMints+t], p->pValues[i*p->nMints+u]);
            Lits[n++] = Bmc_Lut2And(p, p->Select[p->nNodes-1][p->nVars+i], d);
        }
        Bmc_Lut2Clause(p, Lits, n);
    }
}

/**Function*************************************************************

  Synopsis    [Reads a model literal and extracts the selected LUT functions.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Lut2Value( Bmc_Lut2Man_t * p, int Lit )
{
    if ( Lit == 1 || Lit == -1 ) return Lit == 1;
    return (p->pCadical ? ccadical_val(p->pCadical, Lit) : kissat_value(p->pKissat, Lit)) > 0;
}
static int Bmc_Lut2Extract( Bmc_Lut2Man_t * p )
{
    int i, j, k, t, Address, Lit;
    for ( i = 0; i < p->nNodes; ++i )
    {
        for ( j = 0; j < p->nVars+i; ++j ) if ( Bmc_Lut2Value(p, p->Select[i][j]) )
        {
            if ( p->nFans[i] == p->pPars->nLutSize ) return 0;
            p->Fans[i][p->nFans[i]++] = j;
        }
        if ( p->nFans[i] != p->pPars->nLutSize ) return 0;
        for ( t = 0; t < (1 << p->nFans[i]); ++t )
        {
            Address = 0;
            if ( p->Expanded[i] )
                for ( k = 0; k < p->nFans[i]; ++k )
                    Address |= ((t >> k) & 1) << (p->pPars->fCascade && p->Fans[i][k] >= p->nVars ? p->nVars : p->Fans[i][k]);
            Lit = p->Expanded[i] ? p->pCofs[i][Address] : p->Funcs[i][t];
            if ( Bmc_Lut2Value(p, Lit) ) Abc_TtSetBit(p->Truths[i], t);
        }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Exhaustively checks the synthesized network before exporting it.]

  Description [Inputs and LUTs use ascending indices; local pin zero is the LSB.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Lut2Verify( Bmc_Lut2Man_t * p )
{
    int Values[LUT2_MAX_OBJS], i, j, t, Address, Result;
    if ( p->pPars->fCascade )
        for ( i = 1; i < p->nNodes; ++i )
        {
            int fPrevious = 0;
            for ( j = 0; j < p->nFans[i]; ++j )
            {
                if ( p->Fans[i][j] == p->nVars+i-1 ) fPrevious = 1;
                else if ( p->Fans[i][j] >= p->nVars ) return 0;
            }
            if ( !fPrevious ) return 0;
        }
    for ( t = 0; t < p->nMints; ++t )
    {
        if ( p->pCare && !Abc_TtGetBit(p->pCare, t) ) continue;
        for ( j = 0; j < p->nVars; ++j ) Values[j] = (t >> j) & 1;
        for ( i = 0; i < p->nNodes; ++i )
        {
            Address = 0;
            for ( j = 0; j < p->nFans[i]; ++j )
            {
                if ( p->Fans[i][j] < 0 || p->Fans[i][j] >= p->nVars+i ) return 0;
                Address |= Values[p->Fans[i][j]] << j;
            }
            Values[p->nVars+i] = Abc_TtGetBit(p->Truths[i], Address);
        }
        Result = p->nNodes ? Values[p->nVars+p->nNodes-1] : p->nVars ? Values[0] : 0;
        if ( Result != Abc_TtGetBit(p->pTruth, t) ) return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Maps between a subset of input positions and its local address.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Lut2Deposit( int Value, int Mask )
{
    int Result = 0, Bit;
    for ( Bit = 1; Mask; Bit <<= 1, Mask >>= 1 ) if ( Mask & 1 )
    {
        if ( Value & 1 ) Result |= Bit;
        Value >>= 1;
    }
    return Result;
}
static int Bmc_Lut2Compress( int Value, int Mask )
{
    int Result = 0, Bit = 1;
    for ( ; Mask; Value >>= 1, Mask >>= 1 ) if ( Mask & 1 )
    {
        if ( Value & 1 ) Result |= Bit;
        Bit <<= 1;
    }
    return Result;
}

/**Function*************************************************************

  Synopsis    [Packs truth-table columns with the bound inputs last.]

  Description [Preserves increasing input order in both groups. Word-sized
               slices avoid rebuilding the same columns one bit at a time.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Lut2Columns( word * pTruth, int nVars, int Bound, int nBound, word * pCols )
{
    word Packed[1 << (LUT2_MAX_VARS-6)], Mask;
    int Perm[LUT2_MAX_VARS], Order[LUT2_MAX_VARS];
    int nFree = nVars-nBound, nWords = Abc_TtWordNum(nVars);
    int nColWords = Abc_TtWordNum(nFree), i, j, a, n = 0, Pos;
    assert( nVars <= LUT2_MAX_VARS && nFree >= 0 );
    memcpy(Packed, pTruth, sizeof(word)*nWords);
    for ( i = 0; i < nVars; ++i ) if ( !((Bound >> i)&1) ) Order[n++] = i;
    for ( i = 0; i < nVars; ++i ) if (  ((Bound >> i)&1) ) Order[n++] = i;
    assert( n == nVars );
    for ( i = 0; i < nVars; ++i ) Perm[i] = i;
    for ( i = 0; i < nVars; ++i )
    {
        a = Order[i];
        for ( j = i; Perm[j] != a; ++j ) {}
        if ( j == i ) continue;
        Abc_TtSwapVars(Packed, nVars, i, j);
        Perm[j] = Perm[i]; Perm[i] = a;
    }
    if ( nFree >= 6 )
        memcpy(pCols, Packed, sizeof(word)*nColWords*(1 << nBound));
    else
    {
        Mask = ((word)1 << (1 << nFree))-1;
        for ( i = 0; i < (1 << nBound); ++i )
        {
            Pos = i << nFree;
            pCols[i] = (Packed[Pos >> 6] >> (Pos & 63)) & Mask;
        }
    }
}


/**Function*************************************************************

  Synopsis    [Completely decides the two-LUT case by column multiplicity.]

  Description [For each root PI set A and shared subset S, the bound inputs
  D are all PIs outside A.  At each assignment to S, columns indexed by D
  must take at most two values over A minus S.  These two classes are the
  first LUT's output.  Enumerating all A and S is complete, including
  decompositions with fewer essential pins, which can be padded to K.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Lut2Decompose( Bmc_Lut2Man_t * p )
{
    int K = p->pPars->nLutSize, All = p->nMints-1, nShared = 2*K-1-p->nVars;
    int A, S, D, F, B, a, s, d, f, j, Address, nD, nF, nS, Class, nClasses, fGood;
    int Bound[256], Free[128], Shared[128];
    word Col[2], Cols[2][2];
    assert( p->nVars > K && nShared >= 0 );
    for ( A = 1; A <= All && !Bmc_Lut2Stop(p); ++A )
    {
        if ( Abc_TtCountOnes((word)A) != K-1 ) continue;
        D = All ^ A;
        nD = 1 << (p->nVars-K+1);
        for ( d = 0; d < nD; ++d ) Bound[d] = Bmc_Lut2Deposit(d, D);
        for ( S = A; ; S = (S-1) & A )
        {
            if ( Abc_TtCountOnes((word)S) == nShared )
            {
                if ( Bmc_Lut2Stop(p) ) return 0;
                F = A ^ S; B = D | S;
                nS = 1 << nShared; nF = 1 << (K-1-nShared);
                for ( s = 0; s < nS; ++s ) Shared[s] = Bmc_Lut2Deposit(s, S);
                for ( f = 0; f < nF; ++f ) Free[f] = Bmc_Lut2Deposit(f, F);
                memset(p->Truths[0], 0, sizeof(p->Truths[0]));
                memset(p->Truths[1], 0, sizeof(p->Truths[1]));
                fGood = 1;
                for ( s = 0; s < nS && fGood; ++s )
                {
                    nClasses = 0;
                    memset(Cols, 0, sizeof(Cols));
                    for ( d = 0; d < nD; ++d )
                    {
                        Col[0] = Col[1] = 0;
                        for ( f = 0; f < nF; ++f )
                            if ( Abc_TtGetBit(p->pTruth, Shared[s] | Bound[d] | Free[f]) ) Abc_TtSetBit(Col, f);
                        for ( Class = 0; Class < nClasses; ++Class )
                            if ( Col[0] == Cols[Class][0] && Col[1] == Cols[Class][1] ) break;
                        if ( Class == 2 ) { fGood = 0; break; }
                        if ( Class == nClasses ) { memcpy(Cols[nClasses++], Col, sizeof(Col)); }
                        Address = Bmc_Lut2Compress(Shared[s] | Bound[d], B);
                        if ( Class ) Abc_TtSetBit(p->Truths[0], Address);
                    }
                    for ( Class = 0; Class < nClasses; ++Class )
                        for ( f = 0; f < nF; ++f ) if ( Abc_TtGetBit(Cols[Class], f) )
                        {
                            Address = Bmc_Lut2Compress(Shared[s] | Free[f], A) | (Class << (K-1));
                            Abc_TtSetBit(p->Truths[1], Address);
                        }
                }
                if ( fGood )
                {
                    a = 0;
                    for ( j = 0; j < p->nVars; ++j ) if ( (B >> j) & 1 ) p->Fans[0][a++] = j;
                    assert( a == K );
                    a = 0;
                    for ( j = 0; j < p->nVars; ++j ) if ( (A >> j) & 1 ) p->Fans[1][a++] = j;
                    p->Fans[1][a] = p->nVars;
                    p->nFans[0] = p->nFans[1] = K;
                    return 10;
                }
            }
            if ( S == 0 ) break;
        }
    }
    return p->fStopped ? 0 : 20;
}

/**Function*************************************************************

  Synopsis    [Solves a complete or partial function in one shared encoding.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Lut2Search( Bmc_Lut2Man_t * p, abctime * pTimeSolve )
{
    Bmc_Lut2Par_t * q = p->pPars;
    abctime clkSolve;
    int Status = 0;
    if ( q->fCadical )
    {
        p->pCadical = ccadical_init();
        ccadical_set_option(p->pCadical, "seed", q->nSeed);
        if ( p->timeStop ) ccadical_set_terminate(p->pCadical, p, Bmc_Lut2Terminate);
        if ( q->nConflicts ) ccadical_limit(p->pCadical, "conflicts", q->nConflicts);
    }
    else
    {
        p->pKissat = kissat_init();
        if ( p->timeStop ) kissat_set_terminate(p->pKissat, p, Bmc_Lut2Terminate);
        if ( q->fNoFastElim ) kissat_disable_fast_elimination(p->pKissat);
        if ( q->nConflicts ) kissat_set_conflict_limit(p->pKissat, (unsigned)q->nConflicts);
    }
    Bmc_Lut2Structure(p);
    if ( !Bmc_Lut2Stop(p) ) Bmc_Lut2Groups(p);
    if ( !Bmc_Lut2Stop(p) ) Bmc_Lut2Cofactors(p);
    if ( !Bmc_Lut2Stop(p) ) Bmc_Lut2Function(p);
    if ( !Bmc_Lut2Stop(p) ) Bmc_Lut2Backward(p);
    if ( !Bmc_Lut2Stop(p) )
    {
        clkSolve = (abctime)clock();
        Status = p->pCadical ? ccadical_solve(p->pCadical) : kissat_solve(p->pKissat);
        *pTimeSolve += (abctime)clock()-clkSolve;
        if ( Status == 10 && !Bmc_Lut2Extract(p) ) Status = -1;
    }
    return Status;
}

/**Function*************************************************************

  Synopsis    [Releases a search while retaining the extracted LUTs.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Lut2ClearSearch( Bmc_Lut2Man_t * p )
{
    int i;
    if ( p->pKissat ) kissat_release(p->pKissat);
    if ( p->pCadical ) ccadical_release(p->pCadical);
    p->pKissat = NULL; p->pCadical = NULL;
    for ( i = 0; i < LUT2_MAX_NODES; ++i )
    {
        ABC_FREE(p->pCofs[i]);
        ABC_FREE(p->pPins[i]);
    }
    ABC_FREE(p->pValues);
}

/**Function*************************************************************

  Synopsis    [Decides two-LUT decomposition of an incompletely specified function.]

  Description [Two partial columns conflict when their cared values disagree.
  A two-coloring of this conflict graph is exactly a one-bit column encoding.
  In cascade mode the last PI is the preceding rail and cannot bypass a stage.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Lut2DecomposeCare( Bmc_Lut2Man_t * p, word * pCare )
{
    int K = p->pPars->nLutSize, All = p->nMints-1, nShared = 2*K-1-p->nVars;
    int A, S, D, F, B, a, s, d, e, f, j, w, Address, nD, nF, nS, fGood;
    int Bound[256], Free[128], Shared[128], Color[256], Queue[256], Head, Tail;
    int Addresses[256], nColWords;
    word Val[256][2], Care[256][2], Merged[2][2];
    word PackedVal[256], PackedCare[256];
    if ( p->nVars <= K )
    {
        p->nNodes = 1; p->nFans[0] = p->nVars;
        for ( j = 0; j < p->nVars; ++j ) p->Fans[0][j] = j;
        memset(p->Truths[0], 0, sizeof(p->Truths[0]));
        memset(p->Truths[1], 0, sizeof(p->Truths[1]));
        for ( a = 0; a < p->nMints; ++a )
            if ( Abc_TtGetBit(pCare, a) && Abc_TtGetBit(p->pTruth, a) ) Abc_TtSetBit(p->Truths[0], a);
        return 10;
    }
    assert( nShared >= 0 );
    nColWords = Abc_TtWordNum(p->nVars-K);
    assert( nColWords <= 2 );
    p->nNodes = 2;
    for ( A = 1; A <= All && !Bmc_Lut2Stop(p); ++A )
    {
        if ( Abc_TtCountOnes((word)A) != K-1 ) continue;
        if ( p->pPars->fCascade && (A & (1 << (p->nVars-1))) ) continue;
        D = All ^ A; nD = 1 << (p->nVars-K+1);
        for ( d = 0; d < nD; ++d ) Bound[d] = Bmc_Lut2Deposit(d, D);
        for ( S = A; ; S = (S-1) & A )
        {
            if ( Abc_TtCountOnes((word)S) == nShared )
            {
                if ( Bmc_Lut2Stop(p) ) return 0;
                F = A ^ S; B = D | S;
                nS = 1 << nShared; nF = 1 << (K-1-nShared);
                for ( s = 0; s < nS; ++s ) Shared[s] = Bmc_Lut2Deposit(s, S);
                for ( f = 0; f < nF; ++f ) Free[f] = Bmc_Lut2Deposit(f, F);
                memset(p->Truths[0], 0, sizeof(p->Truths[0]));
                memset(p->Truths[1], 0, sizeof(p->Truths[1]));
                Bmc_Lut2Columns(p->pTruth, p->nVars, B, K, PackedVal);
                Bmc_Lut2Columns(pCare, p->nVars, B, K, PackedCare);
                for ( w = 0; w < (1 << K)*nColWords; ++w ) PackedVal[w] &= PackedCare[w];
                fGood = 1;
                for ( s = 0; s < nS && fGood; ++s )
                {
                    memset(Val, 0, nD*sizeof(Val[0])); memset(Care, 0, nD*sizeof(Care[0]));
                    memset(Merged, 0, sizeof(Merged));
                    for ( d = 0; d < nD; ++d )
                    {
                        Color[d] = -1;
                        Addresses[d] = Bmc_Lut2Compress(Shared[s] | Bound[d], B);
                        for ( w = 0; w < nColWords; ++w )
                        {
                            Val[d][w] = PackedVal[Addresses[d]*nColWords+w];
                            Care[d][w] = PackedCare[Addresses[d]*nColWords+w];
                        }
                    }
                    for ( a = 0; a < nD && fGood; ++a ) if ( Color[a] < 0 )
                    {
                        Head = Tail = 0; Queue[Tail++] = a; Color[a] = 0;
                        while ( Head < Tail && fGood )
                        {
                            d = Queue[Head++];
                            for ( e = 0; e < nD; ++e )
                            {
                                for ( w = 0; w < 2; ++w )
                                    if ( (Val[d][w] ^ Val[e][w]) & Care[d][w] & Care[e][w] ) break;
                                if ( w == 2 ) continue;
                                if ( Color[e] == Color[d] ) { fGood = 0; break; }
                                if ( Color[e] >= 0 ) continue;
                                Color[e] = Color[d] ^ 1; Queue[Tail++] = e;
                            }
                        }
                    }
                    if ( !fGood ) break;
                    for ( d = 0; d < nD; ++d )
                    {
                        Address = Addresses[d];
                        if ( Color[d] ) Abc_TtSetBit(p->Truths[0], Address);
                        for ( w = 0; w < 2; ++w ) Merged[Color[d]][w] |= Val[d][w];
                    }
                    for ( d = 0; d < 2; ++d )
                        for ( f = 0; f < nF; ++f ) if ( Abc_TtGetBit(Merged[d], f) )
                        {
                            Address = Bmc_Lut2Compress(Shared[s] | Free[f], A) | (d << (K-1));
                            Abc_TtSetBit(p->Truths[1], Address);
                        }
                }
                if ( fGood )
                {
                    a = 0;
                    for ( j = 0; j < p->nVars; ++j ) if ( (B >> j) & 1 ) p->Fans[0][a++] = j;
                    assert( a == K );
                    a = 0;
                    for ( j = 0; j < p->nVars; ++j ) if ( (A >> j) & 1 ) p->Fans[1][a++] = j;
                    p->Fans[1][a] = p->nVars;
                    p->nFans[0] = p->nFans[1] = K;
                    return 10;
                }
            }
            if ( !S ) break;
        }
    }
    return p->fStopped ? 0 : 20;
}


/**Function*************************************************************

  Synopsis    [Proposes a first LUT of a three-LUT partial function.]

  Description [Within each shared-input assignment, conflicting cared
  columns must receive opposite values of the intermediate bit.  One
  coloring is tried per connected component; failure is inconclusive.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Lut2ProposeCare( Bmc_Lut2Man_t * p )
{
    Bmc_Lut2Man_t * h;
    int K = p->pPars->nLutSize, N = p->nVars, All = p->nMints-1;
    int nCW = Abc_TtWordNum(N-K), nF = 1 << (N-K), nB = 1 << K;
    int nExtra = Abc_MinInt(3, 3*K-2-N), Groups[256], Color[256], Queue[256], Map[14];
    int * Free = ABC_ALLOC(int, nF);
    word * Cols = ABC_CALLOC(word, nB*nCW), * Cares = ABC_CALLOC(word, nB*nCW);
    word GTruth[256], GCare[256], First[4], MVal[16][4], MCare[16][4];
    int Shared, B, S, F, A, LocalS, b, e, f, j, i, w, s, c, nS, Good, Head, Tail, Address;
    int Status = 0, nTrials = 0;
    assert( p->pCare && p->nNodes == 3 && N > K && K <= 8 );
    h = ABC_CALLOC(Bmc_Lut2Man_t, 1);
    h->pPars = p->pPars; h->pTruth = GTruth; h->pCare = GCare; h->timeStop = p->timeStop;
    for ( Shared = 0; Shared <= nExtra && !Bmc_Lut2Stop(p); ++Shared )
    for ( B = 1; B <= All && !Bmc_Lut2Stop(p); ++B )
    {
        if ( Abc_TtCountOnes((word)B) != K ) continue;
        F = All ^ B;
        for ( f = 0; f < nF; ++f ) Free[f] = Bmc_Lut2Deposit(f, F);
        Bmc_Lut2Columns(p->pTruth, N, B, K, Cols);
        Bmc_Lut2Columns(p->pCare, N, B, K, Cares);
        for ( w = 0; w < nB*nCW; ++w ) Cols[w] &= Cares[w];
        for ( S = B; ; S = (S-1)&B )
        {
            if ( Abc_TtCountOnes((word)S) != Shared ) { if ( !S ) break; continue; }
            if ( Bmc_Lut2Stop(p) ) goto finish;
            LocalS = Bmc_Lut2Compress(S, B); nS = 1 << Shared;
            for ( b = 0; b < nB; ++b ) { Groups[b] = Bmc_Lut2Compress(b, LocalS); Color[b] = -1; }
            Good = 1;
            for ( i = 0; i < nB && Good; ++i ) if ( Color[i] < 0 )
            {
                Head = Tail = 0; Queue[Tail++] = i; Color[i] = 0;
                while ( Head < Tail && Good )
                {
                    b = Queue[Head++];
                    for ( e = 0; e < nB; ++e )
                    {
                        if ( Groups[b] != Groups[e] ) continue;
                        for ( w = 0; w < nCW; ++w )
                            if ( (Cols[b*nCW+w] ^ Cols[e*nCW+w]) & Cares[b*nCW+w] & Cares[e*nCW+w] ) break;
                        if ( w == nCW ) continue;
                        if ( Color[b] == Color[e] ) { Good = 0; break; }
                        if ( Color[e] >= 0 ) continue;
                        Color[e] = Color[b]^1; Queue[Tail++] = e;
                    }
                }
            }
            if ( Good )
            {
                if ( nTrials++ == 32 ) goto finish;
                assert( nCW <= 4 );
                memset(MVal, 0, sizeof(MVal)); memset(MCare, 0, sizeof(MCare));
                memset(First, 0, sizeof(First));
                for ( b = 0; b < nB; ++b )
                {
                    if ( Color[b] ) Abc_TtSetBit(First, b);
                    j = 2*Groups[b]+Color[b];
                    for ( w = 0; w < nCW; ++w )
                    {
                        MVal[j][w] |= Cols[b*nCW+w];
                        MCare[j][w] |= Cares[b*nCW+w];
                    }
                }
                A = F | S; j = 0;
                for ( i = 0; i < N; ++i ) if ( (A >> i)&1 ) Map[j++] = i;
                Map[j] = N; h->nVars = j+1; h->nWords = Abc_TtWordNum(h->nVars); h->nMints = 1 << h->nVars;
                memset(GTruth, 0, sizeof(GTruth)); memset(GCare, 0, sizeof(GCare));
                for ( s = 0; s < nS; ++s )
                    for ( c = 0; c < 2; ++c )
                        for ( f = 0; f < nF; ++f ) if ( Abc_TtGetBit(MCare[2*s+c], f) )
                        {
                            Address = Bmc_Lut2Compress(Bmc_Lut2Deposit(s, S) | Free[f], A) | (c << (h->nVars-1));
                            Abc_TtSetBit(GCare, Address);
                            if ( Abc_TtGetBit(MVal[2*s+c], f) ) Abc_TtSetBit(GTruth, Address);
                        }
                Status = Bmc_Lut2DecomposeCare(h, GCare);
                if ( h->fStopped ) { p->fStopped = 1; Status = 0; goto finish; }
                if ( Status == 10 )
                {
                    assert( Bmc_Lut2Verify(h) );
                    p->nNodes = 1+h->nNodes; p->nFans[0] = K; j = 0;
                    for ( i = 0; i < N; ++i ) if ( (B >> i)&1 ) p->Fans[0][j++] = i;
                    memcpy(p->Truths[0], First, sizeof(First));
                    for ( i = 0; i < h->nNodes; ++i )
                    {
                        p->nFans[i+1] = h->nFans[i];
                        memcpy(p->Truths[i+1], h->Truths[i], sizeof(First));
                        for ( j = 0; j < h->nFans[i]; ++j )
                        {
                            c = h->Fans[i][j];
                            p->Fans[i+1][j] = c < h->nVars ? Map[c] : N+1+c-h->nVars;
                        }
                    }
                    goto finish;
                }
                Status = 0;
            }
            if ( !S ) break;
        }
    }
finish:
    ABC_FREE(Cols); ABC_FREE(Cares); ABC_FREE(Free); ABC_FREE(h);
    return Status;
}


/**Function*************************************************************

  Synopsis    [Decides small decompositions and proposes a bounded first LUT.]

  Description [Three connected K-LUTs have at most 3K-2 PI occurrences.
  Therefore at most 3K-2-N inputs of the first LUT can also occur later.
  Enumerate those shared inputs and both column labels for each shared
  assignment, then decide the remaining two-LUT partial function.  At most
  two shared inputs are handled here, bounding the label choices by eight.
  Unreachable rail values remain don't-cares; assigning them would be unsound.
  Outside the complete case, bounded partial-function SAT searches propose
  a first LUT. A failed proposal never proves the original problem UNSAT.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Lut2DecomposePrefix( Bmc_Lut2Man_t * p, int fComplete, int nSharedLimit )
{
    Bmc_Lut2Man_t * g = ABC_CALLOC(Bmc_Lut2Man_t, 1);
    Bmc_Lut2Par_t Pars = *p->pPars;
    abctime timeSolve = 0;
    int nTrials = 0, Remaining = p->nNodes-1;
    int K = p->pPars->nLutSize, nExtra = Abc_MinInt(nSharedLimit, p->nNodes*(K-1)+1-p->nVars), All = p->nMints-1;
    int nF = 1 << (p->nVars-K), nCW = Abc_TtWordNum(p->nVars-K);
    int * Free = ABC_ALLOC(int, nF), Classes[256], Groups[256], Map[LUT2_MAX_VARS];
    int Reps[16][2], nReps[16], Prev[LUT2_MAX_VARS];
    int B, S, F, A, LocalS, nS, b, f, s, c, j, i, t, u, Phase, Address, Status = 20;
    word * Cols = ABC_ALLOC(word, (1 << K)*nCW);
    word GTruth[256], GCare[256], First[4];
    int nCacheWords = Abc_TtWordNum(p->nVars);
    word * Cache = ABC_ALLOC(word, 64*nCacheWords);
    int CacheVars[32], CacheStatus[32], nCached = 0, NextCache = 0, Hits = 0, Key, KeyWords;
    assert( nExtra >= 0 && nExtra <= 4 && p->nVars > K );
    assert( !fComplete || (p->nNodes == 3 && p->nVars >= 3*K-4) );
    Pars.nConflicts = 5000;
    g->pPars = &Pars; g->pTruth = GTruth; g->timeStop = p->timeStop;
    for ( i = 0; i < p->nVars; ++i )
    {
        Prev[i] = -1;
        if ( !p->pPars->fSymmetry ) continue;
        for ( j = i-1; j >= 0; --j )
        {
            for ( t = 0; t < p->nMints; ++t )
            {
                u = t ^ ((((t >> i) ^ (t >> j)) & 1)*((1 << i)|(1 << j)));
                if ( Abc_TtGetBit(p->pTruth, t) != Abc_TtGetBit(p->pTruth, u) ) break;
            }
            if ( t == p->nMints ) { Prev[i] = j; break; }
        }
    }
    for ( B = 1; B <= All && !Bmc_Lut2Stop(p); ++B )
    {
        if ( Abc_TtCountOnes((word)B) != K ) continue;
        // A valid input renaming makes both B and its shared subset prefixes
        // of each verified symmetry class.  This does not bind named inputs.
        for ( i = 0; i < p->nVars; ++i )
            if ( ((B >> i) & 1) && Prev[i] >= 0 && !((B >> Prev[i]) & 1) ) break;
        if ( i < p->nVars ) continue;
        F = All ^ B;
        for ( f = 0; f < nF; ++f ) Free[f] = Bmc_Lut2Deposit(f, F);
        Bmc_Lut2Columns(p->pTruth, p->nVars, B, K, Cols);
        for ( S = B; ; S = (S-1) & B )
        {
            for ( i = 0; i < p->nVars; ++i )
                if ( ((S >> i) & 1) && Prev[i] >= 0 && !((S >> Prev[i]) & 1) ) break;
            if ( i == p->nVars && Abc_TtCountOnes((word)S) <= nExtra &&
                (fComplete || nSharedLimit <= 2 || Abc_TtCountOnes((word)S) == nSharedLimit) )
            {
                if ( Bmc_Lut2Stop(p) ) { Status = 0; goto finish; }
                LocalS = Bmc_Lut2Compress(S, B); nS = 1 << Abc_TtCountOnes((word)S);
                memset(nReps, 0, sizeof(nReps));
                for ( b = 0; b < (1 << K); ++b )
                {
                    s = Groups[b] = Bmc_Lut2Compress(b, LocalS);
                    for ( c = 0; c < nReps[s]; ++c )
                        if ( !memcmp(Cols+b*nCW, Cols+Reps[s][c]*nCW, sizeof(word)*nCW) ) break;
                    if ( c == 2 ) break;
                    if ( c == nReps[s] ) Reps[s][nReps[s]++] = b;
                    Classes[b] = c;
                }
                if ( b == (1 << K) )
                {
                    A = F | S; j = 0;
                    for ( i = 0; i < p->nVars; ++i ) if ( (A >> i) & 1 ) Map[j++] = i;
                    Map[j] = p->nVars; g->nVars = j+1; g->nMints = 1 << g->nVars;
                    // Complementing the first rail absorbs the phase at S = 0.
                    for ( Phase = 0; Phase < (fComplete ? (1 << nS) : 1); Phase += 2 )
                    {
                        if ( Bmc_Lut2Stop(p) ) { Status = 0; goto finish; }
                        memset(First, 0, sizeof(First));
                        memset(GTruth, 0, sizeof(GTruth)); memset(GCare, 0, sizeof(GCare));
                        for ( b = 0; b < (1 << K); ++b )
                            if ( Classes[b] ^ ((Phase >> Groups[b]) & 1) ) Abc_TtSetBit(First, b);
                        for ( s = 0; s < nS; ++s )
                            for ( c = 0; c < nReps[s]; ++c )
                                for ( f = 0; f < nF; ++f )
                                {
                                    Address = Bmc_Lut2Compress(Bmc_Lut2Deposit(s, S) | Free[f], A);
                                    Address |= (c ^ ((Phase >> s) & 1)) << (g->nVars-1);
                                    Abc_TtSetBit(GCare, Address);
                                    if ( Abc_TtGetBit(Cols+Reps[s][c]*nCW, f) ) Abc_TtSetBit(GTruth, Address);
                                }
                        if ( !fComplete && nTrials == 16 ) { Status = 0; goto finish; }
                        nTrials++;
                        // Equal reduced truth/care tables describe the same
                        // child query in local input order. A cached failure
                        // only skips that child; it never proves the parent
                        // UNSAT. Complete searches cache only proved failures.
                        KeyWords = Abc_TtWordNum(g->nVars);
                        assert( KeyWords <= nCacheWords );
                        for ( Key = 0; Key < nCached; ++Key )
                            if ( CacheVars[Key] == g->nVars &&
                                 !memcmp(Cache+2*Key*nCacheWords, GTruth, sizeof(word)*KeyWords) &&
                                 !memcmp(Cache+(2*Key+1)*nCacheWords, GCare, sizeof(word)*KeyWords) ) break;
                        if ( Key < nCached ) { Status = CacheStatus[Key]; Hits++; }
                        else if ( Remaining == 2 ) Status = Bmc_Lut2DecomposeCare(g, GCare);
                        else
                        {
                            int nInputs = g->nVars;
                            memset(g, 0, sizeof(*g));
                            g->pPars = &Pars; g->pTruth = GTruth; g->pCare = GCare;
                            g->nVars = nInputs; g->nMints = 1 << nInputs; g->nWords = Abc_TtWordNum(nInputs);
                            g->nNodes = Remaining; g->nNext = 1; g->timeStop = p->timeStop;
                            g->iRailInput = p->pPars->fCascade ? nInputs : 0;
                            Status = Remaining == 3 && !p->pPars->fCascade && g->nVars > K ? Bmc_Lut2ProposeCare(g) : 0;
                            if ( Status == 0 && !g->fStopped ) Status = Bmc_Lut2Search(g, &timeSolve);
                            if ( Status == 10 && !Bmc_Lut2Verify(g) ) Status = -1;
                            Bmc_Lut2ClearSearch(g);
                        }
                        if ( Status < 0 ) goto finish;
                        if ( g->fStopped ) { Status = 0; p->fStopped = !g->fResource; goto finish; }
                        if ( Status != 10 )
                        {
                            if ( Key == nCached )
                            {
                                CacheVars[NextCache] = g->nVars;
                                CacheStatus[NextCache] = Status;
                                memcpy(Cache+2*NextCache*nCacheWords, GTruth, sizeof(word)*KeyWords);
                                memcpy(Cache+(2*NextCache+1)*nCacheWords, GCare, sizeof(word)*KeyWords);
                                if ( nCached < 32 ) ++nCached;
                                NextCache = (NextCache+1)&31;
                            }
                            continue;
                        }
                        p->nNodes = 1+g->nNodes; p->nFans[0] = K;
                        j = 0;
                        for ( i = 0; i < p->nVars; ++i ) if ( (B >> i) & 1 ) p->Fans[0][j++] = i;
                        memcpy(p->Truths[0], First, sizeof(First));
                        for ( i = 0; i < g->nNodes; ++i )
                        {
                            p->nFans[i+1] = g->nFans[i];
                            memcpy(p->Truths[i+1], g->Truths[i], sizeof(First));
                            for ( j = 0; j < g->nFans[i]; ++j )
                            {
                                c = g->Fans[i][j];
                                p->Fans[i+1][j] = c < g->nVars ? Map[c] : p->nVars+1+c-g->nVars;
                            }
                        }
                        goto finish;
                    }
                }
            }
            if ( !S ) break;
        }
    }
    Status = p->fStopped || !fComplete ? 0 : 20;
finish:
    p->timeCandidates += timeSolve;
    if ( !fComplete && p->pPars->fVerbose ) printf("Partial decomposition: shared limit %d, %d reduced problems, %.6f solver CPU seconds.\n", nSharedLimit, nTrials, (double)timeSolve/CLOCKS_PER_SEC);
    if ( p->pPars->fVerbose && Hits ) printf("Repeated partial queries skipped: %d.\n", Hits);
    ABC_FREE(Cache); ABC_FREE(Cols); ABC_FREE(Free); ABC_FREE(g);
    return Status;
}

/**Function*************************************************************

  Synopsis    [Enumerates fixed-size subsets in lexicographic PI order.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Lut2NextSubset( int Mask, int nVars )
{
    int Vars[LUT2_MAX_VARS], n = 0, i, j;
    for ( i = 0; i < nVars; ++i ) if ( (Mask >> i) & 1 ) Vars[n++] = i;
    for ( i = n-1; i >= 0 && Vars[i] == nVars-n+i; --i ) {}
    if ( i < 0 ) return -1;
    ++Vars[i];
    for ( j = i+1; j < n; ++j ) Vars[j] = Vars[j-1]+1;
    for ( Mask = i = 0; i < n; ++i ) Mask |= 1 << Vars[i];
    return Mask;
}

/**Function*************************************************************

  Synopsis    [Proposes two parallel LUTs encoding a four-column decomposition.]

  Description [Enumerate a small bound set with at most four distinct columns.
  Assign two-bit labels, requiring each label bit to depend on at most K PIs,
  then solve the remaining two-LUT partial function. Only a verified witness
  is useful; exhausting this restricted search never proves global UNSAT.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Lut2DecomposePair( Bmc_Lut2Man_t * p, int BoundSize, abctime End )
{
    static const int Perms[6][3] = {{1,2,3},{1,3,2},{2,1,3},{2,3,1},{3,1,2},{3,2,1}};
    int K = p->pPars->nLutSize, N = p->nVars;
    int FreeSize = N-BoundSize, nCW, nB, nF, B, b, f, c, j, k, i, r, a, Count, Status = 0;
    int Classes[512], Reps[4], BoundMap[9], LeafMap[2][9], FreeMap[14], LeafSize[2], Codes[4];
    word * Cols, Leaf[2][8], Truth[256], Care[256];
    Bmc_Lut2Man_t * h;
    int Queries = 0, GoodGroups = 0;
    assert( p->nNodes == 4 && !p->pPars->fCascade && !p->pCare );
    if ( FreeSize < 0 || FreeSize+2 > 2*K-1 || BoundSize > 9 || (abctime)clock() >= End ) return 0;
    if ( p->timeStop && p->timeStop < End ) End = p->timeStop;
    nCW = Abc_TtWordNum(FreeSize); nB = 1 << BoundSize; nF = 1 << FreeSize;
    Cols = ABC_ALLOC(word, nB*nCW); h = ABC_CALLOC(Bmc_Lut2Man_t, 1);
    h->pPars = p->pPars; h->pTruth = Truth; h->pCare = Care;
    h->nVars = FreeSize+2; h->nMints = 1 << h->nVars; h->nWords = Abc_TtWordNum(h->nVars); h->timeStop = End;
    for ( B = (1 << BoundSize)-1; B >= 0; B = Bmc_Lut2NextSubset(B, N) )
    {
        if ( (abctime)clock() >= End || Bmc_Lut2Stop(p) ) break;
        Bmc_Lut2Columns(p->pTruth, N, B, BoundSize, Cols);
        Count = 0;
        for ( b = 0; b < nB; ++b )
        {
            for ( c = 0; c < Count; ++c )
                if ( !memcmp(Cols+b*nCW, Cols+Reps[c]*nCW, sizeof(word)*nCW) ) break;
            if ( c == 4 ) break;
            if ( c == Count ) Reps[Count++] = b;
            Classes[b] = c;
        }
        if ( b < nB || Count < 3 ) continue;
        GoodGroups++;
        // The first column includes the all-zero assignment. Labeling it
        // zero normalizes both rails; try every ordering of the other labels.
        for ( i = j = k = 0; i < N; ++i )
            if ( (B >> i) & 1 ) BoundMap[j++] = i; else FreeMap[k++] = i;
        for ( r = 0; r < 6; ++r )
        {
            Codes[0] = 0;
            for ( c = 1; c < 4; ++c ) Codes[c] = Perms[r][c-1];
            memset(Leaf, 0, sizeof(Leaf));
            for ( b = 0; b < nB; ++b )
                for ( k = 0; k < 2; ++k ) if ( (Codes[Classes[b]] >> k) & 1 ) Abc_TtSetBit(Leaf[k], b);
            // Both functions must individually fit one K-input LUT.
            for ( k = 0; k < 2; ++k )
            {
                memcpy(LeafMap[k], BoundMap, sizeof(int)*BoundSize);
                if ( BoundSize < 6 ) Leaf[k][0] = Abc_Tt6Stretch(Leaf[k][0], BoundSize);
                LeafSize[k] = Abc_TtMinBase(Leaf[k], LeafMap[k], BoundSize, BoundSize);
            }
            if ( LeafSize[0] > K || LeafSize[1] > K || LeafSize[0] < 2 || LeafSize[1] < 2 ) continue;
            // Labels absent from the column set are unreachable, and must
            // remain unspecified in the two-LUT child problem.
            memset(Truth, 0, sizeof(Truth)); memset(Care, 0, sizeof(Care));
            for ( c = 0; c < Count; ++c )
                for ( f = 0; f < nF; ++f )
                {
                    a = f | (Codes[c] << FreeSize);
                    Abc_TtSetBit(Care, a);
                    if ( Abc_TtGetBit(Cols+Reps[c]*nCW, f) ) Abc_TtSetBit(Truth, a);
                }
            Queries++;
            Status = Bmc_Lut2DecomposeCare(h, Care);
            if ( Status != 10 ) { Status = 0; continue; }
            p->nNodes = h->nNodes+2;
            for ( k = 0; k < 2; ++k )
            {
                p->nFans[k] = LeafSize[k];
                memcpy(p->Fans[k], LeafMap[k], sizeof(int)*LeafSize[k]);
                memcpy(p->Truths[k], Leaf[k], sizeof(word)*Abc_TtWordNum(LeafSize[k]));
            }
            for ( i = 0; i < h->nNodes; ++i )
            {
                p->nFans[2+i] = h->nFans[i];
                memcpy(p->Truths[2+i], h->Truths[i], sizeof(p->Truths[0]));
                for ( j = 0; j < h->nFans[i]; ++j )
                {
                    a = h->Fans[i][j];
                    p->Fans[2+i][j] = a < FreeSize ? FreeMap[a] : a < FreeSize+2 ? N+a-FreeSize : N+2+a-h->nVars;
                }
            }
            goto finish;
        }
    }
finish:
    if ( p->pPars->fVerbose )
        printf("Two-rail decomposition: %d groups, %d partial queries.\n", GoodGroups, Queries);
    ABC_FREE(Cols); ABC_FREE(h); return Status;
}


/**Function*************************************************************

  Synopsis    [Proposes a final LUT and synthesizes its one-bit input function.]

  Description [The final LUT has K-1 direct PIs and one synthesized input.
  For each assignment to PIs shared with the input function, its columns
  must have at most two distinct values. Canonical labels give one input
  function to try. A failed or limited child search is inconclusive; only
  a verified solution can replace the original, unrestricted SAT search.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Lut2DecomposeRoot( Bmc_Lut2Man_t * p, int fSearch )
{
    Bmc_Lut2Man_t * g = ABC_CALLOC(Bmc_Lut2Man_t, 1);
    Bmc_Lut2Par_t Pars = *p->pPars;
    int K = Pars.nLutSize, N = p->nVars, All = p->nMints-1, Remaining = p->nNodes-1;
    int nD = 1 << (N-K+1), * Bound = ABC_ALLOC(int, nD), Free[128], Shared[8], Map[LUT2_MAX_VARS];
    int A, S, D, F, B, a, s, d, f, j, i, c, Address, nF, nS, Class, nClasses, Good, Share;
    int Status = 0, nTrials = 0, nInputs, Prefix, LocalS;
    word Col[2], Cols[2][2], GTruth[256], Root[4];
    abctime TimeSolve = 0, TimeEnd = (abctime)clock() + (fSearch ? (abctime)20*CLOCKS_PER_SEC : CLOCKS_PER_SEC/4);
    if ( p->timeStop && p->timeStop < TimeEnd ) TimeEnd = p->timeStop;
    Pars.nConflicts = 500000;
    assert( !Pars.fCascade && !p->pCare && N > K && K >= 4 && Remaining >= 3 );
    assert( fSearch || Remaining == 3 );
    for ( Share = 0; Share <= Abc_MinInt(3, K-2); ++Share )
    for ( A = (1 << (K-1))-1; A >= 0; A = Bmc_Lut2NextSubset(A, N) )
    {
        if ( (abctime)clock() >= TimeEnd || Bmc_Lut2Stop(p) ) goto finish;
        D = All ^ A;
        for ( d = 0; d < nD; ++d ) Bound[d] = Bmc_Lut2Deposit(d, D);
        for ( LocalS = (1 << Share)-1; LocalS >= 0; LocalS = Bmc_Lut2NextSubset(LocalS, K-1) )
        {
            S = Bmc_Lut2Deposit(LocalS, A);
            F = A ^ S; B = D | S; nS = 1 << Share; nF = 1 << (K-1-Share);
            for ( s = 0; s < nS; ++s ) Shared[s] = Bmc_Lut2Deposit(s, S);
            for ( f = 0; f < nF; ++f ) Free[f] = Bmc_Lut2Deposit(f, F);
            memset(GTruth, 0, sizeof(GTruth)); memset(Root, 0, sizeof(Root));
            Good = 1;
            for ( s = 0; s < nS && Good; ++s )
            {
                nClasses = 0;
                memset(Cols, 0, sizeof(Cols));
                for ( d = 0; d < nD; ++d )
                {
                    Col[0] = Col[1] = 0;
                    for ( f = 0; f < nF; ++f )
                        if ( Abc_TtGetBit(p->pTruth, Shared[s] | Bound[d] | Free[f]) ) Abc_TtSetBit(Col, f);
                    for ( Class = 0; Class < nClasses; ++Class )
                        if ( Col[0] == Cols[Class][0] && Col[1] == Cols[Class][1] ) break;
                    if ( Class == 2 ) { Good = 0; break; }
                    if ( Class == nClasses ) memcpy(Cols[nClasses++], Col, sizeof(Col));
                    Address = Bmc_Lut2Compress(Shared[s] | Bound[d], B);
                    if ( Class ) Abc_TtSetBit(GTruth, Address);
                }
                for ( Class = 0; Class < nClasses; ++Class )
                    for ( f = 0; f < nF; ++f ) if ( Abc_TtGetBit(Cols[Class], f) )
                    {
                        Address = Bmc_Lut2Compress(Shared[s] | Free[f], A) | (Class << (K-1));
                        Abc_TtSetBit(Root, Address);
                    }
            }
            if ( Good )
            {
                if ( nTrials == 32 || (abctime)clock() >= TimeEnd || Bmc_Lut2Stop(p) ) goto finish;
                ++nTrials; nInputs = 0;
                for ( i = 0; i < N; ++i ) if ( (B >> i) & 1 ) Map[nInputs++] = i;
                if ( nInputs < 6 ) GTruth[0] = Abc_Tt6Stretch(GTruth[0], nInputs);
                nInputs = Abc_TtMinBase(GTruth, Map, nInputs, nInputs);
                memset(g, 0, sizeof(*g));
                g->pPars = &Pars; g->pTruth = GTruth; g->nVars = nInputs;
                g->nWords = Abc_TtWordNum(nInputs); g->nMints = 1 << nInputs;
                g->nNodes = Remaining; g->nNext = 1;
                g->timeStop = (abctime)clock() + (abctime)10*CLOCKS_PER_SEC;
                if ( TimeEnd < g->timeStop ) g->timeStop = TimeEnd;
                Status = 0;
                if ( nInputs > Remaining*(K-1)+1 ) Status = 20;
                else if ( nInputs <= K )
                {
                    g->nNodes = 1; g->nFans[0] = nInputs;
                    for ( i = 0; i < nInputs; ++i ) g->Fans[0][i] = i;
                    memcpy(g->Truths[0], GTruth, sizeof(word)*g->nWords);
                    Status = 10;
                }
                else if ( Remaining == 3 && nInputs >= 3*K-4 ) Status = Bmc_Lut2DecomposePrefix(g, 1, 2);
                else
                {
                    for ( Prefix = 2; Prefix <= Abc_MinInt(4, K-2) && !Status && !Bmc_Lut2Stop(g); ++Prefix )
                        Status = Bmc_Lut2DecomposePrefix(g, 0, Prefix);
                    if ( !Status && fSearch && !Bmc_Lut2Stop(g) ) Status = Bmc_Lut2Search(g, &TimeSolve);
                }
                TimeSolve += g->timeCandidates;
                if ( Status == 10 && !Bmc_Lut2Verify(g) ) Status = -1;
                Bmc_Lut2ClearSearch(g);
                if ( Status < 0 ) goto finish;
                if ( Status == 10 )
                {
                    p->nNodes = g->nNodes+1;
                    for ( i = 0; i < g->nNodes; ++i )
                    {
                        p->nFans[i] = g->nFans[i];
                        memcpy(p->Truths[i], g->Truths[i], sizeof(Root));
                        for ( j = 0; j < g->nFans[i]; ++j )
                        {
                            c = g->Fans[i][j];
                            p->Fans[i][j] = c < nInputs ? Map[c] : N+c-nInputs;
                        }
                    }
                    a = 0;
                    for ( i = 0; i < N; ++i ) if ( (A >> i) & 1 ) p->Fans[g->nNodes][a++] = i;
                    p->Fans[g->nNodes][a] = N+g->nNodes-1;
                    p->nFans[g->nNodes] = K;
                    memcpy(p->Truths[g->nNodes], Root, sizeof(Root));
                    goto finish;
                }
                Status = 0;
            }
        }
    }
finish:
    Bmc_Lut2Stop(p);
    p->timeCandidates += TimeSolve;
    if ( p->pPars->fVerbose ) printf("Output decomposition%s: %d reduced problems, %.6f solver CPU seconds.\n", fSearch ? " with SAT" : "", nTrials, (double)TimeSolve/CLOCKS_PER_SEC);
    ABC_FREE(Bound); ABC_FREE(g);
    return Status;
}

/**Function*************************************************************

  Synopsis    [Derives a LUT network as an AIG in original PI order.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Bmc_Lut2Derive( Bmc_Lut2Man_t * p )
{
    Gia_Man_t * pGia = Gia_ManStart(1000), * pClean;
    int Inputs[LUT2_MAX_VARS], Values[LUT2_MAX_OBJS], Fans[LUT2_MAX_LUT], i, j, Root;
    pGia->pName = Abc_UtilStrsav((char *)"lutexact2");
    for ( i = 0; i < p->pPars->nInputs; ++i ) Inputs[i] = Gia_ManAppendCi(pGia);
    for ( i = 0; i < p->nVars; ++i ) Values[i] = Inputs[p->Map[i]];
    Gia_ManHashAlloc(pGia);
    for ( i = 0; i < p->nNodes; ++i )
    {
        for ( j = 0; j < p->nFans[i]; ++j ) Fans[j] = Values[p->Fans[i][j]];
        Values[p->nVars+i] = Bmc_ExactLut(pGia, p->Truths[i], Fans, p->nFans[i], 0);
    }
    Root = p->nNodes ? Values[p->nVars+p->nNodes-1] : p->nVars ? Values[0] : 0;
    Gia_ManAppendCo(pGia, Abc_LitNotCond(Root, p->fCompl));
    Gia_ManHashStop(pGia);
    pClean = Gia_ManCleanup(pGia);
    Gia_ManStop(pGia);
    return pClean;
}

/**Function*************************************************************

  Synopsis    [Checks the exported AIG, including original input positions and phase.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Lut2CheckGia( Bmc_Lut2Man_t * p, Gia_Man_t * pGia )
{
    word * pTruth = Gia_ObjComputeTruthTable(pGia, Gia_ManCo(pGia, 0));
    int t, j, Address, fOk = 1;
    for ( t = 0; t < (1 << p->pPars->nInputs); ++t )
    {
        Address = 0;
        for ( j = 0; j < p->nVars; ++j ) Address |= ((t >> p->Map[j]) & 1) << j;
        if ( Abc_TtGetBit(pTruth, t) != (Abc_TtGetBit(p->pTruth, Address) ^ p->fCompl) ) { fOk = 0; break; }
    }
    Gia_ObjComputeTruthTableStop(pGia);
    return fOk;
}

/**Function*************************************************************

  Synopsis    [Prints a node name and the verified network.]

  Description [Printed pins are MSB first, reversing the internal Fans array.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Lut2Name( FILE * pFile, Bmc_Lut2Man_t * p, int i )
{
    if ( i < p->nVars ) fprintf(pFile, "%c", 'a'+p->Map[i]);
    else if ( i-p->nVars < 26 ) fprintf(pFile, "%c", 'A'+i-p->nVars);
    else fprintf(pFile, "N%d", i-p->nVars);
}
static void Bmc_Lut2Print( Bmc_Lut2Man_t * p )
{
    int i, j;
    printf("Realization using %d LUTs of at most %d inputs (verified):\n", p->nNodes, p->pPars->nLutSize);
    for ( i = p->nNodes-1; i >= 0; --i )
    {
        Bmc_Lut2Name(stdout, p, p->nVars+i);
        printf(" = %d'b", 1 << p->nFans[i]);
        for ( j = (1 << p->nFans[i])-1; j >= 0; --j ) printf("%d", Abc_TtGetBit(p->Truths[i], j));
        printf("( ");
        for ( j = p->nFans[i]-1; j >= 0; --j ) { Bmc_Lut2Name(stdout, p, p->Fans[i][j]); printf(" "); }
        printf(")\n");
    }
    printf("out = %s", p->fCompl ? "!" : "");
    if ( p->nVars || p->nNodes ) Bmc_Lut2Name(stdout, p, p->nVars+p->nNodes-1);
    else printf("0");
    printf("\n");
}

/**Function*************************************************************

  Synopsis    [Writes the verified LUT network to a function-specific BLIF file.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Lut2Dump( Bmc_Lut2Man_t * p )
{
    unsigned Hash = 2166136261u;
    char Name[128];
    FILE * pFile;
    int i, j, t, fOk;
    for ( i = 0; i < p->nMints; ++i ) Hash = (Hash ^ (unsigned)Abc_TtGetBit(p->pTruth, i)) * 16777619u;
    for ( i = 0; i < p->nVars; ++i ) Hash = (Hash ^ (unsigned)p->Map[i]) * 16777619u;
    Hash = (Hash ^ (unsigned)p->fCompl) * 16777619u;
    sprintf(Name, "lutexact2_%08x_%d_%d.blif", Hash, p->pPars->nLutSize, p->nNodes);
    pFile = fopen(Name, "wb");
    if ( !pFile ) { Abc_Print(-1, "Cannot write %s.\n", Name); return 0; }
    fprintf(pFile, ".model lutexact2\n.inputs");
    for ( i = 0; i < p->pPars->nInputs; ++i ) fprintf(pFile, " %c", 'a'+i);
    fprintf(pFile, "\n.outputs out\n");
    for ( i = 0; i < p->nNodes; ++i )
    {
        fprintf(pFile, ".names ");
        for ( j = 0; j < p->nFans[i]; ++j ) { Bmc_Lut2Name(pFile, p, p->Fans[i][j]); fprintf(pFile, " "); }
        Bmc_Lut2Name(pFile, p, p->nVars+i); fprintf(pFile, "\n");
        for ( t = 0; t < (1 << p->nFans[i]); ++t ) if ( Abc_TtGetBit(p->Truths[i], t) )
        {
            for ( j = 0; j < p->nFans[i]; ++j ) fprintf(pFile, "%d", (t >> j) & 1);
            fprintf(pFile, " 1\n");
        }
    }
    fprintf(pFile, ".names ");
    if ( p->nVars || p->nNodes )
    {
        Bmc_Lut2Name(pFile, p, p->nVars+p->nNodes-1);
        fprintf(pFile, " out\n%d 1\n", !p->fCompl);
    }
    else fprintf(pFile, "out\n%s", p->fCompl ? "1\n" : "");
    fprintf(pFile, ".end\n");
    fOk = !ferror(pFile);
    if ( fclose(pFile) ) fOk = 0;
    if ( !fOk ) Abc_Print(-1, "Error writing %s.\n", Name);
    else printf("Network written to %s.\n", Name);
    return fOk;
}

/**Function*************************************************************

  Synopsis    [Solves one LUT bound, returning SAT, UNSAT, UNKNOWN, or an error.]

  Description [The solver is private to the command.  No global solver defaults
  are changed, and no partial result is installed after UNKNOWN or an error.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Lut2Solve( Bmc_Lut2Par_t * q, word * pTruth, int nVars, int * pMap, int nNodes, Gia_Man_t ** ppGia )
{
    Bmc_Lut2Man_t * p = ABC_CALLOC(Bmc_Lut2Man_t, 1);
    abctime clk = (abctime)clock(), timeSolve = 0;
    int i, Shared, Status = 0, fDirect = 0;
    p->pPars = q; p->nVars = nVars; p->nNodes = nNodes; p->nNext = 1;
    p->nWords = Abc_TtWordNum(nVars); p->nMints = 1 << nVars;
    p->pTruth = ABC_ALLOC(word, p->nWords);
    p->fCompl = Abc_TtGetBit(pTruth, 0);
    Abc_TtCopy(p->pTruth, pTruth, p->nWords, p->fCompl);
    memcpy(p->Map, pMap, sizeof(int)*nVars);
    if ( q->nSeconds ) p->timeStop = clk + (abctime)q->nSeconds*CLOCKS_PER_SEC;
    if ( nVars > 1 && nNodes*(q->nLutSize-1)+1 < nVars ) Status = 20;
    else if ( nVars <= 1 ) { p->nNodes = 0; Status = 10; }
    else if ( nVars <= q->nLutSize )
    {
        p->nNodes = 1; p->nFans[0] = nVars;
        for ( i = 0; i < nVars; ++i ) p->Fans[0][i] = i;
        Abc_TtCopy(p->Truths[0], p->pTruth, p->nWords, 0);
        Status = 10;
    }
    else if ( nNodes == 2 && q->fDirect ) { fDirect = 2; Status = Bmc_Lut2Decompose(p); }
    else if ( nNodes == 3 && q->fThree && nVars >= 3*q->nLutSize-4 )
    { fDirect = 3; Status = Bmc_Lut2DecomposePrefix(p, 1, 2); }
    else
    {
        abctime timeStop = p->timeStop;
        // Only incomplete candidate searches use this deadline. Expiring it
        // cannot prove UNSAT or prevent the original exact search below.
        if ( q->nProbeSeconds >= 0 )
        {
            abctime timeProbe = (abctime)clock() + (abctime)q->nProbeSeconds*CLOCKS_PER_SEC;
            if ( !p->timeStop || timeProbe < p->timeStop ) p->timeStop = timeProbe;
        }
        if ( q->fPrefix && !Bmc_Lut2Stop(p) && !q->nConflicts && !q->fCascade && q->nLutSize >= 4 && nNodes == 4 )
        {
            int BoundSize;
            abctime timePairEnd = (abctime)clock()+CLOCKS_PER_SEC/4;
            // At most 512 columns; all bound sizes share this short budget.
            for ( BoundSize = q->nLutSize+1; BoundSize <= Abc_MinInt(q->nLutSize+3, 9) && !Status && !Bmc_Lut2Stop(p); ++BoundSize )
                Status = Bmc_Lut2DecomposePair(p, BoundSize, timePairEnd);
        }
        if ( Status == 0 && q->fPrefix && !Bmc_Lut2Stop(p) && !q->nConflicts && !q->fCascade && q->nLutSize >= 4 && nNodes == 4 )
            Status = Bmc_Lut2DecomposeRoot(p, 0);
        if ( q->fPrefix && !q->nConflicts && q->nLutSize >= 4 && nNodes >= 3 && nNodes <= 8 )
            for ( Shared = 2; Shared <= Abc_MinInt(4, q->nLutSize-2) && Status == 0 && !Bmc_Lut2Stop(p); ++Shared )
                Status = Bmc_Lut2DecomposePrefix(p, 0, Shared);
        if ( Status == 0 && !Bmc_Lut2Stop(p) && q->fPrefix && !q->nConflicts && !q->fCascade && q->nLutSize >= 4 && nNodes >= 4 && nNodes <= 8 )
            Status = Bmc_Lut2DecomposeRoot(p, 1);
        if ( q->nProbeSeconds >= 0 )
        {
            abctime timeNow = (abctime)clock();
            // Resume only if the candidate deadline stopped the proposals
            // and the overall count still has time left.
            if ( p->fStopped && !p->fResource && p->timeStop && timeNow >= p->timeStop &&
                 (!timeStop || (p->timeStop < timeStop && timeNow < timeStop)) )
            {
                p->fStopped = 0;
                if ( q->fVerbose ) printf("Candidate budget exhausted; continuing with exact SAT.\n");
            }
            p->timeStop = timeStop;
        }
        if ( Status == 0 && !Bmc_Lut2Stop(p) ) Status = Bmc_Lut2Search(p, &timeSolve);
    }
    timeSolve += p->timeCandidates;
    if ( Status == 10 && !Bmc_Lut2Verify(p) ) Status = -1;
    if ( Status == 10 )
    {
        *ppGia = Bmc_Lut2Derive(p);
        if ( !Bmc_Lut2CheckGia(p, *ppGia) )
        {
            Gia_ManStop(*ppGia); *ppGia = NULL; Status = -1;
        }
    }
    if ( Status < 0 ) Abc_Print(-1, "Internal error: LUT network failed exhaustive verification.\n");
    if ( !q->fSilent )
    {
        printf("LUT bound = %d : %s  CPU = %.6f sec\n", nNodes,
            Status == 10 ? "SAT" : Status == 20 ? "UNSAT" : Status < 0 ? "ERROR" : "UNKNOWN", (double)((abctime)clock()-clk)/CLOCKS_PER_SEC);
        if ( p->fResource ) printf("Formula resource limit reached; no UNSAT conclusion.\n");
        if ( fDirect ) printf("Complete %d-LUT decomposition test.\n", fDirect);
    }
    if ( q->fVerbose )
        printf("Final CNF: %d variables, %.0f clauses, %.0f literals.  Build/check = %.6f sec.  Solve = %.6f sec.\n",
            p->nNext-1, (double)p->nClauses, (double)p->nLiterals,
            (double)((abctime)clock()-clk-timeSolve)/CLOCKS_PER_SEC, (double)timeSolve/CLOCKS_PER_SEC);
    if ( Status == 10 )
    {
        Bmc_Lut2Print(p);
        if ( q->fDump && !Bmc_Lut2Dump(p) ) { Gia_ManStop(*ppGia); *ppGia = NULL; Status = -1; }
    }
    Bmc_Lut2ClearSearch(p);
    ABC_FREE(p->pTruth);
    ABC_FREE(p);
    return Status;
}

/**Function*************************************************************

  Synopsis    [Parses a nonnegative integer without truncation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Lut2Number( int argc, char ** argv, int c, int * pValue )
{
    char * pEnd;
    long Value;
    if ( globalUtilOptind >= argc ) { Abc_Print(-1, "Option -%c requires an integer.\n", c); return 0; }
    errno = 0;
    Value = strtol(argv[globalUtilOptind], &pEnd, 10);
    if ( errno || pEnd == argv[globalUtilOptind] || *pEnd || Value < 0 || Value > INT_MAX )
    { Abc_Print(-1, "Option -%c requires an integer in [0, %d].\n", c, INT_MAX); return 0; }
    globalUtilOptind++;
    *pValue = (int)Value;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Prints the traditional ABC command usage.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Lut2Usage( void )
{
    Abc_Print(-2, "usage: lutexact2 [-NMKTCSEB <num>] [-Y string] [-rpamckougjbedsvh] [hex]\n");
    Abc_Print(-2, "\t           exact synthesis of general LUT networks; replaces the current network\n");
    Abc_Print(-2, "\t-N <num> : input count, 0..14 [default = infer from hex, -Y, or network]\n");
    Abc_Print(-2, "\t-M <num> : maximum LUT count, 0..64 [required]\n");
    Abc_Print(-2, "\t-K <num> : maximum LUT size, 2..8 [default = 2]\n");
    Abc_Print(-2, "\t-T <num> : CPU time limit per count, including construction [default = 0: none]\n");
    Abc_Print(-2, "\t-B <num> : candidate CPU seconds per count; 0 disables [default = automatic]\n");
    Abc_Print(-2, "\t           within -T; complete two/three-LUT tests and full SAT are unaffected\n");
    Abc_Print(-2, "\t-C <num> : conflict limit per count [default = 0: none]\n");
    Abc_Print(-2, "\t-S <num> : CaDiCaL seed, 0..2000000000 [default = 0]\n");
    Abc_Print(-2, "\t-E <num> : encoding: 0 = hybrid, 1 = pins, 2 = cofactors [default = 0]\n");
    Abc_Print(-2, "\t-Y <str> : symmetric function values by increasing Hamming weight\n");
    Abc_Print(-2, "\t-r       : toggle single-rail LUT cascades [default = no]\n");
    Abc_Print(-2, "\t-m       : toggle minimum search through M; -T skips UNKNOWN [default = no]\n");
    Abc_Print(-2, "\t-c       : toggle CaDiCaL instead of Kissat [default = no]\n");
    Abc_Print(-2, "\t-k       : toggle explicit Kissat selection [default = no]\n");
    Abc_Print(-2, "\t-o       : toggle complete two-LUT decomposition test [default = yes]\n");
    Abc_Print(-2, "\t-p       : toggle bounded decomposition candidates [default = yes]\n");
    Abc_Print(-2, "\t-a       : toggle complete three-LUT test near the coverage bound [default = yes]\n");
    Abc_Print(-2, "\t-u       : toggle verified input and node symmetries [default = yes]\n");
    Abc_Print(-2, "\t-g       : toggle verified simultaneous input-swap symmetries [default = no]\n");
    Abc_Print(-2, "\t-j       : toggle two-clause consensus for 2:1 muxes [default = no]\n");
    Abc_Print(-2, "\t-b       : toggle output backward distinguishability [default = no]\n");
    Abc_Print(-2, "\t-e       : toggle skipping Kissat's initial fast elimination [default = no]\n");
    Abc_Print(-2, "\t-d       : toggle writing verified solutions to lutexact2_*.blif [default = no]\n");
    Abc_Print(-2, "\t-s       : toggle printing solutions only [default = no]\n");
    Abc_Print(-2, "\t-v       : toggle construction and solving statistics [default = no]\n");
    Abc_Print(-2, "\t-h       : print the command usage\n");
    Abc_Print(-2, "\t[hex]    : hexadecimal truth table, bit 0 = all-zero input (keep leading zeros)\n");
    Abc_Print(-2, "\t           without hex/-Y, uses the current single-output combinational network\n");
    Abc_Print(-2, "\t           removes inessential inputs; constants and literals need zero LUTs\n");
    Abc_Print(-2, "\t           use casexact for fixed cascade input bindings\n");
    Abc_Print(-2, "\tExample: lutexact2 -K 3 -M 3 -m -Y 000111\n");
}

/**Function*************************************************************

  Synopsis    [Implements lutexact2 without modifying the legacy command.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandLutExact2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Bmc_Lut2Par_t Pars, * p = &Pars;
    Gia_Man_t * pGia = NULL;
    Bmc_Exact_t Target = {0};
    word * pTruth = NULL;
    char * pHex = NULL, * pSym = NULL;
    int Map[LUT2_MAX_VARS], c, i, t, n, nVars, Bound, Lower, Status = 20, FirstUnknown = -1, Ret = 1;
    int fN = 0, fM = 0, fKissat = 0;
    memset(p, 0, sizeof(*p));
    p->nLutSize = 2; p->fSymmetry = p->fDirect = p->fThree = p->fPrefix = 1;
    p->nProbeSeconds = -1;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "NMKTCSEBYrpamckougjbedsvh")) != EOF )
    {
        switch ( c )
        {
        case 'N': if ( !Bmc_Lut2Number(argc, argv, c, &p->nInputs) ) goto finish; fN = 1; break;
        case 'M': if ( !Bmc_Lut2Number(argc, argv, c, &p->nNodes) ) goto finish; fM = 1; break;
        case 'K': if ( !Bmc_Lut2Number(argc, argv, c, &p->nLutSize) ) goto finish; break;
        case 'T': if ( !Bmc_Lut2Number(argc, argv, c, &p->nSeconds) ) goto finish; break;
        case 'B': if ( !Bmc_Lut2Number(argc, argv, c, &p->nProbeSeconds) ) goto finish; break;
        case 'C': if ( !Bmc_Lut2Number(argc, argv, c, &p->nConflicts) ) goto finish; break;
        case 'S': if ( !Bmc_Lut2Number(argc, argv, c, &p->nSeed) ) goto finish; break;
        case 'E': if ( !Bmc_Lut2Number(argc, argv, c, &p->Encoding) ) goto finish; break;
        case 'Y':
            if ( globalUtilOptind >= argc ) { Abc_Print(-1, "Option -Y requires a string.\n"); goto finish; }
            pSym = argv[globalUtilOptind++]; break;
        case 'm': p->fMinimum ^= 1; break;
        case 'r': p->fCascade ^= 1; break;
        case 'a': p->fThree ^= 1; break;
        case 'p': p->fPrefix ^= 1; break;
        case 'c': p->fCadical ^= 1; break;
        case 'k': fKissat ^= 1; break;
        case 'o': p->fDirect ^= 1; break;
        case 'u': p->fSymmetry ^= 1; break;
        case 'g': p->fGroups ^= 1; break;
        case 'j': p->fConsensus ^= 1; break;
        case 'b': p->fBackward ^= 1; break;
        case 'e': p->fNoFastElim ^= 1; break;
        case 'd': p->fDump ^= 1; break;
        case 's': p->fSilent ^= 1; break;
        case 'v': p->fVerbose ^= 1; break;
        default: Bmc_Lut2Usage(); goto finish;
        }
    }
    if ( !fM || p->nInputs > LUT2_MAX_VARS || p->nNodes > LUT2_MAX_NODES ||
        p->nLutSize < 2 || p->nLutSize > LUT2_MAX_LUT || p->Encoding > 2 || p->nSeed > 2000000000 )
    { Abc_Print(-1, "Require -M in 0..64, N in 0..14, K in 2..8, E in 0..2, and S in 0..2000000000.\n"); goto finish; }
    if ( (p->fCadical && fKissat) || (!p->fCadical && p->nSeed) || (p->fCadical && p->fNoFastElim) )
    { Abc_Print(-1, "Options -c and -k are exclusive; -S requires -c, and -e requires Kissat.\n"); goto finish; }
    if ( argc-globalUtilOptind > 1 ) { Abc_Print(-1, "Expected at most one hexadecimal truth table.\n"); goto finish; }
    if ( argc > globalUtilOptind ) pHex = argv[globalUtilOptind];
    if ( pHex && pSym ) { Abc_Print(-1, "Choose either hex or -Y.\n"); goto finish; }
    if ( pSym )
    {
        n = (int)strlen(pSym)-1;
        if ( n < 0 || n > LUT2_MAX_VARS || (fN && p->nInputs != n) )
        { Abc_Print(-1, "-Y needs N+1 binary values, with N in 0..14.\n"); goto finish; }
        for ( i = 0; i <= n; ++i ) if ( pSym[i] != '0' && pSym[i] != '1' )
        { Abc_Print(-1, "-Y values must be 0 or 1.\n"); goto finish; }
        p->nInputs = n;
        pTruth = ABC_CALLOC(word, Abc_TtWordNum(n));
        for ( t = 0; t < (1 << n); ++t ) if ( pSym[Abc_TtCountOnes((word)t)] == '1' ) Abc_TtSetBit(pTruth, t);
        if ( n < 6 ) pTruth[0] = Abc_Tt6Stretch(pTruth[0], n);
    }
    else
    {
        if ( !Bmc_ExactRead(pAbc, pHex, fN ? p->nInputs : -1, LUT2_MAX_VARS, &Target) ) goto finish;
        p->nInputs = Target.nVars;
        pTruth = Target.pTruth;
    }
    Target.nVars = p->nInputs;
    Target.pTruth = pTruth;
    pTruth = ABC_ALLOC(word, Abc_TtWordNum(p->nInputs));
    Abc_TtCopy(pTruth, Target.pTruth, Abc_TtWordNum(p->nInputs), 0);
    for ( i = 0; i < p->nInputs; ++i ) Map[i] = i;
    nVars = Abc_TtMinBase(pTruth, Map, p->nInputs, p->nInputs);
    if ( nVars < 6 ) pTruth[0] = Abc_Tt6Stretch(pTruth[0], nVars);
    Lower = nVars <= 1 ? 0 : (nVars-2)/(p->nLutSize-1)+1;
    if ( !p->fSilent ) printf("Exact %s LUT synthesis: %d inputs, %d essential, K = %d (%s).\n",
        p->fCascade ? "cascade" : "general", p->nInputs, nVars, p->nLutSize, p->fCadical ? "CaDiCaL" : "Kissat");
    Bound = p->fMinimum ? Abc_MinInt(Lower, p->nNodes) : p->nNodes;
    for ( ; Bound <= p->nNodes; ++Bound )
    {
        Status = Bmc_Lut2Solve(p, pTruth, nVars, Map, Bound, &pGia);
        if ( Status == 10 )
        {
            if ( !Bmc_ExactInstall(pAbc, pGia, &Target) ) { Status = -1; break; }
            pGia = NULL;
        }
        if ( !Bmc_ExactContinue(Status, p->fMinimum, p->nSeconds, Bound, &FirstUnknown) ) break;
    }
    if ( p->fMinimum && !p->fSilent )
        Bmc_ExactReport(Status, FirstUnknown, nVars <= 1 ? 0 : nVars <= p->nLutSize ? 1 : Bound,
            p->nNodes, "LUT", p->fCascade ? " within cascades" : "");
    else if ( Status == 20 && !p->fSilent )
        printf("The problem has no solution within %d LUTs.\n", p->nNodes);
    Ret = Status < 0;

finish:
    if ( pGia ) Gia_ManStop(pGia);
    ABC_FREE(pTruth);
    ABC_FREE(Target.pTruth);
    return Ret;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
