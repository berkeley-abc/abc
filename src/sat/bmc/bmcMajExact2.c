/**CFile****************************************************************

  FileName    [bmcMajExact2.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based bounded model checking.]

  Synopsis    [Exact synthesis of positive majority-three networks.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 8, 2026.]

***********************************************************************/

#include "bmc.h"
#include "bmcExact.h"
#include "base/main/main.h"
#include "base/cmd/cmd.h"
#include "misc/extra/extra.h"
#include "misc/util/utilTruth.h"
#include "sat/kissat/kissat.h"
#include "sat/cadical/ccadical.h"
#include <errno.h>
#include <limits.h>
#include <math.h>

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define MAJ2_MAX_VARS  15
#define MAJ2_MAX_NODES 64
#define MAJ2_MAX_OBJS  (MAJ2_MAX_VARS + MAJ2_MAX_NODES + 2)
#define MAJ2_MAX_LITS  (3 * MAJ2_MAX_NODES)

typedef struct Bmc_Maj2Par_t_ Bmc_Maj2Par_t;
struct Bmc_Maj2Par_t_
{
    int nVars, nNodes, nSeconds, nConflicts, nSeed, Encoding, nProbeSeconds;
    int nInputs, fMajority, Map[MAJ2_MAX_VARS];
    word * pTruth;
    int fConst, fCascade, fMinimum, fCadical, fSymmetry, fVerbose, fProbe, fNoFastElim;
};

typedef struct Bmc_Maj2Man_t_ Bmc_Maj2Man_t;
struct Bmc_Maj2Man_t_
{
    Bmc_Maj2Par_t * pPars;
    int nBase, nVars, nPatterns, fStopped, fResource;
    int Select[MAJ2_MAX_NODES][MAJ2_MAX_OBJS];
    int Pins[MAJ2_MAX_NODES][3][MAJ2_MAX_OBJS];
    int Fans[MAJ2_MAX_NODES][3];
    word nClauses, nLiterals;
    abctime timeStop;
    kissat * pKissat;
    CCaDiCaL * pCadical;
};

#define MAJ2_REPLICAS 32
#define MAJ2_PROBE_WORDS 32
typedef struct Bmc_Maj2Net_t_ Bmc_Maj2Net_t;
struct Bmc_Maj2Net_t_
{
    int Fans[MAJ2_MAX_NODES][3], Energy;
    word Values[MAJ2_MAX_OBJS][MAJ2_PROBE_WORDS];
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Tests the per-query deadline, including CNF construction.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Maj2Stop( void * pData )
{
    Bmc_Maj2Man_t * p = (Bmc_Maj2Man_t *)pData;
    if ( p->timeStop && Abc_Clock() >= p->timeStop )
        p->fStopped = 1;
    return p->fStopped;
}

/**Function*************************************************************

  Synopsis    [Allocates a SAT variable; signed literals 1 and -1 are constants.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Maj2Var( Bmc_Maj2Man_t * p )
{
    if ( p->nVars >= 5000000 ) p->fResource = p->fStopped = 1;
    return ++p->nVars;
}

/**Function*************************************************************

  Synopsis    [Adds a simplified clause through the public solver interface.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Maj2Clause( Bmc_Maj2Man_t * p, const int * pLits, int nLits )
{
    int Lits[MAJ2_MAX_LITS], n = 0, i, j, Temp;
    assert( nLits <= MAJ2_MAX_LITS );
    if ( p->fStopped ) return;
    for ( i = 0; i < nLits; ++i )
    {
        if ( pLits[i] == 1 ) return;
        if ( pLits[i] == -1 ) continue;
        assert( pLits[i] != 0 );
        for ( j = 0; j < n; ++j )
        {
            if ( Lits[j] == -pLits[i] ) return;
            if ( Lits[j] == pLits[i] ) break;
        }
        if ( j == n ) Lits[n++] = pLits[i];
    }
    // Stable literal order also makes the independently generated CNF comparable.
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
    if ( (p->nClauses & 4095) == 0 ) Bmc_Maj2Stop(p);
}

/**Function*************************************************************

  Synopsis    [Adds clauses of up to four literals.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Maj2Unit( Bmc_Maj2Man_t * p, int a )
{
    Bmc_Maj2Clause(p, &a, 1);
}
static void Bmc_Maj2Binary( Bmc_Maj2Man_t * p, int a, int b )
{
    int Lits[2] = {a, b};
    Bmc_Maj2Clause(p, Lits, 2);
}
static void Bmc_Maj2Ternary( Bmc_Maj2Man_t * p, int a, int b, int c )
{
    int Lits[3] = {a, b, c};
    Bmc_Maj2Clause(p, Lits, 3);
}
static void Bmc_Maj2Quaternary( Bmc_Maj2Man_t * p, int a, int b, int c, int d )
{
    int Lits[4] = {a, b, c, d};
    Bmc_Maj2Clause(p, Lits, 4);
}

/**Function*************************************************************

  Synopsis    [Encodes conjunction with constant and equality simplification.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Maj2And( Bmc_Maj2Man_t * p, int a, int b )
{
    int y;
    if ( a == -1 || b == -1 ) return -1;
    if ( a == 1 ) return b;
    if ( b == 1 || a == b ) return a;
    y = Bmc_Maj2Var(p);
    Bmc_Maj2Binary(p, -y, a);
    Bmc_Maj2Binary(p, -y, b);
    Bmc_Maj2Ternary(p, y, -a, -b);
    return y;
}

/**Function*************************************************************

  Synopsis    [Builds fully equivalent prefix thresholds up to four.]

  Description [Result[j] means at least j selected literals are true.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Maj2Count( Bmc_Maj2Man_t * p, int * pLits, int nLits, int Limit, int * pResult )
{
    int Old[5] = {1, -1, -1, -1, -1}, New[5] = {1}, i, j, a, b, y;
    assert( Limit <= 4 );
    for ( i = 0; i < nLits; ++i )
    {
        for ( j = 1; j <= Limit; ++j )
        {
            a = Old[j]; b = Old[j-1];
            if ( a == 1 ) y = 1;
            else if ( a == -1 ) y = Bmc_Maj2And(p, pLits[i], b);
            else
            {
                y = Bmc_Maj2Var(p);
                Bmc_Maj2Binary(p, -a, y);
                Bmc_Maj2Ternary(p, -pLits[i], -b, y);
                Bmc_Maj2Ternary(p, -y, a, pLits[i]);
                Bmc_Maj2Ternary(p, -y, a, b);
            }
            New[j] = y;
        }
        memcpy(Old, New, sizeof(int) * (Limit + 1));
    }
    memcpy(pResult, Old, sizeof(int) * (Limit + 1));
}

/**Function*************************************************************

  Synopsis    [Enforces a lexicographic order using equality-prefix guards.]

  Description [A guard is required only while the preceding columns agree.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Maj2Lex( Bmc_Maj2Man_t * p, int * pA, int * pB, int nLits, int fStrict )
{
    int i, Equal = 1, Next;
    for ( i = 0; i < nLits; ++i )
    {
        Bmc_Maj2Ternary(p, -Equal, -pA[i], pB[i]);
        Next = i+1 < nLits ? Bmc_Maj2Var(p) : fStrict ? -1 : 1;
        Bmc_Maj2Quaternary(p, -Equal, pA[i], pB[i], Next);
        Bmc_Maj2Quaternary(p, -Equal, -pA[i], -pB[i], Next);
        Equal = Next;
    }
}

/**Function*************************************************************

  Synopsis    [Encodes distinct fanins, support, and structural symmetries.]

  Description [The first gate can use the first three PIs without constants.
               A lexicographically least sequence among all input renamings
               and topological orders has ordered input incidence columns
               and colexicographically ordered fanin sets. Duplicate gates
               and dangling gates are unnecessary in a minimum network.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Maj2Structure( Bmc_Maj2Man_t * p )
{
    Bmc_Maj2Par_t * q = p->pPars;
    int Lits[MAJ2_MAX_LITS], A[MAJ2_MAX_OBJS], B[MAJ2_MAX_OBJS], Counts[5];
    int i, j, k, l, n, a, b, Obj, Offset = q->fConst ? 2 : 0;
    for ( i = 0; i < q->nNodes && !Bmc_Maj2Stop(p); ++i )
    {
        Obj = p->nBase + i;
        if ( q->Encoding == 0 )
        {
            for ( k = 0; k < 3; ++k )
            {
                n = 0;
                for ( j = k; j < Obj-2+k; ++j )
                    Lits[n++] = p->Pins[i][k][j] = Bmc_Maj2Var(p);
                Bmc_Maj2Clause(p, Lits, n);
                for ( a = 0; a < n; ++a )
                for ( b = a+1; b < n; ++b )
                    Bmc_Maj2Binary(p, -Lits[a], -Lits[b]);
            }
            for ( k = 0; k < 2; ++k )
            for ( j = k; j < Obj-2+k; ++j )
            for ( l = k+1; l <= j; ++l )
                if ( p->Pins[i][k+1][l] )
                    Bmc_Maj2Binary(p, -p->Pins[i][k][j], -p->Pins[i][k+1][l]);
            for ( j = 0; j < Obj; ++j )
            {
                n = 1;
                Lits[0] = -(p->Select[i][j] = Bmc_Maj2Var(p));
                for ( k = 0; k < 3; ++k )
                    if ( p->Pins[i][k][j] ) Lits[n++] = p->Pins[i][k][j];
                Bmc_Maj2Clause(p, Lits, n);
                for ( k = 1; k < n; ++k )
                    Bmc_Maj2Binary(p, -Lits[0], -Lits[k]);
            }
        }
        else
        {
            for ( j = 0; j < Obj; ++j )
                p->Select[i][j] = Bmc_Maj2Var(p);
            Bmc_Maj2Count(p, p->Select[i], Obj, 4, Counts);
            Bmc_Maj2Unit(p, Counts[3]);
            Bmc_Maj2Unit(p, -Counts[4]);
        }
        if ( i == 0 && !q->fConst && q->fMajority )
            for ( j = 0; j < Obj; ++j )
                Bmc_Maj2Unit(p, j < 3 ? p->Select[i][j] : -p->Select[i][j]);
        if ( q->fConst ) Bmc_Maj2Binary(p, -p->Select[i][0], -p->Select[i][1]);
        if ( q->fCascade && i ) Bmc_Maj2Unit(p, p->Select[i][Obj-1]);
    }
    if ( p->fStopped ) return;
    for ( j = Offset; j < p->nBase + q->nNodes-1; ++j )
    {
        n = 0;
        for ( i = 0; i < q->nNodes; ++i )
            if ( j < p->nBase+i ) Lits[n++] = p->Select[i][j];
        Bmc_Maj2Clause(p, Lits, n);
    }
    if ( !q->fSymmetry ) return;
    for ( j = Offset; q->fMajority && j+1 < p->nBase; ++j )
    {
        for ( i = 0; i < q->nNodes; ++i )
        {
            A[i] = -p->Select[i][j]; B[i] = -p->Select[i][j+1];
        }
        Bmc_Maj2Lex(p, A, B, q->nNodes, 0);
    }
    for ( i = 0; i+1 < q->nNodes; ++i )
    {
        n = 0;
        for ( j = p->nBase+i; j >= 0; --j )
        {
            A[n] = j == p->nBase+i ? -1 : p->Select[i][j];
            B[n++] = p->Select[i+1][j];
        }
        Bmc_Maj2Lex(p, A, B, n, 1);
    }
}

/**Function*************************************************************

  Synopsis    [Encodes the target, using middle layers only for majority.]

  Description [Positive majority networks are monotone. Without constants,
               they are also self-dual, so the zero-valued middle layer
               determines the entire majority function. Constants require
               both middle layers. No assumption of symmetric internal
               functions is made. Other monotone targets use all rows;
               input-permutation constraints are disabled for these targets.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Maj2Function( Bmc_Maj2Man_t * p )
{
    Bmc_Maj2Par_t * q = p->pPars;
    int Values[MAJ2_MAX_OBJS], Lits[MAJ2_MAX_OBJS], Counts[5], Ins[3];
    int t, Weight, i, j, k, a, b, Out, Obj, Target, Offset = q->fConst ? 2 : 0;
    for ( t = 0; t < (1 << q->nVars) && !Bmc_Maj2Stop(p); ++t )
    {
        Weight = Abc_TtBitCount16(t);
        if ( q->fMajority && Weight != q->nVars/2 && !(q->fConst && Weight == q->nVars/2+1) ) continue;
        p->nPatterns++;
        Values[0] = -1; Values[1] = 1;
        for ( j = 0; j < q->nVars; ++j ) Values[Offset+j] = ((t >> j) & 1) ? 1 : -1;
        Target = Abc_TtGetBit(q->pTruth, t) ? 1 : -1;
        for ( i = 0; i < q->nNodes && !p->fStopped; ++i )
        {
            Obj = p->nBase+i;
            Out = i+1 == q->nNodes ? Target : Bmc_Maj2Var(p);
            if ( q->Encoding == 0 )
            {
                for ( k = 0; k < 3; ++k ) Ins[k] = Bmc_Maj2Var(p);
                for ( k = 0; k < 3; ++k )
                for ( j = k; j < Obj-2+k; ++j )
                {
                    Bmc_Maj2Ternary(p, -p->Pins[i][k][j], -Ins[k], Values[j]);
                    Bmc_Maj2Ternary(p, -p->Pins[i][k][j], Ins[k], -Values[j]);
                }
                for ( a = 0; a < 3; ++a )
                for ( b = a+1; b < 3; ++b )
                {
                    Bmc_Maj2Ternary(p, -Ins[a], -Ins[b], Out);
                    Bmc_Maj2Ternary(p, Ins[a], Ins[b], -Out);
                }
            }
            else if ( q->Encoding == 1 )
            {
                for ( a = 0; a < Obj; ++a )
                for ( b = a+1; b < Obj; ++b )
                {
                    int Clause[5] = {-p->Select[i][a], -p->Select[i][b], -Values[a], -Values[b], Out};
                    Bmc_Maj2Clause(p, Clause, 5);
                    Clause[2] = Values[a]; Clause[3] = Values[b]; Clause[4] = -Out;
                    Bmc_Maj2Clause(p, Clause, 5);
                }
            }
            else
            {
                for ( j = 0; j < Obj; ++j ) Lits[j] = Bmc_Maj2And(p, p->Select[i][j], Values[j]);
                Bmc_Maj2Count(p, Lits, Obj, 2, Counts);
                Bmc_Maj2Binary(p, -Out, Counts[2]);
                Bmc_Maj2Binary(p, Out, -Counts[2]);
            }
            Values[Obj] = Out;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Independently verifies every input assignment and builds an AIG.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Bmc_Maj2Verify( Bmc_Maj2Man_t * p, int fReadSat )
{
    Bmc_Maj2Par_t * q = p->pPars;
    Gia_Man_t * pGia, * pClean;
    int Values[MAJ2_MAX_OBJS], Levels[MAJ2_MAX_OBJS] = {0}, i, j, k, n, t;
    int Inputs[MAJ2_MAX_VARS], Offset = q->fConst ? 2 : 0;
    for ( i = 0; fReadSat && i < q->nNodes; ++i )
    {
        n = 0;
        for ( j = 0; j < p->nBase+i; ++j )
            if ( (p->pCadical ? ccadical_val(p->pCadical, p->Select[i][j]) : kissat_value(p->pKissat, p->Select[i][j])) > 0 )
            {
                if ( n == 3 ) return NULL;
                p->Fans[i][n++] = j;
            }
        if ( n != 3 ) return NULL;
    }
    for ( t = 0; t < (1 << q->nVars); ++t )
    {
        Values[0] = 0; Values[1] = 1;
        for ( j = 0; j < q->nVars; ++j ) Values[Offset+j] = (t >> j) & 1;
        for ( i = 0; i < q->nNodes; ++i )
            Values[p->nBase+i] = Values[p->Fans[i][0]] + Values[p->Fans[i][1]] + Values[p->Fans[i][2]] >= 2;
        if ( Values[p->nBase+q->nNodes-1] != Abc_TtGetBit(q->pTruth, t) ) return NULL;
    }
    pGia = Gia_ManStart(10 + q->nInputs + 3*q->nNodes);
    pGia->pName = Abc_UtilStrsav((char *)"majority");
    Gia_ManHashStart(pGia);
    Values[0] = 0; Values[1] = 1;
    for ( j = 0; j < q->nInputs; ++j ) Inputs[j] = Gia_ManAppendCi(pGia);
    for ( j = 0; j < q->nVars; ++j ) Values[Offset+j] = Inputs[q->Map[j]];
    for ( i = 0; i < q->nNodes; ++i )
    {
        Values[p->nBase+i] = Gia_ManHashMaj(pGia, Values[p->Fans[i][0]], Values[p->Fans[i][1]], Values[p->Fans[i][2]]);
        for ( k = 0; k < 3; ++k )
            Levels[p->nBase+i] = Abc_MaxInt(Levels[p->nBase+i], Levels[p->Fans[i][k]] + 1);
    }
    Gia_ManAppendCo(pGia, Values[p->nBase+q->nNodes-1]);
    Gia_ManHashStop(pGia);
    pClean = Gia_ManCleanup(pGia);
    Gia_ManStop(pGia);
    Abc_Print(1, "Realization of %d-input function using %d MAJ3 gates (%d levels):\n", q->nInputs, q->nNodes, Levels[p->nBase+q->nNodes-1]);
    for ( i = 0; i < q->nNodes; ++i )
    {
        Abc_Print(1, "%02d = MAJ(", q->nInputs+i);
        for ( k = 0; k < 3; ++k )
        {
            j = p->Fans[i][k];
            if ( j < Offset ) Abc_Print(1, " %d", j);
            else if ( j < p->nBase ) Abc_Print(1, " %c", 'a'+q->Map[j-Offset]);
            else Abc_Print(1, " %02d", q->nInputs+j-p->nBase);
        }
        Abc_Print(1, " )\n");
    }
    Abc_Print(1, "Verified all %d input assignments.\n", 1 << q->nVars);
    return pClean;
}

/**Function*************************************************************

  Synopsis    [Provides a local deterministic random stream for candidate search.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static unsigned Bmc_Maj2Random( word * pState )
{
    *pState ^= *pState << 13;
    *pState ^= *pState >> 7;
    *pState ^= *pState << 17;
    return (unsigned)(*pState >> 16);
}
static double Bmc_Maj2Uniform( word * pState )
{
    return ((double)Bmc_Maj2Random(pState) + 0.5) / 4294967296.0;
}

/**Function*************************************************************

  Synopsis    [Counts the live gates and optionally copies a compact candidate.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Maj2Live( Bmc_Maj2Net_t * pNet, int nInputs, int nNodes, Bmc_Maj2Man_t * pCopy )
{
    int Used[MAJ2_MAX_OBJS] = {0}, Map[MAJ2_MAX_OBJS];
    int Count = 0, i, k;
    Used[nInputs+nNodes-1] = 1;
    for ( i = nNodes-1; i >= 0; --i )
        if ( Used[nInputs+i] )
        {
            Count++;
            for ( k = 0; k < 3; ++k ) Used[pNet->Fans[i][k]] = 1;
        }
    if ( pCopy == NULL ) return Count;
    for ( i = 0; i < nInputs; ++i ) Map[i] = i;
    Count = 0;
    for ( i = 0; i < nNodes; ++i )
        if ( Used[nInputs+i] )
        {
            Map[nInputs+i] = nInputs+Count;
            for ( k = 0; k < 3; ++k ) pCopy->Fans[Count][k] = Map[pNet->Fans[i][k]];
            Count++;
        }
    pCopy->pPars->nNodes = Count;
    return Count;
}

/**Function*************************************************************

  Synopsis    [Finds candidate networks by bounded single-core tempering.]

  Description [Inspired by Haener, Steiger, and Katzgraber, "Parallel Tempering
               for Logic Synthesis", arXiv:2311.12394 (2023). Replicas are
               evaluated sequentially, with no threads. Extra temporary gates
               help cross search barriers; only a fully checked candidate at
               or below the requested count can be returned. Failure provides
               no lower bound and the complete SAT encoding follows.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Maj2Probe( Bmc_Maj2Man_t * p )
{
    Bmc_Maj2Par_t * q = p->pPars;
    Bmc_Maj2Net_t * Nets[MAJ2_REPLICAS] = {NULL}, * pNet, * pTemp;
    word Scratch[MAJ2_MAX_OBJS][MAJ2_PROBE_WORDS], Target[MAJ2_PROBE_WORDS] = {0};
    word State = ABC_CONST(0x0123456789abcdef) + (word)q->nSeed * ABC_CONST(0x9e3779b97f4a7c15);
    double Betas[MAJ2_REPLICAS], LogProb;
    abctime clk = Abc_Clock(), Stop;
    int nInputs = q->nVars, Limit = q->nNodes, nNodes = Abc_MinInt(Limit+4, MAJ2_MAX_NODES);
    int nPatterns, nWords, Round = 0, Best = INT_MAX, Found = 0;
    int i, j, k, w, t, r, a, b, c, x, Old, Energy, Delta;
    word av, bv, cv;
    unsigned char Changed[MAJ2_MAX_OBJS];
    if ( !q->nProbeSeconds || nInputs < 3 || nInputs > 11 || q->fConst || q->fCascade ) return 0;
    // With no constants, both the target and every candidate are self-dual.
    // Complementary assignments have equal errors. Keep one of each pair
    // and double its error count to preserve every acceptance decision.
    nPatterns = 1 << (nInputs-1);
    nWords = Abc_TtWordNum(nInputs-1);
    Abc_Print(1, "Searching for a candidate on one core before SAT...\n");
    Stop = clk + (abctime)q->nProbeSeconds * CLOCKS_PER_SEC;
    if ( p->timeStop && p->timeStop < Stop ) Stop = p->timeStop;
    if ( State == 0 ) State = 1;
    for ( t = 0; t < nPatterns; ++t )
        if ( Abc_TtGetBit(q->pTruth, t) ) Target[t >> 6] |= (word)1 << (t & 63);
    for ( r = 0; r < MAJ2_REPLICAS; ++r )
    {
        pNet = Nets[r] = ABC_CALLOC(Bmc_Maj2Net_t, 1);
        for ( t = 0; t < nPatterns; ++t )
            for ( i = 0; i < nInputs; ++i )
                if ( (t >> i) & 1 ) pNet->Values[i][t >> 6] |= (word)1 << (t & 63);
        for ( i = 0; i < nNodes; ++i )
        {
            for ( k = 0; k < 3; ++k )
            {
                do { x = Bmc_Maj2Random(&State) % (nInputs+i); }
                while ( (k > 0 && x == pNet->Fans[i][0]) || (k > 1 && x == pNet->Fans[i][1]) );
                pNet->Fans[i][k] = x;
            }
            for ( w = 0; w < nWords; ++w )
            {
                av = pNet->Values[pNet->Fans[i][0]][w];
                bv = pNet->Values[pNet->Fans[i][1]][w];
                cv = pNet->Values[pNet->Fans[i][2]][w];
                pNet->Values[nInputs+i][w] = (av & bv) | ((av | bv) & cv);
            }
        }
        for ( w = 0; w < nWords; ++w )
            pNet->Energy += Abc_TtCountOnes(pNet->Values[nInputs+nNodes-1][w] ^ Target[w]);
        pNet->Energy *= 2;
        if ( pNet->Energy == 0 ) pNet->Energy = Bmc_Maj2Live(pNet, nInputs, nNodes, NULL) - nNodes;
        Betas[r] = r ? 0.002 * pow(2000.0, (double)(r-1)/(MAJ2_REPLICAS-2)) : 0.0;
        if ( pNet->Energy <= 0 && nNodes+pNet->Energy <= Limit )
        {
            Bmc_Maj2Live(pNet, nInputs, nNodes, p);
            Found = 1;
            goto finish;
        }
    }
    while ( Abc_Clock() < Stop )
    {
        for ( r = 0; r < MAJ2_REPLICAS && Abc_Clock() < Stop; ++r )
        for ( t = 0; t < 15*nNodes; ++t )
        {
            pNet = Nets[r];
            i = Bmc_Maj2Random(&State) % nNodes;
            k = Bmc_Maj2Random(&State) % 3;
            do { x = Bmc_Maj2Random(&State) % (nInputs+i); }
            while ( x == pNet->Fans[i][(k+1)%3] || x == pNet->Fans[i][(k+2)%3] );
            Old = pNet->Fans[i][k];
            if ( x == Old ) continue;
            pNet->Fans[i][k] = x;
            // Earlier gates and gates outside this fanout cone retain
            // their saved values, including after a rejected mutation.
            memset(Changed, 0, sizeof(Changed));
            for ( j = i; j < nNodes; ++j )
            {
                a = pNet->Fans[j][0]; b = pNet->Fans[j][1]; c = pNet->Fans[j][2];
                if ( j != i && !Changed[a] && !Changed[b] && !Changed[c] ) continue;
                Changed[nInputs+j] = 1;
                for ( w = 0; w < nWords; ++w )
                {
                    av = Changed[a] ? Scratch[a][w] : pNet->Values[a][w];
                    bv = Changed[b] ? Scratch[b][w] : pNet->Values[b][w];
                    cv = Changed[c] ? Scratch[c][w] : pNet->Values[c][w];
                    Scratch[nInputs+j][w] = (av & bv) | ((av | bv) & cv);
                }
            }
            Energy = 0;
            for ( w = 0; w < nWords; ++w ) Energy += Abc_TtCountOnes((Changed[nInputs+nNodes-1] ? Scratch[nInputs+nNodes-1][w] : pNet->Values[nInputs+nNodes-1][w]) ^ Target[w]);
            Energy *= 2;
            if ( Energy == 0 ) Energy = Bmc_Maj2Live(pNet, nInputs, nNodes, NULL) - nNodes;
            Delta = Energy - pNet->Energy;
            if ( Delta <= 0 || Bmc_Maj2Uniform(&State) < exp(-Betas[r]*Delta) )
            {
                pNet->Energy = Energy;
                for ( j = i; j < nNodes; ++j ) if ( Changed[nInputs+j] ) memcpy(pNet->Values[nInputs+j], Scratch[nInputs+j], sizeof(word)*nWords);
                if ( Energy < Best )
                {
                    Best = Energy;
                    if ( q->fVerbose )
                        Abc_Print(1, "Candidate search: %s = %d.\n", Best > 0 ? "incorrect minterms" : "live gates", Best > 0 ? Best : nNodes+Best);
                }
                if ( Energy <= 0 && nNodes+Energy <= Limit )
                {
                    Bmc_Maj2Live(pNet, nInputs, nNodes, p);
                    Found = 1;
                    goto finish;
                }
            }
            else pNet->Fans[i][k] = Old;
        }
        for ( r = Round & 1; r+1 < MAJ2_REPLICAS; r += 2 )
        {
            LogProb = (Betas[r]-Betas[r+1]) * (Nets[r]->Energy-Nets[r+1]->Energy);
            if ( LogProb >= 0 || Bmc_Maj2Uniform(&State) < exp(LogProb) )
            {
                pTemp = Nets[r]; Nets[r] = Nets[r+1]; Nets[r+1] = pTemp;
            }
        }
        Round++;
    }
finish:
    for ( r = 0; r < MAJ2_REPLICAS; ++r ) ABC_FREE(Nets[r]);
    if ( q->fVerbose ) Abc_PrintTime(1, "Candidate search", Abc_Clock()-clk);
    return Found;
}

/**Function*************************************************************

  Synopsis    [Solves one gate count, distinguishing UNKNOWN from UNSAT.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Maj2Solve( Bmc_Maj2Par_t * q, Gia_Man_t ** ppGia )
{
    Bmc_Maj2Man_t * p = ABC_CALLOC(Bmc_Maj2Man_t, 1);
    abctime clk = Abc_Clock(), clkBuild;
    int Status = 0;
    *ppGia = NULL;
    p->pPars = q;
    p->nBase = q->nVars + (q->fConst ? 2 : 0);
    p->nVars = 1;
    p->timeStop = q->nSeconds ? clk + (abctime)q->nSeconds * CLOCKS_PER_SEC : 0;
    Abc_Print(1, "Running exact synthesis for %d-input function with at most %d MAJ3 gates (%s)...\n", q->nVars, q->nNodes, q->fCadical ? "CaDiCaL" : "Kissat");
    if ( q->fProbe && Bmc_Maj2Probe(p) )
    {
        *ppGia = Bmc_Maj2Verify(p, 0);
        Status = *ppGia ? 10 : -1;
        if ( Status < 0 ) Abc_Print(-1, "Candidate-network verification failed.\n");
        ABC_FREE(p);
        Abc_PrintTime(1, "Total runtime", Abc_Clock()-clk);
        return Status;
    }
    if ( q->fCadical )
    {
        p->pCadical = ccadical_init();
        ccadical_set_option(p->pCadical, "quiet", 1);
        ccadical_set_option(p->pCadical, "seed", q->nSeed);
        ccadical_set_terminate(p->pCadical, p, Bmc_Maj2Stop);
        if ( q->nConflicts ) ccadical_limit(p->pCadical, "conflicts", q->nConflicts);
        ccadical_add(p->pCadical, 1); ccadical_add(p->pCadical, 0);
    }
    else
    {
        p->pKissat = kissat_init();
        if ( q->fNoFastElim ) kissat_disable_fast_elimination(p->pKissat);
        kissat_set_terminate(p->pKissat, p, Bmc_Maj2Stop);
        if ( q->nConflicts ) kissat_set_conflict_limit(p->pKissat, (unsigned)q->nConflicts);
        kissat_add(p->pKissat, 1); kissat_add(p->pKissat, 0);
    }
    p->nClauses = p->nLiterals = 1;
    Bmc_Maj2Structure(p);
    Bmc_Maj2Function(p);
    clkBuild = Abc_Clock();
    if ( q->fVerbose )
    {
        Abc_Print(1, "CNF: %d variables, %.0f clauses, %d truth-table patterns.\n", p->nVars, (double)p->nClauses, p->nPatterns);
        Abc_PrintTime(1, "CNF construction", clkBuild-clk);
    }
    if ( !Bmc_Maj2Stop(p) )
        Status = p->pCadical ? ccadical_solve(p->pCadical) : kissat_solve(p->pKissat);
    if ( Status == 10 )
    {
        *ppGia = Bmc_Maj2Verify(p, 1);
        if ( *ppGia == NULL )
        {
            Abc_Print(-1, "Majority-network verification failed.\n");
            Status = -1;
        }
    }
    else if ( Status == 20 ) Abc_Print(1, "The problem has no solution.\n");
    else Abc_Print(1, "The result is UNKNOWN (%s limit).\n", p->fResource ? "CNF resource" : "search");
    if ( p->pCadical ) ccadical_release(p->pCadical);
    else kissat_release(p->pKissat);
    ABC_FREE(p);
    Abc_PrintTime(1, "Total runtime", Abc_Clock()-clk);
    return Status;
}

/**Function*************************************************************

  Synopsis    [Reads a nonnegative integer without silent truncation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Maj2ReadInt( int argc, char ** argv, int Option, int * pValue )
{
    char * pEnd;
    long Value;
    if ( globalUtilOptind >= argc ) goto fail;
    errno = 0;
    Value = strtol(argv[globalUtilOptind], &pEnd, 10);
    if ( errno || *pEnd || pEnd == argv[globalUtilOptind] || Value < 0 || Value > INT_MAX ) goto fail;
    globalUtilOptind++;
    *pValue = (int)Value;
    return 1;
fail:
    Abc_Print(-1, "Command line switch \"-%c\" requires an integer in [0, %d].\n", Option, INT_MAX);
    return 0;
}

/**Function*************************************************************

  Synopsis    [Implements the majexact2 command.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandMajExact2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Bmc_Maj2Par_t Pars, * p = &Pars;
    Gia_Man_t * pGia = NULL;
    Bmc_Exact_t Target = {0};
    int c, i, t, Count, Limit, Lower, Status = 0, fInputs = 0, fKissat = 0, FirstUnknown = -1;
    memset(p, 0, sizeof(Bmc_Maj2Par_t));
    p->nNodes = 1; p->fSymmetry = 1; p->nProbeSeconds = 120;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "INTSCEPBfmrckqevuh")) != EOF )
    {
        switch ( c )
        {
        case 'I': if ( !Bmc_Maj2ReadInt(argc, argv, c, &p->nVars) ) return 1; fInputs = 1; break;
        case 'N': if ( !Bmc_Maj2ReadInt(argc, argv, c, &p->nNodes) ) return 1; break;
        case 'T': if ( !Bmc_Maj2ReadInt(argc, argv, c, &p->nSeconds) ) return 1; break;
        case 'S': if ( !Bmc_Maj2ReadInt(argc, argv, c, &p->nSeed) ) return 1; break;
        case 'C': if ( !Bmc_Maj2ReadInt(argc, argv, c, &p->nConflicts) ) return 1; break;
        case 'E': if ( !Bmc_Maj2ReadInt(argc, argv, c, &p->Encoding) ) return 1; break;
        case 'B': case 'P': if ( !Bmc_Maj2ReadInt(argc, argv, c, &p->nProbeSeconds) ) return 1; break;
        case 'f': p->fConst ^= 1; break;
        case 'm': p->fMinimum ^= 1; break;
        case 'r': p->fCascade ^= 1; break;
        case 'c': p->fCadical ^= 1; break;
        case 'k': fKissat ^= 1; break;
        case 'v': p->fVerbose ^= 1; break;
        case 'q': p->fProbe ^= 1; break;
        case 'e': p->fNoFastElim ^= 1; break;
        case 'u': p->fSymmetry ^= 1; break;
        default: goto usage;
        }
    }
    if ( argc > globalUtilOptind+1 ) goto usage;
    if ( p->nVars > MAJ2_MAX_VARS ||
         p->nNodes > MAJ2_MAX_NODES || p->Encoding > 2 )
    {
        Abc_Print(-1, "Expected I in [0, %d], N in [0, %d], and E in [0, 2].\n", MAJ2_MAX_VARS, MAJ2_MAX_NODES);
        return 1;
    }
    if ( p->fCadical && fKissat )
    {
        Abc_Print(-1, "Options -c and -k cannot be combined.\n");
        return 1;
    }
    if ( p->nSeed > 2000000000 )
    {
        Abc_Print(-1, "The random seed must be in 0..2000000000.\n");
        return 1;
    }
    if ( p->fCadical && p->fNoFastElim )
    {
        Abc_Print(-1, "Option -e requires Kissat.\n");
        return 1;
    }
    if ( p->nSeed && !p->fCadical && !p->fProbe )
    {
        Abc_Print(-1, "The seed option requires -c or -q; this build of Kissat has fixed options.\n");
        return 1;
    }
    if ( !Bmc_ExactRead(pAbc, argc > globalUtilOptind ? argv[globalUtilOptind] : NULL,
            fInputs ? p->nVars : -1, MAJ2_MAX_VARS, &Target) ) return 1;
    p->nInputs = Target.nVars;
    p->pTruth = ABC_ALLOC(word, Abc_TtWordNum(p->nInputs));
    Abc_TtCopy(p->pTruth, Target.pTruth, Abc_TtWordNum(p->nInputs), 0);
    for ( i = 0; i < p->nInputs; ++i ) p->Map[i] = i;
    p->nVars = Abc_TtMinBase(p->pTruth, p->Map, p->nInputs, p->nInputs);
    if ( p->nVars < 6 ) p->pTruth[0] = Abc_Tt6Stretch(p->pTruth[0], p->nVars);
    // Positive MAJ3 gates cannot implement nonmonotone functions.
    for ( t = 0; t < (1 << p->nVars); ++t )
    for ( i = 0; i < p->nVars; ++i )
        if ( !((t >> i) & 1) && Abc_TtGetBit(p->pTruth, t) && !Abc_TtGetBit(p->pTruth, t | (1 << i)) )
        {
            Abc_Print(1, "No solution: positive MAJ3 gates require a monotone target.\n");
            goto finish;
        }
    if ( p->nVars < 2 )
    {
        int Out = (int)(p->pTruth[0] & 1);
        pGia = Gia_ManStart(p->nInputs+2);
        pGia->pName = Abc_UtilStrsav((char *)"majexact2");
        for ( i = 0; i < p->nInputs; ++i )
        {
            int Lit = Gia_ManAppendCi(pGia);
            if ( p->nVars && i == p->Map[0] ) Out = Lit;
        }
        Gia_ManAppendCo(pGia, Out);
        Abc_Print(1, "%sMAJ3 count = 0.\n", p->fMinimum ? "Minimum " : "");
        Status = 10;
        goto finish;
    }
    if ( !p->fConst )
        for ( t = 0; t < (1 << (p->nVars-1)); ++t )
            if ( Abc_TtGetBit(p->pTruth, t) == Abc_TtGetBit(p->pTruth, ((1 << p->nVars)-1) ^ t) )
            {
                Abc_Print(1, "No solution: MAJ3 gates without constant fanins require a self-dual target; use -f to allow constants.\n");
                goto finish;
            }
    p->fMajority = p->nVars & 1;
    for ( t = 0; t < (1 << p->nVars) && p->fMajority; ++t )
        if ( Abc_TtGetBit(p->pTruth, t) != (Abc_TtBitCount16(t) > p->nVars/2) ) p->fMajority = 0;
    // A connected ternary network with M gates has at most 2*M+1 distinct PIs.
    Lower = p->nVars/2;
    Limit = p->nNodes;
    if ( Limit < Lower )
    {
        Abc_Print(1, "The problem has no solution (input coverage requires at least %d gates).\n", Lower);
        goto finish;
    }
    for ( Count = p->fMinimum ? Lower : Limit; Count <= Limit; ++Count )
    {
        p->nNodes = Count;
        if ( p->fMinimum ) Abc_Print(1, "\nTrying N = %d:\n", Count);
        Status = Bmc_Maj2Solve(p, &pGia);
        if ( !Bmc_ExactContinue(Status, p->fMinimum, p->nSeconds, Count, &FirstUnknown) ) break;
    }
    if ( p->fMinimum )
        Bmc_ExactReport(Status, FirstUnknown, p->nNodes, Limit, "MAJ3", p->fCascade ? " within cascades" : "");
finish:
    if ( pGia && Bmc_ExactInstall(pAbc, pGia, &Target) ) pGia = NULL;
    else if ( pGia ) Status = -1;
    if ( pGia ) Gia_ManStop(pGia);
    ABC_FREE(p->pTruth);
    ABC_FREE(Target.pTruth);
    return Status < 0;

usage:
    Abc_Print(-2, "usage: majexact2 [-INTSCEBP <num>] [-fmrckqevuh] [hex]\n");
    Abc_Print(-2, "\t           exact synthesis of monotone functions using positive MAJ3 gates\n");
    Abc_Print(-2, "\t           uses Kissat by default; -c and -k are mutually exclusive\n");
    Abc_Print(-2, "\t-I <num> : number of input variables, 0..15 [default = infer from hex/network]\n");
    Abc_Print(-2, "\t-N <num> : gate bound, 0..64 [default = 1]\n");
    Abc_Print(-2, "\t-T <num> : runtime limit per count in seconds, 0 = unlimited [default = 0]\n");
    Abc_Print(-2, "\t-C <num> : conflict limit per count, 0 = unlimited [default = 0]\n");
    Abc_Print(-2, "\t-S <num> : candidate/CaDiCaL random seed, 0..2000000000 [default = 0]\n");
    Abc_Print(-2, "\t           a nonzero seed requires -q/-c; Kissat has fixed internal options\n");
    Abc_Print(-2, "\t-E <num> : encoding: 0 = pins, 1 = pairs, 2 = counters [default = 0]\n");
    Abc_Print(-2, "\t-B <num> : candidate seconds per count with -q; 0 disables [default = 120]\n");
    Abc_Print(-2, "\t-P <num> : alias for -B, retained for existing scripts\n");
    Abc_Print(-2, "\t-f       : toggle using constant fanins [default = no]\n");
    Abc_Print(-2, "\t-m       : toggle minimum search through N; -T skips UNKNOWN [default = no]\n");
    Abc_Print(-2, "\t-r       : toggle restricting the network to a cascade [default = no]\n");
    Abc_Print(-2, "\t           fanin 0 is the previous gate; other fanins may use earlier gates\n");
    Abc_Print(-2, "\t-c       : toggle using CaDiCaL instead of Kissat [default = no]\n");
    Abc_Print(-2, "\t-k       : toggle explicit Kissat selection [default = no]\n");
    Abc_Print(-2, "\t-e       : toggle skipping initial Kissat elimination [default = no]\n");
    Abc_Print(-2, "\t-q       : toggle bounded candidate search before SAT [default = no]\n");
    Abc_Print(-2, "\t           applies to I <= 11 without -f/-r; failure falls back to SAT\n");
    Abc_Print(-2, "\t-u       : toggle input and node symmetry breaking [default = yes]\n");
    Abc_Print(-2, "\t-v       : toggle verbose printout [default = no]\n");
    Abc_Print(-2, "\t-h       : print the command usage\n");
    Abc_Print(-2, "\t           SAT results replace the current network; &-space is unchanged.\n");
    Abc_Print(-2, "\t[hex]    : truth table; without hex, uses the current single-output network\n");
    Abc_Print(-2, "\t           removes inessential inputs; constants and positive literals need zero gates\n");
    Abc_Print(-2, "\t           without -f, a nonconstant target must be self-dual\n");
    Abc_Print(-2, "\tExample: majexact2 -N 1 E8\n");
    return 1;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
