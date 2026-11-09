/**CFile****************************************************************

  FileName    [bmcTwo.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based bounded model checking.]

  Synopsis    [Exact synthesis with two-input gates.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 1, 2017.]

  Revision    [$Id: bmcMaj.c,v 1.00 2017/10/01 00:00:00 alanmi Exp $]

***********************************************************************/

#include "bmc.h"
#include "bmcExact.h"
#include "base/main/main.h"
#include "misc/extra/extra.h"
#include "misc/util/utilTruth.h"
#include "sat/bsat/satSolver.h"
#include "sat/kissat/kissat.h"
#include "sat/cadical/ccadical.h"
#include <errno.h>
#include <limits.h>

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define TWO_MAX_VARS  12
#define TWO_MAX_NODES 64
#define TWO_MAX_OBJS  (TWO_MAX_VARS + TWO_MAX_NODES)

typedef struct Bmc_TwoMan_t_ Bmc_TwoMan_t;
struct Bmc_TwoMan_t_
{
    int               fBoost;     // optional redundant constraints
    int               fPreRows, fCofRows, fCofAdded, fDiffAdded;
    int               RowVars[32][TWO_MAX_NODES][3]; // shared values for small functions
    Bmc_EsPar_t *      pPars;      // parameters
    int               nVars;      // essential inputs
    int               nNodes;     // internal nodes
    int               nObjs;      // inputs and internal nodes
    int               nWords;     // truth table words
    int               iVar;       // last allocated DIMACS variable
    int               nClauses;   // emitted clauses
    int               nLiterals;  // emitted literals
    int               fCompl;     // output complement
    int               fUnsat;     // bsat rejected a clause
    word *            pTruth;     // normalized truth table
    Vec_Wrd_t *       vInfo;      // simulation tables
    Vec_Int_t *       vCnf;       // optional DIMACS copy
    Vec_Wec_t *       vOutLits;   // uses of each object
    int               VarMarks[TWO_MAX_OBJS][2][TWO_MAX_OBJS];
    int               Funcs[TWO_MAX_NODES][3];
    int               Fans[TWO_MAX_NODES][2];
    int               Truths[TWO_MAX_NODES];
    int               Map[TWO_MAX_VARS];
    sat_solver *      pSat;
    kissat *          pKissat;
    CCaDiCaL *        pCadical;
    abctime           timeStop;   // zero means unlimited
};

typedef struct Bmc_TwoSeedGate_t_
{
    int a, b, f;
} Bmc_TwoSeedGate_t;
typedef struct Bmc_TwoSeedState_t_
{
    Bmc_TwoSeedGate_t Gates[TWO_MAX_NODES];
    word Active;                // gates used by the best output pair
    int a, b, f, Cost;           // output pair, function, and wrong rows
} Bmc_TwoSeedState_t;


static inline word * Bmc_TwoTruth( Bmc_TwoMan_t * p, int i ) { return Vec_WrdEntryP(p->vInfo, p->nWords*i); }
static inline int Bmc_TwoNewVar( Bmc_TwoMan_t * p ) { return ++p->iVar; }
static inline int Bmc_TwoValue( Bmc_TwoMan_t * p, int v ) { return p->pSat ? sat_solver_var_value(p->pSat, v-1) : (p->pCadical ? ccadical_val(p->pCadical, v) : kissat_value(p->pKissat, v)) > 0; }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Checks the time limit shared by construction and solving.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_TwoTerminate( void * pState )
{
    Bmc_TwoMan_t * p = (Bmc_TwoMan_t *)pState;
    return p->timeStop && (abctime)clock() >= p->timeStop;
}

/**Function*************************************************************

  Synopsis    [Emits a DIMACS clause to the selected bundled solver.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_TwoEmit( Bmc_TwoMan_t * p, int * pLits, int nLits )
{
    int i;
    if ( p->pSat && !p->fUnsat )
    {
        lit Lits[2*TWO_MAX_OBJS];
        assert( nLits <= 2*TWO_MAX_OBJS );
        for ( i = 0; i < nLits; i++ ) Lits[i] = toLitCond(abs(pLits[i])-1, pLits[i] < 0);
        // bsat rejects empty clauses and does not remember failed additions.
        p->fUnsat = !nLits || !sat_solver_addclause(p->pSat, Lits, Lits+nLits);
    }
    for ( i = 0; i < nLits; i++ )
    {
        if ( p->pCadical ) ccadical_add(p->pCadical, pLits[i]);
        else if ( p->pKissat ) kissat_add(p->pKissat, pLits[i]);
        if ( p->vCnf ) Vec_IntPush(p->vCnf, pLits[i]);
    }
    if ( p->pCadical ) ccadical_add(p->pCadical, 0);
    else if ( p->pKissat ) kissat_add(p->pKissat, 0);
    if ( p->vCnf ) Vec_IntPush(p->vCnf, 0);
    p->nClauses++;
    p->nLiterals += nLits;
}

/**Function*************************************************************

  Synopsis    [Simplifies constants and repeated literals before emission.]

  Description [DIMACS variable 1 is true; literal -1 is false.]

  SideEffects [Compacts the caller's literal array in place.]

  SeeAlso     []

***********************************************************************/
static void Bmc_TwoClause( Bmc_TwoMan_t * p, int * pLits, int nLits )
{
    int i, j, n = 0;
    for ( i = 0; i < nLits; i++ )
    {
        int Lit = pLits[i];
        if ( Lit == 1 ) return;
        if ( Lit == -1 ) continue;
        assert( Lit && abs(Lit) <= p->iVar );
        for ( j = 0; j < n; j++ )
        {
            if ( pLits[j] == -Lit ) return;
            if ( pLits[j] == Lit ) break;
        }
        if ( j == n ) pLits[n++] = Lit;
    }
    Bmc_TwoEmit(p, pLits, n);
}
static inline void Bmc_TwoClause2( Bmc_TwoMan_t * p, int a, int b )
{
    int Lits[2]; Lits[0] = a; Lits[1] = b;
    Bmc_TwoClause(p, Lits, 2);
}
static inline void Bmc_TwoClause3( Bmc_TwoMan_t * p, int a, int b, int c )
{
    int Lits[3]; Lits[0] = a; Lits[1] = b; Lits[2] = c;
    Bmc_TwoClause(p, Lits, 3);
}
static inline void Bmc_TwoClause4( Bmc_TwoMan_t * p, int a, int b, int c, int d )
{
    int Lits[4]; Lits[0] = a; Lits[1] = b; Lits[2] = c; Lits[3] = d;
    Bmc_TwoClause(p, Lits, 4);
}

/**Function*************************************************************

  Synopsis    [Requires exactly one positive literal to hold.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_TwoOneHot( Bmc_TwoMan_t * p, int * pLits, int nLits )
{
    int i, j;
    Bmc_TwoClause(p, pLits, nLits);
    for ( i = 0; i < nLits; i++ )
    for ( j = i+1; j < nLits; j++ )
        Bmc_TwoClause2(p, -pLits[i], -pLits[j]);
}

/**Function*************************************************************

  Synopsis    [Duplicates the positional connectivity encoding of twoexact.]

  Description [Gate functions are normalized to zero at the all-zero input.
               Complementing internal signals and absorbing their phases into
               fanout functions preserves every circuit in either gate library.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_TwoMarkup( Bmc_TwoMan_t * p )
{
    int i, j, k;
    p->iVar = 1;
    Bmc_TwoEmit(p, &p->iVar, 1);
    for ( i = 0; i < p->nNodes; i++ )
        for ( k = 0; k < 3; k++ )
            p->Funcs[i][k] = Bmc_TwoNewVar(p);
    for ( i = p->nVars; i < p->nObjs; i++ )
    for ( k = 0; k < 2; k++ )
    for ( j = 1-k; j < i-k; j++ )
    {
        if ( i == p->nObjs-1 && k == 0 && j != i-1 ) continue;
        p->VarMarks[i][k][j] = Bmc_TwoNewVar(p);
        Vec_WecPush(p->vOutLits, j, p->iVar);
    }
}

/**Function*************************************************************

  Synopsis    [Finds a first-gate representative under input automorphisms.]

  Description [Only verified swaps and input phases preserving the truth table
               up to output complementation are used. A transformed circuit
               has the same gate count in both supported gate libraries.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_TwoRoot( int * pRoots, int i )
{
    while ( pRoots[i] != i ) i = pRoots[i] = pRoots[pRoots[i]];
    return i;
}
static void Bmc_TwoSymmetrySimple( Bmc_TwoMan_t * p )
{
    static const int Truths[5] = { 2, 4, 8, 14, 6 };
    int Roots[5*TWO_MAX_VARS*(TWO_MAX_VARS-1)/2];
    int i, j, a, b, k, t, x, y, z, r0, r1, Lits[5];
    int nPairs = p->nVars*(p->nVars-1)/2;
    word * pCopy = ABC_ALLOC(word, p->nWords);
    for ( i = 0; i < 5*nPairs; i++ ) Roots[i] = i;
    for ( i = 0; i < p->nVars; i++ )
    for ( j = i; j < p->nVars; j++ )
    {
        Abc_TtCopy(pCopy, p->pTruth, p->nWords, 0);
        if ( i == j ) Abc_TtFlip(pCopy, p->nWords, i);
        else          Abc_TtSwapVars(pCopy, p->nVars, i, j);
        if ( pCopy[0] & 1 ) Abc_TtNot(pCopy, p->nWords);
        if ( !Abc_TtEqual(pCopy, p->pTruth, p->nWords) ) continue;
        for ( a = 1; a < p->nVars; a++ )
        for ( b = 0; b < a; b++ )
        for ( k = 0; k < 5; k++ )
        {
            t = Truths[k]; x = a; y = b;
            if ( i == j )
            {
                if ( a == i ) t = ((t & 5) << 1) | ((t & 10) >> 1);
                if ( b == i ) t = ((t & 3) << 2) | ((t & 12) >> 2);
                if ( t & 1 ) t ^= 15;
            }
            else
            {
                x = a == i ? j : a == j ? i : a;
                y = b == i ? j : b == j ? i : b;
                if ( x < y )
                {
                    z = x; x = y; y = z;
                    t = (t & 9) | ((t & 2) << 1) | ((t & 4) >> 1);
                }
            }
            for ( z = 0; z < 5 && Truths[z] != t; z++ ) {}
            assert( z < 5 );
            r0 = Bmc_TwoRoot(Roots, 5*(a*(a-1)/2+b)+k);
            r1 = Bmc_TwoRoot(Roots, 5*(x*(x-1)/2+y)+z);
            Roots[Abc_MaxInt(r0, r1)] = Abc_MinInt(r0, r1);
        }
    }
    for ( a = 1; a < p->nVars; a++ )
    for ( b = 0; b < a; b++ )
    for ( k = 0; k < 5-p->pPars->fOnlyAnd; k++ )
    {
        i = 5*(a*(a-1)/2+b)+k;
        if ( Bmc_TwoRoot(Roots, i) == i ) continue;
        if ( !p->VarMarks[p->nVars][0][a] || !p->VarMarks[p->nVars][1][b] ) continue;
        Lits[0] = -p->VarMarks[p->nVars][0][a];
        Lits[1] = -p->VarMarks[p->nVars][1][b];
        for ( j = 0; j < 3; j++ ) Lits[j+2] = (Truths[k] >> (j+1)) & 1 ? -p->Funcs[0][j] : p->Funcs[0][j];
        Bmc_TwoClause(p, Lits, 5);
    }
    ABC_FREE(pCopy);
}

/**Function*************************************************************

  Synopsis    [Collects first-gate orbits under signed input automorphisms.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_TwoSymPerm( Bmc_TwoMan_t * p, int * pRoots, int * pPerm, unsigned Used, int Level )
{
    static const int Truths[5] = { 2, 4, 8, 14, 6 };
    int Mapped[64], nMints = 1 << p->nVars;
    int i, Phase, Mint, Compl, a, b, k, t, x, y, z, r0, r1;
    if ( Level < p->nVars )
    {
        for ( i = 0; i < p->nVars; i++ ) if ( !(Used & (1u << i)) )
        {
            pPerm[Level] = i;
            Bmc_TwoSymPerm(p, pRoots, pPerm, Used | (1u << i), Level+1);
        }
        return;
    }
    for ( Mint = 0; Mint < nMints; Mint++ )
    {
        Mapped[Mint] = 0;
        for ( i = 0; i < p->nVars; i++ ) Mapped[Mint] |= ((Mint >> pPerm[i]) & 1) << i;
    }
    for ( Phase = 0; Phase < nMints; Phase++ )
    {
        Compl = Abc_TtGetBit(p->pTruth, Phase);
        for ( Mint = 1; Mint < nMints; Mint++ )
            if ( (Abc_TtGetBit(p->pTruth, Mapped[Mint] ^ Phase) ^ Compl) != Abc_TtGetBit(p->pTruth, Mint) ) break;
        if ( Mint < nMints ) continue;
        for ( a = 1; a < p->nVars; a++ )
        for ( b = 0; b < a; b++ )
        for ( k = 0; k < 5; k++ )
        {
            t = Truths[k]; x = pPerm[a]; y = pPerm[b];
            if ( (Phase >> a) & 1 ) t = ((t & 5) << 1) | ((t & 10) >> 1);
            if ( (Phase >> b) & 1 ) t = ((t & 3) << 2) | ((t & 12) >> 2);
            if ( t & 1 ) t ^= 15;
            if ( x < y )
            {
                z = x; x = y; y = z;
                t = (t & 9) | ((t & 2) << 1) | ((t & 4) >> 1);
            }
            for ( z = 0; z < 5 && Truths[z] != t; z++ ) {}
            assert( z < 5 );
            r0 = Bmc_TwoRoot(pRoots, 5*(a*(a-1)/2+b)+k);
            r1 = Bmc_TwoRoot(pRoots, 5*(x*(x-1)/2+y)+z);
            pRoots[Abc_MaxInt(r0, r1)] = Abc_MinInt(r0, r1);
        }
    }
}

/**Function*************************************************************

  Synopsis    [Keeps one representative of each symmetric first gate.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_TwoSymmetry( Bmc_TwoMan_t * p )
{
    static const int Truths[5] = { 2, 4, 8, 14, 6 };
    int Roots[75], Perm[6], Lits[5], i, j, a, b, k;
    if ( !p->fBoost || p->nVars != 4 ) { Bmc_TwoSymmetrySimple(p); return; }
    for ( i = 0; i < 5*p->nVars*(p->nVars-1)/2; i++ ) Roots[i] = i;
    Bmc_TwoSymPerm(p, Roots, Perm, 0, 0);
    for ( a = 1; a < p->nVars; a++ )
    for ( b = 0; b < a; b++ )
    for ( k = 0; k < 5-p->pPars->fOnlyAnd; k++ )
    {
        i = 5*(a*(a-1)/2+b)+k;
        if ( Bmc_TwoRoot(Roots, i) == i ) continue;
        if ( !p->VarMarks[p->nVars][0][a] || !p->VarMarks[p->nVars][1][b] ) continue;
        Lits[0] = -p->VarMarks[p->nVars][0][a];
        Lits[1] = -p->VarMarks[p->nVars][1][b];
        for ( j = 0; j < 3; j++ ) Lits[j+2] = (Truths[k] >> (j+1)) & 1 ? -p->Funcs[0][j] : p->Funcs[0][j];
        Bmc_TwoClause(p, Lits, 5);
    }
}

/**Function*************************************************************

  Synopsis    [Constrains connectivity, gate functions, and node symmetries.]

  Description [Constants and projection gates are omitted; they need no node.
               No-reapplication pruning is used only during minimum search,
               where redundant gates are unnecessary.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_TwoStart( Bmc_TwoMan_t * p )
{
    int Lits[2*TWO_MAX_OBJS], i, j, k, h, n;
    for ( i = p->nVars; i < p->nObjs; i++ )
    {
        int * f = p->Funcs[i-p->nVars];
        if ( Bmc_TwoTerminate(p) ) return 0;
        for ( k = 0; k < 2; k++ )
        {
            n = 0;
            for ( j = 0; j < i; j++ )
                if ( p->VarMarks[i][k][j] ) Lits[n++] = p->VarMarks[i][k][j];
            Bmc_TwoOneHot(p, Lits, n);
        }
        for ( j = 0; j < i; j++ ) if ( p->VarMarks[i][0][j] )
        for ( k = j; k < i; k++ ) if ( p->VarMarks[i][1][k] )
            Bmc_TwoClause2(p, -p->VarMarks[i][0][j], -p->VarMarks[i][1][k]);
        Bmc_TwoClause3(p, f[0], f[1], f[2]);
        Bmc_TwoClause3(p, -f[0], f[1], -f[2]);
        Bmc_TwoClause3(p, f[0], -f[1], -f[2]);
        if ( p->pPars->fOnlyAnd ) Bmc_TwoClause3(p, -f[0], -f[1], f[2]);
        // Order nodes by their higher-numbered fanin to remove node permutations.
        if ( i > p->nVars )
        {
            for ( j = 0; j < i; j++ ) if ( p->VarMarks[i][0][j] )
            for ( k = j+1; k < i-1; k++ ) if ( p->VarMarks[i-1][0][k] )
                Bmc_TwoClause2(p, -p->VarMarks[i][0][j], -p->VarMarks[i-1][0][k]);
        }
        if ( p->pPars->fMinNodes )
        for ( j = p->nVars; j < i; j++ ) if ( p->VarMarks[i][0][j] )
        for ( k = 0; k < j; k++ ) if ( p->VarMarks[i][1][k] )
        for ( h = 0; h < 2; h++ ) if ( p->VarMarks[j][h][k] )
            Bmc_TwoClause3(p, -p->VarMarks[i][0][j], -p->VarMarks[i][1][k], -p->VarMarks[j][h][k]);
    }
    for ( i = 0; i < p->nObjs-1; i++ )
    {
        Vec_Int_t * vLits = Vec_WecEntry(p->vOutLits, i);
        Bmc_TwoClause(p, Vec_IntArray(vLits), Vec_IntSize(vLits));
    }
    Bmc_TwoSymmetry(p);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Encodes one complete input assignment.]

  Description [The all-zero assignment is implicit in normalized functions.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_TwoRow( Bmc_TwoMan_t * p, int Mint )
{
    int Values[TWO_MAX_OBJS], i, j, k, a, b, y, f, * g;
    for ( i = 0; i < p->nVars; i++ ) Values[i] = (Mint >> i) & 1 ? 1 : -1;
    for ( i = p->nVars; i < p->nObjs; i++ )
    {
        a = p->fPreRows || p->fCofRows ? p->RowVars[Mint][i-p->nVars][0] : Bmc_TwoNewVar(p);
        b = p->fPreRows || p->fCofRows ? p->RowVars[Mint][i-p->nVars][1] : Bmc_TwoNewVar(p);
        y = Values[i] = i == p->nObjs-1 ? (Abc_TtGetBit(p->pTruth, Mint) ? 1 : -1) : (p->fPreRows || p->fCofRows ? p->RowVars[Mint][i-p->nVars][2] : Bmc_TwoNewVar(p));
        for ( k = 0; k < 2; k++ )
        for ( j = 0; j < i; j++ ) if ( p->VarMarks[i][k][j] )
        {
            Bmc_TwoClause3(p, -p->VarMarks[i][k][j], k ? -b : -a, Values[j]);
            Bmc_TwoClause3(p, -p->VarMarks[i][k][j], k ? b : a, -Values[j]);
        }
        g = p->Funcs[i-p->nVars];
        for ( k = 0; k < 4; k++ )
        {
            f = k ? g[k-1] : -1;
            Bmc_TwoClause4(p, (k&1) ? -a : a, (k&2) ? -b : b, -y, f);
            Bmc_TwoClause4(p, (k&1) ? -a : a, (k&2) ? -b : b, y, -f);
        }
    }
}

/**Function*************************************************************

  Synopsis    [Decodes the model and returns its first failing truth-table row.]

  Description [Returns -1 for a match, -2 for an invalid model.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_TwoEval( Bmc_TwoMan_t * p )
{
    int i, j, k, n, Count;
    for ( i = 0; i < p->nVars; i++ ) Abc_TtIthVar(Bmc_TwoTruth(p, i), i, p->nVars);
    for ( i = p->nVars; i < p->nObjs; i++ )
    {
        n = i-p->nVars;
        for ( k = 0; k < 2; k++ )
        {
            Count = 0;
            for ( j = 0; j < i; j++ )
                if ( p->VarMarks[i][k][j] && Bmc_TwoValue(p, p->VarMarks[i][k][j]) )
                    p->Fans[n][k] = j, Count++;
            if ( Count != 1 ) return -2;
        }
        if ( p->Fans[n][0] <= p->Fans[n][1] ) return -2;
        p->Truths[n] = 0;
        for ( k = 0; k < 3; k++ )
            p->Truths[n] |= Bmc_TwoValue(p, p->Funcs[n][k]) << (k+1);
        if ( p->Truths[n] != 2 && p->Truths[n] != 4 && p->Truths[n] != 8 &&
             p->Truths[n] != 14 && (p->pPars->fOnlyAnd || p->Truths[n] != 6) ) return -2;
        Abc_TtClear(Bmc_TwoTruth(p, i), p->nWords);
        for ( k = 1; k < 4; k++ ) if ( (p->Truths[n] >> k) & 1 )
        {
            Abc_TtAndCompl(Bmc_TwoTruth(p, p->nObjs), Bmc_TwoTruth(p, p->Fans[n][0]), !(k&1),
                          Bmc_TwoTruth(p, p->Fans[n][1]), !(k&2), p->nWords);
            Abc_TtOr(Bmc_TwoTruth(p, i), Bmc_TwoTruth(p, i), Bmc_TwoTruth(p, p->nObjs), p->nWords);
        }
    }
    return Abc_TtFindFirstDiffBit(Bmc_TwoTruth(p, p->nObjs-1), p->pTruth, p->nVars);
}

/**Function*************************************************************

  Synopsis    [Names original inputs and synthesized nodes.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static char * Bmc_TwoName( Bmc_TwoMan_t * p, int i, char * pName )
{
    if ( i < p->nVars ) sprintf(pName, "%c", 'a'+p->Map[i]);
    else if ( i-p->nVars < 26 ) sprintf(pName, "%c", 'A'+i-p->nVars);
    else sprintf(pName, "N%d", i-p->nVars);
    return pName;
}

/**Function*************************************************************

  Synopsis    [Prints the circuit and derives its AIG representation.]

  Description [Inverters on edges and the output are not counted as gates.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Bmc_TwoDerive( Bmc_TwoMan_t * p )
{
    Gia_Man_t * pGia = Gia_ManStart(4*p->nNodes + p->pPars->nVars + 4), * pClean;
    int Values[TWO_MAX_OBJS], Phases[TWO_MAX_OBJS] = {0}, Inputs[TWO_MAX_VARS];
    int i, a, b, t, n;
    char Name[16], Name0[16], Name1[16];
    pGia->pName = Abc_UtilStrsav("twoexact2");
    for ( i = 0; i < p->pPars->nVars; i++ ) Inputs[i] = Gia_ManAppendCi(pGia);
    for ( i = 0; i < p->nVars; i++ ) Values[i] = Inputs[p->Map[i]];
    Gia_ManHashAlloc(pGia);
    printf("Realization using %d %s gates (verified):\n", p->nNodes, p->pPars->fOnlyAnd ? "AND" : "two-input");
    for ( n = 0; n < p->nNodes; n++ )
    {
        i = p->nVars+n; t = p->Truths[n];
        a = p->Fans[n][0]; b = p->Fans[n][1];
        if ( t == 6 ) Values[i] = Gia_ManHashXor(pGia, Values[a], Values[b]);
        else Values[i] = Abc_LitNotCond(Gia_ManHashAnd(pGia, Abc_LitNotCond(Values[a], t == 4 || t == 14),
                                                                           Abc_LitNotCond(Values[b], t == 2 || t == 14)), t == 14);
        if ( p->pPars->fOnlyAnd )
        {
            printf("%s = %s%s & %s%s\n", Bmc_TwoName(p, i, Name),
                   Phases[a] ^ (t == 4 || t == 14) ? "!" : "", Bmc_TwoName(p, a, Name0),
                   Phases[b] ^ (t == 2 || t == 14) ? "!" : "", Bmc_TwoName(p, b, Name1));
            Phases[i] = t == 14;
        }
        else
            printf("%s = 4'b%d%d%d0( %s %s )\n", Bmc_TwoName(p, i, Name), (t>>3)&1, (t>>2)&1, (t>>1)&1,
                   Bmc_TwoName(p, b, Name1), Bmc_TwoName(p, a, Name0));
    }
    printf("out = %s%s\n", Phases[p->nObjs-1] ^ p->fCompl ? "!" : "", Bmc_TwoName(p, p->nObjs-1, Name));
    Gia_ManAppendCo(pGia, Abc_LitNotCond(Values[p->nObjs-1], p->fCompl));
    Gia_ManHashStop(pGia);
    pClean = Gia_ManCleanup(pGia);
    Gia_ManStop(pGia);
    return pClean;
}

/**Function*************************************************************

  Synopsis    [Writes the complete formula using a function-specific file name.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_TwoDump( Bmc_TwoMan_t * p )
{
    unsigned Hash = 2166136261u;
    char Name[128];
    FILE * pFile;
    int i, Lit, fOk;
    if ( p->pPars->pTtStr )
        for ( i = 0; p->pPars->pTtStr[i]; ++i ) Hash = (Hash ^ (unsigned char)p->pPars->pTtStr[i]) * 16777619u;
    else for ( i = 0; i < p->nWords; ++i )
    {
        word Value = p->pTruth[i];
        int b;
        for ( b = 0; b < 8; ++b, Value >>= 8 ) Hash = (Hash ^ (unsigned)(Value & 255)) * 16777619u;
    }
    sprintf(Name, "twoexact2_%08x_%d_%s.cnf", Hash, p->nNodes, p->pPars->fOnlyAnd ? "and" : "gate");
    pFile = fopen(Name, "wb");
    if ( !pFile ) { Abc_Print(-1, "Cannot open CNF file \"%s\".\n", Name); return 0; }
    fprintf(pFile, "p cnf %d %d\n", p->iVar, p->nClauses);
    Vec_IntForEachEntry(p->vCnf, Lit, i)
        if ( Lit ) fprintf(pFile, "%d ", Lit);
        else       fprintf(pFile, "0\n");
    fOk = !ferror(pFile);
    if ( fclose(pFile) ) fOk = 0;
    if ( !fOk ) Abc_Print(-1, "Could not write CNF file \"%s\".\n", Name);
    else printf("CNF written to %s.\n", Name);
    return fOk;
}

/**Function*************************************************************

  Synopsis    [Advances a reproducible encoder-local random generator.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static unsigned Bmc_TwoRandom( unsigned * pState )
{
    unsigned x = *pState;
    x ^= x << 13; x ^= x >> 17; x ^= x << 5;
    return *pState = x;
}

/**Function*************************************************************

  Synopsis    [Calls incremental bsat within the shared CPU time budget.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_TwoSolveBsat( Bmc_TwoMan_t * p, int * pnCalls )
{
    int Status = l_Undef;
    if ( p->fUnsat ) return 20;
    sat_solver_setnvars(p->pSat, p->iVar);
    do
    {
        if ( Bmc_TwoTerminate(p) ) break;
        // bsat uses Abc_Clock(), which is monotonic wall time on Linux.
        // Resume with retained clauses if our clock() budget remains.
        if ( p->timeStop )
            sat_solver_set_runtime_limit(p->pSat, Abc_Clock() + p->timeStop - (abctime)clock());
        Status = sat_solver_solve(p->pSat, NULL, NULL, 0, 0, 0, 0);
        (*pnCalls)++;
    }
    while ( Status == l_Undef && !Bmc_TwoTerminate(p) );
    return Status == l_True ? 10 : Status == l_False ? 20 : 0;
}

/**Function*************************************************************

  Synopsis    [Advances the reproducible candidate-search generator.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static unsigned Bmc_TwoSeedRandom( word * pState )
{
    *pState ^= *pState << 13;
    *pState ^= *pState >> 7;
    *pState ^= *pState << 17;
    return (unsigned)(*pState >> 16);
}

/**Function*************************************************************

  Synopsis    [Counts set bits without platform-specific instructions.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_TwoSeedPop( word x )
{
    x -= (x >> 1) & ABC_CONST(0x5555555555555555);
    x = (x & ABC_CONST(0x3333333333333333)) + ((x >> 2) & ABC_CONST(0x3333333333333333));
    x = (x + (x >> 4)) & ABC_CONST(0x0F0F0F0F0F0F0F0F);
    return (int)((x * ABC_CONST(0x0101010101010101)) >> 56);
}

/**Function*************************************************************

  Synopsis    [Evaluates a normal two-input gate on one truth-table word.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Bmc_TwoSeedFunction( int f, word a, word b, word Mask )
{
    if ( f == 2 ) return a & ~b & Mask;
    if ( f == 4 ) return ~a & b & Mask;
    if ( f == 8 ) return a & b;
    if ( f == 14 ) return a | b;
    return a ^ b;
}

/**Function*************************************************************

  Synopsis    [Copies the active prefix and its best output gate.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_TwoSeedCopy( Bmc_TwoSeedState_t * p, const Bmc_TwoSeedState_t * q, int nNodes )
{
    memcpy(p->Gates, q->Gates, sizeof(Bmc_TwoSeedGate_t)*(nNodes-1));
    p->Active = q->Active;
    p->a = q->a;
    p->b = q->b;
    p->f = q->f;
    p->Cost = q->Cost;
}

/**Function*************************************************************

  Synopsis    [Evaluates a prefix and chooses its best final gate.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_TwoSeedEvaluate( Bmc_TwoSeedState_t * p, const word * pInputs, int nVars, int nNodes, int fOnlyAnd, word Target, word Mask, word * pRandom )
{
    static const int Truths[5] = {2, 4, 8, 14, 6};
    word Values[TWO_MAX_OBJS], Deps[TWO_MAX_OBJS];
    unsigned Tie = 0, Rank;
    int i, g, a, b, k, Cost, Best = 1000;
    int Costs[5], Errors[TWO_MAX_OBJS], BaseCost = Bmc_TwoSeedPop(Target);
    for ( i = 0; i < nVars; i++ )
    {
        Values[i] = pInputs[i];
        Deps[i] = 0;
    }
    for ( g = 0; g < nNodes-1; g++ )
    {
        Bmc_TwoSeedGate_t Gate = p->Gates[g];
        Values[nVars+g] = Bmc_TwoSeedFunction(Gate.f, Values[Gate.a], Values[Gate.b], Mask);
        Deps[nVars+g] = Deps[Gate.a] | Deps[Gate.b] | ((word)1 << g);
    }
    for ( i = 0; i < nVars+nNodes-1; i++ )
        Errors[i] = Bmc_TwoSeedPop(Values[i] ^ Target);
    for ( a = 1; a < nVars+nNodes-1; a++ )
    for ( b = 0; b < a; b++ )
    {
        // For disjoint sets, error minus the all-zero error is additive.
        // The cached single-signal errors and one intersection error thus
        // determine all five gate errors, preserving the candidate order.
        Costs[2] = Bmc_TwoSeedPop((Values[a] & Values[b]) ^ Target);
        Costs[0] = Errors[a]-Costs[2]+BaseCost;
        Costs[1] = Errors[b]-Costs[2]+BaseCost;
        Costs[3] = Errors[a]+Errors[b]-Costs[2];
        Costs[4] = Errors[a]+Errors[b]-2*Costs[2]+BaseCost;
        for ( k = 0; k < 5-fOnlyAnd; k++ )
        {
            Cost = Costs[k];
            Rank = Cost <= Best ? Bmc_TwoSeedRandom(pRandom) : 0;
            if ( Cost < Best || (Cost == Best && Rank > Tie) )
            {
                Best = Cost;
                Tie = Rank;
                p->a = a;
                p->b = b;
                p->f = Truths[k];
                p->Active = Deps[a] | Deps[b];
            }
        }
    }
    p->Cost = Best;
}

/**Function*************************************************************

  Synopsis    [Samples an essential gate with ordered fanins.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Bmc_TwoSeedGate_t Bmc_TwoSeedGate( int Available, int fOnlyAnd, word * pRandom )
{
    static const int Truths[5] = {2, 4, 8, 14, 6};
    Bmc_TwoSeedGate_t Gate;
    int Temp;
    Gate.a = Bmc_TwoSeedRandom(pRandom) % Available;
    Gate.b = Bmc_TwoSeedRandom(pRandom) % (Available-1);
    if ( Gate.b >= Gate.a ) Gate.b++;
    Gate.f = Truths[Bmc_TwoSeedRandom(pRandom) % (5-fOnlyAnd)];
    if ( Gate.a < Gate.b )
    {
        Temp = Gate.a;
        Gate.a = Gate.b;
        Gate.b = Temp;
        if ( Gate.f == 2 ) Gate.f = 4;
        else if ( Gate.f == 4 ) Gate.f = 2;
    }
    return Gate;
}

/**Function*************************************************************

  Synopsis    [Searches several populations for a near-matching circuit.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_TwoSeedSearch( Bmc_TwoSeedState_t * pBest, word Target, int nVars, int nNodes, int fOnlyAnd, unsigned Seed, abctime Stop, int fVerbose )
{
    Bmc_TwoSeedState_t Parents[16], Child, * pParent;
    unsigned Ages[16] = {0}, Iter = 0;
    word Inputs[6] = {0}, Mask = nVars == 6 ? ~(word)0 : ((word)1 << (1 << nVars))-1;
    word Random = ABC_CONST(0x9e3779b97f4a7c15) ^ ((word)Seed+1);
    int Active[TWO_MAX_NODES], Count, g, i, row, Best = 1000, Island, Edits, Edit, Kind;
    abctime Start = (abctime)clock();
    Target &= Mask;
    for ( i = 0; i < nVars; i++ )
    for ( row = 0; row < (1 << nVars); row++ )
        if ( (row >> i) & 1 ) Inputs[i] |= (word)1 << row;
    for ( i = 0; i < 16; i++ )
    {
        for ( g = 0; g < nNodes-1; g++ ) Parents[i].Gates[g] = Bmc_TwoSeedGate(nVars+g, fOnlyAnd, &Random);
        Bmc_TwoSeedEvaluate(Parents+i, Inputs, nVars, nNodes, fOnlyAnd, Target, Mask, &Random);
    }
    for ( ;; )
    {
        Island = Iter % 16;
        pParent = Parents+Island;
        if ( pParent->Cost < Best )
        {
            Best = pParent->Cost;
            Bmc_TwoSeedCopy(pBest, pParent, nNodes);
        }
        // SAT repair handles the remaining error; no target-specific seed is used.
        if ( Best <= 1 ) break;
        if ( !(Iter & 1023) && (Iter >= 5000000 || (Stop && (abctime)clock() >= Stop)) ) break;
        Bmc_TwoSeedCopy(&Child, pParent, nNodes);
        if ( ++Ages[Island] >= 50000 )
        {
            Ages[Island] = 0;
            if ( Bmc_TwoSeedRandom(&Random) & 1 ) Bmc_TwoSeedCopy(&Child, pBest, nNodes);
            else for ( g = 0; g < nNodes-1; g++ ) Child.Gates[g] = Bmc_TwoSeedGate(nVars+g, fOnlyAnd, &Random);
        }
        Count = 0;
        for ( g = 0; g < nNodes-1; g++ ) if ( (pParent->Active >> g) & 1 ) Active[Count++] = g;
        // Keep the two random draws sequenced explicitly across C/C++ compilers.
        Edits = 1 + (Bmc_TwoSeedRandom(&Random) % 4 == 0);
        Edits += Bmc_TwoSeedRandom(&Random) % 8 == 0;
        for ( Edit = 0; Edit < Edits && nNodes > 1; Edit++ )
        {
            Bmc_TwoSeedGate_t Change;
            g = !Edit && Count ? Active[Bmc_TwoSeedRandom(&Random) % Count] : (int)(Bmc_TwoSeedRandom(&Random) % (nNodes-1));
            Change = Bmc_TwoSeedGate(nVars+g, fOnlyAnd, &Random);
            Kind = Bmc_TwoSeedRandom(&Random) % 4;
            if ( Kind == 0 ) Child.Gates[g].f = Change.f;
            else if ( Kind == 1 )
            {
                Child.Gates[g].a = Change.a;
                Child.Gates[g].b = Change.b;
            }
            else Child.Gates[g] = Change;
        }
        Bmc_TwoSeedEvaluate(&Child, Inputs, nVars, nNodes, fOnlyAnd, Target, Mask, &Random);
        Iter++;
        if ( Child.Cost <= pParent->Cost )
        {
            if ( Child.Cost < pParent->Cost ) Ages[Island] = 0;
            Bmc_TwoSeedCopy(pParent, &Child, nNodes);
        }
        else if ( !Ages[Island] ) Bmc_TwoSeedCopy(pParent, &Child, nNodes);
    }
    pBest->Gates[nNodes-1].a = pBest->a;
    pBest->Gates[nNodes-1].b = pBest->b;
    pBest->Gates[nNodes-1].f = pBest->f;
    if ( fVerbose ) printf("Candidate: errors = %d. Evaluations = %u. CPU = %.6f sec.\n", Best, Iter, (double)((abctime)clock()-Start)/CLOCKS_PER_SEC);
    return Best;
}

/**Function*************************************************************

  Synopsis    [Orders DIMACS literals by variable number.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_TwoSeedCompare( const void * pA, const void * pB )
{
    int a = abs(*(const int *)pA), b = abs(*(const int *)pB);
    return (a>b)-(a<b);
}

/**Function*************************************************************

  Synopsis    [Emits a repair clause after consistent literal ordering.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_TwoSeedClause( Bmc_TwoMan_t * p, int * pLits, int Count )
{
    qsort(pLits, Count, sizeof(int), Bmc_TwoSeedCompare);
    Bmc_TwoClause(p, pLits, Count);
}

/**Function*************************************************************

  Synopsis    [Emits a binary repair clause.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_TwoSeedC2( Bmc_TwoMan_t * p, int a, int b )
{
    int Lits[2] = {a, b};
    Bmc_TwoSeedClause(p, Lits, 2);
}

/**Function*************************************************************

  Synopsis    [Emits a ternary repair clause.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_TwoSeedC3( Bmc_TwoMan_t * p, int a, int b, int c )
{
    int Lits[3] = {a, b, c};
    Bmc_TwoSeedClause(p, Lits, 3);
}

/**Function*************************************************************

  Synopsis    [Emits a four-literal repair clause.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_TwoSeedC4( Bmc_TwoMan_t * p, int a, int b, int c, int d )
{
    int Lits[4] = {a, b, c, d};
    Bmc_TwoSeedClause(p, Lits, 4);
}

/**Function*************************************************************

  Synopsis    [Encodes a candidate neighborhood without structural order restrictions.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_TwoSeedEncode( Bmc_TwoMan_t * p, Bmc_TwoSeedState_t * pSeed, int * pChanged )
{
    int i, j, k, pin, row, a, b, y, f, Lits[2*TWO_MAX_OBJS], n, Values[TWO_MAX_OBJS];
    p->iVar = 1;
    Bmc_TwoEmit(p, &p->iVar, 1);
    for ( i = 0; i < p->nNodes; i++ )
        for ( k = 0; k < 3; k++ ) p->Funcs[i][k] = Bmc_TwoNewVar(p);
    for ( i = p->nVars; i < p->nObjs; i++ )
    {
        if ( Bmc_TwoTerminate(p) ) return 0;
        for ( pin = 0; pin < 2; pin++ )
        {
            n = 0;
            for ( j = 1-pin; j < i-pin; j++ ) Lits[n++] = p->VarMarks[i][pin][j] = Bmc_TwoNewVar(p);
            Bmc_TwoSeedClause(p, Lits, n);
            for ( j = 0; j < n; j++ )
                for ( k = 0; k < j; k++ ) Bmc_TwoSeedC2(p, -Lits[j], -Lits[k]);
        }
        for ( j = 1; j < i; j++ )
            for ( k = j; k < i-1; k++ ) Bmc_TwoSeedC2(p, -p->VarMarks[i][0][j], -p->VarMarks[i][1][k]);
        Bmc_TwoSeedC3(p,  p->Funcs[i-p->nVars][0],  p->Funcs[i-p->nVars][1],  p->Funcs[i-p->nVars][2]);
        Bmc_TwoSeedC3(p, -p->Funcs[i-p->nVars][0],  p->Funcs[i-p->nVars][1], -p->Funcs[i-p->nVars][2]);
        Bmc_TwoSeedC3(p,  p->Funcs[i-p->nVars][0], -p->Funcs[i-p->nVars][1], -p->Funcs[i-p->nVars][2]);
        if ( p->pPars->fOnlyAnd ) Bmc_TwoSeedC3(p, -p->Funcs[i-p->nVars][0], -p->Funcs[i-p->nVars][1], p->Funcs[i-p->nVars][2]);
    }
    for ( row = 1; row < (1 << p->nVars); row++ )
    {
        if ( Bmc_TwoTerminate(p) ) return 0;
        for ( i = 0; i < p->nVars; i++ ) Values[i] = (row >> i) & 1 ? 1 : -1;
        for ( i = p->nVars; i < p->nObjs; i++ )
        {
            a = Bmc_TwoNewVar(p);
            b = Bmc_TwoNewVar(p);
            y = Values[i] = i == p->nObjs-1 ? (Abc_TtGetBit(p->pTruth, row) ? 1 : -1) : Bmc_TwoNewVar(p);
            for ( pin = 0; pin < 2; pin++ )
            for ( j = 0; j < i; j++ ) if ( p->VarMarks[i][pin][j] )
            {
                Bmc_TwoSeedC3(p, -p->VarMarks[i][pin][j], pin ? -b : -a,  Values[j]);
                Bmc_TwoSeedC3(p, -p->VarMarks[i][pin][j], pin ?  b :  a, -Values[j]);
            }
            for ( k = 0; k < 4; k++ )
            {
                f = k ? p->Funcs[i-p->nVars][k-1] : -1;
                Bmc_TwoSeedC4(p, k & 1 ? -a : a, k & 2 ? -b : b, -y,  f);
                Bmc_TwoSeedC4(p, k & 1 ? -a : a, k & 2 ? -b : b,  y, -f);
            }
        }
    }
    for ( i = 0; i < p->nNodes; i++ )
    {
        int Condition[5];
        pChanged[i] = Bmc_TwoNewVar(p);
        Condition[0] = p->VarMarks[p->nVars+i][0][pSeed->Gates[i].a];
        Condition[1] = p->VarMarks[p->nVars+i][1][pSeed->Gates[i].b];
        for ( k = 0; k < 3; k++ ) Condition[k+2] = (pSeed->Gates[i].f >> (k+1)) & 1 ? p->Funcs[i][k] : -p->Funcs[i][k];
        for ( k = 0; k < 5; k++ ) Bmc_TwoSeedC2(p, pChanged[i], Condition[k]);
        Lits[0] = -pChanged[i];
        for ( k = 0; k < 5; k++ ) Lits[k+1] = -Condition[k];
        Bmc_TwoSeedClause(p, Lits, 6);
    }
    return !Bmc_TwoTerminate(p);
}

/**Function*************************************************************

  Synopsis    [Checks whether every internal gate reaches the output.]

  Description [Every non-output gate must have a fanout in this acyclic graph.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_TwoSeedCovered( Bmc_TwoMan_t * p )
{
    int Used[TWO_MAX_NODES] = {0}, i, k;
    for ( i = 0; i < p->nNodes; i++ )
        for ( k = 0; k < 2; k++ )
            if ( p->Fans[i][k] >= p->nVars )
                Used[p->Fans[i][k]-p->nVars] = 1;
    for ( i = 0; i < p->nNodes-1; i++ )
        if ( !Used[i] ) return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Requires every input and non-output gate to have a fanout.]

  Description [Added lazily if a repair model contains unused gates.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_TwoSeedRequireUsed( Bmc_TwoMan_t * p )
{
    int Lits[2*TWO_MAX_OBJS], i, j, k, n;
    for ( i = 0; i < p->nObjs-1; i++ )
    {
        n = 0;
        for ( j = Abc_MaxInt(p->nVars, i+1); j < p->nObjs; j++ )
            for ( k = 0; k < 2; k++ )
                if ( p->VarMarks[j][k][i] ) Lits[n++] = p->VarMarks[j][k][i];
        Bmc_TwoClause(p, Lits, n);
    }
}

/**Function*************************************************************

  Synopsis    [Tries a bounded candidate search and incremental SAT repair.]

  Description [A failed assumption core chooses the next gate to unlock.
               A restricted UNSAT or timeout only rejects this candidate.
               A stalled neighborhood gives way to the next candidate.
               Only an exhaustively checked, fully used circuit returns SAT;
               otherwise the caller continues its unrestricted exact search.
               Uses the bundled CaDiCaL through its public C interface.]

  SideEffects [Stores a verified circuit on success.]

  SeeAlso     []

***********************************************************************/
static int Bmc_TwoSeedSolve( Bmc_EsPar_t * pPars, word * pTruth, int nVars,
                           int * pMap, int nNodes, int nProbeSeconds, abctime timeStop, Gia_Man_t ** ppGia )
{
    abctime Start = (abctime)clock(), Stop = Start + (abctime)nProbeSeconds*CLOCKS_PER_SEC;
    abctime TrialStop, GenStop, CallStop, Before;
    Bmc_TwoMan_t * p;
    Bmc_TwoSeedState_t Best;
    int Changed[TWO_MAX_NODES], Fixed[TWO_MAX_NODES];
    int Attempt, Count, i, Status = 0, Selected, Seconds, fCovered, fFailed = 0;
    word Truth;
    if ( !nProbeSeconds || nVars > 6 || nNodes < 1 ) return 0;
    if ( timeStop && Stop > timeStop ) Stop = timeStop;
    Truth = (pTruth[0]&1) ? ~pTruth[0] : pTruth[0];
    for ( Attempt = 0; Attempt < 3 && (abctime)clock() < Stop; Attempt++ )
    {
        TrialStop = (abctime)clock() + (abctime)35*CLOCKS_PER_SEC;
        if ( TrialStop > Stop ) TrialStop = Stop;
        GenStop = (abctime)clock() + (abctime)8*CLOCKS_PER_SEC;
        if ( GenStop > TrialStop ) GenStop = TrialStop;
        memset(&Best, 0, sizeof(Best));
        Bmc_TwoSeedSearch(&Best, Truth, nVars, nNodes, pPars->fOnlyAnd,
                         (unsigned)pPars->Seed + Attempt, GenStop, pPars->fVerbose);
        if ( (abctime)clock() >= TrialStop ) continue;
        p = ABC_CALLOC(Bmc_TwoMan_t, 1);
        p->pPars = pPars;
        p->nVars = nVars;
        p->nNodes = nNodes;
        p->nObjs = nVars+nNodes;
        p->nWords = 1;
        p->pTruth = &Truth;
        p->fCompl = (int)(pTruth[0]&1);
        p->timeStop = TrialStop;
        memcpy(p->Map, pMap, sizeof(int)*nVars);
        p->vInfo = Vec_WrdStart(p->nObjs+1);
        p->pCadical = ccadical_init();
        ccadical_set_option(p->pCadical, "quiet", 1);
        ccadical_set_option(p->pCadical, "seed", pPars->Seed);
        ccadical_set_terminate(p->pCadical, p, Bmc_TwoTerminate);
        fCovered = 0;
        for ( i = 0; i < nNodes; i++ ) Fixed[i] = 1;
        if ( Bmc_TwoSeedEncode(p, &Best, Changed) )
        for ( Count = 0; Count <= Abc_MinInt(nNodes, 8) && (abctime)clock() < TrialStop; Count++ )
        {
            Seconds = Count < 4 ? 1 : Count < 7 ? 3 : 8;
            CallStop = (abctime)clock() + (abctime)Seconds*CLOCKS_PER_SEC;
            p->timeStop = CallStop < TrialStop ? CallStop : TrialStop;
            Before = (abctime)clock();
            for ( ;; )
            {
                for ( i = 0; i < nNodes; i++ )
                    if ( Fixed[i] ) ccadical_assume(p->pCadical, -Changed[i]);
                Status = ccadical_solve(p->pCadical);
                if ( Status != 10 ) break;
                if ( Bmc_TwoEval(p) != -1 )
                {
                    fFailed = 1;
                    Status = -1;
                    break;
                }
                if ( Bmc_TwoSeedCovered(p) ) break;
                if ( fCovered )
                {
                    fFailed = 1;
                    Status = -1;
                    break;
                }
                Bmc_TwoSeedRequireUsed(p);
                fCovered = 1;
                if ( Bmc_TwoTerminate(p) ) { Status = 0; break; }
            }
            if ( pPars->fVerbose )
                printf("Candidate %d: unlocked %d, %s, CPU = %.6f sec.\n", Attempt+1, Count,
                       Status == 10 ? "SAT" : Status == 20 ? "restricted UNSAT" : "undecided",
                    (double)((abctime)clock()-Before)/CLOCKS_PER_SEC);
            // A stalled neighborhood is less useful than a fresh candidate.
            if ( Status != 20 || fFailed ) break;
            Selected = -1;
            for ( i = 0; i < nNodes; i++ )
                if ( Fixed[i] && ccadical_failed(p->pCadical, -Changed[i]) )
                { Selected = i; break; }
            if ( Selected < 0 ) break;
            Fixed[Selected] = 0;
        }
        if ( Status == 10 )
        {
            printf("Nodes = %d : SAT  Vars = %d  Clauses = %d  CPU = %.6f sec (candidate repair)\n",
                   nNodes, p->iVar, p->nClauses, (double)((abctime)clock()-Start)/CLOCKS_PER_SEC);
            *ppGia = Bmc_TwoDerive(p);
        }
        ccadical_release(p->pCadical);
        Vec_WrdFree(p->vInfo);
        ABC_FREE(p);
        if ( Status == 10 ) return 10;
        if ( fFailed )
        {
            Abc_Print(-1, "Internal error: candidate repair failed exhaustive verification.\n");
            return -1;
        }
    }
    if ( pPars->fVerbose )
        printf("Candidate search found no circuit. CPU = %.6f sec.\n", (double)((abctime)clock()-Start)/CLOCKS_PER_SEC);
    return 0;
}

/**Function*************************************************************

  Synopsis    [Orders independent ready gates during minimum search.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_TwoStrongOrder( Bmc_TwoMan_t * p )
{
    int g, i, j, k, a, b, SameHigh, Same, Lits[5], * fa, * fb;
    if ( !p->fPreRows ) return;
    for ( g = p->nVars+1; g < p->nObjs; g++ )
    {
        SameHigh = Bmc_TwoNewVar(p);
        for ( i = 1; i < g-1; i++ )
            if ( p->VarMarks[g-1][0][i] && p->VarMarks[g][0][i] )
                Bmc_TwoClause3(p, -p->VarMarks[g-1][0][i], -p->VarMarks[g][0][i], SameHigh);
        for ( i = 0; i < g-2; i++ )
        for ( j = 0; j < i; j++ )
            if ( p->VarMarks[g-1][1][i] && p->VarMarks[g][1][j] )
                Bmc_TwoClause3(p, -SameHigh, -p->VarMarks[g-1][1][i], -p->VarMarks[g][1][j]);
        Same = Bmc_TwoNewVar(p);
        for ( i = 0; i < g-2; i++ )
            if ( p->VarMarks[g-1][1][i] && p->VarMarks[g][1][i] )
                Bmc_TwoClause4(p, -SameHigh, -p->VarMarks[g-1][1][i], -p->VarMarks[g][1][i], Same);
        fa = p->Funcs[g-p->nVars-1];
        fb = p->Funcs[g-p->nVars];
        for ( a = 0; a < 4; a++ )
        for ( b = 0; b <= a; b++ )
        {
            Lits[0] = -Same;
            for ( k = 0; k < 2; k++ )
            {
                Lits[1+k] = (a >> k) & 1 ? -fa[1+k] : fa[1+k];
                Lits[3+k] = (b >> k) & 1 ? -fb[1+k] : fb[1+k];
            }
            Bmc_TwoClause(p, Lits, 5);
        }
    }
}

/**Function*************************************************************

  Synopsis    [Encodes a difference between two simulation values.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_TwoStrongXor( Bmc_TwoMan_t * p, int a, int b )
{
    int q;
    if ( a == b ) return -1;
    if ( a == -b ) return 1;
    if ( a == 1 ) return -b;
    if ( a == -1 ) return b;
    if ( b == 1 ) return -a;
    if ( b == -1 ) return a;
    q = Bmc_TwoNewVar(p);
    Bmc_TwoClause3(p, a, b, -q);
    Bmc_TwoClause3(p, a, -b, q);
    Bmc_TwoClause3(p, -a, b, q);
    Bmc_TwoClause3(p, -a, -b, -q);
    return q;
}

/**Function*************************************************************

  Synopsis    [Encodes a lower bound with an equivalent sequential counter.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_TwoStrongAtLeast( Bmc_TwoMan_t * p, int * pVars, int Count, int Bound )
{
    int Prev[7], Cur[7], i, j, q, a, b, c;
    assert( Bound >= 1 && Bound <= 6 );
    Prev[0] = 1;
    for ( j = 1; j <= Bound; j++ ) Prev[j] = -1;
    for ( i = 0; i < Count; i++ )
    {
        Cur[0] = 1;
        for ( j = 1; j <= Bound; j++ ) Cur[j] = j <= i+1 ? Bmc_TwoNewVar(p) : -1;
        for ( j = 1; j <= Abc_MinInt(i+1, Bound); j++ )
        {
            q = Cur[j]; a = Prev[j]; b = Prev[j-1]; c = pVars[i];
            Bmc_TwoClause2(p, -a, q);
            Bmc_TwoClause3(p, -b, -c, q);
            Bmc_TwoClause3(p, -q, a, b);
            Bmc_TwoClause3(p, -q, a, c);
        }
        memcpy(Prev, Cur, sizeof(int)*(Bound+1));
    }
    Bmc_TwoClause(p, Prev+Bound, 1);
}

// Exact three-input AND minima, independently checked including all smaller counts.
/**Function*************************************************************

  Synopsis    [Bounds gates surviving each three-input cofactor.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_TwoStrongBounds( Bmc_TwoMan_t * p )
{
    static const unsigned char Costs3[256] = {
        0, 2, 2, 1, 2, 1, 4, 2, 2, 4, 1, 2, 1, 2, 2, 0,
        2, 1, 4, 2, 4, 2, 6, 4, 5, 4, 4, 3, 4, 3, 4, 2,
        2, 4, 1, 2, 5, 4, 4, 3, 4, 6, 2, 4, 4, 4, 3, 2,
        1, 2, 2, 0, 4, 3, 4, 2, 4, 4, 3, 2, 3, 4, 4, 1,
        2, 4, 5, 4, 1, 2, 4, 3, 4, 6, 4, 4, 2, 4, 3, 2,
        1, 2, 4, 3, 2, 0, 4, 2, 4, 4, 3, 4, 3, 2, 4, 1,
        4, 6, 4, 4, 4, 4, 3, 4, 6, 6, 4, 6, 4, 6, 4, 4,
        2, 4, 3, 2, 3, 2, 4, 1, 4, 6, 4, 4, 4, 4, 5, 2,
        2, 5, 4, 4, 4, 4, 6, 4, 1, 4, 2, 3, 2, 3, 4, 2,
        4, 4, 6, 4, 6, 4, 6, 6, 4, 3, 4, 4, 4, 4, 6, 4,
        1, 4, 2, 3, 4, 3, 4, 4, 2, 4, 0, 2, 3, 4, 2, 1,
        2, 3, 4, 2, 4, 4, 6, 4, 3, 4, 2, 1, 4, 5, 4, 2,
        1, 4, 4, 3, 2, 3, 4, 4, 2, 4, 3, 4, 0, 2, 2, 1,
        2, 3, 4, 4, 4, 2, 6, 4, 3, 4, 4, 5, 2, 1, 4, 2,
        2, 4, 3, 4, 3, 4, 4, 5, 4, 6, 2, 4, 2, 4, 1, 2,
        0, 2, 2, 1, 2, 1, 4, 2, 2, 4, 1, 2, 1, 2, 2, 0
     };
    int Diffs[16][TWO_MAX_NODES][2] = {{{0}}};
    int pi, phase, row, g, pin, j, small, bound, rows[8], Values[8], Other, Lits[9], Live[TWO_MAX_NODES];
    if ( !p->fPreRows ) return;
    for ( pi = 0; pi < 4; pi++ )
    for ( phase = 0; phase < 2; phase++ )
    {
        small = j = 0;
        for ( row = 0; row < 16; row++ ) if ( ((row >> pi) & 1) == phase )
        {
            rows[j] = row;
            small |= Abc_TtGetBit(p->pTruth, row) << j++;
        }
        assert( j == 8 );
        bound = Costs3[small];
        if ( !bound ) continue;
        for ( g = 0; g < p->nNodes; g++ )
        {
            for ( j = 0; j < 8; j++ )
            {
                row = rows[j];
                Values[j] = !row ? -1 : g == p->nNodes-1 ? (Abc_TtGetBit(p->pTruth, row) ? 1 : -1) : p->RowVars[row][g][2];
            }
            Live[g] = Bmc_TwoNewVar(p);
            Lits[0] = -Live[g];
            for ( j = 0; j < 8; j++ ) Lits[1+j] = Values[j];
            Bmc_TwoClause(p, Lits, 9);
            for ( j = 0; j < 8; j++ ) Lits[1+j] = -Values[j];
            Bmc_TwoClause(p, Lits, 9);
            for ( pin = 0; pin < 2; pin++ )
            {
                for ( j = 0; j < 8; j++ )
                {
                    row = rows[j];
                    Other = row ? p->RowVars[row][g][pin] : -1;
                    if ( !Diffs[row][g][pin] ) Diffs[row][g][pin] = Bmc_TwoStrongXor(p, Values[j], Other);
                    Lits[1+j] = Diffs[row][g][pin];
                }
                Bmc_TwoClause(p, Lits, 9);
                // Bmc_TwoClause compacts Lits in place. Rebuild from the stable cache.
                for ( j = 0; j < 8; j++ ) Lits[1+j] = -Diffs[rows[j]][g][pin];
                Bmc_TwoClause(p, Lits, 9);
            }
        }
        Bmc_TwoStrongAtLeast(p, Live, p->nNodes, bound);
    }
}

/**Function*************************************************************

  Synopsis    [Reserves row variables for four-input AND minimum search.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_TwoStrongPrepare( Bmc_TwoMan_t * p )
{
    int row, g;
    p->fPreRows = p->fBoost && p->pPars->fMinNodes && p->pPars->fOnlyAnd && p->nVars == 4;
    if ( p->fPreRows )
        for ( row = 1; row < 16; row++ )
            for ( g = 0; g < p->nNodes; g++ )
            {
                p->RowVars[row][g][0] = Bmc_TwoNewVar(p);
                p->RowVars[row][g][1] = Bmc_TwoNewVar(p);
                if ( g < p->nNodes-1 ) p->RowVars[row][g][2] = Bmc_TwoNewVar(p);
            }
    Bmc_TwoStrongOrder(p);
    Bmc_TwoStrongBounds(p);
}

/**Function*************************************************************

  Synopsis    [Finds a proven lower bound for a smaller cofactor.]

  Description [The table contains the complete four-input NPN library for
               both gate bases, not solutions to the enclosing problem.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_TwoCofCost( unsigned Truth, int nVars, int fOnlyAnd )
{
    static const unsigned short Classes[222] = {
        0x0000, 0x0001, 0x0003, 0x0006, 0x0007, 0x000F, 0x0016, 0x0017, 0x0018, 0x0019, 0x001B, 0x001E, 0x001F, 0x003C, 0x003D, 0x003F,
        0x0069, 0x006B, 0x006F, 0x007E, 0x007F, 0x00FF, 0x0116, 0x0117, 0x0118, 0x0119, 0x011A, 0x011B, 0x011E, 0x011F, 0x012C, 0x012D,
        0x012F, 0x013C, 0x013D, 0x013E, 0x013F, 0x0168, 0x0169, 0x016A, 0x016B, 0x016E, 0x016F, 0x017E, 0x017F, 0x0180, 0x0181, 0x0182,
        0x0183, 0x0186, 0x0187, 0x0189, 0x018B, 0x018F, 0x0196, 0x0197, 0x0198, 0x0199, 0x019A, 0x019B, 0x019E, 0x019F, 0x01A8, 0x01A9,
        0x01AA, 0x01AB, 0x01AC, 0x01AD, 0x01AE, 0x01AF, 0x01BC, 0x01BD, 0x01BE, 0x01BF, 0x01E8, 0x01E9, 0x01EA, 0x01EB, 0x01EE, 0x01EF,
        0x01FE, 0x033C, 0x033D, 0x033F, 0x0356, 0x0357, 0x0358, 0x0359, 0x035A, 0x035B, 0x035E, 0x035F, 0x0368, 0x0369, 0x036A, 0x036B,
        0x036C, 0x036D, 0x036E, 0x036F, 0x037C, 0x037D, 0x037E, 0x03C0, 0x03C1, 0x03C3, 0x03C5, 0x03C6, 0x03C7, 0x03CF, 0x03D4, 0x03D5,
        0x03D6, 0x03D7, 0x03D8, 0x03D9, 0x03DB, 0x03DC, 0x03DD, 0x03DE, 0x03FC, 0x0660, 0x0661, 0x0662, 0x0663, 0x0666, 0x0667, 0x0669,
        0x066B, 0x066F, 0x0672, 0x0673, 0x0676, 0x0678, 0x0679, 0x067A, 0x067B, 0x067E, 0x0690, 0x0691, 0x0693, 0x0696, 0x0697, 0x069F,
        0x06B0, 0x06B1, 0x06B2, 0x06B3, 0x06B4, 0x06B5, 0x06B6, 0x06B7, 0x06B9, 0x06BD, 0x06F0, 0x06F1, 0x06F2, 0x06F6, 0x06F9, 0x0776,
        0x0778, 0x0779, 0x077A, 0x077E, 0x07B0, 0x07B1, 0x07B4, 0x07B5, 0x07B6, 0x07BC, 0x07E0, 0x07E1, 0x07E2, 0x07E3, 0x07E6, 0x07E9,
        0x07F0, 0x07F1, 0x07F2, 0x07F8, 0x0FF0, 0x1668, 0x1669, 0x166A, 0x166B, 0x166E, 0x167E, 0x1681, 0x1683, 0x1686, 0x1687, 0x1689,
        0x168B, 0x168E, 0x1696, 0x1697, 0x1698, 0x1699, 0x169A, 0x169B, 0x169E, 0x16A9, 0x16AC, 0x16AD, 0x16BC, 0x16E9, 0x177E, 0x178E,
        0x1796, 0x1798, 0x179A, 0x17AC, 0x17E8, 0x18E7, 0x19E1, 0x19E3, 0x19E6, 0x1BD8, 0x1BE4, 0x1EE1, 0x3CC3, 0x6996
     };
    static const unsigned char Costs[2][222] = { {
        0, 3, 2, 3, 3, 1, 5, 5, 4, 4, 4, 3, 3, 2, 4, 2,
        3, 5, 3, 4, 3, 0, 7, 7, 6, 6, 6, 6, 5, 5, 5, 5,
        5, 5, 5, 5, 5, 5, 5, 6, 6, 5, 5, 6, 6, 5, 5, 5,
        5, 5, 5, 5, 5, 5, 6, 6, 4, 4, 5, 6, 6, 6, 4, 4,
        4, 4, 6, 6, 4, 4, 6, 6, 5, 5, 6, 6, 5, 5, 4, 4,
        3, 4, 6, 4, 3, 3, 5, 4, 4, 4, 5, 4, 6, 5, 5, 5,
        5, 6, 5, 5, 5, 6, 5, 3, 5, 3, 5, 5, 5, 3, 5, 5,
        5, 5, 6, 5, 6, 4, 5, 4, 2, 3, 6, 5, 5, 3, 6, 5,
        7, 5, 6, 5, 5, 6, 6, 6, 6, 6, 4, 6, 6, 4, 6, 4,
        6, 6, 6, 6, 6, 6, 6, 6, 5, 5, 4, 5, 6, 4, 3, 6,
        5, 7, 6, 6, 4, 6, 5, 6, 6, 5, 5, 6, 6, 6, 6, 5,
        4, 5, 4, 3, 1, 6, 6, 7, 6, 6, 6, 7, 6, 5, 6, 6,
        7, 7, 5, 6, 7, 5, 6, 7, 5, 6, 7, 6, 5, 5, 6, 5,
        5, 6, 7, 6, 5, 4, 6, 6, 4, 5, 4, 3, 2, 3
     }, {
        0, 3, 2, 5, 3, 1, 7, 5, 6, 5, 4, 5, 3, 4, 5, 2,
        7, 7, 5, 6, 3, 0, 9, 7, 8, 7, 7, 6, 7, 5, 8, 7,
        5, 7, 6, 7, 5, 9, 8, 8, 8, 8, 6, 8, 6, 7, 6, 8,
        6, 9, 7, 5, 5, 5, 9, 9, 8, 6, 8, 7, 9, 7, 6, 5,
        5, 4, 7, 6, 6, 4, 8, 7, 8, 6, 8, 7, 7, 6, 5, 4,
        5, 6, 7, 4, 5, 3, 7, 7, 6, 6, 7, 4, 8, 8, 8, 7,
        7, 8, 8, 7, 7, 7, 8, 5, 6, 4, 6, 6, 5, 3, 7, 6,
        7, 5, 7, 7, 6, 6, 5, 6, 4, 7, 9, 7, 7, 5, 7, 9,
        9, 7, 7, 7, 6, 9, 9, 8, 9, 8, 8, 9, 8, 7, 8, 6,
        8, 9, 8, 8, 8, 8, 7, 8, 8, 8, 7, 7, 7, 6, 7, 7,
        7, 9, 7, 8, 7, 8, 7, 7, 8, 7, 7, 7, 7, 7, 7, 7,
        5, 7, 6, 5, 3, 9, 10, 9, 10, 9, 9, 10, 10, 9, 9, 9,
        9, 9, 8, 9, 9, 8, 8, 9, 8, 9, 9, 9, 8, 9, 9, 8,
        9, 8, 8, 8, 7, 8, 9, 9, 7, 9, 6, 7, 6, 9
     } };
    unsigned Stretched = 0, Canon;
    int i, Lo = 0, Hi = 221;
    assert( nVars >= 0 && nVars <= 4 );
    for ( i = 0; i < 16; i++ )
        Stretched |= ((Truth >> (i & ((1 << nVars)-1))) & 1) << i;
    Canon = Extra_TruthCanonNPN(Stretched, 4);
    while ( Lo <= Hi )
    {
        int Mid = (Lo+Hi)/2;
        if ( Classes[Mid] == Canon ) return Costs[fOnlyAnd != 0][Mid];
        if ( Classes[Mid] < Canon ) Lo = Mid+1;
        else Hi = Mid-1;
    }
    assert( 0 );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Emits a copied clause in a deterministic literal order.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_TwoCofClause( Bmc_TwoMan_t * p, int * pLits, int nLits )
{
    int Lits[17], i, j, Temp;
    assert( nLits <= 17 );
    memcpy(Lits, pLits, sizeof(int)*nLits);
    for ( i = 1; i < nLits; i++ )
        for ( j = i; j && abs(Lits[j]) < abs(Lits[j-1]); j-- )
        { Temp = Lits[j]; Lits[j] = Lits[j-1]; Lits[j-1] = Temp; }
    Bmc_TwoClause(p, Lits, nLits);
}

/**Function*************************************************************

  Synopsis    [Encodes a difference used to recognize a bypassed gate.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_TwoCofXor( Bmc_TwoMan_t * p, int a, int b )
{
    int q, Lits[3];
    if ( a == b ) return -1;
    if ( a == -b ) return 1;
    if ( a == 1 ) return -b;
    if ( a == -1 ) return b;
    if ( b == 1 ) return -a;
    if ( b == -1 ) return a;
    q = Bmc_TwoNewVar(p);
    Lits[0] = a; Lits[1] = b; Lits[2] = -q; Bmc_TwoCofClause(p, Lits, 3);
    Lits[0] = a; Lits[1] = -b; Lits[2] = q; Bmc_TwoCofClause(p, Lits, 3);
    Lits[0] = -a; Lits[1] = b; Lits[2] = q; Bmc_TwoCofClause(p, Lits, 3);
    Lits[0] = -a; Lits[1] = -b; Lits[2] = -q; Bmc_TwoCofClause(p, Lits, 3);
    return q;
}

/**Function*************************************************************

  Synopsis    [Requires enough gates to remain nontrivial in a cofactor.]

  Description [Each counter state is an equivalence, including constants.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_TwoCofAtLeast( Bmc_TwoMan_t * p, int * pVars, int Count, int Bound )
{
    int Prev[11], Cur[11], i, j, q, a, b, c, Lits[3];
    assert( Bound >= 1 && Bound <= 10 );
    Prev[0] = 1;
    for ( j = 1; j <= Bound; j++ ) Prev[j] = -1;
    for ( i = 0; i < Count; i++ )
    {
        Cur[0] = 1;
        for ( j = 1; j <= Bound; j++ ) Cur[j] = j <= i+1 ? Bmc_TwoNewVar(p) : -1;
        for ( j = 1; j <= Abc_MinInt(i+1, Bound); j++ )
        {
            q = Cur[j]; a = Prev[j]; b = Prev[j-1]; c = pVars[i];
            Lits[0] = -a; Lits[1] = q; Bmc_TwoCofClause(p, Lits, 2);
            Lits[0] = -b; Lits[1] = -c; Lits[2] = q; Bmc_TwoCofClause(p, Lits, 3);
            Lits[0] = -q; Lits[1] = a; Lits[2] = b; Bmc_TwoCofClause(p, Lits, 3);
            Lits[0] = -q; Lits[1] = a; Lits[2] = c; Bmc_TwoCofClause(p, Lits, 3);
        }
        memcpy(Prev, Cur, sizeof(int)*(Bound+1));
    }
    Bmc_TwoCofClause(p, Prev+Bound, 1);
}

/**Function*************************************************************

  Synopsis    [Adds target-independent lower bounds on all input cofactors.]

  Description [A gate survives only if its cofactor is nonconstant and is
               neither polarity of a fanin. Bypassing all other gates gives
               a circuit with at least the known smaller-function minimum.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_TwoCofBounds( Bmc_TwoMan_t * p )
{
    int Diffs[32][TWO_MAX_NODES][2] = {{{0}}};
    int pi, phase, row, g, pin, j, Small, Bound, Rows[16], Values[16];
    int Other, Lits[17], Live[TWO_MAX_NODES], nRows = 1 << (p->nVars-1);
    if ( !p->fCofRows || p->fCofAdded ) return;
    p->fCofAdded = 1;
    for ( pi = 0; pi < p->nVars; pi++ )
    for ( phase = 0; phase < 2; phase++ )
    {
        Small = j = 0;
        for ( row = 0; row < 2*nRows; row++ ) if ( ((row >> pi) & 1) == phase )
        {
            Rows[j] = row;
            Small |= Abc_TtGetBit(p->pTruth, row) << j++;
        }
        assert( j == nRows );
        Bound = Bmc_TwoCofCost((unsigned)Small, p->nVars-1, p->pPars->fOnlyAnd);
        if ( !Bound ) continue;
        for ( g = 0; g < p->nNodes; g++ )
        {
            for ( j = 0; j < nRows; j++ )
            {
                row = Rows[j];
                Values[j] = !row ? -1 : g == p->nNodes-1 ? (Abc_TtGetBit(p->pTruth, row) ? 1 : -1) : p->RowVars[row][g][2];
            }
            Live[g] = Bmc_TwoNewVar(p);
            Lits[0] = -Live[g];
            for ( j = 0; j < nRows; j++ ) Lits[1+j] = Values[j];
            Bmc_TwoCofClause(p, Lits, nRows+1);
            for ( j = 0; j < nRows; j++ ) Lits[1+j] = -Values[j];
            Bmc_TwoCofClause(p, Lits, nRows+1);
            for ( pin = 0; pin < 2; pin++ )
            {
                for ( j = 0; j < nRows; j++ )
                {
                    row = Rows[j];
                    Other = row ? p->RowVars[row][g][pin] : -1;
                    if ( !Diffs[row][g][pin] ) Diffs[row][g][pin] = Bmc_TwoCofXor(p, Values[j], Other);
                    Lits[1+j] = Diffs[row][g][pin];
                }
                Bmc_TwoCofClause(p, Lits, nRows+1);
                for ( j = 0; j < nRows; j++ ) Lits[1+j] = -Diffs[Rows[j]][g][pin];
                Bmc_TwoCofClause(p, Lits, nRows+1);
            }
        }
        Bmc_TwoCofAtLeast(p, Live, p->nNodes, Bound);
    }
}

/**Function*************************************************************

  Synopsis    [Reserves row values shared by cofactor bounds and refinement.]

  Description [Only small cofactors use the finite library. Larger functions
               keep the ordinary encoding. No target circuit is stored.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_TwoCofPrepare( Bmc_TwoMan_t * p )
{
    int row, g;
    p->fCofRows = p->fBoost && !p->fPreRows && p->nVars >= 3 && p->nVars <= 5;
    if ( !p->fCofRows ) return;
    for ( row = 1; row < (1 << p->nVars); row++ )
        for ( g = 0; g < p->nNodes; g++ )
        {
            p->RowVars[row][g][0] = Bmc_TwoNewVar(p);
            p->RowVars[row][g][1] = Bmc_TwoNewVar(p);
            if ( g < p->nNodes-1 ) p->RowVars[row][g][2] = Bmc_TwoNewVar(p);
        }
    if ( p->pSat ) Bmc_TwoCofBounds(p);
}
/**Function*************************************************************

  Synopsis    [Copies and orders an implied distinguishability clause.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_TwoDiffClause( Bmc_TwoMan_t * p, const int * pLits, int Count )
{
    int Lits[TWO_MAX_OBJS+2], i, j, Temp;
    assert( Count <= TWO_MAX_OBJS+2 );
    memcpy(Lits, pLits, sizeof(int)*Count);
    for ( i = 1; i < Count; i++ )
        for ( j = i; j && abs(Lits[j-1]) > abs(Lits[j]); j-- )
        { Temp = Lits[j]; Lits[j] = Lits[j-1]; Lits[j-1] = Temp; }
    Bmc_TwoClause(p, Lits, Count);
}

/**Function*************************************************************

  Synopsis    [Emits a three-literal distinguishability clause.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_TwoDiffC3( Bmc_TwoMan_t * p, int a, int b, int c )
{
    int Lits[3] = {a, b, c};
    Bmc_TwoDiffClause(p, Lits, 3);
}

/**Function*************************************************************

  Synopsis    [Emits a four-literal distinguishability clause.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_TwoDiffC4( Bmc_TwoMan_t * p, int a, int b, int c, int d )
{
    int Lits[4] = {a, b, c, d};
    Bmc_TwoDiffClause(p, Lits, 4);
}

/**Function*************************************************************

  Synopsis    [Returns the row literal of a signal, including constants.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_TwoDiffValue( Bmc_TwoMan_t * p, int Obj, int Row )
{
    if ( !Row ) return -1;
    if ( Obj < p->nVars ) return (Row >> Obj) & 1 ? 1 : -1;
    if ( Obj == p->nObjs-1 ) return Abc_TtGetBit(p->pTruth, Row) ? 1 : -1;
    return p->RowVars[Row][Obj-p->nVars][2];
}

/**Function*************************************************************

  Synopsis    [Encodes the XOR of two row literals.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_TwoDiffXor( Bmc_TwoMan_t * p, int a, int b )
{
    int q;
    if ( a == b ) return -1;
    if ( a == -b ) return 1;
    if ( a == -1 ) return b;
    if ( a == 1 ) return -b;
    if ( b == -1 ) return a;
    if ( b == 1 ) return -a;
    q = Bmc_TwoNewVar(p);
    Bmc_TwoDiffC3(p, -a, -b, -q);
    Bmc_TwoDiffC3(p,  a,  b, -q);
    Bmc_TwoDiffC3(p,  a, -b,  q);
    Bmc_TwoDiffC3(p, -a,  b,  q);
    return q;
}

/**Function*************************************************************

  Synopsis    [Selects the difference of a gate fanin.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_TwoDiffMux( Bmc_TwoMan_t * p, int Obj, int Pin, int Dst, int * pValues )
{
    int Lits[TWO_MAX_OBJS+2], i, n;
    for ( i = 0; i < Obj; i++ ) if ( p->VarMarks[Obj][Pin][i] )
    {
        Bmc_TwoDiffC3(p, -p->VarMarks[Obj][Pin][i], -Dst, pValues[i]);
        Bmc_TwoDiffC3(p, -p->VarMarks[Obj][Pin][i], Dst, -pValues[i]);
    }
    Lits[0] = -Dst;
    for ( i = 0, n = 1; i < Obj; i++ ) if ( p->VarMarks[Obj][Pin][i] ) Lits[n++] = pValues[i];
    Bmc_TwoDiffClause(p, Lits, n);
    Lits[0] = Dst;
    for ( i = 0, n = 1; i < Obj; i++ ) if ( p->VarMarks[Obj][Pin][i] ) Lits[n++] = -pValues[i];
    Bmc_TwoDiffClause(p, Lits, n);
}

/**Function*************************************************************

  Synopsis    [Propagates distinguishability between adjacent input patterns.]

  Description [A gate can differ only if one of its selected fanins differs.
               If one fanin is unchanged, its value and the gate's input phase
               further restrict propagation from the other fanin.  These
               constraints are implied by the complete simulation rows.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_TwoDiffAll( Bmc_TwoMan_t * p )
{
    int Row, Other, Pi, Obj, g, a, b, x, z, Da, Db, Dy, Values[TWO_MAX_OBJS];
    if ( !p->fPreRows || p->fDiffAdded || p->fUnsat ) return;
    for ( Row = 0; Row < 16; Row++ )
    for ( Pi = 0; Pi < 4; Pi++ ) if ( !((Row >> Pi) & 1) )
    {
        if ( Bmc_TwoTerminate(p) ) return;
        Other = Row | (1 << Pi);
        for ( Obj = 0; Obj < p->nObjs; Obj++ )
            Values[Obj] = Bmc_TwoDiffXor(p, Bmc_TwoDiffValue(p, Obj, Row), Bmc_TwoDiffValue(p, Obj, Other));
        for ( g = 0; g < p->nNodes; g++ )
        {
            Da = Bmc_TwoNewVar(p);
            Db = Bmc_TwoNewVar(p);
            Dy = Values[p->nVars+g];
            Bmc_TwoDiffMux(p, p->nVars+g, 0, Da, Values);
            Bmc_TwoDiffMux(p, p->nVars+g, 1, Db, Values);
            Bmc_TwoDiffC3(p, -Dy, Da, Db);
            // A normal AND-only gate has y = a*b XOR x*a XOR z*b.
            // When Da is zero, Dy = (a XOR z)*Db; likewise for Db.
            a = Row ? p->RowVars[Row][g][0] : -1;
            b = Row ? p->RowVars[Row][g][1] : -1;
            x = p->Funcs[g][0];
            z = p->Funcs[g][1];
            Bmc_TwoDiffC4(p, -a, Da, -z, -Dy);
            Bmc_TwoDiffC4(p,  a, Da,  z, -Dy);
            Bmc_TwoDiffC4(p, -b, Db, -x, -Dy);
            Bmc_TwoDiffC4(p,  b, Db,  x, -Dy);
        }
    }
    p->fDiffAdded = 1;
}

/**Function*************************************************************

  Synopsis    [Solves one node count and returns SAT, UNSAT, or UNKNOWN.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_TwoSolve( Bmc_EsPar_t * pPars, word * pTruth, int nVars, int * pMap, int nNodes, int fSeed, int fBoost, int nProbeSeconds, Gia_Man_t ** ppGia )
{
    Bmc_TwoMan_t * p;
    abctime clk = (abctime)clock(), clkCall, timeSolve = 0;
    int i, j, Temp, Mint, Status = 0, fVerified = 0, fStarted, nAdded = 0, nCalls = 0;
    int * pRows = NULL, nRows = (1 << nVars)-1;
    unsigned char * pAdded;
    unsigned Random = (unsigned)pPars->Seed ^ 0x9e3779b9u;
    if ( fSeed )
    {
        abctime Stop = pPars->RuntimeLim ? clk + (abctime)pPars->RuntimeLim*CLOCKS_PER_SEC : 0;
        Status = Bmc_TwoSeedSolve(pPars, pTruth, nVars, pMap, nNodes, nProbeSeconds, Stop, ppGia);
        if ( Status == 10 || Status < 0 ) return Status;
    }
    p = ABC_CALLOC(Bmc_TwoMan_t, 1);
    p->fBoost = fBoost;
    pAdded = ABC_CALLOC(unsigned char, nRows+1);
    p->pPars = pPars;
    p->nVars = nVars;
    p->nNodes = nNodes;
    p->nObjs = nVars+nNodes;
    p->nWords = Abc_TtWordNum(nVars);
    p->pTruth = ABC_ALLOC(word, p->nWords);
    Abc_TtCopy(p->pTruth, pTruth, p->nWords, 0);
    p->fCompl = (int)(pTruth[0] & 1);
    if ( p->fCompl ) Abc_TtNot(p->pTruth, p->nWords);
    memcpy(p->Map, pMap, sizeof(int)*nVars);
    p->vInfo = Vec_WrdStart(p->nWords*(p->nObjs+1));
    p->vOutLits = Vec_WecStart(p->nObjs);
    if ( pPars->fDumpCnf ) p->vCnf = Vec_IntAlloc(1000);
    if ( pPars->RuntimeLim ) p->timeStop = clk + (abctime)pPars->RuntimeLim*CLOCKS_PER_SEC;
    if ( pPars->fCadical )
    {
        p->pCadical = ccadical_init();
        ccadical_set_option(p->pCadical, "seed", pPars->Seed);
        ccadical_set_terminate(p->pCadical, p, Bmc_TwoTerminate);
    }
    else if ( pPars->fKissat )
    {
        p->pKissat = kissat_init();
        if ( fBoost && nVars == 5 ) kissat_disable_fast_elimination(p->pKissat);
        kissat_set_option(p->pKissat, "seed", pPars->Seed);
        kissat_set_terminate(p->pKissat, p, Bmc_TwoTerminate);
    }
    else
    {
        p->pSat = sat_solver_new();
        if ( pPars->Seed ) p->pSat->random_seed = pPars->Seed;
    }
    Bmc_TwoMarkup(p);
    fStarted = Bmc_TwoStart(p);
    Bmc_TwoStrongPrepare(p);
    Bmc_TwoCofPrepare(p);
    if ( p->pSat ) Bmc_TwoDiffAll(p);
    // Kissat's bundled fixed-option build ignores its solver seed. Randomize
    // the row order in all backends; seed zero retains the natural order.
    if ( pPars->Seed )
    {
        pRows = ABC_ALLOC(int, nRows);
        for ( i = 0; i < nRows; i++ ) pRows[i] = i+1;
        for ( i = 0; i < nRows-1; i++ )
        {
            j = i + Bmc_TwoRandom(&Random) % (nRows-i);
            Temp = pRows[i]; pRows[i] = pRows[j]; pRows[j] = Temp;
        }
    }
    if ( p->pSat )
    {
        // Keep one bsat solver and its learned clauses across failing rows.
        Mint = pRows ? pRows[0] : 1;
        while ( !Bmc_TwoTerminate(p) )
        {
            if ( Mint < 1 || Mint > nRows || pAdded[Mint] ) { Status = -1; break; }
            Bmc_TwoRow(p, Mint);
            pAdded[Mint] = 1;
            nAdded++;
            if ( Bmc_TwoTerminate(p) ) { Status = 0; break; }
            clkCall = (abctime)clock();
            Status = Bmc_TwoSolveBsat(p, &nCalls);
            timeSolve += (abctime)clock()-clkCall;
            if ( pPars->fVerbose )
                printf("Refinement %d: row %d, %s, conflicts %d.\n", nAdded, Mint,
                       Status == 10 ? "SAT candidate" : Status == 20 ? "UNSAT" : "UNKNOWN",
                       sat_solver_nconflicts(p->pSat));
            if ( Status != 10 ) break;
            Mint = Bmc_TwoEval(p);
            if ( Mint == -1 ) { fVerified = 1; break; }
            if ( Mint == -2 ) { Status = -1; break; }
            if ( pRows )
                for ( i = 0; i < nRows; i++ )
                    if ( Abc_TtGetBit(Bmc_TwoTruth(p, p->nObjs-1), pRows[i]) != Abc_TtGetBit(p->pTruth, pRows[i]) )
                    { Mint = pRows[i]; break; }
        }
        if ( Status == 10 && !fVerified ) Status = 0;
    }
    else
    {
        // CaDiCaL and Kissat solve the complete formula in one call.
        for ( i = 0; i < nRows && !Bmc_TwoTerminate(p); i++ )
        {
            Mint = pRows ? pRows[i] : i+1;
            Bmc_TwoRow(p, Mint);
            pAdded[Mint] = 1;
            nAdded++;
        }
        if ( i == nRows && !Bmc_TwoTerminate(p) )
        {
            Bmc_TwoCofBounds(p);
            Bmc_TwoDiffAll(p);
            clkCall = (abctime)clock();
            Status = p->pCadical ? ccadical_solve(p->pCadical) : kissat_solve(p->pKissat);
            timeSolve += (abctime)clock()-clkCall;
            nCalls++;
            if ( Status == 10 )
            {
                fVerified = Bmc_TwoEval(p) == -1;
                if ( !fVerified ) Status = -1;
            }
        }
    }
    ABC_FREE(pRows);
    if ( Status < 0 ) Abc_Print(-1, "Internal error: synthesized circuit failed exhaustive verification.\n");
    printf("Nodes = %d : %s  Vars = %d  Clauses = %d  CPU = %.6f sec\n", nNodes,
           Status == 10 ? "SAT" : Status == 20 ? "UNSAT" : Status < 0 ? "ERROR" : "UNKNOWN",
           p->iVar, p->nClauses, (double)((abctime)clock()-clk)/CLOCKS_PER_SEC);
    if ( pPars->fVerbose )
    {
        printf("Construction and checking = %.6f sec.  Solving = %.6f sec.  Literals = %d.\n",
               (double)((abctime)clock()-clk-timeSolve)/CLOCKS_PER_SEC, (double)timeSolve/CLOCKS_PER_SEC, p->nLiterals);
        printf("Rows = %d/%d.  Solver calls = %d.\n", nAdded, nRows, nCalls);
        if ( p->pSat ) printf("Conflicts = %d.\n", sat_solver_nconflicts(p->pSat));
        else if ( p->pCadical ) printf("Conflicts = %d.\n", ccadical_conflicts(p->pCadical));
    }
    if ( p->pSat ) sat_solver_delete(p->pSat);
    else if ( p->pCadical ) ccadical_release(p->pCadical);
    else kissat_release(p->pKissat);
    p->pSat = NULL;
    p->pCadical = NULL;
    p->pKissat = NULL;
    // Export a complete formula, including rows unnecessary for this search.
    // The solver is already released; emission now only appends to vCnf.
    if ( p->vCnf && Status >= 0 )
    {
        if ( !fStarted )
        {
            // Replace the interrupted prefix, keeping the constant-true unit.
            Vec_IntClear(p->vCnf);
            p->nClauses = p->nLiterals = 0;
            Temp = 1;
            Bmc_TwoEmit(p, &Temp, 1);
            p->timeStop = 0;
            Bmc_TwoStart(p);
            Bmc_TwoStrongOrder(p);
            Bmc_TwoStrongBounds(p);
            p->fCofAdded = p->fDiffAdded = 0;
        }
        for ( Mint = 1; Mint <= nRows; Mint++ ) if ( !pAdded[Mint] ) Bmc_TwoRow(p, Mint);
        p->timeStop = 0;
        Bmc_TwoCofBounds(p);
        Bmc_TwoDiffAll(p);
        if ( !Bmc_TwoDump(p) ) Status = -1;
    }
    if ( Status == 10 ) *ppGia = Bmc_TwoDerive(p);
    ABC_FREE(pAdded);
    Vec_IntFreeP(&p->vCnf);
    Vec_WrdFree(p->vInfo);
    Vec_WecFree(p->vOutLits);
    ABC_FREE(p->pTruth);
    ABC_FREE(p);
    return Status;
}

/**Function*************************************************************

  Synopsis    [Reads a nonnegative command-line integer without truncation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_TwoNumber( int argc, char ** argv, int c, int * pValue )
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

  Synopsis    [Prints the command usage.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_TwoUsage( void )
{
    Abc_Print(-2, "usage: twoexact2 [-NTSB <num>] [-madckgevh] [hex]\n");
    Abc_Print(-2, "\t          exact synthesis with two-input gates; replaces the current network\n");
    Abc_Print(-2, "\t          uses incremental bsat by default; -c and -k are mutually exclusive\n");
    Abc_Print(-2, "\t-N <num> : node count, 0..64; upper bound with -m [required]\n");
    Abc_Print(-2, "\t-T <num> : CPU time limit per node count in seconds [default = 0: unlimited]\n");
    Abc_Print(-2, "\t-B <num> : candidate CPU seconds per count with -g; 0 disables [default = 90]\n");
    Abc_Print(-2, "\t-S <num> : random seed for row order and solver, 0..2000000000 [default = 0]\n");
    Abc_Print(-2, "\t           seed 0 uses natural row order; Kissat has fixed internal options\n");
    Abc_Print(-2, "\t-m       : toggle minimum search from the coverage bound [default = no]\n");
    Abc_Print(-2, "\t           constants and literals need no gates; -T skips UNKNOWN\n");
    Abc_Print(-2, "\t-a       : toggle AND nodes with complemented edges only [default = no]\n");
    Abc_Print(-2, "\t-d       : toggle dumping complete CNFs to twoexact2_*.cnf [default = no]\n");
    Abc_Print(-2, "\t           completes CNF after search; export time is additional to -T\n");
    Abc_Print(-2, "\t-c       : toggle full-CNF CaDiCaL instead of incremental bsat [default = no]\n");
    Abc_Print(-2, "\t-k       : toggle full-CNF Kissat instead of incremental bsat [default = no]\n");
    Abc_Print(-2, "\t-g       : toggle candidate search and CaDiCaL repair, up to 6 inputs [default = no]\n");
    Abc_Print(-2, "\t           tries up to three seeds before exact search, within -B and -T\n");
    Abc_Print(-2, "\t           uses bundled CaDiCaL for repair; incompatible with -d\n");
    Abc_Print(-2, "\t-e       : toggle cofactor bounds and difference clauses [default = no]\n");
    Abc_Print(-2, "\t           for 3..5 essential inputs; difference clauses with -ma\n");
    Abc_Print(-2, "\t           uses smaller-function minima; no target circuit is stored\n");
    Abc_Print(-2, "\t-v       : toggle construction and solving details [default = no]\n");
    Abc_Print(-2, "\t-h       : print this help\n");
    Abc_Print(-2, "\t[hex]    : truth table, up to 1024 hex digits (12 inputs)\n");
    Abc_Print(-2, "\t           keep leading zeros; without hex, use the current single-output network\n");
}

/**Function*************************************************************

  Synopsis    [Implements twoexact2 independently of the original command.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTwoExact2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Bmc_EsPar_t Pars, * p = &Pars;
    Gia_Man_t * pGia = NULL;
    Bmc_Exact_t Target = {0};
    word * pTruth;
    abctime clk;
    int c, i, n, nVars, fNodes = 0, fSeed = 0, fBoost = 0, Status = 20, FirstUnknown = -1, Map[TWO_MAX_VARS];
    int nProbeSeconds = 90;
    Bmc_EsParSetDefault(p);
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "NTSBmadckgevh")) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( !Bmc_TwoNumber(argc, argv, c, &p->nNodes) ) return 1;
            fNodes = 1; break;
        case 'T': if ( !Bmc_TwoNumber(argc, argv, c, &p->RuntimeLim) ) return 1; break;
        case 'B': if ( !Bmc_TwoNumber(argc, argv, c, &nProbeSeconds) ) return 1; break;
        case 'S': if ( !Bmc_TwoNumber(argc, argv, c, &p->Seed) ) return 1; break;
        case 'm': p->fMinNodes ^= 1; break;
        case 'a': p->fOnlyAnd ^= 1; break;
        case 'd': p->fDumpCnf ^= 1; break;
        case 'c': p->fCadical ^= 1; break;
        case 'k': p->fKissat ^= 1; break;
        case 'g': fSeed ^= 1; break;
        case 'e': fBoost ^= 1; break;
        case 'v': p->fVerbose ^= 1; break;
        case 'h': Bmc_TwoUsage(); return 0;
        default:  Bmc_TwoUsage(); return 1;
        }
    }
    if ( !fNodes || p->nNodes > TWO_MAX_NODES || argc > globalUtilOptind+1 )
    {
        Abc_Print(-1, "Provide -N in 0..64 and at most one hexadecimal truth table.\n");
        return 1;
    }
    if ( p->fCadical && p->fKissat )
    {
        Abc_Print(-1, "Options -c and -k cannot be combined.\n");
        return 1;
    }
    if ( fSeed && p->fDumpCnf )
    {
        Abc_Print(-1, "Options -g and -d cannot be combined.\n");
        return 1;
    }
    if ( p->Seed > 2000000000 )
    {
        Abc_Print(-1, "The random seed must be in 0..2000000000 for all SAT solvers.\n");
        return 1;
    }
    p->pTtStr = argc > globalUtilOptind ? argv[globalUtilOptind] : NULL;
    if ( !Bmc_ExactRead(pAbc, p->pTtStr, -1, TWO_MAX_VARS, &Target) ) return 1;
    p->nVars = Target.nVars;
    pTruth = ABC_ALLOC(word, Abc_TtWordNum(p->nVars));
    Abc_TtCopy(pTruth, Target.pTruth, Abc_TtWordNum(p->nVars), 0);
    for ( i = 0; i < p->nVars; i++ ) Map[i] = i;
    nVars = Abc_TtMinBase(pTruth, Map, p->nVars, p->nVars);
    printf("twoexact2: %d inputs (%d essential), %s, seed %d.\n", p->nVars, nVars,
           p->fCadical ? "CaDiCaL" : p->fKissat ? "Kissat" : "bsat", p->Seed);
    clk = (abctime)clock();
    if ( nVars < 2 )
    {
        int Out = 0;
        pGia = Gia_ManStart(p->nVars+2);
        pGia->pName = Abc_UtilStrsav("twoexact2");
        for ( i = 0; i < p->nVars; i++ )
        {
            int Lit = Gia_ManAppendCi(pGia);
            if ( nVars && i == Map[0] ) Out = Lit;
        }
        Gia_ManAppendCo(pGia, Abc_LitNotCond(Out, (int)(pTruth[0]&1)));
        printf("Realization using 0 gates (verified):\n");
        if ( nVars ) printf("out = %s%c\n", pTruth[0]&1 ? "!" : "", 'a'+Map[0]);
        else printf("out = %d\n", (int)(pTruth[0]&1));
        printf("%s\n", p->fMinNodes ? "Minimum gate count = 0." : "Gate count = 0.");
        Status = 10;
    }
    else
    {
        for ( n = p->fMinNodes ? nVars-1 : p->nNodes; n <= p->nNodes; n++ )
        {
            if ( n < nVars-1 ) break;
            Status = Bmc_TwoSolve(p, pTruth, nVars, Map, n, fSeed, fBoost, nProbeSeconds, &pGia);
            if ( !Bmc_ExactContinue(Status, p->fMinNodes, p->RuntimeLim, n, &FirstUnknown) ) break;
        }
        if ( p->fMinNodes )
            Bmc_ExactReport(Status, FirstUnknown, n, p->nNodes, "gate", "");
        else if ( Status == 20 ) printf("No solution with %d gates.\n", p->nNodes);
        else if ( Status == 0 ) printf("Search stopped at %d gates; the result is undecided.\n", n);
    }
    if ( pGia && Bmc_ExactInstall(pAbc, pGia, &Target) ) pGia = NULL;
    else if ( pGia ) Status = -1;
    printf("Total CPU time = %.6f sec.\n", (double)((abctime)clock()-clk)/CLOCKS_PER_SEC);
    if ( pGia ) Gia_ManStop(pGia);
    ABC_FREE(pTruth);
    ABC_FREE(Target.pTruth);
    return Status < 0;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
