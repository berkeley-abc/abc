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
static void Bmc_TwoSymmetry( Bmc_TwoMan_t * p )
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
        a = Bmc_TwoNewVar(p);
        b = Bmc_TwoNewVar(p);
        y = Values[i] = i == p->nObjs-1 ? (Abc_TtGetBit(p->pTruth, Mint) ? 1 : -1) : Bmc_TwoNewVar(p);
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
    for ( i = 0; p->pPars->pTtStr[i]; i++ ) Hash = (Hash ^ (unsigned char)p->pPars->pTtStr[i]) * 16777619u;
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
        // bsat uses Abc_Clock(), which may measure wall time. Resume with
        // retained clauses if it expires before our CPU budget is consumed.
        if ( p->timeStop )
            sat_solver_set_runtime_limit(p->pSat, Abc_Clock() + p->timeStop - (abctime)clock());
        Status = sat_solver_solve(p->pSat, NULL, NULL, 0, 0, 0, 0);
        (*pnCalls)++;
    }
    while ( Status == l_Undef && !Bmc_TwoTerminate(p) );
    return Status == l_True ? 10 : Status == l_False ? 20 : 0;
}

/**Function*************************************************************

  Synopsis    [Solves one node count and returns SAT, UNSAT, or UNKNOWN.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_TwoSolve( Bmc_EsPar_t * pPars, word * pTruth, int nVars, int * pMap, int nNodes, Gia_Man_t ** ppGia )
{
    Bmc_TwoMan_t * p = ABC_CALLOC(Bmc_TwoMan_t, 1);
    abctime clk = (abctime)clock(), clkCall, timeSolve = 0;
    int i, j, Temp, Mint, Status = 0, fVerified = 0, fStarted, nAdded = 0, nCalls = 0;
    int * pRows = NULL, nRows = (1 << nVars)-1;
    unsigned char * pAdded = ABC_CALLOC(unsigned char, nRows+1);
    unsigned Random = (unsigned)pPars->Seed ^ 0x9e3779b9u;
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
        }
        for ( Mint = 1; Mint <= nRows; Mint++ ) if ( !pAdded[Mint] ) Bmc_TwoRow(p, Mint);
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
    Abc_Print(-2, "usage: twoexact2 [-NTR <num>] [-macskvh] <hex>\n");
    Abc_Print(-2, "           exact synthesis with two-input gates; stores a verified AIG in &-space\n");
    Abc_Print(-2, "           uses incremental bsat by default; -s and -k are mutually exclusive\n");
    Abc_Print(-2, " -N <num> : node count, 0..64; upper bound with -m [required]\n");
    Abc_Print(-2, " -T <num> : CPU time limit per node count in seconds [default = 0: unlimited]\n");
    Abc_Print(-2, " -R <num> : random seed for row order and solver, 0..2000000000 [default = 0]\n");
    Abc_Print(-2, "            seed 0 uses natural row order; Kissat has fixed internal options\n");
    Abc_Print(-2, " -m       : find a minimum, starting at essential inputs minus one\n");
    Abc_Print(-2, "            constants and literals need no gates; stop on UNKNOWN\n");
    Abc_Print(-2, " -a       : use only AND nodes with complemented edges [default = no]\n");
    Abc_Print(-2, " -c       : dump each complete CNF to twoexact2_*.cnf [default = no]\n");
    Abc_Print(-2, "            completes CNF after search; export time is additional to -T\n");
    Abc_Print(-2, " -s       : use full-CNF CaDiCaL instead of incremental bsat [default = no]\n");
    Abc_Print(-2, " -k       : use full-CNF Kissat instead of incremental bsat [default = no]\n");
    Abc_Print(-2, " -v       : print construction and solving details [default = no]\n");
    Abc_Print(-2, " -h       : print this help\n");
    Abc_Print(-2, " <hex>    : 1, 2, 4, ..., 1024 hex digits, without 0x (2..12 inputs)\n");
    Abc_Print(-2, "            keep leading zeros; least significant bit is the all-zero input\n");
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
    word * pTruth;
    abctime clk;
    int c, i, n, nVars, fNodes = 0, Status = 20, Map[TWO_MAX_VARS];
    Bmc_EsParSetDefault(p);
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "NTRmacskvh")) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( !Bmc_TwoNumber(argc, argv, c, &p->nNodes) ) return 1;
            fNodes = 1; break;
        case 'T': if ( !Bmc_TwoNumber(argc, argv, c, &p->RuntimeLim) ) return 1; break;
        case 'R': if ( !Bmc_TwoNumber(argc, argv, c, &p->Seed) ) return 1; break;
        case 'm': p->fMinNodes ^= 1; break;
        case 'a': p->fOnlyAnd ^= 1; break;
        case 'c': p->fDumpCnf ^= 1; break;
        case 's': p->fCadical ^= 1; break;
        case 'k': p->fKissat ^= 1; break;
        case 'v': p->fVerbose ^= 1; break;
        case 'h': Bmc_TwoUsage(); return 0;
        default:  Bmc_TwoUsage(); return 1;
        }
    }
    if ( !fNodes || p->nNodes > TWO_MAX_NODES || argc != globalUtilOptind+1 )
    {
        Abc_Print(-1, "Provide -N in 0..64 and exactly one hexadecimal truth table.\n");
        return 1;
    }
    if ( p->fCadical && p->fKissat )
    {
        Abc_Print(-1, "Options -s and -k cannot be combined.\n");
        return 1;
    }
    if ( p->Seed > 2000000000 )
    {
        Abc_Print(-1, "The random seed must be in 0..2000000000 for all SAT solvers.\n");
        return 1;
    }
    p->pTtStr = argv[globalUtilOptind];
    n = (int)strlen(p->pTtStr);
    if ( n < 1 || n > (1 << (TWO_MAX_VARS-2)) || (n & (n-1)) )
    {
        Abc_Print(-1, "Truth table needs a power-of-two number of hex digits, from 1 through 1024.\n");
        return 1;
    }
    for ( i = 0; i < n; i++ )
        if ( !Abc_TtIsHexDigit(p->pTtStr[i]) )
        {
            Abc_Print(-1, "Use only hexadecimal digits, without a leading 0x.\n");
            return 1;
        }
    p->nVars = 2 + (n == 1 ? 0 : Abc_Base2Log(n));
    pTruth = ABC_CALLOC(word, Abc_TtWordNum(p->nVars));
    Abc_TtReadHex(pTruth, p->pTtStr);
    if ( p->nVars < 6 ) pTruth[0] = Abc_Tt6Stretch(pTruth[0], p->nVars);
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
        printf("Minimum gate count = 0.\n");
        Status = 10;
    }
    else
    {
        for ( n = p->fMinNodes ? nVars-1 : p->nNodes; n <= p->nNodes; n++ )
        {
            if ( n < nVars-1 ) break;
            Status = Bmc_TwoSolve(p, pTruth, nVars, Map, n, &pGia);
            if ( Status != 20 ) break;
        }
        if ( p->fMinNodes && Status == 10 ) printf("Minimum gate count = %d.\n", n);
        else if ( Status == 20 ) printf("No solution %s %d gates.\n", p->fMinNodes ? "with at most" : "with", p->nNodes);
        else if ( Status == 0 ) printf("Search stopped at %d gates; the result is undecided.\n", n);
    }
    if ( pGia )
    {
        // Check the exported AIG, including restored input positions and phase.
        Abc_TtReadHex(pTruth, p->pTtStr);
        if ( p->nVars < 6 ) pTruth[0] = Abc_Tt6Stretch(pTruth[0], p->nVars);
        if ( !Abc_TtEqual(pTruth, Gia_ObjComputeTruthTable(pGia, Gia_ManPo(pGia, 0)), Abc_TtWordNum(p->nVars)) )
        {
            Abc_Print(-1, "Internal error: exported AIG failed exhaustive verification.\n");
            Gia_ManStop(pGia);
            pGia = NULL;
            Status = -1;
        }
        else
            Gia_ObjComputeTruthTableStop(pGia);
    }
    printf("Total CPU time = %.6f sec.\n", (double)((abctime)clock()-clk)/CLOCKS_PER_SEC);
    if ( pGia ) Abc_FrameUpdateGia(pAbc, pGia);
    ABC_FREE(pTruth);
    return Status < 0;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
