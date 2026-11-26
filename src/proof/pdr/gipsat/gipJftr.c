/**CFile****************************************************************

  FileName    [gipJftr.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [GipSAT.]

  Synopsis    [Justification-frontier search and register completion.]

  Author      [ChenWish]

  Affiliation []

  Date        [November 2026.]

  Revision    [$Id$]

  Description [This module was written for ABC. The solver uses the
  requested conflict budget to justify its assumptions on the circuit
  CNF. An early SAT candidate must cover the frame lemmas and the
  temporary constraints with one consistent register completion. A
  predecessor query also requests the leaves justifying its assumptions.
  The ordinary search continues from the assumptions if this search
  runs out of conflicts or cannot justify a candidate.]

***********************************************************************/

#include <limits.h>
#include "gipsat.h"

ABC_NAMESPACE_IMPL_START

// Gip_SolverSetJftr requests the mode for one query outside a batch. The eligible Cnf_DeriveOther
// encoding has a distinct variable for each represented AIG object, with fanins numbered before
// their gate. Gip_JftrEligible also checks the solver configuration. The caller supplies frame
// lemmas over register literals and the property is the only permitted non-leaf unit.
//
// A frontier decision satisfies an open gate clause, a temporary constraint or an uncovered lemma.
// Conflict analysis proceeds normally. The frontier preserves the decision queue and saved phases.
// An early answer consists of a partial assignment and one common value for each unassigned register.
// Every assigned node has a true literal in each defining clause, except that a root clause may
// contain an unassigned literal outside the domain. The completion covers every frame lemma and
// satisfies temporary constraints that rely on free registers outside the domain.
//
// For predecessor queries the walk marks leaves that imply the assumptions under the transition
// relation alone. Shrinking releases the other inputs and registers above level zero. The answer
// remains valid until the formula or assignment changes.

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

static inline int Gip_JftrPoll( Gip_Solver_t * p )
{
    if ( (++p->Jftr.nPoll & 4095u) == 0 && (p->TimeLimit || p->pFuncStop) && Gip_SolverTimedOut(p) )
        p->fCanceled = 1;
    return p->fCanceled;
}

// the dirty set of the lemma cover: one bit per lemma position, and one summary bit per word that is not zero
static inline void Gip_JftrCoverSetDirty( Gip_Solver_t * p, int pos )
{
    word * pW = p->Jftr.pDirty + (pos >> 6);
    if ( (*pW >> (pos & 63)) & 1 )
        return;
    *pW |= (word)1 << (pos & 63);
    p->Jftr.pDirtySummary[pos >> 12] |= (word)1 << ((pos >> 6) & 63);
}
static inline void Gip_JftrCoverClearDirty( Gip_Solver_t * p, int pos )
{
    word * pW = p->Jftr.pDirty + (pos >> 6);
    *pW &= ~((word)1 << (pos & 63));
    if ( *pW == 0 )
        p->Jftr.pDirtySummary[pos >> 12] &= ~((word)1 << ((pos >> 6) & 63));
}
// the count of covered positions starts again: a literal that covered a clause may not hold any more
static inline void Gip_JftrCoverRestart( Gip_Solver_t * p )
{
    p->Jftr.nCovered = 0;
    p->Jftr.iCoverStart = p->Jftr.iLo;
}

// a decision of the mode: the literal, of a var of the domain, becomes true at a new level
static inline void Gip_JftrDecideLit( Gip_Solver_t * p, int Lit )
{
    assert( Gip_DomainHas( &p->Domain, Gip_LitVar(Lit) ) );
    Gip_SolverNewLevel( p );
    Gip_SolverAssign( p, Lit, GIP_CREF_NONE );
    p->Stats.nDecisions++;
}

/**Function*************************************************************

  Synopsis    [Updates the frontier and lemma cover before a backtrack.]

  Description [Marks witnesses that may disappear when the trail is popped.
  The next frontier scan rechecks the retained assignments.]

***********************************************************************/
void Gip_SolverJftrBacktrack( Gip_Solver_t * p, int Level )
{
    int i, pos, nTrail = Vec_IntEntry( p->vPosInTrail, Level );
    p->Jftr.fWalkClosed = 0;
    Gip_JftrCoverRestart( p );
    // a witness that is true on the trail but not in pCompletion may be unassigned now
    if ( !p->Jftr.fCoverDirty )
        Vec_IntForEachEntry( p->Jftr.vVolatile, pos, i )
            if ( pos < Vec_IntSize(p->Cdb.vLemmas) )
                Gip_JftrCoverSetDirty( p, pos );
    Vec_IntClear( p->Jftr.vVolatile );
    if ( p->Jftr.iScan > nTrail )
        p->Jftr.iScan = nTrail;
    // a node below the backtrack point may have been justified by a popped literal: recheck from level 1
    if ( p->Jftr.fActive )
    {
        p->Jftr.iCheck = Level > 0 ? Vec_IntEntry( p->vPosInTrail, 0 ) : nTrail;
        p->Jftr.fRootRecheck = 1;   // a root node may have been closed by a popped literal too
        Vec_IntClear( p->Jftr.vFront );   // the next scan queues every node that can be open
    }
}

/**Function*************************************************************

  Synopsis    [Resumes ordinary search at the assumption level.]

  Description [A fixed domain keeps its decision queue. Other domains
  rebuild it after the speculative decisions have been undone.]

***********************************************************************/
void Gip_SolverJftrHandover( Gip_Solver_t * p, int Level )
{
    Gip_SolverBacktrack( p, Level, 0 );
    p->Jftr.fActive = 0;
    assert( Gip_SolverLevelOf(p) == Level );
    Gip_SolverPrepareVsids( p );
}

// Fills the per-var tables of the context: the kind, the register index, and pCost[4*v + 2*m + b] = the cost of
// making var v take value b in metric m (0: the registers that must be assigned; 1: SCOAP, every leaf and every gate
// counts 1). For a node: the minimum over its defining clauses with the literal (v = b) of the cost of making the
// other literals false.
#define GIP_JFTR_COST_MAX (1 << 28)
// the defining clauses of a var are clauses [Beg, Beg + Num) of the static CNF, which lists them by AIG object
static inline int Gip_JftrClaBeg( Gip_Ctx_t * p, int Var )
{
    return p->pCnf->pObj2Clause[p->pVar2Obj ? p->pVar2Obj[Var] : Var];
}
static inline int Gip_JftrClaNum( Gip_Ctx_t * p, int Var )
{
    return p->pCnf->pObj2Count[p->pVar2Obj ? p->pVar2Obj[Var] : Var];
}
static inline int Gip_JftrCostLitTrue( int * pCost, int Lit, int m )
{
    return pCost[(size_t)4 * Gip_LitVar(Lit) + 2 * m + (1 ^ Gip_LitCompl(Lit))];
}
/**Function*************************************************************

  Synopsis    [Computes gate costs and clause ranges for the circuit.]

  Description [Visits variables in topological order and computes both
  polarity costs for both metrics in one pass over each gate's clauses.
  The completed tables are shared by the owning PDR manager's frame solvers.]

***********************************************************************/
static int Gip_JftrPrepareCtx( Gip_Solver_t * pSat )
{
    Gip_Ctx_t * p = pSat->pCtx;
    Cnf_Dat_t * pCnf = p->pCnf;
    Aig_Obj_t * pObj;
    size_t nVars = (size_t)p->nVars + 1;
    int i, v, b, m, c;
    // one extra entry: the solvers' activation var is nVars
    if ( nVars > (size_t)-1 / (4 * sizeof(int)) || p->nVars == INT_MAX )
        return 0;
    p->pKind     = ABC_CALLOC( char, nVars );
    p->pCost     = ABC_CALLOC( int, 4 * nVars );
    p->pLoIdx    = ABC_ALLOC( int, nVars );
    p->pClsSplit = ABC_ALLOC( int, nVars );
    p->pClsPol0  = ABC_CALLOC( char, nVars );
    if ( !p->pKind || !p->pCost || !p->pLoIdx || !p->pClsSplit || !p->pClsPol0 )
        goto failed;
    for ( v = 0; v <= p->nVars; v++ )
    {
        if ( Gip_JftrPoll(pSat) )
            goto failed;
        p->pLoIdx[v] = -1;
        p->pClsSplit[v] = -1;
    }
    // inputs and register outputs by their position among the CIs
    Aig_ManForEachCi( p->pAig, pObj, i )
    {
        if ( Gip_JftrPoll(pSat) )
            goto failed;
        v = Gip_CtxObjVar( p, pObj );
        p->pKind[v] = i < Saig_ManPiNum(p->pAig) ? GIP_KIND_PI : GIP_KIND_LO;
        if ( i >= Saig_ManPiNum(p->pAig) )
            p->pLoIdx[v] = i - Saig_ManPiNum(p->pAig);
    }
    p->nLo = Aig_ManCiNum(p->pAig) - Saig_ManPiNum(p->pAig);
    for ( v = 0; v < p->nVars; v++ )
    {
        int * pCosts = p->pCost + (size_t)4 * v;
        if ( Gip_JftrPoll(pSat) )
            goto failed;
        pObj = Aig_ManObj( p->pAig, p->pVar2Obj ? p->pVar2Obj[v] : v );
        if ( pObj && Aig_ObjIsCo(pObj) )
            p->pKind[v] = GIP_KIND_CO;
        else if ( pObj && Aig_ObjIsNode(pObj) && Gip_JftrClaNum(p, v) > 0 )
            p->pKind[v] = GIP_KIND_NODE;
        // the leaves; the clauses of a node refer only to vars with smaller numbers (its cut leaves)
        if ( p->pKind[v] != GIP_KIND_NODE && p->pKind[v] != GIP_KIND_CO )
        {
            pCosts[0] = pCosts[1] = p->pKind[v] == GIP_KIND_LO;
            pCosts[2] = pCosts[3] = p->pKind[v] == GIP_KIND_PI || p->pKind[v] == GIP_KIND_LO;
            continue;
        }
        pCosts[0] = pCosts[1] = pCosts[2] = pCosts[3] = GIP_JFTR_COST_MAX;
        for ( c = Gip_JftrClaBeg(p, v); c < Gip_JftrClaBeg(p, v) + Gip_JftrClaNum(p, v); c++ )
        {
            int * pLit, Has[2] = { 0, 0 }, Sum[2] = { 0, 1 };
            if ( Gip_JftrPoll(pSat) )
                goto failed;
            for ( pLit = pCnf->pClauses[c]; pLit < pCnf->pClauses[c+1]; pLit++ )
            {
                if ( Gip_LitVar(*pLit) == v )
                    Has[1 ^ Gip_LitCompl(*pLit)] = 1;
                else
                {
                    if ( Gip_LitVar(*pLit) > v )
                        goto unordered;
                    for ( m = 0; m < 2; m++ )
                        Sum[m] = Abc_MinInt(GIP_JFTR_COST_MAX,
                            Sum[m] + Gip_JftrCostLitTrue(p->pCost, Gip_LitNot(*pLit), m));
                }
            }
            for ( b = 0; b < 2; b++ )
                if ( Has[b] )
                    for ( m = 0; m < 2; m++ )
                        pCosts[2*m + b] = Abc_MinInt(pCosts[2*m + b], Sum[m]);
        }
    }
    // pClsSplit / pClsPol0: a node with a value can only be open in a clause that contains its false literal. When the
    // clauses with one sign of the node's literal all come before those with the other, that group is a range.
    for ( v = 0; v < p->nVars; v++ )
    {
        int c0 = Gip_JftrClaBeg(p, v), c1 = c0 + Gip_JftrClaNum(p, v), Split = -1, Pol0 = -1, fOk = c1 > c0;
        if ( Gip_JftrPoll(pSat) )
            goto failed;
        for ( c = c0; c < c1 && fOk; c++ )
        {
            int * pLit, Pol = -1;
            for ( pLit = pCnf->pClauses[c]; pLit < pCnf->pClauses[c+1]; pLit++ )
                if ( Gip_LitVar(*pLit) == v )
                {
                    if ( Pol != -1 )
                        fOk = 0;   // the var twice in one clause
                    Pol = Gip_LitCompl( *pLit );
                }
            if ( Pol == -1 )
                fOk = 0;
            else if ( Pol0 == -1 )
                Pol0 = Pol;
            else if ( Pol != Pol0 && Split == -1 )
                Split = c;
            else if ( Pol == Pol0 && Split != -1 )
                fOk = 0;   // the first sign again after the second: not grouped
        }
        if ( c1 <= c0 )
            continue;
        if ( !fOk )
            goto unordered;
        p->pClsSplit[v] = Split == -1 ? c1 : Split;
        p->pClsPol0[v]  = (char)Pol0;
    }
    return 1;
unordered:
    p->fJftrOrder = 0;
failed:
    ABC_FREE( p->pKind );
    ABC_FREE( p->pCost );
    ABC_FREE( p->pLoIdx );
    ABC_FREE( p->pClsSplit );
    ABC_FREE( p->pClsPol0 );
    return 0;
}

// the index of the lowest set bit of a word that is not zero
static inline int Gip_JftrFirstBit( word w )
{
#if defined(__GNUC__) || defined(__clang__)
    return __builtin_ctzll( w );
#else
    int n = 0;
    if ( (w & ABC_CONST(0x00000000FFFFFFFF)) == 0 ) { n += 32; w >>= 32; }
    if ( (w & ABC_CONST(0x000000000000FFFF)) == 0 ) { n += 16; w >>= 16; }
    if ( (w & ABC_CONST(0x00000000000000FF)) == 0 ) { n +=  8; w >>=  8; }
    if ( (w & ABC_CONST(0x000000000000000F)) == 0 ) { n +=  4; w >>=  4; }
    if ( (w & ABC_CONST(0x0000000000000003)) == 0 ) { n +=  2; w >>=  2; }
    if ( (w & ABC_CONST(0x0000000000000001)) == 0 ) { n++; }
    return n;
#endif
}
// the first dirty position in [From, To), or -1
static int Gip_JftrCoverNextDirty( Gip_Solver_t * p, int From, int To )
{
    int iW, nW = (To + 63) >> 6;
    word w;
    if ( From >= To )
        return -1;
    iW = From >> 6;
    w = p->Jftr.pDirty[iW] & (~(word)0 << (From & 63));
    while ( w == 0 )
    {
        // the next word that is not zero, from the summary
        int iS;
        word s;
        if ( ++iW >= nW )
            return -1;
        iS = iW >> 6;
        s = p->Jftr.pDirtySummary[iS] & (~(word)0 << (iW & 63));
        while ( s == 0 )
        {
            if ( ++iS > ((nW - 1) >> 6) )
                return -1;
            s = p->Jftr.pDirtySummary[iS];
        }
        iW = (iS << 6) + Gip_JftrFirstBit( s );
        if ( iW >= nW )
            return -1;
        w = p->Jftr.pDirty[iW];
    }
    iW = (iW << 6) + Gip_JftrFirstBit( w );
    return iW < To ? iW : -1;
}
// room for the positions below nPos (new words are zero)
static int Gip_JftrCoverReserve( Gip_Solver_t * p, int nPos )
{
    int nW = (nPos + 63) >> 6, nOld = p->Jftr.nDirtyWords;
    int nSummary = (nW + 63) >> 6, nOldSummary = (nOld + 63) >> 6;
    word * pWords;
    if ( nW <= nOld )
        return 1;
    pWords = ABC_REALLOC( word, p->Jftr.pDirty, nW );
    if ( pWords == NULL )
        return 0;
    p->Jftr.pDirty = pWords;
    pWords = ABC_REALLOC( word, p->Jftr.pDirtySummary, nSummary );
    if ( pWords == NULL )
        return 0;
    p->Jftr.pDirtySummary = pWords;
    memset( p->Jftr.pDirty + nOld, 0, sizeof(word) * (nW - nOld) );
    memset( p->Jftr.pDirtySummary + nOldSummary, 0, sizeof(word) * (nSummary - nOldSummary) );
    p->Jftr.nDirtyWords = nW;
    return 1;
}
// the literal does not cover any more: the positions whose witness it is become dirty and leave its list
static void Gip_JftrCoverDirtyLit( Gip_Solver_t * p, int Lit )
{
    Vec_Int_t * vList = p->Jftr.pvWitPos[2 * p->pCtx->pLoIdx[Gip_LitVar(Lit)] + Gip_LitCompl(Lit)];
    int i, pos;
    if ( vList == NULL || Vec_IntSize(vList) == 0 )
        return;
    Vec_IntForEachEntry( vList, pos, i )
        if ( p->Jftr.pListedWit[pos] == Lit )
        {
            Gip_JftrCoverSetDirty( p, pos );
            p->Jftr.pListedWit[pos] = -1;
        }
    Vec_IntClear( vList );
}

// adds the lemma clause at this position of Cdb.vLemmas to the cover tables, as a dirty position
static int Gip_JftrCoverAdd( Gip_Solver_t * p, int pos )
{
    int Cref = Vec_IntEntry( p->Cdb.vLemmas, pos );
    int * pLits = Gip_ClaLits( &p->Cdb.Alloc, Cref ), nLits = Gip_ClaLen( &p->Cdb.Alloc, Cref );
    int i, fSat0 = 0;
    if ( pos >= p->Jftr.nLemmaAlloc )
    {
        int nNew, * pWits;
        char * pSat;
        // Cover positions and their cyclic distances are summed in an int.
        if ( pos > INT_MAX / 2 - 1024 )
            return 0;
        nNew = Abc_MaxInt( 2 * Abc_MinInt(p->Jftr.nLemmaAlloc, INT_MAX / 4), pos + 1024 );
        if ( (size_t)nNew > (size_t)-1 / sizeof(int) )
            return 0;
        pWits = ABC_REALLOC( int, p->Jftr.pWit, nNew );
        if ( pWits == NULL )
            return 0;
        p->Jftr.pWit = pWits;
        pWits = ABC_REALLOC( int, p->Jftr.pListedWit, nNew );
        if ( pWits == NULL )
            return 0;
        p->Jftr.pListedWit = pWits;
        pSat = ABC_REALLOC( char, p->Jftr.pRootSat, nNew );
        if ( pSat == NULL )
            return 0;
        p->Jftr.pRootSat = pSat;
        if ( !Gip_JftrCoverReserve(p, nNew) )
            return 0;
        p->Jftr.nLemmaAlloc = nNew;
    }
    for ( i = 0; i < nLits; i++ )
    {
        if ( Gip_LitVar(pLits[i]) >= p->nVars || p->pCtx->pKind[Gip_LitVar(pLits[i])] != GIP_KIND_LO )
            return 0;
        if ( Gip_SolverLitValue(p, pLits[i]) == GIP_TRUE && p->pLevel[Gip_LitVar(pLits[i])] == 0 )
            fSat0 = 1;
    }
    p->Jftr.pWit[pos]  = -1;
    p->Jftr.pRootSat[pos] = (char)fSat0;
    p->Jftr.pListedWit[pos] = -1;
    Gip_JftrCoverSetDirty( p, pos );   // a new position is examined before it is passed
    return 1;
}

/**Function*************************************************************

  Synopsis    [Rebuilds the cover from the frame lemma list at level zero.]

***********************************************************************/
static int Gip_JftrCoverRebuild( Gip_Solver_t * p )
{
    int i, pos, nLo = Abc_MaxInt(p->pCtx->nLo, 1);
    assert( Gip_SolverLevelOf(p) == 0 );
    if ( p->Jftr.pvWitPos == NULL )
    {
        if ( nLo > INT_MAX / 2 || (size_t)nLo > (size_t)-1 / (2 * sizeof(Vec_Int_t *)) )
            return 0;
        p->Jftr.pvWitPos = ABC_CALLOC( Vec_Int_t *, 2 * nLo );
        if ( p->Jftr.pvWitPos == NULL )
            return 0;
    }
    else
        for ( i = 0; i < 2 * p->pCtx->nLo; i++ )
        {
            if ( Gip_JftrPoll(p) )
                return 0;
            if ( p->Jftr.pvWitPos[i] )
                Vec_IntClear( p->Jftr.pvWitPos[i] );
        }
    Vec_IntClear( p->Jftr.vVolatile );
    if ( p->Jftr.nDirtyWords )
    {
        memset( p->Jftr.pDirty, 0, sizeof(word) * p->Jftr.nDirtyWords );
        memset( p->Jftr.pDirtySummary, 0, sizeof(word) * ((p->Jftr.nDirtyWords + 63) >> 6) );
    }
    // every position is dirty now, so the root trail up to here needs no look
    p->Jftr.nRootChecked = Vec_IntSize( p->vTrail );
    for ( pos = 0; pos < Vec_IntSize(p->Cdb.vLemmas); pos++ )
        if ( Gip_JftrPoll(p) || !Gip_JftrCoverAdd(p, pos) )
            return 0;
    p->Jftr.fCoverDirty = 0;
    if ( p->Jftr.pStats )
        p->Jftr.pStats->nRebuilds++;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Extends the cover when a frame lemma is attached.]

  Description [A failed extension invalidates the cover for the next query.]

***********************************************************************/
void Gip_SolverJftrLemmaAdded( Gip_Solver_t * p )
{
    if ( !p->Jftr.nConfLimit || p->Jftr.fCoverDirty )
        return;
    if ( !Gip_JftrCoverAdd(p, Vec_IntSize(p->Cdb.vLemmas) - 1) )
        p->Jftr.fCoverDirty = 1;
}

// start of a solve in the mode: the root facts since the last look falsify the witnesses on their other literal
static void Gip_JftrCoverRoot( Gip_Solver_t * p )
{
    int i, Lit;
    assert( p->Jftr.nRootChecked <= Vec_IntSize(p->vTrail) );   // the root trail only grows
    for ( i = p->Jftr.nRootChecked; i < Vec_IntSize(p->vTrail); i++ )
    {
        if ( Gip_JftrPoll(p) )
            return;
        Lit = Vec_IntEntry( p->vTrail, i );
        if ( Gip_LitVar(Lit) < p->nVars && p->pCtx->pKind[Gip_LitVar(Lit)] == GIP_KIND_LO )
            Gip_JftrCoverDirtyLit( p, Gip_LitNot(Lit) );
    }
    p->Jftr.nRootChecked = Vec_IntSize( p->vTrail );
}

// the mode is defined for this solver and its context (see the contract at the top of the file)
static int Gip_JftrEligible( Gip_Solver_t * p )
{
    Gip_Ctx_t * pCtx = p->pCtx;
    if ( !pCtx->fJftrCnf || !pCtx->fJftrOrder || pCtx->iUnusedPiVar >= 0 )
        return 0;
    if ( pCtx->nVars != pCtx->pCnf->nVars )
        return 0;
    if ( p->pShared || p->Jftr.fCopied || p->pLoaded || p->nRecycleMode || p->fJustify || p->fInputDecisions )
        return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Retires the previous answer and consumes the next query's request.]

***********************************************************************/
void Gip_SolverJftrBegin( Gip_Solver_t * p, int fBatch )
{
    // the trail of a solve that ended in the mode is retired with fActive still set, so that no phase is saved
    if ( p->Jftr.fActive )
    {
        Gip_SolverBacktrack( p, 0, p->fTempDomain );
        p->Jftr.fActive = 0;
    }
    p->Jftr.fEarly = p->Jftr.fWalkClosed = 0;
    p->Jftr.Mode = p->Jftr.nConfLimit > 0 && !fBatch && Gip_JftrEligible( p ) ? p->Jftr.Request : GIP_JFTR_NONE;
    p->Jftr.Request = GIP_JFTR_NONE;
}

/**Function*************************************************************

  Synopsis    [Creates the private frontier state for a solver with a positive budget.]

***********************************************************************/
void Gip_SolverJftrInit( Gip_Solver_t * p )
{
    int nConfLimit = p->Jftr.nConfLimit;
    assert( nConfLimit > 0 );
    memset( &p->Jftr, 0, sizeof(Gip_Jftr_t) );
    p->Jftr.nConfLimit  = nConfLimit;
    p->Jftr.fCoverDirty = 1;   // no cover tables yet
    p->Jftr.vFront      = Vec_IntAlloc( 100 );
    p->Jftr.vMarked     = Vec_IntAlloc( 100 );
    p->Jftr.vRootOpen   = Vec_IntAlloc( 16 );
    p->Jftr.vCst        = Vec_IntAlloc( 4 );
    p->Jftr.vCstWit     = Vec_IntAlloc( 4 );
    p->Jftr.vCstFree    = Vec_IntAlloc( 4 );
    p->Jftr.vVolatile   = Vec_IntAlloc( 64 );
}

/**Function*************************************************************

  Synopsis    [Prepares the cover and initial register values for a frontier query.]

  Description [Enables frontier decisions after preparation completes.
  A resource failure releases the optional solver data. The caller
  returns undecided if a deadline or stop callback interrupted preparation.]

***********************************************************************/
void Gip_SolverJftrStart( Gip_Solver_t * p, int * pAssump, int nAssump )
{
    Aig_Obj_t * pLo;
    int i;
    if ( p->pCtx->pKind == NULL && !Gip_JftrPrepareCtx(p) )
        goto failed;
    if ( p->Jftr.fCoverDirty && !Gip_JftrCoverRebuild(p) )
        goto failed;
    Gip_JftrCoverRoot( p );
    if ( p->fCanceled )
        goto failed;
    Vec_IntClear( p->Jftr.vFront );
    if ( p->Jftr.pCur == NULL )
    {
        p->Jftr.pCur = ABC_ALLOC( unsigned char, p->nVarsAlloc );
        if ( p->Jftr.pCur == NULL )
            goto failed;
    }
    if ( p->Jftr.pCompletion == NULL )
    {
        // the completion starts as the saved phases (no phase = false, as in the ordinary decision)
        p->Jftr.pCompletion = ABC_ALLOC( char, Abc_MaxInt(p->pCtx->nLo, 1) );
        if ( p->Jftr.pCompletion == NULL )
            goto failed;
        Saig_ManForEachLo( p->pCtx->pAig, pLo, i )
        {
            int Var = Gip_CtxObjVar( p->pCtx, pLo );
            if ( Gip_JftrPoll(p) )
            {
                ABC_FREE( p->Jftr.pCompletion );
                goto failed;
            }
            p->Jftr.pCompletion[i] = p->pPhase[Var] == GIP_TRUE ? GIP_TRUE : GIP_FALSE;
        }
    }
    p->Jftr.iScan = p->Jftr.iCheck = Vec_IntSize( p->vTrail );
    p->Jftr.iLo = 0;
    Gip_JftrCoverRestart( p );
    // the caller's array, read only during the solve
    p->Jftr.pAssump = pAssump;
    p->Jftr.nAssump = nAssump;
    p->Jftr.fRootRecheck = 1;
    Vec_IntClear( p->Jftr.vCstFree );
    p->Jftr.fActive = 1;
    return;
failed:
    p->Jftr.Mode = GIP_JFTR_NONE;
    p->Jftr.fCoverDirty = 1;
    if ( !p->fCanceled )
    {
        Gip_SolverJftrFree( p );
        memset( &p->Jftr, 0, sizeof(p->Jftr) );
    }
}

/**Function*************************************************************

  Synopsis    [Frees the frontier data owned by this solver.]

***********************************************************************/
void Gip_SolverJftrFree( Gip_Solver_t * p )
{
    int i;
    ABC_FREE( p->Jftr.pWit );
    ABC_FREE( p->Jftr.pRootSat );
    ABC_FREE( p->Jftr.pCur );
    ABC_FREE( p->Jftr.pCompletion );
    if ( p->Jftr.pvWitPos )
        for ( i = 0; i < 2 * p->pCtx->nLo; i++ )
            Vec_IntFreeP( &p->Jftr.pvWitPos[i] );
    ABC_FREE( p->Jftr.pvWitPos );
    ABC_FREE( p->Jftr.pDirty );
    ABC_FREE( p->Jftr.pDirtySummary );
    ABC_FREE( p->Jftr.pListedWit );
    Vec_IntFreeP( &p->Jftr.vFront );
    Vec_IntFreeP( &p->Jftr.vMarked );
    Vec_IntFreeP( &p->Jftr.vRootOpen );
    Vec_IntFreeP( &p->Jftr.vCst );
    Vec_IntFreeP( &p->Jftr.vCstWit );
    Vec_IntFreeP( &p->Jftr.vCstFree );
    Vec_IntFreeP( &p->Jftr.vVolatile );
}

// the register literal is true in pCompletion
static inline int Gip_JftrLitCompleted( Gip_Solver_t * p, int Lit )
{
    return p->Jftr.pCompletion[p->pCtx->pLoIdx[Gip_LitVar(Lit)]] == (1 ^ Gip_LitCompl(Lit));
}
// the register literal holds in the completion: it is true, or unassigned and true in pCompletion
static inline int Gip_JftrLitCovers( Gip_Solver_t * p, int Lit )
{
    int v = Gip_SolverLitValue(p, Lit);
    return v == GIP_TRUE || (v == GIP_NONE && Gip_JftrLitCompleted(p, Lit));
}
// the position is covered (settled at level 0, or by its witness): it becomes clean, is put on the list of its
// witness, and on the volatile list when the witness is true on the trail but not in pCompletion
static inline void Gip_JftrCoverClean( Gip_Solver_t * p, int pos )
{
    int Wit = p->Jftr.pWit[pos];
    Gip_JftrCoverClearDirty( p, pos );
    if ( p->Jftr.pRootSat[pos] )
        return;
    if ( p->Jftr.pListedWit[pos] != Wit )
    {
        Vec_Int_t ** ppList = p->Jftr.pvWitPos + 2 * p->pCtx->pLoIdx[Gip_LitVar(Wit)] + Gip_LitCompl(Wit);
        if ( *ppList == NULL )
            *ppList = Vec_IntAlloc( 8 );
        else if ( Vec_IntSize(*ppList) >= 64 && (Vec_IntSize(*ppList) & (Vec_IntSize(*ppList) - 1)) == 0 )
        {
            // drops the stale entries (positions whose witness changed since they were listed) at each doubling
            int i, k = 0, q;
            Vec_IntForEachEntry( *ppList, q, i )
                if ( p->Jftr.pListedWit[q] == Wit )
                    Vec_IntWriteEntry( *ppList, k++, q );
            Vec_IntShrink( *ppList, k );
        }
        Vec_IntPush( *ppList, pos );
        p->Jftr.pListedWit[pos] = Wit;
    }
    if ( !Gip_JftrLitCompleted(p, Wit) )
        Vec_IntPush( p->Jftr.vVolatile, pos );
}
// the literal is true under the value the ordinary search would give its var: the saved phase, false when there is none
static inline int Gip_JftrLitPreferred( Gip_Solver_t * p, int Lit )
{
    int Ph = p->pPhase[Gip_LitVar(Lit)];
    return Ph == GIP_NONE ? Gip_LitCompl(Lit) : Ph == (char)(1 ^ Gip_LitCompl(Lit));
}

// the literal of a lemma / constraint clause to make true: the last unassigned one that is preferred
// (Gip_JftrLitPreferred), else the first unassigned one. Returns -1 when the clause has a true literal (*pTrueLit)
// or is falsified (*pTrueLit = -1)
static inline int Gip_JftrPickClauseLit( Gip_Solver_t * p, int Cref, int * pTrueLit )
{
    int * pLits = Gip_ClaLits( &p->Cdb.Alloc, Cref ), nLits = Gip_ClaLen( &p->Cdb.Alloc, Cref );
    int i, Best = -1;
    *pTrueLit = -1;
    for ( i = 0; i < nLits; i++ )
    {
        int Lit = pLits[i], v = Gip_SolverLitValue(p, Lit);
        if ( v == GIP_TRUE )
        {
            *pTrueLit = Lit;
            return -1;
        }
        if ( v != GIP_NONE )
            continue;
        if ( Best == -1 || Gip_JftrLitPreferred(p, Lit) )
            Best = Lit;
    }
    return Best;
}

// the clauses of Var with its false literal: a range [*pc0, *pc1), as the clauses of a var are grouped by the sign
// of its literal in the CNF the mode accepts
static inline void Gip_JftrFalseRange( Gip_Solver_t * p, int Var, int * pc0, int * pc1 )
{
    int Split = p->pCtx->pClsSplit[Var];
    assert( Split >= 0 );
    // the false literal is negative when the value is true
    if ( (p->pValue[Var] == GIP_TRUE) == (int)p->pCtx->pClsPol0[Var] )
        *pc0 = Gip_JftrClaBeg( p->pCtx, Var ), *pc1 = Split;
    else
        *pc0 = Split, *pc1 = Gip_JftrClaBeg( p->pCtx, Var ) + Gip_JftrClaNum( p->pCtx, Var );
}
// a defining clause of the assigned var that has no true literal, or -1 (clause index into the static CNF): over the
// clauses with the var's false literal only (the others contain its true literal) and resumed at the var's cursor
// pCur: the clauses before it were found satisfied since the var was queued, and stay satisfied until a backtrack,
// after which the scan queues the var again (iCheck)
static inline int Gip_JftrOpenClauseRange( Gip_Solver_t * p, int Var )
{
    Cnf_Dat_t * pCnf = p->pCtx->pCnf;
    int Off, c0, c1;
    Gip_JftrFalseRange( p, Var, &c0, &c1 );
    for ( Off = p->Jftr.pCur[Var]; Off < c1 - c0; Off++ )
    {
        int c = c0 + Off, * pLit, * pStop = pCnf->pClauses[c+1];
        for ( pLit = pCnf->pClauses[c]; pLit < pStop; pLit++ )
        {
            if ( Gip_SolverLitValue(p, *pLit) == GIP_TRUE )
                break;
        }
        if ( pLit == pStop )
            break;
    }
    // A longer verified prefix can safely be rescanned from the last representable offset.
    p->Jftr.pCur[Var] = (unsigned char)Abc_MinInt( Off, UCHAR_MAX );
    return Off < c1 - c0 ? c0 + Off : -1;
}
// The var was propagated by one of its own defining clauses that is still whole (GIP_CLA_WHOLE): the var has the
// largest number in its defining clauses, so its assigned fanins force the value and no clause of it is open while
// it stays assigned. A stored clause that lost a literal at level 0 may be the clause of a fanout and does not count.
static inline int Gip_JftrOwnWhole( Gip_Solver_t * p, int Var )
{
    int Cref = p->pReason[Var], * pLits, nLits, k;
    if ( Cref == GIP_CREF_NONE || !Gip_ClaIsWholeTrans(&p->Cdb.Alloc, Cref) )
        return 0;
    pLits = Gip_ClaLits( &p->Cdb.Alloc, Cref );
    nLits = Gip_ClaLen( &p->Cdb.Alloc, Cref );
    for ( k = 0; k < nLits; k++ )
        if ( Gip_LitVar(pLits[k]) > Var )
            return 0;
    return 1;
}
// queues a var assigned above level 0 for examination from its first clause
static inline void Gip_JftrQueue( Gip_Solver_t * p, int Var )
{
    p->Jftr.pCur[Var] = 0;
    Vec_IntPush( p->Jftr.vFront, Var );
}

// the literal of the open clause to make true: first by the var's preferred value (Gip_JftrLitPreferred), then inputs,
// registers whose saved phase agrees, other registers, nodes; then by the lower cost in metric 0, in metric 1, and by
// the lower activity
static inline int Gip_JftrPickLit( Gip_Solver_t * p, int c )
{
    Cnf_Dat_t * pCnf = p->pCtx->pCnf;
    char * pKind = p->pCtx->pKind;
    int * pLit, * pStop = pCnf->pClauses[c+1], Best = -1;
    int bestTier = 0, bestC0 = 0, bestC1 = 0;
    double bestAct = 0;
    for ( pLit = pCnf->pClauses[c]; pLit < pStop; pLit++ )
    {
        int Lit = *pLit, Var = Gip_LitVar( Lit ), tier, c0, c1;
        double act;
        if ( Gip_SolverLitValue(p, Lit) != GIP_NONE )
            continue;
        if ( pKind[Var] == GIP_KIND_PI )
            tier = 0;
        else if ( pKind[Var] == GIP_KIND_LO )
            tier = p->pPhase[Var] == (char)(1 ^ Gip_LitCompl(Lit)) ? 1 : 2;
        else
            tier = 3;
        tier = (Gip_JftrLitPreferred(p, Lit) ? 0 : 4) + tier;
        c0 = Gip_JftrCostLitTrue( p->pCtx->pCost, Lit, 0 );
        c1 = Gip_JftrCostLitTrue( p->pCtx->pCost, Lit, 1 );
        act = p->Vsids.Act.pAct[Var];
        if ( Best == -1 || tier < bestTier || (tier == bestTier && (c0 < bestC0 || (c0 == bestC0 &&
             (c1 < bestC1 || (c1 == bestC1 && act < bestAct))))) )
        {
            Best = Lit; bestTier = tier; bestC0 = c0; bestC1 = c1; bestAct = act;
        }
    }
    return Best;
}

// The justification walk from the assumptions. Every node reached must be closed; in each defining clause with its
// false literal the first true literal of minimum cost is the justification: its var is marked, and walked when it
// is a node or an output. Returns -1 when the walk closes, with the leaves (inputs, registers) marked; else the first
// open var.
static int Gip_JftrWalk( Gip_Solver_t * p )
{
    Cnf_Dat_t * pCnf = p->pCtx->pCnf;
    char * pKind = p->pCtx->pKind;
    Vec_Int_t * vStack = p->Jftr.vFront;   // scratch: the frontier is empty when the walk runs
    int i, Var, Open = -1;
    assert( Vec_IntSize(vStack) == 0 );
    for ( i = 0; i < p->Jftr.nAssump; i++ )
    {
        Var = Gip_LitVar( p->Jftr.pAssump[i] );
        if ( Var >= p->nVars || p->pMark[Var] )
            continue;
        p->pMark[Var] = 1;
        Vec_IntPush( p->Jftr.vMarked, Var );
        if ( pKind[Var] == GIP_KIND_NODE || pKind[Var] == GIP_KIND_CO )
            Vec_IntPush( vStack, Var );
    }
    while ( Vec_IntSize(vStack) > 0 && Open == -1 )
    {
        int FalseLit, c, c0, c1;
        if ( Gip_JftrPoll(p) )
            break;
        Var = Vec_IntPop( vStack );
        assert( p->pValue[Var] != GIP_NONE );   // an assumption, or the var of a true literal
        FalseLit = Gip_Lit( Var, p->pValue[Var] == GIP_TRUE );
        c0 = Gip_JftrClaBeg( p->pCtx, Var );
        c1 = c0 + Gip_JftrClaNum( p->pCtx, Var );
        for ( c = c0; c < c1; c++ )
        {
            int * pLit, * pStop = pCnf->pClauses[c+1], fHasFalse = 0, Sat = -1, SatCost = 0;
            // a clause that starts with the var's true literal adds nothing: it lacks the false literal, or is
            // justified by the var itself, which is marked
            if ( pCnf->pClauses[c] < pStop && pCnf->pClauses[c][0] == Gip_LitNot(FalseLit) )
                continue;
            for ( pLit = pCnf->pClauses[c]; pLit < pStop; pLit++ )
            {
                int u = Gip_LitVar( *pLit ), Cost;
                if ( *pLit == FalseLit )
                {
                    fHasFalse = 1;
                    continue;
                }
                if ( Gip_SolverLitValue(p, *pLit) != GIP_TRUE )
                    continue;
                // by cost: a var already in the walk, a level-0 fact, an input, a node, a register
                Cost = p->pMark[u] ? 0 : p->pLevel[u] == 0 ? 1 :
                       pKind[u] == GIP_KIND_PI ? 2 : pKind[u] == GIP_KIND_LO ? 4 : 3;
                if ( Sat == -1 || Cost < SatCost )
                {
                    Sat = *pLit;
                    SatCost = Cost;
                }
            }
            if ( !fHasFalse )
                continue;
            if ( Sat == -1 )
            {
                Open = Var;
                break;
            }
            {
                int u = Gip_LitVar( Sat );
                if ( p->pMark[u] )
                    continue;
                p->pMark[u] = 1;
                Vec_IntPush( p->Jftr.vMarked, u );
                if ( pKind[u] == GIP_KIND_NODE || pKind[u] == GIP_KIND_CO )
                    Vec_IntPush( vStack, u );
            }
        }
    }
    Vec_IntClear( vStack );
    return Open;
}

// clears the marks of the walk
static void Gip_JftrUnmark( Gip_Solver_t * p )
{
    int i, Var;
    Vec_IntForEachEntry( p->Jftr.vMarked, Var, i )
        p->pMark[Var] = 0;
    Vec_IntClear( p->Jftr.vMarked );
}
// the shrink of an early answer: the inputs and registers assigned above level 0 that are not leaves of the walk are
// unassigned. The trail keeps them: the next backtrack pops them like any other entry.
static void Gip_JftrShrinkModel( Gip_Solver_t * p )
{
    char * pKind = p->pCtx->pKind;
    int i, Var, iRootEnd = Gip_SolverLevelOf(p) > 0 ? Vec_IntEntry( p->vPosInTrail, 0 ) : Vec_IntSize( p->vTrail );
    for ( i = iRootEnd; i < Vec_IntSize(p->vTrail); i++ )
    {
        Var = Gip_LitVar( Vec_IntEntry(p->vTrail, i) );
        if ( Var < p->nVars && (pKind[Var] == GIP_KIND_PI || pKind[Var] == GIP_KIND_LO) && !p->pMark[Var] )
            Gip_SolverSetNone( p, Var );
    }
}

// as Gip_JftrOpenClauseRange over every clause of the var, but only a literal true at level 0 closes a clause: the
// classification of a root node
static int Gip_JftrOpenClauseRoot( Gip_Solver_t * p, int Var )
{
    Cnf_Dat_t * pCnf = p->pCtx->pCnf;
    int FalseLit = Gip_Lit( Var, p->pValue[Var] == GIP_TRUE );
    int c, c0 = Gip_JftrClaBeg( p->pCtx, Var ), c1 = c0 + Gip_JftrClaNum( p->pCtx, Var );
    for ( c = c0; c < c1; c++ )
    {
        int * pLit, * pStop = pCnf->pClauses[c+1], fHasFalse = 0, fSat = 0;
        for ( pLit = pCnf->pClauses[c]; pLit < pStop; pLit++ )
        {
            if ( *pLit == FalseLit )
                fHasFalse = 1;
            else if ( Gip_SolverLitValue(p, *pLit) == GIP_TRUE && p->pLevel[Gip_LitVar(*pLit)] == 0 )
            {
                fSat = 1;
                break;
            }
        }
        if ( fHasFalse && !fSat )
            return c;
    }
    return -1;
}
// a defining clause of the root node that is open and whose unassigned literals are all in the domain, or -1. The
// propagation skips a clause with an unassigned literal outside the domain: such a clause does not constrain the
// answer. (The node itself may have left the domain: assigned vars are removed from it, their fanins stay.)
static int Gip_JftrOpenClauseDom( Gip_Solver_t * p, int Var )
{
    Cnf_Dat_t * pCnf = p->pCtx->pCnf;
    int FalseLit = Gip_Lit( Var, p->pValue[Var] == GIP_TRUE );
    int c, c0 = Gip_JftrClaBeg( p->pCtx, Var ), c1 = c0 + Gip_JftrClaNum( p->pCtx, Var );
    for ( c = c0; c < c1; c++ )
    {
        int * pLit, * pStop = pCnf->pClauses[c+1], fHasFalse = 0, fSkip = 0;
        for ( pLit = pCnf->pClauses[c]; pLit < pStop; pLit++ )
        {
            if ( *pLit == FalseLit )
                fHasFalse = 1;
            else if ( Gip_SolverLitValue(p, *pLit) == GIP_TRUE ||
                      (Gip_SolverLitValue(p, *pLit) == GIP_NONE && !Gip_DomainHas(&p->Domain, Gip_LitVar(*pLit))) )
            {
                fSkip = 1;
                break;
            }
        }
        if ( fHasFalse && !fSkip )
            return c;
    }
    return -1;
}
// The nodes assigned at level 0 (the asserted property and what it implies, learnt units) must be closed like the nodes
// assigned above it. vRootOpen keeps, across solves, those that no level-0 literal closes.
static void Gip_JftrRootUpdate( Gip_Solver_t * p )
{
    char * pKind = p->pCtx->pKind;
    int i, k, Var, iRootEnd = Gip_SolverLevelOf(p) > 0 ? Vec_IntEntry( p->vPosInTrail, 0 ) : Vec_IntSize( p->vTrail );
    assert( p->Jftr.nRootSeen <= iRootEnd );   // the root trail only grows
    if ( p->Jftr.nRootSeen == iRootEnd )
        return;
    for ( i = p->Jftr.nRootSeen; i < iRootEnd; i++ )
    {
        if ( Gip_JftrPoll(p) )
            return;
        Var = Gip_LitVar( Vec_IntEntry(p->vTrail, i) );
        if ( Var >= p->nVars || (pKind[Var] != GIP_KIND_NODE && pKind[Var] != GIP_KIND_CO) ||
             Gip_JftrClaNum( p->pCtx, Var ) == 0 )
            continue;
        if ( Gip_JftrOpenClauseRoot( p, Var ) >= 0 )
            Vec_IntPush( p->Jftr.vRootOpen, Var );
    }
    p->Jftr.nRootSeen = iRootEnd;
    k = 0;
    Vec_IntForEachEntry( p->Jftr.vRootOpen, Var, i )
    {
        if ( Gip_JftrPoll(p) )
            return;
        // the new root facts may have closed a kept node for good
        if ( p->pValue[Var] == GIP_NONE || p->pLevel[Var] != 0 || Gip_JftrOpenClauseRoot( p, Var ) < 0 )
            continue;
        Vec_IntWriteEntry( p->Jftr.vRootOpen, k++, Var );
    }
    Vec_IntShrink( p->Jftr.vRootOpen, k );
}
// queues the nodes that may have an open clause (the root nodes at the start and after a backtrack, the trail from the
// last scan on) and makes dirty the lemma positions whose witness a newly assigned register falsifies
static inline void Gip_JftrScan( Gip_Solver_t * p )
{
    char * pKind = p->pCtx->pKind;
    int i, Lit, Var, iFrom = Abc_MinInt( p->Jftr.iScan, p->Jftr.iCheck );
    if ( p->Jftr.fRootRecheck )
    {
        // the root nodes that are open in the current domain
        Gip_JftrRootUpdate( p );
        Vec_IntForEachEntry( p->Jftr.vRootOpen, Var, i )
        {
            if ( Gip_JftrPoll(p) )
                return;
            if ( Gip_JftrOpenClauseDom( p, Var ) >= 0 )
                Vec_IntPush( p->Jftr.vFront, Var );
        }
        p->Jftr.fRootRecheck = 0;
    }
    for ( i = iFrom; i < Vec_IntSize(p->vTrail); i++ )
    {
        if ( Gip_JftrPoll(p) )
            return;
        Lit = Vec_IntEntry( p->vTrail, i );
        Var = Gip_LitVar( Lit );
        if ( Var >= p->nVars )
            continue;
        if ( pKind[Var] == GIP_KIND_LO )
        {
            // assigned against pCompletion: a clause covered by the other literal is not covered any more
            if ( i >= p->Jftr.iScan && !Gip_JftrLitCompleted(p, Lit) && p->Jftr.nCovered > 0 )
                Gip_JftrCoverRestart( p );
            if ( i >= p->Jftr.iScan )
                Gip_JftrCoverDirtyLit( p, Gip_LitNot(Lit) );
        }
        // the root nodes are queued above
        else if ( i >= p->Jftr.iCheck && Gip_JftrClaNum( p->pCtx, Var ) > 0 && p->pLevel[Var] > 0 )
        {
            if ( !Gip_JftrOwnWhole(p, Var) )   // else closed by its own fanins for as long as it is assigned
                Gip_JftrQueue( p, Var );
        }
    }
    p->Jftr.iScan = p->Jftr.iCheck = Vec_IntSize( p->vTrail );
}

// the registers that the early answer assigned above level 0 take their values in pCompletion, before a shrink
// unassigns some of them: the answer is then "the assignment, else pCompletion" for every register
static void Gip_JftrCoverCommit( Gip_Solver_t * p )
{
    int i;
    if ( Gip_SolverLevelOf(p) == 0 )
        return;
    for ( i = Vec_IntEntry(p->vPosInTrail, 0); i < Vec_IntSize(p->vTrail); i++ )
    {
        int Lit = Vec_IntEntry( p->vTrail, i ), Var = Gip_LitVar( Lit );
        if ( Var < p->nVars && p->pCtx->pKind[Var] == GIP_KIND_LO )
            p->Jftr.pCompletion[p->pCtx->pLoIdx[Var]] = p->pValue[Var];
    }
    // no clean position is volatile now: a witness that is true above level 0 is true in pCompletion as well
    Vec_IntClear( p->Jftr.vVolatile );
}
// the lemma clause at this position is settled at level 0 or has a covering register literal, which becomes its witness
static inline int Gip_JftrLemmaCovered( Gip_Solver_t * p, int pos )
{
    int Wit, Cref, * pLits, nLits, k;
    if ( p->Jftr.pRootSat[pos] )
        return 1;
    Wit = p->Jftr.pWit[pos];
    if ( Wit >= 0 && Gip_JftrLitCovers(p, Wit) )
        return 1;
    Cref = Vec_IntEntry( p->Cdb.vLemmas, pos );
    pLits = Gip_ClaLits( &p->Cdb.Alloc, Cref );  nLits = Gip_ClaLen( &p->Cdb.Alloc, Cref );
    for ( k = 0; k < nLits; k++ )
    {
        if ( !Gip_JftrLitCovers(p, pLits[k]) )
            continue;
        // a literal true at level 0 is not a witness: the caller marks the clause as settled (pRootSat)
        if ( Gip_SolverLitValue(p, pLits[k]) == GIP_TRUE && p->pLevel[Gip_LitVar(pLits[k])] == 0 )
            continue;
        p->Jftr.pWit[pos] = pLits[k];
        return 1;
    }
    return 0;
}

// makes true a literal of a constraint clause of the round that has no true literal. Returns 1 after a decision, 0 when
// every constraint clause has a true literal or is left to a free register, and -1 if the completion fails
static int Gip_JftrDecideCst( Gip_Solver_t * p )
{
    int i, Lit;
    for ( i = 0; i < Vec_IntSize(p->Jftr.vCst); i++ )
    {
        int Cref = Vec_IntEntry( p->Jftr.vCst, i ), TrueLit, Wit = Vec_IntEntry( p->Jftr.vCstWit, i );
        if ( Gip_JftrPoll(p) )
            return -1;
        if ( Wit >= 0 && Gip_SolverLitValue(p, Wit) == GIP_TRUE )
            continue;
        if ( Gip_ClaIsRemoved(&p->Cdb.Alloc, Cref) )
            continue;
        {
            // A clause with an unassigned literal outside the domain is not enforced by the propagation, and a decision
            // must not assign a var outside the domain: the clause is left to that literal, which must be a register
            // literal, in the completion. vCstFree keeps one such literal per clause; they must not be opposite.
            int * pL = Gip_ClaLits( &p->Cdb.Alloc, Cref ), nL = Gip_ClaLen( &p->Cdb.Alloc, Cref );
            int k, fFree = 0, Pick = -1;
            for ( k = 0; k < nL; k++ )
                if ( Gip_SolverLitValue(p, pL[k]) == GIP_TRUE )
                    break;
            for ( k = k < nL ? nL : 0; k < nL; k++ )   // a clause with a true literal takes the ordinary path below
            {
                if ( Gip_SolverLitValue(p, pL[k]) != GIP_NONE || Gip_DomainHas( &p->Domain, Gip_LitVar(pL[k]) ) )
                    continue;
                fFree = 1;
                if ( Gip_LitVar(pL[k]) >= p->nVars || p->pCtx->pKind[Gip_LitVar(pL[k])] != GIP_KIND_LO )
                    return -1;
                if ( Vec_IntFind( p->Jftr.vCstFree, pL[k] ) >= 0 )
                {
                    Pick = -2;   // already recorded for this or another clause
                    break;
                }
                if ( Pick == -1 && Vec_IntFind( p->Jftr.vCstFree, Gip_LitNot(pL[k]) ) < 0 )
                    Pick = pL[k];
            }
            if ( fFree )
            {
                // conservative: one literal per clause is recorded in the order met
                if ( Pick == -1 )
                    return -1;
                if ( Pick >= 0 )
                {
                    Vec_IntPush( p->Jftr.vCstFree, Pick );
                    // the recorded polarity is the register's value in the completion of this answer
                    Gip_JftrCoverDirtyLit( p, Gip_LitNot(Pick) );
                    p->Jftr.pCompletion[p->pCtx->pLoIdx[Gip_LitVar(Pick)]] = Gip_LitCompl(Pick) ? GIP_FALSE : GIP_TRUE;
                    Gip_JftrCoverRestart( p );
                }
                continue;
            }
        }
        Lit = Gip_JftrPickClauseLit( p, Cref, &TrueLit );
        if ( Lit == -1 )
        {
            if ( TrueLit < 0 )
                return -1;
            Vec_IntWriteEntry( p->Jftr.vCstWit, i, TrueLit );
            continue;
        }
        Vec_IntWriteEntry( p->Jftr.vCstWit, i, Lit );
        Gip_JftrDecideLit( p, Lit );
        return 1;
    }
    return 0;
}

static inline int Gip_JftrCheckDefined( Gip_Solver_t * p, int Var )
{
    char Kind = p->pCtx->pKind[Var];
    return (Kind == GIP_KIND_NODE || Kind == GIP_KIND_CO) && Gip_JftrClaNum( p->pCtx, Var ) > 0;
}
static inline int Gip_JftrCheckLit( Gip_Solver_t * p, char * pVal, int Lit )
{
    int Var = Gip_LitVar( Lit ), v = Var < p->nVars ? pVal[Var] : p->pValue[Var];
    return v == GIP_NONE ? GIP_NONE : (v == GIP_TRUE) != Gip_LitCompl(Lit) ? GIP_TRUE : GIP_FALSE;
}
// 1 = the clause has a true literal, 0 = every literal is false, -1 = a literal has no value and none is true
static int Gip_JftrCheckClause( Gip_Solver_t * p, char * pVal, int * pLits, int * pStop )
{
    int fNone = 0;
    for ( ; pLits < pStop; pLits++ )
    {
        int v = Gip_JftrCheckLit( p, pVal, *pLits );
        if ( v == GIP_TRUE )
            return 1;
        fNone |= v == GIP_NONE;
    }
    return fNone ? -1 : 0;
}
// the assigned node has a defining clause without a true literal; for a node assigned at level 0, a clause with an
// unassigned literal outside the domain does not count
static int Gip_JftrCheckOpen( Gip_Solver_t * p, int Var )
{
    Cnf_Dat_t * pCnf = p->pCtx->pCnf;
    int c, c0 = Gip_JftrClaBeg( p->pCtx, Var ), c1 = c0 + Gip_JftrClaNum( p->pCtx, Var ), * pLit;
    for ( c = c0; c < c1; c++ )
    {
        int fOutside = 0;
        for ( pLit = pCnf->pClauses[c]; pLit < pCnf->pClauses[c+1]; pLit++ )
        {
            if ( Gip_SolverLitValue(p, *pLit) == GIP_TRUE )
                break;
            fOutside |= Gip_SolverLitValue(p, *pLit) == GIP_NONE && !Gip_DomainHas( &p->Domain, Gip_LitVar(*pLit) );
        }
        if ( pLit == pCnf->pClauses[c+1] && !(fOutside && p->pLevel[Var] == 0) )
            return 1;
    }
    return 0;
}
// gives the node the value for which each of its defining clauses has a true literal. Returns 0 when there is none or
// when another var of these clauses is in the domain and has no value; such a var outside the domain leaves the node
// without a value
static int Gip_JftrCheckNode( Gip_Solver_t * p, char * pVal, int Var )
{
    Cnf_Dat_t * pCnf = p->pCtx->pCnf;
    int v, c, c0 = Gip_JftrClaBeg( p->pCtx, Var ), c1 = c0 + Gip_JftrClaNum( p->pCtx, Var ), * pLit, fOutside = 0;
    for ( c = c0; c < c1; c++ )
        for ( pLit = pCnf->pClauses[c]; pLit < pCnf->pClauses[c+1]; pLit++ )
            if ( Gip_LitVar(*pLit) != Var && Gip_JftrCheckLit( p, pVal, *pLit ) == GIP_NONE )
            {
                if ( Gip_DomainHas( &p->Domain, Gip_LitVar(*pLit) ) )
                    return 0;
                fOutside = 1;
            }
    if ( fOutside )
        return 1;
    for ( v = GIP_FALSE; v <= GIP_TRUE; v++ )
    {
        pVal[Var] = (char)v;
        for ( c = c0; c < c1; c++ )
            if ( Gip_JftrCheckClause( p, pVal, pCnf->pClauses[c], pCnf->pClauses[c+1] ) != 1 )
                break;
        if ( c == c1 )
            return 1;
    }
    pVal[Var] = GIP_NONE;
    return 0;
}
/**Function*************************************************************

  Synopsis    [Checks a candidate before shrinking the partial assignment.]

  Description [Checks assigned nodes, the assumptions and the clauses
  against the register completion. An unassigned literal outside the
  query domain can leave a clause undecided.]

***********************************************************************/
static int Gip_JftrCheck( Gip_Solver_t * p )
{
    Cnf_Dat_t * pCnf = p->pCtx->pCnf;
    Vec_Int_t * vLists[3] = { p->Cdb.vLemmas, p->Cdb.vLearnt, p->Cdb.vTemp };   // vTemp has the constraint clauses
    char * pKind = p->pCtx->pKind, * pVal = ABC_ALLOC( char, p->nVars );
    const char * pFail = NULL;
    int i, k, c, c1, Var, Lit, Cref;
    if ( pVal == NULL )
    {
        p->Jftr.fCoverDirty = 1;
        return 0;
    }
    Vec_IntForEachEntry( p->vTrail, Lit, i )
    {
        if ( Gip_JftrPoll(p) )
            goto cleanup;
        Var = Gip_LitVar( Lit );
        if ( Var < p->nVars && Gip_JftrCheckDefined( p, Var ) && Gip_JftrCheckOpen( p, Var ) )
            pFail = "an assigned node has an open defining clause";
    }
    // a constraint clause without a true literal is left to a free register outside the domain (vCstFree), which
    // makes it true in the completion
    Vec_IntForEachEntry( p->Jftr.vCst, Cref, i )
    {
        int * pLits = Gip_ClaLits( &p->Cdb.Alloc, Cref ), nLits = Gip_ClaLen( &p->Cdb.Alloc, Cref );
        if ( Gip_JftrPoll(p) )
            goto cleanup;
        if ( Gip_ClaIsRemoved(&p->Cdb.Alloc, Cref) || Gip_JftrCheckClause( p, p->pValue, pLits, pLits + nLits ) == 1 )
            continue;
        for ( k = 0; k < nLits; k++ )
        {
            Var = Gip_LitVar( pLits[k] );
            if ( Var < p->nVars && pKind[Var] == GIP_KIND_LO && p->pValue[Var] == GIP_NONE &&
                 !Gip_DomainHas(&p->Domain, Var) && Vec_IntFind(p->Jftr.vCstFree, pLits[k]) >= 0 &&
                 Gip_JftrLitCompleted(p, pLits[k]) )
                break;
        }
        if ( k == nLits )
            pFail = "a constraint clause has no true literal and no free register that makes it true";
    }
    // the completed assignment, in var order: the clauses of a node are over smaller vars
    memcpy( pVal, p->pValue, p->nVars );
    for ( Var = 0; Var < p->nVars; Var++ )
    {
        if ( Gip_JftrPoll(p) )
            goto cleanup;
        if ( pVal[Var] != GIP_NONE || !Gip_DomainHas(&p->Domain, Var) )
            continue;
        if ( pKind[Var] == GIP_KIND_LO )
            pVal[Var] = p->Jftr.pCompletion[p->pCtx->pLoIdx[Var]];
        else if ( pKind[Var] == GIP_KIND_PI )
            pVal[Var] = p->pPhase[Var] == GIP_TRUE ? GIP_TRUE : GIP_FALSE;
        else if ( Gip_JftrCheckDefined( p, Var ) && !Gip_JftrCheckNode( p, pVal, Var ) )
            pFail = "an unassigned node of the domain has no value in the completed assignment";
    }
    for ( Var = 0; Var < p->nVars; Var++ )
    {
        if ( Gip_JftrPoll(p) )
            goto cleanup;
        if ( pVal[Var] != GIP_NONE && Gip_JftrCheckDefined( p, Var ) )
            for ( c = Gip_JftrClaBeg(p->pCtx, Var), c1 = c + Gip_JftrClaNum(p->pCtx, Var); c < c1; c++ )
                if ( Gip_JftrCheckClause( p, pVal, pCnf->pClauses[c], pCnf->pClauses[c+1] ) == 0 )
                    pFail = "the completed assignment falsifies a transition clause";
    }
    for ( k = 0; k < 3; k++ )
        Vec_IntForEachEntry( vLists[k], Cref, i )
        {
            int * pLits = Gip_ClaLits( &p->Cdb.Alloc, Cref );
            if ( Gip_JftrPoll(p) )
                goto cleanup;
            if ( !Gip_ClaIsRemoved(&p->Cdb.Alloc, Cref) &&
                 Gip_JftrCheckClause( p, pVal, pLits, pLits + Gip_ClaLen(&p->Cdb.Alloc, Cref) ) == 0 )
                pFail = "the completed assignment falsifies a lemma, constraint or learnt clause";
        }
    for ( i = 0; i < p->Jftr.nAssump; i++ )
        if ( Gip_JftrCheckLit( p, pVal, p->Jftr.pAssump[i] ) != GIP_TRUE )
            pFail = "the completed assignment falsifies an assumption";
cleanup:
    ABC_FREE( pVal );
    if ( p->Jftr.pStats && (pFail || !p->fCanceled) )
        p->Jftr.pStats->nChecks++;
    if ( pFail )
    {
        if ( p->Jftr.pStats )
            p->Jftr.pStats->nFailures++;
        p->Jftr.fCoverDirty = 1;
        Abc_Print( 1, "JFTR CHECK FAILED: %s.\n", pFail );
    }
    return pFail == NULL && !p->fCanceled;
}

/**Function*************************************************************

  Synopsis    [The jftr decision: makes true a literal of an open or uncovered clause.]

  Description [Returns 1 after a decision, 0 for a justified SAT answer,
  and -1 to leave frontier search. A stop request is latched separately.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gip_SolverJftrDecide( Gip_Solver_t * p )
{
    int Var, Lit, c, Status, PrevOpen = -1;
    while ( 1 )
    {
        // 1. the assignments since the last scan may have opened clauses
        Gip_JftrScan( p );
        if ( p->fCanceled || p->Jftr.fCoverDirty )
            goto fallback;
        // 2. the constraint clauses of this round (few, checked directly), before the gates
        Status = Gip_JftrDecideCst( p );
        if ( Status < 0 )
            goto fallback;
        if ( Status > 0 )
            return 1;
        // 3. an open clause: make one of its literals true
        while ( Vec_IntSize(p->Jftr.vFront) > 0 )
        {
            if ( Gip_JftrPoll(p) )
                goto fallback;
            Var = Vec_IntPop( p->Jftr.vFront );
            if ( p->pValue[Var] == GIP_NONE )
                continue;
            c = p->pLevel[Var] == 0 ? Gip_JftrOpenClauseDom( p, Var ) : Gip_JftrOpenClauseRange( p, Var );
            if ( c < 0 )
                continue;
            Lit = Gip_JftrPickLit( p, c );
            if ( Lit < 0 || !Gip_DomainHas(&p->Domain, Gip_LitVar(Lit)) )
                goto fallback;
            // the node stays on the frontier: another defining clause of it may still be open
            Vec_IntPush( p->Jftr.vFront, Var );
            Gip_JftrDecideLit( p, Lit );
            return 1;
        }
        // 4. the lemma clauses: one without a covering witness
        while ( p->Jftr.nCovered < Vec_IntSize(p->Cdb.vLemmas) )
        {
            int n = Vec_IntSize( p->Cdb.vLemmas ), pos = -1, Cref, TrueLit;
            // The positions are visited cyclically from iCoverStart; n covered positions in a row without an
            // unassignment in between mean that every lemma clause is covered. A clean position is covered by its
            // witness, so only the dirty positions are examined.
            while ( p->Jftr.nCovered < n )
            {
                int q0 = (p->Jftr.iCoverStart + p->Jftr.nCovered) % n, d = Gip_JftrCoverNextDirty( p, q0, n ), nSkip;
                if ( Gip_JftrPoll(p) )
                    goto fallback;
                if ( d >= 0 )
                    nSkip = d - q0;
                else
                {
                    d = Gip_JftrCoverNextDirty( p, 0, q0 );
                    nSkip = d >= 0 ? d + n - q0 : n;
                }
                if ( p->Jftr.nCovered + nSkip >= n )
                {
                    p->Jftr.nCovered = n;
                    break;
                }
                p->Jftr.nCovered += nSkip;
                if ( !Gip_JftrLemmaCovered( p, d ) )
                {
                    pos = d;
                    break;
                }
                Gip_JftrCoverClean( p, d );
                p->Jftr.nCovered++;
            }
            if ( pos == -1 )
                break;
            p->Jftr.iLo = pos + 1;
            Cref = Vec_IntEntry( p->Cdb.vLemmas, pos );
            Lit = Gip_JftrPickClauseLit( p, Cref, &TrueLit );
            if ( Lit == -1 && TrueLit >= 0 && p->pLevel[Gip_LitVar(TrueLit)] == 0 )
            {
                // satisfied for good by a fact learnt since the rebuild
                p->Jftr.pRootSat[pos] = 1;
                Gip_JftrCoverClean( p, pos );
                p->Jftr.nCovered++;
                continue;
            }
            if ( Lit < 0 || !Gip_DomainHas(&p->Domain, Gip_LitVar(Lit)) )
                goto fallback;
            p->Jftr.pWit[pos] = Lit;   // the decision makes this literal true
            p->Jftr.nCovered++;
            Gip_JftrDecideLit( p, Lit );
            Gip_JftrCoverClean( p, pos );   // after the assignment: the decided literal covers it now
            return 1;
        }
        // 5. A request with the walk also needs the leaves that imply the assumptions under the transition clauses
        // alone: the walk marks them; a var it finds open goes back to the frontier
        Var = p->Jftr.Mode >= GIP_JFTR_WALK ? Gip_JftrWalk( p ) : -1;
        if ( p->fCanceled )
            goto fallback;
        if ( Var >= 0 )
        {
            // The walk is deterministic until a decision changes the trail.
            if ( Var == PrevOpen )
                goto fallback;
            PrevOpen = Var;
            Gip_JftrUnmark( p );
            Gip_JftrQueue( p, Var );
            continue;
        }
        // an early answer
        if ( p->Jftr.fCheck && !Gip_JftrCheck(p) )
            goto fallback;
        p->Jftr.fWalkClosed = p->Jftr.Mode >= GIP_JFTR_WALK;
        Gip_JftrCoverCommit( p );
        if ( p->Jftr.Mode == GIP_JFTR_WALK_SHRINK )
            Gip_JftrShrinkModel( p );
        Gip_JftrUnmark( p );
        return 0;
    }
fallback:
    if ( p->Jftr.pStats )
        p->Jftr.pStats->nFallbacks++;
    Gip_JftrUnmark( p );
    Vec_IntClear( p->Jftr.vFront );
    if ( p->fCanceled || p->Jftr.fCoverDirty )
    {
        Vec_IntClear( p->Jftr.vRootOpen );
        p->Jftr.nRootSeen = 0;
        p->Jftr.fCoverDirty = 1;
    }
    p->Jftr.fWalkClosed = 0;
    return -1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
