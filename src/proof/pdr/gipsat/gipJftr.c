/**************************************************************************************************
GipSAT -- the justification-frontier (jftr) search mode: decisions by backward justification on the
CNF of the circuit, early SAT answers with a register completion, the lemma cover, and the
justification walk and shrink. Written for ABC; not part of the port of rIC3.
**************************************************************************************************/

#include "gipsat.h"

ABC_NAMESPACE_IMPL_START

/*
   The jftr mode. A solver created with a positive PDR2_JFTR_CONFS (nConfLimit) has it. A solve uses it when the
   caller requested it right before (Gip_SolverSetJftr; every solve consumes the request), outside a batch, and where
   the mode is defined (Gip_JftrEligible, checked per solve): Cnf_DeriveOther's CNF as derived, every var an AIG
   object of its own (also in pdr2's compact numbering), smaller vars in the clauses of a var; a solver that is not
   shared, lazily loaded, copied or warm-started, without recycling, fJustify or fInputDecisions. The caller
   requests it only for a solver with no unit over a non-leaf var except the property, and with lemma clauses over
   register literals only.
   A decision makes true a literal of an open defining clause of an assigned node, of a constraint clause of the round
   or of an uncovered lemma clause; conflicts are handled as in the ordinary search. While the mode is active, the
   decision queue is neither consumed nor rebuilt and phases are not saved; after nConfLimit conflicts the solve
   continues as the ordinary GipSAT search.
   An early SAT answer is the partial assignment plus one register completion (pCompletion, for the unassigned
   registers; an unassigned input is free). When it is found, every assigned node is closed: each defining clause has
   a true literal or, for a node assigned at level 0, an unassigned literal outside the domain. Every lemma clause
   holds in the completion; every constraint clause of the round has a true literal or is left to an unassigned
   register outside the domain. With a requested walk, the marked leaves imply the assumptions under the transition
   clauses alone; a shrink then unassigns the other inputs and registers above level 0, and what is left is the
   completed register state and those leaves. A changed assignment or formula ends the answer.
*/

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

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

// the bookkeeping of the mode for a backtrack to Level, called before the trail is popped
void Gip_SolverJftrBacktrack( Gip_Solver_t * p, int Level )
{
    int i, pos, nTrail = Vec_IntEntry( p->vPosInTrail, Level );
    p->Jftr.fWalkClosed = 0;
    Gip_JftrCoverRestart( p );
    // a witness that is true on the trail but not in pCompletion may be unassigned now
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

// The budget ran out: the ordinary search goes on from the assumptions (Level = their number). The decision queue is
// what it was at the start of the solve: that of a fixed domain is kept, otherwise it is filled here.
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
    return pCost[4 * Gip_LitVar(Lit) + 2 * m + (1 ^ Gip_LitCompl(Lit))];
}
static void Gip_JftrPrepareCtx( Gip_Ctx_t * p )
{
    Cnf_Dat_t * pCnf = p->pCnf;
    Aig_Obj_t * pObj;
    int i, v, b, m, c;
    // one extra entry: the solvers' activation var is nVars
    p->pKind  = ABC_CALLOC( char, p->nVars + 1 );
    p->pCost  = ABC_CALLOC( int, 4 * (p->nVars + 1) );
    p->pLoIdx = ABC_ALLOC( int, p->nVars + 1 );
    for ( v = 0; v < p->nVars + 1; v++ )
        p->pLoIdx[v] = -1;
    // inputs and register outputs by their position among the CIs
    Aig_ManForEachCi( p->pAig, pObj, i )
    {
        v = Gip_CtxObjVar( p, pObj );
        p->pKind[v] = i < Saig_ManPiNum(p->pAig) ? GIP_KIND_PI : GIP_KIND_LO;
        if ( i >= Saig_ManPiNum(p->pAig) )
            p->pLoIdx[v] = i - Saig_ManPiNum(p->pAig);
    }
    p->nLo = Aig_ManCiNum(p->pAig) - Saig_ManPiNum(p->pAig);
    for ( v = 0; v < p->nVars; v++ )
    {
        pObj = Aig_ManObj( p->pAig, p->pVar2Obj ? p->pVar2Obj[v] : v );
        if ( pObj && Aig_ObjIsCo(pObj) )
            p->pKind[v] = GIP_KIND_CO;
        else if ( pObj && Aig_ObjIsNode(pObj) && Gip_JftrClaNum(p, v) > 0 )
            p->pKind[v] = GIP_KIND_NODE;
        // the leaves; the clauses of a node refer only to vars with smaller numbers (its cut leaves)
        for ( m = 0; m < 2; m++ )
            for ( b = 0; b < 2; b++ )
                p->pCost[4*v + 2*m + b] = p->pKind[v] == GIP_KIND_PI ? m : p->pKind[v] == GIP_KIND_LO;
        if ( p->pKind[v] != GIP_KIND_NODE && p->pKind[v] != GIP_KIND_CO )
            continue;
        for ( m = 0; m < 2; m++ )
            for ( b = 0; b < 2; b++ )
            {
                int LitV = Gip_Lit( v, 1 ^ b ), Best = GIP_JFTR_COST_MAX;
                for ( c = Gip_JftrClaBeg(p, v); c < Gip_JftrClaBeg(p, v) + Gip_JftrClaNum(p, v); c++ )
                {
                    int * pLit, fHas = 0, Sum = m;
                    for ( pLit = pCnf->pClauses[c]; pLit < pCnf->pClauses[c+1]; pLit++ )
                    {
                        if ( *pLit == LitV )
                            fHas = 1;
                        else if ( Gip_LitVar(*pLit) != v )
                        {
                            assert( Gip_LitVar(*pLit) < v );
                            Sum += Gip_JftrCostLitTrue( p->pCost, Gip_LitNot(*pLit), m );
                            if ( Sum > GIP_JFTR_COST_MAX )
                                Sum = GIP_JFTR_COST_MAX;
                        }
                    }
                    if ( fHas && Sum < Best )
                        Best = Sum;
                }
                p->pCost[4*v + 2*m + b] = Best;
            }
    }
    // pClsSplit / pClsPol0: a node with a value can only be open in a clause that contains its false literal. When the
    // clauses with one sign of the node's literal all come before those with the other, that group is a range.
    p->pClsSplit = ABC_ALLOC( int, p->nVars + 1 );
    p->pClsPol0  = ABC_CALLOC( char, p->nVars + 1 );
    for ( v = 0; v < p->nVars + 1; v++ )
        p->pClsSplit[v] = -1;
    for ( v = 0; v < p->nVars; v++ )
    {
        int c0 = Gip_JftrClaBeg(p, v), c1 = c0 + Gip_JftrClaNum(p, v), Split = -1, Pol0 = -1, fOk = c1 > c0;
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
        if ( !fOk )
            continue;
        p->pClsSplit[v] = Split == -1 ? c1 : Split;
        p->pClsPol0[v]  = (char)Pol0;
    }
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
static void Gip_JftrCoverReserve( Gip_Solver_t * p, int nPos )
{
    int nW = (nPos + 63) >> 6, nOld = p->Jftr.nDirtyWords;
    if ( nW <= nOld )
        return;
    nW = Abc_MaxInt( nW, 2 * nOld );
    p->Jftr.pDirty = ABC_REALLOC( word, p->Jftr.pDirty, nW );
    memset( p->Jftr.pDirty + nOld, 0, sizeof(word) * (nW - nOld) );
    p->Jftr.pDirtySummary = ABC_REALLOC( word, p->Jftr.pDirtySummary, (nW + 63) >> 6 );
    memset( p->Jftr.pDirtySummary + ((nOld + 63) >> 6), 0, sizeof(word) * (((nW + 63) >> 6) - ((nOld + 63) >> 6)) );
    p->Jftr.nDirtyWords = nW;
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
static void Gip_JftrCoverAdd( Gip_Solver_t * p, int pos )
{
    int Cref = Vec_IntEntry( p->Cdb.vLemmas, pos );
    int * pLits = Gip_ClaLits( &p->Cdb.Alloc, Cref ), nLits = Gip_ClaLen( &p->Cdb.Alloc, Cref );
    int i, fSat0 = 0;
    if ( pos >= p->Jftr.nLemmaAlloc )
    {
        int nNew = Abc_MaxInt( 2 * p->Jftr.nLemmaAlloc, pos + 1024 );
        p->Jftr.pWit  = ABC_REALLOC( int,  p->Jftr.pWit,  nNew );
        p->Jftr.pRootSat = ABC_REALLOC( char, p->Jftr.pRootSat, nNew );
        p->Jftr.pListedWit = ABC_REALLOC( int, p->Jftr.pListedWit, nNew );
        Gip_JftrCoverReserve( p, nNew );
        p->Jftr.nLemmaAlloc = nNew;
    }
    for ( i = 0; i < nLits; i++ )
    {
        assert( p->pCtx->pKind[Gip_LitVar(pLits[i])] == GIP_KIND_LO );   // a lemma clause is over register literals
        if ( Gip_SolverLitValue(p, pLits[i]) == GIP_TRUE && p->pLevel[Gip_LitVar(pLits[i])] == 0 )
            fSat0 = 1;
    }
    p->Jftr.pWit[pos]  = -1;
    p->Jftr.pRootSat[pos] = (char)fSat0;
    p->Jftr.pListedWit[pos] = -1;
    Gip_JftrCoverSetDirty( p, pos );   // a new position is examined before it is passed
}

// rebuilds the cover tables from the current lemma list (at level 0, between solves)
static void Gip_JftrCoverRebuild( Gip_Solver_t * p )
{
    int i, pos;
    assert( Gip_SolverLevelOf(p) == 0 );
    if ( p->Jftr.pvWitPos == NULL )
        p->Jftr.pvWitPos = ABC_CALLOC( Vec_Int_t *, 2 * Abc_MaxInt(p->pCtx->nLo, 1) );
    else
        for ( i = 0; i < 2 * p->pCtx->nLo; i++ )
            if ( p->Jftr.pvWitPos[i] )
                Vec_IntClear( p->Jftr.pvWitPos[i] );
    Vec_IntClear( p->Jftr.vVolatile );
    if ( p->Jftr.nDirtyWords )
    {
        memset( p->Jftr.pDirty, 0, sizeof(word) * p->Jftr.nDirtyWords );
        memset( p->Jftr.pDirtySummary, 0, sizeof(word) * ((p->Jftr.nDirtyWords + 63) >> 6) );
    }
    // every position is dirty now, so the root trail up to here needs no look
    p->Jftr.nRootChecked = Vec_IntSize( p->vTrail );
    for ( pos = 0; pos < Vec_IntSize(p->Cdb.vLemmas); pos++ )
        Gip_JftrCoverAdd( p, pos );
    p->Jftr.fCoverDirty = 0;
}

// a lemma clause was attached and appended to Cdb.vLemmas (a dirty cover is rebuilt at the next solve in the mode)
void Gip_SolverJftrLemmaAdded( Gip_Solver_t * p )
{
    if ( !p->Jftr.nConfLimit || p->Jftr.fCoverDirty )
        return;
    Gip_JftrCoverAdd( p, Vec_IntSize(p->Cdb.vLemmas) - 1 );
}

// start of a solve in the mode: the root facts since the last look falsify the witnesses on their other literal
static void Gip_JftrCoverRoot( Gip_Solver_t * p )
{
    int i, Lit;
    assert( p->Jftr.nRootChecked <= Vec_IntSize(p->vTrail) );   // the root trail only grows
    for ( i = p->Jftr.nRootChecked; i < Vec_IntSize(p->vTrail); i++ )
    {
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
    if ( p->pShared || p->Jftr.fCopied || p->pLoaded || p->nRecycleMode || p->fJustify || p->fInputDecisions )
        return 0;
    return 1;
}

// The entry of every solve: retires the answer of the previous solve and consumes the request, which is accepted only
// by a solver with the mode, outside a batch (a resumed solve skips the round setup) and where the mode is defined.
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

  Synopsis    [Creates the jftr state of a solver, starts the mode for one solve, frees the state.]

  Description [Gip_SolverJftrInit is called for a solver with a positive
  budget, also for a copy made by *p = *pSrc: the copied pointers belong
  to the source and are dropped, not freed. Gip_SolverJftrStart is called
  after the round is set up.]

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
void Gip_SolverJftrStart( Gip_Solver_t * p, int * pAssump, int nAssump )
{
    int i;
    p->Jftr.fActive = 1;
    if ( p->pCtx->pKind == NULL )
        Gip_JftrPrepareCtx( p->pCtx );
    if ( p->Jftr.fCoverDirty )
        Gip_JftrCoverRebuild( p );
    Gip_JftrCoverRoot( p );
    Vec_IntClear( p->Jftr.vFront );
    if ( p->Jftr.pCur == NULL )
        p->Jftr.pCur = ABC_ALLOC( int, p->nVarsAlloc );
    if ( p->Jftr.pCompletion == NULL )
    {
        // the completion starts as the saved phases (no phase = false, as in the ordinary decision)
        p->Jftr.pCompletion = ABC_ALLOC( char, Abc_MaxInt(p->pCtx->nLo, 1) );
        for ( i = 0; i < p->nVars; i++ )
            if ( p->pCtx->pLoIdx[i] >= 0 )
                p->Jftr.pCompletion[p->pCtx->pLoIdx[i]] = p->pPhase[i] == GIP_TRUE ? GIP_TRUE : GIP_FALSE;
    }
    p->Jftr.iScan = p->Jftr.iCheck = Vec_IntSize( p->vTrail );
    p->Jftr.iLo = 0;
    Gip_JftrCoverRestart( p );
    // the caller's array, read only during the solve
    p->Jftr.pAssump = pAssump;
    p->Jftr.nAssump = nAssump;
    p->Jftr.fRootRecheck = 1;
    Vec_IntClear( p->Jftr.vCstFree );
}
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
    int c, c0, c1;
    Gip_JftrFalseRange( p, Var, &c0, &c1 );
    for ( c = Abc_MaxInt( p->Jftr.pCur[Var], c0 ); c < c1; c++ )
    {
        int * pLit, * pStop = pCnf->pClauses[c+1];
        for ( pLit = pCnf->pClauses[c]; pLit < pStop; pLit++ )
        {
            if ( Gip_SolverLitValue(p, *pLit) == GIP_TRUE )
                break;
        }
        if ( pLit == pStop )
            break;
    }
    p->Jftr.pCur[Var] = c;
    return c < c1 ? c : -1;
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
    p->Jftr.pCur[Var] = Gip_JftrClaBeg( p->pCtx, Var );
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
    assert( Best >= 0 );   // an open clause is not falsified
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
            if ( Gip_JftrOpenClauseDom( p, Var ) >= 0 )
                Vec_IntPush( p->Jftr.vFront, Var );
        p->Jftr.fRootRecheck = 0;
    }
    for ( i = iFrom; i < Vec_IntSize(p->vTrail); i++ )
    {
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
// every constraint clause has a true literal or is left to a free register
static int Gip_JftrDecideCst( Gip_Solver_t * p )
{
    int i, Lit;
    for ( i = 0; i < Vec_IntSize(p->Jftr.vCst); i++ )
    {
        int Cref = Vec_IntEntry( p->Jftr.vCst, i ), TrueLit, Wit = Vec_IntEntry( p->Jftr.vCstWit, i );
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
                assert( Gip_LitVar(pL[k]) < p->nVars && p->pCtx->pKind[Gip_LitVar(pL[k])] == GIP_KIND_LO );
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
                assert( Pick != -1 );
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
            assert( TrueLit >= 0 );   // not falsified: the propagation would have reported it
            Vec_IntWriteEntry( p->Jftr.vCstWit, i, TrueLit );
            continue;
        }
        Vec_IntWriteEntry( p->Jftr.vCstWit, i, Lit );
        Gip_JftrDecideLit( p, Lit );
        return 1;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Checks an early answer as it is found, before a shrink (PDR2_JFTR_CHECK).]

  Description [The assigned nodes are closed, and one completed assignment
  satisfies every clause and the assumptions: the vars of the domain
  without a value get the register completion, the saved phase of an
  input, the function value of a node. A clause with a literal that still
  has no value (a var outside the domain) is not counted as falsified.]

***********************************************************************/
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
static void Gip_JftrCheck( Gip_Solver_t * p )
{
    Cnf_Dat_t * pCnf = p->pCtx->pCnf;
    Vec_Int_t * vLists[3] = { p->Cdb.vLemmas, p->Cdb.vLearnt, p->Cdb.vTemp };   // vTemp has the constraint clauses
    char * pKind = p->pCtx->pKind, * pVal = ABC_ALLOC( char, p->nVars );
    const char * pFail = NULL;
    int i, k, c, c1, Var, Lit, Cref;
    Vec_IntForEachEntry( p->vTrail, Lit, i )
    {
        Var = Gip_LitVar( Lit );
        if ( Var < p->nVars && Gip_JftrCheckDefined( p, Var ) && Gip_JftrCheckOpen( p, Var ) )
            pFail = "an assigned node has an open defining clause";
    }
    // a constraint clause without a true literal is left to a free register outside the domain (vCstFree), which
    // makes it true in the completion
    Vec_IntForEachEntry( p->Jftr.vCst, Cref, i )
    {
        int * pLits = Gip_ClaLits( &p->Cdb.Alloc, Cref ), nLits = Gip_ClaLen( &p->Cdb.Alloc, Cref );
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
        if ( pVal[Var] != GIP_NONE && Gip_JftrCheckDefined( p, Var ) )
            for ( c = Gip_JftrClaBeg(p->pCtx, Var), c1 = c + Gip_JftrClaNum(p->pCtx, Var); c < c1; c++ )
                if ( Gip_JftrCheckClause( p, pVal, pCnf->pClauses[c], pCnf->pClauses[c+1] ) == 0 )
                    pFail = "the completed assignment falsifies a transition clause";
    for ( k = 0; k < 3; k++ )
        Vec_IntForEachEntry( vLists[k], Cref, i )
        {
            int * pLits = Gip_ClaLits( &p->Cdb.Alloc, Cref );
            if ( !Gip_ClaIsRemoved(&p->Cdb.Alloc, Cref) &&
                 Gip_JftrCheckClause( p, pVal, pLits, pLits + Gip_ClaLen(&p->Cdb.Alloc, Cref) ) == 0 )
                pFail = "the completed assignment falsifies a lemma, constraint or learnt clause";
        }
    for ( i = 0; i < p->Jftr.nAssump; i++ )
        if ( Gip_JftrCheckLit( p, pVal, p->Jftr.pAssump[i] ) != GIP_TRUE )
            pFail = "the completed assignment falsifies an assumption";
    ABC_FREE( pVal );
    if ( pFail )
        Abc_Print( 1, "JFTR CHECK FAILED: %s.\n", pFail );
    assert( pFail == NULL );
}

/**Function*************************************************************

  Synopsis    [The jftr decision: makes true a literal of an open or uncovered clause.]

  Description [Returns 1 after a decision, 0 when the partial assignment
  is an early answer (see the contract at the top of the file).]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gip_SolverJftrDecide( Gip_Solver_t * p )
{
    int Var, Lit, c;
    unsigned nPass = 0;
    while ( 1 )
    {
        // 1. the assignments since the last scan may have opened clauses
        Gip_JftrScan( p );
        // 2. the constraint clauses of this round (few, checked directly), before the gates
        if ( Gip_JftrDecideCst( p ) )
            return 1;
        // 3. an open clause: make one of its literals true
        while ( Vec_IntSize(p->Jftr.vFront) > 0 )
        {
            Var = Vec_IntPop( p->Jftr.vFront );
            if ( p->pValue[Var] == GIP_NONE )
                continue;
            c = p->pLevel[Var] == 0 ? Gip_JftrOpenClauseDom( p, Var ) : Gip_JftrOpenClauseRange( p, Var );
            if ( c < 0 )
                continue;
            Lit = Gip_JftrPickLit( p, c );
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
            assert( Lit >= 0 );   // an uncovered clause is not falsified and has no true literal above level 0
            p->Jftr.pWit[pos] = Lit;   // the decision makes this literal true
            p->Jftr.nCovered++;
            Gip_JftrDecideLit( p, Lit );
            Gip_JftrCoverClean( p, pos );   // after the assignment: the decided literal covers it now
            return 1;
        }
        // 5. A request with the walk also needs the leaves that imply the assumptions under the transition clauses
        // alone: the walk marks them; a var it finds open goes back to the frontier
        Var = p->Jftr.Mode >= GIP_JFTR_WALK ? Gip_JftrWalk( p ) : -1;
        if ( Var >= 0 )
        {
            Gip_JftrUnmark( p );
            Gip_JftrQueue( p, Var );
            assert( nPass <= 1000 );   // the walk closes
            nPass++;
            continue;
        }
        // an early answer
        p->Jftr.fWalkClosed = p->Jftr.Mode >= GIP_JFTR_WALK;
        if ( p->Jftr.fCheck )
            Gip_JftrCheck( p );
        Gip_JftrCoverCommit( p );
        if ( p->Jftr.Mode == GIP_JFTR_WALK_SHRINK )
            Gip_JftrShrinkModel( p );
        Gip_JftrUnmark( p );
        return 0;
    }
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
