// Default-off search heuristic for one immutable Strict, micro-batched pass.
// Page zero is unchanged. A validated history certificate, regardless of its
// current gain, or a fresh positive full certificate on page zero exempts a
// root from the gate. No certificate, proof, cursor or commit rule is altered.
enum {
    CEC_TRAN_FP_ELIGIBLE = 1,
    CEC_TRAN_FP_HISTORY = 2,
    CEC_TRAN_FP_FRESH = 4,
    CEC_TRAN_FP_SUBMITTED = 8,
    CEC_TRAN_FP_STOPPED = 16
};

typedef struct Cec_TranRootFirstPage_t_ {
    unsigned char * pFlags;
    int nObjects, fSealed, nEligible, nGroups[4], nNoSubmitted;
    int nStopped, nStoppedNoSubmitted, nNaturalFinished, nUnbounded;
    long long nSkippedPages, nUnusedQSlots;
    long long nSubmitted[2], nProvedCbs[2], nProvedSeq[2];
    // Profiling only: immutable shared recipe references for exact later
    // certificate -> Selected membership. Never used to schedule or prove.
    Cec_TranCandVec_t LaterProved;
} Cec_TranRootFirstPage_t;

static int Cec_TranRootFirstPageApplicable( Cec_ParTran_t const * pPars,
    int fCombOnly )
{
    // Both fanout and legacy serial ODC force j=0. The explicit scope check
    // also rejects fanout ODC if a caller were to change its page setting.
    return pPars->fRoute3 && !fCombOnly && !pPars->fOdcProofScope &&
        pPars->nRootProofBatch > 0 && pPars->fUseConstr;
}

static Cec_TranRootFirstPage_t Cec_TranRootFirstPageStart( int nObjects,
    int fEnabled )
{
    Cec_TranRootFirstPage_t s;
    memset( &s, 0, sizeof(s) );
    s.nObjects = nObjects;
    if ( fEnabled ) s.pFlags = ABC_CALLOC( unsigned char, nObjects );
    return s;
}

// Call only after the original topology, structure and simulation checks have
// populated HistoryLive. In particular, do not require its recomputed Gain>0.
static void Cec_TranRootFirstPagePrime( Cec_TranRootFirstPage_t * s,
    Cec_TranRoot_t const * pRoots, int nRoots,
    Cec_TranCandVec_t const * pHistoryLive )
{
    int i;
    if ( !s->pFlags ) return;
    assert( !s->fSealed && s->nEligible == 0 );
    for ( i = 0; i < nRoots; ++i )
        if ( Cec_TranRootBuildEligible(pRoots + i) )
        {
            int root = pRoots[i].iObj;
            assert( root > 0 && root < s->nObjects );
            assert( !s->pFlags[root] );
            s->pFlags[root] = CEC_TRAN_FP_ELIGIBLE;
            ++s->nEligible;
        }
    for ( i = 0; i < pHistoryLive->nSize; ++i )
    {
        Cec_TranCand_t const * c = pHistoryLive->pArray + i;
        assert( c->iTarget > 0 && c->iTarget < s->nObjects );
        assert( c->nStatus == CEC_TRAN_STATE_PROVED_COMB ||
                c->nStatus == CEC_TRAN_STATE_PROVED_SEQ );
        assert( c->nProofStage == 1 || c->nProofStage == 2 );
        if ( s->pFlags[c->iTarget] & CEC_TRAN_FP_ELIGIBLE )
            s->pFlags[c->iTarget] |= CEC_TRAN_FP_HISTORY;
    }
}

// Observe complete portfolio results, including an empty first proof frontier.
// Failure or UNKNOWN is never interpreted as an impossibility certificate.
static void Cec_TranRootFirstPageObserve( Cec_TranRootFirstPage_t * s,
    Cec_TranCandVec_t const * pSubmitted,
    Cec_TranCandVec_t const * pBatchProved, int iPage )
{
    int i, later = iPage > 0;
    if ( !s->pFlags ) return;
    assert( s->fSealed == later );
    s->nSubmitted[later] += pSubmitted->nSize;
    if ( !later )
        for ( i = 0; i < pSubmitted->nSize; ++i )
        {
            int root = pSubmitted->pArray[i].iTarget;
            assert( root > 0 && root < s->nObjects );
            s->pFlags[root] |= CEC_TRAN_FP_SUBMITTED;
        }
    for ( i = 0; i < pBatchProved->nSize; ++i )
    {
        Cec_TranCand_t const * c = pBatchProved->pArray + i;
        if ( c->nStatus != CEC_TRAN_STATE_PROVED_COMB &&
             c->nStatus != CEC_TRAN_STATE_PROVED_SEQ )
            continue;
        assert( c->iTarget > 0 && c->iTarget < s->nObjects );
        assert( c->nProofStage == 1 || c->nProofStage == 2 );
        assert( c->nProofLane == c->nProofStage );
        s->nProvedCbs[later] += c->nProofStage == 1;
        s->nProvedSeq[later] += c->nProofStage == 2;
        if ( !later && c->Gain > 0 &&
             (s->pFlags[c->iTarget] & CEC_TRAN_FP_ELIGIBLE) )
            s->pFlags[c->iTarget] |= CEC_TRAN_FP_FRESH;
        if ( later && !Cec_TranCandVecContains(&s->LaterProved, c) )
            Cec_TranCandVecPush( &s->LaterProved, *c );
    }
}

static void Cec_TranRootFirstPageSeal( Cec_TranRootFirstPage_t * s,
    Cec_TranRootCursor_t const * pCursors, int nQ )
{
    int root;
    if ( !s->pFlags ) return;
    assert( !s->fSealed && nQ >= 0 );
    s->fSealed = 1;
    for ( root = 1; root < s->nObjects; ++root )
    {
        unsigned char flags = s->pFlags[root];
        Cec_TranRootCursor_t const * cursor = pCursors + root;
        int group;
        if ( !(flags & CEC_TRAN_FP_ELIGIBLE) ) continue;
        // 0=neither, 1=history only, 2=fresh only, 3=both.
        group = !!(flags & CEC_TRAN_FP_HISTORY) +
            2 * !!(flags & CEC_TRAN_FP_FRESH);
        ++s->nGroups[group];
        s->nNoSubmitted += !(flags & CEC_TRAN_FP_SUBMITTED);
        if ( group ) continue;
        if ( cursor->fExhausted || (nQ > 0 && cursor->nBuildAccepted >= nQ) )
        {
            ++s->nNaturalFinished;
            continue;
        }
        s->pFlags[root] |= CEC_TRAN_FP_STOPPED;
        ++s->nStopped;
        s->nStoppedNoSubmitted += !(flags & CEC_TRAN_FP_SUBMITTED);
        if ( nQ > 0 ) s->nUnusedQSlots += nQ - cursor->nBuildAccepted;
        else ++s->nUnbounded;
    }
    assert( s->nGroups[0] == s->nStopped + s->nNaturalFinished );
}

// The caller checks ordinary completion first. Do not consume q, fabricate
// iterator exhaustion, or touch the native cursor when a page is skipped.
static int Cec_TranRootFirstPageSkip( Cec_TranRootFirstPage_t * s,
    int iRoot, int iPage )
{
    if ( !s->pFlags || iPage == 0 ) return 0;
    assert( s->fSealed && iRoot > 0 && iRoot < s->nObjects );
    if ( !(s->pFlags[iRoot] & CEC_TRAN_FP_STOPPED) ) return 0;
    ++s->nSkippedPages;
    return 1;
}

static void Cec_TranRootFirstPageSelected( Cec_TranRootFirstPage_t const * s,
    Cec_TranCandVec_t const * pSelected, int * pLaterSelected,
    long long * pLaterLocalGain )
{
    int i;
    *pLaterSelected = 0; *pLaterLocalGain = 0;
    for ( i = 0; i < pSelected->nSize; ++i )
        if ( Cec_TranCandVecContains(&s->LaterProved, pSelected->pArray + i) )
        {
            ++*pLaterSelected;
            *pLaterLocalGain += pSelected->pArray[i].Gain;
        }
}

static void Cec_TranRootFirstPageStop( Cec_TranRootFirstPage_t * s )
{
    Cec_TranCandVecStop( &s->LaterProved );
    ABC_FREE( s->pFlags );
}

static void Cec_TranRootFirstPageFinish( Cec_TranRootFirstPage_t * s,
    Cec_TranCandVec_t const * pSelected, int iRound,
    int nAndBefore, int nAndAfter )
{
    int laterSelected;
    long long laterGain;
    if ( !s->pFlags ) return;
    Cec_TranRootFirstPageSelected( s, pSelected, &laterSelected, &laterGain );
    Abc_Print( 1, "stran-root first-page-gate: schema=1 enabled=1 scope=immutable-strict-pass round=%d sealed=%d eligible-roots=%d history-only=%d fresh-only=%d both=%d neither=%d no-first-submitted=%d stopped-roots=%d stopped-no-first-submitted=%d neither-naturally-finished=%d skipped-root-pages=%lld unused-q-slots-at-seal=%lld unbounded-stopped-roots=%d first-submitted=%lld first-proved-cbs=%lld first-proved-seq=%lld later-submitted=%lld later-proved-cbs=%lld later-proved-seq=%lld later-selected=%d later-selected-local-gain=%lld selected=%d AND=%d->%d final-and-gain=%d gain-basis=full-bundle-final-AND unenumerated-candidates=unobserved quality-policy=stop-after-no-first-page-certificate\n",
        iRound + 1, s->fSealed, s->nEligible, s->nGroups[1], s->nGroups[2],
        s->nGroups[3], s->nGroups[0], s->nNoSubmitted, s->nStopped, s->nStoppedNoSubmitted,
        s->nNaturalFinished, s->nSkippedPages, s->nUnusedQSlots, s->nUnbounded,
        s->nSubmitted[0], s->nProvedCbs[0], s->nProvedSeq[0],
        s->nSubmitted[1], s->nProvedCbs[1], s->nProvedSeq[1],
        laterSelected, laterGain, pSelected->nSize,
        nAndBefore, nAndAfter, nAndBefore - nAndAfter );
    Cec_TranRootFirstPageStop( s );
}
