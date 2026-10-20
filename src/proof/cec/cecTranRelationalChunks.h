// Default Strict mode 1 skips re-proving complete CBS certificates within one
// immutable batch. Explicit mode 2 also closes bounded groups.
// Mode 2 groups are independent: no outside relation enters their formula.
// Previously proved results remain global certificates, not group hypotheses.
// A group may lose cross-group mutual induction. There is no global retry.
#define CEC_TRAN_REL_CHUNK_SIZE 256
#define CEC_CHUNK_REQUIRE(C) do { if (!(C)) { \
    Abc_Print(-1,"Assertion relational chunk failed at %s:%d: %s\n",__FILE__,__LINE__,#C); \
    abort(); } } while (0)

typedef struct Cec_TranRelChunkOrder_t_ {
    int Edge, Kind, Gain, Target;
} Cec_TranRelChunkOrder_t;
static int Cec_TranRelChunkTestActive = -1; // private deterministic fixture

static int Cec_TranRelChunkMode( Cec_ParTran_t const * pPars )
{
    char const * s;
    int Mode;
    if ( !pPars->fRoute3 || pPars->fOdcProofScope ) return 0;
    s = getenv("ABC_SRESUB_SEQ_PROOF_MODE");
    // Explicit older basis backends retain their original proof route.
    if ( !s ) return Cec_TranRelationalBackend(pPars) == 2 ? 1 : 0;
    if ( !strcmp(s,"0") ) return 0;
    if ( !strcmp(s,"1") ) Mode = 1;
    else if ( !strcmp(s,"2") ) Mode = 2;
    else
    {
        Abc_Print(-1,"ABC_SRESUB_SEQ_PROOF_MODE must be 0 (legacy), 1 (CBS known), or 2 (independent 256-relation groups)\n");
        exit(2); return 0;
    }
    if ( Cec_TranRelationalBackend(pPars) != 2 )
    {
        Abc_Print(-1,"ABC_SRESUB_SEQ_PROOF_MODE requires the lazy-basis backend (Route3 default or ABC_STRAN_RELATIONAL_BASIS=2)\n");
        exit(2);
    }
    return Mode;
}

static int Cec_TranRelChunkCompare( void const * p0, void const * p1 )
{
    Cec_TranRelChunkOrder_t const * a = (Cec_TranRelChunkOrder_t const *)p0;
    Cec_TranRelChunkOrder_t const * b = (Cec_TranRelChunkOrder_t const *)p1;
    if ( a->Kind != b->Kind ) return a->Kind < b->Kind ? -1 : 1;
    if ( a->Gain != b->Gain ) return a->Gain > b->Gain ? -1 : 1;
    if ( a->Target != b->Target ) return a->Target < b->Target ? -1 : 1;
    return a->Edge < b->Edge ? -1 : a->Edge > b->Edge;
}

// The caller owns a single BudgetBegin/End around this entire operation.
// Every group therefore inherits the SAME absolute deadline, including order,
// projection and cleanup costs. Earlier completed groups survive a later stop.
// ChunkSize==0 is the CBS-only ablation: original order and one full batch.
// Positive sizes bound ALL relations in a group. The original transition graph
// is still unrolled for every group; this is not a bounded transition cone.
static Vec_Int_t * Cec_TranRelChunksProve( Gia_Man_t * pBatch,
    Vec_Int_t * Pairs, Cec_TranCand_t const * Cands, int nCands, int nHelpers,
    Vec_Str_t * Stage, Cec_ParTran_t * Pars, int * pnRounds, int ChunkSize )
{
    Cec_TranRelClosed_t * PreviousClosed = Cec_TranRelClosedCurrent;
    Cec_TranRelObserve_t * PreviousObserve = Cec_TranRelObserveCurrent;
    int n = nHelpers + nCands, i, j, f, l, a, Edge, Value, nPending = 0;
    int nCbs = 0, nHistory = 0, nGroups = 0, nNew = 0, nDirect = 0, nBuild = 0;
    int RequestedSize = ChunkSize;
    int nRefuted = 0, nUnknown = 0, nAttempted = 0, nGroupMax = 0;
    long long KnownVisits = 0;
    abctime Started = Abc_Clock(), EngineTicks = 0;
    Cec_TranRelChunkOrder_t * Order = ABC_ALLOC(Cec_TranRelChunkOrder_t,n);
    Vec_Int_t * Status = Vec_IntStartFull(n), * Known = Vec_IntAlloc(n);
    Vec_Int_t * Map = Vec_IntAlloc(n), * LocalPairs = Vec_IntAlloc(2*n);
    CEC_CHUNK_REQUIRE(Vec_IntSize(Pairs) == 2*n && Vec_StrSize(Stage) == nCands);
    CEC_CHUNK_REQUIRE(!PreviousClosed || (PreviousClosed->Frames == Pars->nFrames &&
        Vec_StrSize(PreviousClosed->Known) == n));
    *pnRounds = 0;
    for ( i = 0; i < n; ++i )
    {
        int IsHistory = Cec_TranRelClosedKnown(i);
        int IsCbs = i >= nHelpers && Vec_StrEntry(Stage,i-nHelpers) == 1;
        nHistory += IsHistory; nCbs += IsCbs;
        if ( IsHistory || IsCbs )
        {
            Vec_IntWriteEntry(Status,i,1);
            // CBS equalities already follow from the unchanged circuit. Mode
            // 2 also omits all historical sequential facts instead of taking
            // an arbitrary fragment of an old mutually inductive bundle.
            if ( !ChunkSize ) Vec_IntPush(Known,i);
            continue;
        }
        Order[nPending].Edge = i;
        // Direct/CONST first, then constructed candidates, then unproved
        // helpers. Gain is only an ordering hint; selection still checks it.
        Order[nPending].Kind = i < nHelpers ? 2 :
            Cands[i-nHelpers].nKind == CEC_TRAN_CAND_CONSTR ? 1 : 0;
        Order[nPending].Gain = i < nHelpers ? 0 : Cands[i-nHelpers].Gain;
        Order[nPending].Target = i < nHelpers ? i : Cands[i-nHelpers].iTarget;
        ++nPending;
    }
    if ( ChunkSize ) qsort(Order,nPending,sizeof(*Order),Cec_TranRelChunkCompare);
    else ChunkSize = nPending ? nPending : 1;
    for ( i = 0; i < nPending; )
    {
        Cec_TranRelClosed_t LocalClosed = {0};
        Cec_TranRelObserve_t LocalObserve;
        Vec_Int_t * LocalStatus;
        int End = i + Abc_MinInt(ChunkSize,nPending-i), LocalHelpers = 0, Rounds = 0;
        int GroupProved = 0, GroupUnknown = 0, GroupRefuted = 0;
        abctime EngineStart;
        if ( Cec_TranSeqBudgetStop() ) break;
        Vec_IntClear(Map); Vec_IntAppend(Map,Known);
        for ( j = i; j < End; ++j ) Vec_IntPush(Map,Order[j].Edge);
        // Global numeric order keeps helper/target lanes contiguous and makes
        // the mode-1 formula/order identical apart from complete CBS facts.
        Vec_IntSort(Map,0); Vec_IntClear(LocalPairs);
        CEC_CHUNK_REQUIRE(!RequestedSize || Vec_IntSize(Map) <= RequestedSize);
        LocalClosed.Frames = Pars->nFrames;
        LocalClosed.Known = Vec_StrStart(Vec_IntSize(Map));
        LocalClosed.KnownIds = Vec_IntAlloc(Vec_IntSize(Known));
        Vec_IntForEachEntry(Map,Edge,j)
        {
            Vec_IntPushTwo(LocalPairs,Vec_IntEntry(Pairs,2*Edge),Vec_IntEntry(Pairs,2*Edge+1));
            LocalHelpers += Edge < nHelpers;
            if ( Vec_IntEntry(Status,Edge) == 1 )
            {
                Vec_StrWriteEntry(LocalClosed.Known,j,1);
                Vec_IntPush(LocalClosed.KnownIds,j); ++LocalClosed.nKnown;
            }
        }
        CEC_CHUNK_REQUIRE(LocalClosed.nKnown == Vec_IntSize(Known));
        Cec_TranRelClosedCurrent = &LocalClosed;
        if ( PreviousObserve )
        {
            // This is a borrowed query-counter view only. Candidate identity
            // lookup/ClosedRecord/ObserveClosed remain in the global caller.
            LocalObserve = *PreviousObserve;
            LocalObserve.Helpers = LocalObserve.Targets = NULL;
            LocalObserve.nHelpers = LocalHelpers;
            LocalObserve.nTargets = Vec_IntSize(Map)-LocalHelpers;
            LocalObserve.nPriorClosed = 0; LocalObserve.ObserveTicks = 0;
            LocalObserve.PriorClosed = Vec_StrStart(Vec_IntSize(Map));
            memset(LocalObserve.Queries,0,sizeof(LocalObserve.Queries));
            memset(LocalObserve.SatTicks,0,sizeof(LocalObserve.SatTicks));
            Vec_IntForEachEntry(Map,Edge,j)
                if ( Vec_StrEntry(PreviousObserve->PriorClosed,Edge) )
                { Vec_StrWriteEntry(LocalObserve.PriorClosed,j,1); ++LocalObserve.nPriorClosed; }
            Cec_TranRelObserveCurrent = &LocalObserve;
        }
        EngineStart = Abc_Clock();
        LocalStatus = Cec_TranRelChunkTestActive < 0 ?
            Cec_TranRelationalProve(pBatch,LocalPairs,Pars,&Rounds) :
            Cec_TranRelationalLazyBasisEngine(pBatch,LocalPairs,Pars,&Rounds,Cec_TranRelChunkTestActive);
        EngineTicks += Abc_Clock()-EngineStart;
        Cec_TranRelClosedCurrent = PreviousClosed;
        Cec_TranRelObserveCurrent = PreviousObserve;
        if ( PreviousObserve )
        {
            for ( f = 0; f < 2; ++f ) for ( l = 0; l < 3; ++l )
            {
                for ( a = 0; a < 4; ++a ) PreviousObserve->Queries[f][l][a] += LocalObserve.Queries[f][l][a];
                PreviousObserve->SatTicks[f][l] += LocalObserve.SatTicks[f][l];
            }
            PreviousObserve->ObserveTicks += LocalObserve.ObserveTicks;
            Vec_StrFree(LocalObserve.PriorClosed);
        }
        Vec_IntForEachEntry(Map,Edge,j)
        {
            Value = Vec_IntEntry(LocalStatus,j);
            CEC_CHUNK_REQUIRE(Value >= -1 && Value <= 1);
            if ( Vec_StrEntry(LocalClosed.Known,j) )
            { CEC_CHUNK_REQUIRE(Value == 1); continue; }
            Vec_IntWriteEntry(Status,Edge,Value);
            GroupProved += Value == 1; GroupUnknown += Value < 0; GroupRefuted += Value == 0;
            if ( Value != 1 ) continue;
            // The engine returns 1 only for a complete closure or input Known.
            // Publish the whole new closed subset, never intermediate UNSATs.
            ++nNew;
            nDirect += Edge >= nHelpers && Cands[Edge-nHelpers].nKind != CEC_TRAN_CAND_CONSTR;
            nBuild += Edge >= nHelpers && Cands[Edge-nHelpers].nKind == CEC_TRAN_CAND_CONSTR;
        }
        ++nGroups; nAttempted += End-i; *pnRounds += Rounds;
        KnownVisits += LocalClosed.nKnown;
        nGroupMax = Abc_MaxInt(nGroupMax,Vec_IntSize(Map));
        if ( Pars->fVerbose )
            CEC_TRAN_VERBOSE( Pars->fVerbose, "stran-root relational-chunk: schema=1 scope=strict group=%d new-relations=%d known=%d proved-new=%d refuted=%d unknown=%d rounds=%d\n",
                nGroups,End-i,LocalClosed.nKnown,GroupProved,GroupRefuted,GroupUnknown,Rounds);
        Vec_IntFree(LocalStatus); Vec_StrFree(LocalClosed.Known); Vec_IntFree(LocalClosed.KnownIds);
        i = End;
    }
    Vec_IntForEachEntry(Status,Value,i)
    { nRefuted += Value == 0; nUnknown += Value < 0; }
    CEC_TRAN_VERBOSE( Pars->fVerbose, "stran-root relational-chunks: schema=1 scope=strict mode=%d chunk-size=%d relations=%d cbs-known=%d history-known=%d groups=%d attempted-new=%d unattempted=%d known-visits=%lld group-relations-max=%d proved-new=%d proved-direct=%d proved-build=%d refuted=%d unknown=%d engine-sec=%.6f setup-sec=%.6f\n",
        RequestedSize ? 2 : 1,RequestedSize,n,nCbs,nHistory,nGroups,nAttempted,nPending-nAttempted,KnownVisits,nGroupMax,nNew,nDirect,nBuild,nRefuted,nUnknown,
        (double)EngineTicks/CLOCKS_PER_SEC,(double)(Abc_Clock()-Started-EngineTicks)/CLOCKS_PER_SEC);
    ABC_FREE(Order); Vec_IntFree(Known); Vec_IntFree(Map); Vec_IntFree(LocalPairs);
    return Status;
}

#undef CEC_CHUNK_REQUIRE
