// Exact source-global rank intersection.  Original signatures remain intact
// for every other consumer.  No row, care bit, divisor, or candidate is lost.
struct Cec_TranSigDot_t_
{
    Cec_TranSim_t * pSource;
    Gia_Man_t * pGia;
    word * pSims;
    int nObjects, nSlots, Mode, Scope;
    word * pOnes;
    int * pCounts;
    size_t * pStarts;
    unsigned char * pComplement;
    int * pExceptions;
    word Calls, Pairs, BaselineWords, DenseWords, ExceptionWords;
    word ConstantShortcuts, MarginalLookups, OraclePairWords, OracleTargetWords;
    word SetupWords, SetupPopcounts, CacheBytes, nRankable, nExceptions;
    abctime timeSetup, timeRank;
};

static int Cec_TranSigDotTraceEnabled( void )
{
    static int Enabled = -1;
    if ( Enabled < 0 ) Enabled = Cec_TranStrictCexOption("ABC_STRICT_SIGNATURE_DOT_TRACE", 0, 1);
    return Enabled;
}

static void Cec_TranSigDotAssertOwner( Cec_TranSigDot_t * p )
{
    assert( p && p->pSource && p->pSource->pSigDot == p );
    assert( p->pSource->pGia == p->pGia && p->pSource->pSims == p->pSims );
    assert( Gia_ManObjNum(p->pGia) == p->nObjects && p->pSource->nSlots == p->nSlots );
}

static void Cec_TranSigDotConfigure( Cec_TranSim_t * pSource )
{
    static int Scope = 0;
    int Mode = Cec_TranStrictCexOption("ABC_STRICT_SIGNATURE_DOT", 0, 3);
    Cec_TranSigDot_t * p;
    if ( !Mode && !Cec_TranStrictCexOption("ABC_STRICT_SIGNATURE_DOT_PROFILE", 0, 1) ) return;
    assert( pSource->pSigDot == NULL );
    p = ABC_CALLOC(Cec_TranSigDot_t, 1);
    assert(p);
    p->pSource = pSource; p->pGia = pSource->pGia; p->pSims = pSource->pSims;
    p->nObjects = Gia_ManObjNum(p->pGia); p->nSlots = pSource->nSlots;
    p->Mode = Mode; p->Scope = ++Scope;
    pSource->pSigDot = p;
}

static void Cec_TranSigDotPrepare( Cec_TranSigDot_t * p )
{
    Gia_Obj_t * pObj;
    size_t nExceptions = 0;
    int i, s;
    abctime clk;
    Cec_TranSigDotAssertOwner(p);
    assert(p->Mode > 0);
    if ( p->pOnes ) return;
    clk = Abc_Clock();
    p->pOnes = ABC_CALLOC(word, p->nObjects);
    p->CacheBytes = sizeof(*p) + sizeof(word) * (word)p->nObjects;
    if ( p->Mode >= 2 )
    {
        p->pCounts = ABC_CALLOC(int, p->nObjects);
        p->pStarts = ABC_CALLOC(size_t, (size_t)p->nObjects+1);
        p->pComplement = ABC_CALLOC(unsigned char, p->nObjects);
        p->CacheBytes += (word)(sizeof(int)+sizeof(size_t)+sizeof(unsigned char))*p->nObjects + sizeof(size_t);
    }
    assert(p->pOnes && (p->Mode == 1 || (p->pCounts && p->pStarts && p->pComplement)));
    Gia_ManForEachObj(p->pGia, pObj, i)
    {
        word * pSig;
        int Zero = 0, One = 0;
        if ( !Gia_ObjIsCi(pObj) && !Gia_ObjIsAnd(pObj) ) continue;
        ++p->nRankable;
        pSig = Cec_TranSimObj(p->pSource, i);
        for ( s = 0; s < p->nSlots; ++s )
        {
            word v = pSig[s];
            p->pOnes[i] += Abc_TtCountOnes(v);
            if ( p->Mode >= 2 ) { Zero += v == 0; One += v == ~(word)0; }
        }
        if ( p->Mode >= 2 )
        {
            p->pComplement[i] = One > Zero;
            p->pCounts[i] = p->nSlots - Abc_MaxInt(Zero, One);
            p->pStarts[i] = nExceptions;
            nExceptions += p->pCounts[i];
        }
    }
    p->SetupWords = p->SetupPopcounts = p->nRankable * p->nSlots;
    if ( p->Mode >= 2 )
    {
        assert(nExceptions <= ((size_t)-1)/sizeof(int));
        p->pExceptions = ABC_ALLOC(int, nExceptions ? nExceptions : 1);
        assert(p->pExceptions);
        p->CacheBytes += sizeof(int) * (word)(nExceptions ? nExceptions : 1);
        Gia_ManForEachObj(p->pGia, pObj, i)
        {
            word * pSig, Default;
            size_t k;
            if ( !Gia_ObjIsCi(pObj) && !Gia_ObjIsAnd(pObj) ) continue;
            pSig = Cec_TranSimObj(p->pSource, i);
            Default = p->pComplement[i] ? ~(word)0 : 0;
            k = p->pStarts[i];
            for ( s = 0; s < p->nSlots; ++s )
                if ( pSig[s] != Default ) p->pExceptions[k++] = s;
            assert(k == p->pStarts[i] + p->pCounts[i]);
        }
        p->SetupWords += p->nRankable * p->nSlots;
        p->nExceptions = nExceptions;
    }
    p->timeSetup += Abc_Clock()-clk;
}

static word Cec_TranSigDotIntersection( Cec_TranSigDot_t * p, int iTarget, int iDiv )
{
    word Sum = 0;
    int iA = iTarget, iB = iDiv, k;
    word * pA, * pB;
    assert(p->pOnes && p->Mode > 0);
    assert( Gia_ObjIsCi(Gia_ManObj(p->pGia, iDiv)) || Gia_ObjIsAnd(Gia_ManObj(p->pGia, iDiv)) );
    assert( Gia_ObjIsAnd(Gia_ManObj(p->pGia, iTarget)) );
    if ( p->Mode == 1 )
    {
        pA = Cec_TranSimObj(p->pSource, iA); pB = Cec_TranSimObj(p->pSource, iB);
        for ( k = 0; k < p->nSlots; ++k ) Sum += Abc_TtCountOnes(pA[k] & pB[k]);
        p->DenseWords += p->nSlots;
        return Sum;
    }
    if ( p->pCounts[iB] < p->pCounts[iA] ) { iA = iDiv; iB = iTarget; }
    pA = Cec_TranSimObj(p->pSource, iA); pB = Cec_TranSimObj(p->pSource, iB);
    if ( !p->pCounts[iA] ) ++p->ConstantShortcuts;
    if ( p->pComplement[iA] )
    {
        for ( k = 0; k < p->pCounts[iA]; ++k )
        {
            int s = p->pExceptions[p->pStarts[iA]+k];
            Sum += Abc_TtCountOnes(~pA[s] & pB[s]);
        }
        assert(Sum <= p->pOnes[iB]);
        Sum = p->pOnes[iB] - Sum;
    }
    else
        for ( k = 0; k < p->pCounts[iA]; ++k )
        {
            int s = p->pExceptions[p->pStarts[iA]+k];
            Sum += Abc_TtCountOnes(pA[s] & pB[s]);
        }
    p->ExceptionWords += p->pCounts[iA];
    return Sum;
}

static void Cec_TranSigDotSnapshot( Cec_TranSigDot_t * p, char const * pStatus )
{
    if ( !p ) return;
    Cec_TranSigDotAssertOwner(p);
    Abc_Print(1, "stran-signature dot: schema=1 scope-id=%d status=%s mode=%d prepared=%d slots=%d objects=%d rankable=%llu rank-calls=%llu rank-pairs=%llu baseline-pair-words=%llu baseline-pair-popcounts=%llu raw-quadrant-pair-popcounts=%llu dense-dot-words=%llu exception-words=%llu constant-shortcuts=%llu marginal-lookups=%llu oracle-pair-words=%llu oracle-target-words=%llu setup-word-visits=%llu setup-popcounts=%llu exception-indices=%llu cache-bytes=%llu original-dense-bytes=%llu setup-sec=%.6f rank-sec=%.6f\n",
        p->Scope, pStatus, p->Mode, p->pOnes != NULL, p->nSlots, p->nObjects,
        (unsigned long long)p->nRankable,
        (unsigned long long)p->Calls, (unsigned long long)p->Pairs,
        (unsigned long long)p->BaselineWords, (unsigned long long)(2*p->BaselineWords),
        (unsigned long long)(p->Mode ? 0 : 2*p->BaselineWords),
        (unsigned long long)p->DenseWords, (unsigned long long)p->ExceptionWords,
        (unsigned long long)p->ConstantShortcuts, (unsigned long long)p->MarginalLookups,
        (unsigned long long)p->OraclePairWords, (unsigned long long)p->OracleTargetWords,
        (unsigned long long)p->SetupWords, (unsigned long long)p->SetupPopcounts,
        (unsigned long long)p->nExceptions, (unsigned long long)(p->CacheBytes ? p->CacheBytes : sizeof(*p)),
        (unsigned long long)8*p->nObjects*p->nSlots,
        (double)p->timeSetup/CLOCKS_PER_SEC, (double)p->timeRank/CLOCKS_PER_SEC);
    fflush(stdout);
}

static void Cec_TranSigDotStop( Cec_TranSigDot_t * p )
{
    if ( !p ) return;
    Cec_TranSigDotSnapshot(p, "CLOSED");
    ABC_FREE(p->pOnes); ABC_FREE(p->pCounts); ABC_FREE(p->pStarts);
    ABC_FREE(p->pComplement); ABC_FREE(p->pExceptions);
    p->pSource->pSigDot = NULL;
    ABC_FREE(p);
}
