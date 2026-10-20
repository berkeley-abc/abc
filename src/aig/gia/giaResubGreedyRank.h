// Minimal greedy-only import from reviewed B source 3dc19f13d.
// No flat/tiled pair variants, top-template dispatch, or new search caps.
// Exact output-sensitive construction of the existing bounded AND frontier.
// Heap order is worst first: low exact coverage, then late original emission.
typedef struct Gia_ResbRankPair_t_ {
    int Lo, Hi, Score;
    long long Order;
} Gia_ResbRankPair_t;

static int Gia_ResbRankPairWorse( Gia_ResbRankPair_t const * a,
    Gia_ResbRankPair_t const * b, long long * pCompares )
{
    (*pCompares)++;
    return a->Score != b->Score ? a->Score < b->Score : a->Order > b->Order;
}

static int Gia_ResbRankPairSort( void const * a, void const * b )
{
    Gia_ResbRankPair_t const * pA = (Gia_ResbRankPair_t const *)a;
    Gia_ResbRankPair_t const * pB = (Gia_ResbRankPair_t const *)b;
    if ( pA->Score != pB->Score ) return pA->Score > pB->Score ? -1 : 1;
    return pA->Order == pB->Order ? 0 : (pA->Order < pB->Order ? -1 : 1);
}

static void Gia_ResbFindRankedPairs( Gia_ResbMan_t * p, Vec_Int_t * vDomain, int Canonical )
{
    int D = Vec_IntSize(vDomain), K = p->nDivsMax, W = p->nWords;
    int * pCover = ABC_ALLOC(int, 2*D);
    Gia_ResbRankPair_t * pHeap = ABC_ALLOC(Gia_ResbRankPair_t, K);
    int n, i, k, phase, Div, Used, Total;
    assert(!p->fQualityNoTruncation && !p->fUseXor && K >= 0);
    // This constructor creates only the ranked AND lists; XOR/common-pair
    // consumers retain their original path. Masks and columns are immutable
    // for this call, and no physical divisor identities are merged.
    for ( n = 0; n < 2; n++ )
    {
        word * pOff = p->pSets[n], * pOn = p->pSets[!n];
        long long Order = 0, Bound = 0, Skipped = 0, OffCalls = 0, OffWords = 0;
        long long Scored = 0, ScoreWords = 0, Positive = 0, Inserted = 0, Replaced = 0, Compares = 0;
        int Measure = p->fProfilePivots && getenv("ABC_STRICT_PREPROOF_TRACE") && atoi(getenv("ABC_STRICT_PREPROOF_TRACE"));
        abctime clk = Abc_Clock(), clkHeap;
        double HeapSec = 0, FinalSec;
        Used = 0;
        assert(Vec_IntSize(p->vUnatePairs[n]) == 0 && Vec_IntSize(p->vUnatePairsW[n]) == 0);
        if ( Measure )
        {
            Abc_Print(1, "stran-resub pair-ranked-begin: schema=1 orientation=%d domain=%d words=%d bound=%d tie-mode=%d\n", n,D,W,K,Canonical);
            fflush(stdout);
        }
        Total = Abc_TtCountOnesVec(pOn,W);
        Vec_IntForEachEntry(vDomain,Div,i)
        {
            word * pSig = (word *)Vec_PtrEntry(p->vDivs,Div);
            pCover[2*i] = Abc_TtCountOnesVecMask(pSig,pOn,W,0);
            pCover[2*i+1] = Total-pCover[2*i];
        }
        for ( i = 0; i < D; i++ ) for ( k = 0; k < i; k++ )
        {
            int a = Abc_MinInt(Vec_IntEntry(vDomain,i),Vec_IntEntry(vDomain,k));
            int b = Abc_MaxInt(Vec_IntEntry(vDomain,i),Vec_IntEntry(vDomain,k));
            word * pA = (word *)Vec_PtrEntry(p->vDivs,a);
            word * pB = (word *)Vec_PtrEntry(p->vDivs,b);
            for ( phase = 0; phase < 4; phase++, Order++ )
            {
                int OuterPhase = Vec_IntEntry(vDomain,i) == b ? phase>>1 : phase&1;
                int InnerPhase = Vec_IntEntry(vDomain,i) == b ? phase&1 : phase>>1;
                int Upper = Abc_MinInt(pCover[2*i+OuterPhase],pCover[2*k+InnerPhase]);
                word MaskA = (phase&1) ? ~(word)0 : 0, MaskB = (phase>>1) ? ~(word)0 : 0;
                int w, Hit = 0, Score = 0;
                Gia_ResbRankPair_t Item = {Abc_Var2Lit(a,phase&1),Abc_Var2Lit(b,phase>>1),0,Order};
                // Greedy first canonicalizes by (Hi,Lo,descriptor phase).
                // AND descriptors here have phase0, and two31-bit literals
                // fit an exact positive62-bit lexicographic key.
                if ( Canonical ) Item.Order = ((long long)Item.Hi << 31) | Item.Lo;
                Bound++;
                // Positive ON coverage is required even before the heap is
                // full. Once full, a later score tie cannot displace an
                // earlier emitted physical pair. This is an exact bound.
                if ( !K || !Upper || (Used == K && (Upper < pHeap[0].Score ||
                     (Upper == pHeap[0].Score && Item.Order >= pHeap[0].Order))) ) { Skipped++; continue; }
                if ( Measure )
                {
                    for ( w = 0; w < W; w++ )
                        if ( pOff[w] & (pA[w]^MaskA) & (pB[w]^MaskB) ) { Hit = 1; break; }
                    OffCalls++; OffWords += w+Hit;
                }
                else Hit = Abc_TtIntersectTwo(pOff,0,pA,phase&1,pB,phase>>1,W);
                if ( Hit ) continue;
                // Full exact ON score also establishes positive ON coverage;
                // no separate existential ON scan is needed.
                Score = Abc_TtCountOnesVecMask2(pA,pB,phase&1,phase>>1,pOn,W);
                Scored++; ScoreWords += W;
                if ( !Score ) continue;
                Positive++;
                Item.Score = Score;
                if ( Used == K && !Gia_ResbRankPairWorse(&pHeap[0],&Item,&Compares) ) continue;
                clkHeap = Measure ? Abc_Clock() : 0;
                if ( Used < K )
                {
                    int Pos = Used++;
                    Inserted++;
                    while ( Pos && Gia_ResbRankPairWorse(&Item,&pHeap[(Pos-1)/2],&Compares) )
                    { pHeap[Pos] = pHeap[(Pos-1)/2]; Pos = (Pos-1)/2; }
                    pHeap[Pos] = Item;
                }
                else
                {
                    int Pos = 0, Child;
                    Replaced++;
                    while ( (Child = 2*Pos+1) < Used )
                    {
                        if ( Child+1 < Used && Gia_ResbRankPairWorse(&pHeap[Child+1],&pHeap[Child],&Compares) ) Child++;
                        if ( !Gia_ResbRankPairWorse(&pHeap[Child],&Item,&Compares) ) break;
                        pHeap[Pos] = pHeap[Child]; Pos = Child;
                    }
                    pHeap[Pos] = Item;
                }
                if ( Measure ) HeapSec += (double)(Abc_Clock()-clkHeap)/CLOCKS_PER_SEC;
            }
        }
        clkHeap = Abc_Clock();
        qsort(pHeap,Used,sizeof(Gia_ResbRankPair_t),Gia_ResbRankPairSort);
        for ( i = 0; i < Used; i++ )
        {
            Vec_IntPush(p->vUnatePairs[n],Gia_ResbPairIntern(p,pHeap[i].Lo,pHeap[i].Hi,0));
            Vec_IntPush(p->vUnatePairsW[n],pHeap[i].Score);
        }
        FinalSec = (double)(Abc_Clock()-clkHeap)/CLOCKS_PER_SEC;
        if ( Measure )
        {
            Abc_Print(1, "stran-resub pair-ranked: schema=1 orientation=%d domain=%d words=%d bound=%d tie-mode=%d bound-tests=%lld bound-skipped=%lld singleton-words=%lld off-calls=%lld off-words=%lld score-calls=%lld score-words=%lld positive=%lld inserted=%lld replaced=%lld heap-compares=%lld retained=%d intern-calls=%d heap-bytes=%llu heap-sec=%.6f final-sec=%.6f seconds=%.6f\n",
                n,D,W,K,Canonical,Bound,Skipped,(long long)(D+1)*W,OffCalls,OffWords,Scored,ScoreWords,Positive,Inserted,Replaced,Compares,Used,Used,
                (unsigned long long)(sizeof(int)*2*D+sizeof(Gia_ResbRankPair_t)*K),HeapSec,FinalSec,(double)(Abc_Clock()-clk)/CLOCKS_PER_SEC);
            fflush(stdout);
        }
    }
    ABC_FREE(pCover); ABC_FREE(pHeap);
}
