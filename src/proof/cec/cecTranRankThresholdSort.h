// Exact ordering of every surviving physical record. This changes neither
// scoring nor lazy-CI visitation; the low-score protected tail is retained.
typedef struct Cec_TranRankThreshold_t_ {
    int Mode, Profile, Enabled, Applied, PartitionKnown, InputMonotone;
    int N, B, H, E, P;
    word Cutoff, BucketSpan, FirstSorted, SecondSorted, BucketRecords;
    word FirstMoved, SecondMoved, ScratchBytes, CountBytes, OracleBytes;
    word FirstChecks, SecondChecks, CiOrderChecks;
    char const * Reason, * SecondKind, * SecondReason;
    Cec_TranDivRank_t * Buffer;
    abctime FirstTicks, SecondTicks, FreeTicks, OracleTicks;
} Cec_TranRankThreshold_t;

static void Cec_TranRankThresholdStart(Cec_TranRankThreshold_t * s)
{
    static int Mode=-1,Profile=-1;
    if(Mode<0)
    {
        Mode=Cec_TranStrictCexOption("ABC_STRICT_RANK_THRESHOLD_SORT",0,2);
        Profile=Cec_TranStrictCexOption("ABC_STRICT_RANK_THRESHOLD_SORT_PROFILE",0,1);
    }
    s->Mode=Mode;s->Profile=Profile;s->Enabled=Mode||Profile;
}

static void Cec_TranRankThresholdCheck(Cec_TranRankThreshold_t * s,
    Cec_TranDivRank_t const * ranks,Cec_TranDivRank_t const * ref,int second)
{
    int i;
    for(i=0;i<s->N;++i)
    {
        assert(ranks[i].Score==ref[i].Score);
        assert(ranks[i].CiOverlap==ref[i].CiOverlap);
        assert(ranks[i].iPos==ref[i].iPos);
        if(second)++s->SecondChecks;
        else {++s->FirstChecks;++s->CiOrderChecks;}
    }
}

static Cec_TranDivRank_t * Cec_TranRankThresholdReference(
    Cec_TranRankThreshold_t * s,Cec_TranDivRank_t const * ranks)
{
    Cec_TranDivRank_t * ref;abctime clk=Abc_Clock();
    ref=ABC_ALLOC(Cec_TranDivRank_t,s->N);assert(ref);
    memcpy(ref,ranks,(size_t)s->N*sizeof(*ref));
    qsort(ref,s->N,sizeof(*ref),Cec_TranDivRankCompare);
    s->OracleBytes=(word)s->N*sizeof(*ref);
    s->OracleTicks+=Abc_Clock()-clk;
    return ref;
}

static void Cec_TranRankThresholdFinishReference(Cec_TranRankThreshold_t * s,
    Cec_TranDivRank_t const * ranks,Cec_TranDivRank_t * ref,int second)
{
    abctime clk;
    if(!ref)return;
    clk=Abc_Clock();Cec_TranRankThresholdCheck(s,ranks,ref,second);
    ABC_FREE(ref);s->OracleTicks+=Abc_Clock()-clk;
}

static void Cec_TranRankThresholdFirst(Cec_TranRankThreshold_t * s,
    Cec_TranDivRank_t * ranks,int n,int b,word cutoff,int finalMode)
{
    int i,h=0,e=0,p=0,ciZero=1;
    Cec_TranDivRank_t * ref=NULL;abctime clk=0;
    s->N=n;s->B=b;s->Cutoff=cutoff;
    s->Reason="disabled";s->SecondKind="full";s->SecondReason="disabled";
    assert(n>=0 && (size_t)n<=(size_t)-1/sizeof(*ranks));
    if(s->Mode==2)ref=Cec_TranRankThresholdReference(s,ranks);
    if(s->Profile)clk=Abc_Clock();
    // The measured mode0 control does no observer-only full-array scan.
    if(!s->Mode)goto original;
    s->Reason="final-filter-off";
    if(!finalMode)goto original;
    s->Reason="dimensions";
    if(n<=0 || b<=0 || b>n)goto original;
    s->PartitionKnown=1;s->InputMonotone=1;
    for(i=0;i<n;++i)
    {
        if(ranks[i].Score>cutoff)++s->H;
        else if(ranks[i].Score==cutoff)++s->E;
        else ++s->P;
        if(ranks[i].CiOverlap)ciZero=0;
        if(i && ranks[i-1].iPos>=ranks[i].iPos)s->InputMonotone=0;
    }
    s->Reason="initial-ci";if(!ciZero)goto original;
    s->Reason="position-order";if(!s->InputMonotone)goto original;
    s->Reason="cutoff-not-Bth";
    if(s->H>=b || s->H+s->E<b)goto original;
    s->Buffer=ABC_ALLOC(Cec_TranDivRank_t,n);
    s->Reason="buffer-allocation";if(!s->Buffer)goto original;
    s->ScratchBytes=(word)n*sizeof(*ranks);
    e=s->H;p=s->H+s->E;
    for(i=0;i<n;++i)
        if(ranks[i].Score>cutoff)s->Buffer[h++]=ranks[i];
        else if(ranks[i].Score==cutoff)s->Buffer[e++]=ranks[i];
        else s->Buffer[p++]=ranks[i];
    assert(h==s->H && e==s->H+s->E && p==n);
    qsort(s->Buffer,s->H,sizeof(*ranks),Cec_TranDivRankCompare);
    qsort(s->Buffer+s->H+s->E,s->P,sizeof(*ranks),Cec_TranDivRankCompare);
    memcpy(ranks,s->Buffer,(size_t)n*sizeof(*ranks));
    s->FirstSorted=s->H+s->P;s->FirstMoved=(word)2*n;
    s->Applied=1;s->Reason="none";goto finish;
original:
    qsort(ranks,n,sizeof(*ranks),Cec_TranDivRankCompare);s->FirstSorted=n;
finish:
    if(s->Profile)s->FirstTicks+=Abc_Clock()-clk;
    Cec_TranRankThresholdFinishReference(s,ranks,ref,0);
}

static void Cec_TranRankThresholdSecond(Cec_TranRankThreshold_t * s,
    Cec_TranDivRank_t * ranks)
{
    int i,j,minCi=0,maxCi=0,sum,count,* counts=NULL;
    Cec_TranDivRank_t * ref=NULL;abctime clk=0;
    if(s->Mode==2)ref=Cec_TranRankThresholdReference(s,ranks);
    if(s->Profile)clk=Abc_Clock();
    if(!s->Applied){s->SecondReason=s->Mode?"first-fallback":"disabled";goto full;}
    // CI may change only its key, not record identities or low-tail CI=0.
    for(i=0;i<s->N;++i)
    {
        s->SecondReason="changed-record";
        if(ranks[i].Score!=s->Buffer[i].Score || ranks[i].iPos!=s->Buffer[i].iPos)goto full;
        s->SecondReason="changed-tail";
        if(i>=s->H+s->E && ranks[i].CiOverlap)goto full;
    }
    qsort(ranks,s->H,sizeof(*ranks),Cec_TranDivRankCompare);s->SecondSorted=s->H;
    s->SecondReason="none";
    if(s->E<=1){s->SecondKind="trivial";goto finish;}
    minCi=maxCi=ranks[s->H].CiOverlap;
    for(i=s->H+1;i<s->H+s->E;++i)
    {minCi=Abc_MinInt(minCi,ranks[i].CiOverlap);maxCi=Abc_MaxInt(maxCi,ranks[i].CiOverlap);}
    s->BucketSpan=(word)((long long)maxCi-(long long)minCi+1);
    s->SecondReason="negative-ci";if(minCi<0)goto segment;
    // A general linear-work rule: the histogram span never exceeds the
    // number of tied records. No benchmark/circuit-specific thresholds.
    s->SecondReason="bucket-span";if(s->BucketSpan>(word)s->E)goto segment;
    s->SecondReason="count-size";
    if(s->BucketSpan>(size_t)-1/sizeof(int))goto segment;
    counts=ABC_CALLOC(int,(size_t)s->BucketSpan);
    s->SecondReason="count-allocation";if(!counts)goto segment;
    s->CountBytes=s->BucketSpan*sizeof(int);
    for(i=s->H;i<s->H+s->E;++i)++counts[ranks[i].CiOverlap-minCi];
    sum=s->H;
    for(j=(int)s->BucketSpan;j-- >0;)
    {count=counts[j];counts[j]=sum;sum+=count;}
    assert(sum==s->H+s->E);
    for(i=s->H;i<s->H+s->E;++i)s->Buffer[counts[ranks[i].CiOverlap-minCi]++]=ranks[i];
    memcpy(ranks+s->H,s->Buffer+s->H,(size_t)s->E*sizeof(*ranks));
    ABC_FREE(counts);s->BucketRecords=s->E;s->SecondMoved=(word)2*s->E;
    s->SecondKind="bucket";s->SecondReason="none";goto finish;
segment:
    qsort(ranks+s->H,s->E,sizeof(*ranks),Cec_TranDivRankCompare);
    s->SecondSorted+=s->E;s->SecondKind="segment";goto finish;
full:
    qsort(ranks,s->N,sizeof(*ranks),Cec_TranDivRankCompare);
    s->SecondSorted=s->N;s->SecondKind="full";
finish:
    if(s->Profile)s->SecondTicks+=Abc_Clock()-clk;
    Cec_TranRankThresholdFinishReference(s,ranks,ref,1);
    // No ordering scratch remains resident during downstream core selection.
    if(s->Buffer)
    {
        if(s->Profile)clk=Abc_Clock();
        ABC_FREE(s->Buffer);
        if(s->Profile)s->FreeTicks+=Abc_Clock()-clk;
    }
}

static void Cec_TranRankThresholdStop(Cec_TranRankThreshold_t * s,
    int boundMode,int finalMode,int scope,int round,int wave,int root)
{
    abctime clk=0;
    if(!s->Enabled)return;
    if(s->Buffer)
    {
        if(s->Profile)clk=Abc_Clock();
        ABC_FREE(s->Buffer);
        if(s->Profile)s->FreeTicks+=Abc_Clock()-clk;
    }
    if(s->Profile)
        Abc_Print(1,"stran-rank-threshold-sort profile: schema=1 mode=%d bound-mode=%d filter-mode=%d status=%s reason=%s source-scope=%d round=%d wave=%d root=%d B=%d cutoff=%llu records=%d partition-known=%d H=%d E=%d P=%d input-monotone=%d first-qsort-records=%llu second-qsort-records=%llu bucket-records=%llu bucket-span=%llu first-moved-records=%llu second-moved-records=%llu scratch-bytes=%llu count-bytes=%llu oracle-bytes=%llu second-kind=%s second-reason=%s oracle-first-checks=%llu oracle-second-checks=%llu oracle-ci-order-checks=%llu first-sec=%.6f second-sec=%.6f free-sec=%.6f oracle-sec=%.6f\n",
            s->Mode,boundMode,finalMode,!s->Mode?"DISABLED":s->Applied?"APPLIED":"FALLBACK",s->Reason,
            scope,round,wave,root,s->B,(unsigned long long)s->Cutoff,s->N,s->PartitionKnown,s->H,s->E,s->P,s->InputMonotone,
            (unsigned long long)s->FirstSorted,(unsigned long long)s->SecondSorted,(unsigned long long)s->BucketRecords,(unsigned long long)s->BucketSpan,
            (unsigned long long)s->FirstMoved,(unsigned long long)s->SecondMoved,(unsigned long long)s->ScratchBytes,(unsigned long long)s->CountBytes,(unsigned long long)s->OracleBytes,
            s->SecondKind,s->SecondReason,(unsigned long long)s->FirstChecks,(unsigned long long)s->SecondChecks,(unsigned long long)s->CiOrderChecks,
            (double)s->FirstTicks/CLOCKS_PER_SEC,(double)s->SecondTicks/CLOCKS_PER_SEC,(double)s->FreeTicks/CLOCKS_PER_SEC,(double)s->OracleTicks/CLOCKS_PER_SEC);
}

// Independent stable insertion oracle, separate from the production qsort
// comparator and histogram. All fixture CI differences fit signed int.
