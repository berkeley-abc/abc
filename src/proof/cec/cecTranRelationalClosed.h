// Default-off complete closed invariant bundles on one immutable source T.
// Full k-inductive bundles can be unioned. Individual old-H UNSATs cannot.
#define CEC_CLOSED_REQUIRE(C) do { if(!(C)) { \
    Abc_Print(-1,"Assertion closed invariant bundle failed: %s\n",#C);abort(); } } while(0)
typedef struct Cec_TranRelClosed_t_ {
    Gia_Man_t * Source;
    Vec_Int_t * SourceKey;
    Cec_TranCandVec_t Closed;
    Cec_TranCand_t const * Helpers, * Targets;
    Vec_Str_t * Known;
    Vec_Int_t * KnownIds;
    int Frames, nHelpers, nTargets, nKnown, ClosedBefore, Appended;
    long long Calls;
    abctime Ticks;
} Cec_TranRelClosed_t;
static Cec_TranRelClosed_t * Cec_TranRelClosedCurrent=NULL;
static int Cec_TranRelClosedEnabled()
{
    char const * s=getenv("ABC_STRAN_RELATIONAL_CLOSED");
    if(!s || !strcmp(s,"0"))return 0;
    if(!strcmp(s,"1"))return 1;
    Abc_Print(-1,"stran-quality-invalid-option: ABC_STRAN_RELATIONAL_CLOSED must be 0 or 1\n");
    exit(2);return 0;
}
static Cec_TranRelClosed_t Cec_TranRelClosedStart(Gia_Man_t * p,int enabled)
{
    Cec_TranRelClosed_t s;memset(&s,0,sizeof(s));
    if(enabled){s.Source=p;s.SourceKey=Cec_TranRelObserveSourceKey(p);s.Known=Vec_StrAlloc(64);s.KnownIds=Vec_IntAlloc(64);}
    return s;
}
static int Cec_TranRelClosedSourceMatches(Cec_TranRelClosed_t * s,Gia_Man_t * p)
{
    Vec_Int_t * key;int same;
    if(s->Source!=p)return 0;
    key=Cec_TranRelObserveSourceKey(p);same=Cec_TranRelObserveSameKey(key,s->SourceKey);
    Vec_IntFree(key);return same;
}
static Cec_TranCand_t const * Cec_TranRelClosedCandidate(Cec_TranRelClosed_t * s,int i)
{return i<s->nHelpers ? s->Helpers+i : s->Targets+i-s->nHelpers;}

// Retain ALL members, including proved helpers absent from later metadata.
// Preserve original order, append only missing exact recipes. Batch IDs are
// disposable and never enter this source-scoped identity.
static void Cec_TranRelClosedPrepare(Cec_TranRelClosed_t * s,Gia_Man_t * source,
    Cec_TranCand_t const * helpers,int nHelpers,Cec_TranCand_t const * targets,int nTargets,
    int frames,Cec_TranCandVec_t * expanded)
{
    Cec_TranCandVec_t present={0};int i;abctime start=Abc_Clock();
    CEC_CLOSED_REQUIRE(nHelpers>=0 && nTargets>0 && frames>0 && Cec_TranRelClosedSourceMatches(s,source));
    if(s->Frames!=frames){Cec_TranCandVecClear(&s->Closed);s->Frames=frames;}
    for(i=0;i<nHelpers;++i){Cec_TranCandVecPush(expanded,helpers[i]);Cec_TranCandVecPush(&present,helpers[i]);}
    for(i=0;i<nTargets;++i)Cec_TranCandVecPush(&present,targets[i]);
    s->Appended=0;
    for(i=0;i<s->Closed.nSize;++i)
        if(!Cec_TranCandVecContains(&present,s->Closed.pArray+i))
        {Cec_TranCandVecPush(expanded,s->Closed.pArray[i]);Cec_TranCandVecPush(&present,s->Closed.pArray[i]);++s->Appended;}
    for(i=0;i<s->Closed.nSize;++i)CEC_CLOSED_REQUIRE(Cec_TranCandVecContains(&present,s->Closed.pArray+i));
    Cec_TranCandVecStop(&present);
    s->Helpers=expanded->pArray;s->Targets=targets;s->nHelpers=expanded->nSize;s->nTargets=nTargets;
    s->ClosedBefore=s->Closed.nSize;s->nKnown=0;++s->Calls;
    Vec_StrFill(s->Known,s->nHelpers+nTargets,0);
    Vec_IntClear(s->KnownIds);
    for(i=0;i<s->nHelpers+nTargets;++i)
        if(Cec_TranCandVecContains(&s->Closed,Cec_TranRelClosedCandidate(s,i)))
        {Vec_StrWriteEntry(s->Known,i,1);Vec_IntPush(s->KnownIds,i);++s->nKnown;}
    s->Ticks+=Abc_Clock()-start;
    Abc_Print(1,"stran-root closed-bundle: schema=1 stage=enter depth=%d batch=%lld closed-before=%d helpers=%d targets=%d known-relations=%d appended=%d scope-sec=%.6f\n",
        frames,s->Calls,s->ClosedBefore,s->nHelpers,nTargets,s->nKnown,s->Appended,(double)s->Ticks/CLOCKS_PER_SEC);fflush(stdout);
}
static int Cec_TranRelClosedKnown(int edge)
{
    Cec_TranRelClosed_t * s=Cec_TranRelClosedCurrent;
    if(!s)return 0;
    CEC_CLOSED_REQUIRE(edge>=0 && edge<Vec_StrSize(s->Known));
    return Vec_StrEntry(s->Known,edge);
}
static void Cec_TranRelClosedRecord(Cec_TranRelClosed_t * s,Vec_Int_t * status)
{
    int i,value;abctime start;
    if(!s)return;
    start=Abc_Clock();CEC_CLOSED_REQUIRE(Cec_TranRelClosedSourceMatches(s,s->Source));
    CEC_CLOSED_REQUIRE(Vec_IntSize(status)==s->nHelpers+s->nTargets);
    Vec_IntForEachEntry(status,value,i)
    {
        CEC_CLOSED_REQUIRE(value>=-1 && value<=1);
        if(Vec_StrEntry(s->Known,i))CEC_CLOSED_REQUIRE(value==1);
        if(value==1 && !Cec_TranCandVecContains(&s->Closed,Cec_TranRelClosedCandidate(s,i)))
            Cec_TranCandVecPush(&s->Closed,*Cec_TranRelClosedCandidate(s,i));
    }
    s->Ticks+=Abc_Clock()-start;
    Abc_Print(1,"stran-root closed-bundle: schema=1 stage=closed depth=%d batch=%lld closed-before=%d closed-now=%d known-relations=%d scope-sec=%.6f\n",
        s->Frames,s->Calls,s->ClosedBefore,s->Closed.nSize,s->nKnown,(double)s->Ticks/CLOCKS_PER_SEC);fflush(stdout);
}
static void Cec_TranRelClosedStop(Cec_TranRelClosed_t * s)
{
    if(!s->Source)return;
    CEC_CLOSED_REQUIRE(Cec_TranRelClosedCurrent!=s);
    Cec_TranCandVecStop(&s->Closed);Vec_StrFree(s->Known);Vec_IntFree(s->KnownIds);Vec_IntFree(s->SourceKey);
    memset(s,0,sizeof(*s));
}
