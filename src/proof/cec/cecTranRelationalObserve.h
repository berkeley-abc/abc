// Default-off obligation accounting. No observation changes a proof answer.
// A source owner is one immutable root pass; recipe-batch IDs are never keys.
#define CEC_REL_OBSERVE_REQUIRE(C) do { if(!(C)) { \
    Abc_Print(-1,"Assertion relational observation identity failed: %s\n",#C);abort(); } } while(0)

typedef struct Cec_TranRelObserve_t_ {
    Gia_Man_t * Source;
    Vec_Int_t * SourceKey;
    Cec_TranCandVec_t Closed;
    Cec_TranCand_t const * Helpers, * Targets;
    Vec_Str_t * PriorClosed;
    long long Epoch, Calls;
    unsigned long long SourceDigest;
    int Frames, DepthRevision, nHelpers, nTargets, ClosedBefore, nPriorClosed;
    long long Queries[2][3][4]; // base/ind, helper/target/prior-closed, all/UNSAT/SAT/UNKNOWN
    abctime SatTicks[2][3], ObserveTicks;
} Cec_TranRelObserve_t;

static Cec_TranRelObserve_t * Cec_TranRelObserveCurrent=NULL;
static long long Cec_TranRelObserveNextEpoch=0;

static int Cec_TranRelObserveEnabled()
{
    char const * s=getenv("ABC_STRAN_RELATIONAL_OBSERVE");
    if(!s || !strcmp(s,"0"))return 0;
    if(!strcmp(s,"1"))return 1;
    Abc_Print(-1,"stran-quality-invalid-option: ABC_STRAN_RELATIONAL_OBSERVE must be 0 or 1\n");
    exit(2);return 0;
}

// Full structural descriptor, excluding mutable scratch Value/mark/ref fields.
// CI and CO order plus register partition identify the transition interface.
static Vec_Int_t * Cec_TranRelObserveSourceKey(Gia_Man_t * p)
{
    Vec_Int_t * key=Vec_IntAlloc(3*Gia_ManObjNum(p)+16);
    Gia_Obj_t * o;int i,type;
    Vec_IntPush(key,Gia_ManObjNum(p));Vec_IntPush(key,Gia_ManCiNum(p));
    Vec_IntPush(key,Gia_ManCoNum(p));Vec_IntPush(key,Gia_ManRegNum(p));
    Vec_IntPush(key,p->nConstrs);
    Gia_ManForEachObj(p,o,i)
    {
        type=i==0 ? 0 : Gia_ObjIsCi(o) ? 1 : Gia_ObjIsCo(o) ? 2 :
            Gia_ObjIsBuf(o) ? 3 : Gia_ObjIsXor(o) ? 4 : 5;
        Vec_IntPush(key,type);
        Vec_IntPush(key,type>=2 ? Gia_ObjFaninLit0p(p,o) : -1);
        Vec_IntPush(key,type>=4 ? Gia_ObjFaninLit1p(p,o) : -1);
    }
    Gia_ManForEachCi(p,o,i)Vec_IntPush(key,Gia_ObjId(p,o));
    Gia_ManForEachCo(p,o,i)Vec_IntPush(key,Gia_ObjId(p,o));
    return key;
}

static int Cec_TranRelObserveSameKey(Vec_Int_t * a,Vec_Int_t * b)
{return Vec_IntSize(a)==Vec_IntSize(b) && !memcmp(Vec_IntArray(a),Vec_IntArray(b),sizeof(int)*Vec_IntSize(a));}

static Cec_TranRelObserve_t Cec_TranRelObserveStart(Gia_Man_t * source,int enabled)
{
    Cec_TranRelObserve_t s;int i,value;
    memset(&s,0,sizeof(s));
    if(!enabled)return s;
    s.Source=source;s.SourceKey=Cec_TranRelObserveSourceKey(source);
    s.Epoch=++Cec_TranRelObserveNextEpoch;s.SourceDigest=1469598103934665603ULL;
    Vec_IntForEachEntry(s.SourceKey,value,i)
    {s.SourceDigest^=(unsigned)value;s.SourceDigest*=1099511628211ULL;}
    // Digest is diagnostic only. Identity uses owner and the full descriptor.
    s.PriorClosed=Vec_StrAlloc(64);return s;
}

static Cec_TranCand_t const * Cec_TranRelObserveCandidate(Cec_TranRelObserve_t * s,int i)
{return i<s->nHelpers ? s->Helpers+i : s->Targets+i-s->nHelpers;}

static int Cec_TranRelObserveSourceMatches(Cec_TranRelObserve_t * s,Gia_Man_t * source)
{
    Vec_Int_t * key;int same;
    if(s->Source!=source)return 0;
    key=Cec_TranRelObserveSourceKey(source);same=Cec_TranRelObserveSameKey(key,s->SourceKey);
    Vec_IntFree(key);return same;
}

static void Cec_TranRelObserveBegin(Cec_TranRelObserve_t * s,Gia_Man_t * source,
    Cec_TranCand_t const * helpers,int nHelpers,Cec_TranCand_t const * targets,int nTargets,int frames)
{
    int i;abctime start=Abc_Clock();
    CEC_REL_OBSERVE_REQUIRE(s->Source==source && nHelpers>=0 && nTargets>0 && frames>0);
    CEC_REL_OBSERVE_REQUIRE(Cec_TranRelObserveSourceMatches(s,source));
    if(s->Frames!=frames)
    {Cec_TranCandVecClear(&s->Closed);s->Frames=frames;++s->DepthRevision;}
    s->Helpers=helpers;s->Targets=targets;s->nHelpers=nHelpers;s->nTargets=nTargets;
    s->ClosedBefore=s->Closed.nSize;s->nPriorClosed=0;++s->Calls;
    memset(s->Queries,0,sizeof(s->Queries));memset(s->SatTicks,0,sizeof(s->SatTicks));
    Vec_StrFill(s->PriorClosed,nHelpers+nTargets,0);
    for(i=0;i<nHelpers+nTargets;++i)
        if(Cec_TranCandVecContains(&s->Closed,Cec_TranRelObserveCandidate(s,i)))
        {Vec_StrWriteEntry(s->PriorClosed,i,1);++s->nPriorClosed;}
    s->ObserveTicks+=Abc_Clock()-start;
}

static void Cec_TranRelObserveQuery(int ind,int edge,int status,abctime ticks)
{
    Cec_TranRelObserve_t * s=Cec_TranRelObserveCurrent;
    int lane,answer;
    if(!s)return;
    CEC_REL_OBSERVE_REQUIRE(edge>=0 && edge<s->nHelpers+s->nTargets && (ind==0 || ind==1));
    lane=edge<s->nHelpers ? 0 : 1;
    answer=status==l_False ? 1 : status==l_True ? 2 : 3;
    CEC_REL_OBSERVE_REQUIRE(status==l_False || status==l_True || status==l_Undef);
    ++s->Queries[ind][lane][0];++s->Queries[ind][lane][answer];s->SatTicks[ind][lane]+=ticks;
    if(Vec_StrEntry(s->PriorClosed,edge))
    {++s->Queries[ind][2][0];++s->Queries[ind][2][answer];s->SatTicks[ind][2]+=ticks;}
}

static void Cec_TranRelObservePrint(Cec_TranRelObserve_t * s,char const * stage,int round)
{
    int f,l;abctime start;
    char const * lanes[3]={"helper","target","prior-closed"};
    if(!s)return;
    start=Abc_Clock();
    Abc_Print(1,"stran-root relational-obligation-work: schema=1 source-epoch=%lld source-digest=%llu source-objs=%d depth=%d depth-revision=%d batch=%lld stage=%s round=%d helpers=%d targets=%d prior-closed-relations=%d closed-before=%d closed-now=%d observe-sec=%.6f",
        s->Epoch,s->SourceDigest,Gia_ManObjNum(s->Source),s->Frames,s->DepthRevision,s->Calls,stage,round,
        s->nHelpers,s->nTargets,s->nPriorClosed,s->ClosedBefore,s->Closed.nSize,(double)s->ObserveTicks/CLOCKS_PER_SEC);
    for(f=0;f<2;++f)for(l=0;l<3;++l)
        Abc_Print(1," %s-%s-queries=%lld %s-%s-unsat=%lld %s-%s-sat=%lld %s-%s-unknown=%lld %s-%s-sec=%.6f",
            f?"ind":"base",lanes[l],s->Queries[f][l][0],f?"ind":"base",lanes[l],s->Queries[f][l][1],
            f?"ind":"base",lanes[l],s->Queries[f][l][2],f?"ind":"base",lanes[l],s->Queries[f][l][3],
            f?"ind":"base",lanes[l],(double)s->SatTicks[f][l]/CLOCKS_PER_SEC);
    Abc_Print(1,"\n");fflush(stdout);s->ObserveTicks+=Abc_Clock()-start;
}

// Only full returned closed subsets enter this observation set. Individual
// UNSATs under a changing Frozen H never enter it; UNKNOWN/refuted do not enter.
// This set is queried for COUNTERS ONLY and grants no certificate or assumption.
static void Cec_TranRelObserveClosed(Cec_TranRelObserve_t * s,Vec_Int_t * status,int rounds)
{
    int i,value;abctime start;
    if(!s)return;
    start=Abc_Clock();CEC_REL_OBSERVE_REQUIRE(Vec_IntSize(status)==s->nHelpers+s->nTargets);
    Vec_IntForEachEntry(status,value,i)
    {
        CEC_REL_OBSERVE_REQUIRE(value>=-1 && value<=1);
        if(value==1 && !Cec_TranCandVecContains(&s->Closed,Cec_TranRelObserveCandidate(s,i)))
            Cec_TranCandVecPush(&s->Closed,*Cec_TranRelObserveCandidate(s,i));
    }
    s->ObserveTicks+=Abc_Clock()-start;Cec_TranRelObservePrint(s,"closed",rounds);
}

static void Cec_TranRelObserveStop(Cec_TranRelObserve_t * s)
{
    if(!s->Source)return;
    CEC_REL_OBSERVE_REQUIRE(Cec_TranRelObserveCurrent!=s);
    Cec_TranRelObservePrint(s,"source-stop",0);
    Cec_TranCandVecStop(&s->Closed);Vec_StrFree(s->PriorClosed);Vec_IntFree(s->SourceKey);
    memset(s,0,sizeof(*s));
}
