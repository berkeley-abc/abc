// Exact maxima for immutable (vertex,target) groups within one GWMIN call.
// This private fragment follows the original RootLoss definition.
typedef struct Cec_TranRootMaxMember_t_ { int Vertex, Next; } Cec_TranRootMaxMember_t;
typedef struct Cec_TranRootMaxGroup_t_ { int Head, Witness; } Cec_TranRootMaxGroup_t;
struct Cec_TranSelectionRootMax_t_ {
    int Mode, Profile, Applied, Building, NVertices, NObjects, Captured;
    int AllocationAttempt, FailAt;
    char const * Reason;
    size_t Limit, Current, Peak, MemberCap, GroupCap, NMembers, NGroups;
    size_t * MemberBeg, * GroupBeg;
    Cec_TranRootMaxMember_t * Members;
    Cec_TranRootMaxGroup_t * Groups;
    int * BuildGroup;
    unsigned * BuildSeen, BuildEpoch;
    Cec_TranCandVec_t const * Vertices;
    Cec_TranConflictGraph_t Reference;
    Vec_Int_t RefNeighbors;
    int * RefBest;
    unsigned * RefSeen, RefTravId;
    word InitialCalls, UpdateCalls, OriginalUpdates, CacheUpdates;
    word GroupVisits, LiveHits, DeadHits, Rescans, MemberVisits, Expired;
    word PayloadBytes, CacheBytes, OracleBytes;
    word OracleInitial, OracleUpdate, OracleNeighbors;
    abctime SetupTicks, InitialTicks, UpdateTicks, FreeTicks, OracleTicks;
};

static void Cec_TranRootMaxInit(Cec_TranSelectionRootMax_t * s,
    int mode, int profile, size_t limit, int failAt)
{
    memset(s,0,sizeof(*s));
    s->Mode=mode; s->Profile=profile; s->Limit=limit;
    s->FailAt=failAt; s->Reason="disabled";
}

static void * Cec_TranRootMaxAlloc(Cec_TranSelectionRootMax_t * s,
    size_t count, size_t size, int clear)
{
    void * p;
    size_t bytes;
    if(count && size>(size_t)-1/count)
    { s->Reason="dimensions"; return NULL; }
    bytes=count*size;
    if(bytes>s->Limit || s->Current>s->Limit-bytes)
    { s->Reason="cap"; return NULL; }
    ++s->AllocationAttempt;
    p=s->AllocationAttempt==s->FailAt ? NULL :
        clear ? calloc(count,size) : malloc(bytes);
    if(!p) { s->Reason="allocation"; return NULL; }
    s->Current+=bytes;
    if(s->Peak<s->Current) s->Peak=s->Current;
    return p;
}

static void Cec_TranRootMaxFree(Cec_TranSelectionRootMax_t * s,
    void * p, size_t count, size_t size)
{
    if(!p) return;
    assert(s->Current>=count*size);
    s->Current-=count*size;
    free(p);
}

static void Cec_TranRootMaxRelease(Cec_TranSelectionRootMax_t * s)
{
    abctime clk=s->Profile ? Abc_Clock() : 0;
#define CEC_ROOTMAX_FREE(field,count) do { \
    Cec_TranRootMaxFree(s,s->field,(count),sizeof(*s->field)); s->field=NULL; \
} while(0)
    CEC_ROOTMAX_FREE(MemberBeg,(size_t)s->NVertices+1);
    CEC_ROOTMAX_FREE(GroupBeg,(size_t)s->NVertices+1);
    CEC_ROOTMAX_FREE(Members,s->MemberCap);
    CEC_ROOTMAX_FREE(Groups,s->GroupCap);
    CEC_ROOTMAX_FREE(BuildGroup,(size_t)s->NObjects);
    CEC_ROOTMAX_FREE(BuildSeen,(size_t)s->NObjects);
    CEC_ROOTMAX_FREE(Reference.pSeen,(size_t)s->NVertices);
    CEC_ROOTMAX_FREE(RefNeighbors.pArray,(size_t)s->NVertices);
    CEC_ROOTMAX_FREE(RefBest,(size_t)s->NObjects);
    CEC_ROOTMAX_FREE(RefSeen,(size_t)s->NObjects);
#undef CEC_ROOTMAX_FREE
    assert(!s->Current);
    s->Building=0;
    if(s->Profile) s->FreeTicks+=Abc_Clock()-clk;
}

static int Cec_TranRootMaxGrow(Cec_TranSelectionRootMax_t * s,
    void * array, size_t * capacity, size_t used, size_t need, size_t size, void ** result)
{
    size_t cap=*capacity ? *capacity : 64;
    void * p;
    if(need<=*capacity) { *result=array; return 1; }
    while(cap<need)
    {
        if(cap>(size_t)-1/2) { cap=need; break; }
        cap*=2;
    }
    // Allocate-copy-free deliberately accounts for both buffers at peak.
    p=Cec_TranRootMaxAlloc(s,cap,size,0);
    if(!p) return 0;
    if(used) memcpy(p,array,used*size);
    Cec_TranRootMaxFree(s,array,*capacity,size);
    *result=p; *capacity=cap;
    return 1;
}

static void Cec_TranRootMaxStart(Cec_TranSelectionRootMax_t * s,
    Cec_TranConflictGraph_t const * graph, Cec_TranCandVec_t const * vertices)
{
    abctime clk=s->Profile ? Abc_Clock() : 0;
    size_t v,n;
    s->NVertices=vertices->nSize; s->NObjects=Vec_WecSize(graph->vUsers);
    s->Vertices=vertices;
    if(!s->NVertices) { s->Reason="empty"; goto done; }
    if(!s->Mode) goto done;
    s->Reason="dimensions";
    if(sizeof(int)!=4 || sizeof(Cec_TranRootMaxMember_t)!=8 ||
        sizeof(Cec_TranRootMaxGroup_t)!=8 || s->NVertices<0 ||
        s->NObjects<=0 || graph->nVertices!=s->NVertices)
        goto done;
    v=(size_t)s->NVertices; n=(size_t)s->NObjects;
#define CEC_ROOTMAX_ALLOC(type,field,count,clear) do { \
    s->field=(type *)Cec_TranRootMaxAlloc(s,(count),sizeof(*s->field),(clear)); \
    if(!s->field) goto failed; \
} while(0)
    CEC_ROOTMAX_ALLOC(size_t,MemberBeg,v+1,0);
    CEC_ROOTMAX_ALLOC(size_t,GroupBeg,v+1,0);
    CEC_ROOTMAX_ALLOC(int,BuildGroup,n,0);
    CEC_ROOTMAX_ALLOC(unsigned,BuildSeen,n,1);
    if(s->Mode==2)
    {
        // Only immutable incidence is borrowed. Never Stop this shallow graph.
        s->Reference=*graph; s->Reference.TravId=0; s->Reference.pSeen=NULL;
        CEC_ROOTMAX_ALLOC(unsigned,Reference.pSeen,v,1);
        CEC_ROOTMAX_ALLOC(int,RefNeighbors.pArray,v,0);
        s->RefNeighbors.nCap=s->NVertices;
        CEC_ROOTMAX_ALLOC(int,RefBest,n,0);
        CEC_ROOTMAX_ALLOC(unsigned,RefSeen,n,1);
        s->OracleBytes=(word)v*(sizeof(unsigned)+sizeof(int))+
            (word)n*(sizeof(unsigned)+sizeof(int));
    }
#undef CEC_ROOTMAX_ALLOC
    s->Building=1; s->Reason="none";
    goto done;
failed:
    Cec_TranRootMaxRelease(s);
done:
    if(s->Profile) s->SetupTicks+=Abc_Clock()-clk;
}

// Capture only the already produced original all-active initial neighbor list.
// Each per-vertex list fits the original Vec_Int int length; global offsets do not.
static void Cec_TranRootMaxCapture(Cec_TranSelectionRootMax_t * s,
    int vertex, Vec_Int_t * neighbors)
{
    size_t mb=s->NMembers,gb=s->NGroups,g;
    int i,other,target;
    Cec_TranRootMaxGroup_t * group;
    void * grown;
    if(!s->Building) return;
    assert(vertex==s->Captured);
    if((size_t)Vec_IntSize(neighbors)>(size_t)-1-mb)
    { s->Reason="dimensions"; goto failed; }
    if(!Cec_TranRootMaxGrow(s,s->Members,&s->MemberCap,
        s->NMembers,mb+(size_t)Vec_IntSize(neighbors),sizeof(*s->Members),&grown))
        goto failed;
    s->Members=(Cec_TranRootMaxMember_t *)grown;
    if(++s->BuildEpoch==0)
    {
        memset(s->BuildSeen,0,(size_t)s->NObjects*sizeof(unsigned));
        s->BuildEpoch=1;
    }
    s->MemberBeg[vertex]=mb; s->GroupBeg[vertex]=gb;
    Vec_IntForEachEntry(neighbors,other,i)
    {
        target=s->Vertices->pArray[other].iTarget;
        assert(target>=0 && target<s->NObjects);
        if(s->BuildSeen[target]!=s->BuildEpoch)
        {
            if(s->NGroups==(size_t)-1)
            { s->Reason="dimensions"; goto failed; }
            if(!Cec_TranRootMaxGrow(s,s->Groups,&s->GroupCap,
                s->NGroups,s->NGroups+1,sizeof(*s->Groups),&grown)) goto failed;
            s->Groups=(Cec_TranRootMaxGroup_t *)grown;
            g=s->NGroups++;
            assert(g-gb<=(size_t)INT_MAX);
            s->BuildGroup[target]=(int)(g-gb);
            s->BuildSeen[target]=s->BuildEpoch;
            s->Groups[g].Head=-1; s->Groups[g].Witness=other;
        }
        else g=gb+(size_t)s->BuildGroup[target];
        group=s->Groups+g;
        if(s->Vertices->pArray[group->Witness].Gain<s->Vertices->pArray[other].Gain)
            group->Witness=other;
        s->Members[mb+(size_t)i].Vertex=other;
        s->Members[mb+(size_t)i].Next=group->Head;
        group->Head=i;
        ++s->NMembers;
    }
    ++s->Captured;
    s->MemberBeg[vertex+1]=s->NMembers;
    s->GroupBeg[vertex+1]=s->NGroups;
    return;
failed:
    // Initial original losses remain valid; disable every cached update.
    Cec_TranRootMaxRelease(s);
}

static long long Cec_TranRootMaxRead(Cec_TranSelectionRootMax_t * s,
    int vertex, char const * active, int count)
{
    size_t g,mb=s->MemberBeg[vertex];
    long long loss=0;
    word visits=0,live=0,dead=0,rescans=0,members=0,expired=0;
    int witness,j,other;
    for(g=s->GroupBeg[vertex];g<s->GroupBeg[vertex+1];++g)
    {
        Cec_TranRootMaxGroup_t * group=s->Groups+g;
        ++visits;
        witness=group->Witness;
        if(witness<0) { ++dead; continue; }
        if(active[witness]) ++live;
        else
        {
            ++rescans; witness=-1;
            for(j=group->Head;j>=0;j=s->Members[mb+(size_t)j].Next)
            {
                ++members;
                other=s->Members[mb+(size_t)j].Vertex;
                if(active[other] && (witness<0 ||
                    s->Vertices->pArray[witness].Gain<s->Vertices->pArray[other].Gain))
                    witness=other;
            }
            group->Witness=witness;
            expired+=witness<0;
        }
        if(witness>=0) loss+=s->Vertices->pArray[witness].Gain;
    }
    if(count)
    {
        s->GroupVisits+=visits; s->LiveHits+=live; s->DeadHits+=dead;
        s->Rescans+=rescans; s->MemberVisits+=members; s->Expired+=expired;
    }
    return loss;
}

static void Cec_TranRootMaxOracle(Cec_TranSelectionRootMax_t * s,
    int vertex, char const * active, long long actual, int initial)
{
    abctime clk=s->Profile ? Abc_Clock() : 0;
    long long reference=Cec_TranConflictGraphRootLoss(&s->Reference,s->Vertices,
        vertex,active,&s->RefNeighbors,s->RefBest,s->RefSeen,&s->RefTravId,NULL);
    assert(reference==actual);
    if(initial) ++s->OracleInitial; else ++s->OracleUpdate;
    s->OracleNeighbors+=(word)Vec_IntSize(&s->RefNeighbors);
    if(s->Profile) s->OracleTicks+=Abc_Clock()-clk;
}

static void Cec_TranRootMaxFinish(Cec_TranSelectionRootMax_t * s,
    long long const * losses, char const * active)
{
    int i;
    if(!s->Building) return;
    assert(s->Captured==s->NVertices);
    s->Building=0; s->Applied=1;
    Cec_TranRootMaxFree(s,s->BuildGroup,(size_t)s->NObjects,sizeof(int));
    Cec_TranRootMaxFree(s,s->BuildSeen,(size_t)s->NObjects,sizeof(unsigned));
    s->BuildGroup=NULL; s->BuildSeen=NULL;
    s->PayloadBytes=(word)s->NMembers*sizeof(*s->Members)+
        (word)s->NGroups*sizeof(*s->Groups);
    s->CacheBytes=(word)s->Current-s->OracleBytes;
    if(s->Mode==2)
        for(i=0;i<s->NVertices;++i)
        {
            long long cached=Cec_TranRootMaxRead(s,i,active,0);
            assert(cached==losses[i]);
            Cec_TranRootMaxOracle(s,i,active,cached,1);
        }
}

static void Cec_TranRootMaxPrint(Cec_TranSelectionRootMax_t const * s,
    Cec_TranSelectionDirty_t const * dirty, long long edges, int selected)
{
    char const * status=!s->NVertices ? "EMPTY" : !s->Mode ? "DISABLED" :
        s->Applied ? "APPLIED" : "FALLBACK";
    if(!s->Profile) return;
    assert(s->InitialCalls==(word)s->NVertices);
    assert(s->UpdateCalls==dirty->DirtyVertices);
    assert(s->OriginalUpdates+s->CacheUpdates==s->UpdateCalls);
    assert(s->GroupVisits==s->LiveHits+s->DeadHits+s->Rescans);
    assert(s->Expired<=s->Rescans);
    assert(s->Peak<=s->Limit);
    if(s->Applied) assert(s->NMembers==(size_t)edges*2);
    assert(s->OracleInitial==(s->Applied && s->Mode==2 ? (word)s->NVertices : 0));
    assert(s->OracleUpdate==(s->Applied && s->Mode==2 ? s->UpdateCalls : 0));
    Abc_Print(1,"stran-selection-rootmax profile: schema=1 scope=seq-discovery mode=%d status=%s reason=%s call=%d round=%d wave=%d vertices=%d edges=%lld selected=%d heap-pops=%llu dirty-vertices=%llu initial-calls=%llu update-calls=%llu original-update-calls=%llu cache-update-calls=%llu captured-vertices=%d members=%llu groups=%llu group-visits=%llu live-hits=%llu dead-hits=%llu rescans=%llu member-visits=%llu expired-groups=%llu cap-bytes=%llu payload-bytes=%llu cache-bytes=%llu oracle-bytes=%llu peak-bytes=%llu oracle-initial-checks=%llu oracle-update-checks=%llu oracle-neighbors=%llu setup-sec=%.6f initial-sec=%.6f update-sec=%.6f free-sec=%.6f oracle-sec=%.6f\n",
        s->Mode,status,s->Reason,dirty->Call,dirty->Round,dirty->Wave,s->NVertices,
        edges,selected,(unsigned long long)dirty->Epochs,(unsigned long long)dirty->DirtyVertices,
        (unsigned long long)s->InitialCalls,(unsigned long long)s->UpdateCalls,
        (unsigned long long)s->OriginalUpdates,(unsigned long long)s->CacheUpdates,s->Captured,
        (unsigned long long)(s->Applied ? s->NMembers : 0),(unsigned long long)(s->Applied ? s->NGroups : 0),
        (unsigned long long)s->GroupVisits,(unsigned long long)s->LiveHits,(unsigned long long)s->DeadHits,
        (unsigned long long)s->Rescans,(unsigned long long)s->MemberVisits,(unsigned long long)s->Expired,
        (unsigned long long)s->Limit,(unsigned long long)s->PayloadBytes,(unsigned long long)s->CacheBytes,
        (unsigned long long)(s->Applied ? s->OracleBytes : 0),(unsigned long long)s->Peak,
        (unsigned long long)s->OracleInitial,(unsigned long long)s->OracleUpdate,(unsigned long long)s->OracleNeighbors,
        Cec_TranTimeSec(s->SetupTicks),Cec_TranTimeSec(s->InitialTicks),Cec_TranTimeSec(s->UpdateTicks),
        Cec_TranTimeSec(s->FreeTicks),Cec_TranTimeSec(s->OracleTicks));
}
