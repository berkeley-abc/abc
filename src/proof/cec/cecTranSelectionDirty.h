// Ordered dirty-set construction for one immutable commit conflict graph.
// Only dirty enumeration uses the role stamps; loss and deletion queries do not.
typedef struct Cec_TranSelectionRootMax_t_ Cec_TranSelectionRootMax_t;
typedef struct Cec_TranSelectionDirty_t_ {
    Cec_TranSelectionRootMax_t * RootMax;
    int Mode, Profile, Applied, Call, Round, Wave, NObjects, NVertices;
    char const * Reason;
    unsigned Epoch, * Stamp;
    unsigned char * Roles;
    Cec_TranConflictGraph_t Reference;
    Vec_Int_t RefNeighbors, RefDirty;
    char * RefDirtyBits;
    word StateBytes, OracleBytes, Epochs, Removed, NeighborCalls, DirtyVertices;
    word MffcRequests, SupportRequests, BaselineEntries, ActualEntries;
    word SkippedEntries, SkippedLists, PartialLists, NeighborOutputs;
    word OracleEpochs, OracleDirtyChecks, PopHash, SelectedHash;
    abctime Started, SetupTicks, FreeTicks, PrepareTicks, GwminTicks;
    abctime InitialTicks, RemoveTicks, DirtyTicks, UpdateTicks;
    abctime RepairTicks, ApplyTicks, OracleTicks;
} Cec_TranSelectionDirty_t;

static word Cec_TranSelectionDirtyHash(word hash, int value)
{
    return (hash ^ (word)(unsigned)value) * ABC_CONST(1099511628211);
}

static void Cec_TranSelectionDirtyInit(Cec_TranSelectionDirty_t * s,
    int mode, int profile)
{
    memset(s, 0, sizeof(*s));
    s->Mode=mode; s->Profile=profile; s->Reason="disabled";
    s->PopHash=s->SelectedHash=ABC_CONST(0xcbf29ce484222325);
    if(profile) s->Started=Abc_Clock();
}

static void Cec_TranSelectionDirtyRelease(Cec_TranSelectionDirty_t * s)
{
    abctime clk=s->Profile ? Abc_Clock() : 0;
    ABC_FREE(s->Stamp); ABC_FREE(s->Roles);
    ABC_FREE(s->Reference.pSeen); ABC_FREE(s->RefDirtyBits);
    ABC_FREE(s->RefNeighbors.pArray); ABC_FREE(s->RefDirty.pArray);
    if(s->Profile) s->FreeTicks+=Abc_Clock()-clk;
}

// Failure injection is used only by the real helper selftest. Production passes0.
static void * Cec_TranSelectionDirtyAlloc(size_t count, size_t size,
    int * attempt, int failAt)
{
    ++*attempt;
    return *attempt==failAt ? NULL : calloc(count, size);
}

static void Cec_TranSelectionDirtyStart(Cec_TranSelectionDirty_t * s,
    Cec_TranConflictGraph_t const * graph, int failAt)
{
    int attempt=0;
    size_t n, v;
    abctime clk=s->Profile ? Abc_Clock() : 0;
    s->NObjects=Vec_WecSize(graph->vUsers); s->NVertices=graph->nVertices;
    if(!s->NVertices) { s->Reason="empty"; goto done; }
    if(!s->Mode) goto done;
    s->Reason="dimensions";
    if(s->NObjects<=0 || s->NVertices<0) goto done;
    n=(size_t)s->NObjects; v=(size_t)s->NVertices;
    if(n>(size_t)-1/(sizeof(unsigned)+sizeof(unsigned char)) ||
       v>(size_t)-1/(sizeof(unsigned)+sizeof(char)+2*sizeof(int))) goto done;
    s->Reason="allocation";
    s->Stamp=(unsigned *)Cec_TranSelectionDirtyAlloc(n,sizeof(unsigned),&attempt,failAt);
    s->Roles=(unsigned char *)Cec_TranSelectionDirtyAlloc(n,sizeof(unsigned char),&attempt,failAt);
    if(!s->Stamp || !s->Roles) goto failed;
    if(s->Mode==2)
    {
        // Borrow only immutable incidence arrays. The traversal/dirty scratch
        // is independent and is never passed to ConflictGraphStop.
        s->Reference=*graph; s->Reference.TravId=0;
        s->Reference.pSeen=(unsigned *)Cec_TranSelectionDirtyAlloc(v,sizeof(unsigned),&attempt,failAt);
        s->RefDirtyBits=(char *)Cec_TranSelectionDirtyAlloc(v,sizeof(char),&attempt,failAt);
        s->RefNeighbors.pArray=(int *)Cec_TranSelectionDirtyAlloc(v,sizeof(int),&attempt,failAt);
        s->RefDirty.pArray=(int *)Cec_TranSelectionDirtyAlloc(v,sizeof(int),&attempt,failAt);
        if(!s->Reference.pSeen || !s->RefDirtyBits ||
           !s->RefNeighbors.pArray || !s->RefDirty.pArray) goto failed;
        s->RefNeighbors.nCap=s->RefDirty.nCap=s->NVertices;
        s->OracleBytes=(word)v*(sizeof(unsigned)+sizeof(char)+2*sizeof(int));
    }
    s->StateBytes=(word)n*(sizeof(unsigned)+sizeof(unsigned char));
    s->Applied=1; s->Reason="none";
    goto done;
failed:
    Cec_TranSelectionDirtyRelease(s);
done:
    if(s->Profile) s->SetupTicks+=Abc_Clock()-clk;
}

static void Cec_TranSelectionDirtyEpoch(Cec_TranSelectionDirty_t * s)
{
    ++s->Epochs;
    if(s->Applied && ++s->Epoch==0)
    {
        memset(s->Stamp,0,(size_t)s->NObjects*sizeof(unsigned));
        s->Epoch=1;
    }
}

static void Cec_TranSelectionDirtyList(Cec_TranSelectionDirty_t * s,
    Cec_TranConflictGraph_t * graph, int object, int vertex, int requested,
    Vec_Int_t * neighbors)
{
    Vec_Int_t * users=Vec_WecEntry(graph->vUsers,object);
    int unseen=requested, user, other, i;
    int count=s->Profile || s->Mode==2;
    if(count)
    {
        if(requested==3) ++s->MffcRequests; else ++s->SupportRequests;
        s->BaselineEntries+=(word)Vec_IntSize(users);
    }
    if(s->Applied)
    {
        if(s->Stamp[object]!=s->Epoch)
            s->Stamp[object]=s->Epoch, s->Roles[object]=0;
        unseen=requested & ~s->Roles[object];
        s->Roles[object]|=(unsigned char)requested;
    }
    if(!unseen)
    {
        if(count) ++s->SkippedLists, s->SkippedEntries+=(word)Vec_IntSize(users);
        return;
    }
    if(count)
    {
        s->ActualEntries+=(word)Vec_IntSize(users);
        s->PartialLists+=unseen!=requested;
    }
    // A partial role request still reads the whole original list. Keep its
    // parity interleaving; splitting even/odd users would reorder first hits.
    Vec_IntForEachEntry(users,user,i)
    {
        if(!(unseen & (1 << Abc_LitIsCompl(user)))) continue;
        other=Abc_Lit2Var(user);
        if(other==vertex || graph->pSeen[other]==graph->TravId) continue;
        graph->pSeen[other]=graph->TravId;
        Vec_IntPush(neighbors,other);
    }
}

static void Cec_TranSelectionDirtyNeighbors(Cec_TranSelectionDirty_t * s,
    Cec_TranConflictGraph_t * graph, int vertex, Vec_Int_t * neighbors)
{
    int i, object;
    Vec_IntClear(neighbors);
    if(++graph->TravId==0)
    {
        memset(graph->pSeen,0,(size_t)graph->nVertices*sizeof(unsigned));
        graph->TravId=1;
    }
    graph->pSeen[vertex]=graph->TravId;
    for(i=Vec_IntEntry(graph->vMffcBeg,vertex);i<Vec_IntEntry(graph->vMffcBeg,vertex+1);++i)
    {
        object=Vec_IntEntry(graph->vMffcData,i);
        Cec_TranSelectionDirtyList(s,graph,object,vertex,3,neighbors);
    }
    for(i=Vec_IntEntry(graph->vSuppBeg,vertex);i<Vec_IntEntry(graph->vSuppBeg,vertex+1);++i)
    {
        object=Vec_IntEntry(graph->vSuppData,i);
        Cec_TranSelectionDirtyList(s,graph,object,vertex,1,neighbors);
    }
    if(s->Profile || s->Mode==2)
    {
        ++s->NeighborCalls;
        s->NeighborOutputs+=(word)Vec_IntSize(neighbors);
    }
}

static void Cec_TranSelectionDirtyCheck(Cec_TranSelectionDirty_t * s,
    Vec_Int_t * removed, char const * active, Vec_Int_t * dirty)
{
    int i,k,vertex,other;
    abctime clk=s->Profile ? Abc_Clock() : 0;
    Vec_IntClear(&s->RefDirty);
    Vec_IntForEachEntry(removed,vertex,i)
    {
        Cec_TranConflictGraphNeighbors(&s->Reference,vertex,&s->RefNeighbors);
        Vec_IntForEachEntry(&s->RefNeighbors,other,k)
            if(active[other] && !s->RefDirtyBits[other])
            {
                s->RefDirtyBits[other]=1;
                Vec_IntPush(&s->RefDirty,other);
            }
    }
    assert(Vec_IntSize(&s->RefDirty)==Vec_IntSize(dirty));
    Vec_IntForEachEntry(&s->RefDirty,other,i)
    {
        assert(other==Vec_IntEntry(dirty,i));
        s->RefDirtyBits[other]=0;
        ++s->OracleDirtyChecks;
    }
    ++s->OracleEpochs;
    if(s->Profile) s->OracleTicks+=Abc_Clock()-clk;
}

static void Cec_TranSelectionDirtySelected(Cec_TranSelectionDirty_t * s,
    Cec_TranCand_t const * c, int provedIndex)
{
    int i;
#define CEC_DIRTY_HASH(v) s->SelectedHash=Cec_TranSelectionDirtyHash(s->SelectedHash,(int)(v))
    CEC_DIRTY_HASH(provedIndex); CEC_DIRTY_HASH(c->iTarget);
    CEC_DIRTY_HASH(c->Gain); CEC_DIRTY_HASH(c->nMffc);
    CEC_DIRTY_HASH(c->nKind); CEC_DIRTY_HASH(c->fStrict);
    CEC_DIRTY_HASH(c->iOut); CEC_DIRTY_HASH(c->nGates);
    CEC_DIRTY_HASH(c->nProofStage); CEC_DIRTY_HASH(c->nProofLane);
    CEC_DIRTY_HASH(c->nProofPhase); CEC_DIRTY_HASH(c->nProofKind);
    for(i=0;i<2*c->nGates;++i) CEC_DIRTY_HASH(c->Recipe[i]);
#undef CEC_DIRTY_HASH
}

static void Cec_TranSelectionDirtyPrint(Cec_TranSelectionDirty_t * s,
    int proved, int vertices, long long edges, int selected,
    long long weight, int firstGain)
{
    char const * status=!vertices ? "EMPTY" : !s->Mode ? "DISABLED" :
        s->Applied ? "APPLIED" : "FALLBACK";
    if(!s->Profile) return;
    assert(s->BaselineEntries==s->ActualEntries+s->SkippedEntries);
    assert(s->Removed==(word)vertices && s->NeighborCalls==(word)vertices);
    assert(s->OracleEpochs==(s->Mode==2 && s->Applied ? s->Epochs : 0));
    assert(s->OracleDirtyChecks==(s->Mode==2 && s->Applied ? s->DirtyVertices : 0));
    if(!s->Applied) assert(s->NeighborOutputs==(word)edges*2);
    Abc_Print(1,"stran-selection-dirty profile: schema=1 scope=seq-discovery mode=%d status=%s reason=%s call=%d round=%d wave=%d initial-proved=%d vertices=%d edges=%lld selected=%d selected-weight=%lld first-gain=%d heap-pops=%llu removed=%llu neighbor-calls=%llu dirty-vertices=%llu mffc-requests=%llu support-requests=%llu baseline-entry-visits=%llu actual-entry-visits=%llu skipped-entry-visits=%llu skipped-lists=%llu partial-lists=%llu neighbor-outputs=%llu state-bytes=%llu oracle-bytes=%llu oracle-epochs=%llu oracle-dirty-checks=%llu pop-hash=%016llx selected-hash=%016llx prepare-sec=%.6f setup-sec=%.6f gwmin-sec=%.6f initial-loss-sec=%.6f remove-sec=%.6f dirty-enum-sec=%.6f dirty-update-sec=%.6f audit-repair-sec=%.6f apply-sec=%.6f free-sec=%.6f oracle-sec=%.6f total-sec=%.6f\n",
        s->Mode,status,s->Reason,s->Call,s->Round,s->Wave,proved,vertices,edges,
        selected,weight,firstGain,(unsigned long long)s->Epochs,
        (unsigned long long)s->Removed,(unsigned long long)s->NeighborCalls,
        (unsigned long long)s->DirtyVertices,(unsigned long long)s->MffcRequests,
        (unsigned long long)s->SupportRequests,(unsigned long long)s->BaselineEntries,
        (unsigned long long)s->ActualEntries,(unsigned long long)s->SkippedEntries,
        (unsigned long long)s->SkippedLists,(unsigned long long)s->PartialLists,
        (unsigned long long)s->NeighborOutputs,(unsigned long long)s->StateBytes,
        (unsigned long long)s->OracleBytes,(unsigned long long)s->OracleEpochs,
        (unsigned long long)s->OracleDirtyChecks,(unsigned long long)s->PopHash,
        (unsigned long long)s->SelectedHash,Cec_TranTimeSec(s->PrepareTicks),
        Cec_TranTimeSec(s->SetupTicks),Cec_TranTimeSec(s->GwminTicks),
        Cec_TranTimeSec(s->InitialTicks),Cec_TranTimeSec(s->RemoveTicks),
        Cec_TranTimeSec(s->DirtyTicks),Cec_TranTimeSec(s->UpdateTicks),
        Cec_TranTimeSec(s->RepairTicks),Cec_TranTimeSec(s->ApplyTicks),
        Cec_TranTimeSec(s->FreeTicks),Cec_TranTimeSec(s->OracleTicks),
        Cec_TranTimeSec(Abc_Clock()-s->Started));
}
