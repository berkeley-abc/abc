// Frozen-H local CNF. Inspired by Ssw_ManLoadSolver/Ssw_CnfNodeAddToSolver,
// but all literals refer to the immutable conditioned SRM, not SSW classes.
//
// F = G(all SRM gates) & R(all residuals) & Q. For loaded nodes U and
// residuals I, L = G(U) & R(I) & Q in a fresh compact variable domain.
// U contains both fanin cones of every loaded gate and residual endpoint.
// Restricting any F model to U, then renaming its variables, satisfies L.
// Thus local UNSAT is a sound conditional answer. Structural selection is
// only a heuristic. Backend 2 confirms SAT in a full solver; backend 4 first
// completes the circuit assignment and checks every residual of F directly.
// Query definitions cached in this solver are unconstrained definitions;
// no query result is added as an unconditional relation.

typedef struct Cec_TranStrictLocal_t_ {
    int * Vars, * FanHead, * FanNext, * FanTarget;
    int * ResidualHead, * ResidualNext, * Seen, * ResidualSeen;
    unsigned char * ResidualCone, * Loaded;
    unsigned char * ForwardSeen, * StateCi, * Values; // Backend 4 only.
    Vec_Int_t * Stack, * Nodes, * Support, * Selected, * Touched, * LoadedIds;
    int Stamp, Aborted, Disabled, Group, GroupQueries, GroupNontrivial, GroupGates;
    int VarsMax, GatesMax, ClausesMax, ResidualMax;
    int EntryVars, EntryGates, EntryClauses, EntryResidual;
    int LastFrame, LastEdge, LastQuery, LastRelated, LastVisits, LastCapped;
    int LastStructural; // -1: stopped before mapping; 0: a!=b; 1: a==b.
    long long Queries, Recycles, EncodedGates, SelectedResiduals, SelectionVisits, SelectionCaps;
    long long StructuralQueries, NontrivialQueries, UnclassifiedQueries, NontrivialSolves;
    long long RecycleReasons[4], SelectionSkips; // Direct test, vars, cache, both.
    long long BackwardVisits, LiftAttempts, LiftFailures;
    long long VarsSum, GatesSum, ClausesSum, ResidualSum;
    long long Conflicts, Decisions, Propagations, GroupConflicts, GroupDecisions, GroupPropagations;
    long long VarBins[6], GateBins[6], ResidualBins[6], SaturatedAt[4];
    abctime IndexTicks, LoadTicks, SelectTicks, RecycleTicks, QueryLoadTicks;
} Cec_TranStrictLocal_t;

// SSW labels external PIs once per solver generation. A conditioned CI with
// an initial-state preimage remains a state seed even if H aliases it to a PI.
static void Cec_TranStrictDynamicLabels(Cec_TranFrozenCnfSolver_t * s)
{
    Cec_TranStrictLocal_t * p=(Cec_TranStrictLocal_t *)s->ResearchData;
    Gia_Obj_t * o;int i,id;
    memset(p->Seen,0,s->Srm.Objects*sizeof(int));
    memset(p->ForwardSeen,0,s->Srm.Objects);
    memset(p->ResidualSeen,0,(size_t)s->Srm.EqualitiesKept*sizeof(int));
    p->Seen[0]=p->ForwardSeen[0]=1;
    Gia_ManForEachCi(s->Srm.Graph,o,i)
    {id=Gia_ObjId(s->Srm.Graph,o);p->Seen[id]=p->ForwardSeen[id]=!p->StateCi[id];}
}

static int Cec_TranStrictLocalBin(int count,int total)
{
    if(!count)return 0;
    if(count>=total)return 5;
    if(10LL*count<=total)return 1;
    if(4LL*count<=total)return 2;
    if(2LL*count<=total)return 3;
    return 4;
}

static int Cec_TranStrictLocalStamp(Cec_TranFrozenCnfSolver_t * s)
{
    Cec_TranStrictLocal_t * p=(Cec_TranStrictLocal_t *)s->ResearchData;
    if(p->Stamp==INT_MAX)
    {
        memset(p->Seen,0,s->Srm.Objects*sizeof(int));
        memset(p->ResidualSeen,0,(size_t)s->Srm.EqualitiesKept*sizeof(int));
        p->Stamp=0;
    }
    return ++p->Stamp;
}

static int Cec_TranStrictLocalStopped(Cec_TranStrictLocal_t * p)
{
    if(p->Aborted || Cec_TranSeqBudgetStop()){p->Aborted=1;return 1;}
    return 0;
}

static void Cec_TranStrictLocalWork(Cec_TranFrozenCnfSolver_t * s)
{
    Cec_TranStrictLocal_t * p=(Cec_TranStrictLocal_t *)s->ResearchData;
    sat_solver * sat=s->View.u.pSat;
    p->Conflicts+=sat->stats.conflicts-p->GroupConflicts;
    p->Decisions+=sat->stats.decisions-p->GroupDecisions;
    p->Propagations+=sat->stats.propagations-p->GroupPropagations;
    p->GroupConflicts=sat->stats.conflicts;
    p->GroupDecisions=sat->stats.decisions;
    p->GroupPropagations=sat->stats.propagations;
}

static void Cec_TranStrictLocalTable(Cec_TranFrozenCnfSolver_t * s)
{
    // The hash contains clauses in the LOCAL domain. Map.Map remains the
    // original-object -> SRM-literal map used by the full confirmer/replay.
    ABC_FREE(s->Map.Table);s->Map.Capacity=256;s->Map.UniqueClauses=0;
    s->Map.Table=ABC_CALLOC(Cec_TranFrozenCnfClause_t,s->Map.Capacity);
}

static void Cec_TranStrictLocalRecycle(Cec_TranFrozenCnfSolver_t * s,int reason)
{
    Cec_TranStrictLocal_t * p=(Cec_TranStrictLocal_t *)s->ResearchData;
    int i,id,c=1;abctime clk=Abc_Clock();
    CEC_BASIS_REQUIRE(reason>=0 && reason<4);++p->RecycleReasons[reason];
    Cec_TranStrictLocalWork(s);
    if(s->Profile)
        Abc_Print(1,"stran-strict-local-group: schema=2 call=%llu round=%d group=%d queries=%d nontrivial-solves=%d recycle-reason=%d vars=%d gates=%d clauses=%d residuals=%d full-objects=%d full-gates=%d full-residuals=%lld\n",
            s->Call,s->Round,p->Group,p->GroupQueries,p->GroupNontrivial,reason,sat_solver_nvars(s->View.u.pSat),p->GroupGates,
            sat_solver_nclauses(s->View.u.pSat),s->ResidualActive,s->Srm.Objects,s->Srm.Gates,s->Srm.EqualitiesKept);
    sat_solver_delete(s->View.u.pSat);s->View.u.pSat=sat_solver_new();
    sat_solver_setnvars(s->View.u.pSat,1);Cec_TranSeqBudgetSetSolver(s->View.u.pSat);
    Vec_IntForEachEntry(p->Touched,id,i)p->Vars[id]=-1;
    Vec_IntForEachEntry(p->LoadedIds,id,i)p->Loaded[id]=0;
    Vec_IntClear(p->Touched);Vec_IntClear(p->LoadedIds);p->Vars[0]=0;
    Vec_IntClear(s->View.QueryFrames);Vec_IntClear(s->View.QueryEdges);Vec_IntClear(s->View.QueryLits);
    memset(s->View.Slots,0,s->View.nSlots*sizeof(int));
    s->View.queryVars=0;s->ResidualActive=0;s->Inconsistent=s->Map.Contradictions!=0;
    Cec_TranStrictLocalTable(s);Cec_TranFrozenCnfEmit(s,&c,1,0,1);
    if(s->ResearchMode==4)Cec_TranStrictDynamicLabels(s);
    p->GroupQueries=p->GroupNontrivial=p->GroupGates=0;
    p->GroupConflicts=p->GroupDecisions=p->GroupPropagations=0;
    ++p->Group;++p->Recycles;p->RecycleTicks+=Abc_Clock()-clk;
}

static void Cec_TranStrictLocalStart(Cec_TranFrozenCnfSolver_t * s)
{
    Cec_TranStrictLocal_t * p=ABC_CALLOC(Cec_TranStrictLocal_t,1);
    Gia_Man_t * g=s->Srm.Graph;Gia_Obj_t * o;
    int i,j,id,a,b,c=1,link=0,visits=0,n=s->Srm.Objects,r=(int)s->Srm.EqualitiesKept;
    abctime clk=Abc_Clock();
    CEC_BASIS_REQUIRE(s->Mode==3 && (s->ResearchMode==2 || s->ResearchMode==4) && !s->ResearchData && !s->LazyMode);
    CEC_BASIS_REQUIRE(sat_solver_nvars(s->View.u.pSat)==1 && s->Srm.EqualitiesKept<=INT_MAX/2);
    s->ResearchData=p;s->Guard=1;p->Group=1;p->Vars=ABC_FALLOC(int,n);p->Vars[0]=0;
    p->FanHead=ABC_FALLOC(int,n);p->FanNext=ABC_ALLOC(int,2*s->Srm.Gates);
    p->FanTarget=ABC_ALLOC(int,2*s->Srm.Gates);
    p->ResidualHead=ABC_FALLOC(int,n);p->ResidualNext=ABC_ALLOC(int,2*r);
    p->Seen=ABC_CALLOC(int,n);p->ResidualSeen=ABC_CALLOC(int,r);
    p->ResidualCone=ABC_CALLOC(unsigned char,n);p->Loaded=ABC_CALLOC(unsigned char,r);
    p->Stack=Vec_IntAlloc(128);p->Nodes=Vec_IntAlloc(128);p->Support=Vec_IntAlloc(128);
    p->Selected=Vec_IntAlloc(64);p->Touched=Vec_IntAlloc(128);p->LoadedIds=Vec_IntAlloc(64);
    if(s->ResearchMode==4)
    {
        p->ForwardSeen=ABC_CALLOC(unsigned char,n);p->StateCi=ABC_CALLOC(unsigned char,n);
        p->Values=ABC_CALLOC(unsigned char,n);
        for(i=0;i<s->Template->nInitialRos;++i)
        {
            o=Gia_ManCi(s->Template->u.p,s->Template->nSourcePis+i);
            id=Abc_Lit2Var(s->Map.Map[Gia_ObjId(s->Template->u.p,o)]);
            if(id && Gia_ObjIsCi(Gia_ManObj(g,id)))p->StateCi[id]=1;
        }
        Cec_TranStrictDynamicLabels(s);
    }
    Cec_TranStrictLocalTable(s);Cec_TranFrozenCnfEmit(s,&c,1,0,1);
    // Incidence is per SRM object. The CIs are already distinct per unrolled
    // frame except where Frozen H/J deliberately identifies their values.
    for(i=0;i<2*r;++i)
    {
        id=Abc_Lit2Var(Vec_IntEntry(s->Srm.Equalities,i));
        p->ResidualNext[i]=p->ResidualHead[id];p->ResidualHead[id]=i;
        if(id && !p->ResidualCone[id]){p->ResidualCone[id]=1;Vec_IntPush(p->Stack,id);}
        if(!(i&4095) && Cec_TranStrictLocalStopped(p))break;
    }
    while(!p->Aborted && Vec_IntSize(p->Stack))
    {
        if(!(visits++&4095) && Cec_TranStrictLocalStopped(p))break;
        id=Vec_IntPop(p->Stack);o=Gia_ManObj(g,id);
        if(Gia_ObjIsCi(o))continue;
        CEC_BASIS_REQUIRE(Gia_ObjIsAnd(o) && !Gia_ObjIsBuf(o));
        a=Gia_ObjFaninId0p(g,o);b=Gia_ObjFaninId1p(g,o);
        if(a && !p->ResidualCone[a]){p->ResidualCone[a]=1;Vec_IntPush(p->Stack,a);}
        if(b && !p->ResidualCone[b]){p->ResidualCone[b]=1;Vec_IntPush(p->Stack,b);}
    }
    Gia_ManForEachObj1(g,o,i)
    {
        if(p->Aborted || (!(visits++&4095) && Cec_TranStrictLocalStopped(p)))break;
        if(!p->ResidualCone[i] || !Gia_ObjIsAnd(o))continue;
        a=Gia_ObjFaninId0p(g,o);b=Gia_ObjFaninId1p(g,o);
        p->FanTarget[link]=i;p->FanNext[link]=p->FanHead[a];p->FanHead[a]=link++;
        p->FanTarget[link]=i;p->FanNext[link]=p->FanHead[b];p->FanHead[b]=link++;
    }
    // H/J themselves became identities in the SRM map. Their nontrivial
    // gate obligations are precisely Srm.Equalities. Do not add H at k.
    if(!s->Map.Contradictions)
    {
        for(i=0;i<s->Depth && !p->Aborted;++i)Vec_IntForEachEntry(s->FrozenEdges,id,j)
        {
            CEC_BASIS_REQUIRE(Cec_TranFrozenCnfEndpoint(s,i,Vec_IntEntry(s->Pairs,2*id))==
                Cec_TranFrozenCnfEndpoint(s,i,Vec_IntEntry(s->Pairs,2*id+1)));
            if(!(j&4095) && Cec_TranStrictLocalStopped(p))break;
        }
        if(s->Known)for(i=0;i<=s->Depth && !p->Aborted;++i)Vec_IntForEachEntry(Cec_TranRelClosedCurrent->KnownIds,id,j)
        {
            CEC_BASIS_REQUIRE(Cec_TranFrozenCnfEndpoint(s,i,Vec_IntEntry(s->Pairs,2*id))==
                Cec_TranFrozenCnfEndpoint(s,i,Vec_IntEntry(s->Pairs,2*id+1)));
            if(!(j&4095) && Cec_TranStrictLocalStopped(p))break;
        }
    }
    Vec_IntClear(p->Stack);p->Disabled=p->Aborted;p->IndexTicks=Abc_Clock()-clk;
}

static int Cec_TranStrictLocalLit(Cec_TranStrictLocal_t * p,int lit)
{
    int var=p->Vars[Abc_Lit2Var(lit)];CEC_BASIS_REQUIRE(var>=0);
    return Abc_Var2Lit(var,Abc_LitIsCompl(lit));
}

// Iterative postorder avoids C recursion on deep recipes. Allocate exactly
// one SAT variable per loaded object; unvisited CIs/gates consume none.
static void Cec_TranStrictLocalLoad(Cec_TranFrozenCnfSolver_t * s,int root)
{
    Cec_TranStrictLocal_t * p=(Cec_TranStrictLocal_t *)s->ResearchData;
    Gia_Man_t * g=s->Srm.Graph;Gia_Obj_t * o;
    int id,a,b,z,x,y,c[3],visits=0;
    Vec_IntClear(p->Stack);Vec_IntPush(p->Stack,Abc_Lit2Var(root));
    while(Vec_IntSize(p->Stack))
    {
        if(!(visits++&4095) && Cec_TranStrictLocalStopped(p))break;
        id=Vec_IntEntryLast(p->Stack);
        if(p->Vars[id]>=0){Vec_IntPop(p->Stack);continue;}
        o=Gia_ManObj(g,id);
        if(!Gia_ObjIsCi(o))
        {
            CEC_BASIS_REQUIRE(Gia_ObjIsAnd(o) && !Gia_ObjIsBuf(o));
            a=Gia_ObjFaninId0p(g,o);b=Gia_ObjFaninId1p(g,o);
            if(p->Vars[a]<0){Vec_IntPush(p->Stack,a);continue;}
            if(p->Vars[b]<0){Vec_IntPush(p->Stack,b);continue;}
        }
        CEC_BASIS_REQUIRE(sat_solver_nvars(s->View.u.pSat)<1073741823);
        p->Vars[id]=sat_solver_nvars(s->View.u.pSat);
        sat_solver_setnvars(s->View.u.pSat,p->Vars[id]+1);Vec_IntPush(p->Touched,id);Vec_IntPop(p->Stack);
        if(Gia_ObjIsCi(o))continue;
        a=Cec_TranStrictLocalLit(p,Gia_ObjFaninLit0p(g,o));b=Cec_TranStrictLocalLit(p,Gia_ObjFaninLit1p(g,o));
        z=Abc_Var2Lit(p->Vars[id],0);
        if(Gia_ObjIsXor(o))for(x=0;x<2;++x)for(y=0;y<2;++y)
        {c[0]=a^x;c[1]=b^y;c[2]=z^(1^x^y);Cec_TranFrozenCnfEmit(s,c,3,0,0);}
        else
        {
            c[0]=z^1;c[1]=a;Cec_TranFrozenCnfEmit(s,c,2,0,0);
            c[0]=z^1;c[1]=b;Cec_TranFrozenCnfEmit(s,c,2,0,0);
            c[0]=z;c[1]=a^1;c[2]=b^1;Cec_TranFrozenCnfEmit(s,c,3,0,0);
        }
        ++p->GroupGates;++p->EncodedGates;
    }
    Vec_IntClear(p->Stack);
}

static void Cec_TranStrictLocalRelated(Cec_TranStrictLocal_t * p,int id,int stamp)
{
    int link,r;
    if(!id)return; // Constant incidence would associate every constant residual.
    for(link=p->ResidualHead[id];link>=0;link=p->ResidualNext[link])
    {
        r=link/2;
        if(p->Loaded[r] || p->ResidualSeen[r]==stamp)continue;
        if(Vec_IntSize(p->Selected)==64){p->LastCapped=1;return;}
        p->ResidualSeen[r]=stamp;Vec_IntPush(p->Selected,r);
    }
}

// One support/fanout pass, not a transitive constraint closure. Both the
// residual and visit bounds only weaken L; they never restrict F or its model.
static void Cec_TranStrictLocalSelect(Cec_TranFrozenCnfSolver_t * s,int a,int b)
{
    Cec_TranStrictLocal_t * p=(Cec_TranStrictLocal_t *)s->ResearchData;
    Gia_Man_t * g=s->Srm.Graph;Gia_Obj_t * o;
    int stamp=Cec_TranStrictLocalStamp(s),selectStamp=stamp,forwardStamp=Cec_TranStrictLocalStamp(s);
    int i,id,next,link,r,x,y,c[2];
    abctime clk=Abc_Clock();
    Vec_IntClear(p->Nodes);Vec_IntClear(p->Support);Vec_IntClear(p->Selected);
    a=Abc_Lit2Var(a);b=Abc_Lit2Var(b);p->Seen[a]=stamp;Vec_IntPush(p->Nodes,a);
    if(p->Seen[b]!=stamp){p->Seen[b]=stamp;Vec_IntPush(p->Nodes,b);}
    Vec_IntForEachEntry(p->Nodes,id,i)
    {
        if(!(i&4095) && Cec_TranStrictLocalStopped(p))break;
        if(!id)continue;
        Cec_TranStrictLocalRelated(p,id,stamp);o=Gia_ManObj(g,id);
        if(Gia_ObjIsCi(o)){if(p->ResidualCone[id])Vec_IntPush(p->Support,id);continue;}
        x=Gia_ObjFaninId0p(g,o);y=Gia_ObjFaninId1p(g,o);
        if(p->Seen[x]!=stamp){p->Seen[x]=stamp;Vec_IntPush(p->Nodes,x);}
        if(p->Seen[y]!=stamp){p->Seen[y]=stamp;Vec_IntPush(p->Nodes,y);}
    }
    stamp=forwardStamp;
    Vec_IntForEachEntry(p->Support,id,i)p->Seen[id]=stamp;
    Vec_IntForEachEntry(p->Support,id,i)
    {
        if(p->Aborted)break;
        if(i==8192 || Vec_IntSize(p->Selected)==64){p->LastCapped=1;break;}
        if(!(i&1023) && Cec_TranStrictLocalStopped(p))break;
        ++p->LastVisits;Cec_TranStrictLocalRelated(p,id,selectStamp);
        for(link=p->FanHead[id];link>=0;link=p->FanNext[link])
        {
            next=p->FanTarget[link];if(p->Seen[next]==stamp)continue;
            // Bound the queue as well as popped nodes on high-fanout inputs.
            if(Vec_IntSize(p->Support)>=8192){p->LastCapped=1;break;}
            p->Seen[next]=stamp;Vec_IntPush(p->Support,next);
        }
    }
    p->LastRelated=Vec_IntSize(p->Selected);p->SelectTicks+=Abc_Clock()-clk;
    clk=Abc_Clock();
    Vec_IntForEachEntry(p->Selected,r,i)
    {
        if(Cec_TranStrictLocalStopped(p))break;
        x=Vec_IntEntry(s->Srm.Equalities,2*r);y=Vec_IntEntry(s->Srm.Equalities,2*r+1);
        Cec_TranStrictLocalLoad(s,x);Cec_TranStrictLocalLoad(s,y);if(p->Aborted)break;
        x=Cec_TranStrictLocalLit(p,x);y=Cec_TranStrictLocalLit(p,y);
        c[0]=x^1;c[1]=y;Cec_TranFrozenCnfEmit(s,c,2,4,0);
        c[0]=x;c[1]=y^1;Cec_TranFrozenCnfEmit(s,c,2,4,0);
        p->Loaded[r]=1;Vec_IntPush(p->LoadedIds,r);++s->ResidualActive;++p->SelectedResiduals;
    }
    p->LoadTicks+=Abc_Clock()-clk;p->SelectionVisits+=p->LastVisits;p->SelectionCaps+=p->LastCapped;
}

// Same two traversals as Ssw_ManLoadSolver: newly seen initial-state support,
// then its fanout to residual endpoints. Marks persist until solver recycling;
// visiting a residual does not recursively expand its other state supports.
static void Cec_TranStrictDynamicSelect(Cec_TranFrozenCnfSolver_t * s,int a,int b)
{
    Cec_TranStrictLocal_t * p=(Cec_TranStrictLocal_t *)s->ResearchData;
    Gia_Man_t * g=s->Srm.Graph;Gia_Obj_t * o;
    int i,id,link,next,r,x,y,c[2];abctime clk=Abc_Clock();
    Vec_IntClear(p->Nodes);Vec_IntClear(p->Support);Vec_IntClear(p->Selected);
    a=Abc_Lit2Var(a);b=Abc_Lit2Var(b);
    if(!p->Seen[a]){p->Seen[a]=1;Vec_IntPush(p->Nodes,a);}
    if(!p->Seen[b]){p->Seen[b]=1;Vec_IntPush(p->Nodes,b);}
    Vec_IntForEachEntry(p->Nodes,id,i)
    {
        if(!(i&4095) && Cec_TranStrictLocalStopped(p))break;
        ++p->BackwardVisits;o=Gia_ManObj(g,id);
        if(Gia_ObjIsCi(o))
        {
            if(!p->ForwardSeen[id]){p->ForwardSeen[id]=1;Vec_IntPush(p->Support,id);}
            continue;
        }
        CEC_BASIS_REQUIRE(Gia_ObjIsAnd(o));
        x=Gia_ObjFaninId0p(g,o);y=Gia_ObjFaninId1p(g,o);
        if(!p->Seen[x]){p->Seen[x]=1;Vec_IntPush(p->Nodes,x);}
        if(!p->Seen[y]){p->Seen[y]=1;Vec_IntPush(p->Nodes,y);}
    }
    Vec_IntForEachEntry(p->Support,id,i)
    {
        if(p->Aborted || (!(i&4095) && Cec_TranStrictLocalStopped(p)))break;
        ++p->LastVisits;
        for(link=p->ResidualHead[id];link>=0;link=p->ResidualNext[link])
        {
            r=link/2;
            if(!p->Loaded[r] && !p->ResidualSeen[r])
            {p->ResidualSeen[r]=1;Vec_IntPush(p->Selected,r);}
        }
        for(link=p->FanHead[id];link>=0;link=p->FanNext[link])
        {
            next=p->FanTarget[link];if(p->ForwardSeen[next])continue;
            p->ForwardSeen[next]=1;Vec_IntPush(p->Support,next);
        }
    }
    p->LastRelated=Vec_IntSize(p->Selected);p->SelectTicks+=Abc_Clock()-clk;clk=Abc_Clock();
    Vec_IntForEachEntry(p->Selected,r,i)
    {
        if(Cec_TranStrictLocalStopped(p))break;
        x=Vec_IntEntry(s->Srm.Equalities,2*r);y=Vec_IntEntry(s->Srm.Equalities,2*r+1);
        Cec_TranStrictLocalLoad(s,x);Cec_TranStrictLocalLoad(s,y);if(p->Aborted)break;
        x=Cec_TranStrictLocalLit(p,x);y=Cec_TranStrictLocalLit(p,y);
        c[0]=x^1;c[1]=y;Cec_TranFrozenCnfEmit(s,c,2,4,0);
        c[0]=x;c[1]=y^1;Cec_TranFrozenCnfEmit(s,c,2,4,0);
        p->Loaded[r]=1;Vec_IntPush(p->LoadedIds,r);++s->ResidualActive;++p->SelectedResiduals;
    }
    p->LoadTicks+=Abc_Clock()-clk;p->SelectionVisits+=p->LastVisits;
}

// A local SAT assignment need not satisfy omitted residuals. Completing free
// CIs by zero and evaluating G gives a full circuit assignment, but it is only
// exposed after ALL R and the target mismatch have been checked. Otherwise the
// unchanged full confirmer receives the remaining logical conflict budget.
static int Cec_TranStrictDynamicLift(Cec_TranFrozenCnfSolver_t * s,int edge)
{
    Cec_TranStrictLocal_t * p=(Cec_TranStrictLocal_t *)s->ResearchData;
    Gia_Man_t * g=s->Srm.Graph;Gia_Obj_t * o;
    int i,a,b,value,ok=0;abctime clk=Abc_Clock();
    ++p->LiftAttempts;p->Values[0]=0;
    Gia_ManForEachObj1(g,o,i)
    {
        if(!(i&4095) && Cec_TranStrictLocalStopped(p))goto finish;
        if(Gia_ObjIsCi(o))
        {
            value=p->Vars[i]<0?0:Cec_TranLazyModelLit(s->View.u.pSat,Abc_Var2Lit(p->Vars[i],0));
            p->Values[i]=value<0?0:value;
        }
        else
        {
            a=p->Values[Gia_ObjFaninId0p(g,o)]^Gia_ObjFaninC0(o);
            b=p->Values[Gia_ObjFaninId1p(g,o)]^Gia_ObjFaninC1(o);
            p->Values[i]=Gia_ObjIsXor(o)?a^b:a&b;
        }
        if(p->Vars[i]>=0)
        {
            value=Cec_TranLazyModelLit(s->View.u.pSat,Abc_Var2Lit(p->Vars[i],0));
            CEC_BASIS_REQUIRE(value<0 || value==p->Values[i]);
        }
    }
    for(i=0;i<Vec_IntSize(s->Srm.Equalities);i+=2)
    {
        if(!(i&4095) && Cec_TranStrictLocalStopped(p))goto finish;
        a=Vec_IntEntry(s->Srm.Equalities,i);b=Vec_IntEntry(s->Srm.Equalities,i+1);++s->ResidualChecks;
        if((p->Values[Abc_Lit2Var(a)]^Abc_LitIsCompl(a))!=(p->Values[Abc_Lit2Var(b)]^Abc_LitIsCompl(b)))goto finish;
    }
    a=Cec_TranFrozenCnfEndpoint(s,s->Depth,Vec_IntEntry(s->Pairs,2*edge));
    b=Cec_TranFrozenCnfEndpoint(s,s->Depth,Vec_IntEntry(s->Pairs,2*edge+1));
    CEC_BASIS_REQUIRE((p->Values[Abc_Lit2Var(a)]^Abc_LitIsCompl(a))!=(p->Values[Abc_Lit2Var(b)]^Abc_LitIsCompl(b)));
    s->ModelValues=p->Values;s->ModelOwner=s;++s->LiftedSat;ok=1;
finish:
    p->LiftFailures+=!ok;s->ResidualTicks+=Abc_Clock()-clk;return ok;
}

static int Cec_TranStrictLocalQuery(Cec_TranFrozenCnfSolver_t * s,int frame,int edge)
{
    Cec_TranStrictLocal_t * p=(Cec_TranStrictLocal_t *)s->ResearchData;
    Cec_TranRelLazy_t * v=&s->View;
    int a,b,q=0,x,y,c[3],slot,reason;abctime clk=Abc_Clock(),load;
    CEC_BASIS_REQUIRE(frame==s->Depth && edge>=0 && edge<s->View.u.nRelations);
    p->Aborted=p->Disabled;p->LastFrame=frame;p->LastEdge=edge;
    p->LastRelated=p->LastVisits=p->LastCapped=0;p->LastStructural=-1;
    p->EntryVars=sat_solver_nvars(v->u.pSat);p->EntryGates=p->GroupGates;
    p->EntryClauses=sat_solver_nclauses(v->u.pSat);p->EntryResidual=s->ResidualActive;
    if(Cec_TranStrictLocalStopped(p))goto finish;
    a=Cec_TranFrozenCnfEndpoint(s,frame,Vec_IntEntry(s->Pairs,2*edge));
    b=Cec_TranFrozenCnfEndpoint(s,frame,Vec_IntEntry(s->Pairs,2*edge+1));
    p->LastStructural=a==b;
    // An identity adds no local state. Do not let its cache record or call
    // count evict useful cones; its ordinary q=0 solve still happens below.
    if(p->LastStructural)goto finish;
    // These thresholds control accumulation, never one obligation's size.
    reason=(sat_solver_nvars(v->u.pSat)>5000 && p->GroupNontrivial>=250) |
        ((s->ResearchMode==2 && Vec_IntSize(v->QueryLits)>=1024)<<1);
    if(reason)
    {
        Cec_TranStrictLocalRecycle(s,reason);
        p->EntryVars=sat_solver_nvars(v->u.pSat);p->EntryGates=p->GroupGates;
        p->EntryClauses=sat_solver_nclauses(v->u.pSat);p->EntryResidual=s->ResidualActive;
    }
    ++v->cacheLookups;
    slot=Cec_TranLazySlot(v,frame,edge);
    if(v->Slots[slot]){++v->cacheHits;q=Vec_IntEntry(v->QueryLits,v->Slots[slot]-1);goto finish;}
    load=Abc_Clock();Cec_TranStrictLocalLoad(s,a);Cec_TranStrictLocalLoad(s,b);p->LoadTicks+=Abc_Clock()-load;
    if(p->Aborted)goto finish;
    if(s->ResidualActive<s->Srm.EqualitiesKept)
    {
        if(s->ResearchMode==4)Cec_TranStrictDynamicSelect(s,a,b);
        else Cec_TranStrictLocalSelect(s,a,b);
    }
    else ++p->SelectionSkips; // Includes a graph with no residuals.
    if(p->Aborted)goto finish;
    a=Cec_TranStrictLocalLit(p,a);b=Cec_TranStrictLocalLit(p,b);
    if(a==(b^1))q=1;
    else
    {
        CEC_BASIS_REQUIRE(sat_solver_nvars(v->u.pSat)<1073741823);
        q=Abc_Var2Lit(sat_solver_nvars(v->u.pSat),0);
        sat_solver_setnvars(v->u.pSat,sat_solver_nvars(v->u.pSat)+1);++v->queryVars;
        for(x=0;x<2;++x)for(y=0;y<2;++y)
        {c[0]=a^x;c[1]=b^y;c[2]=q^(1^x^y);Cec_TranFrozenCnfEmit(s,c,3,3,0);}
    }
    if(2*(Vec_IntSize(v->QueryFrames)+1)>v->nSlots){Cec_TranLazyGrow(v);slot=Cec_TranLazySlot(v,frame,edge);}
    Vec_IntPush(v->QueryFrames,frame);Vec_IntPush(v->QueryEdges,edge);Vec_IntPush(v->QueryLits,q);
    v->Slots[slot]=Vec_IntSize(v->QueryFrames);
finish:
    p->LastQuery=q;p->QueryLoadTicks=Abc_Clock()-clk;
    return q;
}

static int Cec_TranStrictLocalSolve(Cec_TranFrozenCnfSolver_t * s,int edge,int query,int limit)
{
    Cec_TranStrictLocal_t * p=(Cec_TranStrictLocal_t *)s->ResearchData;
    Cec_TranFrozenCnfSolver_t * full;
    long long used=0,before=s->View.u.pSat->stats.conflicts,callsBefore;
    int status,fastStatus=l_Undef,fullStatus=l_Undef,fullCalled=0,i,vars,clauses;
    int fastLimit=s->ResearchMode==4?limit:limit?Abc_MaxInt(1,limit/4):0;
    CEC_BASIS_REQUIRE(edge==p->LastEdge && query==p->LastQuery && limit>=0);
    s->ModelOwner=NULL;s->ModelValues=NULL;++p->Queries;++p->GroupQueries;
    if(p->LastStructural==1)++p->StructuralQueries;
    else if(p->LastStructural==0)++p->NontrivialQueries;
    else ++p->UnclassifiedQueries;
    if(p->Aborted || Cec_TranSeqBudgetStop()){++s->BudgetStops;status=l_Undef;}
    else
    {
        callsBefore=s->SolverCalls;
        status=fastStatus=Cec_TranFrozenLazyPhase(s,s,query,fastLimit,&used,0);
        if(p->LastStructural==0 && s->SolverCalls>callsBefore)
        {++p->GroupNontrivial;++p->NontrivialSolves;}
        if(s->ResearchMode==4 && status==l_True)Cec_TranStrictDynamicLift(s,edge);
        if(status!=l_False && !s->ModelOwner)
        {
            if((limit && used>=limit) || Cec_TranSeqBudgetStop()){++s->BudgetStops;status=l_Undef;}
            else
            {
                ++s->Fallbacks;fullCalled=1;full=Cec_TranFrozenLazyFull(s);
                query=Cec_TranFrozenCnfQuery(full,s->Depth,edge);
                status=fullStatus=Cec_TranFrozenLazyPhase(s,full,query,limit,&used,1);
                if(status==l_True)s->ModelOwner=full;
            }
        }
    }
    CEC_BASIS_REQUIRE(!limit || used<=limit);
    if(used>s->QueryConflictsMax)s->QueryConflictsMax=used;
    Cec_TranStrictLocalWork(s);vars=sat_solver_nvars(s->View.u.pSat);clauses=sat_solver_nclauses(s->View.u.pSat);
    p->VarsMax=Abc_MaxInt(p->VarsMax,vars);p->GatesMax=Abc_MaxInt(p->GatesMax,p->GroupGates);
    p->ClausesMax=Abc_MaxInt(p->ClausesMax,clauses);p->ResidualMax=Abc_MaxInt(p->ResidualMax,s->ResidualActive);
    p->VarsSum+=vars;p->GatesSum+=p->GroupGates;p->ClausesSum+=clauses;p->ResidualSum+=s->ResidualActive;
    ++p->VarBins[Cec_TranStrictLocalBin(Vec_IntSize(p->Touched),s->Srm.Objects-1)];
    ++p->GateBins[Cec_TranStrictLocalBin(p->GroupGates,s->Srm.Gates)];
    ++p->ResidualBins[Cec_TranStrictLocalBin(s->ResidualActive,(int)s->Srm.EqualitiesKept)];
    ++s->ActiveBins[Cec_TranStrictLocalBin(s->ResidualActive,(int)s->Srm.EqualitiesKept)];
    for(i=0;i<4;++i)
    {
        int percent[4]={25,50,90,100};
        if(!p->SaturatedAt[i] && 100LL*Vec_IntSize(p->Touched)>=(long long)percent[i]*(s->Srm.Objects-1))
            p->SaturatedAt[i]=p->Queries;
        if(!s->SaturatedAt[i] && s->Srm.EqualitiesKept && 100LL*s->ResidualActive>=(long long)percent[i]*s->Srm.EqualitiesKept)
            s->SaturatedAt[i]=p->Queries;
    }
    // Keep all query-weighted aggregates, but bound diagnostic log volume.
    if(s->Profile && (p->Queries<=8 || !(p->Queries&(p->Queries-1))))
        Abc_Print(1,"stran-strict-local-query: schema=2 call=%llu round=%d query=%lld edge=%d frame=%d group=%d group-position=%d group-nontrivial-solves=%d structural=%d vars=%d graph-vars=%d gates=%d clauses=%d unique-clauses=%lld residuals=%d added-vars=%d added-gates=%d added-clauses=%d added-residuals=%d full-objects=%d full-gates=%d full-gate-clauses=%lld full-residuals=%lld related=%d support-visits=%d selection-capped=%d local-status=%d full-called=%d full-status=%d status=%d conflicts=%lld local-conflicts=%lld query-build-sec=%.6f load-stopped=%d\n",
            s->Call,s->Round,p->Queries,edge,p->LastFrame,p->Group,p->GroupQueries,p->GroupNontrivial,p->LastStructural,vars,1+Vec_IntSize(p->Touched),p->GroupGates,clauses,s->Map.UniqueClauses,s->ResidualActive,
            vars-p->EntryVars,p->GroupGates-p->EntryGates,clauses-p->EntryClauses,s->ResidualActive-p->EntryResidual,
            s->Srm.Objects,s->Srm.Gates,1+3LL*s->Srm.Gates+s->Srm.Xors,s->Srm.EqualitiesKept,
            p->LastRelated,p->LastVisits,p->LastCapped,fastStatus,fullCalled,fullStatus,status,used,
            (long long)s->View.u.pSat->stats.conflicts-before,(double)p->QueryLoadTicks/CLOCKS_PER_SEC,p->Aborted);
    return status;
}

static void Cec_TranStrictLocalStop(Cec_TranFrozenCnfSolver_t * s)
{
    Cec_TranStrictLocal_t * p=(Cec_TranStrictLocal_t *)s->ResearchData;int i;
    if(!p)return;
    Cec_TranStrictLocalWork(s);
    CEC_BASIS_REQUIRE(p->Queries==p->StructuralQueries+p->NontrivialQueries+p->UnclassifiedQueries);
    if(s->Profile)
    {
        Abc_Print(1,"stran-strict-local: schema=2 call=%llu round=%d queries=%lld groups=%d recycles=%lld encoded-gates=%lld selected-residuals=%lld support-visits=%lld selection-caps=%lld vars-max=%d gates-max=%d clauses-max=%d residuals-max=%d vars-sum=%lld gates-sum=%lld clauses-sum=%lld residuals-sum=%lld conflicts=%lld decisions=%lld propagations=%lld index-sec=%.6f gate-residual-load-sec=%.6f selection-sec=%.6f recycle-sec=%.6f structural-queries=%lld nontrivial-queries=%lld unclassified-queries=%lld nontrivial-solves=%lld recycle-direct=%lld recycle-vars=%lld recycle-cache=%lld recycle-both=%lld selection-skips-full=%lld\n",
            s->Call,s->Round,p->Queries,p->Group,p->Recycles,p->EncodedGates,p->SelectedResiduals,p->SelectionVisits,p->SelectionCaps,
            p->VarsMax,p->GatesMax,p->ClausesMax,p->ResidualMax,p->VarsSum,p->GatesSum,p->ClausesSum,p->ResidualSum,
            p->Conflicts,p->Decisions,p->Propagations,(double)p->IndexTicks/CLOCKS_PER_SEC,(double)p->LoadTicks/CLOCKS_PER_SEC,
            (double)p->SelectTicks/CLOCKS_PER_SEC,(double)p->RecycleTicks/CLOCKS_PER_SEC,
            p->StructuralQueries,p->NontrivialQueries,p->UnclassifiedQueries,p->NontrivialSolves,
            p->RecycleReasons[0],p->RecycleReasons[1],p->RecycleReasons[2],p->RecycleReasons[3],p->SelectionSkips);
        Abc_Print(1,"stran-strict-local-distribution: schema=1 call=%llu round=%d",s->Call,s->Round);
        for(i=0;i<6;++i)Abc_Print(1," vars-bin%d=%lld gates-bin%d=%lld residual-bin%d=%lld",i,p->VarBins[i],i,p->GateBins[i],i,p->ResidualBins[i]);
        for(i=0;i<4;++i)Abc_Print(1," graph-saturation%d-query=%lld",i,p->SaturatedAt[i]);
        Abc_Print(1,"\n");
        if(s->ResearchMode==4)
            Abc_Print(1,"stran-strict-dynamic: schema=1 call=%llu round=%d backward-visits=%lld forward-visits=%lld lift-attempts=%lld lift-failures=%lld lifted-sat=%lld full-fallbacks=%lld\n",
                s->Call,s->Round,p->BackwardVisits,p->SelectionVisits,p->LiftAttempts,p->LiftFailures,s->LiftedSat,s->Fallbacks);
    }
    ABC_FREE(p->Vars);ABC_FREE(p->FanHead);ABC_FREE(p->FanNext);ABC_FREE(p->FanTarget);
    ABC_FREE(p->ResidualHead);ABC_FREE(p->ResidualNext);ABC_FREE(p->Seen);ABC_FREE(p->ResidualSeen);
    ABC_FREE(p->ResidualCone);ABC_FREE(p->Loaded);
    ABC_FREE(p->ForwardSeen);ABC_FREE(p->StateCi);ABC_FREE(p->Values);s->ModelValues=NULL;
    Vec_IntFree(p->Stack);Vec_IntFree(p->Nodes);Vec_IntFree(p->Support);Vec_IntFree(p->Selected);
    Vec_IntFree(p->Touched);Vec_IntFree(p->LoadedIds);ABC_FREE(p);s->ResearchData=NULL;
}
