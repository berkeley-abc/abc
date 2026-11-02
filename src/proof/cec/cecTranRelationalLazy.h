// Endpoint encoding adapted only from src/proof/cec/cecTranRelLazyEndpoint.h
// in historical candidate_complete_source_prebuild.tar.gz SHA256
// 93d32b3a06bea0201c6feb5480b798a68a690ddd22b0baa18206c77f6991c497.
// No archived diag/export/CLI/construction hooks are imported.
// Lazy endpoint encoding for the signed-basis backend only.  The full
// transition/recipe graph and every original relation remain present.
typedef struct Cec_TranRelLazy_t_ {
    Cec_TranRelUnroll_t u;
    Vec_Int_t * Maps, * QueryFrames, * QueryEdges, * QueryLits;
    int * Slots;
    int nSlots, nOriginalObjects, nTransitionVars, nInitialStored;
    int nSourcePis, nInitialRos; // Initial CIs are frame-0 PIs followed by free ROs.
    int OdcProofScope; // Select the ODC encoder independently of Strict.
    int queryVars, guardVars;
    long long transitionAttempted, queryAttempted, hypothesisAttempted, disableAttempted;
    long long closedAttempted;
    long long cacheLookups, cacheHits;
    char const * Context;
    FILE * Trace;
} Cec_TranRelLazy_t;

static int Cec_TranLazyModelLit(sat_solver * sat,int lit)
{
    int var=Abc_Lit2Var(lit);
    CEC_BASIS_REQUIRE(var>=0 && var<sat_solver_nvars(sat));
    if(sat->model[var]!=l_True && sat->model[var]!=l_False) return -1;
    return (sat->model[var]==l_True)^Abc_LitIsCompl(lit);
}

static void Cec_TranLazyClause(Cec_TranRelLazy_t * s,int * lits,int width,int kind)
{
    int before=sat_solver_nclauses(s->u.pSat);
    if(kind==0)++s->transitionAttempted;
    else if(kind==1)++s->queryAttempted;
    else if(kind==2)++s->hypothesisAttempted;
    else if(kind==3)++s->disableAttempted;
    else {CEC_BASIS_REQUIRE(kind==4);++s->closedAttempted;}
    Cec_TranRelClause(s->u.pSat,lits,width);
    if(s->Trace)
    {
        int i;
        fprintf(s->Trace,"clause context=%s kind=%d width=%d before=%d after=%d lits=",s->Context,kind,width,before,sat_solver_nclauses(s->u.pSat));
        for(i=0;i<width;++i)fprintf(s->Trace,"%d,",lits[i]);
        fprintf(s->Trace,"\n");
    }
}

static Cec_TranRelLazy_t Cec_TranLazyUnroll(Gia_Man_t * p,Vec_Int_t * pairs,int nFrames,int fReset,FILE * trace)
{
    Cec_TranRelLazy_t s;
    Gia_Obj_t * o;
    int * old=ABC_CALLOC(int,Gia_ManObjNum(p)),* cur=ABC_CALLOC(int,Gia_ManObjNum(p));
    int f,i,a,b,z,x,y,clause[3];
    CEC_BASIS_REQUIRE(nFrames>0 && !(Vec_IntSize(pairs)&1));
    CEC_BASIS_REQUIRE((long long)nFrames*Gia_ManObjNum(p)<=2147483647);
    memset(&s,0,sizeof(s));s.Context=fReset?"base":"ind";s.Trace=trace;
    s.nSourcePis=Gia_ManPiNum(p);s.nInitialRos=fReset?0:Gia_ManRegNum(p);
    s.nOriginalObjects=Gia_ManObjNum(p);s.u.nRelations=Vec_IntSize(pairs)/2;s.u.nFrames=nFrames;
    s.Maps=Vec_IntAlloc(nFrames*Gia_ManObjNum(p));
    s.QueryFrames=Vec_IntAlloc(128);s.QueryEdges=Vec_IntAlloc(128);s.QueryLits=Vec_IntAlloc(128);
    s.nSlots=256;s.Slots=ABC_CALLOC(int,s.nSlots);
    s.u.vQueries=Vec_IntAlloc(0); // no dense query graph or query-literal array
    s.u.p=Gia_ManStart(Gia_ManObjNum(p));Gia_ManHashStart(s.u.p);
    for(f=0;f<nFrames;++f)
    {
        int * tmp;cur[0]=0;
        Gia_ManForEachPi(p,o,i)cur[Gia_ObjId(p,o)]=Gia_ManAppendCi(s.u.p);
        Gia_ManForEachRo(p,o,i)cur[Gia_ObjId(p,o)]=f?old[Gia_ObjId(p,Gia_ManRi(p,i))]:fReset?0:Gia_ManAppendCi(s.u.p);
        Gia_ManForEachObj1(p,o,i)
        {
            if(Gia_ObjIsCi(o))continue;
            a=Abc_LitNotCond(cur[Gia_ObjFaninId0p(p,o)],Gia_ObjFaninC0(o));
            if(Gia_ObjIsCo(o)||Gia_ObjIsBuf(o))cur[i]=a;
            else {b=Abc_LitNotCond(cur[Gia_ObjFaninId1p(p,o)],Gia_ObjFaninC1(o));cur[i]=Cec_TranHashGate(s.u.p,o,a,b);}
        }
        for(i=0;i<Gia_ManObjNum(p);++i)Vec_IntPush(s.Maps,cur[i]);
        tmp=old;old=cur;cur=tmp;
    }
    ABC_FREE(old);ABC_FREE(cur);Gia_ManHashStop(s.u.p);
    s.u.pSat=sat_solver_new();s.nTransitionVars=Gia_ManObjNum(s.u.p);
    sat_solver_setnvars(s.u.pSat,s.nTransitionVars);
    clause[0]=1;Cec_TranLazyClause(&s,clause,1,0);
    Gia_ManForEachAnd(s.u.p,o,i)
    {
        a=Gia_ObjFaninLit0p(s.u.p,o);b=Gia_ObjFaninLit1p(s.u.p,o);z=Abc_Var2Lit(i,0);
        if(Gia_ObjIsXor(o))
            for(x=0;x<2;++x)for(y=0;y<2;++y)
            {clause[0]=a^x;clause[1]=b^y;clause[2]=z^(1^x^y);Cec_TranLazyClause(&s,clause,3,0);}
        else
        {
            clause[0]=z^1;clause[1]=a;Cec_TranLazyClause(&s,clause,2,0);
            clause[0]=z^1;clause[1]=b;Cec_TranLazyClause(&s,clause,2,0);
            clause[0]=z;clause[1]=a^1;clause[2]=b^1;Cec_TranLazyClause(&s,clause,3,0);
        }
    }
    s.nInitialStored=sat_solver_nclauses(s.u.pSat);
    if(trace)fprintf(trace,"unroll context=%s frames=%d original-objects=%d transition-vars=%d attempted=%lld stored=%d\n",s.Context,nFrames,s.nOriginalObjects,s.nTransitionVars,s.transitionAttempted,s.nInitialStored);
    return s;
}

static int Cec_TranLazyEndpoint(Cec_TranRelLazy_t * s,int frame,int originalLit)
{
    int id=Abc_Lit2Var(originalLit);
    CEC_BASIS_REQUIRE(frame>=0 && frame<s->u.nFrames && id<s->nOriginalObjects);
    return Vec_IntEntry(s->Maps,frame*s->nOriginalObjects+id)^Abc_LitIsCompl(originalLit);
}

static unsigned Cec_TranLazyHash(int frame,int edge)
{
    unsigned long long x=((unsigned long long)(unsigned)frame<<32)|(unsigned)edge;
    x^=x>>33;x*=0xff51afd7ed558ccdULL;x^=x>>33;x*=0xc4ceb9fe1a85ec53ULL;x^=x>>33;
    return (unsigned)x;
}

static int Cec_TranLazySlot(Cec_TranRelLazy_t * s,int frame,int edge)
{
    unsigned slot=Cec_TranLazyHash(frame,edge)&(s->nSlots-1);
    while(s->Slots[slot])
    {
        int record=s->Slots[slot]-1;
        if(Vec_IntEntry(s->QueryFrames,record)==frame && Vec_IntEntry(s->QueryEdges,record)==edge)break;
        slot=(slot+1)&(s->nSlots-1);
    }
    return (int)slot;
}

static void Cec_TranLazyGrow(Cec_TranRelLazy_t * s)
{
    int i,slot;CEC_BASIS_REQUIRE(s->nSlots<=1073741823);
    ABC_FREE(s->Slots);s->nSlots*=2;s->Slots=ABC_CALLOC(int,s->nSlots);
    for(i=0;i<Vec_IntSize(s->QueryFrames);++i)
    {
        slot=Cec_TranLazySlot(s,Vec_IntEntry(s->QueryFrames,i),Vec_IntEntry(s->QueryEdges,i));
        CEC_BASIS_REQUIRE(!s->Slots[slot]);s->Slots[slot]=i+1;
    }
}

static int Cec_TranLazyQuery(Cec_TranRelLazy_t * s,Vec_Int_t * pairs,int frame,int edge)
{
    int slot,a,b,q,x,y,clause[3],beforeVars=sat_solver_nvars(s->u.pSat),beforeStored=sat_solver_nclauses(s->u.pSat);
    CEC_BASIS_REQUIRE(edge>=0 && edge<s->u.nRelations);
    ++s->cacheLookups;slot=Cec_TranLazySlot(s,frame,edge);
    if(s->Slots[slot])
    {
        ++s->cacheHits;return Vec_IntEntry(s->QueryLits,s->Slots[slot]-1);
    }
    if(2*(Vec_IntSize(s->QueryFrames)+1)>s->nSlots){Cec_TranLazyGrow(s);slot=Cec_TranLazySlot(s,frame,edge);}
    a=Cec_TranLazyEndpoint(s,frame,Vec_IntEntry(pairs,2*edge));b=Cec_TranLazyEndpoint(s,frame,Vec_IntEntry(pairs,2*edge+1));
    if(a==b)q=0;
    else if(a==(b^1))q=1;
    else
    {
        q=Abc_Var2Lit(beforeVars,0);sat_solver_setnvars(s->u.pSat,beforeVars+1);++s->queryVars;
        for(x=0;x<2;++x)for(y=0;y<2;++y)
        {clause[0]=a^x;clause[1]=b^y;clause[2]=q^(1^x^y);Cec_TranLazyClause(s,clause,3,1);}
    }
    Vec_IntPush(s->QueryFrames,frame);Vec_IntPush(s->QueryEdges,edge);Vec_IntPush(s->QueryLits,q);
    s->Slots[slot]=Vec_IntSize(s->QueryFrames);
    if(s->Trace)fprintf(s->Trace,"query context=%s frame=%d edge=%d a=%d b=%d q=%d before-vars=%d after-vars=%d before-stored=%d after-stored=%d\n",s->Context,frame,edge,a,b,q,beforeVars,sat_solver_nvars(s->u.pSat),beforeStored,sat_solver_nclauses(s->u.pSat));
    return q;
}

static void Cec_TranLazyGuard(Cec_TranRelLazy_t * s,Vec_Int_t * pairs,int frame,int edge,int guard)
{
    int a=Cec_TranLazyEndpoint(s,frame,Vec_IntEntry(pairs,2*edge)),b=Cec_TranLazyEndpoint(s,frame,Vec_IntEntry(pairs,2*edge+1)),clause[3];
    clause[0]=guard^1;clause[1]=a^1;clause[2]=b;Cec_TranLazyClause(s,clause,3,2);
    clause[0]=guard^1;clause[1]=a;clause[2]=b^1;Cec_TranLazyClause(s,clause,3,2);
    if(s->Trace)fprintf(s->Trace,"guard-edge context=%s frame=%d edge=%d guard=%d a=%d b=%d\n",s->Context,frame,edge,guard,a,b);
}

// J is a complete previously CLOSED bundle on this exact source and depth.
// J(0..k-1),T implies J(k), so these permanent facts are valid independently
// of every later speculative Frozen H. They never contain withdrawn/UNKNOWN
// hypotheses. Full transition and recipe definitions remain immutable.
static int Cec_TranLazyClosedFact(Cec_TranRelLazy_t * s,Vec_Int_t * pairs,int frame,int edge)
{
    int a=Cec_TranLazyEndpoint(s,frame,Vec_IntEntry(pairs,2*edge));
    int b=Cec_TranLazyEndpoint(s,frame,Vec_IntEntry(pairs,2*edge+1)),clause[2];
    if(a==b)return 0;
    clause[0]=a^1;clause[1]=b;Cec_TranLazyClause(s,clause,2,4);
    clause[0]=a;clause[1]=b^1;Cec_TranLazyClause(s,clause,2,4);
    return 2;
}

static void Cec_TranLazyProfile(Cec_TranRelLazy_t * s,char const * stage,int fVerbose)
{
    CEC_TRAN_VERBOSE( fVerbose, "stran-root relational-lazy: schema=1 context=%s stage=%s frames=%d original-objects=%d transition-vars=%d current-vars=%d transition-clauses-attempted=%lld initial-stored-clauses=%d current-stored-clauses=%d query-records=%d query-vars=%d query-clauses-attempted=%lld hypothesis-clauses-attempted=%lld disable-clauses-attempted=%lld closed-fact-clauses-attempted=%lld guard-vars=%d cache-lookups=%lld cache-hits=%lld\n",
        s->Context,stage,s->u.nFrames,s->nOriginalObjects,s->nTransitionVars,sat_solver_nvars(s->u.pSat),s->transitionAttempted,s->nInitialStored,sat_solver_nclauses(s->u.pSat),Vec_IntSize(s->QueryFrames),s->queryVars,s->queryAttempted,s->hypothesisAttempted,s->disableAttempted,s->closedAttempted,s->guardVars,s->cacheLookups,s->cacheHits);
    fflush(stdout);
}

static void Cec_TranLazyStop(Cec_TranRelLazy_t * s)
{
    Cec_TranRelUnrollStop(&s->u);Vec_IntFree(s->Maps);Vec_IntFree(s->QueryFrames);Vec_IntFree(s->QueryEdges);Vec_IntFree(s->QueryLits);ABC_FREE(s->Slots);
}
static Vec_Int_t * Cec_TranLazyReplay(Gia_Man_t * p, Vec_Int_t * vPairs,
    Cec_TranRelLazy_t * lazy, Vec_Int_t * vPending, Vec_Int_t * vFrozen,
    int fReset, int Frame, int Round, FILE * Trace,
    long long * pGateChecks, long long * pRelationChecks)
{
    Cec_TranRelUnroll_t * u=&lazy->u;
    Vec_Int_t * Bad = Vec_IntAlloc(0);
    int * Unroll = ABC_CALLOC(int,Gia_ManObjNum(u->p));
    int * Original = ABC_CALLOC(int,Gia_ManObjNum(p));
    int * Prev = ABC_CALLOC(int,Gia_ManObjNum(p));
    Gia_Obj_t * o;
    int i, f, ci = 0, n = u->nRelations, q;
    Gia_ManForEachCi(u->p,o,i)
    {
        int Id = Gia_ObjId(u->p,o);
        CEC_BASIS_REQUIRE(u->pSat->model[Id] == l_True || u->pSat->model[Id] == l_False);
        Unroll[Id] = sat_solver_var_value(u->pSat,Id);
    }
    Cec_TranBasisScalar(u->p,Unroll);
    CEC_BASIS_REQUIRE(Unroll[0] == 0 && !sat_solver_var_value(u->pSat,0));
    Gia_ManForEachObj1(u->p,o,i)
    {
        CEC_BASIS_REQUIRE(u->pSat->model[i] == l_True || u->pSat->model[i] == l_False);
        CEC_BASIS_REQUIRE(Unroll[i] == sat_solver_var_value(u->pSat,i));
        ++*pGateChecks;
    }
    if (Trace)
    {
        fprintf(Trace,"model reset=%d frame=%d round=%d ci=",fReset,Frame,Round);
        Gia_ManForEachCi(u->p,o,i) fprintf(Trace,"%d",Unroll[Gia_ObjId(u->p,o)]);
        fprintf(Trace," bad=");
    }
    for (f = 0; f < u->nFrames; ++f)
    {
        int * Tmp;
        Original[0] = 0;
        Gia_ManForEachPi(p,o,i)
        {
            CEC_BASIS_REQUIRE(ci < Gia_ManCiNum(u->p));
            Original[Gia_ObjId(p,o)] = Unroll[Gia_ObjId(u->p,Gia_ManCi(u->p,ci++))];
        }
        Gia_ManForEachRo(p,o,i)
        {
            if (f) Original[Gia_ObjId(p,o)] = Prev[Gia_ObjId(p,Gia_ManRi(p,i))];
            else if (fReset) Original[Gia_ObjId(p,o)] = 0;
            else
            {
                CEC_BASIS_REQUIRE(ci < Gia_ManCiNum(u->p));
                Original[Gia_ObjId(p,o)] = Unroll[Gia_ObjId(u->p,Gia_ManCi(u->p,ci++))];
            }
        }
        Cec_TranBasisScalar(p,Original);
        *pGateChecks += Gia_ManObjNum(p)-1;
        for (i = 0; i < n; ++i)
        {
            int a = Cec_TranBasisValue(Original,Vec_IntEntry(vPairs,2*i));
            int b = Cec_TranBasisValue(Original,Vec_IntEntry(vPairs,2*i+1));
            CEC_BASIS_REQUIRE(a==Cec_TranBasisValue(Unroll,Cec_TranLazyEndpoint(lazy,f,Vec_IntEntry(vPairs,2*i))));
            CEC_BASIS_REQUIRE(b==Cec_TranBasisValue(Unroll,Cec_TranLazyEndpoint(lazy,f,Vec_IntEntry(vPairs,2*i+1))));
            q = a ^ b;
            ++*pRelationChecks;
            if (!fReset && f < Frame && Vec_IntEntry(vFrozen,i))
                CEC_BASIS_REQUIRE(q == 0);
            if (f == Frame && q && Vec_IntEntry(vPending,i))
            {
                Vec_IntPush(Bad,i);
                if (Trace) fprintf(Trace,"%d,",i);
            }
        }
        Tmp = Prev; Prev = Original; Original = Tmp;
    }
    CEC_BASIS_REQUIRE(ci == Gia_ManCiNum(u->p));
    for(i=0;i<Vec_IntSize(lazy->QueryLits);++i)
    {
        int frame=Vec_IntEntry(lazy->QueryFrames,i),edge=Vec_IntEntry(lazy->QueryEdges,i);
        int lit=Vec_IntEntry(lazy->QueryLits,i),var=Abc_Lit2Var(lit);
        int a=Cec_TranBasisValue(Unroll,Cec_TranLazyEndpoint(lazy,frame,Vec_IntEntry(vPairs,2*edge)));
        int b=Cec_TranBasisValue(Unroll,Cec_TranLazyEndpoint(lazy,frame,Vec_IntEntry(vPairs,2*edge+1)));
        CEC_BASIS_REQUIRE(u->pSat->model[var]==l_True || u->pSat->model[var]==l_False);
        CEC_BASIS_REQUIRE((sat_solver_var_value(u->pSat,var)^Abc_LitIsCompl(lit))==(a^b));
        ++*pGateChecks;
    }
    CEC_BASIS_REQUIRE(Vec_IntSize(Bad) > 0);
    if (Trace) { fprintf(Trace,"\n"); fflush(Trace); }
    ABC_FREE(Unroll); ABC_FREE(Original); ABC_FREE(Prev);
    return Bad;
}


#include "cecTranRelationalActive.h"
#include "cecTranFrozenCnfQuotientProbe.h"
#include "cecTranFrozenCnfSolver.h"

// This solver applies only to already materialized ODC exit predicates. It
// never replaces an ODC root by its recipe or changes the window environment.
static int Cec_TranFrozenOdcSolverTestMode = -1;
static int Cec_TranFrozenOdcSolverOption()
{
    char const * s = getenv("ABC_STRAN_ODC_SRM");
    if ( Cec_TranFrozenOdcSolverTestMode >= 0 ) return Cec_TranFrozenOdcSolverTestMode;
    // Preserve an explicit older core selection; explicit SRM still wins.
    if ( !s ) return getenv("ABC_STRAN_ODC_CORE") ? 0 : 3;
    if ( !strcmp(s,"0") ) return 0;
    if ( !strcmp(s,"1") ) return 1; // Historical shared CEC SRM comparison.
    if ( !strcmp(s,"2") ) return 2;
    if ( !strcmp(s,"3") ) return 3;
    Abc_Print(-1,"stran-quality-invalid-option: ABC_STRAN_ODC_SRM must be 0, 1, 2 or 3\n");
    exit(2); return 0;
}

static Vec_Int_t * Cec_TranRelationalLazyBasisEngine(Gia_Man_t * p,Vec_Int_t * pairs,
    Cec_ParTran_t * pars,int * pnRounds,int useActive)
{
    int n=Vec_IntSize(pairs)/2,k=pars->nFrames,i,j,f,pivot,q,status,found,rebuild;
    static unsigned long long ProbeCalls=0;
    int fFrozenCnfProbe=pars->fRoute3 && !pars->fOdcProofScope &&
        Cec_TranFrozenCnfProbeOption("ABC_STRAN_FROZEN_CNF_QUOTIENT_PROBE");
    unsigned long long ProbeCall=fFrozenCnfProbe?++ProbeCalls:0;
    static unsigned long long SolverCalls=0;
    int SolverMode=Cec_TranFrozenCnfSolverOption();
    int SolverProfile=0,SolverOracle=0;
    unsigned long long SolverCall=0;
    int alive=n,rounds=0,changed=1,incomplete=0,baseSat=0,baseUnknown=0,indSat=0,indUnknown=0;
    long long baseQueries=0,indQueries=0,models=0,baseSatQueries=0,indSatQueries=0;
    long long gateChecks=0,relationChecks=0,baseBuilds=0,hypClauses=0;
    long long cycleObligations=0,baseDerivedFrames=0,indDerived=0;
    long long deferredWithdrawals=0;
    long long closedBaseSkipVisits=0,closedIndSkipVisits=0,closedFactVisits=0,closedFactClauses=0;
    int nKnown=Cec_TranRelClosedCurrent ? Cec_TranRelClosedCurrent->nKnown : 0;
    abctime clk=Abc_Clock(),UnrollTicks=0,SatTicks=0,ReplayTicks=0,ForestTicks=0,GuardTicks=0,TotalTicks,ResidualTicks;
    abctime ObserveSatBefore;
    // Profile only. Reuse the existing timed solve interval, with no extra
    // per-query clock reads. A requery is the same edge queried again in this
    // proof call/phase (base repeats can also come from different frames).
    abctime AnswerTicks[2][3] = {{0}}; // UNSAT, SAT, UNKNOWN
    long long AnswerQueries[2][3] = {{0}}, Requeries[2] = {0};
    Vec_Bit_t * QuerySeen[2] = {NULL, NULL};
    Vec_Int_t * Status=Vec_IntStart(n),* Scope=Vec_IntStart(n),* Frozen=Vec_IntStart(n),* Done=Vec_IntStart(n),* Bad;
    Cec_TranRelLazy_t base,ind;
    int baseLive=0,indLive=0;
    int maxBaseWithdrawn=0,maxIndWithdrawn=0;
    Cec_TranBasisForest_t g;
    Cec_TranRelActive_t active=Cec_TranActiveStart(useActive?n:0);
    FILE * trace=NULL, * lazyTrace=NULL; // No archived trace/export hook.
    if(pars->fOdcProofScope)SolverMode=Cec_TranFrozenOdcSolverOption();
    if(!pars->fRoute3 || useActive!=3)SolverMode=0;
    if(SolverMode)
    {
        SolverCall=++SolverCalls;
        SolverProfile=Cec_TranFrozenCnfProbeOption("ABC_STRAN_FROZEN_CNF_SOLVER_PROFILE");
        SolverOracle=Cec_TranFrozenCnfProbeOption("ABC_STRAN_FROZEN_CNF_SOLVER_ORACLE");
        if(Cec_TranFrozenCnfSolverTestMode>=0)SolverProfile=SolverOracle=0;
        CEC_BASIS_REQUIRE(!fFrozenCnfProbe); // Keep the frozen diagnostic separate.
    }
    if(SolverProfile)
        QuerySeen[0]=Vec_BitStart(n),QuerySeen[1]=Vec_BitStart(n);
    CEC_BASIS_REQUIRE(k>0);
    CEC_BASIS_REQUIRE(!Cec_TranRelClosedCurrent || (Cec_TranRelClosedCurrent->Frames==k && Vec_StrSize(Cec_TranRelClosedCurrent->Known)==n));
    active.fused=useActive>=2;
    CEC_BASIS_TIMED(ForestTicks,g=Cec_TranBasisForestStart(p,pairs));

    for(i=0;i<n;++i){Vec_IntWriteEntry(Status,i,1);Vec_IntWriteEntry(Scope,i,1);}
    CEC_BASIS_TIMED(UnrollTicks,base=Cec_TranLazyUnroll(p,pairs,k,1,lazyTrace));
    baseLive=1;Cec_TranSeqBudgetSetSolver(base.u.pSat);
    if(Cec_TranSeqBudgetStop())goto budget_finish;
    Cec_TranLazyProfile(&base,"construction",pars->fVerbose);
    CEC_TRAN_VERBOSE( pars->fVerbose, "stran-root relational-progress: engine=basis stage=base-unroll-ready relations=%d unroll-cnf-seconds=%.6f seconds=%.6f\n",n,(double)UnrollTicks/CLOCKS_PER_SEC,(double)(Abc_Clock()-clk)/CLOCKS_PER_SEC);fflush(stdout);
    for(f=0;f<k;++f)
    {
        if(useActive){Vec_IntForEachEntry(active.Ids,i,j)Vec_IntWriteEntry(Done,i,0);}
        else Vec_IntFill(Done,n,0);
        if(nKnown)Vec_IntForEachEntry(Cec_TranRelClosedCurrent->KnownIds,i,j)Vec_IntWriteEntry(Done,i,1);
        rebuild=1;
        while(1)
        {
            if(rebuild){CEC_BASIS_TIMED(ForestTicks,if(useActive)Cec_TranActiveBuild(&g,Scope,&active);else Cec_TranBasisBuild(&g,Scope));cycleObligations+=g.conflicts;rebuild=0;}
            Vec_IntForEachEntry(g.Edges,pivot,j)
            {
                if(useActive==3 && !Vec_IntEntry(Scope,pivot))continue;
                if(Vec_IntEntry(Done,pivot)){if(Cec_TranRelClosedKnown(pivot))++closedBaseSkipVisits;continue;}
                if(Cec_TranSeqBudgetStop())goto budget_finish;
                CEC_BASIS_REQUIRE(Vec_IntEntry(Scope,pivot));
                CEC_BASIS_TIMED(UnrollTicks,q=Cec_TranLazyQuery(&base,pairs,f,pivot));++baseQueries;
                ObserveSatBefore=SatTicks;
                CEC_BASIS_TIMED(SatTicks,status=sat_solver_solve(base.u.pSat,&q,&q+1,pars->nBTLimit,0,0,0));
                if(SolverProfile)
                {
                    int Answer=status==l_False ? 0 : status==l_True ? 1 : 2;
                    ++AnswerQueries[0][Answer];AnswerTicks[0][Answer]+=SatTicks-ObserveSatBefore;
                    Requeries[0]+=Vec_BitEntry(QuerySeen[0],pivot);
                    Vec_BitWriteEntry(QuerySeen[0],pivot,1);
                }
                Cec_TranRelObserveQuery(0,pivot,status,SatTicks-ObserveSatBefore);
                if(status==l_False)
                {
                    Vec_IntWriteEntry(Done,pivot,1);continue;
                }
                if(status==l_True)
                {
                    ++models;++baseSatQueries;found=0;
                    CEC_BASIS_TIMED(ReplayTicks,Bad=useActive ? Cec_TranActiveReplay(pairs,&base,Scope,&active,1,f,pivot,&gateChecks,&relationChecks) : Cec_TranLazyReplay(p,pairs,&base,Scope,Frozen,1,f,0,trace,&gateChecks,&relationChecks));
                    maxBaseWithdrawn=Abc_MaxInt(maxBaseWithdrawn,Vec_IntSize(Bad));
                    Vec_IntForEachEntry(Bad,i,q)
                    {
                        CEC_BASIS_REQUIRE(!Cec_TranRelClosedKnown(i));
                        CEC_BASIS_REQUIRE(Vec_IntEntry(Status,i)==1 && Vec_IntEntry(Scope,i) && !Vec_IntEntry(Done,i));
                        found|=i==pivot;Vec_IntWriteEntry(Status,i,0);Vec_IntWriteEntry(Scope,i,0);

                        ++baseSat;--alive;
                    }
                    CEC_BASIS_REQUIRE(found);Vec_IntFree(Bad);
                }
                else
                {
                    CEC_BASIS_REQUIRE(status==l_Undef);
                    Vec_IntWriteEntry(Status,pivot,-1);Vec_IntWriteEntry(Scope,pivot,0);

                    ++baseUnknown;--alive;
                }
                // Base UNSAT certificates are unconditional on this fixed
                // reset graph/frame, so retain Done while recomputing basis.
                if(useActive){if(!active.fused || status==l_Undef){CEC_BASIS_TIMED(ForestTicks,Cec_TranActiveCompact(&active,Scope));}CEC_BASIS_REQUIRE(Vec_IntSize(active.Ids)==alive);}
                rebuild=1;
                // Done consists only of actual UNSATs on this unchanged
                // reset/frame. A withdrawn forest edge grants no certificate
                // to a replacement; exhaust live old targets, then repair.
                if(useActive==3){++deferredWithdrawals;continue;}
                break;
            }
            if(rebuild) continue;
            CEC_BASIS_TIMED(ForestTicks,if(useActive)Cec_TranActiveVerify(&g,Scope,Done,&active);else Cec_TranBasisVerify(&g,Scope,Done));
            for(j=0;j<(useActive?Vec_IntSize(active.Ids):n);++j) if(Vec_IntEntry(Scope,i=useActive?Vec_IntEntry(active.Ids,j):j))
            {
                if(!Vec_IntEntry(Done,i)) ++baseDerivedFrames;
            }
            break;
        }
    }
    baseBuilds=g.builds;
    Cec_TranRelObservePrint(Cec_TranRelObserveCurrent,"base-closed",0);
    CEC_TRAN_VERBOSE( pars->fVerbose, "stran-root relational-progress: engine=basis stage=base-closed alive=%d queries=%lld sat=%d unknown=%d unroll-cnf-seconds=%.6f sat-seconds=%.6f replay-seconds=%.6f forest-seconds=%.6f seconds=%.6f\n",alive,baseQueries,baseSat,baseUnknown,(double)UnrollTicks/CLOCKS_PER_SEC,(double)SatTicks/CLOCKS_PER_SEC,(double)ReplayTicks/CLOCKS_PER_SEC,(double)ForestTicks/CLOCKS_PER_SEC,(double)(Abc_Clock()-clk)/CLOCKS_PER_SEC);fflush(stdout);
    Cec_TranLazyProfile(&base,"finish",pars->fVerbose);Cec_TranLazyStop(&base);baseLive=0;
    if(Cec_TranSeqBudgetStop())goto budget_finish;
    CEC_BASIS_TIMED(UnrollTicks,ind=Cec_TranLazyUnroll(p,pairs,k+1,0,lazyTrace));
    ind.OdcProofScope=pars->fOdcProofScope;
    indLive=1;Cec_TranSeqBudgetSetSolver(ind.u.pSat);
    if(Cec_TranSeqBudgetStop())goto budget_finish;
    if(!SolverMode)Cec_TranLazyProfile(&ind,"construction",pars->fVerbose);
    else if(SolverProfile)Cec_TranFrozenCnfTemplateProfile(&ind,"construction",SolverCall,k);
    if(nKnown)for(f=0;f<=k;++f)Vec_IntForEachEntry(Cec_TranRelClosedCurrent->KnownIds,i,j)
    {
        ++closedFactVisits;
        CEC_BASIS_TIMED(GuardTicks,closedFactClauses+=Cec_TranLazyClosedFact(&ind,pairs,f,i));
    }
    CEC_TRAN_VERBOSE( pars->fVerbose, "stran-root relational-progress: engine=basis stage=ind-unroll-ready alive=%d unroll-cnf-seconds=%.6f seconds=%.6f\n",alive,(double)UnrollTicks/CLOCKS_PER_SEC,(double)(Abc_Clock()-clk)/CLOCKS_PER_SEC);fflush(stdout);
    while(pars->nStepsMax<0 || rounds<pars->nStepsMax)
    {
        int guard,clause[3];
        Cec_TranFrozenCnfSolver_t * Fresh=NULL;
        if(Cec_TranSeqBudgetStop())goto budget_finish;
        changed=0;++rounds;
        if(useActive){Vec_IntForEachEntry(active.Ids,i,j)Vec_IntWriteEntry(Done,i,0);}
        else Vec_IntFill(Done,n,0);
        if(nKnown)Vec_IntForEachEntry(Cec_TranRelClosedCurrent->KnownIds,i,j)
        {CEC_BASIS_REQUIRE(Vec_IntEntry(Scope,i) && Vec_IntEntry(Status,i)==1);Vec_IntWriteEntry(Done,i,1);}
        if(!useActive){CEC_BASIS_TIMED(GuardTicks,for(i=0;i<n;++i)Vec_IntWriteEntry(Frozen,i,Vec_IntEntry(Scope,i)));}
        CEC_BASIS_TIMED(ForestTicks,if(useActive)Cec_TranActiveBuild(&g,Scope,&active);else Cec_TranBasisBuild(&g,Frozen));CEC_BASIS_REQUIRE(g.conflicts==0);
        if(useActive){Vec_IntClear(active.FrozenEdges);Vec_IntAppend(active.FrozenEdges,g.Edges);}
        if(fFrozenCnfProbe)
            Cec_TranFrozenCnfQuotientProbe(&ind,pairs,g.Edges,k,rounds,alive,ProbeCall);
        if(SolverMode)
        {
            CEC_BASIS_TIMED(UnrollTicks,Fresh=Cec_TranFrozenCnfStart(&ind,pairs,active.FrozenEdges,k,rounds,alive,SolverMode,SolverProfile,SolverOracle,SolverCall));
            Cec_TranSeqBudgetSetSolver(Fresh->View.u.pSat);
            guard=Fresh->Guard;hypClauses+=2*Fresh->HEquations;
        }
        else
        {
            CEC_BASIS_TIMED(GuardTicks,guard=Abc_Var2Lit(sat_solver_nvars(ind.u.pSat),0);
                sat_solver_setnvars(ind.u.pSat,sat_solver_nvars(ind.u.pSat)+1));++ind.guardVars;
            // A forest is exactly the full frozen conjunction at every frame.
            // The graph is never speculatively replaced or changed by this UF.
            for(f=0;f<k;++f) Vec_IntForEachEntry(g.Edges,i,j)
            {
                CEC_BASIS_TIMED(GuardTicks,Cec_TranLazyGuard(&ind,pairs,f,i,guard));hypClauses+=2;
            }
        }
        rebuild=0;
        while(1)
        {
            if(rebuild){CEC_BASIS_TIMED(ForestTicks,if(useActive)Cec_TranActiveBuild(&g,Scope,&active);else Cec_TranBasisBuild(&g,Scope));CEC_BASIS_REQUIRE(g.conflicts==0);rebuild=0;}
            Vec_IntForEachEntry(g.Edges,pivot,j)
            {
                int assumptions[2];
                if(useActive==3 && !Vec_IntEntry(Scope,pivot))continue;
                if(Vec_IntEntry(Done,pivot)){if(Cec_TranRelClosedKnown(pivot))++closedIndSkipVisits;continue;}
                if(Cec_TranSeqBudgetStop())
                {
                    if(Fresh)Cec_TranFrozenCnfStop(Fresh,alive);
                    goto budget_finish;
                }
                CEC_BASIS_REQUIRE(Vec_IntEntry(Scope,pivot));
                if(Fresh)
                {
                    CEC_BASIS_TIMED(UnrollTicks,assumptions[1]=Cec_TranFrozenCnfQuery(Fresh,k,pivot));
                    ++indQueries;ObserveSatBefore=SatTicks;
                    CEC_BASIS_TIMED(SatTicks,status=Cec_TranFrozenCnfSolve(Fresh,pivot,assumptions[1],pars->nBTLimit));
                }
                else
                {
                    assumptions[0]=guard;CEC_BASIS_TIMED(UnrollTicks,assumptions[1]=Cec_TranLazyQuery(&ind,pairs,k,pivot));++indQueries;
                    ObserveSatBefore=SatTicks;
                    CEC_BASIS_TIMED(SatTicks,status=sat_solver_solve(ind.u.pSat,assumptions,assumptions+2,pars->nBTLimit,0,0,0));
                }
                if(SolverProfile)
                {
                    int Answer=status==l_False ? 0 : status==l_True ? 1 : 2;
                    ++AnswerQueries[1][Answer];AnswerTicks[1][Answer]+=SatTicks-ObserveSatBefore;
                    Requeries[1]+=Vec_BitEntry(QuerySeen[1],pivot);
                    Vec_BitWriteEntry(QuerySeen[1],pivot,1);
                }
                Cec_TranRelObserveQuery(1,pivot,status,SatTicks-ObserveSatBefore);


                if(status==l_False){Vec_IntWriteEntry(Done,pivot,1);continue;}
                changed=1;
                if(status==l_True)
                {
                    ++models;++indSatQueries;found=0;
                    CEC_BASIS_TIMED(ReplayTicks,Bad=Fresh ? Cec_TranFrozenCnfReplay(Fresh,Scope,&active,pivot,&gateChecks,&relationChecks) : useActive ? Cec_TranActiveReplay(pairs,&ind,Scope,&active,0,k,pivot,&gateChecks,&relationChecks) : Cec_TranLazyReplay(p,pairs,&ind,Scope,Frozen,0,k,rounds,trace,&gateChecks,&relationChecks));
                    maxIndWithdrawn=Abc_MaxInt(maxIndWithdrawn,Vec_IntSize(Bad));
                    Vec_IntForEachEntry(Bad,i,q)
                    {
                        CEC_BASIS_REQUIRE(!Cec_TranRelClosedKnown(i));
                        CEC_BASIS_REQUIRE(Vec_IntEntry(Status,i)==1 && Vec_IntEntry(Scope,i) && !Vec_IntEntry(Done,i));
                        found|=i==pivot;Vec_IntWriteEntry(Status,i,0);Vec_IntWriteEntry(Scope,i,0);

                        ++indSat;--alive;
                    }
                    CEC_BASIS_REQUIRE(found);Vec_IntFree(Bad);
                }
                else
                {
                    CEC_BASIS_REQUIRE(status==l_Undef);
                    Vec_IntWriteEntry(Status,pivot,-1);Vec_IntWriteEntry(Scope,pivot,0);

                    ++indUnknown;--alive;
                }
                // Guard stays the original Frozen H. Rebuild the target
                // basis and reuse only actual UNSATs from this exact guard.
                // This closes all survivors under Frozen before next round.
                if(useActive){if(!active.fused || status==l_Undef){CEC_BASIS_TIMED(ForestTicks,Cec_TranActiveCompact(&active,Scope));}CEC_BASIS_REQUIRE(Vec_IntSize(active.Ids)==alive);}
                rebuild=1;
                // Frozen H and its guard remain unchanged. Query remaining
                // live selected targets, then rebuild the current Scope and
                // query all newly needed edges before any forest verification.
                if(useActive==3){++deferredWithdrawals;continue;}
                break;
            }
            if(rebuild)continue;
            CEC_BASIS_TIMED(ForestTicks,if(useActive)Cec_TranActiveVerify(&g,Scope,Done,&active);else Cec_TranBasisVerify(&g,Scope,Done));break;
        }
        if(Fresh){CEC_BASIS_TIMED(GuardTicks,Cec_TranFrozenCnfStop(Fresh,alive));}
        else {clause[0]=guard^1;CEC_BASIS_TIMED(GuardTicks,Cec_TranLazyClause(&ind,clause,1,3));}
        Cec_TranRelObservePrint(Cec_TranRelObserveCurrent,"ind-round",rounds);
        CEC_TRAN_VERBOSE( pars->fVerbose, "stran-root relational-progress: engine=basis stage=ind-round round=%d alive=%d changed=%d queries=%lld sat=%d unknown=%d unroll-cnf-seconds=%.6f sat-seconds=%.6f replay-seconds=%.6f forest-seconds=%.6f guard-seconds=%.6f seconds=%.6f\n",rounds,alive,changed,indQueries,indSat,indUnknown,(double)UnrollTicks/CLOCKS_PER_SEC,(double)SatTicks/CLOCKS_PER_SEC,(double)ReplayTicks/CLOCKS_PER_SEC,(double)ForestTicks/CLOCKS_PER_SEC,(double)GuardTicks/CLOCKS_PER_SEC,(double)(Abc_Clock()-clk)/CLOCKS_PER_SEC);fflush(stdout);
        if(!changed)
        {
            for(j=0;j<(useActive?Vec_IntSize(active.Ids):n);++j) if(Vec_IntEntry(Scope,i=useActive?Vec_IntEntry(active.Ids,j):j))
            {


                if(!Vec_IntEntry(Done,i)){++indDerived;}
            }
            break;
        }
        if(!alive)break;
    }
budget_finish:
    if(baseLive)baseBuilds=g.builds;
    // A partial round proves nothing new: its UNSATs depend on the old H.
    // Keep only independently closed history; CBS is retained by the caller.
    if(Cec_TranSeqBudgetCurrent && Cec_TranSeqBudgetCurrent->Aborted)changed=1;
    if(changed && alive)
    {
        if(!nKnown)
        {
            incomplete=alive;
            for(i=0;i<n;++i)if(Vec_IntEntry(Status,i)==1)Vec_IntWriteEntry(Status,i,-1);
            alive=0;
        }
        else
        {
            incomplete=alive-nKnown;
            for(j=0;j<(useActive?Vec_IntSize(active.Ids):n);++j)
                if(Vec_IntEntry(Status,i=useActive?Vec_IntEntry(active.Ids,j):j)==1 && !Cec_TranRelClosedKnown(i))Vec_IntWriteEntry(Status,i,-1);
            alive=nKnown;
        }
    }
    CEC_BASIS_REQUIRE(rounds<=n+1);
    if(indLive && !SolverMode)Cec_TranLazyProfile(&ind,"finish",pars->fVerbose);
    else if(indLive && SolverProfile)Cec_TranFrozenCnfTemplateProfile(&ind,"finish",SolverCall,k);
    if(Cec_TranRelClosedCurrent)
        CEC_TRAN_VERBOSE( pars->fVerbose || Cec_TranRelClosedEnabled(), "stran-root closed-bundle-work: schema=1 relations=%d known-relations=%d base-known-target-skip-visits=%lld ind-known-target-skip-visits=%lld permanent-fact-visits=%lld permanent-fact-clauses=%lld incomplete-fresh=%d\n",
            n,nKnown,closedBaseSkipVisits,closedIndSkipVisits,closedFactVisits,closedFactClauses,incomplete);
    CEC_TRAN_VERBOSE( pars->fVerbose, "stran-root relational-lazy-summary: schema=1 max-base-withdrawn=%d max-ind-withdrawn=%d\n",maxBaseWithdrawn,maxIndWithdrawn);
    if(SolverProfile)
    {
        int Phase;
        for(Phase=0;Phase<2;++Phase)
            Abc_Print(1,"stran-root relational-query-work: schema=1 call=%llu phase=%s relations=%d rounds=%d known=%d unsat=%lld sat=%lld unknown=%lld unsat-sec=%.6f sat-sec=%.6f unknown-sec=%.6f requeries=%lld withdrawn-sat=%lld withdrawn-unknown=%lld incomplete=%d\n",
                SolverCall,Phase ? "ind" : "base",n,rounds,nKnown,
                AnswerQueries[Phase][0],AnswerQueries[Phase][1],AnswerQueries[Phase][2],
                (double)AnswerTicks[Phase][0]/CLOCKS_PER_SEC,
                (double)AnswerTicks[Phase][1]/CLOCKS_PER_SEC,
                (double)AnswerTicks[Phase][2]/CLOCKS_PER_SEC,Requeries[Phase],
                (long long)(Phase ? indSat : baseSat),
                (long long)(Phase ? indUnknown : baseUnknown),incomplete);
    }
    TotalTicks=Abc_Clock()-clk;ResidualTicks=TotalTicks-UnrollTicks-SatTicks-ReplayTicks-ForestTicks-GuardTicks;
    CEC_BASIS_REQUIRE(ResidualTicks>=0);
    CEC_TRAN_VERBOSE( pars->fVerbose, "stran-root relational-proof: schema=1 depth=%d relations=%d proved=%d rounds=%d base-queries=%lld base-sat=%lld base-unknown=%d ind-queries=%lld ind-sat=%lld ind-unknown=%d incomplete=%d seconds=%.6f\n",
        k,n,alive,rounds,baseQueries,baseSatQueries,baseUnknown,indQueries,indSatQueries,indUnknown,incomplete,(double)TotalTicks/CLOCKS_PER_SEC);
    CEC_TRAN_VERBOSE( pars->fVerbose, "stran-root signed-basis-work: schema=1 relations=%d endpoint-vertices=%d models=%lld base-refuted=%d ind-refuted=%d replay-gates=%lld replay-relations=%lld base-forest-builds=%lld ind-forest-builds=%lld forest-edge-visits=%lld hypothesis-clauses=%lld cycle-obligations=%lld base-derived-frames=%lld ind-derived=%lld unroll-cnf-sec=%.6f sat-sec=%.6f replay-sec=%.6f forest-sec=%.6f guard-sec=%.6f residual-sec=%.6f\n",
        n,Vec_IntSize(g.Vars),models,baseSat,indSat,gateChecks,relationChecks,baseBuilds,g.builds-baseBuilds,g.edgeVisits,hypClauses,cycleObligations,baseDerivedFrames,indDerived,
        (double)UnrollTicks/CLOCKS_PER_SEC,(double)SatTicks/CLOCKS_PER_SEC,(double)ReplayTicks/CLOCKS_PER_SEC,(double)ForestTicks/CLOCKS_PER_SEC,(double)GuardTicks/CLOCKS_PER_SEC,(double)ResidualTicks/CLOCKS_PER_SEC);
    CEC_TRAN_VERBOSE( pars->fVerbose, "stran-root relational-active-work: schema=1 enabled=%d fused-compaction=%d deferred-forest=%d deferred-withdrawals=%lld relations=%d active-target-visits=%lld frozen-basis-visits=%lld transition-visits=%lld compact-visits=%lld verify-visits=%lld dense-replay-opportunities=%lld dense-forest-opportunities=%lld\n",
        !!useActive,active.fused,useActive==3,deferredWithdrawals,n,active.targetVisits,active.frozenVisits,active.transitionVisits,active.compactVisits,active.verifyVisits,active.denseReplayOpportunities,active.denseForestOpportunities);
    fflush(stdout);

    if(baseLive)Cec_TranLazyStop(&base);
    if(indLive)Cec_TranLazyStop(&ind);
    Cec_TranBasisForestStop(&g);
    Cec_TranActiveStop(&active);
    Vec_BitFreeP(&QuerySeen[0]);Vec_BitFreeP(&QuerySeen[1]);
    Vec_IntFree(Scope);Vec_IntFree(Frozen);Vec_IntFree(Done);if(trace)fclose(trace);if(lazyTrace)fclose(lazyTrace);
    *pnRounds=rounds;return Status;
}

static int Cec_TranRelationalLazyActiveMode(Cec_ParTran_t const * pars)
{
    // Frozen SRM requires the deferred-forest engine. Keep explicit active
    // overrides and other routes/scopes on their existing selection path.
    if(pars->fRoute3 && !pars->fOdcProofScope && !getenv("ABC_STRAN_RELATIONAL_ACTIVE"))return 3;
    return Cec_TranRelationalActiveMode();
}

static Vec_Int_t * Cec_TranRelationalLazyBasisProve(Gia_Man_t * p,Vec_Int_t * pairs,
    Cec_ParTran_t * pars,int * pnRounds)
{return Cec_TranRelationalLazyBasisEngine(p,pairs,pars,pnRounds,Cec_TranRelationalLazyActiveMode(pars));}

// End-to-end tiny engine checks retain the original base, finite-round and
// closure logic; only the induction solver is selected by the test override.
