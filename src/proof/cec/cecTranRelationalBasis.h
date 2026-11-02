// Signed equality basis adapted from the archived 2026-10-04 phase-timed
// core (source_delta_basis_v1.tar.gz SHA256 7d9806681998a66d09e635063315a6d75e2318fac6d55a56a2742e17d9bb73c1).
// Only the proof core is imported: no old export/CLI/construction hooks.
// Every SAT model is independently replayed before any predicate is removed.
#define CEC_BASIS_REQUIRE(C) do { if (!(C)) { \
    Abc_Print(-1,"Assertion basis relational invariant failed at %s:%d: %s\n",__FILE__,__LINE__,#C); \
    abort(); } } while (0)

#define CEC_BASIS_TIMED(T,A) do { abctime cecBasisTick=Abc_Clock(); A; (T)+=Abc_Clock()-cecBasisTick; } while(0)

static int Cec_TranRelationalBasisMode()
{
    char const * s = getenv("ABC_STRAN_RELATIONAL_BASIS");
    if (!s || !strcmp(s,"0")) return 0;
    if (!strcmp(s,"1")) return 1;
    if (!strcmp(s,"2")) return 2; // Same basis closure, lazy query definitions.
    Abc_Print(-1,"stran-quality-invalid-option: ABC_STRAN_RELATIONAL_BASIS must be 0, 1 or 2\n");
    exit(2); return 0;
}

static int Cec_TranBasisValue(int * Values, int Lit)
{
    return Values[Abc_Lit2Var(Lit)] ^ Abc_LitIsCompl(Lit);
}

static void Cec_TranBasisScalar(Gia_Man_t * p, int * Values)
{
    Gia_Obj_t * o;
    int i, a, b;
    Gia_ManForEachObj1(p,o,i)
    {
        if (Gia_ObjIsCi(o)) continue;
        a = Values[Gia_ObjFaninId0p(p,o)] ^ Gia_ObjFaninC0(o);
        if (Gia_ObjIsCo(o) || Gia_ObjIsBuf(o)) Values[i] = a;
        else
        {
            b = Values[Gia_ObjFaninId1p(p,o)] ^ Gia_ObjFaninC1(o);
            Values[i] = Gia_ObjIsXor(o) ? a ^ b : a & b;
        }
    }
}

// One model is evaluated twice: the explicit CNF's unrolled gate graph, then
// the original graph with scalar register transitions and fresh frame PIs.
// The original graph already contains all explicit recipe gates. No inferred
// equality, replacement graph, or random resimulation is used here.
static Vec_Int_t * Cec_TranBasisReplay(Gia_Man_t * p, Vec_Int_t * vPairs,
    Cec_TranRelUnroll_t * u, Vec_Int_t * vPending, Vec_Int_t * vFrozen,
    int fReset, int Frame, int Round, FILE * Trace,
    long long * pGateChecks, long long * pRelationChecks)
{
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
            q = Cec_TranBasisValue(Unroll,Vec_IntEntry(u->vQueries,f*n+i));
            CEC_BASIS_REQUIRE(q == (a ^ b));
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
    CEC_BASIS_REQUIRE(Vec_IntSize(Bad) > 0);
    if (Trace) { fprintf(Trace,"\n"); fflush(Trace); }
    ABC_FREE(Unroll); ABC_FREE(Original); ABC_FREE(Prev);
    return Bad;
}


// Algebraic equality basis only. No graph replacement or simulation phases.
typedef struct Cec_TranBasisForest_t_ {
    Vec_Int_t * Vars, * Left, * Right, * Parent, * Size, * Edges;
    Vec_Str_t * Sign, * Parity, * Chosen;
    int n, conflicts;
    long long builds, edgeVisits;
} Cec_TranBasisForest_t;

static Cec_TranBasisForest_t Cec_TranBasisForestStart(Gia_Man_t * p, Vec_Int_t * pairs)
{
    Cec_TranBasisForest_t g;
    int * map=ABC_FALLOC(int,Gia_ManObjNum(p));
    int i,a,b;
    memset(&g,0,sizeof(g)); g.n=Vec_IntSize(pairs)/2;
    g.Vars=Vec_IntAlloc(128); g.Left=Vec_IntAlloc(g.n); g.Right=Vec_IntAlloc(g.n);
    g.Sign=Vec_StrAlloc(g.n); g.Chosen=Vec_StrStart(g.n); g.Edges=Vec_IntAlloc(128);
    for(i=0;i<g.n;++i)
    {
        a=Abc_Lit2Var(Vec_IntEntry(pairs,2*i)); b=Abc_Lit2Var(Vec_IntEntry(pairs,2*i+1));
        CEC_BASIS_REQUIRE(a<Gia_ManObjNum(p) && b<Gia_ManObjNum(p));
        if(map[a]<0) {map[a]=Vec_IntSize(g.Vars);Vec_IntPush(g.Vars,a);}
        if(map[b]<0) {map[b]=Vec_IntSize(g.Vars);Vec_IntPush(g.Vars,b);}
        Vec_IntPush(g.Left,map[a]);Vec_IntPush(g.Right,map[b]);
        Vec_StrPush(g.Sign,(char)((Vec_IntEntry(pairs,2*i)^Vec_IntEntry(pairs,2*i+1))&1));
    }
    g.Parent=Vec_IntStart(Vec_IntSize(g.Vars));g.Size=Vec_IntStart(Vec_IntSize(g.Vars));
    g.Parity=Vec_StrStart(Vec_IntSize(g.Vars));ABC_FREE(map);return g;
}

static int Cec_TranBasisFind(Cec_TranBasisForest_t * g,int x,int * value)
{
    int r=x,par=0,y=x,tail;
    while(Vec_IntEntry(g->Parent,r)!=r)
    {par^=Vec_StrEntry(g->Parity,r);r=Vec_IntEntry(g->Parent,r);}
    tail=par;
    while(Vec_IntEntry(g->Parent,y)!=y)
    {
        int next=Vec_IntEntry(g->Parent,y),old=Vec_StrEntry(g->Parity,y);
        Vec_IntWriteEntry(g->Parent,y,r);Vec_StrWriteEntry(g->Parity,y,(char)tail);
        tail^=old;y=next;
    }
    *value=par;return r;
}

// Preserve conflicting original edges as explicit obligations. A forest
// alone never represents an inconsistent signed conjunction.
static void Cec_TranBasisBuild(Cec_TranBasisForest_t * g,Vec_Int_t * scope)
{
    int i,a,b,ra,rb,pa,pb,tmp;
    ++g->builds;g->edgeVisits+=g->n;g->conflicts=0;
    Vec_IntClear(g->Edges);Vec_StrFill(g->Chosen,g->n,0);
    for(i=0;i<Vec_IntSize(g->Vars);++i)
    {Vec_IntWriteEntry(g->Parent,i,i);Vec_IntWriteEntry(g->Size,i,1);Vec_StrWriteEntry(g->Parity,i,0);}
    for(i=0;i<g->n;++i) if(Vec_IntEntry(scope,i))
    {
        a=Vec_IntEntry(g->Left,i);b=Vec_IntEntry(g->Right,i);
        ra=Cec_TranBasisFind(g,a,&pa);rb=Cec_TranBasisFind(g,b,&pb);
        if(ra==rb)
        {
            if((pa^pb)==Vec_StrEntry(g->Sign,i)) continue;
            Vec_StrWriteEntry(g->Chosen,i,2);Vec_IntPush(g->Edges,i);++g->conflicts;continue;
        }
        if(Vec_IntEntry(g->Size,ra)<Vec_IntEntry(g->Size,rb)) {tmp=ra;ra=rb;rb=tmp;}
        Vec_IntWriteEntry(g->Parent,rb,ra);
        Vec_StrWriteEntry(g->Parity,rb,(char)(pa^pb^Vec_StrEntry(g->Sign,i)));
        Vec_IntWriteEntry(g->Size,ra,Vec_IntEntry(g->Size,ra)+Vec_IntEntry(g->Size,rb));
        Vec_StrWriteEntry(g->Chosen,i,1);Vec_IntPush(g->Edges,i);
    }
}

static void Cec_TranBasisVerify(Cec_TranBasisForest_t * g,Vec_Int_t * scope,Vec_Int_t * done)
{
    int i,j,ra,rb,pa,pb;
    CEC_BASIS_REQUIRE(g->conflicts==0);
    Vec_IntForEachEntry(g->Edges,i,j)
        CEC_BASIS_REQUIRE(Vec_IntEntry(scope,i) && Vec_IntEntry(done,i));
    for(i=0;i<g->n;++i) if(Vec_IntEntry(scope,i))
    {
        ra=Cec_TranBasisFind(g,Vec_IntEntry(g->Left,i),&pa);
        rb=Cec_TranBasisFind(g,Vec_IntEntry(g->Right,i),&pb);
        CEC_BASIS_REQUIRE(ra==rb && (pa^pb)==Vec_StrEntry(g->Sign,i));
    }
}

static void Cec_TranBasisForestStop(Cec_TranBasisForest_t * g)
{
    Vec_IntFree(g->Vars);Vec_IntFree(g->Left);Vec_IntFree(g->Right);Vec_IntFree(g->Parent);
    Vec_IntFree(g->Size);Vec_IntFree(g->Edges);Vec_StrFree(g->Sign);Vec_StrFree(g->Parity);Vec_StrFree(g->Chosen);
}

static Vec_Int_t * Cec_TranRelationalBasisProve(Gia_Man_t * p,Vec_Int_t * pairs,
    Cec_ParTran_t * pars,int * pnRounds)
{
    int n=Vec_IntSize(pairs)/2,k=pars->nFrames,i,j,f,pivot,q,status,found,rebuild;
    int alive=n,rounds=0,changed=1,incomplete=0,baseSat=0,baseUnknown=0,indSat=0,indUnknown=0;
    long long baseQueries=0,indQueries=0,models=0,baseSatQueries=0,indSatQueries=0;
    long long gateChecks=0,relationChecks=0,baseBuilds=0,hypClauses=0;
    long long cycleObligations=0,baseDerivedFrames=0,indDerived=0;
    abctime clk=Abc_Clock(),UnrollTicks=0,SatTicks=0,ReplayTicks=0,ForestTicks=0,GuardTicks=0,TotalTicks,ResidualTicks;
    Vec_Int_t * Status=Vec_IntStart(n),* Scope=Vec_IntStart(n),* Frozen=Vec_IntStart(n),* Done=Vec_IntStart(n),* Bad;
    Cec_TranRelUnroll_t base,ind;
    Cec_TranBasisForest_t g;
    FILE * trace=NULL; // Archived trace/export hooks are not restored.
    CEC_BASIS_REQUIRE(k>0);
    CEC_BASIS_TIMED(ForestTicks,g=Cec_TranBasisForestStart(p,pairs));

    for(i=0;i<n;++i){Vec_IntWriteEntry(Status,i,1);Vec_IntWriteEntry(Scope,i,1);}
    CEC_BASIS_TIMED(UnrollTicks,base=Cec_TranRelUnroll(p,pairs,k,1));
    CEC_TRAN_VERBOSE( pars->fVerbose, "stran-root relational-progress: engine=basis stage=base-unroll-ready relations=%d unroll-cnf-seconds=%.6f seconds=%.6f\n",n,(double)UnrollTicks/CLOCKS_PER_SEC,(double)(Abc_Clock()-clk)/CLOCKS_PER_SEC);fflush(stdout);
    for(f=0;f<k;++f)
    {
        Vec_IntFill(Done,n,0);rebuild=1;
        while(1)
        {
            if(rebuild){CEC_BASIS_TIMED(ForestTicks,Cec_TranBasisBuild(&g,Scope));cycleObligations+=g.conflicts;rebuild=0;}
            Vec_IntForEachEntry(g.Edges,pivot,j)
            {
                if(Vec_IntEntry(Done,pivot)) continue;
                CEC_BASIS_REQUIRE(Vec_IntEntry(Scope,pivot));
                q=Vec_IntEntry(base.vQueries,f*n+pivot);++baseQueries;
                CEC_BASIS_TIMED(SatTicks,status=sat_solver_solve(base.pSat,&q,&q+1,pars->nBTLimit,0,0,0));
                if(status==l_False)
                {
                    Vec_IntWriteEntry(Done,pivot,1);continue;
                }
                if(status==l_True)
                {
                    ++models;++baseSatQueries;found=0;
                    CEC_BASIS_TIMED(ReplayTicks,Bad=Cec_TranBasisReplay(p,pairs,&base,Scope,Frozen,1,f,0,trace,&gateChecks,&relationChecks));
                    Vec_IntForEachEntry(Bad,i,q)
                    {
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
                rebuild=1;break;
            }
            if(rebuild) continue;
            CEC_BASIS_TIMED(ForestTicks,Cec_TranBasisVerify(&g,Scope,Done));
            for(i=0;i<n;++i) if(Vec_IntEntry(Scope,i))
            {
                if(!Vec_IntEntry(Done,i)) ++baseDerivedFrames;
            }
            break;
        }
    }
    baseBuilds=g.builds;
    CEC_TRAN_VERBOSE( pars->fVerbose, "stran-root relational-progress: engine=basis stage=base-closed alive=%d queries=%lld sat=%d unknown=%d unroll-cnf-seconds=%.6f sat-seconds=%.6f replay-seconds=%.6f forest-seconds=%.6f seconds=%.6f\n",alive,baseQueries,baseSat,baseUnknown,(double)UnrollTicks/CLOCKS_PER_SEC,(double)SatTicks/CLOCKS_PER_SEC,(double)ReplayTicks/CLOCKS_PER_SEC,(double)ForestTicks/CLOCKS_PER_SEC,(double)(Abc_Clock()-clk)/CLOCKS_PER_SEC);fflush(stdout);
    Cec_TranRelUnrollStop(&base);CEC_BASIS_TIMED(UnrollTicks,ind=Cec_TranRelUnroll(p,pairs,k+1,0));
    CEC_TRAN_VERBOSE( pars->fVerbose, "stran-root relational-progress: engine=basis stage=ind-unroll-ready alive=%d unroll-cnf-seconds=%.6f seconds=%.6f\n",alive,(double)UnrollTicks/CLOCKS_PER_SEC,(double)(Abc_Clock()-clk)/CLOCKS_PER_SEC);fflush(stdout);
    while(pars->nStepsMax<0 || rounds<pars->nStepsMax)
    {
        int guard,clause[2];
        changed=0;++rounds;Vec_IntFill(Done,n,0);
        CEC_BASIS_TIMED(GuardTicks,for(i=0;i<n;++i)Vec_IntWriteEntry(Frozen,i,Vec_IntEntry(Scope,i)));
        CEC_BASIS_TIMED(ForestTicks,Cec_TranBasisBuild(&g,Frozen));CEC_BASIS_REQUIRE(g.conflicts==0);
        CEC_BASIS_TIMED(GuardTicks,guard=Abc_Var2Lit(sat_solver_nvars(ind.pSat),0);
            sat_solver_setnvars(ind.pSat,sat_solver_nvars(ind.pSat)+1));
        // A forest is exactly the full frozen conjunction at every frame.
        // The graph is never speculatively replaced or changed by this UF.
        for(f=0;f<k;++f) Vec_IntForEachEntry(g.Edges,i,j)
        {
            clause[0]=guard^1;clause[1]=Vec_IntEntry(ind.vQueries,f*n+i)^1;
            CEC_BASIS_TIMED(GuardTicks,Cec_TranRelClause(ind.pSat,clause,2));++hypClauses;
        }
        rebuild=0;
        while(1)
        {
            if(rebuild){CEC_BASIS_TIMED(ForestTicks,Cec_TranBasisBuild(&g,Scope));CEC_BASIS_REQUIRE(g.conflicts==0);rebuild=0;}
            Vec_IntForEachEntry(g.Edges,pivot,j)
            {
                int assumptions[2];
                if(Vec_IntEntry(Done,pivot))continue;
                CEC_BASIS_REQUIRE(Vec_IntEntry(Scope,pivot));
                assumptions[0]=guard;assumptions[1]=Vec_IntEntry(ind.vQueries,k*n+pivot);++indQueries;
                CEC_BASIS_TIMED(SatTicks,status=sat_solver_solve(ind.pSat,assumptions,assumptions+2,pars->nBTLimit,0,0,0));


                if(status==l_False){Vec_IntWriteEntry(Done,pivot,1);continue;}
                changed=1;
                if(status==l_True)
                {
                    ++models;++indSatQueries;found=0;
                    CEC_BASIS_TIMED(ReplayTicks,Bad=Cec_TranBasisReplay(p,pairs,&ind,Scope,Frozen,0,k,rounds,trace,&gateChecks,&relationChecks));
                    Vec_IntForEachEntry(Bad,i,q)
                    {
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
                rebuild=1;break;
            }
            if(rebuild)continue;
            CEC_BASIS_TIMED(ForestTicks,Cec_TranBasisVerify(&g,Scope,Done));break;
        }
        clause[0]=guard^1;CEC_BASIS_TIMED(GuardTicks,Cec_TranRelClause(ind.pSat,clause,1));
        CEC_TRAN_VERBOSE( pars->fVerbose, "stran-root relational-progress: engine=basis stage=ind-round round=%d alive=%d changed=%d queries=%lld sat=%d unknown=%d unroll-cnf-seconds=%.6f sat-seconds=%.6f replay-seconds=%.6f forest-seconds=%.6f guard-seconds=%.6f seconds=%.6f\n",rounds,alive,changed,indQueries,indSat,indUnknown,(double)UnrollTicks/CLOCKS_PER_SEC,(double)SatTicks/CLOCKS_PER_SEC,(double)ReplayTicks/CLOCKS_PER_SEC,(double)ForestTicks/CLOCKS_PER_SEC,(double)GuardTicks/CLOCKS_PER_SEC,(double)(Abc_Clock()-clk)/CLOCKS_PER_SEC);fflush(stdout);
        if(!changed)
        {
            for(i=0;i<n;++i) if(Vec_IntEntry(Scope,i))
            {


                if(!Vec_IntEntry(Done,i)){++indDerived;}
            }
            break;
        }
        if(!alive)break;
    }
    if(changed && alive)
    {
        incomplete=alive;
        for(i=0;i<n;++i)if(Vec_IntEntry(Status,i)==1)Vec_IntWriteEntry(Status,i,-1);
        alive=0;
    }
    CEC_BASIS_REQUIRE(rounds<=n+1);
    TotalTicks=Abc_Clock()-clk;ResidualTicks=TotalTicks-UnrollTicks-SatTicks-ReplayTicks-ForestTicks-GuardTicks;
    CEC_BASIS_REQUIRE(ResidualTicks>=0);
    // Preserve the old schema's SAT/UNKNOWN fields as actual solver queries.
    CEC_TRAN_VERBOSE( pars->fVerbose, "stran-root relational-proof: schema=1 depth=%d relations=%d proved=%d rounds=%d base-queries=%lld base-sat=%lld base-unknown=%d ind-queries=%lld ind-sat=%lld ind-unknown=%d incomplete=%d seconds=%.6f\n",
        k,n,alive,rounds,baseQueries,baseSatQueries,baseUnknown,indQueries,indSatQueries,indUnknown,incomplete,(double)TotalTicks/CLOCKS_PER_SEC);
    CEC_TRAN_VERBOSE( pars->fVerbose, "stran-root signed-basis-work: schema=1 relations=%d endpoint-vertices=%d models=%lld base-refuted=%d ind-refuted=%d replay-gates=%lld replay-relations=%lld base-forest-builds=%lld ind-forest-builds=%lld forest-edge-visits=%lld hypothesis-clauses=%lld cycle-obligations=%lld base-derived-frames=%lld ind-derived=%lld unroll-cnf-sec=%.6f sat-sec=%.6f replay-sec=%.6f forest-sec=%.6f guard-sec=%.6f residual-sec=%.6f\n",
        n,Vec_IntSize(g.Vars),models,baseSat,indSat,gateChecks,relationChecks,baseBuilds,g.builds-baseBuilds,g.edgeVisits,hypClauses,cycleObligations,baseDerivedFrames,indDerived,
        (double)UnrollTicks/CLOCKS_PER_SEC,(double)SatTicks/CLOCKS_PER_SEC,(double)ReplayTicks/CLOCKS_PER_SEC,(double)ForestTicks/CLOCKS_PER_SEC,(double)GuardTicks/CLOCKS_PER_SEC,(double)ResidualTicks/CLOCKS_PER_SEC);

    Cec_TranRelUnrollStop(&ind);Cec_TranBasisForestStop(&g);
    Vec_IntFree(Scope);Vec_IntFree(Frozen);Vec_IntFree(Done);if(trace)fclose(trace);
    *pnRounds=rounds;return Status;
}
#include "cecTranRelationalLazy.h"

// Independent 6-variable conjunction oracle, including odd cycles and deletion.
// It does not use union-find or paths to determine either Boolean truth.
#undef CEC_BASIS_TIMED
#undef CEC_BASIS_REQUIRE
