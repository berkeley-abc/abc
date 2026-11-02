// Fixed-H relaxation only: every solver uses the same SRM graph and literal
// map. Adding a residual strengthens the formula; learned clauses never move
// between solvers or H generations. SAT is released only after full lifting.
static Cec_TranFrozenCnfSolver_t * Cec_TranFrozenLazyFull(Cec_TranFrozenCnfSolver_t * s)
{
    Cec_TranFrozenCnfSolver_t * t;int f,i,j;abctime clk=Abc_Clock();
    if(s->Full)return s->Full;
    t=ABC_CALLOC(Cec_TranFrozenCnfSolver_t,1);
    t->Template=s->Template;t->Pairs=s->Pairs;t->FrozenEdges=s->FrozenEdges;
    t->Mode=s->Mode;t->Depth=s->Depth;t->Known=s->Known;
    t->Srm=s->Srm;t->Map=s->Map; // Graph, UF and map are immutable borrowed data.
    t->Map.Table=ABC_CALLOC(Cec_TranFrozenCnfClause_t,t->Map.Capacity);t->Map.UniqueClauses=0;
    t->Inconsistent=t->Map.Contradictions!=0;t->View=*s->Template;
    t->View.u.pSat=sat_solver_new();sat_solver_setnvars(t->View.u.pSat,t->Srm.Objects);
    t->View.QueryFrames=Vec_IntAlloc(128);t->View.QueryEdges=Vec_IntAlloc(128);t->View.QueryLits=Vec_IntAlloc(128);
    t->View.nSlots=256;t->View.Slots=ABC_CALLOC(int,256);t->View.queryVars=0;
    t->View.cacheLookups=t->View.cacheHits=0;
    Cec_TranFrozenCnfEncode(t);
    if(t->Known)for(f=0;f<=t->Depth;++f)Vec_IntForEachEntry(Cec_TranRelClosedCurrent->KnownIds,i,j)
        Cec_TranFrozenCnfEquality(t,f,i,1);
    t->Guard=Abc_Var2Lit(sat_solver_nvars(t->View.u.pSat),0);
    sat_solver_setnvars(t->View.u.pSat,sat_solver_nvars(t->View.u.pSat)+1);
    for(f=0;f<t->Depth;++f)Vec_IntForEachEntry(t->FrozenEdges,i,j)Cec_TranFrozenCnfEquality(t,f,i,2);
    Cec_TranSeqBudgetSetSolver(t->View.u.pSat);
    s->Full=t;s->FullSetupTicks+=Abc_Clock()-clk;return t;
}

// remaining==0 must never reach BSAT: its zero parameter means unlimited.
// The opt-in exact cap also stops consecutive conflicts at the requested C.
static int Cec_TranFrozenLazyPhase(Cec_TranFrozenCnfSolver_t * s,Cec_TranFrozenCnfSolver_t * t,
    int query,int limit,long long * used,int full)
{
    int assumptions[2]={t->Guard,query},status,index;
    long long before=t->View.u.pSat->stats.conflicts;
    abctime clk=Abc_Clock(),elapsed;
    if(t->Inconsistent)status=l_False;
    else if((limit && *used>=limit) || Cec_TranSeqBudgetStop())
    {++s->BudgetStops;return l_Undef;}
    else
    {
        t->View.u.pSat->fExactConfLimit=1;++s->SolverCalls;
        status=sat_solver_solve(t->View.u.pSat,assumptions,assumptions+2,limit?limit-*used:0,0,0,0);
    }
    *used+=t->View.u.pSat->stats.conflicts-before;
    CEC_BASIS_REQUIRE(!limit || *used<=limit);
    elapsed=Abc_Clock()-clk;index=status+1;
    CEC_BASIS_REQUIRE(index>=0 && index<3);
    if(full){++s->FullResults[index];s->FullTicks[index]+=elapsed;}
    else {++s->FastResults[index];s->FastTicks[index]+=elapsed;}
    s->SolveTicks+=elapsed;return status;
}

// Only abstract SAT triggers a scan. Stop at eight violations; a zero result
// means ALL residual equalities were checked against this complete BSAT model.
static int Cec_TranFrozenLazyRefine(Cec_TranFrozenCnfSolver_t * s)
{
    int bad[8],n=0,i,a,b,c[2],total=(int)s->Srm.EqualitiesKept;
    abctime clk=Abc_Clock();
    if(s->ResidualActive==total)return 0;
    for(i=0;i<total && n<8;++i)
    {
        if(s->ResidualLoaded[i])continue;
        a=Cec_TranLazyModelLit(s->View.u.pSat,Vec_IntEntry(s->Srm.Equalities,2*i));
        b=Cec_TranLazyModelLit(s->View.u.pSat,Vec_IntEntry(s->Srm.Equalities,2*i+1));
        CEC_BASIS_REQUIRE(a>=0 && b>=0);++s->ResidualChecks;
        if(a!=b)bad[n++]=i;
    }
    for(i=0;i<n;++i)
    {
        int id=bad[i];a=Vec_IntEntry(s->Srm.Equalities,2*id);b=Vec_IntEntry(s->Srm.Equalities,2*id+1);
        c[0]=a^1;c[1]=b;Cec_TranFrozenCnfEmit(s,c,2,4,0);
        c[0]=a;c[1]=b^1;Cec_TranFrozenCnfEmit(s,c,2,4,0);
        s->ResidualLoaded[id]=1;++s->ResidualActive;
    }
    if(n)++s->Refinements;
    for(i=0;i<4;++i)
    {
        int percent[4]={25,50,90,100};
        if(!s->SaturatedAt[i] && 100LL*s->ResidualActive>=(long long)percent[i]*total)
            s->SaturatedAt[i]=s->Requests;
    }
    s->ResidualTicks+=Abc_Clock()-clk;return n;
}

static int Cec_TranFrozenLazySolve(Cec_TranFrozenCnfSolver_t * s,int edge,int query,int limit)
{
    Cec_TranFrozenCnfSolver_t * t;long long used=0;
    int status,step,bin,total=(int)s->Srm.EqualitiesKept;
    int fastLimit=limit?Abc_MaxInt(1,limit/4):0;
    s->ModelOwner=NULL;
    // Distribution is active residuals at query entry: 0, <=10%, <=25%,
    // <=50%, <100%, 100%. Full-confirmation frequency is separate.
    bin=!s->ResidualActive?0:s->ResidualActive==total?5:
        10LL*s->ResidualActive<=total?1:4LL*s->ResidualActive<=total?2:
        2LL*s->ResidualActive<=total?3:4;
    ++s->ActiveBins[bin];
    status=Cec_TranFrozenLazyPhase(s,s,query,fastLimit,&used,0);
    for(step=0;s->LazyMode==2 && status==l_True && step<2;++step)
    {
        if(Cec_TranSeqBudgetStop()){status=l_Undef;break;}
        if(!Cec_TranFrozenLazyRefine(s))
        {++s->LiftedSat;s->ModelOwner=s;break;}
        status=Cec_TranFrozenLazyPhase(s,s,query,fastLimit,&used,0);
    }
    // Fast/refinement share C/4 (at least one). Full gets the remaining C;
    // neither abstract SAT nor UNKNOWN is released as a counterexample.
    if(status!=l_False && !s->ModelOwner)
    {
        if((limit && used>=limit) || Cec_TranSeqBudgetStop()){++s->BudgetStops;status=l_Undef;}
        else
        {
            ++s->Fallbacks;t=Cec_TranFrozenLazyFull(s);
            query=Cec_TranFrozenCnfQuery(t,t->Depth,edge);
            status=Cec_TranFrozenLazyPhase(s,t,query,limit,&used,1);
            if(status==l_True)s->ModelOwner=t;
        }
    }
    if(used>s->QueryConflictsMax)s->QueryConflictsMax=used;
    return status;
}

static void Cec_TranFrozenLazyStop(Cec_TranFrozenCnfSolver_t * s)
{
    Cec_TranFrozenCnfSolver_t * t=(s->LazyMode || s->ResearchMode==2 || s->ResearchMode==4)?s->Full:s;int i;
    if(s->Profile)
    {
        Abc_Print(1,"stran-lazy-residual: schema=1 mode=%d research-mode=%d call=%llu round=%d residual-total=%lld residual-active=%d queries=%lld refinements=%lld residual-checks=%lld lifted-sat=%lld full-fallbacks=%lld budget-stops=%lld query-conflicts-max=%lld full-vars=%d full-clauses=%d full-conflicts=%lld full-propagations=%lld full-setup-sec=%.6f residual-sec=%.6f replay-sec=%.6f",
            s->LazyMode,s->ResearchMode,s->Call,s->Round,s->Srm.EqualitiesKept,(s->LazyMode || s->ResearchMode>=2)?s->ResidualActive:(int)s->Srm.EqualitiesKept,s->Requests,s->Refinements,s->ResidualChecks,s->LiftedSat,s->Fallbacks,s->BudgetStops,s->QueryConflictsMax,
            t?sat_solver_nvars(t->View.u.pSat):0,t?sat_solver_nclauses(t->View.u.pSat):0,t?(long long)t->View.u.pSat->stats.conflicts:0,t?(long long)t->View.u.pSat->stats.propagations:0,
            (double)s->FullSetupTicks/CLOCKS_PER_SEC,(double)s->ResidualTicks/CLOCKS_PER_SEC,(double)s->ReplayTicks/CLOCKS_PER_SEC);
        for(i=0;i<3;++i)
        {
            char const * names[3]={"unsat","unknown","sat"};
            Abc_Print(1," fast-%s=%lld fast-%s-sec=%.6f full-%s=%lld full-%s-sec=%.6f",names[i],s->FastResults[i],names[i],(double)s->FastTicks[i]/CLOCKS_PER_SEC,
                names[i],s->FullResults[i],names[i],(double)s->FullTicks[i]/CLOCKS_PER_SEC);
        }
        for(i=0;i<6;++i)Abc_Print(1," active-bin%d=%lld",i,s->ActiveBins[i]);
        for(i=0;i<4;++i)Abc_Print(1," saturation%d-query=%lld",i,s->SaturatedAt[i]);
        Abc_Print(1," scope=%s\n",s->Template->OdcProofScope?"odc":"strict");
    }
    if(s->Full)
    {
        t=s->Full;
        sat_solver_delete(t->View.u.pSat);
        Vec_IntFree(t->View.QueryFrames);Vec_IntFree(t->View.QueryEdges);Vec_IntFree(t->View.QueryLits);
        ABC_FREE(t->View.Slots);ABC_FREE(t->Map.Table);ABC_FREE(t);
    }
    ABC_FREE(s->ResidualLoaded);
}
