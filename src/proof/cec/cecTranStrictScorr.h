// Ordinary SSW/scorr-style CNF on one immutable Frozen-H SRM. Every residual
// is loaded, but only its endpoint cones and subsequently requested query
// cones get SAT variables. Supergates and muxes have exact definitions, so a
// compact SAT model extends to the complete SRM by evaluating its omitted
// gates. No second solver, relaxation, or independently proved H is involved.
typedef struct Cec_TranStrictScorr_t_ {
    int * Vars, * Refs;
    unsigned char * Values;
    Vec_Int_t * Frontier, * Stack, * Fanins, * Clause;
    int Aborted, LastEdge, LastQuery, EncodedGates, EncodedCis;
    long long Queries, StructuralQueries, Supergates, SuperLeaves, Absorbed, Muxes, Xors, WideClauses;
    abctime IndexTicks, LoadTicks, ModelTicks;
} Cec_TranStrictScorr_t;

static int Cec_TranStrictScorrStopped(Cec_TranStrictScorr_t * p)
{
    if(p->Aborted || Cec_TranSeqBudgetStop()){p->Aborted=1;return 1;}
    return 0;
}

static int Cec_TranStrictScorrLit(Cec_TranStrictScorr_t * p,int lit)
{
    int var=p->Vars[Abc_Lit2Var(lit)];CEC_BASIS_REQUIRE(var>=0);
    return Abc_Var2Lit(var,Abc_LitIsCompl(lit));
}

// Gia's structural mux recognizer assumes ordinary AND children. The SRM
// also supports typed XORs, which must never be interpreted as those ANDs.
static int Cec_TranStrictScorrIsMux(Gia_Obj_t * o)
{
    if(!Gia_ObjIsAnd(o) || Gia_ObjIsBuf(o) || Gia_ObjIsXor(o))return 0;
    if(!Gia_ObjFaninC0(o) || !Gia_ObjFaninC1(o))return 0;
    if(Gia_ObjIsXor(Gia_ObjFanin0(o)) || Gia_ObjIsXor(Gia_ObjFanin1(o)))return 0;
    return Gia_ObjIsMuxType(o);
}

static void Cec_TranStrictScorrFrontier(Cec_TranFrozenCnfSolver_t * s,int lit)
{
    Cec_TranStrictScorr_t * p=(Cec_TranStrictScorr_t *)s->ResearchData;
    int id=Abc_Lit2Var(lit);
    if(p->Vars[id]>=0)return;
    CEC_BASIS_REQUIRE(sat_solver_nvars(s->View.u.pSat)<1073741823);
    p->Vars[id]=sat_solver_nvars(s->View.u.pSat);
    sat_solver_setnvars(s->View.u.pSat,p->Vars[id]+1);
    if(Gia_ObjIsCi(Gia_ManObj(s->Srm.Graph,id)))++p->EncodedCis;
    else Vec_IntPush(p->Frontier,id);
}

// The only wide clauses are one per unique supergate output variable, hence
// they cannot duplicate each other. Keep the existing small-clause hash and
// its occupancy separate; Kind includes both short and wide clause counts.
static void Cec_TranStrictScorrWide(Cec_TranFrozenCnfSolver_t * s)
{
    Cec_TranStrictScorr_t * p=(Cec_TranStrictScorr_t *)s->ResearchData;
    Cec_TranFrozenCnfKind_t * k=&s->Kind[0];
    int * lits=Vec_IntArray(p->Clause),width=Vec_IntSize(p->Clause),i,n=0,x,before;
    if(width<=3){Cec_TranFrozenCnfEmit(s,lits,width,0,0);return;}
    ++p->WideClauses;++k->Attempted;k->LiteralsIn+=width;Vec_IntSort(p->Clause,0);
    for(i=0;i<width;++i)
    {
        x=lits[i];
        if(x==1 || (n && x==(lits[n-1]^1))){++k->Tautologies;return;}
        if(!x || (n && x==lits[n-1]))continue;
        lits[n++]=x;
    }
    if(!n){++k->Empty;s->Inconsistent=1;return;}
    ++k->Unique;k->LiteralsUnique+=n;
    if(s->Inconsistent)return;
    before=sat_solver_nclauses(s->View.u.pSat);
    if(!sat_solver_addclause(s->View.u.pSat,lits,lits+n))s->Inconsistent=1;
    k->Stored+=sat_solver_nclauses(s->View.u.pSat)-before;
}

// Iterative SSW supergate collection: complemented edges, shared nodes,
// already encoded nodes, muxes, and typed XORs form exact cone boundaries.
static void Cec_TranStrictScorrCollect(Cec_TranFrozenCnfSolver_t * s,int root)
{
    Cec_TranStrictScorr_t * p=(Cec_TranStrictScorr_t *)s->ResearchData;
    Gia_Man_t * g=s->Srm.Graph;Gia_Obj_t * o;
    int lit,id,visits=0;
    Vec_IntClear(p->Stack);Vec_IntClear(p->Fanins);
    o=Gia_ManObj(g,root);
    Vec_IntPush(p->Stack,Gia_ObjFaninLit0p(g,o));Vec_IntPush(p->Stack,Gia_ObjFaninLit1p(g,o));
    while(Vec_IntSize(p->Stack))
    {
        if(!(visits++&4095) && Cec_TranStrictScorrStopped(p))break;
        lit=Vec_IntPop(p->Stack);id=Abc_Lit2Var(lit);o=Gia_ManObj(g,id);
        if(!id || Abc_LitIsCompl(lit) || Gia_ObjIsCi(o) || p->Refs[id]>1 ||
            p->Vars[id]>=0 || Gia_ObjIsXor(o) || Cec_TranStrictScorrIsMux(o))
        {Vec_IntPush(p->Fanins,lit);continue;}
        CEC_BASIS_REQUIRE(Gia_ObjIsAnd(o) && !Gia_ObjIsBuf(o));++p->Absorbed;
        Vec_IntPush(p->Stack,Gia_ObjFaninLit0p(g,o));Vec_IntPush(p->Stack,Gia_ObjFaninLit1p(g,o));
    }
    Vec_IntClear(p->Stack);
}

static void Cec_TranStrictScorrLoad(Cec_TranFrozenCnfSolver_t * s,int root)
{
    Cec_TranStrictScorr_t * p=(Cec_TranStrictScorr_t *)s->ResearchData;
    Gia_Man_t * g=s->Srm.Graph;Gia_Obj_t * o;
    int i,j,id,lit,a,b,z,t,e,c[3],x,y;
    if(p->Aborted || p->Vars[Abc_Lit2Var(root)]>=0)return;
    Vec_IntClear(p->Frontier);Cec_TranStrictScorrFrontier(s,root);
    Vec_IntForEachEntry(p->Frontier,id,i)
    {
        if(Cec_TranStrictScorrStopped(p))break;
        o=Gia_ManObj(g,id);CEC_BASIS_REQUIRE(Gia_ObjIsAnd(o) && !Gia_ObjIsBuf(o));
        z=Abc_Var2Lit(p->Vars[id],0);
        if(Gia_ObjIsXor(o))
        {
            a=Gia_ObjFaninLit0p(g,o);b=Gia_ObjFaninLit1p(g,o);
            Cec_TranStrictScorrFrontier(s,a);Cec_TranStrictScorrFrontier(s,b);
            a=Cec_TranStrictScorrLit(p,a);b=Cec_TranStrictScorrLit(p,b);
            for(x=0;x<2;++x)for(y=0;y<2;++y)
            {c[0]=a^x;c[1]=b^y;c[2]=z^(1^x^y);Cec_TranFrozenCnfEmit(s,c,3,0,0);}
            ++p->Xors;
        }
        else if(Cec_TranStrictScorrIsMux(o))
        {
            a=Gia_ObjRecognizeMuxLits(g,o,&t,&e);
            Cec_TranStrictScorrFrontier(s,a);Cec_TranStrictScorrFrontier(s,t);Cec_TranStrictScorrFrontier(s,e);
            a=Cec_TranStrictScorrLit(p,a);t=Cec_TranStrictScorrLit(p,t);e=Cec_TranStrictScorrLit(p,e);
            c[0]=a^1;c[1]=t^1;c[2]=z;Cec_TranFrozenCnfEmit(s,c,3,0,0);
            c[0]=a^1;c[1]=t;c[2]=z^1;Cec_TranFrozenCnfEmit(s,c,3,0,0);
            c[0]=a;c[1]=e^1;c[2]=z;Cec_TranFrozenCnfEmit(s,c,3,0,0);
            c[0]=a;c[1]=e;c[2]=z^1;Cec_TranFrozenCnfEmit(s,c,3,0,0);
            if(Abc_Lit2Var(t)!=Abc_Lit2Var(e))
            {
                c[0]=t;c[1]=e;c[2]=z^1;Cec_TranFrozenCnfEmit(s,c,3,0,0);
                c[0]=t^1;c[1]=e^1;c[2]=z;Cec_TranFrozenCnfEmit(s,c,3,0,0);
            }
            ++p->Muxes;
        }
        else
        {
            Cec_TranStrictScorrCollect(s,id);if(p->Aborted)break;
            Vec_IntClear(p->Clause);
            Vec_IntForEachEntry(p->Fanins,lit,j)
            {
                if(!(j&4095) && Cec_TranStrictScorrStopped(p))break;
                Cec_TranStrictScorrFrontier(s,lit);a=Cec_TranStrictScorrLit(p,lit);
                c[0]=z^1;c[1]=a;Cec_TranFrozenCnfEmit(s,c,2,0,0);Vec_IntPush(p->Clause,a^1);
            }
            if(p->Aborted)break;
            Vec_IntPush(p->Clause,z);Cec_TranStrictScorrWide(s);
            ++p->Supergates;p->SuperLeaves+=Vec_IntSize(p->Fanins);
        }
        ++p->EncodedGates;
    }
    Vec_IntClear(p->Frontier);
}

static void Cec_TranStrictScorrStart(Cec_TranFrozenCnfSolver_t * s)
{
    Cec_TranStrictScorr_t * p=ABC_CALLOC(Cec_TranStrictScorr_t,1);
    Gia_Obj_t * o;int i,a,b,c[2],n=s->Srm.Objects;abctime clk=Abc_Clock();
    CEC_BASIS_REQUIRE(s->Mode==3 && s->ResearchMode==3 && !s->ResearchData && !s->LazyMode);
    CEC_BASIS_REQUIRE(sat_solver_nvars(s->View.u.pSat)==1 && s->Srm.EqualitiesKept<=INT_MAX/2);
    s->ResearchData=p;s->Guard=1;p->LastEdge=-1;
    p->Vars=ABC_FALLOC(int,n);p->Vars[0]=0;p->Refs=ABC_CALLOC(int,n);p->Values=ABC_CALLOC(unsigned char,n);
    p->Frontier=Vec_IntAlloc(128);p->Stack=Vec_IntAlloc(128);p->Fanins=Vec_IntAlloc(32);p->Clause=Vec_IntAlloc(32);
    // The SRM owns no output objects. Count residual endpoints as external
    // uses as well, to avoid flattening across repeatedly loaded constraints.
    Gia_ManForEachAnd(s->Srm.Graph,o,i)
    {
        if(!(i&4095) && Cec_TranStrictScorrStopped(p))break;
        ++p->Refs[Gia_ObjFaninId0p(s->Srm.Graph,o)];++p->Refs[Gia_ObjFaninId1p(s->Srm.Graph,o)];
    }
    Vec_IntForEachEntry(s->Srm.Equalities,a,i)
    {
        if(!(i&4095) && Cec_TranStrictScorrStopped(p))break;
        ++p->Refs[Abc_Lit2Var(a)];
    }
    p->IndexTicks=Abc_Clock()-clk;clk=Abc_Clock();
    ABC_FREE(s->Map.Table);s->Map.Capacity=256;s->Map.UniqueClauses=0;
    s->Map.Table=ABC_CALLOC(Cec_TranFrozenCnfClause_t,256);
    c[0]=1;Cec_TranFrozenCnfEmit(s,c,1,0,1);Cec_TranSeqBudgetSetSolver(s->View.u.pSat);
    for(i=0;i<s->Srm.EqualitiesKept;++i)
    {
        if(Cec_TranStrictScorrStopped(p))break;
        a=Vec_IntEntry(s->Srm.Equalities,2*i);b=Vec_IntEntry(s->Srm.Equalities,2*i+1);
        Cec_TranStrictScorrLoad(s,a);Cec_TranStrictScorrLoad(s,b);if(p->Aborted)break;
        a=Cec_TranStrictScorrLit(p,a);b=Cec_TranStrictScorrLit(p,b);
        c[0]=a^1;c[1]=b;Cec_TranFrozenCnfEmit(s,c,2,4,0);
        c[0]=a;c[1]=b^1;Cec_TranFrozenCnfEmit(s,c,2,4,0);++s->ResidualActive;
    }
    p->LoadTicks=Abc_Clock()-clk;
}

static int Cec_TranStrictScorrQuery(Cec_TranFrozenCnfSolver_t * s,int frame,int edge)
{
    Cec_TranStrictScorr_t * p=(Cec_TranStrictScorr_t *)s->ResearchData;
    Cec_TranRelLazy_t * v=&s->View;int a,b,q=0,slot,x,y,c[3];abctime clk=Abc_Clock();
    CEC_BASIS_REQUIRE(frame==s->Depth && edge>=0 && edge<v->u.nRelations);
    p->LastEdge=edge;s->ModelValues=NULL;s->ModelOwner=NULL;
    if(Cec_TranStrictScorrStopped(p))goto finish;
    a=Cec_TranFrozenCnfEndpoint(s,frame,Vec_IntEntry(s->Pairs,2*edge));
    b=Cec_TranFrozenCnfEndpoint(s,frame,Vec_IntEntry(s->Pairs,2*edge+1));
    if(a==b){++p->StructuralQueries;goto finish;}
    ++v->cacheLookups;slot=Cec_TranLazySlot(v,frame,edge);
    if(v->Slots[slot]){++v->cacheHits;q=Vec_IntEntry(v->QueryLits,v->Slots[slot]-1);goto finish;}
    Cec_TranStrictScorrLoad(s,a);Cec_TranStrictScorrLoad(s,b);if(p->Aborted)goto finish;
    a=Cec_TranStrictScorrLit(p,a);b=Cec_TranStrictScorrLit(p,b);
    if(a==(b^1))q=1;
    else
    {
        CEC_BASIS_REQUIRE(sat_solver_nvars(v->u.pSat)<1073741823);
        q=Abc_Var2Lit(sat_solver_nvars(v->u.pSat),0);sat_solver_setnvars(v->u.pSat,sat_solver_nvars(v->u.pSat)+1);++v->queryVars;
        for(x=0;x<2;++x)for(y=0;y<2;++y)
        {c[0]=a^x;c[1]=b^y;c[2]=q^(1^x^y);Cec_TranFrozenCnfEmit(s,c,3,3,0);}
    }
    if(2*(Vec_IntSize(v->QueryFrames)+1)>v->nSlots){Cec_TranLazyGrow(v);slot=Cec_TranLazySlot(v,frame,edge);}
    Vec_IntPush(v->QueryFrames,frame);Vec_IntPush(v->QueryEdges,edge);Vec_IntPush(v->QueryLits,q);v->Slots[slot]=Vec_IntSize(v->QueryFrames);
finish:
    p->LastQuery=q;p->LoadTicks+=Abc_Clock()-clk;return q;
}

// ModelValues is a borrowed view of Values, exposed only after every check.
// All CI choices come from this compact solver, with unused CIs set to zero.
// Omitted internal nodes are evaluated, never read in the compact SAT domain.
static int Cec_TranStrictScorrModel(Cec_TranFrozenCnfSolver_t * s,int edge,int query)
{
    Cec_TranStrictScorr_t * p=(Cec_TranStrictScorr_t *)s->ResearchData;
    Gia_Man_t * g=s->Srm.Graph;Gia_Obj_t * o;
    int i,a,b,value,ok=0;abctime clk=Abc_Clock();p->Values[0]=0;
    Gia_ManForEachObj1(g,o,i)
    {
        if(!(i&4095) && Cec_TranStrictScorrStopped(p))goto finish;
        if(Gia_ObjIsCi(o))value=p->Vars[i]<0?0:Cec_TranLazyModelLit(s->View.u.pSat,Abc_Var2Lit(p->Vars[i],0));
        else
        {
            a=p->Values[Gia_ObjFaninId0p(g,o)]^Gia_ObjFaninC0(o);
            b=p->Values[Gia_ObjFaninId1p(g,o)]^Gia_ObjFaninC1(o);
            value=Gia_ObjIsXor(o)?a^b:a&b;
        }
        CEC_BASIS_REQUIRE(value==0 || value==1);p->Values[i]=(unsigned char)value;
        if(p->Vars[i]>=0)CEC_BASIS_REQUIRE(value==Cec_TranLazyModelLit(s->View.u.pSat,Abc_Var2Lit(p->Vars[i],0)));
    }
    for(i=0;i<s->Srm.EqualitiesKept;++i)
    {
        if(!(i&4095) && Cec_TranStrictScorrStopped(p))goto finish;
        a=Vec_IntEntry(s->Srm.Equalities,2*i);b=Vec_IntEntry(s->Srm.Equalities,2*i+1);++s->ResidualChecks;
        CEC_BASIS_REQUIRE((p->Values[Abc_Lit2Var(a)]^Abc_LitIsCompl(a))==(p->Values[Abc_Lit2Var(b)]^Abc_LitIsCompl(b)));
    }
    a=Cec_TranFrozenCnfEndpoint(s,s->Depth,Vec_IntEntry(s->Pairs,2*edge));
    b=Cec_TranFrozenCnfEndpoint(s,s->Depth,Vec_IntEntry(s->Pairs,2*edge+1));
    CEC_BASIS_REQUIRE((p->Values[Abc_Lit2Var(a)]^Abc_LitIsCompl(a))!=(p->Values[Abc_Lit2Var(b)]^Abc_LitIsCompl(b)));
    CEC_BASIS_REQUIRE(Cec_TranLazyModelLit(s->View.u.pSat,query)==1);
    s->ModelValues=p->Values;s->ModelOwner=s;++s->LiftedSat;ok=1;
finish:
    p->ModelTicks+=Abc_Clock()-clk;return ok;
}

static int Cec_TranStrictScorrSolve(Cec_TranFrozenCnfSolver_t * s,int edge,int query,int limit)
{
    Cec_TranStrictScorr_t * p=(Cec_TranStrictScorr_t *)s->ResearchData;
    long long used=0;int status;
    CEC_BASIS_REQUIRE(edge==p->LastEdge && query==p->LastQuery && limit>=0);
    s->ModelValues=NULL;s->ModelOwner=NULL;++p->Queries;++s->ActiveBins[5];
    if(Cec_TranStrictScorrStopped(p)){++s->BudgetStops;status=l_Undef;}
    else
    {
        CEC_BASIS_REQUIRE(s->ResidualActive==s->Srm.EqualitiesKept);
        status=Cec_TranFrozenLazyPhase(s,s,query,limit,&used,1);
        if(status==l_True && !Cec_TranStrictScorrModel(s,edge,query)){++s->BudgetStops;status=l_Undef;}
    }
    CEC_BASIS_REQUIRE(!limit || used<=limit);
    if(used>s->QueryConflictsMax)s->QueryConflictsMax=used;
    return status;
}

static void Cec_TranStrictScorrStop(Cec_TranFrozenCnfSolver_t * s)
{
    Cec_TranStrictScorr_t * p=(Cec_TranStrictScorr_t *)s->ResearchData;
    if(s->ResearchMode!=3 || !p)return;
    if(s->Profile)Abc_Print(1,"stran-strict-scorr: schema=1 call=%llu round=%d queries=%lld structural=%lld encoded-cis=%d encoded-gates=%d supergates=%lld super-leaves=%lld absorbed=%lld muxes=%lld xors=%lld wide-clauses=%lld residual-active=%d residual-total=%lld full-fallbacks=%lld load-stopped=%d index-sec=%.6f load-sec=%.6f model-sec=%.6f scope=%s\n",
        s->Call,s->Round,p->Queries,p->StructuralQueries,p->EncodedCis,p->EncodedGates,p->Supergates,p->SuperLeaves,p->Absorbed,p->Muxes,p->Xors,p->WideClauses,s->ResidualActive,s->Srm.EqualitiesKept,s->Fallbacks,p->Aborted,
        (double)p->IndexTicks/CLOCKS_PER_SEC,(double)p->LoadTicks/CLOCKS_PER_SEC,(double)p->ModelTicks/CLOCKS_PER_SEC,
        s->Template->OdcProofScope?"odc":"strict");
    ABC_FREE(p->Vars);ABC_FREE(p->Refs);ABC_FREE(p->Values);
    Vec_IntFree(p->Frontier);Vec_IntFree(p->Stack);Vec_IntFree(p->Fanins);Vec_IntFree(p->Clause);
    ABC_FREE(p);s->ResearchData=NULL;s->ModelValues=NULL;
}
