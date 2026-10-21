// Read-only structural potential of conditioning complete T/recipe CNF on
// exactly one Frozen H. This is not a SAT solver or an optimization. Query,
// old guard/disable and learned clauses are deliberately outside this count.
#include <limits.h>
typedef struct Cec_TranFrozenCnfClause_t_ {
    int Width, Lits[3];
} Cec_TranFrozenCnfClause_t;

typedef struct Cec_TranFrozenCnfProbe_t_ {
    int nVars, nClasses, nOriginalUsed, nQuotientUsed;
    int * Parent, * Size, * Parity, * Map;
    unsigned char * OriginalUsed, * QuotientUsed;
    Cec_TranFrozenCnfClause_t * Table;
    size_t Capacity, Bytes;
    long long Unions, Merges, Redundant, Contradictions;
    long long OriginalClauses, OriginalLiterals, Tautologies, Empty;
    long long LocalClauses, LocalLiterals, Duplicates, UniqueClauses, UniqueLiterals;
} Cec_TranFrozenCnfProbe_t;

static int Cec_TranFrozenCnfProbeOption(char const * Name)
{
    char const * s=getenv(Name);
    if(!s || !strcmp(s,"0"))return 0;
    if(!strcmp(s,"1"))return 1;
    Abc_Print(-1,"stran-quality-invalid-option: %s must be 0 or 1\n",Name);
    exit(2);return 0;
}

static Cec_TranFrozenCnfProbe_t Cec_TranFrozenCnfProbeStart(int nVars,size_t ClauseBound)
{
    Cec_TranFrozenCnfProbe_t s;
    size_t cap=8,arrays;int i;
    CEC_BASIS_REQUIRE(nVars>0 && nVars<=INT_MAX/2);
    CEC_BASIS_REQUIRE(ClauseBound>0 && ClauseBound<=(size_t)-1/2);
    while(cap<2*ClauseBound){CEC_BASIS_REQUIRE(cap<=(size_t)-1/2);cap*=2;}
    CEC_BASIS_REQUIRE(cap<=(size_t)-1/sizeof(Cec_TranFrozenCnfClause_t));
    CEC_BASIS_REQUIRE((size_t)nVars<=(size_t)-1/(4*sizeof(int)+2));
    arrays=(size_t)nVars*(4*sizeof(int)+2);
    CEC_BASIS_REQUIRE(arrays<=(size_t)-1-cap*sizeof(Cec_TranFrozenCnfClause_t));
    memset(&s,0,sizeof(s));s.nVars=nVars;s.Capacity=cap;
    s.Bytes=arrays+cap*sizeof(Cec_TranFrozenCnfClause_t);
    s.Parent=ABC_ALLOC(int,nVars);s.Size=ABC_ALLOC(int,nVars);
    s.Parity=ABC_CALLOC(int,nVars);s.Map=ABC_ALLOC(int,nVars);
    s.OriginalUsed=ABC_CALLOC(unsigned char,nVars);
    s.QuotientUsed=ABC_CALLOC(unsigned char,nVars);
    s.Table=ABC_CALLOC(Cec_TranFrozenCnfClause_t,cap);
    for(i=0;i<nVars;++i){s.Parent[i]=i;s.Size[i]=1;s.Map[i]=-1;}
    return s;
}

static int Cec_TranFrozenCnfProbeFind(Cec_TranFrozenCnfProbe_t * s,int v,int * sign)
{
    int root=v,parity=0,next,old;
    CEC_BASIS_REQUIRE(v>=0 && v<s->nVars);
    while(s->Parent[root]!=root){parity^=s->Parity[root];root=s->Parent[root];}
    *sign=parity;
    while(s->Parent[v]!=v)
    {
        next=s->Parent[v];old=s->Parity[v];
        s->Parent[v]=root;s->Parity[v]=parity;parity^=old;v=next;
    }
    return root;
}

static void Cec_TranFrozenCnfProbeUnion(Cec_TranFrozenCnfProbe_t * s,int a,int b)
{
    int pa,pb,ra=Cec_TranFrozenCnfProbeFind(s,Abc_Lit2Var(a),&pa);
    int rb=Cec_TranFrozenCnfProbeFind(s,Abc_Lit2Var(b),&pb),tmp;
    int parity=pa^pb^((a^b)&1);
    ++s->Unions;
    if(ra==rb){if(parity)++s->Contradictions;else ++s->Redundant;return;}
    if(s->Size[ra]<s->Size[rb]){tmp=ra;ra=rb;rb=tmp;}
    s->Parent[rb]=ra;s->Parity[rb]=parity;s->Size[ra]+=s->Size[rb];++s->Merges;
}

static void Cec_TranFrozenCnfProbeMap(Cec_TranFrozenCnfProbe_t * s)
{
    int i,sign,zeroSign,zero=Cec_TranFrozenCnfProbeFind(s,0,&zeroSign),root;
    // Map[root] temporarily holds a dense representative literal. The
    // constant class may have a nonzero UF root; normalize original var0=0.
    s->Map[zero]=zeroSign;s->nClasses=1;
    for(i=0;i<s->nVars;++i)
    {
        root=Cec_TranFrozenCnfProbeFind(s,i,&sign);
        if(s->Map[root]<0)s->Map[root]=Abc_Var2Lit(s->nClasses++,0);
    }
    // Roots retain parity zero, so their in-place conversion cannot corrupt
    // later members. The constant root's literal retains zeroSign as well.
    for(i=0;i<s->nVars;++i)
    {root=Cec_TranFrozenCnfProbeFind(s,i,&sign);s->Map[i]=s->Map[root]^sign;}
    CEC_BASIS_REQUIRE(s->Map[0]==0 && s->nClasses==s->nVars-s->Merges);
}

static void Cec_TranFrozenCnfProbeClause(Cec_TranFrozenCnfProbe_t * s,int * Lits,int Width,int ConstantUnit)
{
    int lits[3],i,j,n=0,x;unsigned hash=2166136261u;size_t slot;
    CEC_BASIS_REQUIRE(Width>=1 && Width<=3);
    ++s->OriginalClauses;s->OriginalLiterals+=Width;
    for(i=0;i<Width;++i)
    {
        int v=Abc_Lit2Var(Lits[i]);CEC_BASIS_REQUIRE(v<s->nVars);
        if(!s->OriginalUsed[v]){s->OriginalUsed[v]=1;++s->nOriginalUsed;}
        lits[i]=s->Map[v]^Abc_LitIsCompl(Lits[i]);
    }
    if(ConstantUnit){CEC_BASIS_REQUIRE(Width==1 && lits[0]==1);n=1;}
    else
    {
        for(i=1;i<Width;++i)
        {x=lits[i];for(j=i;j>0 && lits[j-1]>x;--j)lits[j]=lits[j-1];lits[j]=x;}
        for(i=0;i<Width;++i)
        {
            x=lits[i];
            if(x==1 || (n && x==(lits[n-1]^1))){++s->Tautologies;return;}
            if(x==0 || (n && x==lits[n-1]))continue;
            lits[n++]=x;
        }
        if(!n){++s->Empty;return;}
    }
    ++s->LocalClauses;s->LocalLiterals+=n;
    hash=(hash^(unsigned)n)*16777619u;
    for(i=0;i<n;++i)hash=(hash^(unsigned)lits[i])*16777619u;
    slot=(size_t)hash&(s->Capacity-1);
    while(s->Table[slot].Width)
    {
        if(s->Table[slot].Width==n && !memcmp(s->Table[slot].Lits,lits,n*sizeof(int)))
        {++s->Duplicates;return;}
        slot=(slot+1)&(s->Capacity-1);
    }
    s->Table[slot].Width=n;memcpy(s->Table[slot].Lits,lits,n*sizeof(int));
    ++s->UniqueClauses;s->UniqueLiterals+=n;
    for(i=0;i<n;++i)if(!s->QuotientUsed[Abc_Lit2Var(lits[i])])
    {s->QuotientUsed[Abc_Lit2Var(lits[i])]=1;++s->nQuotientUsed;}
}

static void Cec_TranFrozenCnfProbeEncode(Cec_TranFrozenCnfProbe_t * s,Gia_Man_t * p)
{
    Gia_Obj_t * o;int i,a,b,z,x,y,lits[3];
    CEC_BASIS_REQUIRE(Gia_ManObjNum(p)==s->nVars);
    lits[0]=1;Cec_TranFrozenCnfProbeClause(s,lits,1,1);
    // Exactly the same complete immutable gate definitions as LazyUnroll.
    // Do not rebuild a Gia from aliases: substitution can identify a gate
    // output with an earlier input without preserving DAG topology.
    Gia_ManForEachAnd(p,o,i)
    {
        a=Gia_ObjFaninLit0p(p,o);b=Gia_ObjFaninLit1p(p,o);z=Abc_Var2Lit(i,0);
        if(Gia_ObjIsXor(o))for(x=0;x<2;++x)for(y=0;y<2;++y)
        {lits[0]=a^x;lits[1]=b^y;lits[2]=z^(1^x^y);Cec_TranFrozenCnfProbeClause(s,lits,3,0);}
        else
        {
            lits[0]=z^1;lits[1]=a;Cec_TranFrozenCnfProbeClause(s,lits,2,0);
            lits[0]=z^1;lits[1]=b;Cec_TranFrozenCnfProbeClause(s,lits,2,0);
            lits[0]=z;lits[1]=a^1;lits[2]=b^1;Cec_TranFrozenCnfProbeClause(s,lits,3,0);
        }
    }
    CEC_BASIS_REQUIRE(s->OriginalClauses==s->Tautologies+s->Empty+s->LocalClauses);
    CEC_BASIS_REQUIRE(s->LocalClauses==s->Duplicates+s->UniqueClauses);
}

static void Cec_TranFrozenCnfProbeStop(Cec_TranFrozenCnfProbe_t * s)
{
    ABC_FREE(s->Parent);ABC_FREE(s->Size);ABC_FREE(s->Parity);ABC_FREE(s->Map);
    ABC_FREE(s->OriginalUsed);ABC_FREE(s->QuotientUsed);ABC_FREE(s->Table);
}

static void Cec_TranFrozenCnfQuotientProbe(Cec_TranRelLazy_t * lazy,Vec_Int_t * pairs,
    Vec_Int_t * FrozenEdges,int k,int round,int alive,unsigned long long call)
{
    Cec_TranFrozenCnfProbe_t s;int f,i,j,nKnown=0;long long hUnions,closedUnions=0;
    abctime start=Abc_Clock(),ufEnd,encodeEnd,stopEnd;
    CEC_BASIS_REQUIRE((size_t)Gia_ManAndNum(lazy->u.p)<=((size_t)-1-1)/4);
    s=Cec_TranFrozenCnfProbeStart(Gia_ManObjNum(lazy->u.p),1+4*(size_t)Gia_ManAndNum(lazy->u.p));
    for(f=0;f<k;++f)Vec_IntForEachEntry(FrozenEdges,i,j)
        Cec_TranFrozenCnfProbeUnion(&s,Cec_TranLazyEndpoint(lazy,f,Vec_IntEntry(pairs,2*i)),
            Cec_TranLazyEndpoint(lazy,f,Vec_IntEntry(pairs,2*i+1)));
    hUnions=s.Unions;
    if(Cec_TranRelClosedCurrent)
    {
        nKnown=Cec_TranRelClosedCurrent->nKnown;
        CEC_BASIS_REQUIRE(Cec_TranRelClosedCurrent->Frames==k);
        for(f=0;f<=k;++f)Vec_IntForEachEntry(Cec_TranRelClosedCurrent->KnownIds,i,j)
            Cec_TranFrozenCnfProbeUnion(&s,Cec_TranLazyEndpoint(lazy,f,Vec_IntEntry(pairs,2*i)),
                Cec_TranLazyEndpoint(lazy,f,Vec_IntEntry(pairs,2*i+1)));
        closedUnions=s.Unions-hUnions;
    }
    Cec_TranFrozenCnfProbeMap(&s);ufEnd=Abc_Clock();
    Cec_TranFrozenCnfProbeEncode(&s,lazy->u.p);encodeEnd=Abc_Clock();
    CEC_BASIS_REQUIRE(s.nVars==lazy->nTransitionVars && s.OriginalClauses==lazy->transitionAttempted);
    Cec_TranFrozenCnfProbeStop(&s);stopEnd=Abc_Clock();
    Abc_Print(1,"stran-frozen-cnf-quotient-probe: schema=1 purpose=DIAGNOSTIC_NOT_OPTIMIZATION scope=transition-recipe-only excluded=query-guard-disable-learned condition=%s call=%llu round=%d depth=%d relations=%d alive=%d frozen-edges=%d known=%d h-unions=%lld closed-unions=%lld merges=%lld redundant=%lld contradictions=%lld original-vars=%d quotient-classes=%d original-occurring-vars=%d quotient-occurring-vars=%d original-clauses=%lld original-literals=%lld tautologies=%lld empty=%lld local-clauses=%lld local-literals=%lld duplicate-clauses=%lld quotient-clauses=%lld quotient-literals=%lld owned-heap-bytes=%llu query-records=%d query-vars=%d current-sat-vars=%d current-sat-clauses=%d uf-map-sec=%.6f encode-sec=%.6f free-sec=%.6f total-sec=%.6f\n",
        s.Contradictions||s.Empty?"INCONSISTENT":"NOT_CHECKED",call,round,k,lazy->u.nRelations,alive,Vec_IntSize(FrozenEdges),nKnown,hUnions,closedUnions,s.Merges,s.Redundant,s.Contradictions,
        s.nVars,s.nClasses,s.nOriginalUsed,s.nQuotientUsed,s.OriginalClauses,s.OriginalLiterals,s.Tautologies,s.Empty,
        s.LocalClauses,s.LocalLiterals,s.Duplicates,s.UniqueClauses,s.UniqueLiterals,(unsigned long long)s.Bytes,
        Vec_IntSize(lazy->QueryFrames),lazy->queryVars,sat_solver_nvars(lazy->u.pSat),sat_solver_nclauses(lazy->u.pSat),
        (double)(ufEnd-start)/CLOCKS_PER_SEC,(double)(encodeEnd-ufEnd)/CLOCKS_PER_SEC,
        (double)(stopEnd-encodeEnd)/CLOCKS_PER_SEC,(double)(stopEnd-start)/CLOCKS_PER_SEC);
    fflush(stdout);
}

// Independent truth evaluation for a tiny real unrolled graph. Iterate dense
// assignments, lift every original value, and compare original gate equations
// with the exact emitted clause table; no SAT solver is queried here.
// Independent UF oracle: enumerate ORIGINAL assignments and evaluate the
// requested signed equalities without Find/Union. A valuation is representable
// by Map iff every member of each dense class agrees, with dense0 fixed false.
