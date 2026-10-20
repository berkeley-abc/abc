// A solver belongs to exactly one Frozen H. The original Gia/Maps are borrowed;
// query literals, clauses, learned clauses and dense IDs never cross a round.
#include "cecTranFrozenSrm.h"
typedef struct Cec_TranFrozenCnfKind_t_ {
    long long Attempted, Unique, Stored, Tautologies, Duplicates, Empty;
    long long LiteralsIn, LiteralsUnique;
} Cec_TranFrozenCnfKind_t;
typedef struct Cec_TranFrozenCnfSolver_t_ {
    Cec_TranRelLazy_t View, * Template;
    Cec_TranFrozenCnfProbe_t Map;
    Cec_TranFrozenSrm_t Srm;
    Cec_TranFrozenCnfKind_t Kind[5]; // T, J, H, query, residual SRM equality
    Vec_Int_t * Pairs, * FrozenEdges;
    struct Cec_TranFrozenCnfSolver_t_ * Full, * ModelOwner;
    unsigned char * ResidualLoaded;
    int LazyMode, ResidualActive;
    int ResearchMode;
    void * ResearchData; // Backend-owned state; never shared across Frozen H.
    unsigned char * ModelValues; // Borrowed complete SRM values, validated before SAT escapes.
    long long FastResults[3], FullResults[3], ActiveBins[6], SaturatedAt[4];
    long long Refinements, ResidualChecks, LiftedSat, Fallbacks, BudgetStops, QueryConflictsMax;
    abctime FastTicks[3], FullTicks[3], FullSetupTicks, ResidualTicks, ReplayTicks;
    int Mode, Profile, Oracle, Round, Depth, AliveBefore, Known, Guard, ReferenceGuard;
    int Inconsistent, VarsBefore, ClausesBefore, LearnedBefore;
    unsigned long long Call;
    long long HEquations, JEquations, Requests, SolverCalls, ConditionedUnsat;
    long long Sat, Unsat, Unknown, Models, Replays, Gates, HChecks, JChecks, QChecks;
    long long OracleCalls, OracleChecks;
    abctime Started, SetupTicks, UfTicks, GraphTicks, EncodeTicks, SolveTicks, OracleTicks;
} Cec_TranFrozenCnfSolver_t;

// Ordinary SSW encoding is the default. Explicit zero preserves the historical
// path; one changes only the conflict boundary to exact cumulative C.
static int Cec_TranStrictResearchTestMode=-1;
static int Cec_TranStrictResearchOption()
{
    char const * s=getenv("ABC_SRESUB_STRICT_BACKEND");
    if(Cec_TranStrictResearchTestMode>=0)return Cec_TranStrictResearchTestMode;
    if(!s)return 3;
    if(!strcmp(s,"0"))return 0;
    if(!strcmp(s,"1"))return 1;
    if(!strcmp(s,"2"))return 2;
    if(!strcmp(s,"3"))return 3;
    if(!strcmp(s,"4"))return 4;
    Abc_Print(-1,"stran-quality-invalid-option: ABC_SRESUB_STRICT_BACKEND must be 0 through 4\n");
    exit(2);return 0;
}

// ODC uses the same constrained SRM and model replay, but an independent
// encoder switch. Zero preserves its full CNF; one is the exact-budget
// control; default three uses ordinary SSW's compact cone/supergate/MUX encoding.
static int Cec_TranOdcResearchTestMode=-1;
static long long Cec_TranOdcResearchTestStarts=0;
static int Cec_TranOdcResearchOption()
{
    char const * s=getenv("ABC_SRESUB_ODC_BACKEND");
    if(Cec_TranOdcResearchTestMode>=0)return Cec_TranOdcResearchTestMode;
    if(!s)return 3;
    if(!strcmp(s,"0"))return 0;
    if(!strcmp(s,"1"))return 1;
    if(!strcmp(s,"3"))return 3;
    Abc_Print(-1,"stran-quality-invalid-option: ABC_SRESUB_ODC_BACKEND must be 0, 1 or 3\n");
    exit(2);return 0;
}

static int Cec_TranFrozenCnfLazyOption()
{
    char const * s=getenv("ABC_SRESUB_SRM_LAZY");
    if(!s || !strcmp(s,"0"))return 0;
    if(!strcmp(s,"1"))return 1;
    if(!strcmp(s,"2"))return 2;
    Abc_Print(-1,"stran-quality-invalid-option: ABC_SRESUB_SRM_LAZY must be 0, 1 or 2\n");
    exit(2);return 0;
}

static int Cec_TranFrozenCnfSolverTestMode=-1;
static int Cec_TranFrozenCnfSolverOption()
{
    char const * s=getenv("ABC_STRAN_FROZEN_CNF_SOLVER");
    if(Cec_TranFrozenCnfSolverTestMode>=0)return Cec_TranFrozenCnfSolverTestMode;
    if(!s)return 3; // Route3 Strict selects this; ODC has its own option.
    if(!strcmp(s,"0"))return 0;
    if(!strcmp(s,"1"))return 1;
    if(!strcmp(s,"2"))return 2;
    if(!strcmp(s,"3"))return 3;
    Abc_Print(-1,"stran-quality-invalid-option: ABC_STRAN_FROZEN_CNF_SOLVER must be 0, 1, 2 or 3\n");
    exit(2);return 0;
}

static unsigned Cec_TranFrozenCnfHash(int * lits,int width)
{
    unsigned hash=(2166136261u^(unsigned)width)*16777619u;int i;
    for(i=0;i<width;++i)hash=(hash^(unsigned)lits[i])*16777619u;
    return hash;
}

static void Cec_TranFrozenCnfGrow(Cec_TranFrozenCnfProbe_t * s)
{
    Cec_TranFrozenCnfClause_t * old=s->Table;size_t oldCap=s->Capacity,i,slot;
    CEC_BASIS_REQUIRE(oldCap<=(size_t)-1/(2*sizeof(*old)));
    s->Capacity*=2;s->Table=ABC_CALLOC(Cec_TranFrozenCnfClause_t,s->Capacity);
    for(i=0;i<oldCap;++i)if(old[i].Width)
    {
        slot=(size_t)Cec_TranFrozenCnfHash(old[i].Lits,old[i].Width)&(s->Capacity-1);
        while(s->Table[slot].Width)slot=(slot+1)&(s->Capacity-1);
        s->Table[slot]=old[i];
    }
    ABC_FREE(old);
}

// Input is already in THIS solver's literal domain. First occurrence is
// inserted immediately, in original gate/clause order; hash is only an index.
static void Cec_TranFrozenCnfEmit(Cec_TranFrozenCnfSolver_t * s,int * input,int width,int kind,int constantUnit)
{
    Cec_TranFrozenCnfKind_t * c=&s->Kind[kind];
    int lits[3],i,j,n=0,x,before,ok;size_t slot;
    CEC_BASIS_REQUIRE(kind>=0 && kind<5 && width>0 && width<=3);
    ++c->Attempted;c->LiteralsIn+=width;memcpy(lits,input,width*sizeof(int));
    if(constantUnit){CEC_BASIS_REQUIRE(width==1 && lits[0]==1);n=1;}
    else
    {
        for(i=1;i<width;++i)
        {x=lits[i];for(j=i;j>0 && lits[j-1]>x;--j)lits[j]=lits[j-1];lits[j]=x;}
        for(i=0;i<width;++i)
        {
            x=lits[i];
            if(x==1 || (n && x==(lits[n-1]^1))){++c->Tautologies;return;}
            if(!x || (n && x==lits[n-1]))continue;
            lits[n++]=x;
        }
        if(!n){++c->Empty;s->Inconsistent=1;return;}
    }
    if(2*(size_t)(s->Map.UniqueClauses+1)>s->Map.Capacity)Cec_TranFrozenCnfGrow(&s->Map);
    slot=(size_t)Cec_TranFrozenCnfHash(lits,n)&(s->Map.Capacity-1);
    while(s->Map.Table[slot].Width)
    {
        if(s->Map.Table[slot].Width==n && !memcmp(s->Map.Table[slot].Lits,lits,n*sizeof(int)))
        {++c->Duplicates;return;}
        slot=(slot+1)&(s->Map.Capacity-1);
    }
    s->Map.Table[slot].Width=n;memcpy(s->Map.Table[slot].Lits,lits,n*sizeof(int));
    ++s->Map.UniqueClauses;++c->Unique;c->LiteralsUnique+=n;
    if(s->Inconsistent)return;
    before=sat_solver_nclauses(s->View.u.pSat);
    ok=sat_solver_addclause(s->View.u.pSat,lits,lits+n);
    c->Stored+=sat_solver_nclauses(s->View.u.pSat)-before;
    if(!ok)s->Inconsistent=1; // Never pass an empty clause to BSAT's old API.
}

static int Cec_TranFrozenCnfMapLit(Cec_TranFrozenCnfSolver_t * s,int originalLit)
{
    int id=Abc_Lit2Var(originalLit);
    CEC_BASIS_REQUIRE(id>=0 && id<s->Map.nVars);
    return s->Map.Map[id]^Abc_LitIsCompl(originalLit);
}
static int Cec_TranFrozenCnfEndpoint(Cec_TranFrozenCnfSolver_t * s,int frame,int lit)
{return Cec_TranFrozenCnfMapLit(s,Cec_TranLazyEndpoint(s->Template,frame,lit));}

static void Cec_TranFrozenCnfEncode(Cec_TranFrozenCnfSolver_t * s)
{
    Gia_Man_t * p=s->Mode==3?s->Srm.Graph:s->Template->u.p;Gia_Obj_t * o;
    int i,a,b,z,x,y,c[3];long long attempted=1;
    c[0]=1;Cec_TranFrozenCnfEmit(s,c,1,0,1);
    Gia_ManForEachAnd(p,o,i)
    {
        a=Gia_ObjFaninLit0p(p,o);b=Gia_ObjFaninLit1p(p,o);z=Abc_Var2Lit(i,0);
        if(s->Mode!=3)
        {a=Cec_TranFrozenCnfMapLit(s,a);b=Cec_TranFrozenCnfMapLit(s,b);z=Cec_TranFrozenCnfMapLit(s,z);}
        attempted+=Gia_ObjIsXor(o)?4:3;
        if(Gia_ObjIsXor(o))for(x=0;x<2;++x)for(y=0;y<2;++y)
        {c[0]=a^x;c[1]=b^y;c[2]=z^(1^x^y);Cec_TranFrozenCnfEmit(s,c,3,0,0);}
        else
        {
            c[0]=z^1;c[1]=a;Cec_TranFrozenCnfEmit(s,c,2,0,0);
            c[0]=z^1;c[1]=b;Cec_TranFrozenCnfEmit(s,c,2,0,0);
            c[0]=z;c[1]=a^1;c[2]=b^1;Cec_TranFrozenCnfEmit(s,c,3,0,0);
        }
    }
    CEC_BASIS_REQUIRE(s->Kind[0].Attempted==attempted);
    if(s->Mode!=3){CEC_BASIS_REQUIRE(attempted==s->Template->transitionAttempted);return;}
    if(s->LazyMode)return;
    for(i=0;i<Vec_IntSize(s->Srm.Equalities);i+=2)
    {
        a=Vec_IntEntry(s->Srm.Equalities,i);b=Vec_IntEntry(s->Srm.Equalities,i+1);
        c[0]=a^1;c[1]=b;Cec_TranFrozenCnfEmit(s,c,2,4,0);
        c[0]=a;c[1]=b^1;Cec_TranFrozenCnfEmit(s,c,2,4,0);
    }
}

static void Cec_TranFrozenCnfEquality(Cec_TranFrozenCnfSolver_t * s,int frame,int edge,int kind)
{
    int a=Cec_TranFrozenCnfEndpoint(s,frame,Vec_IntEntry(s->Pairs,2*edge));
    int b=Cec_TranFrozenCnfEndpoint(s,frame,Vec_IntEntry(s->Pairs,2*edge+1)),c[3];
    if(kind==1)
    {
        c[0]=a^1;c[1]=b;Cec_TranFrozenCnfEmit(s,c,2,1,0);
        c[0]=a;c[1]=b^1;Cec_TranFrozenCnfEmit(s,c,2,1,0);
    }
    else
    {
        c[0]=s->Guard^1;c[1]=a^1;c[2]=b;Cec_TranFrozenCnfEmit(s,c,3,2,0);
        c[0]=s->Guard^1;c[1]=a;c[2]=b^1;Cec_TranFrozenCnfEmit(s,c,3,2,0);
    }
}

static void Cec_TranStrictLocalStart(Cec_TranFrozenCnfSolver_t * s);
static int Cec_TranStrictLocalQuery(Cec_TranFrozenCnfSolver_t * s,int frame,int edge);
static int Cec_TranStrictLocalSolve(Cec_TranFrozenCnfSolver_t * s,int edge,int query,int limit);
static void Cec_TranStrictLocalStop(Cec_TranFrozenCnfSolver_t * s);
static void Cec_TranStrictScorrStart(Cec_TranFrozenCnfSolver_t * s);
static int Cec_TranStrictScorrQuery(Cec_TranFrozenCnfSolver_t * s,int frame,int edge);
static int Cec_TranStrictScorrSolve(Cec_TranFrozenCnfSolver_t * s,int edge,int query,int limit);
static void Cec_TranStrictScorrStop(Cec_TranFrozenCnfSolver_t * s);

static Cec_TranFrozenCnfSolver_t * Cec_TranFrozenCnfStart(Cec_TranRelLazy_t * original,
    Vec_Int_t * pairs,Vec_Int_t * edges,int k,int round,int alive,int mode,int profile,int oracle,unsigned long long call)
{
    Cec_TranFrozenCnfSolver_t * s=ABC_CALLOC(Cec_TranFrozenCnfSolver_t,1);
    int f,i,j;abctime clk;
    s->Started=Abc_Clock();s->Template=original;s->Pairs=pairs;s->FrozenEdges=edges;
    s->Mode=mode;s->Profile=profile;s->Oracle=oracle;s->Depth=k;s->Round=round;s->AliveBefore=alive;s->Call=call;
    s->LazyMode=mode==3?Cec_TranFrozenCnfLazyOption():0;
    s->ResearchMode=mode==3?(original->OdcProofScope?Cec_TranOdcResearchOption():Cec_TranStrictResearchOption()):0;
    if(original->OdcProofScope && Cec_TranOdcResearchTestMode>=0)++Cec_TranOdcResearchTestStarts;
    if(s->ResearchMode && s->LazyMode)
    {
        Abc_Print(-1,"stran-quality-invalid-option: research backend requires ABC_SRESUB_SRM_LAZY=0\n");
        exit(2);
    }
    CEC_BASIS_REQUIRE(mode>=1 && mode<=3);
    // LazyUnroll aliases source CO/BUF in Maps; its immutable T has only CI/gates.
    CEC_BASIS_REQUIRE(Gia_ManObjNum(original->u.p)==1+Gia_ManCiNum(original->u.p)+Gia_ManAndNum(original->u.p));
    CEC_BASIS_REQUIRE(original->nTransitionVars==Gia_ManObjNum(original->u.p));
    CEC_BASIS_REQUIRE((size_t)Gia_ManAndNum(original->u.p)<=((size_t)-1-1)/4);
    s->Map=Cec_TranFrozenCnfProbeStart(Gia_ManObjNum(original->u.p),1+4*(size_t)Gia_ManAndNum(original->u.p));
    if(Cec_TranRelClosedCurrent)s->Known=Cec_TranRelClosedCurrent->nKnown;
    s->HEquations=(long long)k*Vec_IntSize(edges);s->JEquations=(long long)(k+1)*s->Known;
    if(mode>=2)
    {
        for(f=0;f<k;++f)Vec_IntForEachEntry(edges,i,j)
            Cec_TranFrozenCnfProbeUnion(&s->Map,Cec_TranLazyEndpoint(original,f,Vec_IntEntry(pairs,2*i)),Cec_TranLazyEndpoint(original,f,Vec_IntEntry(pairs,2*i+1)));
        if(s->Known)for(f=0;f<=k;++f)Vec_IntForEachEntry(Cec_TranRelClosedCurrent->KnownIds,i,j)
            Cec_TranFrozenCnfProbeUnion(&s->Map,Cec_TranLazyEndpoint(original,f,Vec_IntEntry(pairs,2*i)),Cec_TranLazyEndpoint(original,f,Vec_IntEntry(pairs,2*i+1)));
    }
    Cec_TranFrozenCnfProbeMap(&s->Map);s->Inconsistent=s->Map.Contradictions!=0;
    s->UfTicks=Abc_Clock()-s->Started;
    if(mode==3)
    {clk=Abc_Clock();s->Srm=Cec_TranFrozenSrmBuild(original->u.p,&s->Map);s->GraphTicks=Abc_Clock()-clk;}
    if(s->LazyMode)s->ResidualLoaded=ABC_CALLOC(unsigned char,s->Srm.EqualitiesKept);
    s->View=*original; // Borrow original Gia/Maps; replace EVERY owned SAT/cache field.
    clk=Abc_Clock();
    s->View.u.pSat=sat_solver_new();
    sat_solver_setnvars(s->View.u.pSat,s->ResearchMode>=2?1:mode==3?s->Srm.Objects:s->Map.nClasses);
    s->View.QueryFrames=Vec_IntAlloc(128);s->View.QueryEdges=Vec_IntAlloc(128);s->View.QueryLits=Vec_IntAlloc(128);
    s->View.nSlots=256;s->View.Slots=ABC_CALLOC(int,256);s->View.queryVars=0;
    s->View.cacheLookups=s->View.cacheHits=0;
    if(s->ResearchMode==2 || s->ResearchMode==4)Cec_TranStrictLocalStart(s);
    else if(s->ResearchMode==3)Cec_TranStrictScorrStart(s);
    else
    {
        Cec_TranFrozenCnfEncode(s);
        if(s->Known)for(f=0;f<=k;++f)Vec_IntForEachEntry(Cec_TranRelClosedCurrent->KnownIds,i,j)Cec_TranFrozenCnfEquality(s,f,i,1);
        CEC_BASIS_REQUIRE(sat_solver_nvars(s->View.u.pSat)<1073741823);
        s->Guard=Abc_Var2Lit(sat_solver_nvars(s->View.u.pSat),0);
        sat_solver_setnvars(s->View.u.pSat,sat_solver_nvars(s->View.u.pSat)+1);
        for(f=0;f<k;++f)Vec_IntForEachEntry(edges,i,j)Cec_TranFrozenCnfEquality(s,f,i,2);
    }
    s->VarsBefore=sat_solver_nvars(s->View.u.pSat);s->ClausesBefore=sat_solver_nclauses(s->View.u.pSat);
    s->LearnedBefore=(int)s->View.u.pSat->stats.learnts;
    s->EncodeTicks=Abc_Clock()-clk;
    s->SetupTicks=Abc_Clock()-s->Started;
    if(oracle)
    {
        abctime clk=Abc_Clock();
        CEC_BASIS_REQUIRE(sat_solver_nvars(original->u.pSat)<1073741823);
        s->ReferenceGuard=Abc_Var2Lit(sat_solver_nvars(original->u.pSat),0);
        sat_solver_setnvars(original->u.pSat,sat_solver_nvars(original->u.pSat)+1);
        for(f=0;f<k;++f)Vec_IntForEachEntry(edges,i,j)Cec_TranLazyGuard(original,pairs,f,i,s->ReferenceGuard);
        s->OracleTicks+=Abc_Clock()-clk;
    }
    return s;
}

static int Cec_TranFrozenCnfQuery(Cec_TranFrozenCnfSolver_t * s,int frame,int edge)
{
    Cec_TranRelLazy_t * v=&s->View;int slot,a,b,q,x,y,c[3];
    if(s->ResearchMode==2 || s->ResearchMode==4)return Cec_TranStrictLocalQuery(s,frame,edge);
    if(s->ResearchMode==3)return Cec_TranStrictScorrQuery(s,frame,edge);
    ++v->cacheLookups;slot=Cec_TranLazySlot(v,frame,edge);
    if(v->Slots[slot]){++v->cacheHits;return Vec_IntEntry(v->QueryLits,v->Slots[slot]-1);}
    if(2*(Vec_IntSize(v->QueryFrames)+1)>v->nSlots){Cec_TranLazyGrow(v);slot=Cec_TranLazySlot(v,frame,edge);}
    a=Cec_TranFrozenCnfEndpoint(s,frame,Vec_IntEntry(s->Pairs,2*edge));
    b=Cec_TranFrozenCnfEndpoint(s,frame,Vec_IntEntry(s->Pairs,2*edge+1));
    if(a==b)q=0;else if(a==(b^1))q=1;
    else
    {
        CEC_BASIS_REQUIRE(sat_solver_nvars(v->u.pSat)<1073741823);
        q=Abc_Var2Lit(sat_solver_nvars(v->u.pSat),0);
        sat_solver_setnvars(v->u.pSat,sat_solver_nvars(v->u.pSat)+1);++v->queryVars;
        for(x=0;x<2;++x)for(y=0;y<2;++y)
        {c[0]=a^x;c[1]=b^y;c[2]=q^(1^x^y);Cec_TranFrozenCnfEmit(s,c,3,3,0);}
    }
    Vec_IntPush(v->QueryFrames,frame);Vec_IntPush(v->QueryEdges,edge);Vec_IntPush(v->QueryLits,q);
    v->Slots[slot]=Vec_IntSize(v->QueryFrames);return q;
}

static void Cec_TranFrozenCnfCheckReference(Cec_TranFrozenCnfSolver_t * s,int pivot,int query)
{
    long long visits=0;int * values=Cec_TranActiveScalar(s->Template,&visits);
    int i,j,f,a,b;
    CEC_BASIS_REQUIRE(Cec_TranLazyModelLit(s->Template->u.pSat,s->ReferenceGuard)==1);
    CEC_BASIS_REQUIRE(Cec_TranLazyModelLit(s->Template->u.pSat,query)==1);
    for(i=0;i<Gia_ManObjNum(s->Template->u.p);++i)CEC_BASIS_REQUIRE(values[i]>=0);
    for(f=0;f<s->Depth;++f)Vec_IntForEachEntry(s->FrozenEdges,i,j)
    {
        a=Cec_TranActiveValue(values,Cec_TranLazyEndpoint(s->Template,f,Vec_IntEntry(s->Pairs,2*i)));
        b=Cec_TranActiveValue(values,Cec_TranLazyEndpoint(s->Template,f,Vec_IntEntry(s->Pairs,2*i+1)));
        CEC_BASIS_REQUIRE(a==b);
    }
    if(s->Known)for(f=0;f<=s->Depth;++f)Vec_IntForEachEntry(Cec_TranRelClosedCurrent->KnownIds,i,j)
    {
        a=Cec_TranActiveValue(values,Cec_TranLazyEndpoint(s->Template,f,Vec_IntEntry(s->Pairs,2*i)));
        b=Cec_TranActiveValue(values,Cec_TranLazyEndpoint(s->Template,f,Vec_IntEntry(s->Pairs,2*i+1)));
        CEC_BASIS_REQUIRE(a==b);
    }
    a=Cec_TranActiveValue(values,Cec_TranLazyEndpoint(s->Template,s->Depth,Vec_IntEntry(s->Pairs,2*pivot)));
    b=Cec_TranActiveValue(values,Cec_TranLazyEndpoint(s->Template,s->Depth,Vec_IntEntry(s->Pairs,2*pivot+1)));
    CEC_BASIS_REQUIRE(a!=b);ABC_FREE(values);
}

#include "cecTranFrozenLazyResidual.h"
#include "cecTranStrictLocal.h"
#include "cecTranStrictScorr.h"

static int Cec_TranFrozenCnfSolve(Cec_TranFrozenCnfSolver_t * s,int edge,int query,int limit)
{
    int assumptions[2],status,reference;
    ++s->Requests;
    assumptions[0]=s->Guard;assumptions[1]=query;
    if(s->ResearchMode==2 || s->ResearchMode==4)status=Cec_TranStrictLocalSolve(s,edge,query,limit);
    else if(s->ResearchMode==3)status=Cec_TranStrictScorrSolve(s,edge,query,limit);
    else if(s->Inconsistent){++s->ConditionedUnsat;status=l_False;}
    else if(s->ResearchMode==1)
    {
        long long used=0;
        s->ModelOwner=NULL;++s->ActiveBins[5];
        status=Cec_TranFrozenLazyPhase(s,s,query,limit,&used,1);
        if(status==l_True)s->ModelOwner=s;
        if(used>s->QueryConflictsMax)s->QueryConflictsMax=used;
    }
    else if(s->LazyMode)status=Cec_TranFrozenLazySolve(s,edge,query,limit);
    else
    {
        abctime clk=Abc_Clock(),elapsed;long long before=s->View.u.pSat->stats.conflicts,used;
        ++s->SolverCalls;
        status=sat_solver_solve(s->View.u.pSat,assumptions,assumptions+2,limit,0,0,0);
        elapsed=Abc_Clock()-clk;s->SolveTicks+=elapsed;
        ++s->FullResults[status+1];s->FullTicks[status+1]+=elapsed;++s->ActiveBins[5];
        used=s->View.u.pSat->stats.conflicts-before;
        if(used>s->QueryConflictsMax)s->QueryConflictsMax=used;
    }
    if(status==l_True)++s->Sat;else if(status==l_False)++s->Unsat;else {CEC_BASIS_REQUIRE(status==l_Undef);++s->Unknown;}
    if(s->Oracle)
    {
        abctime clk=Abc_Clock();
        CEC_BASIS_REQUIRE(sat_solver_nvars(s->Template->u.pSat)<1073741823);
        assumptions[0]=s->ReferenceGuard;assumptions[1]=Cec_TranLazyQuery(s->Template,s->Pairs,s->Depth,edge);
        reference=sat_solver_solve(s->Template->u.pSat,assumptions,assumptions+2,0,0,0,0);++s->OracleCalls;
        CEC_BASIS_REQUIRE(reference==l_False || reference==l_True);
        if(reference==l_True)Cec_TranFrozenCnfCheckReference(s,edge,assumptions[1]);
        if(status!=l_Undef){CEC_BASIS_REQUIRE(status==reference);++s->OracleChecks;}
        s->OracleTicks+=Abc_Clock()-clk;
    }
    return status;
}

// Original-Gia literal accessor. Query/guard literals use LazyModelLit directly
// and must never pass through this map a second time.
static int Cec_TranFrozenCnfModelOriginal(Cec_TranFrozenCnfSolver_t * s,int lit)
{
    Cec_TranFrozenCnfSolver_t * model=s->ModelOwner?s->ModelOwner:s;
    int mapped=Cec_TranFrozenCnfMapLit(s,lit);
    if(model->ModelValues)return model->ModelValues[Abc_Lit2Var(mapped)]^Abc_LitIsCompl(mapped);
    return Cec_TranLazyModelLit(model->View.u.pSat,mapped);
}

static Vec_Int_t * Cec_TranFrozenCnfReplay(Cec_TranFrozenCnfSolver_t * s,Vec_Int_t * scope,
    Cec_TranRelActive_t * active,int pivot,long long * gateChecks,long long * relationChecks)
{
    Cec_TranFrozenCnfSolver_t * model=s->ModelOwner?s->ModelOwner:s;
    abctime started=Abc_Clock();
    Gia_Man_t * p=s->Template->u.p;Gia_Obj_t * o;
    int * values=ABC_FALLOC(int,Gia_ManObjNum(p));Vec_Int_t * bad=Vec_IntAlloc(0);
    int i,j,f,a,b,q,write=0;long long gates=0,hChecks=0,jChecks=0,targets=0;
    ++s->Models;values[0]=0;CEC_BASIS_REQUIRE(Cec_TranFrozenCnfModelOriginal(s,0)==0);
    CEC_BASIS_REQUIRE(Cec_TranLazyModelLit(model->View.u.pSat,model->Guard)==1);
    Gia_ManForEachObj1(p,o,i)
    {
        if(Gia_ObjIsCi(o))values[i]=Cec_TranFrozenCnfModelOriginal(s,Abc_Var2Lit(i,0));
        else
        {
            a=Cec_TranActiveValue(values,Gia_ObjFaninLit0p(p,o));
            if(Gia_ObjIsCo(o)||Gia_ObjIsBuf(o))values[i]=a;
            else
            {
                b=Cec_TranActiveValue(values,Gia_ObjFaninLit1p(p,o));
                values[i]=Gia_ObjIsXor(o)?(a<0||b<0?-1:a^b):(a==0||b==0?0:a<0||b<0?-1:1);
            }
        }
        CEC_BASIS_REQUIRE(values[i]>=0 && values[i]==Cec_TranFrozenCnfModelOriginal(s,Abc_Var2Lit(i,0)));++gates;
    }
    for(f=0;f<s->Depth;++f)Vec_IntForEachEntry(s->FrozenEdges,i,j)
    {
        a=Cec_TranActiveValue(values,Cec_TranLazyEndpoint(s->Template,f,Vec_IntEntry(s->Pairs,2*i)));
        b=Cec_TranActiveValue(values,Cec_TranLazyEndpoint(s->Template,f,Vec_IntEntry(s->Pairs,2*i+1)));
        CEC_BASIS_REQUIRE(a>=0 && b>=0 && a==b);++hChecks;
    }
    if(s->Known)for(f=0;f<=s->Depth;++f)Vec_IntForEachEntry(Cec_TranRelClosedCurrent->KnownIds,i,j)
    {
        a=Cec_TranActiveValue(values,Cec_TranLazyEndpoint(s->Template,f,Vec_IntEntry(s->Pairs,2*i)));
        b=Cec_TranActiveValue(values,Cec_TranLazyEndpoint(s->Template,f,Vec_IntEntry(s->Pairs,2*i+1)));
        CEC_BASIS_REQUIRE(a>=0 && b>=0 && a==b);++jChecks;
    }
    Vec_IntForEachEntry(active->Ids,i,j)
    {
        CEC_BASIS_REQUIRE(Vec_IntEntry(scope,i));
        a=Cec_TranActiveValue(values,Cec_TranLazyEndpoint(s->Template,s->Depth,Vec_IntEntry(s->Pairs,2*i)));
        b=Cec_TranActiveValue(values,Cec_TranLazyEndpoint(s->Template,s->Depth,Vec_IntEntry(s->Pairs,2*i+1)));
        CEC_BASIS_REQUIRE(a>=0 && b>=0);++targets;
        if(a!=b)Vec_IntPush(bad,i);
    }
    i=Cec_TranLazySlot(&model->View,s->Depth,pivot);CEC_BASIS_REQUIRE(model->View.Slots[i]>0);
    q=Vec_IntEntry(model->View.QueryLits,model->View.Slots[i]-1);
    CEC_BASIS_REQUIRE(Cec_TranLazyModelLit(model->View.u.pSat,q)==1 && Vec_IntFind(bad,pivot)>=0);
    // Commit stable compaction only after the entire original model/H/J/query
    // has been verified. This never consumes the reference oracle's model.
    if(active->fused)
    {
        int bpos=0;
        Vec_IntForEachEntry(active->Ids,i,j)
            if(bpos<Vec_IntSize(bad) && i==Vec_IntEntry(bad,bpos))++bpos;
            else Vec_IntWriteEntry(active->Ids,write++,i);
        CEC_BASIS_REQUIRE(bpos==Vec_IntSize(bad));Vec_IntShrink(active->Ids,write);
    }
    ++s->Replays;s->Gates+=gates;s->HChecks+=hChecks;s->JChecks+=jChecks;++s->QChecks;
    active->transitionVisits+=gates;active->frozenVisits+=hChecks;active->targetVisits+=targets;
    active->denseReplayOpportunities+=(long long)s->View.u.nFrames*s->View.u.nRelations;
    *gateChecks+=gates+1;*relationChecks+=hChecks+jChecks+targets;
    s->ReplayTicks+=Abc_Clock()-started;ABC_FREE(values);return bad;
}

static void Cec_TranFrozenCnfTemplateProfile(Cec_TranRelLazy_t * s,char const * stage,unsigned long long call,int k)
{
    Abc_Print(1,"stran-frozen-cnf-template: schema=1 stage=%s call=%llu depth=%d relations=%d template-vars=%d template-clauses=%lld template-stored-clauses=%d\n",
        stage,call,k,s->u.nRelations,s->nTransitionVars,s->transitionAttempted,sat_solver_nclauses(s->u.pSat));
}

static void Cec_TranFrozenCnfStop(Cec_TranFrozenCnfSolver_t * s,int alive)
{
    Cec_TranFrozenCnfSolver_t saved;int vars,clauses,learned,records,i,disable;
    long long conflicts,decisions,propagations;abctime end;
    CEC_BASIS_REQUIRE(s->Requests==s->Sat+s->Unsat+s->Unknown);
    CEC_BASIS_REQUIRE(s->LazyMode || s->ResearchMode || s->Requests==s->SolverCalls+s->ConditionedUnsat);
    CEC_BASIS_REQUIRE(s->Models==s->Sat && s->Replays==s->Sat && s->QChecks==s->Sat);
    CEC_BASIS_REQUIRE(!s->Oracle || (s->OracleCalls==s->Requests && s->OracleChecks==s->Requests-s->Unknown));
    if(s->Oracle)
    {
        abctime clk=Abc_Clock();disable=s->ReferenceGuard^1;Cec_TranLazyClause(s->Template,&disable,1,3);
        s->OracleTicks+=Abc_Clock()-clk;
    }
    vars=sat_solver_nvars(s->View.u.pSat);clauses=sat_solver_nclauses(s->View.u.pSat);
    learned=(int)s->View.u.pSat->stats.learnts;
    conflicts=s->View.u.pSat->stats.conflicts;decisions=s->View.u.pSat->stats.decisions;propagations=s->View.u.pSat->stats.propagations;
    records=Vec_IntSize(s->View.QueryFrames);saved=*s;
    if(s->ResearchMode==2 || s->ResearchMode==4)Cec_TranStrictLocalStop(s);
    else if(s->ResearchMode==3)Cec_TranStrictScorrStop(s);
    Cec_TranFrozenLazyStop(s);
    sat_solver_delete(s->View.u.pSat);
    Vec_IntFree(s->View.QueryFrames);Vec_IntFree(s->View.QueryEdges);Vec_IntFree(s->View.QueryLits);ABC_FREE(s->View.Slots);
    Cec_TranFrozenSrmStop(&s->Srm);
    Cec_TranFrozenCnfProbeStop(&s->Map);ABC_FREE(s);end=Abc_Clock();
    // Numeric snapshots only: borrowed Gia/Maps/template were never freed.
    if(!saved.Profile)return;
    Abc_Print(1,"stran-frozen-cnf-solver: schema=1 event=round mode=%d call=%llu round=%d generation=%d fresh-created=1 fresh-closed=1 encoding-accounted=1 depth=%d relations=%d alive-before=%d alive-after=%d frozen-edges=%d known=%d template-vars=%d template-clauses=%lld class-vars=%d uf-merges=%lld uf-conflicts=%lld inconsistent=%d h-equations=%lld j-equations=%lld query-requests=%lld solver-calls=%lld conditioned-unsat-answers=%lld sat=%lld unsat=%lld unknown=%lld models=%lld replay-calls=%lld replay-gates=%lld replay-h-checks=%lld replay-j-checks=%lld replay-q-checks=%lld replay-failed=0 actual-vars-before=%d actual-vars-after=%d actual-clauses-before=%d actual-clauses-after=%d conflicts=%lld decisions=%lld propagations=%lld learned-before=%d learned-after=%d oracle-enabled=%d oracle-calls=%lld oracle-checks=%lld oracle-sec=%.6f setup-sec=%.6f solve-sec=%.6f round-sec=%.6f",
        saved.Mode,saved.Call,saved.Round,saved.Round,saved.Depth,saved.View.u.nRelations,saved.AliveBefore,alive,Vec_IntSize(saved.FrozenEdges),saved.Known,
        saved.Template->nTransitionVars,saved.Template->transitionAttempted,saved.Map.nClasses,saved.Map.Merges,saved.Map.Contradictions,saved.Inconsistent,
        saved.HEquations,saved.JEquations,saved.Requests,saved.SolverCalls,saved.ConditionedUnsat,saved.Sat,saved.Unsat,saved.Unknown,saved.Models,saved.Replays,
        saved.Gates,saved.HChecks,saved.JChecks,saved.QChecks,saved.VarsBefore,vars,saved.ClausesBefore,clauses,conflicts,decisions,propagations,
        saved.LearnedBefore,learned,saved.Oracle,saved.OracleCalls,saved.OracleChecks,(double)saved.OracleTicks/CLOCKS_PER_SEC,
        (double)saved.SetupTicks/CLOCKS_PER_SEC,(double)saved.SolveTicks/CLOCKS_PER_SEC,(double)(end-saved.Started)/CLOCKS_PER_SEC);
    Abc_Print(1," research-mode=%d guard-vars=%d query-records=%d query-vars=%d cache-lookups=%lld cache-hits=%lld scope=%s",
        saved.ResearchMode,saved.ResearchMode>=2?0:1,records,saved.View.queryVars,saved.View.cacheLookups,saved.View.cacheHits,
        saved.Template->OdcProofScope?"odc":"strict");
    Abc_Print(1," backend=%s original-graph-objects=%d original-graph-cis=%d original-graph-gates=%d srm-objects=%d srm-cis=%d srm-gates=%d srm-xors=%d srm-aliased-cis=%lld srm-aliased-gates=%lld srm-equalities=%lld srm-trivial-equalities=%lld srm-constant-gates=%lld srm-reused-gates=%lld uf-sec=%.6f graph-sec=%.6f encode-sec=%.6f",
        saved.Mode==3?"constrained-srm":saved.Mode==2?"signed-cnf-quotient":"explicit-cnf",
        Gia_ManObjNum(saved.Template->u.p),Gia_ManCiNum(saved.Template->u.p),Gia_ManAndNum(saved.Template->u.p),
        saved.Srm.Objects,saved.Srm.Cis,saved.Srm.Gates,saved.Srm.Xors,saved.Srm.AliasedCis,saved.Srm.AliasedGates,
        saved.Srm.EqualitiesKept,saved.Srm.TrivialEqualities,saved.Srm.ConstantGates,saved.Srm.ReusedGates,
        (double)saved.UfTicks/CLOCKS_PER_SEC,(double)saved.GraphTicks/CLOCKS_PER_SEC,(double)saved.EncodeTicks/CLOCKS_PER_SEC);
    Abc_Print(1," empty-clauses=%lld",saved.Kind[0].Empty+saved.Kind[1].Empty+saved.Kind[2].Empty+saved.Kind[3].Empty+saved.Kind[4].Empty);
    for(i=0;i<5;++i)
    {
        char const * names[5]={"t","j","h","q","r"};Cec_TranFrozenCnfKind_t * c=&saved.Kind[i];
        CEC_BASIS_REQUIRE(c->Attempted==c->Unique+c->Tautologies+c->Duplicates+c->Empty);
        Abc_Print(1," %s-attempted=%lld %s-unique=%lld %s-stored=%lld %s-tautologies=%lld %s-duplicates=%lld %s-empty=%lld %s-literals-in=%lld %s-literals-unique=%lld",
            names[i],c->Attempted,names[i],c->Unique,names[i],c->Stored,names[i],c->Tautologies,names[i],c->Duplicates,names[i],c->Empty,names[i],c->LiteralsIn,names[i],c->LiteralsUnique);
    }
    Abc_Print(1,"\n");fflush(stdout);
}

// Test oracle enumerates original CI assignments and evaluates original gates
// and explicit equalities. It never reads the UF, dense map or encoded clauses.
// A prepared immutable typed-XOR T exercises its four clauses even on builds
// whose production unroller lowers XOR to AND. Two identity frame maps model
// held inputs. This is a helper fixture, not a claimed product unroll case.
// Unlike a finite-round incomplete proof, this enters the real BSAT UNKNOWN
// branch. The unlimited original-formula oracle remains a separate diagnostic.
