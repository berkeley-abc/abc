// A conditioned SRM owns its reduced graph and residual gate equalities.
// The signed UF contains exactly Frozen H and CLOSED J. Its dense map is
// replaced by an original-unroll-object -> SRM-literal map for model lifting.
typedef struct Cec_TranFrozenSrm_t_ {
    Gia_Man_t * Graph;
    Vec_Int_t * Equalities;
    int Objects, Cis, Gates, Xors;
    long long AliasedCis, AliasedGates, TrivialEqualities, EqualitiesKept;
    long long ConstantGates, ReusedGates;
} Cec_TranFrozenSrm_t;

static Cec_TranFrozenSrm_t Cec_TranFrozenSrmBuild(Gia_Man_t * original,Cec_TranFrozenCnfProbe_t * uf)
{
    Cec_TranFrozenSrm_t s;Gia_Obj_t * o;
    int * classes=uf->Map,* mapped=ABC_FALLOC(int,uf->nVars);
    int * representatives=ABC_FALLOC(int,uf->nClasses);
    int i,cl,rep,a,b,raw,before;
    memset(&s,0,sizeof(s));
    CEC_BASIS_REQUIRE(Gia_ManObjNum(original)==uf->nVars && classes[0]==0);
    s.Graph=Gia_ManStart(uf->nVars);s.Equalities=Vec_IntAlloc(0);
    // UF roots follow union-by-size and can point forward in the DAG. Taking
    // the earliest original object of each class ensures every replacement
    // is available before its consumers, including interleaved frame CIs.
    for(i=0;i<uf->nVars;++i)
    {
        cl=Abc_Lit2Var(classes[i]);
        if(representatives[cl]<0)representatives[cl]=i;
    }
    mapped[0]=0;Gia_ManHashStart(s.Graph);
    Gia_ManForEachObj1(original,o,i)
    {
        rep=representatives[Abc_Lit2Var(classes[i])];
        CEC_BASIS_REQUIRE(rep<=i);
        if(rep!=i)
        {
            CEC_BASIS_REQUIRE(mapped[rep]>=0);
            mapped[i]=mapped[rep]^((classes[i]^classes[rep])&1);
        }
        if(Gia_ObjIsCi(o))
        {
            if(rep==i)mapped[i]=Gia_ManAppendCi(s.Graph);
            else ++s.AliasedCis;
            continue;
        }
        CEC_BASIS_REQUIRE(Gia_ObjIsAnd(o) && !Gia_ObjIsBuf(o));
        a=mapped[Gia_ObjFaninId0p(original,o)]^Gia_ObjFaninC0(o);
        b=mapped[Gia_ObjFaninId1p(original,o)]^Gia_ObjFaninC1(o);
        CEC_BASIS_REQUIRE(a>=0 && b>=0);
        before=Gia_ManObjNum(s.Graph);
        // Typed XOR uses reversed fanin order in Gia's extended gate hash.
        // pMuxes enables this mode even for graphs without actual muxes;
        // Gia owns the array and grows/frees it with the object storage.
        if(Gia_ObjIsXor(o) && !s.Graph->pMuxes)
            s.Graph->pMuxes=ABC_CALLOC(unsigned,s.Graph->nObjsAlloc);
        raw=Gia_ObjIsXor(o)?Gia_ManHashXorReal(s.Graph,a,b):Gia_ManHashAnd(s.Graph,a,b);
        if(raw<2)++s.ConstantGates;
        else if(Gia_ManObjNum(s.Graph)==before)++s.ReusedGates;
        if(rep==i){mapped[i]=raw;continue;}
        ++s.AliasedGates;
        // Replacing consumers alone loses the original gate equation. Keep
        // raw == mapped even when it relates a later gate to its own fanin,
        // or makes this conditioned formula inconsistent. These are proof
        // assumptions for one round, never independent CLOSED certificates.
        if(raw==mapped[i])++s.TrivialEqualities;
        else {Vec_IntPushTwo(s.Equalities,raw,mapped[i]);++s.EqualitiesKept;}
    }
    Gia_ManHashStop(s.Graph);
    s.Objects=Gia_ManObjNum(s.Graph);s.Cis=Gia_ManCiNum(s.Graph);s.Gates=Gia_ManAndNum(s.Graph);
    Gia_ManForEachAnd(s.Graph,o,i)s.Xors+=Gia_ObjIsXor(o)!=0;
    CEC_BASIS_REQUIRE(s.Objects<=uf->nVars && s.AliasedGates==s.TrivialEqualities+s.EqualitiesKept);
    // No cleanup: all original values, including unused free CIs and raw
    // constrained gates, must remain available for complete original replay.
    uf->Map=mapped;ABC_FREE(classes);ABC_FREE(representatives);return s;
}

static void Cec_TranFrozenSrmStop(Cec_TranFrozenSrm_t * s)
{
    if(!s->Graph)return;
    Gia_ManStop(s->Graph);Vec_IntFree(s->Equalities);
}
