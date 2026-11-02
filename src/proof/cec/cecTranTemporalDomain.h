// TN1 is a structural search restriction, never a simulation or proof view.
// Two graph-sized queues visit (object, crossed-register=0|1) at most once.
// No GIA traversal IDs, Values, references or persistent per-root masks change.
typedef struct Cec_TranTemporalDomain_t_
{
    Gia_Man_t * pGia;
    unsigned char * pSeen, * pRootSeen;
    int * pWork[2], nWork[2];
    int nObjects, Round, Root, nPoolRecords;
    long long Calls, First, Cont, Roots;
    long long States[2], AndEdges[2], Crossings, RoStops;
    long long Unique, Earlier, Target, Later;
    long long Collected, Before, After, TfoBefore, TfoAfter, Bound;
    long long RankCalls, RankInput, RankOutput, ReuseCalls, ReuseInput;
    long long FreshPools, FreshPostB, ReusePools, ReuseBound;
    abctime TimeStart, TimeWalk, TimeFilter;
} Cec_TranTemporalDomain_t;

static int Cec_TranTemporalDomainParse( char const * text )
{
    if ( text == NULL || !strcmp(text,"0") ) return 0;
    if ( !strcmp(text,"1") ) return 1;
    return -1;
}

static int Cec_TranTemporalDomainEnabled()
{
    int value = Cec_TranTemporalDomainParse(getenv("ABC_STRAN_STRICT_TEMPORAL_DOMAIN"));
    assert(value >= 0);
    return value;
}

static Cec_TranTemporalDomain_t * Cec_TranTemporalDomainStart(
    Gia_Man_t * p, Cec_ParTran_t * pars, Cec_TranProf_t * prof, int comb )
{
    Cec_TranTemporalDomain_t * t;
    abctime clk;
    if ( !pars->fRoute3 || comb || pars->fOdcProofScope ) return NULL;
    if ( !Cec_TranTemporalDomainEnabled() ) return NULL;
    assert(getenv("ABC_SRESUB_LOCAL_DOMAIN") && !strcmp(getenv("ABC_SRESUB_LOCAL_DOMAIN"),"0"));
    clk = Abc_Clock();
    t = ABC_CALLOC(Cec_TranTemporalDomain_t,1);
    t->pGia = p; t->nObjects = Gia_ManObjNum(p);
    t->Round = prof->PreproofRound; t->Root = -1;
    t->pSeen = ABC_CALLOC(unsigned char,t->nObjects);
    t->pRootSeen = ABC_CALLOC(unsigned char,t->nObjects);
    t->pWork[0] = ABC_ALLOC(int,t->nObjects);
    t->pWork[1] = ABC_ALLOC(int,t->nObjects);
    assert(t->pSeen && t->pRootSeen && t->pWork[0] && t->pWork[1]);
    t->TimeStart = Abc_Clock()-clk;
    return t;
}

static void Cec_TranTemporalDomainConfig( Cec_TranTemporalDomain_t * t,
    Cec_ParTran_t * pars, int tfo )
{
    if ( !t ) return;
    Abc_Print(1,"stran-strict temporal-domain config: schema=2 round=%d enabled=1 hops=1 source=global-ordered-subsequence global-earlier=1 no-routing=1 local-mode=0 tfo=%d K=%d B=%d objects=%d regs=%d traversal=full-two-layer cursor=parent-freeze-page-reuse macro-source=filtered-collection rank-work=existing-kernel-profiles scratch-bytes=%lld proof=unchanged\n",
        t->Round,tfo,pars->nConstrMax,pars->nConstrBaseMax,t->nObjects,
        Gia_ManRegNum(t->pGia),(long long)sizeof(*t)+
        t->nObjects*(2LL*sizeof(unsigned char)+2LL*sizeof(int)));
}

static void Cec_TranTemporalDomainEnqueue( Cec_TranTemporalDomain_t * t,
    int object, int layer )
{
    unsigned char bit = (unsigned char)(1 << layer);
    assert(object >= 0 && object < t->nObjects && (layer == 0 || layer == 1));
    if ( t->pSeen[object] & bit ) return;
    if ( !t->pSeen[object] )
    {
        t->Unique++;
        t->Earlier += object < t->Root;
        t->Target += object == t->Root;
        t->Later += object > t->Root;
    }
    t->pSeen[object] |= bit;
    assert(t->nWork[layer] < t->nObjects);
    t->pWork[layer][t->nWork[layer]++] = object;
}

static void Cec_TranTemporalDomainWalk( Cec_TranTemporalDomain_t * t, int root )
{
    int layer, i, object;
    Gia_Obj_t * node;
    abctime clk = Abc_Clock();
    assert(Gia_ManObjNum(t->pGia) == t->nObjects);
    assert(root > 0 && root < t->nObjects && Gia_ObjIsAnd(Gia_ManObj(t->pGia,root)));
    // Clear only last call's visited objects, not |G| bytes per root.
    for ( layer=0; layer<2; ++layer )
    {
        for ( i=0; i<t->nWork[layer]; ++i ) t->pSeen[t->pWork[layer][i]] = 0;
        t->nWork[layer] = 0;
    }
    t->Root = root;
    Cec_TranTemporalDomainEnqueue(t,root,0);
    for ( layer=0; layer<2; ++layer )
        for ( i=0; i<t->nWork[layer]; ++i )
        {
            object = t->pWork[layer][i];
            node = Gia_ManObj(t->pGia,object);
            t->States[layer]++;
            if ( Gia_ObjIsAnd(node) )
            {
                t->AndEdges[layer] += 2;
                Cec_TranTemporalDomainEnqueue(t,Gia_ObjFaninId0p(t->pGia,node),layer);
                Cec_TranTemporalDomainEnqueue(t,Gia_ObjFaninId1p(t->pGia,node),layer);
            }
            else if ( Gia_ObjIsRo(t->pGia,node) )
            {
                if ( layer == 0 )
                {
                    // This helper pairs the final R CI/COs, including typed POs.
                    Gia_Obj_t * ri = Gia_ObjRoToRi(t->pGia,node);
                    t->Crossings++;
                    Cec_TranTemporalDomainEnqueue(t,Gia_ObjFaninId0p(t->pGia,ri),1);
                }
                else t->RoStops++;
            }
            // Every PI/constant is a leaf. Layer1 ROs never cross again.
        }
    t->TimeWalk += Abc_Clock()-clk;
}

static void Cec_TranTemporalDomainCompact( Cec_TranTemporalDomain_t * t,
    Vec_Int_t * pool )
{
    int i, object, kept=0;
    if ( !pool ) return;
    Vec_IntForEachEntry(pool,object,i)
    {
        assert(object > 0 && object < t->Root && Gia_ObjIsCand(Gia_ManObj(t->pGia,object)));
        if ( t->pSeen[object] ) Vec_IntWriteEntry(pool,kept++,object);
    }
    Vec_IntShrink(pool,kept);
}

// Called after the original complete global collection and covered filter.
// Keep both pool and TFO rescue witnesses in their original relative order.
static void Cec_TranTemporalDomainFilter( Cec_TranTemporalDomain_t * t,
    int root, int wave, int collected, Vec_Int_t * pool, Vec_Int_t * tfo )
{
    int i, object, before;
    abctime clk;
    if ( !t ) return;
    Cec_TranTemporalDomainWalk(t,root);
    clk = Abc_Clock();
    t->Calls++; t->First += wave==0; t->Cont += wave!=0;
    t->Roots += !t->pRootSeen[root]; t->pRootSeen[root] = 1;
    before = Vec_IntSize(pool);
    t->Collected += collected; t->Before += before;
    t->TfoBefore += tfo ? Vec_IntSize(tfo) : 0;
    Cec_TranTemporalDomainCompact(t,pool);
    Cec_TranTemporalDomainCompact(t,tfo);
    t->After += Vec_IntSize(pool);
    t->TfoAfter += tfo ? Vec_IntSize(tfo) : 0;
    t->TimeFilter += Abc_Clock()-clk;
    // Bounded examples only. The mechanism test compares complete pools.
    if ( wave || t->nPoolRecords == 8 || Vec_IntSize(pool)>128 ) return;
    Abc_Print(1,"stran-strict temporal-domain pool: schema=2 round=%d ordinal=%d root=%d wave=0 stage=pre-rank before=%d size=%d members=",
        t->Round,++t->nPoolRecords,root,before,Vec_IntSize(pool));
    if ( !Vec_IntSize(pool) ) Abc_Print(1,"none");
    Vec_IntForEachEntry(pool,object,i) Abc_Print(1,"%s%d",i?",":"",object);
    Abc_Print(1,"\n");
}

// Count boundary objects, not dense-loop work: the parent's DOT, bound,
// final-filter and POPCNT kernels already record their own actual work.
static void Cec_TranTemporalDomainRank( Cec_TranTemporalDomain_t * t,
    int input, int output, int reuse )
{
    if ( !t ) return;
    assert(input > 0 && output >= 0 && output <= input);
    if ( reuse )
    {
        t->ReuseCalls++; t->ReuseInput += input;
        return;
    }
    t->RankCalls++; t->RankInput += input; t->RankOutput += output;
}

static void Cec_TranTemporalDomainBound( Cec_TranTemporalDomain_t * t,
    Gia_Man_t * p, int root, int beforeBind, Vec_Int_t * pool, int reuse )
{
    int i, object;
    if ( !t ) return;
    assert(t->pGia == p && t->nObjects == Gia_ManObjNum(p) && t->Root == root);
    // PAGE reuse's input is an unranked reservoir, never a fresh post-B pool.
    if ( reuse )
    {
        t->ReusePools++; t->ReuseBound += Vec_IntSize(pool);
    }
    else
    {
        t->FreshPools++; t->FreshPostB += beforeBind;
    }
    t->Bound += Vec_IntSize(pool);
    Vec_IntForEachEntry(pool,object,i)
    {
        assert(object > 0 && object < root && Gia_ObjIsCand(Gia_ManObj(p,object)));
        assert(t->pSeen[object]);
    }
}

static void Cec_TranTemporalDomainStop( Cec_TranTemporalDomain_t * t )
{
    if ( !t ) return;
    Abc_Print(1,"stran-strict temporal-domain profile: schema=2 round=%d calls=%lld first-pages=%lld continuation-pages=%lld unique-roots=%lld walk-layer0=%lld walk-layer1=%lld walk-unique=%lld walk-earlier=%lld walk-target=%lld walk-later=%lld and-edges0=%lld and-edges1=%lld register-crossings=%lld layer1-ro-stops=%lld collected=%lld before=%lld after=%lld tfo-before=%lld tfo-after=%lld fresh-pool-calls=%lld fresh-post-B=%lld reuse-pool-calls=%lld reuse-bound=%lld bound=%lld rank-calls=%lld rank-input=%lld rank-output=%lld rank-reuse-calls=%lld rank-reuse-input=%lld pool-records=%d start-sec=%.9f walk-sec=%.9f filter-sec=%.9f work=structural-visits-and-boundary-objects rank-work=existing-kernel-profiles proof=unchanged\n",
        t->Round,t->Calls,t->First,t->Cont,t->Roots,t->States[0],t->States[1],
        t->Unique,t->Earlier,t->Target,t->Later,t->AndEdges[0],t->AndEdges[1],
        t->Crossings,t->RoStops,t->Collected,t->Before,t->After,
        t->TfoBefore,t->TfoAfter,t->FreshPools,t->FreshPostB,t->ReusePools,
        t->ReuseBound,t->Bound,t->RankCalls,t->RankInput,t->RankOutput,
        t->ReuseCalls,t->ReuseInput,t->nPoolRecords,
        Cec_TranTimeSec(t->TimeStart),Cec_TranTimeSec(t->TimeWalk),Cec_TranTimeSec(t->TimeFilter));
    ABC_FREE(t->pSeen); ABC_FREE(t->pRootSeen);
    ABC_FREE(t->pWork[0]); ABC_FREE(t->pWork[1]); ABC_FREE(t);
}
