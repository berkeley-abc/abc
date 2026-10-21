// Exact active-domain traversal for the lazy signed-basis engine. All IDs,
// transition gates and endpoint maps belong to this one immutable proof call.
typedef struct Cec_TranRelActive_t_ {
    Vec_Int_t * Ids, * FrozenEdges;
    int fused;
    long long targetVisits, frozenVisits, transitionVisits, compactVisits;
    long long denseReplayOpportunities, denseForestOpportunities, verifyVisits;
} Cec_TranRelActive_t;

static int Cec_TranRelationalActiveMode()
{
    char const * s=getenv("ABC_STRAN_RELATIONAL_ACTIVE");
    if(!s || !strcmp(s,"0"))return 0;
    if(!strcmp(s,"1"))return 1;
    if(!strcmp(s,"2"))return 2; // Also fuse survivor compaction into replay.
    if(!strcmp(s,"3"))return 3; // Repair after exhausting live selected edges.
    Abc_Print(-1,"stran-quality-invalid-option: ABC_STRAN_RELATIONAL_ACTIVE must be 0, 1, 2 or 3\n");
    exit(2);return 0;
}

static Cec_TranRelActive_t Cec_TranActiveStart(int n)
{
    Cec_TranRelActive_t a;
    int i;
    memset(&a,0,sizeof(a));a.Ids=Vec_IntAlloc(n);a.FrozenEdges=Vec_IntAlloc(128);
    for(i=0;i<n;++i)Vec_IntPush(a.Ids,i);
    return a;
}

static void Cec_TranActiveCompact(Cec_TranRelActive_t * a,Vec_Int_t * scope)
{
    int i,j,write=0;
    Vec_IntForEachEntry(a->Ids,i,j)
    {
        ++a->compactVisits;
        if(Vec_IntEntry(scope,i))Vec_IntWriteEntry(a->Ids,write++,i);
    }
    Vec_IntShrink(a->Ids,write);
}

// Identical signed union/odd-cycle construction, in original submission order.
// Clear only the previous chosen edges; the remaining entries are already zero.
static void Cec_TranActiveBuild(Cec_TranBasisForest_t * g,Vec_Int_t * scope,Cec_TranRelActive_t * active)
{
    int i,j,a,b,ra,rb,pa,pb,tmp;
    ++g->builds;g->edgeVisits+=Vec_IntSize(active->Ids);
    active->denseForestOpportunities+=g->n;g->conflicts=0;
    Vec_IntForEachEntry(g->Edges,i,j)Vec_StrWriteEntry(g->Chosen,i,0);
    Vec_IntClear(g->Edges);
    for(i=0;i<Vec_IntSize(g->Vars);++i)
    {Vec_IntWriteEntry(g->Parent,i,i);Vec_IntWriteEntry(g->Size,i,1);Vec_StrWriteEntry(g->Parity,i,0);}
    Vec_IntForEachEntry(active->Ids,i,j)
    {
        CEC_BASIS_REQUIRE(Vec_IntEntry(scope,i) && (!j || Vec_IntEntry(active->Ids,j-1)<i));
        a=Vec_IntEntry(g->Left,i);b=Vec_IntEntry(g->Right,i);
        ra=Cec_TranBasisFind(g,a,&pa);rb=Cec_TranBasisFind(g,b,&pb);
        if(ra==rb)
        {
            if((pa^pb)==Vec_StrEntry(g->Sign,i))continue;
            Vec_StrWriteEntry(g->Chosen,i,2);Vec_IntPush(g->Edges,i);++g->conflicts;continue;
        }
        if(Vec_IntEntry(g->Size,ra)<Vec_IntEntry(g->Size,rb)){tmp=ra;ra=rb;rb=tmp;}
        Vec_IntWriteEntry(g->Parent,rb,ra);
        Vec_StrWriteEntry(g->Parity,rb,(char)(pa^pb^Vec_StrEntry(g->Sign,i)));
        Vec_IntWriteEntry(g->Size,ra,Vec_IntEntry(g->Size,ra)+Vec_IntEntry(g->Size,rb));
        Vec_StrWriteEntry(g->Chosen,i,1);Vec_IntPush(g->Edges,i);
    }
}

static void Cec_TranActiveVerify(Cec_TranBasisForest_t * g,Vec_Int_t * scope,Vec_Int_t * done,Cec_TranRelActive_t * active)
{
    int i,j,ra,rb,pa,pb;
    CEC_BASIS_REQUIRE(g->conflicts==0);
    Vec_IntForEachEntry(g->Edges,i,j)
        CEC_BASIS_REQUIRE(Vec_IntEntry(scope,i) && Vec_IntEntry(done,i));
    Vec_IntForEachEntry(active->Ids,i,j)
    {
        ++active->verifyVisits;CEC_BASIS_REQUIRE(Vec_IntEntry(scope,i));
        ra=Cec_TranBasisFind(g,Vec_IntEntry(g->Left,i),&pa);
        rb=Cec_TranBasisFind(g,Vec_IntEntry(g->Right,i),&pb);
        CEC_BASIS_REQUIRE(ra==rb && (pa^pb)==Vec_StrEntry(g->Sign,i));
    }
}

static int Cec_TranActiveValue(int * values,int lit)
{
    int v=values[Abc_Lit2Var(lit)];
    return v<0 ? -1 : v^Abc_LitIsCompl(lit);
}

// Replay every gate of the complete hash-deduplicated transition/recipe graph.
// Unknown inputs remain unknown; neither polarity is a counterexample.
static int * Cec_TranActiveScalar(Cec_TranRelLazy_t * lazy,long long * visits)
{
    Gia_Man_t * p=lazy->u.p;
    Gia_Obj_t * o;
    int * values=ABC_FALLOC(int,Gia_ManObjNum(p)),i,a,b,v;
    values[0]=0;
    CEC_BASIS_REQUIRE(Cec_TranLazyModelLit(lazy->u.pSat,0)!=1);
    Gia_ManForEachObj1(p,o,i)
    {
        if(Gia_ObjIsCi(o))values[i]=Cec_TranLazyModelLit(lazy->u.pSat,Abc_Var2Lit(i,0));
        else
        {
            a=Cec_TranActiveValue(values,Gia_ObjFaninLit0p(p,o));
            if(Gia_ObjIsCo(o)||Gia_ObjIsBuf(o))values[i]=a;
            else
            {
                b=Cec_TranActiveValue(values,Gia_ObjFaninLit1p(p,o));
                values[i]=Gia_ObjIsXor(o) ? (a<0||b<0 ? -1 : a^b) :
                    (a==0||b==0 ? 0 : a<0||b<0 ? -1 : 1);
            }
            v=Cec_TranLazyModelLit(lazy->u.pSat,Abc_Var2Lit(i,0));
            if(values[i]>=0 && v>=0)CEC_BASIS_REQUIRE(values[i]==v);
        }
        ++*visits;
    }
    return values;
}

static Vec_Int_t * Cec_TranActiveReplay(Vec_Int_t * pairs,Cec_TranRelLazy_t * lazy,
    Vec_Int_t * scope,Cec_TranRelActive_t * active,int reset,int frame,int pivot,
    long long * gateChecks,long long * relationChecks)
{
    Vec_Int_t * bad=Vec_IntAlloc(0);
    long long before=active->transitionVisits;
    int * values=Cec_TranActiveScalar(lazy,&active->transitionVisits);
    int i,j,f,a,b,write=0;
    *gateChecks+=active->transitionVisits-before;
    active->denseReplayOpportunities+=(long long)lazy->u.nFrames*lazy->u.nRelations;
    // Frozen H never changes within a round. Its saved forest is exactly its
    // full conjunction, including signed phases, independently tested below.
    if(!reset)for(f=0;f<frame;++f)Vec_IntForEachEntry(active->FrozenEdges,i,j)
    {
        a=Cec_TranActiveValue(values,Cec_TranLazyEndpoint(lazy,f,Vec_IntEntry(pairs,2*i)));
        b=Cec_TranActiveValue(values,Cec_TranLazyEndpoint(lazy,f,Vec_IntEntry(pairs,2*i+1)));
        if(a>=0 && b>=0)CEC_BASIS_REQUIRE(a==b);
        ++active->frozenVisits;++*relationChecks;
    }
    Vec_IntForEachEntry(active->Ids,i,j)
    {
        CEC_BASIS_REQUIRE(Vec_IntEntry(scope,i));
        a=Cec_TranActiveValue(values,Cec_TranLazyEndpoint(lazy,frame,Vec_IntEntry(pairs,2*i)));
        b=Cec_TranActiveValue(values,Cec_TranLazyEndpoint(lazy,frame,Vec_IntEntry(pairs,2*i+1)));
        ++active->targetVisits;++*relationChecks;
        if(a>=0 && b>=0 && a!=b)Vec_IntPush(bad,i);
        else if(active->fused)Vec_IntWriteEntry(active->Ids,write++,i);
    }
    // Stable in-place filtering reuses the mandatory target evaluation pass.
    // The caller immediately withdraws exactly Bad from Scope/Status, then
    // asserts that the resulting domain size equals its surviving count.
    if(active->fused)Vec_IntShrink(active->Ids,write);
    // Only the actual SAT pivot needs a query-definition check. Unmaterialized
    // endpoints are evaluated semantically; withdrawn query records are unused.
    if(pivot>=0)
    {
        int slot=Cec_TranLazySlot(lazy,frame,pivot),q;
        CEC_BASIS_REQUIRE(lazy->Slots[slot]>0);
        q=Vec_IntEntry(lazy->QueryLits,lazy->Slots[slot]-1);
        CEC_BASIS_REQUIRE(Cec_TranLazyModelLit(lazy->u.pSat,q)==1);
        CEC_BASIS_REQUIRE(Vec_IntFind(bad,pivot)>=0);
        ++*gateChecks;
    }
    ABC_FREE(values);return bad;
}

static void Cec_TranActiveStop(Cec_TranRelActive_t * a)
{Vec_IntFree(a->Ids);Vec_IntFree(a->FrozenEdges);}
