/* Complete FIRST candidate streams, scoped to one native DAR resub pass.
   Only positional recipes survive across roots. Acceptance is never cached.
   Included after Dar_Resub_t and the Dar_ResubConsider forward declaration. */
#define DAR_RS_MEMO_BINS 4096
#define DAR_RS_MEMO_LIMIT (64 * 1024 * 1024)

typedef struct Dar_ResubMemoEntry_t_ Dar_ResubMemoEntry_t;
struct Dar_ResubMemoEntry_t_
{
    Dar_ResubMemoEntry_t * pNext;
    unsigned Hash;
    int nKey, nRecipes;
    /* Key followed by the encoded recipes, in the same allocation. */
};

struct Dar_ResubMemo_t_
{
    Dar_ResubMemoEntry_t * Bins[DAR_RS_MEMO_BINS];
    Vec_Int_t * vKey, * vRecipes;
    unsigned Hash, MapIds[512];
    int MapPositions[512], fRecording;
    long long Bytes, Queries, Hits, Replayed, Complete;
};

static Dar_ResubMemo_t * Dar_ResubMemoStart( void )
{
    Dar_ResubMemo_t * m = ABC_CALLOC(Dar_ResubMemo_t, 1);
    m->vKey = Vec_IntAlloc(256);
    m->vRecipes = Vec_IntAlloc(64);
    return m;
}

static void Dar_ResubMemoStop( Dar_ResubMemo_t * m, int fProfile )
{
    Dar_ResubMemoEntry_t * e, * next;
    int b;
    if ( !m ) return;
    assert(!m->fRecording);
    if ( fProfile )
        printf("DAR_RESUB_MEMO queries=%lld hits=%lld replayed=%lld complete=%lld bytes=%lld\n",
            m->Queries,m->Hits,m->Replayed,m->Complete,m->Bytes);
    for ( b = 0; b < DAR_RS_MEMO_BINS; b++ )
        for ( e = m->Bins[b]; e; e = next ) { next = e->pNext; ABC_FREE(e); }
    Vec_IntFree(m->vKey); Vec_IntFree(m->vRecipes); ABC_FREE(m);
}

static Dec_Graph_t * Dar_ResubMemoDecode( Dar_Resub_t * p, int ** ppData )
{
    int * data = *ppData;
    int nLeaves = *data++, nSize = *data++, root = *data++, i, a, b;
    Dec_Graph_t * g = Dec_GraphCreate(nLeaves);
    assert(nLeaves >= 2 && nLeaves <= 4 && nSize <= 8);
    for ( i = 0; i < nLeaves; i++ )
    {
        assert(*data >= 0 && *data < p->nSearchDivs);
        Dec_GraphNode(g,i)->pFunc = Vec_PtrEntry(p->vDivs, *data++);
    }
    for ( i = nLeaves; i < nSize; i++ )
    {
        a = *data++; b = *data++;
        assert(Abc_Lit2Var(a) < i && Abc_Lit2Var(b) < i);
        Dec_GraphAddNodeAnd(g, Dec_EdgeCreate(Abc_Lit2Var(a),Abc_LitIsCompl(a)),
                              Dec_EdgeCreate(Abc_Lit2Var(b),Abc_LitIsCompl(b)));
    }
    Dec_GraphSetRoot(g, Dec_EdgeCreate(Abc_Lit2Var(root),Abc_LitIsCompl(root)));
    assert(g->nSize == nSize);
    *ppData = data;
    return g;
}

/* FIRST classification, pair caps, and triple ordering read levels before
   yielding candidates. They are part of the key, together with every ordered
   truth word and phase. A hash hit alone never authorizes replay. */
static int Dar_ResubMemoBegin( Dar_Resub_t * p, Dec_Graph_t ** ppGraph )
{
    Dar_ResubMemo_t * m = p->pMemo;
    Dar_ResubMemoEntry_t * e;
    Aig_Obj_t * obj;
    int i, w, value, * data, * end;
    unsigned id, slot;
    if ( !m ) return 0;
    assert(!m->fRecording && !*ppGraph);
    m->Queries++;
    Vec_IntClear(m->vKey);
    Vec_IntPush(m->vKey, p->nWords);
    Vec_IntPush(m->vKey, p->nLeaves);
    Vec_IntPush(m->vKey, p->nLeavesMax);
    Vec_IntPush(m->vKey, p->nSearchDivs);
    Vec_IntPush(m->vKey, p->Required);
    Vec_IntPush(m->vKey, p->pPars->nMinSaved);
    Vec_IntPush(m->vKey, p->fIndex);
    Vec_IntPush(m->vKey, p->pRoot->fPhase);
    for ( w = 0; w < p->nWords; w++ )
    {
        Vec_IntPush(m->vKey, p->pCareSet[w]);
        Vec_IntPush(m->vKey, ((unsigned *)p->pRoot->pData)[w]);
    }
    Vec_PtrForEachEntryStop(Aig_Obj_t *, p->vDivs, obj, i, p->nSearchDivs)
    {
        Vec_IntPush(m->vKey, obj->Level);
        Vec_IntPush(m->vKey, obj->fPhase);
        for ( w = 0; w < p->nWords; w++ ) Vec_IntPush(m->vKey, ((unsigned *)obj->pData)[w]);
    }
    m->Hash = 2166136261u;
    Vec_IntForEachEntry(m->vKey, value, i) m->Hash = (m->Hash ^ (unsigned)value) * 16777619u;
    slot = m->Hash & (DAR_RS_MEMO_BINS-1);
    for ( e = m->Bins[slot]; e; e = e->pNext )
        if ( e->Hash == m->Hash && e->nKey == Vec_IntSize(m->vKey) &&
             !memcmp(e+1, Vec_IntArray(m->vKey), sizeof(int)*e->nKey) )
        {
            m->Hits++;
            data = (int *)(e+1) + e->nKey; end = data + e->nRecipes;
            while ( data < end )
            {
                Dec_Graph_t * g = Dar_ResubMemoDecode(p, &data);
                m->Replayed++;
                if ( Dar_ResubConsider(p,g) ) { *ppGraph = g; return 1; }
                Dec_GraphFree(g);
            }
            assert(data == end);
            return 1;
        }
    Vec_IntClear(m->vRecipes);
    if ( m->Bytes + sizeof(*e) + sizeof(int)*Vec_IntSize(m->vKey) > DAR_RS_MEMO_LIMIT )
        return 0;
    memset(m->MapIds, 0, sizeof(m->MapIds));
    Vec_PtrForEachEntryStop(Aig_Obj_t *, p->vDivs, obj, i, p->nSearchDivs)
    {
        id = (unsigned)obj->Id + 1;
        slot = (id * 2654435761u) & 511;
        while ( m->MapIds[slot] ) { assert(m->MapIds[slot] != id); slot = (slot+1) & 511; }
        m->MapIds[slot] = id; m->MapPositions[slot] = i;
    }
    m->fRecording = 1;
    return 0;
}

static void Dar_ResubMemoRecord( Dar_Resub_t * p, Dec_Graph_t * g )
{
    Dar_ResubMemo_t * m = p->pMemo;
    Dec_Node_t * node;
    unsigned id, slot;
    int i, nInts;
    if ( !m || !m->fRecording ) return;
    assert(!g->fConst && g->nLeaves >= 2 && g->nLeaves <= 4 && g->nSize <= 8);
    nInts = 3 + g->nLeaves + 2*(g->nSize-g->nLeaves);
    if ( m->Bytes + sizeof(Dar_ResubMemoEntry_t) +
         sizeof(int)*(Vec_IntSize(m->vKey)+Vec_IntSize(m->vRecipes)+nInts) > DAR_RS_MEMO_LIMIT )
    { m->fRecording = 0; Vec_IntClear(m->vRecipes); return; }
    Vec_IntPush(m->vRecipes, g->nLeaves); Vec_IntPush(m->vRecipes, g->nSize);
    Vec_IntPush(m->vRecipes, Abc_Var2Lit(g->eRoot.Node,g->eRoot.fCompl));
    Dec_GraphForEachLeaf(g, node, i)
    {
        assert(!Aig_IsComplement((Aig_Obj_t *)node->pFunc));
        id = (unsigned)((Aig_Obj_t *)node->pFunc)->Id + 1;
        slot = (id * 2654435761u) & 511;
        while ( m->MapIds[slot] != id ) { assert(m->MapIds[slot]); slot = (slot+1) & 511; }
        Vec_IntPush(m->vRecipes, m->MapPositions[slot]);
    }
    Dec_GraphForEachNode(g, node, i)
    {
        Vec_IntPush(m->vRecipes, Abc_Var2Lit(node->eEdge0.Node,node->eEdge0.fCompl));
        Vec_IntPush(m->vRecipes, Abc_Var2Lit(node->eEdge1.Node,node->eEdge1.fCompl));
    }
}

/* A successful search stopped at a prefix. Only a fully exhausted stream,
   including an empty stream, may be published for another graph context. */
static void Dar_ResubMemoEnd( Dar_Resub_t * p, int fComplete )
{
    Dar_ResubMemo_t * m = p->pMemo;
    Dar_ResubMemoEntry_t * e;
    int bytes, slot;
    if ( !m || !m->fRecording ) return;
    m->fRecording = 0;
    if ( !fComplete ) return;
    bytes = sizeof(*e) + sizeof(int)*(Vec_IntSize(m->vKey)+Vec_IntSize(m->vRecipes));
    assert(m->Bytes + bytes <= DAR_RS_MEMO_LIMIT);
    e = (Dar_ResubMemoEntry_t *)ABC_ALLOC(char, bytes);
    e->Hash = m->Hash; e->nKey = Vec_IntSize(m->vKey); e->nRecipes = Vec_IntSize(m->vRecipes);
    memcpy(e+1, Vec_IntArray(m->vKey), sizeof(int)*e->nKey);
    if ( e->nRecipes ) memcpy((int *)(e+1)+e->nKey, Vec_IntArray(m->vRecipes), sizeof(int)*e->nRecipes);
    slot = e->Hash & (DAR_RS_MEMO_BINS-1);
    e->pNext = m->Bins[slot]; m->Bins[slot] = e;
    m->Bytes += bytes; m->Complete++;
}
