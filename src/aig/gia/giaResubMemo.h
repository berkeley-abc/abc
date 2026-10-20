// Exact memoization of COMPLETE native recipe streams, scoped to one ODC pass.
// Input equality includes every ordered truth-table word and iterator option.
// Hashes only index the table; a hit always requires a full key comparison.
// A q-truncated stream is discarded, never mistaken for an exhausted problem.

#define GIA_RESUB_MEMO_OPTIONS 11
#define GIA_RESUB_MEMO_META 9
#define GIA_RESUB_MEMO_FEATURES (GIA_RESUB_PIVOT_CURRENT_DUPLICATE-GIA_RESUB_PIVOT_CURRENT_PATH+1)
struct Gia_ResbMemoEntry_t_
{
    word Hash;
    Vec_Wrd_t * vKey;
    Vec_Wec_t * vRecipes;
    Vec_Int_t * vMeta;
    Vec_Wrd_t * vFeatures;
    Gia_ResbMemoEntry_t * pNext;
    int fComplete;
    long long nBytes;
};
typedef struct Gia_ResbMemo_t_
{
    Gia_ResbMemoEntry_t ** pBins;
    Vec_Ptr_t * vEntries;
    int nBins, nLive;
    long long nBytes, nByteLimit, nBudgetSkips;
    long long nBinds, nHits, nReplay, nIncomplete, nKeyWords, nRecipeInts;
} Gia_ResbMemo_t;
static Gia_ResbMemo_t * s_pResbMemo = NULL;

static void Gia_ResbMemoEntryFree( Gia_ResbMemoEntry_t * p )
{
    Vec_WrdFree(p->vKey); Vec_WecFree(p->vRecipes);
    Vec_IntFree(p->vMeta); Vec_WrdFree(p->vFeatures); ABC_FREE(p);
}

void Abc_ResubProblemCacheStart( int nPayloadMiB )
{
    assert(s_pResbMemo == NULL);
    s_pResbMemo = ABC_CALLOC(Gia_ResbMemo_t,1);
    assert(nPayloadMiB >= 0);
    s_pResbMemo->nByteLimit = (long long)nPayloadMiB * 1024 * 1024;
    s_pResbMemo->nBins = 1024;
    s_pResbMemo->pBins = ABC_CALLOC(Gia_ResbMemoEntry_t *,1024);
    s_pResbMemo->vEntries = Vec_PtrAlloc(1024);
}

void Abc_ResubProblemCacheStop( int fPrint )
{
    Gia_ResbMemo_t * p = s_pResbMemo;
    Gia_ResbMemoEntry_t * e;
    int i;
    assert(p && p->nLive == 0);
    if ( fPrint )
        Abc_Print(1,"window-native-cache: schema=1 binds=%lld exact-hits=%lld replayed-next=%lld complete-problems=%d discarded-prefixes=%lld key-bytes=%lld recipe-bytes=%lld\n",
            p->nBinds,p->nHits,p->nReplay,Vec_PtrSize(p->vEntries),
            p->nIncomplete,8*p->nKeyWords,4*p->nRecipeInts);
    if ( fPrint )
        Abc_Print(1,"window-native-cache budget: payload-bytes=%lld limit-bytes=%lld skipped=%lld (allocator overhead excluded).\n",
            p->nBytes,p->nByteLimit,p->nBudgetSkips);
    Vec_PtrForEachEntry(Gia_ResbMemoEntry_t *,p->vEntries,e,i) Gia_ResbMemoEntryFree(e);
    Vec_PtrFree(p->vEntries); ABC_FREE(p->pBins); ABC_FREE(s_pResbMemo);
}

static Gia_ResbMemoEntry_t * Gia_ResbMemoFind( word Hash, Vec_Wrd_t * vKey )
{
    Gia_ResbMemoEntry_t * e;
    for ( e=s_pResbMemo->pBins[Hash & (s_pResbMemo->nBins-1)]; e; e=e->pNext )
        if ( e->Hash == Hash && Vec_WrdSize(e->vKey) == Vec_WrdSize(vKey) &&
             !memcmp(Vec_WrdArray(e->vKey),Vec_WrdArray(vKey),sizeof(word)*Vec_WrdSize(vKey)) )
            return e;
    return NULL;
}

static void Gia_ResbMemoPublish( Gia_ResbMemoEntry_t * e )
{
    Gia_ResbMemo_t * p = s_pResbMemo;
    Gia_ResbMemoEntry_t * q;
    int i, Slot;
    assert(!e->fComplete && !Gia_ResbMemoFind(e->Hash,e->vKey));
    e->fComplete = 1;
    if ( Vec_PtrSize(p->vEntries) >= 2*p->nBins )
    {
        p->nBins *= 2;
        ABC_FREE(p->pBins);
        p->pBins = ABC_CALLOC(Gia_ResbMemoEntry_t *,p->nBins);
        Vec_PtrForEachEntry(Gia_ResbMemoEntry_t *,p->vEntries,q,i)
        {
            Slot = q->Hash & (p->nBins-1);
            q->pNext=p->pBins[Slot]; p->pBins[Slot]=q;
        }
    }
    Slot=e->Hash & (p->nBins-1);
    e->pNext=p->pBins[Slot]; p->pBins[Slot]=e;
    Vec_PtrPush(p->vEntries,e);
    p->nKeyWords += Vec_WrdSize(e->vKey);
    p->nRecipeInts += Vec_WecSizeSize(e->vRecipes);
}

static void Gia_ResbMemoBind( Gia_ResbIter_t * pIt, void ** ppDivs,
    int nDivs, int nWords, int nLimit, int nDivsMax, int fUseZero,
    int fUseXor, int fUseSolvSched, int nStage5Paths, int fProfile,
    int * pCursor, void ** ppRootCache )
{
    Gia_ResbMemoEntry_t * e;
    Vec_Wrd_t * vKey;
    word Hash=ABC_CONST(0xcbf29ce484222325), Entry;
    int d, w;
    long long Bytes;
    int Options[GIA_RESUB_MEMO_OPTIONS] = {nDivs,nWords,nLimit,nDivsMax,
        fUseZero,fUseXor,fUseSolvSched,nStage5Paths,fProfile,
        s_ResubBothPolarities,pIt->p->fCarePairTruth};
    // Only a fresh pure problem can be keyed without the residual cache and
    // traversal history. Existing per-root/page memoization stays unchanged.
    if ( !s_pResbMemo || pCursor[0] || (ppRootCache && *ppRootCache) ) return;
    s_pResbMemo->nBinds++;
    vKey=Vec_WrdAlloc(GIA_RESUB_MEMO_OPTIONS+nDivs*nWords);
    for ( d=0; d<GIA_RESUB_MEMO_OPTIONS; d++ ) Vec_WrdPush(vKey,(word)Options[d]);
    for ( d=0; d<nDivs; d++ ) for ( w=0; w<nWords; w++ )
        Vec_WrdPush(vKey,((word *)ppDivs[d])[w]);
    Vec_WrdForEachEntry(vKey,Entry,d) Hash=(Hash^Entry)*ABC_CONST(1099511628211);
    e=Gia_ResbMemoFind(Hash,vKey);
    if ( e )
    {
        Vec_WrdFree(vKey);
        s_pResbMemo->nHits++;
        pIt->fMemoReplay=1;
    }
    else
    {
        Bytes = (long long)Vec_WrdSize(vKey)*sizeof(word);
        if ( s_pResbMemo->nByteLimit && s_pResbMemo->nBytes + Bytes > s_pResbMemo->nByteLimit )
        {
            Vec_WrdFree(vKey); s_pResbMemo->nBudgetSkips++;
            return;
        }
        e=ABC_CALLOC(Gia_ResbMemoEntry_t,1);
        e->Hash=Hash; e->vKey=vKey;
        e->nBytes=Bytes; s_pResbMemo->nBytes+=Bytes;
        e->vRecipes=Vec_WecAlloc(8);
        e->vMeta=Vec_IntAlloc(8*GIA_RESUB_MEMO_META);
        e->vFeatures=Vec_WrdAlloc(8*GIA_RESUB_MEMO_FEATURES);
    }
    pIt->pMemo=e;
    s_pResbMemo->nLive++;
}

static void Gia_ResbMemoUnbind( Gia_ResbIter_t * pIt )
{
    if ( !pIt->pMemo ) return;
    assert(s_pResbMemo && s_pResbMemo->nLive > 0);
    s_pResbMemo->nLive--;
    if ( !pIt->pMemo->fComplete )
    {
        s_pResbMemo->nIncomplete++;
        s_pResbMemo->nBytes-=pIt->pMemo->nBytes;
        Gia_ResbMemoEntryFree(pIt->pMemo);
    }
    pIt->pMemo=NULL;
}

static void Gia_ResbMemoRecord( Gia_ResbIter_t * pIt, int * pArray,
    int nArray, int Attempt, int Exhausted, int Invalid )
{
    Gia_ResbMemoEntry_t * e=pIt->pMemo;
    Vec_Int_t * vRecipe;
    int Meta[GIA_RESUB_MEMO_META] = {Attempt,Exhausted,Invalid,
        pIt->Stage,pIt->n,pIt->i,pIt->k,pIt->iGreedy,pIt->p->nStage5TopFrontier};
    int i;
    long long Bytes = (long long)(nArray + GIA_RESUB_MEMO_META)*sizeof(int) +
        GIA_RESUB_MEMO_FEATURES*sizeof(word);
    assert(e && !pIt->fMemoReplay && !e->fComplete);
    if ( s_pResbMemo->nByteLimit && s_pResbMemo->nBytes + Bytes > s_pResbMemo->nByteLimit )
    {
        s_pResbMemo->nBudgetSkips++;
        Gia_ResbMemoUnbind(pIt); // drop the prefix; native iteration continues unchanged
        return;
    }
    e->nBytes+=Bytes; s_pResbMemo->nBytes+=Bytes;
    vRecipe=Vec_WecPushLevel(e->vRecipes);
    if ( nArray ) Vec_IntPushArray(vRecipe,pArray,nArray);
    Vec_IntPushArray(e->vMeta,Meta,GIA_RESUB_MEMO_META);
    for ( i=GIA_RESUB_PIVOT_CURRENT_PATH; i<=GIA_RESUB_PIVOT_CURRENT_DUPLICATE; i++ )
        Vec_WrdPush(e->vFeatures,(word)pIt->PivotProfile[i]);
    if ( Exhausted ) Gia_ResbMemoPublish(e);
}

static int Gia_ResbMemoReplay( Gia_ResbIter_t * pIt, int ** ppArray,
    int * pnAttempt, int * pfExhausted, int * pfInvalid )
{
    Gia_ResbMemoEntry_t * e=pIt->pMemo;
    Vec_Int_t * vRecipe;
    int * m, i, Step=Abc_MinInt(pIt->iMemo++,Vec_WecSize(e->vRecipes)-1);
    assert(e->fComplete && Vec_WecSize(e->vRecipes)>0);
    vRecipe=Vec_WecEntry(e->vRecipes,Step);
    m=Vec_IntArray(e->vMeta)+GIA_RESUB_MEMO_META*Step;
    if ( pnAttempt && Vec_IntSize(vRecipe) ) *pnAttempt=m[0];
    *pfExhausted=m[1]; *pfInvalid=m[2];
    pIt->Stage=m[3]; pIt->n=m[4]; pIt->i=m[5]; pIt->k=m[6];
    pIt->iGreedy=m[7]; pIt->p->nStage5TopFrontier=m[8];
    // Candidate ranking metadata is semantic. Historical work/timing counts
    // are not: replay did not run those pivots or residual searches.
    memset(pIt->PivotProfile,0,sizeof(pIt->PivotProfile));
    for ( i=0; i<GIA_RESUB_MEMO_FEATURES; i++ )
        pIt->PivotProfile[GIA_RESUB_PIVOT_CURRENT_PATH+i]=
            (long long)Vec_WrdEntry(e->vFeatures,Step*GIA_RESUB_MEMO_FEATURES+i);
    *ppArray=Vec_IntSize(vRecipe) ? Vec_IntArray(vRecipe) : NULL;
    s_pResbMemo->nReplay++;
    return Vec_IntSize(vRecipe);
}
