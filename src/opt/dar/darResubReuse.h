/* Optional native resub reuse, private to one strict-equivalence pass.

   The pre-cut gate is the rewrite GLOBAL_FAILURE certificate: if removing
   the root can save only one AND, positive COST requires a zero-added
   existing result. Absence of any other live signal with the same signed
   256-bit simulation signature disproves such a result. A matching
   signature NEVER proves equality. The argument is independent of K and
   recipe grammar.

   Include after Dar_Resub_t and darResubMemo.h. No AIG scratch fields used. */
#ifndef ABC_DAR_RESUB_REUSE_H
#define ABC_DAR_RESUB_REUSE_H

typedef struct Dar_ResubGlobalClass_t_
{
    int Representative, Head, Next;
} Dar_ResubGlobalClass_t;

typedef struct Dar_ResubGlobal_t_
{
    Aig_Man_t * pAig;
    word * pWords;
    unsigned char * pReady;
    int * pNext, * pClassId, * pBins;
    Dar_ResubGlobalClass_t * pClasses;
    Vec_Int_t * vStack;
    int nCis, nCap, nSyncedMax, nClasses, nClassCap, nBins;
    long long Queries, WholeOne, Negative, LiveTests, DeletedPruned;
    long long InitSignals, NewSignals, ComputedNodes, AuditCalls, AuditObjects;
    long long AuditCommit;
} Dar_ResubGlobal_t;

struct Dar_ResubReuse_t_
{
    Dar_ResubGlobal_t * pGlobal;
    int fGlobalCheck, GlobalNegative;
    long long GlobalSkipped, GlobalShadowChecked;
};

static int Dar_ResubReuseOption( const char * pName, int fDefault )
{
    const char * pValue = getenv(pName);
    return pValue ? !strcmp(pValue, "1") : fDefault;
}

static int Dar_ResubReuseEnabled( const char * pName )
{
    return Dar_ResubReuseOption(pName, 0);
}

static word Dar_ResubGlobalMix( word x )
{
    x = (x ^ (x >> 30)) * ABC_CONST(0xbf58476d1ce4e5b9);
    x = (x ^ (x >> 27)) * ABC_CONST(0x94d049bb133111eb);
    return x ^ (x >> 31);
}

static int Dar_ResubGlobalSignal( Aig_Obj_t * pObj )
{
    return Aig_ObjIsCi(pObj) || Aig_ObjIsConst1(pObj) ||
        Aig_ObjIsNode(pObj) || Aig_ObjIsBuf(pObj);
}

static void Dar_ResubGlobalGrow( Dar_ResubGlobal_t * g, int nMax )
{
    int nOld = g->nCap, nCap = nOld ? nOld : 16, i;
    if ( nMax <= nOld ) return;
    while ( nCap < nMax ) nCap *= 2;
    g->pWords = ABC_REALLOC(word, g->pWords, 4*nCap);
    g->pReady = ABC_REALLOC(unsigned char, g->pReady, nCap);
    g->pNext = ABC_REALLOC(int, g->pNext, nCap);
    g->pClassId = ABC_REALLOC(int, g->pClassId, nCap);
    memset(g->pReady+nOld, 0, nCap-nOld);
    for ( i = nOld; i < nCap; i++ ) g->pNext[i] = g->pClassId[i] = -1;
    g->nCap = nCap;
}

static unsigned Dar_ResubGlobalHash( Dar_ResubGlobal_t * g, int Id )
{
    word * w = g->pWords + 4*Id;
    word Phase = (word)0 - (w[0] & 1);
    word h = (w[0] ^ Phase) + ABC_CONST(0x9e3779b97f4a7c15);
    h ^= (w[1] ^ Phase) * ABC_CONST(0xbf58476d1ce4e5b9);
    h ^= (w[2] ^ Phase) * ABC_CONST(0x94d049bb133111eb);
    h ^= (w[3] ^ Phase) * ABC_CONST(0xd6e8feb86659fd93);
    return (unsigned)Dar_ResubGlobalMix(h);
}

static int Dar_ResubGlobalSame( Dar_ResubGlobal_t * g, int a, int b )
{
    word * wa = g->pWords+4*a, * wb = g->pWords+4*b;
    word Phase = (word)0 - ((wa[0] ^ wb[0]) & 1);
    int j;
    for ( j = 0; j < 4; j++ ) if ( (wa[j] ^ Phase) != wb[j] ) return 0;
    return 1;
}

static void Dar_ResubGlobalResize( Dar_ResubGlobal_t * g )
{
    int i, Bin;
    g->nBins = g->nBins ? 2*g->nBins : 128;
    g->pBins = ABC_REALLOC(int, g->pBins, g->nBins);
    for ( i = 0; i < g->nBins; i++ ) g->pBins[i] = -1;
    for ( i = 0; i < g->nClasses; i++ )
    {
        Bin = Dar_ResubGlobalHash(g,g->pClasses[i].Representative) & (g->nBins-1);
        g->pClasses[i].Next = g->pBins[Bin]; g->pBins[Bin] = i;
    }
}

static void Dar_ResubGlobalIndex( Dar_ResubGlobal_t * g, int Id )
{
    int Bin, Class;
    assert( g->pReady[Id] == 2 && g->pClassId[Id] == -1 );
    if ( !g->nBins ) Dar_ResubGlobalResize(g);
    Bin = Dar_ResubGlobalHash(g,Id) & (g->nBins-1);
    for ( Class = g->pBins[Bin]; Class >= 0; Class = g->pClasses[Class].Next )
        if ( Dar_ResubGlobalSame(g,Id,g->pClasses[Class].Representative) ) break;
    if ( Class < 0 )
    {
        if ( g->nClasses == g->nClassCap )
        {
            g->nClassCap = g->nClassCap ? 2*g->nClassCap : 128;
            g->pClasses = ABC_REALLOC(Dar_ResubGlobalClass_t,g->pClasses,g->nClassCap);
        }
        Class = g->nClasses++;
        g->pClasses[Class].Representative = Id;
        g->pClasses[Class].Head = -1;
        g->pClasses[Class].Next = g->pBins[Bin]; g->pBins[Bin] = Class;
    }
    g->pNext[Id] = g->pClasses[Class].Head;
    g->pClasses[Class].Head = Id; g->pClassId[Id] = Class;
    if ( g->nClasses >= g->nBins ) Dar_ResubGlobalResize(g);
}

/* IDs need not be topological after in-place replacements. Old surviving
   functions are unchanged by strict root-equivalent commits; compute only
   previously unseen IDs, using an explicit dependency stack. */
static void Dar_ResubGlobalCompute( Dar_ResubGlobal_t * g, Aig_Obj_t * pObj )
{
    Aig_Obj_t * pNode, * pFanin;
    word * w, * a, * b, c0, c1;
    int Id, Fid, k, j, Ready, nFanins;
    assert( !Vec_IntSize(g->vStack) );
    if ( g->pReady[pObj->Id] == 2 ) return;
    Vec_IntPush(g->vStack,pObj->Id);
    while ( Vec_IntSize(g->vStack) )
    {
        Id = Vec_IntEntryLast(g->vStack);
        pNode = Aig_ManObj(g->pAig,Id);
        assert( pNode && pNode->Id == Id && (Aig_ObjIsNode(pNode) || Aig_ObjIsBuf(pNode)) );
        if ( g->pReady[Id] == 2 ) { Vec_IntPop(g->vStack); continue; }
        g->pReady[Id] = 1; Ready = 1;
        nFanins = Aig_ObjIsBuf(pNode) ? 1 : 2;
        for ( k = 0; k < nFanins; k++ )
        {
            pFanin = k ? Aig_ObjFanin1(pNode) : Aig_ObjFanin0(pNode);
            Fid = pFanin->Id;
            assert( Fid < g->nCap && Aig_ManObj(g->pAig,Fid) == pFanin );
            if ( g->pReady[Fid] == 2 ) continue;
            assert( !g->pReady[Fid] && (Aig_ObjIsNode(pFanin) || Aig_ObjIsBuf(pFanin)) );
            Vec_IntPush(g->vStack,Fid); Ready = 0; break;
        }
        if ( !Ready ) continue;
        w = g->pWords+4*Id; a = g->pWords+4*Aig_ObjFanin0(pNode)->Id;
        b = nFanins == 2 ? g->pWords+4*Aig_ObjFanin1(pNode)->Id : NULL;
        c0 = (word)0 - (word)Aig_ObjFaninC0(pNode);
        c1 = nFanins == 2 ? (word)0 - (word)Aig_ObjFaninC1(pNode) : 0;
        for ( j = 0; j < 4; j++ )
            w[j] = !b ? a[j] ^ c0 : Aig_ObjIsExor(pNode) ?
                (a[j] ^ c0) ^ (b[j] ^ c1) : (a[j] ^ c0) & (b[j] ^ c1);
        g->pReady[Id] = 2; Vec_IntPop(g->vStack); g->ComputedNodes++;
    }
}

static Dar_ResubGlobal_t * Dar_ResubGlobalStart( Aig_Man_t * pAig )
{
    Dar_ResubGlobal_t * g = ABC_CALLOC(Dar_ResubGlobal_t,1);
    Aig_Obj_t * pObj;
    word * w;
    int i, j;
    g->pAig = pAig; g->nCis = Aig_ManCiNum(pAig);
    g->vStack = Vec_IntAlloc(64);
    Dar_ResubGlobalGrow(g,Aig_ManObjNumMax(pAig));
    pObj = Aig_ManConst1(pAig); w = g->pWords+4*pObj->Id;
    for ( j = 0; j < 4; j++ ) w[j] = ~(word)0;
    g->pReady[pObj->Id] = 2;
    Aig_ManForEachCi(pAig,pObj,i)
    {
        w = g->pWords+4*pObj->Id;
        for ( j = 0; j < 4; j++ )
            w[j] = Dar_ResubGlobalMix(ABC_CONST(0x243f6a8885a308d3) +
                ABC_CONST(0x9e3779b97f4a7c15) * (4*(word)i+(word)j+1));
        w[0] &= ~(word)1; g->pReady[pObj->Id] = 2;
    }
    Aig_ManForEachObj(pAig,pObj,i)
    {
        if ( !Dar_ResubGlobalSignal(pObj) ) continue;
        Dar_ResubGlobalCompute(g,pObj); Dar_ResubGlobalIndex(g,pObj->Id);
        g->InitSignals++;
    }
    g->nSyncedMax = Aig_ManObjNumMax(pAig);
    g->AuditCommit = -1;
    return g;
}

static void Dar_ResubGlobalFree( Dar_ResubGlobal_t * g )
{
    ABC_FREE(g->pWords); ABC_FREE(g->pReady); ABC_FREE(g->pNext);
    ABC_FREE(g->pClassId); ABC_FREE(g->pBins); ABC_FREE(g->pClasses);
    Vec_IntFree(g->vStack); ABC_FREE(g);
}

static void Dar_ResubGlobalSync( Dar_ResubGlobal_t * g )
{
    Aig_Obj_t * pObj;
    int Id, nMax = Aig_ManObjNumMax(g->pAig);
    assert( nMax >= g->nSyncedMax && Aig_ManCiNum(g->pAig) == g->nCis );
    Dar_ResubGlobalGrow(g,nMax);
    for ( Id = g->nSyncedMax; Id < nMax; Id++ )
    {
        pObj = Aig_ManObj(g->pAig,Id);
        if ( !pObj || !Dar_ResubGlobalSignal(pObj) ) continue;
        assert( pObj->Id == Id && !Aig_ObjIsCi(pObj) && !Aig_ObjIsConst1(pObj) );
        Dar_ResubGlobalCompute(g,pObj); Dar_ResubGlobalIndex(g,Id); g->NewSignals++;
    }
    g->nSyncedMax = nMax;
}

static void Dar_ResubGlobalAudit( Dar_ResubGlobal_t * g )
{
    Dar_ResubGlobal_t * fresh = Dar_ResubGlobalStart(g->pAig);
    Aig_Obj_t * pObj;
    int i;
    Aig_ManForEachObj(g->pAig,pObj,i)
    {
        if ( !Dar_ResubGlobalSignal(pObj) ) continue;
        if ( !g->pReady[pObj->Id] || memcmp(g->pWords+4*pObj->Id, fresh->pWords+4*pObj->Id,4*sizeof(word)) )
        { fprintf(stderr,"DAR_GLOBAL_FAIL stale signature id=%d\n",pObj->Id); abort(); }
        g->AuditObjects++;
    }
    g->AuditCalls++; Dar_ResubGlobalFree(fresh);
}

static int Dar_ResubGlobalCanSkip( Dar_Resub_t * p )
{
    Dar_ResubReuse_t * r = p->pReuse;
    Dar_ResubGlobal_t * g = r->pGlobal;
    Aig_Obj_t * pObj, * a = Aig_ObjFanin0(p->pRoot), * b = Aig_ObjFanin1(p->pRoot);
    int Edges = a == b ? 2 : 1, Id, Class, * pLink;
    Dar_ResubGlobalSync(g);
    if ( r->fGlobalCheck && g->AuditCommit != p->Commits )
    { Dar_ResubGlobalAudit(g); g->AuditCommit = p->Commits; }
    g->Queries++;
    /* This strict subset avoids transient buffers and all support-dependent
       MFFC estimates. Refcounts are restored before every root query. */
    if ( !(Aig_ObjIsCi(a) || (Aig_ObjIsAnd(a) && a->nRefs > Edges)) ||
         !(Aig_ObjIsCi(b) || (Aig_ObjIsAnd(b) && b->nRefs > Edges)) ) return 0;
    g->WholeOne++;
    Class = g->pClassId[p->pRoot->Id];
    assert( Class >= 0 && Dar_ResubGlobalSame(g,p->pRoot->Id,g->pClasses[Class].Representative) );
    pLink = &g->pClasses[Class].Head;
    while ( (Id = *pLink) >= 0 )
    {
        g->LiveTests++; pObj = Aig_ManObj(g->pAig,Id);
        if ( !pObj )
        {
            *pLink = g->pNext[Id];
            g->DeletedPruned++; continue;
        }
        assert( pObj->Id == Id && Dar_ResubGlobalSignal(pObj) );
        if ( Id != p->pRoot->Id ) return 0;
        pLink = &g->pNext[Id];
    }
    g->Negative++;
    return 1;
}

static void Dar_ResubReuseStart( Dar_Resub_t * p )
{
    int fGlobal = Dar_ResubReuseOption("ABC_DRW_GLOBAL_FAIL", 1);
    Dar_ResubReuse_t * r;
    if ( !fGlobal ) return;
    p->pReuse = r = ABC_CALLOC(Dar_ResubReuse_t,1);
    r->fGlobalCheck = Dar_ResubReuseEnabled("ABC_DRW_GLOBAL_FAIL_CHECK");
    r->pGlobal = Dar_ResubGlobalStart(p->pAig);
}

static int Dar_ResubReuseRoot( Dar_Resub_t * p )
{
    Dar_ResubReuse_t * r = p->pReuse;
    if ( !r ) return 0;
    r->GlobalNegative = r->pGlobal && Dar_ResubGlobalCanSkip(p);
    if ( !r->GlobalNegative || r->fGlobalCheck ) return 0;
    r->GlobalSkipped++;
    return 1;
}

static void Dar_ResubReuseCheckRoot( Dar_Resub_t * p, Dec_Graph_t * pGraph )
{
    Dar_ResubReuse_t * r = p->pReuse;
    if ( !r || !r->GlobalNegative || !r->fGlobalCheck ) return;
    if ( pGraph ) { fprintf(stderr,"DAR_GLOBAL_FAIL invalid certificate root=%d\n",p->pRoot->Id); abort(); }
    r->GlobalShadowChecked++;
}

static void Dar_ResubReuseStop( Dar_Resub_t * p )
{
    Dar_ResubReuse_t * r = p->pReuse;
    Dar_ResubGlobal_t * g;
    if ( !r ) return;
    if ( (g = r->pGlobal) )
    {
        /* Run the final audit too: the last visited root may have committed. */
        if ( r->fGlobalCheck ) { Dar_ResubGlobalSync(g); Dar_ResubGlobalAudit(g); }
        if ( p->fProfile ) printf("DAR_GLOBAL_FAIL enabled=1 check=%d queries=%lld whole_one=%lld negative=%lld skipped=%lld shadow_checked=%lld init_signals=%lld new_signals=%lld computed_nodes=%lld live_tests=%lld deleted_pruned=%lld audit_calls=%lld audit_objects=%lld classes=%d signature_bits=256 equality_is_proof=0 grammar=any_strict_cost\n",
            r->fGlobalCheck,g->Queries,g->WholeOne,g->Negative,r->GlobalSkipped,r->GlobalShadowChecked,
            g->InitSignals,g->NewSignals,g->ComputedNodes,g->LiveTests,g->DeletedPruned,
            g->AuditCalls,g->AuditObjects,g->nClasses);
        Dar_ResubGlobalFree(g);
    }
    ABC_FREE(p->pReuse);
}

#endif
