// Optional reconvergence cut for Strict divisor discovery, not a proof core.
// The command validates options early; this boundary also protects C callers.
static int Cec_TranCutSizeParse( char const * pText )
{
    if ( !pText ) return 4;
    if ( !strcmp(pText, "0") ) return 0;
    if ( !strcmp(pText, "4") ) return 4;
    if ( !strcmp(pText, "8") ) return 8;
    if ( !strcmp(pText, "16") ) return 16;
    if ( !strcmp(pText, "32") ) return 32;
    return -1;
}

static int Cec_TranCutSizeRead( Cec_ParTran_t const * pPars, int LocalMode )
{
    int Size = Cec_TranCutSizeParse(getenv("ABC_SRESUB_CUT_LEAVES"));
    if ( Size < 0 )
    {
        Abc_Print(-1, "ABC_SRESUB_CUT_LEAVES must be exactly 0, 4, 8, 16 or 32.\n");
        exit(2);
    }
    if ( Size && (pPars->nConstrMax || LocalMode != 2) )
    {
        Abc_Print(-1, "ABC_SRESUB_CUT_LEAVES requires unlimited K and local domain 2.\n");
        exit(2);
    }
    {
        char const * pSelector = getenv("ABC_SRESUB_CUT_SELECTOR");
        char const * pCache = getenv("ABC_SRESUB_CUT_CACHE");
        if ( (pSelector && strcmp(pSelector,"greedy") && strcmp(pSelector,"drw4")) ||
             (pSelector && !strcmp(pSelector,"drw4") && Size != 4) ||
             (pCache && strcmp(pCache,"0") && strcmp(pCache,"1")) ||
             (pCache && !strcmp(pCache,"1") && !Size) )
        {
            Abc_Print(-1,"sresub cut options: selector=greedy|drw4 (drw4 requires 4 leaves), cache=0|1 (requires cut).\n");
            exit(2);
        }
    }
    return Size;
}

// GIA adaptation of abcReconv.c's Abc_NodeFindCut/BuildCutLevelOne: minimum
// newly visited fanins first, higher level breaks ties, zero-cost expands now.
// TravId marks ALL visited members, including expanded internal nodes.  The
// returned leaves bound a subsequent BFS; they do not replace shared divisors
// or define the exact deletion set.  Constants/CIs/buffers are boundaries.
static Vec_Int_t * Cec_TranCutLeaves( Gia_Man_t * p, int iRoot, int nLeaves,
    Cec_TranTfoStats_t * pStats )
{
    Vec_Int_t * vLeaves = Vec_IntAlloc(nLeaves);
    Gia_Obj_t * pObj = Gia_ManObj(p, iRoot);
    int i, k, Id, Fan, Best, Cost, CostBest;
    assert(nLeaves >= 2 && p->vLevels && p->pRefs);
    Gia_ManIncrementTravId(p);
    Gia_ObjSetTravIdCurrentId(p, iRoot);
    for ( k = 0; k < 2; ++k )
    {
        Fan = k ? Gia_ObjFaninId1p(p,pObj) : Gia_ObjFaninId0p(p,pObj);
        if ( Gia_ObjIsTravIdCurrentId(p,Fan) ) continue;
        Gia_ObjSetTravIdCurrentId(p,Fan);
        Vec_IntPush(vLeaves,Fan);
    }
    for ( ;; )
    {
        Best = -1; CostBest = 100;
        Vec_IntForEachEntry(vLeaves, Id, i)
        {
            if ( pStats ) pStats->nCutCosts++;
            pObj = Gia_ManObj(p,Id);
            if ( !Gia_ObjIsAndNotBuf(pObj) ) continue;
            Cost = !Gia_ObjIsTravIdCurrentId(p,Gia_ObjFaninId0p(p,pObj));
            if ( Gia_ObjFaninId0p(p,pObj) != Gia_ObjFaninId1p(p,pObj) )
                Cost += !Gia_ObjIsTravIdCurrentId(p,Gia_ObjFaninId1p(p,pObj));
            if ( Cost == 2 && Gia_ObjRefNumId(p,Id) > 100000 ) continue;
            if ( Cost < CostBest || (Cost == CostBest &&
                 Gia_ObjLevelId(p,Id) > Gia_ObjLevelId(p,Best)) )
                Best = Id, CostBest = Cost;
            if ( CostBest == 0 ) break;
        }
        if ( Best < 0 || Vec_IntSize(vLeaves) - 1 + CostBest > nLeaves ) break;
        if ( pStats ) pStats->nCutExpands++;
        Vec_IntRemove(vLeaves,Best);
        pObj = Gia_ManObj(p,Best);
        for ( k = 0; k < 2; ++k )
        {
            Fan = k ? Gia_ObjFaninId1p(p,pObj) : Gia_ObjFaninId0p(p,pObj);
            if ( Gia_ObjIsTravIdCurrentId(p,Fan) ) continue;
            Gia_ObjSetTravIdCurrentId(p,Fan);
            Vec_IntPush(vLeaves,Fan);
        }
    }
    if ( pStats ) pStats->nCutLeaves = Vec_IntSize(vLeaves);
    return vLeaves;
}

// Boundaries depend only on the immutable pass graph. Do not cache the filtered
// divisor pool: covered/used nodes and the observation/core change across waves.
typedef struct Cec_TranCutCache_t_
{
    Gia_Man_t * pGia;
    Drw_Gia_t * pDrw;
    Vec_Ptr_t * vCuts;
    int Size;
} Cec_TranCutCache_t;

static Cec_TranCutCache_t * Cec_TranCutCacheStartMode( Gia_Man_t * pGia,
    int Size, int fDrw, int fCache )
{
    Cec_TranCutCache_t * p;
    if ( !Size || (!fDrw && !fCache) ) return NULL;
    p = ABC_CALLOC(Cec_TranCutCache_t,1);
    p->pGia = pGia; p->Size = Size;
    p->pDrw = fDrw ? Drw_GiaStart(pGia) : NULL;
    p->vCuts = fCache ? Vec_PtrStart(Gia_ManObjNum(pGia)) : NULL;
    return p;
}

static Cec_TranCutCache_t * Cec_TranCutCacheStart( Gia_Man_t * pGia, int Size )
{
    char const * pSelector = getenv("ABC_SRESUB_CUT_SELECTOR");
    char const * pCache = getenv("ABC_SRESUB_CUT_CACHE");
    return Cec_TranCutCacheStartMode(pGia,Size,
        Size == 4 && (!pSelector || !strcmp(pSelector,"drw4")),
        pCache && !strcmp(pCache,"1"));
}

static Vec_Int_t * Cec_TranCutCacheSelect( Cec_TranCutCache_t * p, int Id,
    Cec_TranTfoStats_t * pStats )
{
    Vec_Int_t * vCut = p->vCuts ? (Vec_Int_t *)Vec_PtrEntry(p->vCuts,Id) : NULL;
    if ( vCut )
    {
        if ( pStats ) pStats->nCutLeaves = Vec_IntSize(vCut);
        return Vec_IntDup(vCut);
    }
    vCut = p->pDrw ? Drw_GiaSelect(p->pDrw,Id) : Cec_TranCutLeaves(p->pGia,Id,p->Size,pStats);
    if ( pStats ) pStats->nCutLeaves = Vec_IntSize(vCut);
    if ( p->vCuts ) Vec_PtrWriteEntry(p->vCuts,Id,Vec_IntDup(vCut));
    return vCut;
}

static void Cec_TranCutCacheStop( Cec_TranCutCache_t * p )
{
    int i;
    Vec_Int_t * vCut;
    if ( !p ) return;
    Drw_GiaStop(p->pDrw);
    if ( p->vCuts )
    {
        Vec_PtrForEachEntry(Vec_Int_t *,p->vCuts,vCut,i) Vec_IntFreeP(&vCut);
        Vec_PtrFree(p->vCuts);
    }
    ABC_FREE(p);
}
