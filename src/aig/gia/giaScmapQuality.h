/**CFile****************************************************************

  FileName    [giaScmapQuality.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Realized seed selection and the window timing model.]

  Description [Included by giaScmap.c after the cover refiner. All mutable
  state belongs to the current mapping call or its private networks.]

***********************************************************************/

extern Abc_Ntk_t * Abc_NtkFromCellMappedGia( Gia_Man_t *, int );
extern Abc_Ntk_t * Abc_NtkPerformMfs3Rounds( Abc_Ntk_t *, Sfm_Par_t *, int );
extern void Sfm_ParSetDefault3( Sfm_Par_t * );

/**Function*************************************************************

  Synopsis    [Normalizes a private mapped network and optionally runs MFS.]

  Description [Runs mfsmap -e -R 2 -N 500 -C 1000 -M 2000 -I 10 -O 10.
  Output normalization matches write_blif before each endpoint measurement.]

  SideEffects [Consumes the private network, including on failure.]

  SeeAlso     []

***********************************************************************/
static Abc_Ntk_t * Scm_NtkPrepare( SC_Lib * pLib, Abc_Ntk_t * pNtk, int fMfs, int fNormalizeMfs )
{
    Abc_Ntk_t * pTemp;
    SC_Man * pTiming;
    if ( pNtk == NULL ) return NULL;
    pTemp = Abc_NtkDupDfs(pNtk);
    Abc_NtkDelete(pNtk);
    pNtk = pTemp;
    if ( pNtk == NULL ) return 0;
    Abc_NtkCleanup(pNtk, 0);
    if ( !Abc_NtkLogicHasSimpleCos(pNtk) ) Abc_NtkLogicMakeSimpleCos(pNtk, 0);
    pTiming = Abc_SclManStart(pLib, pNtk, 1, 1, 0, 0);
    Abc_SclManFree(pTiming);
    if ( fMfs )
    {
        Sfm_Par_t Mfs;
        int nRounds = fMfs == 2 ? 1 : 2;
        Sfm_ParSetDefault3(&Mfs);
        Mfs.fMoreEffort = 1;
        Mfs.nNodesMax = 500;
        Mfs.nBTLimit = 1000;
        Mfs.nWinSizeMax = 2000;
        Mfs.nTfiLevMax = Mfs.nTfoLevMax = 10;
        if ( fMfs == 2 )
        {
            Mfs.fMoreEffort = 0;
            Mfs.nNodesMax = 150;
            Mfs.nBTLimit = 100;
            Mfs.nWinSizeMax = 500;
            Mfs.nTfiLevMax = Mfs.nTfoLevMax = 5;
        }
        pTemp = Abc_NtkPerformMfs3Rounds(pNtk, &Mfs, nRounds);
        if ( pTemp != pNtk ) Abc_NtkDelete(pNtk);
        pNtk = pTemp;
        if ( pNtk == NULL || !fNormalizeMfs ) return pNtk;
        pTemp = Abc_NtkDupDfs(pNtk);
        Abc_NtkDelete(pNtk);
        pNtk = pTemp;
        if ( pNtk == NULL ) return 0;
        Abc_NtkCleanup(pNtk, 0);
        if ( !Abc_NtkLogicHasSimpleCos(pNtk) ) Abc_NtkLogicMakeSimpleCos(pNtk, 0);
        pTiming = Abc_SclManStart(pLib, pNtk, 1, 1, 0, 0);
        Abc_SclManFree(pTiming);
    }
    return pNtk;
}

/**Function*************************************************************

  Synopsis    [Measures a private network after optional MFS and sizing.]

  Description [Positive fMfs matches the full MFS/buffering/sizing endpoint.
  Negative values request screening: -1 omits MFS, -2 uses one bounded round.
  Both screens use limited sizing; retained finalists use the full flow.]

  SideEffects [Consumes the private network, including on failure.]

  SeeAlso     []

***********************************************************************/
static int Scm_NtkLookahead( SC_Lib * pLib, Abc_Ntk_t * pNtk, int fMfs, double * pArea, float * pDelay )
{
    Abc_Ntk_t * pTemp;
    SC_Man * pTiming;
    SC_BusPars Buffer = {0};
    SC_SizePars Size = {0};
    pNtk = Scm_NtkPrepare(pLib, pNtk, fMfs < 0 ? (fMfs == -2 ? 2 : 0) : fMfs, 1);
    if ( pNtk == NULL ) return 0;
    Buffer.GainRatio = 300;
    Buffer.Slew = Abc_SclComputeAverageSlew(pLib);
    Buffer.nDegree = 10;
    Buffer.fAddBufs = Buffer.fUseWireLoads = 1;
    pTemp = Abc_SclBufferingPerform(pNtk, pLib, &Buffer);
    Abc_NtkDelete(pNtk);
    pNtk = pTemp;
    if ( pNtk == NULL ) return 0;
    pTemp = Abc_NtkDupDfs(pNtk);
    Abc_NtkDelete(pNtk);
    pNtk = pTemp;
    if ( pNtk == NULL ) return 0;
    pTiming = Abc_SclManStart(pLib, pNtk, 1, 1, 0, 0);
    Abc_SclManFree(pTiming);
    Size.nIters = 1000;
    Size.nIterNoChange = 50;
    Size.Window = 1;
    Size.Ratio = 10;
    Size.Notches = 1000;
    Size.fUseDept = Size.fUseWireLoads = 1;
    if ( fMfs < 0 ) { Size.nIters = 20; Size.nIterNoChange = 5; }
    Abc_SclUpsizePerform(pLib, pNtk, &Size, NULL);
    memset(&Size, 0, sizeof(Size));
    Size.nIters = 5;
    Size.nIterNoChange = 50;
    Size.Notches = Size.DelayGap = 1000;
    Size.fUseDept = Size.fUseWireLoads = 1;
    if ( fMfs < 0 ) Size.nIters = 1;
    Abc_SclDnsizePerform(pLib, pNtk, &Size, NULL);
    Abc_NtkCleanup(pNtk, 0);
    if ( !Abc_NtkLogicHasSimpleCos(pNtk) ) Abc_NtkLogicMakeSimpleCos(pNtk, 0);
    pTiming = Abc_SclManStart(pLib, pNtk, 1, 1, 0, 0);
    *pArea = pTiming->SumArea;
    *pDelay = pTiming->MaxDelay;
    Abc_SclManFree(pTiming);
    Abc_NtkDelete(pNtk);
    return isfinite(*pArea) && isfinite(*pDelay) && *pArea >= 0 && *pDelay >= 0;
}

/**Function*************************************************************

  Synopsis    [Measures a seed using private-copy buffering and sizing.]

  Description []

  SideEffects [Restores the cover's mapping vector after conversion.]

  SeeAlso     []

***********************************************************************/
static int Scm_CoverLookaheadInt( Scm_Man_t * p, double * pArea, float * pDelay, int fScreen )
{
    Abc_Ntk_t * pNtk;
    Vec_Int_t * Mapping;
    int i, Ok, fMfs = Gia_ManCiNum(p->pGia) && Gia_ManAndNum(p->pGia);
    assert(p->pGia->vCellMapping == NULL);
    Scm_ManUpdateStats(p);
    Scm_ManDeriveMapping(p);
    Mapping = p->pGia->vCellMapping;
    for ( i = 0; !fScreen && i < p->nFlowCache; i++ )
        if ( Vec_IntEqual(Mapping, p->FlowCache[i].Mapping) )
        {
            *pArea = p->FlowCache[i].Qor.Area; *pDelay = p->FlowCache[i].Qor.Delay;
            Vec_IntFreeP(&p->pGia->vCellMapping);
            if ( p->pPars->fVerbose ) Abc_Print(1, "SCMAP_SEED_CACHE hit=%d\n", i);
            return 1;
        }
    pNtk = Abc_NtkFromCellMappedGia(p->pGia, 0);
    p->pGia->vCellMapping = NULL;
    if ( pNtk == NULL ) { Vec_IntFree(Mapping); return 0; }
    if ( fScreen ) fMfs = -1;
    Ok = Scm_NtkLookahead(p->pScl, pNtk, fMfs, pArea, pDelay);
    if ( Ok && !fScreen && p->nFlowCache < 8 )
    {
        Scm_FlowCache_t * pCache = p->FlowCache+p->nFlowCache++;
        pCache->Mapping = Mapping; Mapping = NULL;
        pCache->Qor.Area = *pArea; pCache->Qor.Delay = *pDelay; pCache->Qor.fValid = 1;
    }
    Vec_IntFreeP(&Mapping);
    if ( Ok && fScreen && p->nSeedCovers < SCM_SEED_CAPACITY )
    {
        int nObjs = Gia_ManObjNum(p->pGia), nLits = 2*nObjs, Id = p->nSeedCovers;
        p->nSeedCovers++;
        p->SeedModes[Id] = p->pPars->nSeedMode;
        p->pSeedObjs[Id] = ABC_ALLOC(Scm_Obj_t, nObjs);
        p->pSeedRefs[Id] = ABC_ALLOC(int, nLits);
        p->pSeedFlow[Id] = ABC_ALLOC(float, nLits);
        memcpy(p->pSeedObjs[Id], p->pNfObjs, sizeof(Scm_Obj_t)*nObjs);
        memcpy(p->pSeedRefs[Id], Vec_IntArray(&p->vMapRefs), sizeof(int)*nLits);
        memcpy(p->pSeedFlow[Id], Vec_FltArray(&p->vFlowRefs), sizeof(float)*nLits);
        p->SeedQor[Id].Area = *pArea; p->SeedQor[Id].Delay = *pDelay; p->SeedQor[Id].fValid = 1;
    }
    return Ok;
}

static int Scm_CoverLookahead( Scm_Man_t * p, double * pArea, float * pDelay )
{
    if ( p->pPars->Profile == SCM_PROFILE_T && p->pPars->MapDelayTarget > 0 )
    {
        if ( !p->nSeedCovers )
        {
            double Area;
            float Delay;
            if ( !Scm_CoverLookaheadInt(p, &Area, &Delay, 0) ||
                 !Scm_CoverLookaheadInt(p, pArea, pDelay, 1) ) return 0;
            p->TargetModelScale = Delay > 0 ? p->AffExactDelay / Delay : 1;
            p->TargetScreen = Delay > 0 ? (float)fmin(FLT_MAX,
                (double)p->pPars->MapDelayTarget * *pDelay / Delay) : p->pPars->MapDelayTarget;
            return 1;
        }
        return Scm_CoverLookaheadInt(p, pArea, pDelay, 1);
    }
    return Scm_CoverLookaheadInt(p, pArea, pDelay, p->pPars->MapDelayTarget == 0);
}

static int Scm_QorRankBetter( const Scm_Qor_t * A, const Scm_Qor_t * B, float Target )
{
    return Target > 0 ? Scm_QorTargetBetter(A->Area, A->Delay, B->Area, B->Delay, Target) :
                        A->Area*A->Delay < B->Area*B->Delay;
}

/**Function*************************************************************

  Synopsis    [Confirms screened seeds at the unchanged full-flow endpoint.]

  Description [Always retains the first refined seed as an exact fallback.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_ManConfirmSeeds( Scm_Man_t * p )
{
    int nObjs = Gia_ManObjNum(p->pGia), nLits = 2*nObjs, i, j, Id, Best = 0;
    int Order[SCM_SEED_CAPACITY], nConfirm = 3;
    Scm_Qor_t Bound = {0}, Kept = {0};
    if ( !p->nSeedCovers ) return 1;
    if ( p->pPars->Profile == SCM_PROFILE_R && p->pPars->Area > 2000 ) nConfirm = 2;
    for ( i = 0; i < p->nSeedCovers; i++ ) Order[i] = i;
    for ( i = 1; i < p->nSeedCovers; i++ ) for ( j = i+1; j < p->nSeedCovers; j++ )
        if ( Scm_QorRankBetter(p->SeedQor+Order[j], p->SeedQor+Order[i], p->TargetScreen) )
            { Id = Order[i]; Order[i] = Order[j]; Order[j] = Id; }
    for ( i = 0; i < Abc_MinInt(nConfirm, p->nSeedCovers); i++ )
    {
        Scm_Qor_t Trial = {0};
        int Accept;
        Id = Order[i];
        if ( p->pPars->Profile == SCM_PROFILE_Q && i > 1 && p->SeedQor[Id].Area >= p->SeedQor[Order[1]].Area &&
             p->SeedQor[Id].Delay >= p->SeedQor[Order[1]].Delay &&
             p->SeedQor[Id].Area*p->SeedQor[Id].Delay >
                 1.03*p->SeedQor[Order[1]].Area*p->SeedQor[Order[1]].Delay )
        {
            if ( p->pPars->fVerbose ) Abc_Print(1, "SCMAP_SEED_SKIP seed=%d reason=screen_dominated\n", Id);
            continue;
        }
        memcpy(p->pNfObjs, p->pSeedObjs[Id], sizeof(Scm_Obj_t)*nObjs);
        memcpy(Vec_IntArray(&p->vMapRefs), p->pSeedRefs[Id], sizeof(int)*nLits);
        memcpy(Vec_FltArray(&p->vFlowRefs), p->pSeedFlow[Id], sizeof(float)*nLits);
        if ( !Scm_CoverLookaheadInt(p, &Trial.Area, &Trial.Delay, 0) )
        {
            if ( !Kept.fValid ) return 0;
            Abc_Print(0, "SCMap: optional seed %d could not be measured; retaining the confirmed cover.\n", Id);
            continue;
        }
        Trial.fValid = 1;
        if ( i == 0 ) Bound = Trial;
        Accept = i == 0 || (Trial.Area <= 1.05*Bound.Area && Trial.Delay <= 1.05*Bound.Delay &&
            Trial.Area*Trial.Delay < Kept.Area*Kept.Delay);
        if ( p->TargetScreen > 0 ) Accept = i == 0 || Scm_QorRankBetter(&Trial, &Kept, p->pPars->MapDelayTarget);
        if ( p->pPars->fVerbose )
            Abc_Print(1, "SCMAP_SEED_CONFIRM seed=%d accepted=%d area=%.9g delay=%.9g screen_area=%.9g screen_delay=%.9g\n",
                Id, Accept, Trial.Area, Trial.Delay, p->SeedQor[Id].Area, p->SeedQor[Id].Delay);
        if ( Accept ) { Best = Id; Kept = Trial; }
    }
    memcpy(p->pNfObjs, p->pSeedObjs[Best], sizeof(Scm_Obj_t)*nObjs);
    memcpy(Vec_IntArray(&p->vMapRefs), p->pSeedRefs[Best], sizeof(int)*nLits);
    memcpy(Vec_FltArray(&p->vFlowRefs), p->pSeedFlow[Best], sizeof(float)*nLits);
    p->pPars->Quality = Kept;
    p->pPars->nSeedMode = p->SeedModes[Best];
    Scm_ManUpdateStats(p);
    return Scm_ManAffElaTimeCover(p);
}

/**Function*************************************************************

  Synopsis    [Measures a window candidate through the fixed downstream flow.]

  Description [Does not replace the frame network or the input cover.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Scm_WinModelLookahead( Gia_Man_t * pGia, int fMfs, double * pArea, float * pDelay )
{
    Abc_Ntk_t * pNtk = Abc_NtkFromCellMappedGia(pGia, 0);
    if ( pNtk == NULL ) return 0;
    return Scm_NtkLookahead((SC_Lib *)Abc_FrameReadLibScl(), pNtk, fMfs, pArea, pDelay);
}

/**Function*************************************************************

  Synopsis    [Refines the alternate seed and compares realized area-delay products.]

  Description []

  SideEffects [Restores full timing and statistics for the selected cover.]

  SeeAlso     []

***********************************************************************/
static int Scm_ManSelectSeed( Scm_Man_t * p, Scm_Obj_t * pSeed,
    int * pSeedRefs, float * pSeedFlow, int Seed, Scm_Qor_t * pBound )
{
    int nObjs = Gia_ManObjNum(p->pGia), nLits = 2*nObjs, OldSeed = p->pPars->nSeedMode;
    Scm_Obj_t * pSave;
    int * pRefs;
    float * pFlow;
    float OldDelay, NewDelay = 0;
    float OldModel = p->AffExactDelay;
    float OldLoad = p->pPars->SeedLoad, OldGain = p->pPars->SeedGain, OldRelax = p->pPars->RefineRelax;
    float OldTarget = p->pPars->ModelDelayTarget;
    double OldArea, NewArea = 0;
    int Ok, Accept = 0, OldDeep = p->pPars->fDeep;
    if ( p->nSeedCovers >= SCM_SEED_CAPACITY ) return 1;
    if ( p->pPars->Quality.fValid )
        { OldArea = p->pPars->Quality.Area; OldDelay = p->pPars->Quality.Delay; }
    else if ( !Scm_CoverLookahead(p, &OldArea, &OldDelay) ) return 0;
    if ( pBound && !pBound->fValid )
        { pBound->Area = OldArea; pBound->Delay = OldDelay; pBound->fValid = 1; }
    pSave = ABC_ALLOC(Scm_Obj_t, nObjs);
    pRefs = ABC_ALLOC(int, nLits);
    pFlow = ABC_ALLOC(float, nLits);
    memcpy(pSave, p->pNfObjs, sizeof(Scm_Obj_t)*nObjs);
    memcpy(pRefs, Vec_IntArray(&p->vMapRefs), sizeof(int)*nLits);
    memcpy(pFlow, Vec_FltArray(&p->vFlowRefs), sizeof(float)*nLits);
    p->pPars->nSeedMode = Seed & 1;
    p->pPars->fDeep = Seed >= 6;
    p->pPars->RefineRelax = Seed >= 6 ? 1.02f : Seed >= 4 ? 1.05f : OldRelax;
    // Keep the relaxed seeds unconstrained; calibrate the others at the realized endpoint.
    if ( p->pPars->MapDelayTarget > 0 )
    {
        double Target = OldDelay > 0 && OldModel > 0 ?
            (double)p->pPars->MapDelayTarget * OldModel / OldDelay : p->pPars->MapDelayTarget;
        if ( p->TargetModelScale > 0 ) Target = (double)p->pPars->MapDelayTarget * p->TargetModelScale;
        p->pPars->ModelDelayTarget = Seed >= 4 ? 0 : (float)fmin(Target, FLT_MAX);
        if ( p->pPars->fVerbose )
            Abc_Print(1, "SCMAP_SEED_TARGET seed=%d target=%.9g model_target=%.9g model_delay=%.9g delay=%.9g\n",
                Seed, p->pPars->MapDelayTarget, p->pPars->ModelDelayTarget, OldModel, OldDelay);
    }
    Ok = 1;
    if ( pSeed )
    {
        memcpy(p->pNfObjs, pSeed, sizeof(Scm_Obj_t)*nObjs);
        memcpy(Vec_IntArray(&p->vMapRefs), pSeedRefs, sizeof(int)*nLits);
    }
    else
    {
        memset(p->pNfObjs, 0, sizeof(Scm_Obj_t)*nObjs);
        Vec_IntFill(&p->vMapRefs, nLits, 0);
        Scm_ObjMatchD(p, 0, 0)->Gate = 0;
        Scm_ObjMatchD(p, 0, 1)->Gate = 1;
        p->pPars->SeedLoad = Seed >= 2 ? 4.0f : OldLoad;
        p->pPars->SeedGain = Seed == 2 ? 4.0f : OldGain;
    }
    memcpy(Vec_FltArray(&p->vFlowRefs), pSeedFlow, sizeof(float)*nLits);
    if ( !pSeed )
    {
        p->pPars->fUseRiseFallAll = 0;
        Ok = Scm_ManAffPairedSeed(p, OldModel);
        p->pPars->fUseRiseFallAll = 1;
    }
    Ok = Ok && Scm_ManAffElaTimeCover(p) && Scm_ManRefineCover(p);
    if ( Ok ) Ok = Scm_CoverLookahead(p, &NewArea, &NewDelay);
    if ( Ok )
    {
        Accept = NewDelay <= 1.05 * (pBound ? pBound->Delay : OldDelay) &&
            NewArea <= 1.05 * (pBound ? pBound->Area : OldArea) &&
            NewDelay * NewArea < OldDelay * OldArea;
        if ( p->pPars->MapDelayTarget > 0 )
            Accept = Scm_QorTargetBetter(NewArea, NewDelay, OldArea, OldDelay,
                p->TargetScreen > 0 ? p->TargetScreen : p->pPars->MapDelayTarget);
        if ( p->pPars->fVerbose )
            Abc_Print(1, "%s seed=%d accepted=%d old_area=%.9g area=%.9g old_delay=%.9g delay=%.9g old_model_delay=%.9g model_delay=%.9g\n",
                p->nSeedCovers ? "SCMAP_SEED_SCREEN" : "SCMAP_SEED_QUALITY",
                Seed, Accept, OldArea, NewArea, OldDelay, NewDelay, OldModel, p->AffExactDelay);
    }
    if ( !Accept )
    {
        memcpy(p->pNfObjs, pSave, sizeof(Scm_Obj_t)*nObjs);
        memcpy(Vec_IntArray(&p->vMapRefs), pRefs, sizeof(int)*nLits);
        memcpy(Vec_FltArray(&p->vFlowRefs), pFlow, sizeof(float)*nLits);
        p->pPars->nSeedMode = OldSeed;
        if ( !Ok ) Abc_Print(0, "SCMap: alternate seed %d failed; retaining the selected cover.\n", Seed);
        Ok = Scm_ManAffElaTimeCover(p);
    }
    p->pPars->SeedLoad = OldLoad;
    p->pPars->SeedGain = OldGain;
    p->pPars->RefineRelax = OldRelax;
    p->pPars->fDeep = OldDeep;
    p->pPars->ModelDelayTarget = OldTarget;
    ABC_FREE(pSave); ABC_FREE(pRefs); ABC_FREE(pFlow);
    p->pPars->Quality.Area = Accept ? NewArea : OldArea;
    p->pPars->Quality.Delay = Accept ? NewDelay : OldDelay;
    p->pPars->Quality.fValid = Ok;
    Scm_ManUpdateStats(p);
    return Ok;
}

typedef struct Scm_WinModel_t_
{
    Scm_Par_t Pars;
    Gia_Man_t * pDummy;
    Scm_Man_t * pScm;
} Scm_WinModel_t;

/**Function*************************************************************

  Synopsis    [Creates a per-call library model for physical-cell windows.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void * Scm_WinModelStartProfile( Scm_Profile_t Profile )
{
    Scm_WinModel_t * p = ABC_CALLOC(Scm_WinModel_t, 1);
    Scm_ManSetDefaultPars(&p->Pars);
    p->Pars.fQuality = 1;
    p->Pars.Profile = Profile;
    p->pDummy = Gia_ManStart(16);
    Gia_ManAppendCi(p->pDummy);
    Gia_ManAppendCo(p->pDummy, 2);
    p->pScm = Scm_StoCreate(p->pDummy, &p->Pars);
    if ( p->pScm == NULL ) { Gia_ManStop(p->pDummy); ABC_FREE(p); return NULL; }
    return p;
}

/**Function*************************************************************

  Synopsis    [Releases the window model and its private manager.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Scm_WinModelStop( void * pModel )
{
    Scm_WinModel_t * p = (Scm_WinModel_t *)pModel;
    if ( p == NULL ) return;
    Scm_StoDelete(p->pScm);
    Gia_ManStop(p->pDummy);
    ABC_FREE(p);
}

/**Function*************************************************************

  Synopsis    [Returns the modeled input load of a candidate cell pin.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Scm_RfPair_t Scm_WinModelCap( void * pModel, int Gate, int Pin )
{
    Scm_Man_t * p = ((Scm_WinModel_t *)pModel)->pScm;
    assert(Gate >= 0 && Gate < p->nCells);
    assert(Pin >= 0 && Pin < (int)p->pCells[Gate].nFanins);
    return p->pFamilyCapsRf[Scm_ManSclCell(p, p->pCells+Gate)->Id * NF_LEAF_MAX + Pin];
}

/**Function*************************************************************

  Synopsis    [Returns virtual buffering and upsizing area at a load.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
double Scm_WinModelCost( void * pModel, int Gate, float Load )
{
    Scm_Man_t * p = ((Scm_WinModel_t *)pModel)->pScm;
    if ( !p->pCells[Gate].nFanins ) return 0;
    Scm_ManEnsureEnv(p, p->pCells+Gate);
    return (double)Scm_AffPwlEval(p->pBufferCosts+Gate, Load)/SCL_NUM;
}

/**Function*************************************************************

  Synopsis    [Propagates cell arrival and slew through the electrical model.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Scm_WinModelCell( void * pModel, int Gate, Scm_RfPair_t Load,
    Scm_RfPair_t * pArrivals, Scm_RfPair_t * pSlews, Scm_RfPair_t * pArrival, Scm_RfPair_t * pSlew )
{
    Scm_Man_t * p = ((Scm_WinModel_t *)pModel)->pScm;
    Scm_RfPair_t Arrival = {{-FLT_MAX, -FLT_MAX}}, Slew = {{0, 0}};
    Mio_Cell2_t * pCell;
    int k;
    assert(Gate >= 0 && Gate < p->nCells);
    pCell = p->pCells+Gate;
    for ( k = 0; k < (int)pCell->nFanins; k++ )
    {
        Scm_LinArc_t Temp, * pArc = Scm_ManAffArcAtLoadRf(p, pCell, k, Load, &Temp);
        if ( pArc == NULL || !pArc->fValid || p->fEnvError ) return 0;
        Scm_ManRfArcAccumulate(pArc, Load, pArrivals[k], pSlews[k], &Arrival, &Slew);
    }
    if ( !pCell->nFanins ) Arrival.Value[0] = Arrival.Value[1] = 0;
    *pArrival = Arrival;
    *pSlew = Slew;
    return isfinite(Arrival.Value[0]) && isfinite(Arrival.Value[1]) &&
           isfinite(Slew.Value[0]) && isfinite(Slew.Value[1]);
}

/**Function*************************************************************

  Synopsis    [Propagates required times using the actual fixed-load cell arc.]

  Description [Slew is held at its current value for root ranking only.
  Every candidate is subsequently retimed, including changed loads and slews.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Scm_WinModelRequired( void * pModel, int Gate, int Pin, Scm_RfPair_t Load,
    Scm_RfPair_t Slew, Scm_RfPair_t Required, Scm_RfPair_t * pRequired )
{
    Scm_Man_t * p = ((Scm_WinModel_t *)pModel)->pScm;
    Scm_LinArc_t Temp, * pArc = Scm_ManAffArcAtLoadRf(p, p->pCells+Gate, Pin, Load, &Temp);
    int In, Out;
    if ( pArc == NULL || !pArc->fValid || p->fEnvError ) return 0;
    for ( Out = 0; Out < 2; Out++ )
        for ( In = 0; In < 2; In++ )
        {
            float Cost;
            if ( pArc->TimingSense != sc_ts_Non &&
                 !(pArc->TimingSense == sc_ts_Pos && In == Out) &&
                 !(pArc->TimingSense == sc_ts_Neg && In != Out) ) continue;
            Cost = Scm_ManRfDelay(pArc, Out, Load.Value[Out], Slew.Value[In]);
            if ( !isfinite(Cost) ) return 0;
            pRequired->Value[In] = Abc_MinFloat(pRequired->Value[In], Rq_Back(Required.Value[Out], Cost));
        }
    return 1;
}
