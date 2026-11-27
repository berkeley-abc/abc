/**CFile****************************************************************

  FileName    [giaScmapQuality.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Measured seed selection and the window timing model.]

  Description [Included by giaScmap.c after the cover refiner. All mutable
  state belongs to the current mapping call or its private networks.]

  Author      [Anqi Lu]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 2026.]

  Revision    [$Id: giaScmapQuality.h,v 1.00 2026/11/27 00:00:00 anqilu Exp $]

***********************************************************************/

extern Abc_Ntk_t * Abc_NtkFromCellMappedGia( Gia_Man_t *, int );

/**Function*************************************************************

  Synopsis    [Normalizes a private mapped network.]

  Description [Takes the DFS copy, cleaned up with simple outputs as
  write_blif writes it.]

  SideEffects [Consumes the private network, including on failure.]

  SeeAlso     []

***********************************************************************/
static Abc_Ntk_t * Scm_NtkNormalize( Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pTemp = Abc_NtkDupDfs(pNtk);
    Abc_NtkDelete(pNtk);
    if ( pTemp == NULL ) return NULL;
    Abc_NtkCleanup(pTemp, 0);
    if ( !Abc_NtkLogicHasSimpleCos(pTemp) ) Abc_NtkLogicMakeSimpleCos(pTemp, 0);
    return pTemp;
}

/**Function*************************************************************

  Synopsis    [Measures a private network after buffering.]

  Description [Runs buffer -c and reports area and delay with stime -c.]

  SideEffects [Consumes the private network, including on failure.]

  SeeAlso     []

***********************************************************************/
static int Scm_NtkLookahead( SC_Lib * pLib, Abc_Ntk_t * pNtk, double * pArea, float * pDelay )
{
    Abc_Ntk_t * pTemp;
    SC_Man * pTiming;
    SC_BusPars Buffer = {0};
    if ( pNtk == NULL || (pNtk = Scm_NtkNormalize(pNtk)) == NULL ) return 0;
    // timing the network once records its wire-load model in it, as the flow's stime does
    Abc_SclManFree( Abc_SclManStart(pLib, pNtk, 1, 1, 0, 0) );
    Buffer.GainRatio = 300;
    Buffer.Slew = Abc_SclComputeAverageSlew(pLib);
    Buffer.nDegree = 10;
    Buffer.fAddBufs = Buffer.fUseWireLoads = 1;
    pTemp = Abc_SclBufferingPerform(pNtk, pLib, &Buffer);
    Abc_NtkDelete(pNtk);
    if ( pTemp == NULL || (pNtk = Scm_NtkNormalize(pTemp)) == NULL ) return 0;
    pTiming = Abc_SclManStart(pLib, pNtk, 1, 1, 0, 0);
    *pArea = pTiming->SumArea;
    *pDelay = pTiming->MaxDelay;
    Abc_SclManFree(pTiming);
    Abc_NtkDelete(pNtk);
    return isfinite(*pArea) && isfinite(*pDelay) && *pArea >= 0 && *pDelay >= 0;
}

/**Function*************************************************************

  Synopsis    [Measures the current cover after buffering.]

  Description []

  SideEffects [Leaves the GIA without a cell mapping.]

  SeeAlso     []

***********************************************************************/
static int Scm_CoverLookahead( Scm_Man_t * p, double * pArea, float * pDelay )
{
    Abc_Ntk_t * pNtk;
    assert(p->pGia->vCellMapping == NULL);
    Scm_ManDeriveMapping(p);
    pNtk = Abc_NtkFromCellMappedGia(p->pGia, 0);
    Vec_IntFreeP(&p->pGia->vCellMapping);
    if ( pNtk == NULL ) return 0;
    return Scm_NtkLookahead(p->pScl, pNtk, pArea, pDelay);
}

/**Function*************************************************************

  Synopsis    [Ranks measured covers by the target rule under a target, else by area-
  delay product.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_QorRankBetter( const Scm_Qor_t * A, const Scm_Qor_t * B, float Target )
{
    return Target > 0 ? Scm_QorTargetBetter(A->Area, A->Delay, B->Area, B->Delay, Target) :
                        A->Area*A->Delay < B->Area*B->Delay;
}

/**Function*************************************************************

  Synopsis    [Measures a mapped cover after buffering.]

  Description [Does not replace the frame network or the input cover.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Scm_WinModelLookahead( Gia_Man_t * pGia, double * pArea, float * pDelay )
{
    Abc_Ntk_t * pNtk = Abc_NtkFromCellMappedGia(pGia, 0);
    if ( pNtk == NULL ) return 0;
    return Scm_NtkLookahead((SC_Lib *)Abc_FrameReadLibScl(), pNtk, pArea, pDelay);
}

/**Function*************************************************************

  Synopsis    [Refines another seed and keeps the better measured cover.]

  Description [Seed is the seed (0 or 1). With pSeed, the saved seed
  cover is refined; otherwise the seed is rebuilt, under a delay target toward
  a model target calibrated by the measured delay. Both covers are measured
  after buffering. The new one is kept if it is within 5% of *pBound's area
  and delay and has a smaller area-delay product, or, under a delay target,
  if it ranks better against the target.]

  SideEffects [Leaves the kept cover timed; sets pPars->Quality to its measurement.]

  SeeAlso     []

***********************************************************************/
static int Scm_ManSelectSeed( Scm_Man_t * p, Scm_Obj_t * pSeed, int * pSeedRefs, float * pSeedFlow, int Seed, Scm_Qor_t * pBound )
{
    int nObjs = Gia_ManObjNum(p->pGia), nLits = 2*nObjs;
    Scm_Obj_t * pSave;
    int * pRefs;
    float * pFlow;
    float OldDelay, NewDelay = 0;
    float OldModel = p->ModelDelay;
    float OldTarget = p->pPars->ModelDelayTarget;
    double OldArea, NewArea = 0;
    int Ok, Accept = 0;
    if ( p->pPars->Quality.fValid )
        { OldArea = p->pPars->Quality.Area; OldDelay = p->pPars->Quality.Delay; }
    else if ( !Scm_CoverLookahead(p, &OldArea, &OldDelay) ) return 0;
    if ( pBound && !pBound->fValid )
        { pBound->Area = OldArea; pBound->Delay = OldDelay; pBound->fValid = 1; }
    pSave = ABC_ALLOC(Scm_Obj_t, nObjs);
    pRefs = ABC_ALLOC(int, nLits);
    pFlow = ABC_ALLOC(float, nLits);
    memcpy(pSave, p->pObjs, sizeof(Scm_Obj_t)*nObjs);
    memcpy(pRefs, Vec_IntArray(&p->vMapRefs), sizeof(int)*nLits);
    memcpy(pFlow, Vec_FltArray(&p->vFlowRefs), sizeof(float)*nLits);
    // calibrate the model target at the measured delay
    if ( p->pPars->MapDelayTarget > 0 )
    {
        double Target = OldDelay > 0 && OldModel > 0 ?
            (double)p->pPars->MapDelayTarget * OldModel / OldDelay : p->pPars->MapDelayTarget;
        p->pPars->ModelDelayTarget = (float)fmin(Target, FLT_MAX);
        if ( p->pPars->fVerbose )
            Abc_Print(1, "SCMAP_SEED_TARGET seed=%d target=%.9g model_target=%.9g model_delay=%.9g delay=%.9g\n",
                Seed, p->pPars->MapDelayTarget, p->pPars->ModelDelayTarget, OldModel, OldDelay);
    }
    if ( pSeed )
    {
        memcpy(p->pObjs, pSeed, sizeof(Scm_Obj_t)*nObjs);
        memcpy(Vec_IntArray(&p->vMapRefs), pSeedRefs, sizeof(int)*nLits);
    }
    else
    {
        memset(p->pObjs, 0, sizeof(Scm_Obj_t)*nObjs);
        Vec_IntFill(&p->vMapRefs, nLits, 0);
        Scm_ObjMatch(p, 0, 0)->Gate = 0;
        Scm_ObjMatch(p, 0, 1)->Gate = 1;
    }
    memcpy(Vec_FltArray(&p->vFlowRefs), pSeedFlow, sizeof(float)*nLits);
    Ok = (pSeed || Scm_ManSeedBuild(p, Seed, OldModel)) && Scm_ManTimeCover(p) && Scm_ManRefineCover(p) &&
         Scm_CoverLookahead(p, &NewArea, &NewDelay);
    if ( Ok )
    {
        Accept = p->pPars->MapDelayTarget > 0 ?
            Scm_QorTargetBetter(NewArea, NewDelay, OldArea, OldDelay, p->pPars->MapDelayTarget) :
            NewDelay <= 1.05 * (pBound ? pBound->Delay : OldDelay) &&
            NewArea <= 1.05 * (pBound ? pBound->Area : OldArea) &&
            NewDelay * NewArea < OldDelay * OldArea;
        if ( p->pPars->fVerbose )
            Abc_Print(1, "SCMAP_SEED_SCREEN seed=%d accepted=%d old_area=%.9g area=%.9g old_delay=%.9g delay=%.9g old_model_delay=%.9g model_delay=%.9g\n",
                Seed, Accept, OldArea, NewArea, OldDelay, NewDelay, OldModel, p->ModelDelay);
    }
    if ( !Accept )
    {
        memcpy(p->pObjs, pSave, sizeof(Scm_Obj_t)*nObjs);
        memcpy(Vec_IntArray(&p->vMapRefs), pRefs, sizeof(int)*nLits);
        memcpy(Vec_FltArray(&p->vFlowRefs), pFlow, sizeof(float)*nLits);
        if ( !Ok ) Abc_Print(0, "SCMap: alternate seed %d failed; retaining the selected cover.\n", Seed);
        Ok = Scm_ManTimeCover(p);
    }
    p->pPars->ModelDelayTarget = OldTarget;
    ABC_FREE(pSave); ABC_FREE(pRefs); ABC_FREE(pFlow);
    p->pPars->Quality.Area = Accept ? NewArea : OldArea;
    p->pPars->Quality.Delay = Accept ? NewDelay : OldDelay;
    p->pPars->Quality.fValid = Ok;
    return Ok;
}

// A cell's rise/fall pin delays and output slews at one load, the values
// Scm_PwlEval returns. Each cell keeps its most recently used load: window
// candidates rescore the same cell at the root's load many times. Each cover
// node keeps the gate and load it was last timed with: a trial retimes the
// unchanged loads of its fanout cone, whose responses are already known.
typedef struct Scm_WinArcs_t_ Scm_WinArcs_t;
struct Scm_WinArcs_t_
{
    Scm_RfPair_t    Load;
    float           Delay[SCM_LEAF_MAX][2];
    float           Slew[2];
    int             Gate;
    int             fValid;
};

typedef struct Scm_WinModel_t_ Scm_WinModel_t;
struct Scm_WinModel_t_
{
    Scm_Par_t       Pars;
    Gia_Man_t *     pDummy;         // the one-output AIG the library model is built on
    Scm_Man_t *     pScm;           // the library model
    Scm_WinArcs_t * pArcs;          // per cell: its responses at its last load
    Scm_WinArcs_t * pNodes;         // per cover node: its responses at its last gate and load
    int             nNodes;
};

/**Function*************************************************************

  Synopsis    [Creates a per-call library model for physical-cell windows.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void * Scm_WinModelStart( void )
{
    Scm_WinModel_t * p = ABC_CALLOC(Scm_WinModel_t, 1);
    Scm_ManSetDefaultPars(&p->Pars);
    p->Pars.fQuality = 1;
    p->pDummy = Gia_ManStart(16);
    Gia_ManAppendCi(p->pDummy);
    Gia_ManAppendCo(p->pDummy, 2);
    p->pScm = Scm_StoCreate(p->pDummy, &p->Pars);
    if ( p->pScm == NULL ) { Gia_ManStop(p->pDummy); ABC_FREE(p); return NULL; }
    p->pArcs = ABC_CALLOC(Scm_WinArcs_t, p->pScm->nCells);
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
    ABC_FREE(p->pArcs);
    ABC_FREE(p->pNodes);
    ABC_FREE(p);
}

/**Function*************************************************************

  Synopsis    [Gives each of nNodes cover nodes its own arc responses.]

  Description [Node arguments of Scm_WinModelCell below nNodes then use
  them; others use the cell's. Returns 0 if they cannot be allocated.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Scm_WinModelNodes( void * pModel, int nNodes )
{
    Scm_WinModel_t * p = (Scm_WinModel_t *)pModel;
    ABC_FREE(p->pNodes);
    p->nNodes = 0;
    if ( nNodes <= 0 ) return 0;
    p->pNodes = ABC_CALLOC(Scm_WinArcs_t, nNodes);
    if ( p->pNodes == NULL ) return 0;
    p->nNodes = nNodes;
    return 1;
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
    return p->pFamilyRfCaps[Scm_ManSclCell(p, p->pCells+Gate)->Id * SCM_LEAF_MAX + Pin];
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
    return (double)Scm_PwlEval(p->pEnvCosts+Gate, Load)/SCL_NUM;
}

/**Function*************************************************************

  Synopsis    [Scm_ManArcAtLoad's load-dependent responses of every pin of Gate at
  Load: the node's cached ones (see Scm_WinModelNodes) or, for a
  negative Node, the cell's, recomputed only for a different gate or
  load. Requires p->pEnvDelays and pins; returns NULL on an envelope
  error.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Scm_WinArcs_t * Scm_WinModelArcs( Scm_WinModel_t * pM, int Node, int Gate, Scm_RfPair_t Load )
{
    Scm_Man_t * p = pM->pScm;
    Mio_Cell2_t * pCell = p->pCells+Gate;
    Scm_WinArcs_t * pC = Node >= 0 && Node < pM->nNodes ? pM->pNodes + Node : pM->pArcs + Gate;
    int k, t;
    Scm_ManEnsureEnv(p, pCell);
    if ( p->fEnvError ) return NULL;
    if ( !pC->fValid || pC->Gate != Gate || memcmp(&pC->Load, &Load, sizeof(Load)) )
    {
        for ( t = 0; t < 2; t++ )
            pC->Slew[t] = Scm_PwlEval(p->pEnvSlews+2*pCell->Id+t, Load.Value[t]);
        for ( k = 0; k < (int)pCell->nFanins; k++ )
            for ( t = 0; t < 2; t++ )
                pC->Delay[k][t] = Scm_PwlEval(p->pEnvDelays+2*(pCell->Id*SCM_LEAF_MAX+k)+t, Load.Value[t]);
        pC->Load = Load;
        pC->Gate = Gate;
        pC->fValid = 1;
    }
    return pC;
}

/**Function*************************************************************

  Synopsis    [Pin's arc with the cached responses in place of its load terms.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_WinArcAt( Scm_Arc_t * pArc, Scm_WinArcs_t * pC, int Pin )
{
    int t;
    for ( t = 0; t < 2; t++ )
    {
        pArc->RfDelay0[t] = pC->Delay[Pin][t];
        pArc->RfDelayLoad[t] = 0;
        pArc->RfSlew0[t] = pC->Slew[t];
        pArc->RfSlewLoad[t] = 0;
    }
}

/**Function*************************************************************

  Synopsis    [Propagates cell arrival and slew through the electrical model.]

  Description [Node selects the cached arc responses: a node's own (see
  Scm_WinModelNodes), or the cell's for a negative Node.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Scm_WinModelCell( void * pModel, int Node, int Gate, Scm_RfPair_t Load,
    Scm_RfPair_t * pArrivals, Scm_RfPair_t * pSlews, Scm_RfPair_t * pArrival, Scm_RfPair_t * pSlew )
{
    Scm_WinModel_t * pM = (Scm_WinModel_t *)pModel;
    Scm_Man_t * p = pM->pScm;
    Scm_RfPair_t Arrival = {{-FLT_MAX, -FLT_MAX}}, Slew = {{0, 0}};
    Mio_Cell2_t * pCell;
    int k;
    assert(Gate >= 0 && Gate < p->nCells);
    pCell = p->pCells+Gate;
    if ( pCell->nFanins )
    {
        // Scm_ManArcAtLoad for every pin, evaluated once per gate and load
        Scm_WinArcs_t * pC = Scm_WinModelArcs(pM, Node, Gate, Load);
        if ( pC == NULL ) return 0;
        for ( k = 0; k < (int)pCell->nFanins; k++ )
        {
            Scm_Arc_t Arc, * pBase = Scm_ManArc(p, pCell, k);
            if ( pBase == NULL || !pBase->fValid ) return 0;
            Arc = *pBase;
            Scm_WinArcAt( &Arc, pC, k );
            Scm_ManRfArcAccumulate(&Arc, Load, pArrivals[k], pSlews[k], &Arrival, &Slew);
        }
    }
    else Arrival.Value[0] = Arrival.Value[1] = 0;
    *pArrival = Arrival;
    *pSlew = Slew;
    return isfinite(Arrival.Value[0]) && isfinite(Arrival.Value[1]) &&
           isfinite(Slew.Value[0]) && isfinite(Slew.Value[1]);
}

/**Function*************************************************************

  Synopsis    [Propagates required times using the actual fixed-load cell arc.]

  Description [Slew is held at its current value for root ranking only.
  Every candidate is subsequently retimed, including changed loads and slews.
  Node selects the cached arc responses as in Scm_WinModelCell.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Scm_WinModelRequired( void * pModel, int Node, int Gate, int Pin, Scm_RfPair_t Load,
    Scm_RfPair_t Slew, Scm_RfPair_t Required, Scm_RfPair_t * pRequired )
{
    Scm_WinModel_t * pM = (Scm_WinModel_t *)pModel;
    Scm_Man_t * p = pM->pScm;
    Scm_WinArcs_t * pC = Scm_WinModelArcs(pM, Node, Gate, Load);
    Scm_Arc_t Temp, * pArc;
    int In, Out;
    if ( pC == NULL || (pArc = Scm_ManArc(p, p->pCells+Gate, Pin)) == NULL || !pArc->fValid ) return 0;
    Temp = *pArc; pArc = &Temp;
    Scm_WinArcAt( pArc, pC, Pin );
    for ( Out = 0; Out < 2; Out++ )
        for ( In = 0; In < 2; In++ )
        {
            float Cost;
            if ( pArc->TimingSense != sc_ts_Non &&
                 !(pArc->TimingSense == sc_ts_Pos && In == Out) &&
                 !(pArc->TimingSense == sc_ts_Neg && In != Out) ) continue;
            Cost = Scm_ManRfDelay(pArc, Out, Load.Value[Out], Slew.Value[In]);
            if ( !isfinite(Cost) ) return 0;
            pRequired->Value[In] = Abc_MinFloat(pRequired->Value[In], Scm_PruneBack(Required.Value[Out], Cost));
        }
    return 1;
}
