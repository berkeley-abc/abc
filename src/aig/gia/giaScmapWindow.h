/**CFile****************************************************************

  FileName    [giaScmapWindow.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Shared-cell windows evaluated by SCMap's electrical model.]

  Description [Included by giaNf3.c to reuse its cell matching, decomposition
  and exact reference accounting. Ordinary NF3 recovery remains unchanged.]

***********************************************************************/

typedef struct Scm_WinState_t_
{
    Scm_RfPair_t Arrival, Slew, Load, Required;
} Scm_WinState_t;
typedef struct Scm_WinMetric_t_
{
    word Area;
    double Electrical, Pressure, EstimatedArea, RealArea;
    float RealDelay;
} Scm_WinMetric_t;
typedef Nf3_Enum_t Scm_WinList_t;
typedef struct Scm_WinRoot_t_ { int Id; word Area; double Path; } Scm_WinRoot_t;

/**Function*************************************************************

  Synopsis    [Orders candidates by exact area gain and stable implementation keys.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_WinPlanCompare( const void * pA, const void * pB )
{
    const Nf3_Plan_t * A = (const Nf3_Plan_t *)pA;
    const Nf3_Plan_t * B = (const Nf3_Plan_t *)pB;
    int k;
    if ( A->Gain != B->Gain ) return A->Gain > B->Gain ? -1 : 1;
    if ( A->Gate != B->Gate ) return A->Gate < B->Gate ? -1 : 1;
    if ( A->Slot != B->Slot ) return A->Slot < B->Slot ? -1 : 1;
    if ( A->ChildGate != B->ChildGate ) return A->ChildGate < B->ChildGate ? -1 : 1;
    if ( A->nFans != B->nFans ) return A->nFans < B->nFans ? -1 : 1;
    for ( k = 0; k < 6; k++ )
    {
        if ( A->Fans[k] != B->Fans[k] ) return A->Fans[k] < B->Fans[k] ? -1 : 1;
        if ( A->ChildFans[k] != B->ChildFans[k] ) return A->ChildFans[k] < B->ChildFans[k] ? -1 : 1;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Keeps a bounded deterministic list of candidate implementations.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_WinPlanAdd( Nf3_Enum_t * p, Nf3_Plan_t * Plan )
{
    int i, Worst = 0;
    p->Generated++;
    for ( i = 0; i < p->Count; i++ )
        if ( !Scm_WinPlanCompare(p->Plans+i, Plan) ) return;
    if ( p->Count < p->Limit ) { p->Plans[p->Count++] = *Plan; return; }
    for ( i = 1; i < p->Count; i++ )
        if ( Scm_WinPlanCompare(p->Plans+Worst, p->Plans+i) < 0 ) Worst = i;
    if ( Scm_WinPlanCompare(Plan, p->Plans+Worst) < 0 ) p->Plans[Worst] = *Plan;
}

/**Function*************************************************************

  Synopsis    [Enumerates bounded windows using NF3's shared candidate generator.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_WinEnumerate( Nf3_Man_t * p, int Root, Scm_WinList_t * List, word Extra, int fTiming )
{
    int Nodes[NF3_WINDOW_MAX] = {Root}, Leaves[NF3_LEAF_MAX], nNodes = 1, nLeaves = 0, k;
    Nf3_Obj_t * Obj = p->Objs+Root;
    List->Extra = Extra; List->fEqual = fTiming;
    List->Count = 0;
    for ( k = 0; k < Obj->nFans; k++ )
        if ( Obj->Fans[k] >= 2 && Nf3_Find(Leaves, nLeaves, Obj->Fans[k]) < 0 ) Leaves[nLeaves++] = Obj->Fans[k];
    do { Nf3_Try(p, Root, Nodes, nNodes, Leaves, nLeaves, NULL, List); }
    while ( Nf3_Expand(p, Nodes, &nNodes, Leaves, &nLeaves) );
    qsort(List->Plans, List->Count, sizeof(Nf3_Plan_t), Scm_WinPlanCompare);
}

/**Function*************************************************************

  Synopsis    [Recomputes all live loads, arrival times, slews and modeled area.]

  Description [Pressure uses the round's fixed threshold, not the trial's delay.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_WinMeasure( Nf3_Man_t * p, void * Model, Scm_WinState_t * State,
    int * Refs, double Threshold, Scm_WinMetric_t * Metric )
{
    int i, k, t, Id;
    memset(State, 0, sizeof(Scm_WinState_t)*p->nObjs);
    memset(Refs, 0, sizeof(int)*p->nObjs);
    memset(Metric, 0, sizeof(*Metric));
    Vec_IntForEachEntry(p->Outputs, Id, i) Refs[Id]++;
    for ( i = p->nObjs-1; i >= 2; i-- ) if ( Refs[i] )
        for ( k = 0; k < p->Objs[i].nFans; k++ )
        {
            Id = p->Objs[i].Fans[k];
            if ( Id < 0 || Id >= i ) return 0;
            Refs[Id]++;
        }
    for ( i = 0; i < p->nObjs; i++ )
        if ( Refs[i] != p->Objs[i].Refs ) return 0;
    for ( i = 2; i < p->nObjs; i++ ) if ( Refs[i] && p->Objs[i].Gate >= 0 )
    {
        Nf3_Obj_t * Obj = p->Objs+i;
        Metric->Area += Nf3_Area(p, i);
        if ( Obj->nFans != (int)p->Cells[Obj->Gate].nFanins ) return 0;
        for ( k = 0; k < Obj->nFans; k++ )
        {
            Scm_RfPair_t Cap = Scm_WinModelCap(Model, Obj->Gate, k);
            for ( t = 0; t < 2; t++ ) State[Obj->Fans[k]].Load.Value[t] += Cap.Value[t];
        }
    }
    // Aliases are wires, not extra cells: transfer all of their sink load.
    for ( i = p->nObjs-1; i >= 2; i-- ) if ( Refs[i] && p->Objs[i].Gate == NF3_ALIAS )
        for ( t = 0; t < 2; t++ ) State[p->Objs[i].Fans[0]].Load.Value[t] += State[i].Load.Value[t];
    for ( i = 2; i < p->nObjs; i++ ) if ( Refs[i] && p->Objs[i].Gate != NF3_CI )
    {
        Nf3_Obj_t * Obj = p->Objs+i;
        Scm_RfPair_t Arrivals[6], Slews[6];
        if ( Obj->Gate == NF3_ALIAS )
        {
            State[i].Arrival = State[Obj->Fans[0]].Arrival;
            State[i].Slew = State[Obj->Fans[0]].Slew;
            continue;
        }
        for ( k = 0; k < Obj->nFans; k++ )
        {
            Arrivals[k] = State[Obj->Fans[k]].Arrival;
            Slews[k] = State[Obj->Fans[k]].Slew;
        }
        if ( !Scm_WinModelCell(Model, Obj->Gate, State[i].Load, Arrivals, Slews, &State[i].Arrival, &State[i].Slew) ) return 0;
        Metric->EstimatedArea += Scm_WinModelCost(Model, Obj->Gate,
            Abc_MaxFloat(State[i].Load.Value[0], State[i].Load.Value[1]));
    }
    Vec_IntForEachEntry(p->Outputs, Id, i)
    {
        for ( k = 0; k < 2; k++ )
        {
            double Arrival = State[Id].Arrival.Value[k];
            if ( Metric->Electrical < Arrival ) Metric->Electrical = Arrival;
            Metric->Pressure += fmax(0, Arrival-Threshold);
        }
    }
    Metric->EstimatedArea += (double)Metric->Area/SCL_NUM;
    return isfinite(Metric->EstimatedArea) && isfinite(Metric->Pressure);
}

/**Function*************************************************************

  Synopsis    [Computes transition-specific slack at the current electrical loads.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_WinRequired( Nf3_Man_t * p, void * Model, Scm_WinState_t * State, float Delay )
{
    int i, k, t, Id;
    for ( i = 0; i < p->nObjs; i++ ) State[i].Required.Value[0] = State[i].Required.Value[1] = FLT_MAX;
    Vec_IntForEachEntry(p->Outputs, Id, i) State[Id].Required.Value[0] = State[Id].Required.Value[1] = Delay;
    for ( i = p->nObjs-1; i >= 2; i-- ) if ( p->Objs[i].Refs )
        for ( k = 0; k < p->Objs[i].nFans; k++ )
        {
            Id = p->Objs[i].Fans[k];
            if ( p->Objs[i].Gate == NF3_ALIAS )
            {
                for ( t = 0; t < 2; t++ ) State[Id].Required.Value[t] =
                    Abc_MinFloat(State[Id].Required.Value[t], State[i].Required.Value[t]);
            }
            else if ( !Scm_WinModelRequired(Model, p->Objs[i].Gate, k, State[i].Load,
                State[Id].Slew, State[i].Required, &State[Id].Required) ) return 0;
        }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Orders roots by slack, area and topological ID.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_WinRootCompare( const void * pA, const void * pB )
{
    const Scm_WinRoot_t * A = (const Scm_WinRoot_t *)pA, * B = (const Scm_WinRoot_t *)pB;
    if ( A->Path != B->Path ) return A->Path > B->Path ? -1 : 1;
    if ( A->Area != B->Area ) return A->Area > B->Area ? -1 : 1;
    return (A->Id > B->Id) - (A->Id < B->Id);
}

/**Function*************************************************************

  Synopsis    [Ranks electrical timing and pressure before modeled area.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_WinBetter( Scm_WinMetric_t * A, Scm_WinMetric_t * B, int fArea )
{
    if ( fArea && A->EstimatedArea != B->EstimatedArea ) return A->EstimatedArea < B->EstimatedArea;
    if ( fabs(A->Electrical-B->Electrical) > 1e-4 ) return A->Electrical < B->Electrical;
    if ( fabs(A->Pressure-B->Pressure) > 1e-4 ) return A->Pressure < B->Pressure;
    return A->EstimatedArea < B->EstimatedArea;
}

/**Function*************************************************************

  Synopsis    [Evaluates a trial without changing the live cover or its statistics.]

  Description [A full-flow trial runs only after model prescreening.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_WinTrial( Nf3_Man_t * p, Nf3_Obj_t * Backup, int Id, Nf3_Plan_t * Plan,
    void * Model, Scm_WinState_t * State, int * Refs, double Threshold,
    Scm_WinMetric_t * Metric, int fFlow )
{
    Nf3_Obj_t * Original = p->Objs;
    word SavedHits = p->nHits, SavedTwo = p->nTwo;
    long long SavedArea = p->Saved;
    int Ok;
    memcpy(Backup, Original, sizeof(Nf3_Obj_t)*p->nObjs);
    p->Objs = Backup;
    Nf3_Apply(p, Id, Plan);
    Ok = Scm_WinMeasure(p, Model, State, Refs, Threshold, Metric);
    if ( Ok && fFlow )
    {
        Jf_Par_t Pars;
        Gia_Man_t * Trial;
        Nf3_ManSetDefaultPars(&Pars);
        Trial = Nf3_Export(p, &Pars);
        Ok = Trial && Scm_WinModelLookahead(Trial, &Metric->RealArea, &Metric->RealDelay);
        if ( Trial ) Gia_ManStop(Trial);
    }
    p->Objs = Original;
    p->nHits = SavedHits; p->nTwo = SavedTwo; p->Saved = SavedArea;
    return Ok;
}

/**Function*************************************************************

  Synopsis    [Retains a realized checkpoint under the original window guard.]

  Description [The search continues from its current cover, not the checkpoint.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_WinCheckpoint( Nf3_Man_t * p, Scm_WinMetric_t * Current,
    Scm_WinMetric_t * Initial, Scm_WinMetric_t * Kept, Gia_Man_t ** ppKept, int fVerbose, float DelayTarget )
{
    Jf_Par_t Pars;
    Gia_Man_t * Check;
    Scm_WinMetric_t Trial = *Current;
    int Accept;
    Nf3_ManSetDefaultPars(&Pars);
    Check = Nf3_Export(p, &Pars);
    if ( Check == NULL ) return 0;
    if ( !Scm_WinModelLookahead(Check, &Trial.RealArea, &Trial.RealDelay) )
        { Gia_ManStop(Check); return 0; }
    Accept = Trial.RealArea <= 1.02 * Initial->RealArea && Trial.RealDelay <= Initial->RealDelay &&
             Trial.RealArea * Trial.RealDelay < Kept->RealArea * Kept->RealDelay;
    if ( DelayTarget > 0 )
        Accept = Scm_QorTargetBetter(Trial.RealArea, Trial.RealDelay, Kept->RealArea, Kept->RealDelay, DelayTarget);
    if ( fVerbose )
        Abc_Print(1, "SCMAP_WINDOW_CHECK kept=%d area=%.9g delay=%.9g model_area=%.9g model_delay=%.9g\n",
            Accept, Trial.RealArea, Trial.RealDelay, (double)Trial.Area/SCL_NUM, Trial.Electrical);
    if ( !Accept ) Gia_ManStop(Check);
    else
    {
        if ( *ppKept ) Gia_ManStop(*ppKept);
        *ppKept = Check; *Kept = Trial;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Searches windows using electrical pressure or full-flow acceptance.]

  Description [Timing may spend 2% mapped area; recovery holds the achieved
  delay. Full-flow search tests at most two model-ranked candidates per root,
  requires a 0.3% realized improvement, and allows 1% realized area growth.
  Model windows allow 2% realized area growth only with a better area-delay
  product and nonincreasing delay. A final realized guard retains the input
  when the optional search violates these bounds.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Scm_ManWindowImproveInt( Gia_Man_t * Gia, Scm_Qor_t * pQor, int nLookahead, int fVerbose, int fVeryVerbose, float DelayTarget )
{
    Jf_Par_t Pars;
    Nf3_Man_t * p = NULL;
    Nf3_Obj_t * Backup = NULL;
    Scm_WinState_t * State = NULL, * TrialState = NULL;
    Scm_WinRoot_t * Roots = NULL;
    int * Refs = NULL;
    void * Model = NULL;
    Gia_Man_t * Result = NULL, * Checkpoint = NULL;
    Scm_WinMetric_t Initial, Current, Trial, BestMetric, KeptMetric, ShortMetric[2] = {{0}};
    Scm_WinList_t List = {0};
    int fLookahead = nLookahead > 0;
    int nRounds = fLookahead ? 1 : 2, nRoots = fLookahead ? 128 : 4096;
    int nBudget = 32768, nTrials = 0, nFlows = 0;
    int Round, Phase, Limit, Id, i, k, t, Count, Best, nHits = 0, nTwo = 0, Before;
    int nNeutral = 0, nTiming = 0, nGrowing = 0, Kept = 0;
    int nChecks = 0, LastCheck = 0, NextGrowth = 1;
    word Growth = 0;
    double Threshold = 0, Bound, AreaLimit;
    abctime Start = Abc_Clock();
    if ( Gia == NULL || !Gia->vCellMapping || Gia->pManTime || Gia_ManBufNum(Gia) ||
         Gia->vInArrs || Gia->vOutReqs || Gia->vCiArrs || Gia->vCoReqs || Scl_ConIsRunning() ) return NULL;
    if ( !Gia_ManCiNum(Gia) || !Gia_ManAndNum(Gia) ) return Gia;
    Nf3_ManSetDefaultPars(&Pars);
    Model = Scm_WinModelStart();
    if ( Model == NULL ) goto done;
    p = Nf3_Import(Gia, &Pars, 1, 1);
    if ( p == NULL ) goto done;
    Backup = ABC_ALLOC(Nf3_Obj_t, p->nObjs);
    State = ABC_ALLOC(Scm_WinState_t, p->nObjs);
    TrialState = ABC_ALLOC(Scm_WinState_t, p->nObjs);
    Refs = ABC_ALLOC(int, p->nObjs);
    Roots = ABC_ALLOC(Scm_WinRoot_t, p->nObjs);
    List.Plans = ABC_ALLOC(Nf3_Plan_t, 128);
    if ( !Scm_WinMeasure(p, Model, State, Refs, Threshold, &Initial) ) goto done;
    if ( pQor && pQor->fValid ) { Initial.RealArea = pQor->Area; Initial.RealDelay = pQor->Delay; }
    else if ( !Scm_WinModelLookahead(Gia, &Initial.RealArea, &Initial.RealDelay) ) goto done;
    Current = KeptMetric = Initial;
    AreaLimit = 1.02 * Initial.Area;
    for ( Round = 0; Round < nRounds && nTrials < nBudget; Round++ )
    {
        Before = nHits;
        Threshold = 0.8 * Current.Electrical;
        Current.Pressure = 0;
        Vec_IntForEachEntry(p->Outputs, Id, i)
            for ( t = 0; t < 2; t++ ) Current.Pressure += fmax(0, State[Id].Arrival.Value[t]-Threshold);
        for ( Phase = 0; Phase < (fLookahead && !(DelayTarget > 0 && Initial.RealDelay > DelayTarget) ? 1 : 2) && nTrials < nBudget; Phase++ )
        {
            int fArea = Phase || (DelayTarget > 0 && (fLookahead ? Current.RealDelay : KeptMetric.RealDelay) <= DelayTarget);
            if ( fLookahead && Phase && Current.RealDelay > DelayTarget ) break;
            Bound = Current.Electrical;
            // Calibrate only the model screen; full-flow timing decides feasibility.
            if ( DelayTarget > 0 && Initial.RealDelay > 0 )
                Bound = fmax(Bound, Initial.Electrical * DelayTarget / Initial.RealDelay);
            Limit = fLookahead ? nBudget : nBudget*(2*Round+Phase+1)/(2*nRounds);
            List.Limit = Phase && !fLookahead ? 32 : 128;
            if ( !fArea && !Scm_WinRequired(p, Model, State, (float)Current.Electrical) ) goto done;
            Count = 0;
            for ( Id = 2; Id < p->nObjs; Id++ ) if ( p->Objs[Id].Refs && p->Objs[Id].Gate >= 0 )
            {
                Roots[Count].Id = Id;
                Roots[Count].Path = fArea ? 0 : -fmin(
                    State[Id].Required.Value[0]-State[Id].Arrival.Value[0],
                    State[Id].Required.Value[1]-State[Id].Arrival.Value[1]);
                Roots[Count++].Area = Nf3_Area(p, Id);
            }
            qsort(Roots, Count, sizeof(Scm_WinRoot_t), Scm_WinRootCompare);
            Count = Abc_MinInt(Count, nRoots);
            for ( i = 0; i < Count && nTrials < Limit && (!fLookahead || nFlows < nLookahead); i++ )
            {
                int Short[2] = {-1, -1};
                word Extra = fArea || AreaLimit <= Current.Area ? 0 : (word)(AreaLimit-Current.Area);
                Id = Roots[i].Id;
                if ( !p->Objs[Id].Refs || p->Objs[Id].Gate < 0 ) continue;
                Scm_WinEnumerate(p, Id, &List, Extra, !fArea);
                Best = -1; BestMetric = Current;
                for ( k = 0; k < List.Count && nTrials < Limit; k++ )
                {
                    if ( !Scm_WinTrial(p, Backup, Id, List.Plans+k, Model, TrialState, Refs, Threshold, &Trial, 0) ||
                         (long long)Trial.Area + List.Plans[k].Gain != (long long)Current.Area ) goto done;
                    nTrials++;
                    if ( fVeryVerbose )
                        Abc_Print(1, "SCMAP_WINDOW_TRIAL round=%d phase=%d root=%d candidate=%d gain=%lld electrical=%.9g pressure=%.9g two=%d\n",
                            Round, Phase, Id, k, List.Plans[k].Gain, Trial.Electrical, Trial.Pressure, List.Plans[k].Slot != 0);
                    if ( fLookahead )
                    {
                        if ( Trial.Electrical > (DelayTarget > 0 ? fmax(Bound, 1.02 * Current.Electrical) : 1.02 * Current.Electrical) ) continue;
                        if ( Short[0] < 0 || Scm_WinBetter(&Trial, ShortMetric, fArea) )
                        {
                            Short[1] = Short[0]; ShortMetric[1] = ShortMetric[0];
                            Short[0] = k; ShortMetric[0] = Trial;
                        }
                        else if ( Short[1] < 0 || Scm_WinBetter(&Trial, ShortMetric+1, fArea) )
                            { Short[1] = k; ShortMetric[1] = Trial; }
                    }
                    else if ( !fArea )
                    {
                        if ( Trial.EstimatedArea <= 1.02 * Initial.EstimatedArea &&
                             Trial.Electrical <= Current.Electrical + 1e-4 &&
                             (Trial.Electrical < Current.Electrical-1e-4 || Trial.Pressure < Current.Pressure-1e-4) &&
                             Scm_WinBetter(&Trial, &BestMetric, 0) ) { Best = k; BestMetric = Trial; }
                    }
                    else if ( Trial.Electrical <= Bound + 1e-4 && Trial.Area < Current.Area &&
                              Trial.EstimatedArea < BestMetric.EstimatedArea ) { Best = k; BestMetric = Trial; }
                }
                for ( t = 0; fLookahead && t < 2 && Short[t] >= 0 && nFlows < nLookahead; t++ )
                {
                    k = Short[t]; nFlows++;
                    if ( !Scm_WinTrial(p, Backup, Id, List.Plans+k, Model, TrialState, Refs, Threshold, &Trial, 1) ) goto done;
                    if ( fVeryVerbose )
                        Abc_Print(1, "SCMAP_LOOKAHEAD_TRIAL root=%d rank=%d model_delay=%.9g old_model_delay=%.9g model_area=%.9g old_model_area=%.9g pressure=%.9g old_pressure=%.9g area=%.9g old_area=%.9g delay=%.9g old_delay=%.9g\n",
                            Id, t, Trial.Electrical, Current.Electrical, Trial.EstimatedArea, Current.EstimatedArea,
                            Trial.Pressure, Current.Pressure, Trial.RealArea, Current.RealArea, Trial.RealDelay, Current.RealDelay);
                    if ( Trial.RealArea > 1.01 * Initial.RealArea ) continue;
                    if ( DelayTarget > 0 )
                    {
                        if ( Scm_QorTargetBetter(Trial.RealArea, Trial.RealDelay,
                             BestMetric.RealArea, BestMetric.RealDelay, DelayTarget) ) { Best = k; BestMetric = Trial; }
                        continue;
                    }
                    if ( !(Trial.RealDelay <= 0.997 * Current.RealDelay ||
                           (Trial.RealDelay <= Current.RealDelay && Trial.RealArea <= 0.997 * Current.RealArea)) ) continue;
                    if ( Trial.RealDelay < BestMetric.RealDelay ||
                         (Trial.RealDelay == BestMetric.RealDelay && Trial.RealArea < BestMetric.RealArea) )
                        { Best = k; BestMetric = Trial; }
                }
                if ( Best < 0 ) continue;
                Nf3_Apply(p, Id, List.Plans+Best);
                nHits++; nTwo += List.Plans[Best].Slot != 0;
                nNeutral += List.Plans[Best].Gain == 0; nTiming += !fArea; nGrowing += List.Plans[Best].Gain < 0;
                if ( !Scm_WinMeasure(p, Model, State, Refs, Threshold, &Current) ||
                     Current.Area != BestMetric.Area || Current.Electrical != BestMetric.Electrical ||
                     Current.EstimatedArea != BestMetric.EstimatedArea || Current.Pressure != BestMetric.Pressure ) goto done;
                Current.RealArea = BestMetric.RealArea; Current.RealDelay = BestMetric.RealDelay;
                // Reorder the roots for area as soon as lookahead reaches the target.
                if ( fLookahead && !fArea && DelayTarget > 0 && Current.RealDelay <= DelayTarget )
                {
                    if ( fVerbose ) Abc_Print(1, "SCMAP_LOOKAHEAD_TARGET target=%.9g delay=%.9g flows=%d\n",
                        DelayTarget, Current.RealDelay, nFlows);
                    break;
                }
                if ( !fLookahead && !fArea && List.Plans[Best].Gain < 0 ) Growth += (word)-List.Plans[Best].Gain;
                if ( !fLookahead && DelayTarget > 0 && fArea ) Growth += (word)List.Plans[Best].Gain;
                if ( !fLookahead && Initial.Area > 0 && (DelayTarget > 0 || NextGrowth <= 4) && Growth >= 0.005 * NextGrowth * Initial.Area )
                {
                    if ( !Scm_WinCheckpoint(p, &Current, &Initial, &KeptMetric, &Checkpoint, fVerbose, DelayTarget) ) goto done;
                    nChecks++; LastCheck = nHits;
                    do { NextGrowth++; } while ( (DelayTarget > 0 || NextGrowth <= 4) && Growth >= 0.005 * NextGrowth * Initial.Area );
                }
            }
            if ( !fLookahead && nHits != LastCheck )
            {
                if ( !Scm_WinCheckpoint(p, &Current, &Initial, &KeptMetric, &Checkpoint, fVerbose, DelayTarget) ) goto done;
                nChecks++; LastCheck = nHits;
            }
        }
        if ( nHits == Before ) break;
    }
    if ( !fLookahead )
    {
        Kept = Checkpoint != NULL; Result = Checkpoint ? Checkpoint : Gia;
        Checkpoint = NULL; Current = KeptMetric; goto report;
    }
    if ( !nHits ) { Current = Initial; Result = Gia; goto report; }
    Result = Nf3_Export(p, &Pars);
    if ( Result == NULL ) goto done;
    if ( !Scm_WinModelLookahead(Result, &Current.RealArea, &Current.RealDelay) )
        { Gia_ManStop(Result); Result = NULL; goto done; }
    // Check final bounds, not bit-identical repetition of downstream optimizers.
    Kept = Current.RealArea <= 1.01 * Initial.RealArea && Current.RealDelay <= Initial.RealDelay;
    if ( DelayTarget > 0 )
        Kept = Scm_QorTargetBetter(Current.RealArea, Current.RealDelay, Initial.RealArea, Initial.RealDelay, DelayTarget);
    if ( !Kept ) { Gia_ManStop(Result); Result = Gia; }
report:
    if ( pQor )
    {
        pQor->Area = Kept ? Current.RealArea : Initial.RealArea;
        pQor->Delay = Kept ? Current.RealDelay : Initial.RealDelay;
        pQor->fValid = 1;
    }
    if ( fVerbose )
        Abc_Print(1, "%s trials=%d flows=%d checks=%d edits=%d two=%d neutral=%d timing=%d growing=%d kept=%d area=%.9g old_area=%.9g delay=%.9g old_delay=%.9g model_delay=%.9g time=%.3f\n",
            fLookahead ? "SCMAP_LOOKAHEAD" : "SCMAP_WINDOWS", nTrials, nFlows, nChecks, nHits, nTwo, nNeutral, nTiming, nGrowing, Kept,
            Current.RealArea, Initial.RealArea, Current.RealDelay, Initial.RealDelay, Current.Electrical,
            (double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
done:
    if ( Result == NULL ) Abc_Print(0, "SCMap: window topology, area, or timing check failed.\n");
    if ( Checkpoint ) Gia_ManStop(Checkpoint);
    ABC_FREE(Backup); ABC_FREE(State); ABC_FREE(TrialState); ABC_FREE(Refs); ABC_FREE(Roots); ABC_FREE(List.Plans);
    if ( p )
    {
        Nf3_CacheClear(p); ABC_FREE(p->Cache); ABC_FREE(p->Objs);
        Vec_IntFree(p->Inputs); Vec_IntFree(p->Outputs); Vec_IntFree(p->Stack); ABC_FREE(p);
    }
    Scm_WinModelStop(Model);
    return Result;
}

/**Function*************************************************************

  Synopsis    [Improves a mapped cover with electrical windows and a realized guard.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Scm_ManWindowImprove( Gia_Man_t * pGia, Scm_Qor_t * pQor, int fVerbose, int fVeryVerbose )
{
    return Scm_ManWindowImproveInt(pGia, pQor, 0, fVerbose, fVeryVerbose, 0);
}

/**Function*************************************************************

  Synopsis    [Searches critical windows with full-flow lookahead.]

  Description [A no-op returns the input manager without reconstruction.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Scm_ManWindowLookahead( Gia_Man_t * pGia, Scm_Qor_t * pQor, int nTrials, int fVerbose, int fVeryVerbose )
{
    if ( nTrials <= 0 ) return nTrials == 0 ? pGia : NULL;
    return Scm_ManWindowImproveInt(pGia, pQor, nTrials, fVerbose, fVeryVerbose, 0);
}

/**Function*************************************************************

  Synopsis    [Searches for lower realized area under a fixed delay target.]

  Description [If the input misses the target, prefers lower realized delay.
  The full-flow guard is authoritative; the model only proposes candidates.]

  SideEffects []

  SeeAlso     [Scm_ManWindowImprove Scm_ManWindowLookahead]

***********************************************************************/
Gia_Man_t * Scm_ManWindowTarget( Gia_Man_t * pGia, Scm_Qor_t * pQor, float DelayTarget, int nTrials, int fVerbose, int fVeryVerbose )
{
    if ( !isfinite(DelayTarget) || DelayTarget <= 0 || nTrials < 0 ) return NULL;
    return Scm_ManWindowImproveInt(pGia, pQor, nTrials, fVerbose, fVeryVerbose, DelayTarget);
}
