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
    Scm_WinPair_t Arrival, Slew;
    float Load;
    double Scalar;
} Scm_WinState_t;
typedef struct Scm_WinMetric_t_
{
    word Area;
    double Scalar, Electrical, EstimatedArea;
} Scm_WinMetric_t;
typedef struct Scm_WinList_t_
{
    Nf3_Plan_t * Plans;
    int Count, Limit, AllowEqual;
    word Generated;
} Scm_WinList_t;
typedef struct Scm_WinRoot_t_ { int Id; word Area; } Scm_WinRoot_t;

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
static void Scm_WinPlanAdd( Scm_WinList_t * p, Nf3_Plan_t * Plan )
{
    int i, Worst = 0;
    if ( !Plan->Gain && !p->AllowEqual ) return;
    p->Generated++;
    for ( i = 0; i < p->Count; i++ )
        if ( !Scm_WinPlanCompare(p->Plans+i, Plan) ) return;
    if ( p->Count < p->Limit ) { p->Plans[p->Count++] = *Plan; return; }
    for ( i = 1; i < p->Count; i++ )
        if ( Scm_WinPlanCompare(p->Plans+Worst, p->Plans+i) < 0 ) Worst = i;
    if ( Scm_WinPlanCompare(Plan, p->Plans+Worst) < 0 ) p->Plans[Worst] = *Plan;
}

/**Function*************************************************************

  Synopsis    [Enumerates two-cell replacements with exact shared-area accounting.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_WinTryTwo( Nf3_Man_t * p, int Root, int * Nodes, int nNodes,
    int * Leaves, int nLeaves, word Truth, Scm_WinList_t * List )
{
    Nf3_Cache_t * Entry;
    int i, j, k;
    if ( nLeaves < 2 || Nf3_TrialArea(p, Root, NULL, 0, NULL) < 2*p->MinArea ) return;
    Entry = Nf3_Recipes(p, Truth, nLeaves);
    for ( i = 0; i < Entry->nRecipes; i++ )
    {
        Nf3_Recipe_t * R = Entry->Recipes+i;
        Nf3_Plan_t Plan = {0};
        int Fans[2][6] = {{0}}, All[12], nAll = 0, MaxFan = 0, Slot, Id, Pin;
        word Saved;
        for ( j = 0; j < 2; j++ )
        {
            for ( k = 0; k < (int)p->Cells[R->Gate[j]].nFanins; k++ )
            {
                Pin = R->Pins[j][k];
                if ( Pin == 12 ) { Fans[j][k] = -1; continue; }
                Id = Leaves[Pin >> 1];
                if ( Pin & 1 ) Id = p->Objs[Id].Compl;
                if ( Id < 0 || Id >= Root || !p->Objs[Id].Refs || Nf3_Find(Nodes, nNodes, Id) >= 0 ) break;
                All[nAll++] = Fans[j][k] = Id;
                if ( j == 0 ) MaxFan = Abc_MaxInt(MaxFan, Id);
            }
            if ( k != (int)p->Cells[R->Gate[j]].nFanins ) break;
        }
        if ( j != 2 ) continue;
        Saved = Nf3_TrialArea(p, Root, All, nAll, &Slot);
        if ( R->Area > Saved || (R->Area == Saved && !List->AllowEqual) ) continue;
        if ( Root-1 > Slot && !p->Objs[Root-1].Refs && p->Objs[Root-1].Gate != NF3_CI ) Slot = Root-1;
        if ( Slot <= MaxFan ) continue;
        Plan.Gain = Saved-R->Area; Plan.Gate = R->Gate[1];
        Plan.Slot = Slot; Plan.ChildGate = R->Gate[0];
        Plan.nFans = p->Cells[R->Gate[1]].nFanins;
        memcpy(Plan.ChildFans, Fans[0], sizeof(int)*p->Cells[R->Gate[0]].nFanins);
        for ( k = 0; k < Plan.nFans; k++ ) Plan.Fans[k] = Fans[1][k] == -1 ? Slot : Fans[1][k];
        Scm_WinPlanAdd(List, &Plan);
    }
}

/**Function*************************************************************

  Synopsis    [Checks the exact area change of a one-cell replacement.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_WinSetGain( Nf3_Man_t * p, int Root, Nf3_Plan_t * Plan, int AllowEqual )
{
    word Saved = Nf3_TrialArea(p, Root, Plan->Fans, Plan->nFans, NULL);
    word Added = Plan->Gate < 0 ? 0 : p->Cells[Plan->Gate].AreaW;
    Nf3_Obj_t * Obj = p->Objs+Root;
    if ( Added > Saved || (Added == Saved && !AllowEqual) ) return 0;
    if ( Plan->Gate == Obj->Gate && Plan->nFans == Obj->nFans &&
         !memcmp(Plan->Fans, Obj->Fans, sizeof(int)*Obj->nFans) ) return 0;
    Plan->Gain = Saved-Added;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Matches a window function to one- and two-cell implementations.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_WinTryFunction( Nf3_Man_t * p, int Root, int * Nodes, int nNodes,
    int * Leaves, int nLeaves, word Truth, Scm_WinList_t * List )
{
    Nf3_Plan_t Plan = {0};
    int Keep[6], Gate, Entry, Index, Id, i, k;
    unsigned Config, Perm, Phase;
    word Key;
    Vec_Int_t * Matches;
    memcpy(Keep, Leaves, sizeof(int)*nLeaves);
    nLeaves = Abc_Tt6MinBase(&Truth, Keep, nLeaves);
    if ( nLeaves <= 1 )
    {
        Plan.Gate = NF3_ALIAS; Plan.nFans = 1;
        Plan.Fans[0] = nLeaves == 0 ? (int)(Truth & 1) : Keep[0];
        if ( nLeaves == 1 && (Truth & 1) )
        {
            Id = p->Objs[Plan.Fans[0]].Compl;
            if ( Id >= 0 && p->Objs[Id].Refs ) Plan.Fans[0] = Id;
            else Plan.Gate = 3;
        }
        if ( Plan.Fans[0] >= Root ) return;
        if ( Scm_WinSetGain(p, Root, &Plan, List->AllowEqual) ) Scm_WinPlanAdd(List, &Plan);
        return;
    }
    Key = Truth & 1 ? ~Truth : Truth;
    Index = *Vec_MemHashLookup(p->Truths, &Key);
    if ( Index >= 0 && Index < Vec_WecSize(p->Matches) )
    {
        Matches = Vec_WecEntry(p->Matches, Index);
        Vec_IntForEachEntryDouble(Matches, Gate, Entry, i)
        {
            Config = (unsigned)Entry;
            if ( (Config & 1) != (unsigned)(Truth & 1) || (int)p->Cells[Gate].nFanins != nLeaves ) continue;
            memset(&Plan, 0, sizeof(Plan)); Plan.Gate = Gate; Plan.nFans = nLeaves;
            Perm = Config >> 8; Phase = (Config >> 1) & 127;
            for ( k = 0; k < nLeaves; k++, Perm >>= 4, Phase >>= 1 )
            {
                Id = Keep[Perm & 15];
                if ( Phase & 1 ) Id = p->Objs[Id].Compl;
                if ( Id < 0 || Id >= Root || !p->Objs[Id].Refs ) break;
                Plan.Fans[k] = Id;
            }
            if ( k < nLeaves ) continue;
            if ( Scm_WinSetGain(p, Root, &Plan, List->AllowEqual) ) Scm_WinPlanAdd(List, &Plan);
        }
    }
    if ( p->fDecompose ) Scm_WinTryTwo(p, Root, Nodes, nNodes, Keep, nLeaves, Truth, List);
}

/**Function*************************************************************

  Synopsis    [Enumerates bounded windows rooted at a mapped cell.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_WinEnumerate( Nf3_Man_t * p, int Root, Scm_WinList_t * List )
{
    int Nodes[NF3_WINDOW_MAX] = {Root}, Leaves[NF3_LEAF_MAX], nNodes = 1, nLeaves = 0, k;
    Nf3_Obj_t * Obj = p->Objs+Root;
    List->Count = 0;
    for ( k = 0; k < Obj->nFans; k++ )
        if ( Obj->Fans[k] >= 2 && Nf3_Find(Leaves, nLeaves, Obj->Fans[k]) < 0 ) Leaves[nLeaves++] = Obj->Fans[k];
    do {
        word Values[NF3_WINDOW_MAX], Truth;
        unsigned Seen = 0;
        Truth = Nf3_WindowTruth_rec(p, Root, Nodes, nNodes, Leaves, nLeaves, Values, &Seen);
        Scm_WinTryFunction(p, Root, Nodes, nNodes, Leaves, nLeaves, Truth, List);
    } while ( Nf3_Expand(p, Nodes, &nNodes, Leaves, &nLeaves) );
    qsort(List->Plans, List->Count, sizeof(Nf3_Plan_t), Scm_WinPlanCompare);
}

/**Function*************************************************************

  Synopsis    [Recomputes all live loads, arrival times, slews and modeled area.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_WinMeasure( Nf3_Man_t * p, void * Model, Scm_WinState_t * State,
    int * Refs, Scm_WinMetric_t * Metric )
{
    int i, k, Id;
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
            State[Obj->Fans[k]].Load += Scm_WinModelCap(Model, Obj->Gate, k);
    }
    // Aliases are wires, not extra cells: transfer all of their sink load.
    for ( i = p->nObjs-1; i >= 2; i-- ) if ( Refs[i] && p->Objs[i].Gate == NF3_ALIAS )
        State[p->Objs[i].Fans[0]].Load += State[i].Load;
    for ( i = 2; i < p->nObjs; i++ ) if ( Refs[i] && p->Objs[i].Gate != NF3_CI )
    {
        Nf3_Obj_t * Obj = p->Objs+i;
        Scm_WinPair_t Arrivals[6], Slews[6];
        if ( Obj->Gate == NF3_ALIAS )
        {
            State[i].Arrival = State[Obj->Fans[0]].Arrival;
            State[i].Slew = State[Obj->Fans[0]].Slew;
            State[i].Scalar = State[Obj->Fans[0]].Scalar;
            continue;
        }
        for ( k = 0; k < Obj->nFans; k++ )
        {
            double Arrival = State[Obj->Fans[k]].Scalar + (double)p->Cells[Obj->Gate].iDelays[k]/SCL_NUM;
            Arrivals[k] = State[Obj->Fans[k]].Arrival;
            Slews[k] = State[Obj->Fans[k]].Slew;
            if ( State[i].Scalar < Arrival ) State[i].Scalar = Arrival;
        }
        if ( !Scm_WinModelCell(Model, Obj->Gate, State[i].Load, Arrivals, Slews, &State[i].Arrival, &State[i].Slew) ) return 0;
        Metric->EstimatedArea += Scm_WinModelCost(Model, Obj->Gate, State[i].Load);
    }
    Vec_IntForEachEntry(p->Outputs, Id, i)
    {
        if ( Metric->Scalar < State[Id].Scalar ) Metric->Scalar = State[Id].Scalar;
        for ( k = 0; k < 2; k++ )
            if ( Metric->Electrical < State[Id].Arrival.Value[k] ) Metric->Electrical = State[Id].Arrival.Value[k];
    }
    Metric->EstimatedArea += (double)Metric->Area/SCL_NUM;
    return isfinite(Metric->EstimatedArea);
}

/**Function*************************************************************

  Synopsis    [Orders roots by cell area with a stable topological tie-break.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_WinRootCompare( const void * pA, const void * pB )
{
    const Scm_WinRoot_t * A = (const Scm_WinRoot_t *)pA, * B = (const Scm_WinRoot_t *)pB;
    if ( A->Area != B->Area ) return A->Area > B->Area ? -1 : 1;
    return (A->Id > B->Id) - (A->Id < B->Id);
}

/**Function*************************************************************

  Synopsis    [Recovers area while preserving electrical and fixed-arc bounds.]

  Description [A timing-first phase allows area-neutral moves; an area phase
  reduces modeled physical area. The whole live cover is retimed for each
  trial, including shared drivers and downstream paths. No physical buffers
  are committed to the returned mapping.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Scm_ManWindowImprove( Gia_Man_t * Gia, int fVerbose, int fVeryVerbose )
{
    Jf_Par_t Pars;
    Nf3_Man_t * p = NULL;
    Nf3_Obj_t * Backup = NULL, * Original;
    Scm_WinState_t * State = NULL;
    Scm_WinRoot_t * Roots = NULL;
    int * Refs = NULL;
    void * Model = NULL;
    Gia_Man_t * Result = NULL;
    Scm_WinMetric_t Initial, Current, Trial, BestMetric;
    Scm_WinList_t List = {0};
    int nRounds = 2, nRoots = 4096, nBudget = 32768;
    int Round, Phase, Limit, Id, i, k, Count, Best, nTrials = 0, nHits = 0, nTwo = 0, Before;
    int nNeutral = 0, nTiming = 0;
    abctime Start = Abc_Clock();
    if ( Gia == NULL || !Gia->vCellMapping || Gia->pManTime || Gia_ManBufNum(Gia) ||
         Gia->vInArrs || Gia->vOutReqs || Gia->vCiArrs || Gia->vCoReqs || Scl_ConIsRunning() ) return NULL;
    Nf3_ManSetDefaultPars(&Pars);
    Model = Scm_WinModelStart();
    if ( Model == NULL ) goto done;
    p = Nf3_Import(Gia, &Pars, 1, 1);
    if ( p == NULL ) goto done;
    Backup = ABC_ALLOC(Nf3_Obj_t, p->nObjs);
    State = ABC_ALLOC(Scm_WinState_t, p->nObjs);
    Refs = ABC_ALLOC(int, p->nObjs);
    Roots = ABC_ALLOC(Scm_WinRoot_t, p->nObjs);
    List.Limit = 32;
    List.AllowEqual = 1;
    List.Plans = ABC_ALLOC(Nf3_Plan_t, List.Limit);
    if ( !Scm_WinMeasure(p, Model, State, Refs, &Initial) ) goto done;
    Current = Initial;
    for ( Round = 0; Round < nRounds && nTrials < nBudget; Round++ )
    {
        Before = nHits;
        for ( Phase = 0; Phase < 2 && nTrials < nBudget; Phase++ )
        {
            Limit = nBudget*(2*Round+Phase+1)/(2*nRounds);
            Count = 0;
            for ( Id = 2; Id < p->nObjs; Id++ ) if ( p->Objs[Id].Refs && p->Objs[Id].Gate >= 0 )
            {
                Roots[Count].Id = Id;
                Roots[Count++].Area = Nf3_Area(p, Id);
            }
            qsort(Roots, Count, sizeof(Scm_WinRoot_t), Scm_WinRootCompare);
            Count = Abc_MinInt(Count, nRoots);
            for ( i = 0; i < Count && nTrials < Limit; i++ )
            {
                Id = Roots[i].Id;
                if ( !p->Objs[Id].Refs || p->Objs[Id].Gate < 0 ) continue;
                Scm_WinEnumerate(p, Id, &List);
                Best = -1; BestMetric = Current;
                for ( k = 0; k < List.Count && nTrials < Limit; k++ )
                {
                    word SavedHits = p->nHits, SavedTwo = p->nTwo, SavedArea = p->Saved;
                    int Ok;
                    Original = p->Objs;
                    memcpy(Backup, Original, sizeof(Nf3_Obj_t)*p->nObjs);
                    p->Objs = Backup;
                    Nf3_Apply(p, Id, List.Plans+k);
                    Ok = Scm_WinMeasure(p, Model, State, Refs, &Trial);
                    p->Objs = Original;
                    p->nHits = SavedHits; p->nTwo = SavedTwo; p->Saved = SavedArea;
                    if ( !Ok || Trial.Area + List.Plans[k].Gain != Current.Area ) goto done;
                    nTrials++;
                    if ( fVeryVerbose )
                        Abc_Print(1, "SCMAP_WINDOW_TRIAL round=%d root=%d candidate=%d gain=%llu scalar=%.9g electrical=%.9g two=%d\n",
                            Round, Id, k, (unsigned long long)List.Plans[k].Gain,
                            Trial.Scalar, Trial.Electrical, List.Plans[k].Slot != 0);
                    if ( Trial.Scalar > Initial.Scalar ) continue;
                    if ( !Phase )
                    {
                        if ( Trial.EstimatedArea <= Current.EstimatedArea &&
                             (Trial.Electrical < BestMetric.Electrical ||
                              (Best >= 0 && Trial.Electrical == BestMetric.Electrical &&
                               Trial.EstimatedArea < BestMetric.EstimatedArea)) )
                            { Best = k; BestMetric = Trial; }
                    }
                    else if ( Trial.Electrical <= Initial.Electrical &&
                              (Trial.EstimatedArea < BestMetric.EstimatedArea ||
                               (Best >= 0 && Trial.EstimatedArea == BestMetric.EstimatedArea &&
                                Trial.Electrical < BestMetric.Electrical)) )
                        { Best = k; BestMetric = Trial; }
                }
                if ( Best < 0 ) continue;
                Nf3_Apply(p, Id, List.Plans+Best);
                nHits++; nTwo += List.Plans[Best].Slot != 0;
                nNeutral += List.Plans[Best].Gain == 0; nTiming += !Phase;
                if ( !Scm_WinMeasure(p, Model, State, Refs, &Current) ||
                     Current.Area != BestMetric.Area || Current.Scalar != BestMetric.Scalar ||
                     Current.Electrical != BestMetric.Electrical ||
                     Current.EstimatedArea != BestMetric.EstimatedArea ) goto done;
            }
        }
        if ( nHits == Before ) break;
    }
    if ( !Scm_WinMeasure(p, Model, State, Refs, &Current) || Current.Area > Initial.Area ||
         Current.EstimatedArea > Initial.EstimatedArea || Current.Scalar > Initial.Scalar ||
         Current.Electrical > Initial.Electrical ) goto done;
    Result = Nf3_Export(p, &Pars);
    if ( fVerbose )
        Abc_Print(1, "SCMAP_WINDOWS trials=%d edits=%d two=%d neutral=%d timing=%d area=%.9g old_area=%.9g delay=%.9g old_delay=%.9g time=%.3f\n",
            nTrials, nHits, nTwo, nNeutral, nTiming,
            (double)Current.Area/SCL_NUM, (double)Initial.Area/SCL_NUM,
            Current.Electrical, Initial.Electrical, (double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
done:
    if ( Result == NULL ) Abc_Print(-1, "SCMap: window topology, area, or timing invariant failed.\n");
    ABC_FREE(Backup); ABC_FREE(State); ABC_FREE(Refs); ABC_FREE(Roots); ABC_FREE(List.Plans);
    if ( p )
    {
        Nf3_CacheClear(p); ABC_FREE(p->Cache); ABC_FREE(p->Objs);
        Vec_IntFree(p->Inputs); Vec_IntFree(p->Outputs); Vec_IntFree(p->Stack); ABC_FREE(p);
    }
    Scm_WinModelStop(Model);
    return Result;
}
