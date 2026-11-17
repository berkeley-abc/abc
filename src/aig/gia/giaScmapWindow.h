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
    double Cost;
} Scm_WinState_t;
typedef struct Scm_WinMetric_t_
{
    word Area;
    double Electrical, Pressure, EstimatedArea, RealArea;
    float RealDelay;
} Scm_WinMetric_t;
typedef Nf3_Enum_t Scm_WinList_t;
typedef struct Scm_WinRoot_t_ { int Id; word Area; double Path; } Scm_WinRoot_t;
typedef struct Scm_WinDelta_t_
{
    int * Starts, * Edges;
    word * TimeBits;
    int TimeMin, TimeMax;
    unsigned char * DirtyLoad, * DirtyTime;
    Scm_RfPair_t * Caps;
    Vec_Int_t * Changed, * Loads, * Times, * Fans;
} Scm_WinDelta_t;
typedef struct Scm_WinChecks_t_
{
    Gia_Man_t * Covers[2];
    Scm_WinMetric_t Metrics[2];
} Scm_WinChecks_t;

/**Function*************************************************************

  Synopsis    [Builds ordered physical fanouts after a committed window edit.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_WinDeltaBuild( Nf3_Man_t * p, Scm_WinDelta_t * d )
{
    int i, k;
    memset(d->Starts, 0, sizeof(int)*(p->nObjs+1));
    for ( i = 2; i < p->nObjs; i++ ) if ( p->Objs[i].Refs )
        for ( k = 0; k < p->Objs[i].nFans; k++ ) d->Starts[p->Objs[i].Fans[k]+1]++;
    for ( i = 1; i <= p->nObjs; i++ ) d->Starts[i] += d->Starts[i-1];
    // Fill backwards so each fanout list has increasing object and pin IDs.
    for ( i = p->nObjs-1; i >= 2; i-- ) if ( p->Objs[i].Refs )
        for ( k = p->Objs[i].nFans-1; k >= 0; k-- )
            d->Edges[--d->Starts[p->Objs[i].Fans[k]+1]] = 8*i+k;
    for ( i = 0; i < p->nObjs; i++ ) d->Starts[i] = d->Starts[i+1];
    d->Starts[p->nObjs] = 0;
    for ( i = 2; i < p->nObjs; i++ ) if ( p->Objs[i].Refs ) d->Starts[p->nObjs] += p->Objs[i].nFans;
}

/**Function*************************************************************

  Synopsis    [Allocates per-search incremental timing state.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Scm_WinDelta_t * Scm_WinDeltaStart( Nf3_Man_t * p, void * Model )
{
    Scm_WinDelta_t * d;
    int i, k;
    if ( p->nObjs > INT_MAX/8 || p->nCells > INT_MAX/6 ) return NULL;
    for ( i = 0; i < p->nCells; i++ ) if ( p->Cells[i].nFanins > 6 ) return NULL;
    d = ABC_CALLOC(Scm_WinDelta_t, 1);
    d->Starts = ABC_ALLOC(int, p->nObjs+1);
    d->Edges = ABC_ALLOC(int, 6*p->nObjs);
    d->TimeBits = ABC_CALLOC(word, Abc_Bit6WordNum(p->nObjs));
    d->DirtyLoad = ABC_CALLOC(unsigned char, p->nObjs);
    d->DirtyTime = ABC_CALLOC(unsigned char, p->nObjs);
    d->Caps = ABC_CALLOC(Scm_RfPair_t, 6*p->nCells);
    d->Changed = Vec_IntAlloc(64); d->Loads = Vec_IntAlloc(64); d->Fans = Vec_IntAlloc(64);
    d->Times = Vec_IntAlloc(64);
    for ( i = 0; i < p->nCells; i++ )
        for ( k = 0; k < (int)p->Cells[i].nFanins; k++ ) d->Caps[6*i+k] = Scm_WinModelCap(Model, i, k);
    Scm_WinDeltaBuild(p, d);
    return d;
}

/**Function*************************************************************

  Synopsis    [Releases incremental timing state.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_WinDeltaStop( Scm_WinDelta_t * d )
{
    if ( d == NULL ) return;
    ABC_FREE(d->Starts); ABC_FREE(d->Edges); ABC_FREE(d->DirtyLoad); ABC_FREE(d->DirtyTime); ABC_FREE(d->Caps);
    ABC_FREE(d->TimeBits);
    Vec_IntFree(d->Changed); Vec_IntFree(d->Loads); Vec_IntFree(d->Times); Vec_IntFree(d->Fans); ABC_FREE(d);
}

/**Function*************************************************************

  Synopsis    [Marks a changed sink load, including the driver of any alias.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_WinDeltaLoad( Scm_WinDelta_t * d, int Id )
{
    if ( d->DirtyLoad[Id] ) return;
    d->DirtyLoad[Id] = 1;
    Vec_IntPush(d->Loads, Id);
}

/**Function*************************************************************

  Synopsis    [Marks forward timing and records the state to restore.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_WinDeltaTime( Scm_WinDelta_t * d, int Id )
{
    if ( d->DirtyTime[Id] ) return;
    d->DirtyTime[Id] = 1;
    d->TimeBits[Id >> 6] |= (word)1 << (Id & 63);
    d->TimeMin = Abc_MinInt(d->TimeMin, Id >> 6);
    d->TimeMax = Abc_MaxInt(d->TimeMax, Id >> 6);
    Vec_IntPush(d->Times, Id);
}

/**Function*************************************************************

  Synopsis    [Updates only affected loads and forward timing in a trial.]

  Description [Fanout sums retain the full evaluator's order. Integer logic
  area is exact; modeled overhead is updated by deltas and checked for double
  roundoff at commit. Only the root and its optional child gain new edges.]

  SideEffects []

  SeeAlso     [Scm_WinMeasure]

***********************************************************************/
static int Scm_WinDeltaMeasure( Nf3_Man_t * p, void * Model, Scm_WinDelta_t * d,
    Nf3_Obj_t * BaseObjs, Scm_WinState_t * BaseState, Scm_WinMetric_t * BaseMetric, Scm_WinState_t * State,
    int Root, int Slot, double Threshold, Scm_WinMetric_t * Metric )
{
    int i, k, t, w, Id, Edge, Fan, Extra[2] = { Root, Slot };
    memset(Metric, 0, sizeof(*Metric));
    Vec_IntForEachEntry(d->Loads, Id, i) d->DirtyLoad[Id] = 0;
    Vec_IntForEachEntry(d->Times, Id, i)
        { d->DirtyTime[Id] = 0; d->TimeBits[Id >> 6] = 0; }
    Vec_IntClear(d->Times);
    Vec_IntClear(d->Loads);
    d->TimeMin = INT_MAX; d->TimeMax = -1;
    Vec_IntForEachEntry(d->Changed, Id, i)
    {
        Nf3_Obj_t * Old = BaseObjs+Id, * Obj = p->Objs+Id;
        if ( Obj->Refs < 0 ) return 0;
        Scm_WinDeltaTime(d, Id);
        if ( !!Old->Refs == !!Obj->Refs && Old->Gate == Obj->Gate && Old->nFans == Obj->nFans &&
             !memcmp(Old->Fans, Obj->Fans, sizeof(int)*Obj->nFans) ) continue;
        if ( Old->Refs ) for ( k = 0; k < Old->nFans; k++ ) Scm_WinDeltaLoad(d, Old->Fans[k]);
        if ( Obj->Refs ) for ( k = 0; k < Obj->nFans; k++ )
        {
            if ( Obj->Fans[k] < 0 || Obj->Fans[k] >= Id ) return 0;
            Scm_WinDeltaLoad(d, Obj->Fans[k]);
        }
        if ( !Obj->Refs ) memset(State+Id, 0, sizeof(*State));
    }
    Vec_IntForEachEntry(d->Loads, Id, i)
    {
        if ( BaseObjs[Id].Refs && BaseObjs[Id].Gate == NF3_ALIAS ) Scm_WinDeltaLoad(d, BaseObjs[Id].Fans[0]);
        if ( p->Objs[Id].Refs && p->Objs[Id].Gate == NF3_ALIAS ) Scm_WinDeltaLoad(d, p->Objs[Id].Fans[0]);
    }
    Vec_IntSort(d->Loads, 1);
    Vec_IntForEachEntry(d->Loads, Id, w)
    {
        Scm_RfPair_t Load = {{0, 0}};
        Vec_IntClear(d->Fans);
        for ( i = d->Starts[Id]; i < d->Starts[Id+1]; i++ )
        {
            Edge = d->Edges[i]; Fan = Edge >> 3;
            if ( Fan != Root && Fan != Slot && p->Objs[Fan].Refs ) Vec_IntPush(d->Fans, Edge);
        }
        for ( t = 0; t < 2; t++ ) if ( Extra[t] )
            for ( k = 0; k < p->Objs[Extra[t]].nFans; k++ )
                if ( p->Objs[Extra[t]].Fans[k] == Id ) Vec_IntPush(d->Fans, 8*Extra[t]+k);
        Vec_IntSort(d->Fans, 0);
        Vec_IntForEachEntry(d->Fans, Edge, i) if ( p->Objs[Edge >> 3].Gate >= 0 )
            for ( t = 0; t < 2; t++ ) Load.Value[t] += d->Caps[6*p->Objs[Edge >> 3].Gate+(Edge & 7)].Value[t];
        Vec_IntForEachEntryReverse(d->Fans, Edge, i) if ( p->Objs[Edge >> 3].Gate == NF3_ALIAS )
            for ( t = 0; t < 2; t++ ) Load.Value[t] += State[Edge >> 3].Load.Value[t];
        State[Id].Load = Load;
        if ( memcmp(&Load, &BaseState[Id].Load, sizeof(Load)) ) Scm_WinDeltaTime(d, Id);
    }
    for ( w = d->TimeMin; w <= d->TimeMax; w++ ) while ( d->TimeBits[w] )
    {
        Nf3_Obj_t * Obj;
        Scm_RfPair_t Arrivals[6], Slews[6];
        Id = 64*w + Abc_Tt6FirstBit(d->TimeBits[w]);
        d->TimeBits[w] &= d->TimeBits[w]-1;
        if ( Id < 2 || !p->Objs[Id].Refs || p->Objs[Id].Gate == NF3_CI ) continue;
        Obj = p->Objs+Id;
        if ( Obj->Gate == NF3_ALIAS )
        {
            State[Id].Arrival = State[Obj->Fans[0]].Arrival;
            State[Id].Slew = State[Obj->Fans[0]].Slew;
            State[Id].Cost = 0;
        }
        else
        {
            if ( Obj->nFans != (int)p->Cells[Obj->Gate].nFanins ) return 0;
            for ( k = 0; k < Obj->nFans; k++ )
            {
                Arrivals[k] = State[Obj->Fans[k]].Arrival;
                Slews[k] = State[Obj->Fans[k]].Slew;
            }
            if ( !Scm_WinModelCell(Model, Obj->Gate, State[Id].Load, Arrivals, Slews, &State[Id].Arrival, &State[Id].Slew) ) return 0;
            if ( BaseObjs[Id].Refs && Obj->Gate == BaseObjs[Id].Gate &&
                 !memcmp(&State[Id].Load, &BaseState[Id].Load, sizeof(Scm_RfPair_t)) ) State[Id].Cost = BaseState[Id].Cost;
            else
                State[Id].Cost = Scm_WinModelCost(Model, Obj->Gate, Abc_MaxFloat(State[Id].Load.Value[0], State[Id].Load.Value[1]));
        }
        if ( !memcmp(&State[Id].Arrival, &BaseState[Id].Arrival, sizeof(Scm_RfPair_t)) &&
             !memcmp(&State[Id].Slew, &BaseState[Id].Slew, sizeof(Scm_RfPair_t)) ) continue;
        for ( i = d->Starts[Id]; i < d->Starts[Id+1]; i++ )
        {
            Fan = d->Edges[i] >> 3;
            if ( Fan != Root && Fan != Slot && p->Objs[Fan].Refs ) Scm_WinDeltaTime(d, Fan);
        }
        for ( t = 0; t < 2; t++ ) if ( Extra[t] )
            for ( k = 0; k < p->Objs[Extra[t]].nFans; k++ )
                if ( p->Objs[Extra[t]].Fans[k] == Id ) Scm_WinDeltaTime(d, Extra[t]);
    }
    Metric->Area = BaseMetric->Area;
    Metric->EstimatedArea = BaseMetric->EstimatedArea - (double)BaseMetric->Area/SCL_NUM;
    Vec_IntForEachEntry(d->Times, Id, i) if ( Id >= 2 )
    {
        if ( p->Objs[Id].Refs && p->Objs[Id].Gate >= 0 )
        {
            Metric->Area += Nf3_Area(p, Id);
            Metric->EstimatedArea += State[Id].Cost;
        }
        if ( BaseObjs[Id].Refs && BaseObjs[Id].Gate >= 0 )
        {
            Metric->Area -= p->Cells[BaseObjs[Id].Gate].AreaW;
            Metric->EstimatedArea -= BaseState[Id].Cost;
        }
    }
    Vec_IntForEachEntry(p->Outputs, Id, i) for ( t = 0; t < 2; t++ )
    {
        double Arrival = State[Id].Arrival.Value[t];
        if ( Metric->Electrical < Arrival ) Metric->Electrical = Arrival;
        Metric->Pressure += fmax(0, Arrival-Threshold);
    }
    Metric->EstimatedArea += (double)Metric->Area/SCL_NUM;
    return isfinite(Metric->EstimatedArea) && isfinite(Metric->Pressure);
}

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

  Synopsis    [Checks loads and references, reusing unchanged cell evaluations.]

  Description [Optional baseline arrays describe the unmodified cover. Loads
  and area retain their original summation order. Pressure uses the round's
  fixed threshold, not the trial's delay.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_WinMeasure( Nf3_Man_t * p, void * Model, Scm_WinState_t * State,
    int * Refs, double Threshold, Scm_WinMetric_t * Metric,
    Nf3_Obj_t * BaseObjs, Scm_WinState_t * BaseState )
{
    int i, k, t, Id, fReuse;
#ifdef SCM_WIN_FULL
    BaseState = NULL;
#endif
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
        fReuse = BaseState && BaseObjs[i].Refs && Obj->Gate == BaseObjs[i].Gate &&
            Obj->nFans == BaseObjs[i].nFans &&
            !memcmp(Obj->Fans, BaseObjs[i].Fans, sizeof(int)*Obj->nFans) &&
            !memcmp(&State[i].Load, &BaseState[i].Load, sizeof(Scm_RfPair_t));
        for ( k = 0; k < Obj->nFans; k++ )
        {
            Arrivals[k] = State[Obj->Fans[k]].Arrival;
            Slews[k] = State[Obj->Fans[k]].Slew;
            if ( fReuse && (memcmp(Arrivals+k, &BaseState[Obj->Fans[k]].Arrival, sizeof(Scm_RfPair_t)) ||
                            memcmp(Slews+k, &BaseState[Obj->Fans[k]].Slew, sizeof(Scm_RfPair_t))) ) fReuse = 0;
        }
        if ( fReuse )
        {
            State[i].Arrival = BaseState[i].Arrival;
            State[i].Slew = BaseState[i].Slew;
            State[i].Cost = BaseState[i].Cost;
        }
        else
        {
            if ( !Scm_WinModelCell(Model, Obj->Gate, State[i].Load, Arrivals, Slews, &State[i].Arrival, &State[i].Slew) ) return 0;
            State[i].Cost = Scm_WinModelCost(Model, Obj->Gate,
                Abc_MaxFloat(State[i].Load.Value[0], State[i].Load.Value[1]));
        }
        Metric->EstimatedArea += State[i].Cost;
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

// Each commit refreshes the sum; the allowance covers one trial's additions/subtractions.
static int Scm_WinAreaEqual( int nObjs, double A, double B )
{
    return fabs(A-B) <= 16*DBL_EPSILON*nObjs*(fabs(A)+fabs(B)+1);
}

/**Function*************************************************************

  Synopsis    [Evaluates a trial without changing the live cover or its statistics.]

  Description [A full-flow trial runs only after model prescreening.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_WinTrial( Nf3_Man_t * p, Nf3_Obj_t * Backup, Scm_WinDelta_t * Delta, int Id, Nf3_Plan_t * Plan,
    void * Model, Scm_WinState_t * BaseState, Scm_WinMetric_t * BaseMetric, Scm_WinState_t * State, int * Refs, double Threshold,
    Scm_WinMetric_t * Metric, int fFlow )
{
    Nf3_Obj_t * Original = p->Objs;
    word SavedHits = p->nHits, SavedTwo = p->nTwo;
    long long SavedArea = p->Saved;
    int Ok, i, ObjId;
#ifdef SCM_WIN_FULL
    memcpy(Backup, Original, sizeof(Nf3_Obj_t)*p->nObjs);
#endif
    p->Objs = Backup;
    Vec_IntClear(Delta->Changed);
    p->Changed = Delta->Changed;
    Nf3_Apply(p, Id, Plan);
    p->Changed = NULL;
#ifdef SCM_WIN_FULL
    BaseState = NULL;
#endif
    Ok = BaseState ? Scm_WinDeltaMeasure(p, Model, Delta, Original, BaseState, BaseMetric, State, Id, Plan->Slot, Threshold, Metric) :
        Scm_WinMeasure(p, Model, State, Refs, Threshold, Metric, NULL, NULL);
#ifdef SCM_WIN_VERIFY
    if ( Ok )
    {
        Scm_WinState_t * Check = ABC_ALLOC(Scm_WinState_t, p->nObjs);
        Scm_WinMetric_t CheckMetric;
        Ok = Scm_WinMeasure(p, Model, Check, Refs, Threshold, &CheckMetric, NULL, NULL) &&
             !memcmp(State, Check, sizeof(Scm_WinState_t)*p->nObjs) &&
             Scm_WinAreaEqual(p->nObjs, Metric->EstimatedArea, CheckMetric.EstimatedArea);
        CheckMetric.EstimatedArea = Metric->EstimatedArea;
        Ok = Ok && !memcmp(Metric, &CheckMetric, sizeof(*Metric));
        if ( !Ok ) Abc_Print(-1, "SCMap: incremental window timing differs at root %d.\n", Id);
        ABC_FREE(Check);
    }
#endif
    if ( Ok && fFlow )
    {
        Jf_Par_t Pars;
        Gia_Man_t * Trial;
        Nf3_ManSetDefaultPars(&Pars);
        Trial = Nf3_Export(p, &Pars);
        Ok = Trial && Scm_WinModelLookahead(Trial, 1, &Metric->RealArea, &Metric->RealDelay);
        if ( Trial ) Gia_ManStop(Trial);
    }
    Vec_IntForEachEntry(Delta->Changed, ObjId, i) Backup[ObjId] = Original[ObjId];
    if ( BaseState )
    {
        Vec_IntForEachEntry(Delta->Times, ObjId, i)
        {
            State[ObjId] = BaseState[ObjId];
            State[ObjId].Required.Value[0] = State[ObjId].Required.Value[1] = 0;
        }
        Vec_IntForEachEntry(Delta->Loads, ObjId, i) State[ObjId].Load = BaseState[ObjId].Load;
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
    Scm_WinMetric_t * Initial, Scm_WinMetric_t * Kept, Gia_Man_t ** ppKept, int fVerbose, float DelayTarget,
    Scm_WinChecks_t * Pool )
{
    Jf_Par_t Pars;
    Gia_Man_t * Check;
    Scm_WinMetric_t Trial = *Current;
    int Accept;
    Nf3_ManSetDefaultPars(&Pars);
    Check = Nf3_Export(p, &Pars);
    if ( Check == NULL ) return 0;
    if ( Pool )
    {
        int i, Worst = 0;
        if ( !Scm_WinModelLookahead(Check, -2, &Trial.RealArea, &Trial.RealDelay) )
            { Gia_ManStop(Check); return 0; }
        for ( i = 0; i < 2; i++ )
        {
            if ( Pool->Covers[i] == NULL ) { Worst = i; break; }
            if ( Pool->Metrics[i].RealArea*Pool->Metrics[i].RealDelay >
                 Pool->Metrics[Worst].RealArea*Pool->Metrics[Worst].RealDelay ) Worst = i;
        }
        Accept = Pool->Covers[Worst] == NULL || Trial.RealArea*Trial.RealDelay <
            Pool->Metrics[Worst].RealArea*Pool->Metrics[Worst].RealDelay;
        if ( fVerbose ) Abc_Print(1, "SCMAP_WINDOW_SCREEN kept=%d area=%.9g delay=%.9g\n",
            Accept, Trial.RealArea, Trial.RealDelay);
        if ( !Accept ) Gia_ManStop(Check);
        else
        {
            if ( Pool->Covers[Worst] ) Gia_ManStop(Pool->Covers[Worst]);
            Pool->Covers[Worst] = Check; Pool->Metrics[Worst] = Trial;
        }
        return 1;
    }
    if ( !Scm_WinModelLookahead(Check, 1, &Trial.RealArea, &Trial.RealDelay) )
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
    Scm_WinDelta_t * Delta = NULL;
    int * Refs = NULL;
    void * Model = NULL;
    Gia_Man_t * Result = NULL, * Checkpoint = NULL;
    Scm_WinMetric_t Initial, Current, Trial, BestMetric, KeptMetric, ShortMetric[2] = {{0}};
    Scm_WinList_t List = {0};
    Scm_WinChecks_t Checks = {{0}}, * Pool = NULL;
    int fLookahead = nLookahead > 0;
    int nRounds = fLookahead ? 1 : 2, nRoots = fLookahead ? 128 : 4096;
    int nBudget = 32768, nTrials = 0, nFlows = 0;
    int Round, Phase, Limit, Id, i, k, t, Count, Best, nHits = 0, nTwo = 0, Before;
    int nNeutral = 0, nTiming = 0, nGrowing = 0, Kept = 0;
    int nChecks = 0, LastCheck = 0, NextGrowth = 1;
    word Growth = 0;
    double Threshold = 0, Bound, AreaLimit;
    abctime Start = Abc_Clock();
    if ( !fLookahead && DelayTarget == 0 ) Pool = &Checks;
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
    if ( !Scm_WinMeasure(p, Model, State, Refs, Threshold, &Initial, NULL, NULL) ) goto done;
    memcpy(Backup, p->Objs, sizeof(Nf3_Obj_t)*p->nObjs);
    memcpy(TrialState, State, sizeof(Scm_WinState_t)*p->nObjs);
    Delta = Scm_WinDeltaStart(p, Model);
    if ( Delta == NULL ) goto done;
    if ( pQor && pQor->fValid ) { Initial.RealArea = pQor->Area; Initial.RealDelay = pQor->Delay; }
    else if ( !Scm_WinModelLookahead(Gia, 1, &Initial.RealArea, &Initial.RealDelay) ) goto done;
    Current = KeptMetric = Initial;
    Count = 0;
    for ( Id = 2; Id < p->nObjs; Id++ )
        Count += p->Objs[Id].Refs && p->Objs[Id].Gate >= 0;
    if ( !fLookahead && Count > 2000 ) { nRounds = 1; nBudget = 4096; }
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
                    if ( !Scm_WinTrial(p, Backup, Delta, Id, List.Plans+k, Model, State, &Current, TrialState, Refs, Threshold, &Trial, 0) ||
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
                    if ( !Scm_WinTrial(p, Backup, Delta, Id, List.Plans+k, Model, State, &Current, TrialState, Refs, Threshold, &Trial, 1) ) goto done;
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
                if ( !Scm_WinMeasure(p, Model, State, Refs, Threshold, &Current, Backup, TrialState) ||
                     Current.Area != BestMetric.Area || Current.Electrical != BestMetric.Electrical ||
                     !Scm_WinAreaEqual(p->nObjs, Current.EstimatedArea, BestMetric.EstimatedArea) || Current.Pressure != BestMetric.Pressure ) goto done;
                Current.RealArea = BestMetric.RealArea; Current.RealDelay = BestMetric.RealDelay;
                memcpy(Backup, p->Objs, sizeof(Nf3_Obj_t)*p->nObjs);
                memcpy(TrialState, State, sizeof(Scm_WinState_t)*p->nObjs);
                Scm_WinDeltaBuild(p, Delta);
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
                    if ( !Scm_WinCheckpoint(p, &Current, &Initial, &KeptMetric, &Checkpoint, fVerbose, DelayTarget, Pool) ) goto done;
                    nChecks++; LastCheck = nHits;
                    do { NextGrowth++; } while ( (DelayTarget > 0 || NextGrowth <= 4) && Growth >= 0.005 * NextGrowth * Initial.Area );
                }
            }
            if ( !fLookahead && nHits != LastCheck )
            {
                if ( !Scm_WinCheckpoint(p, &Current, &Initial, &KeptMetric, &Checkpoint, fVerbose, DelayTarget, Pool) ) goto done;
                nChecks++; LastCheck = nHits;
            }
        }
        if ( nHits == Before ) break;
    }
    if ( !fLookahead )
    {
        if ( Pool && Pool->Covers[0] && Pool->Covers[1] &&
             Pool->Metrics[1].RealArea*Pool->Metrics[1].RealDelay < Pool->Metrics[0].RealArea*Pool->Metrics[0].RealDelay )
        {
            Gia_Man_t * Temp = Pool->Covers[0];
            Scm_WinMetric_t Metric = Pool->Metrics[0];
            Pool->Covers[0] = Pool->Covers[1]; Pool->Metrics[0] = Pool->Metrics[1];
            Pool->Covers[1] = Temp; Pool->Metrics[1] = Metric;
        }
        for ( i = 0; Pool && i < 2; i++ ) if ( Pool->Covers[i] )
        {
            int Accept;
            if ( i && Checkpoint && Pool->Metrics[1].RealDelay >= 0.995*Pool->Metrics[0].RealDelay ) break;
            Trial = Pool->Metrics[i];
            if ( !Scm_WinModelLookahead(Pool->Covers[i], 1, &Trial.RealArea, &Trial.RealDelay) ) goto done;
            nFlows++;
            Accept = Trial.RealArea <= 1.02*Initial.RealArea && Trial.RealDelay <= Initial.RealDelay &&
                Trial.RealArea*Trial.RealDelay < KeptMetric.RealArea*KeptMetric.RealDelay;
            if ( fVerbose ) Abc_Print(1, "SCMAP_WINDOW_CONFIRM kept=%d area=%.9g delay=%.9g\n",
                Accept, Trial.RealArea, Trial.RealDelay);
            if ( Accept )
            {
                if ( Checkpoint ) Gia_ManStop(Checkpoint);
                Checkpoint = Pool->Covers[i]; Pool->Covers[i] = NULL; KeptMetric = Trial;
            }
        }
        Kept = Checkpoint != NULL; Result = Checkpoint ? Checkpoint : Gia;
        Checkpoint = NULL; Current = KeptMetric; goto report;
    }
    if ( !nHits ) { Current = Initial; Result = Gia; goto report; }
    Result = Nf3_Export(p, &Pars);
    if ( Result == NULL ) goto done;
    if ( !Scm_WinModelLookahead(Result, 1, &Current.RealArea, &Current.RealDelay) )
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
    for ( i = 0; i < 2; i++ ) if ( Checks.Covers[i] ) Gia_ManStop(Checks.Covers[i]);
    ABC_FREE(Backup); ABC_FREE(State); ABC_FREE(TrialState); ABC_FREE(Refs); ABC_FREE(Roots); ABC_FREE(List.Plans);
    Scm_WinDeltaStop(Delta);
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
