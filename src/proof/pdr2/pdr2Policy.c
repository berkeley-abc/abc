/**CFile****************************************************************

  FileName    [pdr2Policy.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Property directed reachability, second implementation.]

  Synopsis    [Selects and runs PDR strategies using the property and transition relation.]

  Author      [ABC contributors]

  Date        [Started November 2026.]

***********************************************************************/

#include <limits.h>
#include "pdr2Int.h"
#include "aig/gia/giaAig.h"
#include "proof/ssw/ssw.h"
#include "sat/bmc/bmc.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Pdr2_PolicyStage_t_ Pdr2_PolicyStage_t;
typedef struct Pdr2_Policy_t_ Pdr2_Policy_t;
struct Pdr2_PolicyStage_t_
{
    const char * pName, * pFlags, * pCommand;
    int nSeconds, nOptions;
    const char * pKeys[32];
    char Values[32][32];
};
struct Pdr2_Policy_t_
{
    int nStages;
    Pdr2_PolicyStage_t Stages[32];
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Follows register transitions to normalize a time-indexed literal.]

  Description []

***********************************************************************/
// Follow at most two next-state edges. A term retains its time coordinate:
// the same input at different steps represents different Boolean variables.
static void Pdr2_PolicyNormalize( Aig_Man_t * pAig, int * pFrame, int * pLit )
{
    int nPis = Saig_ManPiNum(pAig);
    Aig_Obj_t * pObj;
    while ( *pFrame )
    {
        pObj = Aig_ManObj(pAig, Abc_Lit2Var(*pLit));
        if ( !Aig_ObjIsCi(pObj) || Aig_ObjCioId(pObj) < nPis ) break;
        *pLit = Aig_ObjToLit(Aig_ObjChild0(Saig_ManLi(pAig, Aig_ObjCioId(pObj) - nPis))) ^ Abc_LitIsCompl(*pLit);
        --*pFrame;
    }
}

/**Function*************************************************************

  Synopsis    [Collects bounded conjunction or disjunction leaves at a specified time.]

  Description []

***********************************************************************/
static int Pdr2_PolicyFlatten( Aig_Man_t * pAig, int Frame, int Lit, int Polarity,
                             int * pSeen, int Stamp, Vec_Int_t * vWork, Vec_Int_t * vLeaves )
{
    int nObjs = Aig_ManObjNumMax(pAig), nSeen = 0, Key;
    Aig_Obj_t * pObj;
    Vec_IntClear(vWork);
    Vec_IntClear(vLeaves);
    Vec_IntPushTwo(vWork, Frame, Lit);
    while ( Vec_IntSize(vWork) && nSeen < 4096 )
    {
        Lit = Vec_IntPop(vWork);
        Frame = Vec_IntPop(vWork);
        Pdr2_PolicyNormalize(pAig, &Frame, &Lit);
        Key = 2 * nObjs * Frame + Lit;
        assert( Key >= 0 && Key < 6 * nObjs );
        if ( pSeen[Key] == Stamp ) continue;
        pSeen[Key] = Stamp;
        nSeen++;
        pObj = Aig_ManObj(pAig, Abc_Lit2Var(Lit));
        if ( Abc_LitIsCompl(Lit) == Polarity && Aig_ObjIsNode(pObj) )
        {
            int Lit0 = Aig_ObjToLit(Aig_ObjChild0(pObj));
            int Lit1 = Aig_ObjToLit(Aig_ObjChild1(pObj));
            // Binary AIGER puts the larger fanin first. Canonical traversal
            // keeps the bounded measurements stable after native hashing.
            Vec_IntPushTwo(vWork, Frame, Abc_MaxInt(Lit0, Lit1) ^ Polarity);
            Vec_IntPushTwo(vWork, Frame, Abc_MinInt(Lit0, Lit1) ^ Polarity);
        }
        else
            Vec_IntPushTwo(vLeaves, Frame, Lit);
    }
    return Vec_IntSize(vWork) != 0;
}

static const char * const Pdr2_PolicyFeatureNames[12] = {
    "inputs", "flops", "ands", "cone0_flops", "cone0_inputs", "cone0_ands",
    "look0_terms", "look0_max_or", "look0_capped", "look2_terms", "look2_max_or", "look2_capped" };

/**Function*************************************************************

  Synopsis    [Measures the input, register and property cones used for stage selection.]

  Description []

***********************************************************************/
static int Pdr2_PolicyFeatures( Aig_Man_t * pAig, int * Features )
{
    int nObjs = Aig_ManObjNumMax(pAig), * pSeen;
    int i, d, k, Id, Stamp = 1, Bad, Width;
    Vec_Int_t * vWork, * vTerms, * vLeaves;
    Aig_Obj_t * pObj;
    if ( Saig_ManPoNum(pAig) != 1 || Saig_ManConstrNum(pAig) || Aig_ManBufNum(pAig) || Aig_ManExorNum(pAig) ||
         nObjs > INT_MAX / 6 || (size_t)nObjs > (size_t)-1 / (6 * sizeof(int)) )
        return 0;
    memset(Features, 0, 12 * sizeof(int));
    Features[0] = Saig_ManPiNum(pAig);
    Features[1] = Aig_ManRegNum(pAig);
    Features[2] = Aig_ManNodeNum(pAig);
    pSeen = ABC_CALLOC(int, (size_t)6 * nObjs);
    vWork = Vec_IntAlloc(256);
    vTerms = Vec_IntAlloc(256);
    vLeaves = Vec_IntAlloc(256);
    Bad = Aig_ObjToLit(Aig_ObjChild0(Aig_ManCo(pAig, 0)));
    Vec_IntPush(vWork, Abc_Lit2Var(Bad));
    while ( Vec_IntSize(vWork) )
    {
        Id = Vec_IntPop(vWork);
        if ( pSeen[Id] == Stamp ) continue;
        pSeen[Id] = Stamp;
        pObj = Aig_ManObj(pAig, Id);
        if ( Aig_ObjIsNode(pObj) )
        {
            Features[5]++;
            Vec_IntPush(vWork, Aig_ObjFaninId0(pObj));
            Vec_IntPush(vWork, Aig_ObjFaninId1(pObj));
        }
        else if ( Aig_ObjIsCi(pObj) )
            Features[Aig_ObjCioId(pObj) < Features[0] ? 4 : 3]++;
    }
    for ( d = 0; d <= 2; d += 2 )
    {
        k = 6 + 3 * (d / 2);
        Features[k+2] = Pdr2_PolicyFlatten(pAig, d, Bad, 0, pSeen, ++Stamp, vWork, vTerms);
        Features[k] = Vec_IntSize(vTerms) / 2;
        for ( i = 0; i < Vec_IntSize(vTerms); i += 2 )
        {
            Pdr2_PolicyFlatten(pAig, Vec_IntEntry(vTerms,i), Vec_IntEntry(vTerms,i+1),
                              1, pSeen, ++Stamp, vWork, vLeaves);
            Width = Vec_IntSize(vLeaves) / 2;
            Features[k+1] = Abc_MaxInt(Features[k+1], Width);
        }
    }
    ABC_FREE(pSeen);
    Vec_IntFree(vWork);
    Vec_IntFree(vTerms);
    Vec_IntFree(vLeaves);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Writes the structural measurements as a JSON object.]

  Description []

***********************************************************************/
static void Pdr2_PolicyPrintFeatures( int * Features )
{
    int i;
    if ( Features == NULL ) { Abc_Print(1, "null"); return; }
    Abc_Print(1, "{");
    for ( i = 0; i < 12; i++ )
        Abc_Print(1, "%s\"%s\":%d", i ? "," : "", Pdr2_PolicyFeatureNames[i], Features[i]);
    Abc_Print(1, "}");
}

/**Function*************************************************************

  Synopsis    [Prints the feature record for the current safety property.]

  Description []

***********************************************************************/
void Pdr2_ManPrintFeatures( Aig_Man_t * pAig )
{
    int Features[12], fValid = Pdr2_PolicyFeatures(pAig, Features);
    Abc_Print(1, "PDR2_FEATURES ");
    Pdr2_PolicyPrintFeatures(fValid ? Features : NULL);
    Abc_Print(1, "\n");
}

/**Function*************************************************************

  Synopsis    [Sets a numeric option in a policy stage.]

  Description []

***********************************************************************/
static void Pdr2_PolicyOption( Pdr2_PolicyStage_t * p, const char * pKey, int Value )
{
    int i;
    for ( i = 0; i < p->nOptions; i++ ) if ( !strcmp(p->pKeys[i], pKey) ) break;
    assert(i < 32);
    if ( i == p->nOptions ) p->pKeys[p->nOptions++] = pKey;
    snprintf(p->Values[i], sizeof(p->Values[i]), "%d", Value);
}

/**Function*************************************************************

  Synopsis    [Appends a stage with its name, time budget and PDR flags.]

  Description []

***********************************************************************/
static Pdr2_PolicyStage_t * Pdr2_PolicyAdd( Pdr2_Policy_t * p, const char * pName, int Seconds, const char * pFlags )
{
    Pdr2_PolicyStage_t * s;
    assert(p->nStages < 32);
    s = &p->Stages[p->nStages++];
    s->pName = pName; s->nSeconds = Seconds; s->pFlags = pFlags ? pFlags : "-g -B 0";
    Pdr2_PolicyOption(s, "PDR2_COMPACT", 1);
    return s;
}

/**Function*************************************************************

  Synopsis    [Prepends a bounded CTG search in the alternative multiplexer encoding.]

***********************************************************************/
static void Pdr2_PolicyMuxFirst( Pdr2_Policy_t * p, Aig_Man_t * pAig, Pdr2_Par_t * pPars, abctime Stop )
{
    const char * pValue = Gip_OptionGet("PDR2_JOINT_MUX");
    Pdr2_PolicyStage_t First, * s;
    int Seconds = pValue ? Abc_MinInt(60, atoi(pValue)) : 0;
    if ( Seconds <= 0 || p->nStages >= 32 || !Pdr2_ManHasMuxReduction(pAig, pPars, Stop) ) return;
    s = Pdr2_PolicyAdd(p, "mux-encoding", Seconds, "-g -B 0 -S 1");
    Pdr2_PolicyOption(s, "PDR2_MUX_PHASE", 1);
    Pdr2_PolicyOption(s, "PDR2_COI", 1);
    Pdr2_PolicyOption(s, "PDR2_BMC", 0);
    First = *s;
    memmove(p->Stages + 1, p->Stages, (p->nStages - 1) * sizeof(First));
    p->Stages[0] = First;
}

/**Function*************************************************************

  Synopsis    [Schedules a bounded search for a concrete witness.]

  Description []

***********************************************************************/
static void Pdr2_PolicyBmc( Pdr2_Policy_t * p, int Seconds )
{
    Pdr2_PolicyStage_t * s = Pdr2_PolicyAdd(p, "bounded-witness", Seconds, NULL);
    Pdr2_PolicyOption(s, "PDR2_BMCFIRST", Seconds);
    Pdr2_PolicyOption(s, "PDR2_BMC_CONFS", 5000);
    Pdr2_PolicyOption(s, "PDR2_BMC_FRAMES", 64);
    Pdr2_PolicyOption(s, "PDR2_BMC_ONLY", 1);
}

/**Function*************************************************************

  Synopsis    [Schedules grouped transitions with a shared 180-second budget.]

  Description []

***********************************************************************/
static void Pdr2_PolicyStride( Pdr2_Policy_t * p, int Stride, int fRetry )
{
    Pdr2_PolicyStage_t * s;
    int i, Budgets[2] = { 180, 160 };
    if ( fRetry ) Budgets[0] = 20;
    for ( i = 0; i <= fRetry; i++ )
    {
        s = Pdr2_PolicyAdd(p, i ? "stride-retry" : "temporal-stride", Budgets[i], NULL);
        Pdr2_PolicyOption(s, "PDR2_STRIDE", Stride);
        Pdr2_PolicyOption(s, "PDR2_STRIDE_TIME", Budgets[i]);
        Pdr2_PolicyOption(s, "PDR2_STRIDE_ONLY", 1);
    }
}

/**Function*************************************************************

  Synopsis    [Searches at one bounded depth and leaves earlier depths to PDR.]

***********************************************************************/
static void Pdr2_PolicyTarget( Pdr2_PolicyStage_t * s, int Seconds, int Depth )
{
    Pdr2_PolicyOption(s, "PDR2_BMCFIRST", Seconds);
    Pdr2_PolicyOption(s, "PDR2_BMC_HORIZON", Depth);
    Pdr2_PolicyOption(s, "PDR2_BMC_ONLY", 1);
    if ( Gip_OptionGet("PDR2_JOINT_TERMS") )
        Pdr2_PolicyOption(s, "PDR2_BMC_TERMS", Abc_MaxInt(1, Abc_MinInt(64, atoi(Gip_OptionGet("PDR2_JOINT_TERMS")))));
    if ( Gip_OptionGet("PDR2_JOINT_LIVE") )
        Pdr2_PolicyOption(s, "PDR2_BMC_WINDOW", Abc_MaxInt(0, Abc_MinInt(2, atoi(Gip_OptionGet("PDR2_JOINT_LIVE")))));
    if ( Gip_OptionGet("PDR2_JOINT_POLAR") )
        Pdr2_PolicyOption(s, "PDR2_BMC_POLAR", 1);
}

/**Function*************************************************************

  Synopsis    [Adds a bounded witness stage on the concrete machine.]

***********************************************************************/
static void Pdr2_PolicyHorizon( Pdr2_Policy_t * p, int Seconds, int Depth )
{
    Pdr2_PolicyTarget(Pdr2_PolicyAdd(p, "fixed-depth-witness", Seconds, NULL), Seconds, Depth);
}

/**Function*************************************************************

  Synopsis    [Selects the PDR search used on a post-reset transition relation.]

***********************************************************************/
static void Pdr2_PolicyTail( Pdr2_Policy_t * p, int Seconds, int Depth, int fRefine, int Style )
{
    Pdr2_PolicyStage_t * s = Pdr2_PolicyAdd(p, "post-reset", Seconds, NULL);
    s->pCommand = "tail";
    Pdr2_PolicyOption(s, "PDR2_TAIL_DEPTH", Depth);
    if ( fRefine ) Pdr2_PolicyOption(s, "PDR2_TAIL_REFINE", 1);
    if ( Style == 1 || Style == 5 || Style == 6 ) Pdr2_PolicyOption(s, "PDR2_DROP_HISTORY", 3);
    if ( Style == 2 )
    {
        Pdr2_PolicyOption(s, "PDR2_STRIDE", 2);
        Pdr2_PolicyOption(s, "PDR2_STRIDE_TIME", Seconds);
        Pdr2_PolicyOption(s, "PDR2_STRIDE_ONLY", 1);
    }
    if ( Style == 3 )
    {
        Pdr2_PolicyOption(s, "PDR2_INPUT_DECISIONS", 1);
        Pdr2_PolicyOption(s, "PDR2_CNFJUST", 1);
        Pdr2_PolicyOption(s, "PDR2_VERIFY_POLICY", 1);
    }
    if ( Style == 4 ) Pdr2_PolicyOption(s, "PDR2_MIC_GROUP", 4);
    if ( Style == 5 ) s->pFlags = "-g -B 0 -U 1";
    if ( Style == 6 ) Pdr2_PolicyOption(s, "PDR2_MICFAIL", 1);
    if ( Style == 7 ) s->pFlags = "-t -g";
    if ( Style == 8 ) s->pFlags = "-g -B 0 -H 1 -i -K 2 -U 1";
    if ( Style == 9 || Style == 10 ) Pdr2_PolicyOption(s, "PDR2_MIC_GROUP", Style-2);
    if ( Gip_OptionGet("PDR2_JOINT_TAIL_CUT") )
        Pdr2_PolicyOption(s, "PDR2_SAMPLE", Abc_MaxInt(2, Abc_MinInt(64, atoi(Gip_OptionGet("PDR2_JOINT_TAIL_CUT")))));
    if ( Style )
    {
        Pdr2_PolicyOption(s, "PDR2_WATCH_PACK", 1);
        Pdr2_PolicyOption(s, "PDR2_WATCH_AHEAD", 4);
    }
}

/**Function*************************************************************

  Synopsis    [Schedules property decomposition with optional lookahead and isomorphism checks.]

  Description []

***********************************************************************/
static void Pdr2_PolicySplit( Pdr2_Policy_t * p, int Seconds, int Depth, int Width, int Maximum, int fIso )
{
    Pdr2_PolicyStage_t * s = Pdr2_PolicyAdd(p, "decompose", Seconds, NULL);
    Pdr2_PolicyOption(s, "PDR2_SPLIT", Seconds);
    Pdr2_PolicyOption(s, "PDR2_SPLIT_MAX", Maximum);
    Pdr2_PolicyOption(s, "PDR2_SPLIT_WIDTH", Width);
    Pdr2_PolicyOption(s, "PDR2_SPLIT_ORDER", 1);
    Pdr2_PolicyOption(s, "PDR2_SPLIT_ONLY", 1);
    if ( Depth )
    {
        Pdr2_PolicyOption(s, "PDR2_SHIFT", Seconds);
        Pdr2_PolicyOption(s, "PDR2_SHIFT_DEPTH", Depth);
        Pdr2_PolicyOption(s, "PDR2_SHIFT_INIT", 2000);
        Pdr2_PolicyOption(s, "PDR2_SHIFT_ONLY", 1);
    }
    if ( fIso ) Pdr2_PolicyOption(s, "PDR2_ISOREDUCE", 20);
}

/**Function*************************************************************

  Synopsis    [Schedules input-guided SAT search and CNF justification.]

  Description []

***********************************************************************/
static void Pdr2_PolicyInputs( Pdr2_Policy_t * p, int Seconds, int fShared )
{
    Pdr2_PolicyStage_t * s = Pdr2_PolicyAdd(p, "input-search", Seconds, NULL);
    Pdr2_PolicyOption(s, "PDR2_INPUT_DECISIONS", 1);
    Pdr2_PolicyOption(s, "PDR2_CNFJUST", 1);
    Pdr2_PolicyOption(s, "PDR2_VERIFY_POLICY", 1);
    if ( fShared ) Pdr2_PolicyOption(s, "PDR2_SHARED", 4);
}

/**Function*************************************************************

  Synopsis    [Schedules a PDR abstraction stage.]

  Description []

***********************************************************************/
static void Pdr2_PolicyAbs( Pdr2_Policy_t * p, int Seconds, int fDynamic )
{
    Pdr2_PolicyAdd(p, fDynamic ? "dynamic-abstraction" : "abstraction", Seconds,
                     fDynamic ? "-t -D 0 -S 0" : "-t -g");
}

/**Function*************************************************************

  Synopsis    [Schedules PDR with zero-biased initial SAT phases.]

  Description []

***********************************************************************/
static void Pdr2_PolicyZero( Pdr2_Policy_t * p, int Seconds )
{
    Pdr2_PolicyOption(Pdr2_PolicyAdd(p, "zero-phases", Seconds, NULL), "PDR2_PHASESIM", 2);
}

/**Function*************************************************************

  Synopsis    [Adds an all-state safety query on the combinational property cone.]

***********************************************************************/
static void Pdr2_PolicyCombSafe( Pdr2_Policy_t * p, int Sweep, int Width, int fCadical, int DefaultConfs )
{
    int Confs = Gip_OptionGet("PDR2_JOINT_CSAFE_CONFS") ?
        Abc_MaxInt(1, atoi(Gip_OptionGet("PDR2_JOINT_CSAFE_CONFS"))) : DefaultConfs;
    Pdr2_PolicyStage_t * s = Pdr2_PolicyAdd( p, "combinational-sweep", 90, NULL );
    s->pCommand = Width ? "comb-projection" : "comb-safe";
    if ( Width )
        Pdr2_PolicyOption( s, "PDR2_PROJECT", Width );
    if ( Sweep > 0 )
        Pdr2_PolicyOption( s, "PDR2_CSAFE_CEC", Abc_MinInt(10000, Sweep) );
    if ( Gip_OptionGet("PDR2_JOINT_KISSAT") && atoi(Gip_OptionGet("PDR2_JOINT_KISSAT")) )
        Pdr2_PolicyOption( s, "PDR2_CSAFE_KISSAT", 1 );
    else if ( fCadical )
        Pdr2_PolicyOption( s, "PDR2_CSAFE_CADICAL", 1 );
    if ( Gip_OptionGet("PDR2_JOINT_CTRACE") )
        Pdr2_PolicyOption( s, "PDR2_CSAFE_TRACE", atoi(Gip_OptionGet("PDR2_JOINT_CTRACE")) );
    Pdr2_PolicyOption( s, "PDR2_CSAFE", Confs );
    Pdr2_PolicyOption( s, "PDR2_CSAFE_TIME", 90 );
}

/**Function*************************************************************

  Synopsis    [Adds a binary encoding stage for large mutually exclusive groups.]

***********************************************************************/
static void Pdr2_PolicyMutex( Pdr2_Policy_t * p, int Seconds, int Minimum )
{
    Pdr2_PolicyStage_t * s = Pdr2_PolicyAdd(p, "mutex-recoding", Seconds, "-g -B 0");
    s->pCommand = "mutex";
    Pdr2_PolicyOption(s, "PDR2_MUTEX_MIN", Minimum);
}

/**Function*************************************************************

  Synopsis    [Uses cut-mapped SAT for expensive bad-state and certificate queries.]

***********************************************************************/
static void Pdr2_PolicyMappedBad( Pdr2_PolicyStage_t * s, int fReuse )
{
    Pdr2_PolicyOption(s, "PDR2_BMC", 0);
    Pdr2_PolicyOption(s, "PDR2_COI", 0);
    Pdr2_PolicyOption(s, "PDR2_VERIFY_BATCH", 3);
    Pdr2_PolicyOption(s, "PDR2_BAD_MAPPED_SECS", 40);
    Pdr2_PolicyOption(s, "PDR2_BAD_MAPPED_CONFS", 512);
    if ( fReuse ) Pdr2_PolicyOption(s, "PDR2_BAD_REUSE_SECS", 2);
}

/**Function*************************************************************

  Synopsis    [Tests a numeric policy switch.]

***********************************************************************/
static int Pdr2_PolicyEnabled( const char * pName )
{
    const char * pValue = Gip_OptionGet(pName);
    return pValue && atoi(pValue) != 0;
}

/**Function*************************************************************

  Synopsis    [Selects sequential verification stages from structural measurements.]

  Description []

***********************************************************************/
// Select verification stages from structural measurements of the input circuit.
static void Pdr2_PolicyBuild( Pdr2_Policy_t * p, int * pFeatures )
{
    double nPis = 0, nRegs = 0, nConeRegs = 0, nTerms0 = 0, nTerms2 = 0;
    double nAnds = 0, nWidth0 = 0, nWidth2 = 0;
    int i, fProject = 0, Mix = Gip_OptionGet("PDR2_JOINT_MIX") ? atoi(Gip_OptionGet("PDR2_JOINT_MIX")) : 0;
    Pdr2_PolicyStage_t * s;
    if ( pFeatures )
    {
        nPis = pFeatures[0];
        nRegs = pFeatures[1];
        nAnds = pFeatures[2];
        nConeRegs = pFeatures[3];
        nTerms0 = pFeatures[6];
        nWidth0 = pFeatures[7];
        nTerms2 = pFeatures[9];
        nWidth2 = pFeatures[10];
        fProject = Mix >= 7 && 1000 <= nRegs && nRegs <= 10000 && 0 < nConeRegs &&
                   32*nConeRegs <= nRegs && (Mix < 8 || nPis <= 4*nRegs);
    }
    if ( Gip_OptionGet("PDR2_JOINT_MUTEX") && pFeatures && pFeatures[1] )
    {
        Pdr2_PolicyMutex(p, 180, Abc_MaxInt(2, atoi(Gip_OptionGet("PDR2_JOINT_MUTEX"))));
        if ( Pdr2_PolicyEnabled("PDR2_JOINT_MUTEX_ONLY") ) goto adjust;
    }
    if ( Gip_OptionGet("PDR2_JOINT_INPUT_LATCHES") && pFeatures && pFeatures[1] )
    {
        Pdr2_PolicyAdd(p, "private-input-latches", 180, NULL)->pCommand = "input-latches";
        if ( Pdr2_PolicyEnabled("PDR2_JOINT_INPUT_LATCHES_ONLY") ) goto adjust;
    }
    if ( Gip_OptionGet("PDR2_JOINT_CEC") )
    {
        int Width = Gip_OptionGet("PDR2_JOINT_PROJECT") ?
            Abc_MaxInt(1, Abc_MinInt(8, atoi(Gip_OptionGet("PDR2_JOINT_PROJECT")))) : 0;
        Pdr2_PolicyCombSafe( p, atoi(Gip_OptionGet("PDR2_JOINT_CEC")), Width,
            Gip_OptionGet("PDR2_JOINT_CADICAL") && atoi(Gip_OptionGet("PDR2_JOINT_CADICAL")), 500000 );
        if ( Pdr2_PolicyEnabled("PDR2_JOINT_CEC_ONLY") ) goto adjust;
    }
    if ( Gip_OptionGet("PDR2_JOINT_CUT") && pFeatures && pFeatures[1] )
    {
        s = Pdr2_PolicyAdd(p, "sampled-property", 180, NULL);
        s->pCommand = "sample";
        Pdr2_PolicyOption(s, "PDR2_SAMPLE", Abc_MaxInt(2, Abc_MinInt(64, atoi(Gip_OptionGet("PDR2_JOINT_CUT")))));
        if ( Pdr2_PolicyEnabled("PDR2_JOINT_CUT_ONLY") ) goto adjust;
    }
    if ( Gip_OptionGet("PDR2_JOINT_HORIZON") )
    {
        Pdr2_PolicyHorizon(p, 90, atoi(Gip_OptionGet("PDR2_JOINT_HORIZON")));
        if ( Pdr2_PolicyEnabled("PDR2_JOINT_HORIZON_ONLY") ) goto adjust;
    }
    if ( Gip_OptionGet("PDR2_JOINT_GATES") && pFeatures )
    {
        s = Pdr2_PolicyAdd(p, "gate-refinement", 180, NULL);
        s->pCommand = "gates";
        Pdr2_PolicyOption(s, "PDR2_GATE_LAYERS", Abc_MaxInt(1, Abc_MinInt(16, atoi(Gip_OptionGet("PDR2_JOINT_GATES")))));
        if ( Gip_OptionGet("PDR2_JOINT_GATE_FLOPS") ) Pdr2_PolicyOption(s, "PDR2_GATE_FLOPS", 1);
        if ( Gip_OptionGet("PDR2_JOINT_GATE_HORIZON") )
            Pdr2_PolicyTarget(s, 180, Abc_MaxInt(0, Abc_MinInt(256, atoi(Gip_OptionGet("PDR2_JOINT_GATE_HORIZON")))));
        if ( Gip_OptionGet("PDR2_JOINT_GATE_SHARE") )
        {
            Pdr2_PolicyOption(s, "PDR2_GATE_SHARE", 1);
            Pdr2_PolicyOption(s, "PDR2_PART_SHARE", Abc_MaxInt(1, Abc_MinInt(30, atoi(Gip_OptionGet("PDR2_JOINT_GATE_SHARE")))));
        }
        if ( Pdr2_PolicyEnabled("PDR2_JOINT_GATES_ONLY") ) goto adjust;
    }
    if ( Gip_OptionGet("PDR2_JOINT_TAIL") && pFeatures && pFeatures[1] )
    {
        int Style = Gip_OptionGet("PDR2_JOINT_TAIL_STYLE") ? atoi(Gip_OptionGet("PDR2_JOINT_TAIL_STYLE")) : 0;
        Pdr2_PolicyTail(p, 140, Abc_MaxInt(1, Abc_MinInt(32, atoi(Gip_OptionGet("PDR2_JOINT_TAIL")))),
                       Gip_OptionGet("PDR2_JOINT_TAIL_REFINE") != NULL, Style);
        if ( Pdr2_PolicyEnabled("PDR2_JOINT_TAIL_ONLY") ) goto adjust;
    }
    if ( Gip_OptionGet("PDR2_JOINT_WINDOW") )
    {
        s = Pdr2_PolicyAdd(p, "window-bmc", 90, NULL);
        s->pCommand = "window";
        Pdr2_PolicyOption(s, "PDR2_WINDOW", Abc_MaxInt(1, Abc_MinInt(256, atoi(Gip_OptionGet("PDR2_JOINT_WINDOW")))));
        if ( Pdr2_PolicyEnabled("PDR2_JOINT_WINDOW_ONLY") ) goto adjust;
    }
    if ( Gip_OptionGet("PDR2_JOINT_INPUTS") && pFeatures )
    {
        int Width = atoi(Gip_OptionGet("PDR2_JOINT_INPUTS"));
        if ( Width >= 2 && pFeatures[0] >= Width )
        {
            s = Pdr2_PolicyAdd(p, "correlated-input-witness", 60, "-g -B 0 -q -P 3");
            s->pCommand = "input-probe";
            Pdr2_PolicyOption(s, "PDR2_INPUT_WIDTH", Abc_MinInt(Width, 256));
            Pdr2_PolicyOption(s, "PDR2_INPUT_BOUNDED", Gip_OptionGet("PDR2_JOINT_INPUT_BMC") != NULL);
            if ( Gip_OptionGet("PDR2_JOINT_INPUT_LANES") )
                Pdr2_PolicyOption(s, "PDR2_INPUT_LANES", Abc_MinInt(2, atoi(Gip_OptionGet("PDR2_JOINT_INPUT_LANES"))));
            if ( Gip_OptionGet("PDR2_JOINT_INPUT_DEPTH") )
            {
                Pdr2_PolicyOption(s, "PDR2_INPUT_BOUNDED", 0);
                Pdr2_PolicyOption(s, "PDR2_BMCFIRST", 60);
                Pdr2_PolicyOption(s, "PDR2_BMC_HORIZON", atoi(Gip_OptionGet("PDR2_JOINT_INPUT_DEPTH")));
                Pdr2_PolicyOption(s, "PDR2_BMC_ONLY", 1);
                s->pFlags = "-g -B 0";
            }
        }
        if ( Pdr2_PolicyEnabled("PDR2_JOINT_INPUT_ONLY") ) goto adjust;
    }
    if ( pFeatures == NULL ) goto ordinary;
    if ( Mix > 0 )
    {
        // When most gates feed the property, an all-state proof can avoid
        // rediscovering the same combinational contradiction in PDR frames.
        if ( Mix >= 7 && !Gip_OptionGet("PDR2_JOINT_CEC") && nAnds >= 15000 &&
             pFeatures[5] >= .95*nAnds && nTerms0 <= 8 )
        {
            int Width = nRegs <= 32 && nConeRegs <= 8 ? 8 : 0;
            Pdr2_PolicyCombSafe(p, 0, Width, 1, Mix >= 9 && Width ? 5000000 : 500000);
            // When the unrestricted check leaves a possible bad state, try
            // blocking it in PDR with a mapped solver for expensive queries.
            if ( Mix >= 11 && nRegs > 0 )
                Pdr2_PolicyMappedBad(Pdr2_PolicyAdd(p, "mapped-bad-states", 300, NULL), Mix >= 13);
        }
        if ( Mix >= 9 && !Gip_OptionGet("PDR2_JOINT_MUTEX") && 96 <= nRegs && nRegs <= 1024 &&
             nPis >= 96 && nConeRegs >= .75*nRegs && nAnds >= 3*nRegs )
            Pdr2_PolicyMutex(p, 90, 96);
        // Dense property cones with several wide terms can admit many witnesses
        // at one depth even when proving each earlier bound is expensive.
        if ( nAnds < 150000 && ((.8*nRegs <= nPis && nPis <= 1.5*nRegs &&
               nConeRegs > .8*nRegs && 10 <= nTerms2 && nTerms2 <= 64 && nWidth2 >= 10) ||
               (32 <= nRegs && nRegs <= 192 && nPis > 8*nRegs && nTerms2 <= 2 && nWidth2 >= 8)) )
            Pdr2_PolicyHorizon(p, 12, 48);
        if ( 64 < nRegs && nRegs <= 512 && nPis <= 128 && nAnds < 30000 &&
             nConeRegs > .72*nRegs && nTerms2 <= 2 && nWidth2 <= 4 )
        {
            Pdr2_PolicyTail(p, 45, 1, 0, 0);
            s = Pdr2_PolicyAdd(p, "limited-generalization", 100, NULL);
            Pdr2_PolicyOption(s, "PDR2_MICFAIL", 1);
        }
        if ( nRegs >= 20000 && nPis > 1.7*nRegs && nConeRegs <= 128 )
        {
            if ( Mix >= 6 )
            {
                s = Pdr2_PolicyAdd(p, "gate-refinement", 8, NULL);
                s->pCommand = "gates";
                Pdr2_PolicyOption(s, "PDR2_GATE_LAYERS", 1);
                Pdr2_PolicyOption(s, "PDR2_GATE_FLOPS", 1);
            }
            if ( Mix >= 3 ) Pdr2_PolicyInputs(p, 60, 0);
            Pdr2_PolicyTail(p, 75, 1, 0, 0);
        }
        if ( Mix >= 2 && 1000 <= nRegs && nRegs <= 3000 && .8*nRegs <= nPis &&
             nPis <= 1.5*nRegs && nConeRegs > nRegs/2 && nTerms2 <= 3 )
        {
            int Seconds = Mix >= 7 && nConeRegs >= .85*nRegs ? 90 : 160;
            if ( Gip_OptionGet("PDR2_JOINT_TAIL_TIME") )
                Seconds = Abc_MaxInt(1, Abc_MinInt(900, atoi(Gip_OptionGet("PDR2_JOINT_TAIL_TIME"))));
            Pdr2_PolicyTail(p, Seconds, 1, 1, Mix >= 6 ? 8 : 1);
        }
    }
    if ( 0 < nRegs && nRegs <= 64 && nAnds < 30000 )
    {
        s = Pdr2_PolicyAdd(p, "bdd-square", 2, NULL);
        Pdr2_PolicyOption(s, "PDR2_BDDSQUARE", 2); Pdr2_PolicyOption(s, "PDR2_BDD_ONLY", 1);
        if ( nConeRegs >= .8*nRegs && nTerms0 >= 64 ) Pdr2_PolicySplit(p, 80, 0, 2, 1024, 1);
    }
    if ( nRegs >= 20000 )
    {
        if ( Mix < 3 || !(nPis > 1.7*nRegs && nConeRegs <= 128) )
        {
            Pdr2_PolicyBmc(p, 15);
            if ( nWidth2 <= 2 || nConeRegs > 8 ) Pdr2_PolicyInputs(p, 45, 0);
        }
        if ( nConeRegs <= 8 ) Pdr2_PolicyAbs(p, 900, 0);
        goto ordinary;
    }
    if ( nRegs >= 64 && nAnds > 100*nRegs && nTerms0 >= 100 ) Pdr2_PolicyBmc(p, 40);
    else if ( nRegs >= 10000 || (nRegs >= 1000 && nAnds > 100*nRegs) ) Pdr2_PolicyBmc(p, 12);
    if ( nRegs && nAnds > 500*nRegs && nTerms2 <= 8 )
    {
        if ( nPis < 8*nRegs ) Pdr2_PolicySplit(p, 25, 2, 1, 4, 0);
        s = Pdr2_PolicyAdd(p, "treb-generalization", 850, "-g -B 0 -H 1");
        Pdr2_PolicyOption(s, "PDR2_MICFAIL", 1);
    }
    if ( nRegs >= 256 && .8*nRegs <= nPis && nPis <= 1.5*nRegs && 10 <= nTerms2 && nTerms2 <= 64 && nWidth2 >= 10 )
    {
        if ( nRegs < 1024 && nConeRegs >= nRegs/2 && nWidth2 <= 16 ) Pdr2_PolicySplit(p, 90, 0, 2, 1024, 1);
        else if ( !(nRegs < 2000 && nConeRegs < 64 && 16 < nWidth2 && nWidth2 <= 20) )
            Pdr2_PolicySplit(p, 120, nWidth2 <= 32 ? 1 : 2, nRegs <= 4096 && nConeRegs >= nRegs/2 && nWidth2 <= 16 && nTerms2 >= 40 ? 2 : 1, 1024, 0);
    }
    if ( 256 < nRegs && nRegs <= 1024 && nPis > 256 && nTerms2 >= 64 && nConeRegs < nRegs/2 )
    {
        s = Pdr2_PolicyAdd(p, "induction-prefix", 3, NULL);
        Pdr2_PolicyOption(s, "PDR2_KIND_PREFIX", 3); Pdr2_PolicyOption(s, "PDR2_KIND_DEPTH", 64);
        Pdr2_PolicyOption(s, "PDR2_KIND_ONLY", 1);
    }
    if ( 32 < nRegs && nRegs <= 1024 && nAnds <= 200000 && !(nPis <= 64 && nTerms2 <= 2 && nWidth2 <= 4) &&
         ((nConeRegs <= 8 && nWidth0 <= 2) || (nWidth0 == 1 && nTerms0 >= .8*nRegs) || (nRegs <= 64 && nPis >= 32)) )
    {
        s = Pdr2_PolicyAdd(p, "reverse", 45, NULL);
        Pdr2_PolicyOption(s, "PDR2_REVERSE", 45); Pdr2_PolicyOption(s, "PDR2_REVERSE_INIT", 1);
        Pdr2_PolicyOption(s, "PDR2_REVERSE_SEED", 2); Pdr2_PolicyOption(s, "PDR2_REVERSE_ONLY", 1);
        if ( (nConeRegs <= 4 && nTerms2 > 16) || nRegs <= 64 )
        {
            Pdr2_PolicyOption(s, "PDR2_REVERSE_WITNESS", 1); Pdr2_PolicyOption(s, "PDR2_STRIDE_REVERSE", 1);
            Pdr2_PolicyOption(s, "PDR2_STRIDE", 2); Pdr2_PolicyOption(s, "PDR2_STRIDE_TIME", 45);
            Pdr2_PolicyOption(s, "PDR2_STRIDE_ONLY", 1);
        }
    }
    if ( 64 < nRegs && nRegs <= 512 && nPis <= 128 && nTerms2 <= 2 && nWidth2 <= 4 && nAnds < 30000 )
    {
        s = Pdr2_PolicyAdd(p, "partitioned-reachability", 180, NULL);
        Pdr2_PolicyOption(s, "PDR2_PARTBDD", 180); Pdr2_PolicyOption(s, "PDR2_PARTBDD_ONLY", 1);
        Pdr2_PolicyOption(s, "PDR2_PARTBDD_MEM", 512); Pdr2_PolicyOption(s, "PDR2_PARTBDD_REGS", 512);
        Pdr2_PolicyOption(s, "PDR2_PARTBDD_PIS", 1024);
        if ( nPis <= 8 && nRegs <= 128 )
        {
            Pdr2_PolicyOption(s, "PDR2_STRIDE", 4); Pdr2_PolicyOption(s, "PDR2_STRIDE_TIME", 180);
            Pdr2_PolicyOption(s, "PDR2_STRIDE_ONLY", 1); Pdr2_PolicyOption(s, "PDR2_PARTBDD_PART", 1);
        }
    }
    if ( nPis <= 64 && nRegs >= 64 && nConeRegs <= 4 && nTerms2 <= 64 ) Pdr2_PolicySplit(p, 60, 2, 1, 1024, 0);
    if ( 1000 <= nRegs && nRegs <= 2000 && nPis <= nRegs/4 && nTerms2 >= 16 && nWidth2 >= 64 )
        Pdr2_PolicyAdd(p, "random-witness", 20, NULL)->pCommand = "sim3";
    if ( nRegs >= 64 && nTerms0 >= 1024 )
    {
        if ( nWidth0 <= 8 || nAnds < 50*nRegs ) Pdr2_PolicyAdd(p, "treb", 700, "-g -B 0 -S 0 -H 1 -i -K 2 -U 1");
        Pdr2_PolicyAbs(p, 900, 1);
    }
    else if ( 64 < nRegs && nRegs <= 256 && nPis > 8*nRegs && nTerms0 == 1 && nTerms2 == 1 )
        Pdr2_PolicyAdd(p, "treb-ternary", 700, "-g -B 0 -S 0 -H 1 -i -K 2 -U 2");
    else if ( nWidth0 == 1 && nConeRegs >= .8*nRegs && nTerms0 >= .8*nRegs && nRegs > 64 )
    {
        if ( nRegs <= 192 && nWidth2 <= 2 ) Pdr2_PolicyAdd(p, "treb-cube", 700, "-g -B 0 -S 0 -H 1 -i -K 2 -U 1");
        else Pdr2_PolicyAbs(p, 900, nRegs <= 128);
    }
    else if ( nRegs >= 2000 && nPis < nRegs && nTerms2 <= 8 && nConeRegs <= 32 )
    {
        Pdr2_PolicyAbs(p, 200, 0); Pdr2_PolicyAbs(p, 900, 1);
    }
    if ( 1000 <= nRegs && nRegs <= 2000 && nAnds > 100*nRegs && nPis >= 4*nRegs )
        Pdr2_PolicyOption(Pdr2_PolicyAdd(p, "rewrite", 850, NULL), "PDR2_REWRITE", 5);
    if ( 1000 <= nRegs && nRegs <= 2000 && nPis > 4*nRegs && nAnds < 100*nRegs && nTerms2 <= 8 ) Pdr2_PolicyZero(p, 900);
    if ( 64 <= nRegs && nRegs < 256 && nPis > 4*nRegs && nTerms2 >= 64 ) Pdr2_PolicyZero(p, 900);
    if ( 128 <= nRegs && nRegs <= 1024 && 1.5*nRegs <= nPis && nPis <= 4*nRegs )
    {
        if ( nAnds > 100*nRegs && nTerms2 <= 8 ) Pdr2_PolicyZero(p, 900);
        else if ( nAnds < 50*nRegs )
        {
            if ( nTerms2 >= 128 ) Pdr2_PolicyAbs(p, 900, 1);
            else if ( nTerms2 <= 4 ) Pdr2_PolicyOption(Pdr2_PolicyAdd(p, "elimination", 900, NULL), "PDR2_BVE", 3);
            else if ( nWidth0 == 2 && nWidth2 >= 64 ) Pdr2_PolicyAbs(p, 900, 0);
        }
    }
    if ( 128 <= nRegs && nRegs <= 256 && .8*nRegs <= nPis && nPis <= 1.5*nRegs && nConeRegs <= 8 && 3 <= nWidth0 && nTerms2 <= 8 )
    {
        Pdr2_PolicyStride(p, 8, Mix >= 10 && fProject);
    }
    if ( 1024 <= nRegs && nRegs <= 2000 && 1.5*nRegs <= nPis && nPis <= 4*nRegs && nTerms2 <= 8 && nConeRegs <= 32 ) Pdr2_PolicyAbs(p, 900, 0);
    if ( nPis <= 64 && nRegs >= 64 )
    {
        if ( nRegs <= 256 && nTerms0 == 2 && nTerms2 <= 2 && nWidth2 >= 16 ) Pdr2_PolicyAbs(p, 900, 1);
        Pdr2_PolicyAdd(p, "correspondence", 600, "-g -B 0 -q -P 30");
    }
    if ( 5000 <= nRegs && nRegs < 10000 )
    {
        if ( nConeRegs >= nRegs/2 ) Pdr2_PolicyInputs(p, 60, 1);
        else if ( nPis >= 4*nRegs && nConeRegs <= 128 )
        {
            if ( nPis > 8*nRegs )
                Pdr2_PolicyStride(p, 2, Mix >= 10 && fProject);
            if ( nWidth2 > 16 ) Pdr2_PolicyAbs(p, 900, 0);
            else if ( nConeRegs >= 80 ) { Pdr2_PolicyInputs(p, 60, 0); Pdr2_PolicyZero(p, 300); }
            else { Pdr2_PolicyAbs(p, 30, 0); Pdr2_PolicyInputs(p, 20, 0); Pdr2_PolicyZero(p, 40); }
        }
        else if ( nPis < nRegs && nAnds >= 65000 )
        {
            // Grouping two transitions also shortens proofs in designs with
            // compact interfaces. Leave the remaining budget for ordinary PDR.
            Pdr2_PolicyStride(p, 2, Mix >= 10 && fProject);
            goto ordinary;
        }
        else if ( nPis <= 1.5*nRegs && nTerms2 <= 2 && nAnds > 15*nRegs && nConeRegs < nRegs/5 ) Pdr2_PolicyAbs(p, 900, 1);
        else if ( nPis >= 1.5*nRegs || nAnds < 65000 ) Pdr2_PolicyInputs(p, 45, 0);
    }
ordinary:
    Pdr2_PolicyAdd(p, "ordinary", 900, NULL);
adjust:
    if ( !p->nStages ) goto ordinary;
    if ( Mix > 0 && pFeatures )
        for ( i = 0; i < p->nStages; ++i )
        {
            s = &p->Stages[i];
            Pdr2_PolicyOption(s, "PDR2_WATCH_PACK", 1);
            Pdr2_PolicyOption(s, "PDR2_WATCH_AHEAD", 4);
            // Seeding both an initial search and its fallback can repeat the
            // same expensive proof obligations. Start retries without these clauses.
            if ( fProject && !s->pCommand && (Mix < 10 ||
                 (strcmp(s->pName, "stride-retry") && strcmp(s->pName, "dynamic-abstraction"))) )
                Pdr2_PolicyOption( s, "PDR2_PROJECT", 8 );
            if ( Mix >= 5 && !strcmp(s->pName, "input-search") && s->nSeconds < 900 )
            {
                if ( Mix < 8 && (!Gip_OptionGet("PDR2_JOINT_INPUT_GRACE") || !atoi(Gip_OptionGet("PDR2_JOINT_INPUT_GRACE"))) )
                    Pdr2_PolicyOption(s, "PDR2_FRAME_SOFT", s->nSeconds);
                s->nSeconds += Abc_MinInt(24, Abc_MaxInt(6, s->nSeconds / 3));
            }
            if ( Mix >= 12 && !strcmp(s->pName, "elimination") ) Pdr2_PolicyMappedBad(s, Mix >= 13);
            if ( Mix >= 4 && !strcmp(s->pName, "ordinary") ) Pdr2_PolicyOption(s, "PDR2_DROP_HISTORY", 4);
            if ( !strcmp(s->pName, "ordinary") && 1000 <= nRegs && nRegs <= 3000 &&
                 .8*nRegs <= nPis && nPis <= 1.5*nRegs && nConeRegs > nRegs/2 && nTerms2 <= 3 )
                Pdr2_PolicyOption(s, "PDR2_DROP_HISTORY", 3);
            if ( (!strcmp(s->pName, "input-search") &&
                  (Mix < 3 || (nRegs < 16000 && nTerms0 <= 4 && nConeRegs >= nRegs/8))) ||
                 !strcmp(s->pName, "reverse") )
                Pdr2_PolicyOption(s, "PDR2_MIC_GROUP", 4);
            if ( nTerms0 >= 1024 && (!strcmp(s->pName, "treb") || !strcmp(s->pName, "dynamic-abstraction")) )
                Pdr2_PolicyOption(s, "PDR2_MIC_GROUP", 2);
        }
    if ( Gip_OptionGet("PDR2_JOINT_PART_HOLD") )
    {
        int i, Width = Abc_MaxInt(2, Abc_MinInt(16, atoi(Gip_OptionGet("PDR2_JOINT_PART_HOLD"))));
        int Pattern = Gip_OptionGet("PDR2_JOINT_PATTERN") ? atoi(Gip_OptionGet("PDR2_JOINT_PATTERN")) : 1;
        for ( i = 0; i < p->nStages; i++ )
            if ( !strcmp(p->Stages[i].pName, "decompose") )
            {
                Pdr2_PolicyOption(&p->Stages[i], "PDR2_STRIDE", Width);
                Pdr2_PolicyOption(&p->Stages[i], "PDR2_STRIDE_PATTERN", Abc_MaxInt(1, Abc_MinInt(5, Pattern)));
                Pdr2_PolicyOption(&p->Stages[i], "PDR2_STRIDE_PART", 1);
                Pdr2_PolicyOption(&p->Stages[i], "PDR2_STRIDE_TIME", 6);
                Pdr2_PolicyOption(&p->Stages[i], "PDR2_STRIDE_BOUNDED", 1);
            }
    }
    if ( Gip_OptionGet("PDR2_JOINT_PART_WINDOW") )
    {
        int i, Width = atoi(Gip_OptionGet("PDR2_JOINT_PART_WINDOW"));
        for ( i = 0; i < p->nStages; ++i )
            if ( !strcmp(p->Stages[i].pName, "decompose") )
                Pdr2_PolicyOption(&p->Stages[i], "PDR2_PART_WINDOW", Width);
    }
    if ( Gip_OptionGet("PDR2_JOINT_WATCH") )
    {
        int i, Mode = atoi(Gip_OptionGet("PDR2_JOINT_WATCH"));
        for ( i = 0; i < p->nStages; ++i )
        {
            if ( Mode & 1 ) Pdr2_PolicyOption(&p->Stages[i], "PDR2_WATCH_PACK", 1);
            if ( Mode > 1 ) Pdr2_PolicyOption(&p->Stages[i], "PDR2_WATCH_AHEAD", Mode >> 1);
        }
    }
    if ( Gip_OptionGet("PDR2_JOINT_BINARY") )
        for ( i = 0; i < p->nStages; ++i ) Pdr2_PolicyOption(&p->Stages[i], "PDR2_WATCH_BINARY", 1);
    if ( Gip_OptionGet("PDR2_JOINT_WATCH_STATE") )
        for ( i = 0; i < p->nStages; ++i )
            Pdr2_PolicyOption( &p->Stages[i], "PDR2_WATCH_STATE", atoi(Gip_OptionGet("PDR2_JOINT_WATCH_STATE")) );
    if ( Gip_OptionGet("PDR2_JOINT_JOIN") )
    {
        int i, Mode = atoi(Gip_OptionGet("PDR2_JOINT_JOIN"));
        for ( i = 0; i < p->nStages; ++i )
            Pdr2_PolicyOption(&p->Stages[i], "PDR2_JOIN_PUSH", Mode);
    }
    if ( Gip_OptionGet("PDR2_JOINT_HISTORY") )
    {
        int i, Mode = atoi(Gip_OptionGet("PDR2_JOINT_HISTORY"));
        for ( i = 0; i < p->nStages; ++i )
            Pdr2_PolicyOption(&p->Stages[i], "PDR2_DROP_HISTORY", Mode);
    }
    if ( Gip_OptionGet("PDR2_JOINT_DRIVER") )
    {
        int i;
        for ( i = 0; i < p->nStages; ++i )
            Pdr2_PolicyOption(&p->Stages[i], "PDR2_LI_DRIVER", 1);
    }
    if ( Gip_OptionGet("PDR2_JOINT_LATE") )
    {
        int i, Width = atoi(Gip_OptionGet("PDR2_JOINT_LATE"));
        for ( i = 0; i < p->nStages; ++i )
            Pdr2_PolicyOption(&p->Stages[i], "PDR2_STRENGTHEN_LATE", Width);
    }
    if ( Gip_OptionGet("PDR2_JOINT_GUARD") )
    {
        int i, Mode = atoi(Gip_OptionGet("PDR2_JOINT_GUARD"));
        for ( i = 0; i < p->nStages; ++i )
            Pdr2_PolicyOption(&p->Stages[i], "PDR2_TRACE_GUARD", Mode);
    }
    if ( Gip_OptionGet("PDR2_JOINT_MIC_CONFS") )
    {
        int i, Limit = atoi(Gip_OptionGet("PDR2_JOINT_MIC_CONFS"));
        for ( i = 0; i < p->nStages; ++i )
            Pdr2_PolicyOption( &p->Stages[i], "PDR2_MIC_CONFS", Limit );
    }
    if ( Gip_OptionGet("PDR2_JOINT_GROUP") )
    {
        int i, Mode = atoi(Gip_OptionGet("PDR2_JOINT_GROUP"));
        for ( i = 0; i < p->nStages; ++i )
            Pdr2_PolicyOption(&p->Stages[i], "PDR2_MIC_GROUP", Mode);
    }
    if ( Gip_OptionGet("PDR2_JOINT_RESOLVE") )
    {
        int Count = atoi(Gip_OptionGet("PDR2_JOINT_RESOLVE"));
        for ( i = 0; i < p->nStages; ++i )
            Pdr2_PolicyOption(&p->Stages[i], "PDR2_RESOLVE", Count);
    }
    if ( Gip_OptionGet("PDR2_JOINT_DOWN") )
    {
        int Mode = atoi(Gip_OptionGet("PDR2_JOINT_DOWN"));
        for ( i = 0; i < p->nStages; i++ )
            if ( !strcmp(p->Stages[i].pName, "abstraction") || !strcmp(p->Stages[i].pName, "dynamic-abstraction") )
                Pdr2_PolicyOption(&p->Stages[i], "PDR2_DOWN_TRIES", Mode);
    }
    if ( Gip_OptionGet("PDR2_JOINT_PROJECT") )
        for ( i = 0; i < p->nStages; i++ )
            Pdr2_PolicyOption(&p->Stages[i], "PDR2_PROJECT", Abc_MaxInt(1, Abc_MinInt(8, atoi(Gip_OptionGet("PDR2_JOINT_PROJECT")))));
    if ( Gip_OptionGet("PDR2_JOINT_RESET_COI") )
        for ( i = 0; i < p->nStages; i++ )
            Pdr2_PolicyOption(&p->Stages[i], atoi(Gip_OptionGet("PDR2_JOINT_RESET_COI")) ? "PDR2_RESET_COI" : "PDR2_COI", 1);
}

/**Function*************************************************************

  Synopsis    [Cofactors latches that record the preceding bad output.]

  Description [On a shortest counterexample every earlier bad output was
  zero. A register whose input is the bad output or its complement thus has
  a known value before and including the failing step, provided its initial
  value agrees. Keep the original interface for concrete witness replay.]

***********************************************************************/
static Aig_Man_t * Pdr2_PolicyFirstFail( Aig_Man_t * pAig, Vec_Int_t * vInit, int * pCount )
{
    int i, Value, nRegs = Aig_ManRegNum(pAig);
    Aig_Obj_t * pObj, * pCi, * pBad, * pNext;
    Aig_Man_t * pNew = NULL;
    char * pKnown;
    *pCount = 0;
    if ( !nRegs || Saig_ManPoNum(pAig) != 1 || Saig_ManConstrNum(pAig) ||
         Aig_ManBufNum(pAig) || Aig_ManExorNum(pAig) || (vInit && Vec_IntSize(vInit) != nRegs) ) return NULL;
    pKnown = ABC_ALLOC(char, nRegs);
    memset(pKnown, 2, nRegs);
    pBad = Aig_ObjChild0(Aig_ManCo(pAig, 0));
    Saig_ManForEachLi( pAig, pObj, i )
    {
        pNext = Aig_ObjChild0(pObj);
        if ( Aig_Regular(pBad) != Aig_Regular(pNext) ) continue;
        Value = Aig_IsComplement(pBad) ^ Aig_IsComplement(pNext);
        if ( Value != (vInit ? Vec_IntEntry(vInit, i) : 0) ) continue;
        pKnown[i] = Value;
        ++*pCount;
    }
    if ( !*pCount ) goto done;
    pNew = Aig_ManStart(Aig_ManNodeNum(pAig));
    pNew->pName = Abc_UtilStrsav(pAig->pName);
    Aig_ManConst1(pAig)->pData = Aig_ManConst1(pNew);
    Saig_ManForEachPi( pAig, pObj, i ) pObj->pData = Aig_ObjCreateCi(pNew);
    Saig_ManForEachLo( pAig, pObj, i )
    {
        pCi = Aig_ObjCreateCi(pNew);
        pObj->pData = pKnown[i] == 2 ? pCi : Aig_NotCond(Aig_ManConst1(pNew), !pKnown[i]);
    }
    Aig_ManForEachNode( pAig, pObj, i )
        pObj->pData = Aig_And(pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj));
    Aig_ObjCreateCo(pNew, Aig_ObjChild0Copy(Aig_ManCo(pAig, 0)));
    Saig_ManForEachLi( pAig, pObj, i )
        Aig_ObjCreateCo(pNew, pKnown[i] == 2 ? Aig_ObjChild0Copy(pObj) : Aig_NotCond(Aig_ManConst1(pNew), !pKnown[i]));
    Aig_ManSetRegNum(pNew, nRegs);
    Aig_ManSetCioIds(pNew);
    Aig_ManCleanup(pNew);
done:
    ABC_FREE(pKnown);
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Writes the measured features and selected stages as JSON.]

  Description []

***********************************************************************/
void Pdr2_ManPrintPolicy( Aig_Man_t * pAig, Vec_Int_t * vInit )
{
    Pdr2_Policy_t * p = ABC_CALLOC(Pdr2_Policy_t, 1);
    int Count, Mode = Gip_OptionGet("PDR2_JOINT_MONITOR") ? atoi(Gip_OptionGet("PDR2_JOINT_MONITOR")) : 0;
    Aig_Man_t * pFirst = Mode == 1 ? Pdr2_PolicyFirstFail(pAig, vInit, &Count) : NULL;
    int F[12], fValid = Pdr2_PolicyFeatures(pFirst ? pFirst : pAig, F), i, k;
    Pdr2_PolicyBuild(p, fValid ? F : NULL);
    if ( fValid ) Pdr2_PolicyMuxFirst(p, pFirst ? pFirst : pAig, NULL, 0);
    Abc_Print(1, "PDR2_PLAN {\"features\":");
    Pdr2_PolicyPrintFeatures(fValid ? F : NULL);
    Abc_Print(1, ",\"stages\":[");
    for ( i = 0; i < p->nStages; i++ )
    {
        Pdr2_PolicyStage_t * s = &p->Stages[i];
        Abc_Print(1, "%s{\"name\":\"%s\",\"seconds\":%d,\"flags\":\"%s\",\"env\":{",
                  i ? "," : "", s->pName, s->nSeconds, s->pFlags);
        for ( k = 0; k < s->nOptions; k++ )
            Abc_Print(1, "%s\"%s\":\"%s\"", k ? "," : "", s->pKeys[k], s->Values[k]);
        Abc_Print(1, "}");
        if ( s->pCommand ) Abc_Print(1, ",\"command\":\"%s\"", s->pCommand);
        Abc_Print(1, "}");
    }
    Abc_Print(1, "]}\n");
    if ( pFirst ) Aig_ManStop(pFirst);
    ABC_FREE(p);
}

/**Function*************************************************************

  Synopsis    [Applies a stage's built-in option string to its private parameters.]

  Description []

***********************************************************************/
// These are the fixed internal plan flags, not an additional user command
// parser. Keep the mapping identical to Abc_CommandPdr2().
static int Pdr2_PolicySetFlags( Pdr2_Par_t * p, const char * s )
{
    char Option, * pEnd;
    int Value;
    while ( *s )
    {
        while ( *s == ' ' ) s++;
        if ( !*s ) break;
        if ( s[0] != '-' || !s[1] ) return 0;
        Option = s[1]; s += 2;
        switch ( Option )
        {
        case 'g': p->fDynamic ^= 1; continue;
        case 't': p->fUseAbs ^= 1; continue;
        case 'i': p->fBlockInduct ^= 1; continue;
        case 'q': p->fPreproc ^= 1; continue;
        }
        Value = (int)strtol(s, &pEnd, 10);
        if ( pEnd == s || Value < 0 ) return 0;
        s = pEnd;
        switch ( Option )
        {
        case 'B': p->nAbsRuns = Value; break;
        case 'D': p->nDynTime = Value; break;
        case 'S': p->nRandomSeed = Value; break;
        case 'H': p->nMicMode = Value; break;
        case 'K': p->nQueueOrder = Value; break;
        case 'U': p->nLiftSim = Value; break;
        case 'P': p->nPreprocTime = Value; break;
        default: return 0;
        }
    }
    // Abc_CommandPdr2 performs this after parsing all flags: explicit
    // abstraction enables relative induction, and -i toggles it back off.
    if ( p->fUseAbs ) p->fBlockInduct ^= 1;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Prints effective PDR parameters for comparison with the command parser.]

  Description []

***********************************************************************/
void Pdr2_ManPrintPolicyParams( Pdr2_Par_t * p )
{
    int First = 1;
    Abc_Print(1, "PDR2_PARAMS {");
#define PDR2_PRINT_PARAM(Field) do { Abc_Print(1, "%s\"" #Field "\":%d", First ? "" : ",", p->Field); First = 0; } while (0)
    PDR2_PRINT_PARAM(nRandomSeed); PDR2_PRINT_PARAM(fCtg); PDR2_PRINT_PARAM(fDynamic);
    PDR2_PRINT_PARAM(nDynLimitMax); PDR2_PRINT_PARAM(nDynAct); PDR2_PRINT_PARAM(nDynTime);
    PDR2_PRINT_PARAM(nCtgTime); PDR2_PRINT_PARAM(fDynFirst); PDR2_PRINT_PARAM(fShareInf);
    PDR2_PRINT_PARAM(nDynExplode); PDR2_PRINT_PARAM(nLevelRestart); PDR2_PRINT_PARAM(fTimeGen);
    PDR2_PRINT_PARAM(fSemContain); PDR2_PRINT_PARAM(fKeepObl); PDR2_PRINT_PARAM(nQueueOrder);
    PDR2_PRINT_PARAM(nCtgMax); PDR2_PRINT_PARAM(nCtgLimit); PDR2_PRINT_PARAM(fCtgMic);
    PDR2_PRINT_PARAM(fCtgLocal); PDR2_PRINT_PARAM(fDropPo); PDR2_PRINT_PARAM(nDropAct);
    PDR2_PRINT_PARAM(nDynDropAct); PDR2_PRINT_PARAM(fParentLemma); PDR2_PRINT_PARAM(fLift);
    PDR2_PRINT_PARAM(fPropHyp); PDR2_PRINT_PARAM(fBlockInduct); PDR2_PRINT_PARAM(nPrefix);
    PDR2_PRINT_PARAM(fCtiCache); PDR2_PRINT_PARAM(nCtpMax); PDR2_PRINT_PARAM(fUseAbs);
    PDR2_PRINT_PARAM(nAbsStart); PDR2_PRINT_PARAM(fAbsCleanup); PDR2_PRINT_PARAM(fAbsRefineAll);
    PDR2_PRINT_PARAM(fAbsReset); PDR2_PRINT_PARAM(fAbsRefineXsim); PDR2_PRINT_PARAM(nAbsRefineMode);
    PDR2_PRINT_PARAM(nAbsRuns); PDR2_PRINT_PARAM(fDynRun); PDR2_PRINT_PARAM(fSimRun);
    PDR2_PRINT_PARAM(nBmcTime); PDR2_PRINT_PARAM(nAbsTime); PDR2_PRINT_PARAM(fTopCtg);
    PDR2_PRINT_PARAM(fInfPromote); PDR2_PRINT_PARAM(nMicMode); PDR2_PRINT_PARAM(nMicFailLimit);
    PDR2_PRINT_PARAM(nDownCacheMode); PDR2_PRINT_PARAM(nCtgSmall); PDR2_PRINT_PARAM(nCtgMinRate);
    PDR2_PRINT_PARAM(nLiftIters); PDR2_PRINT_PARAM(fSparseLift); PDR2_PRINT_PARAM(fWarmStart);
    PDR2_PRINT_PARAM(nLiftSim); PDR2_PRINT_PARAM(nLiftSimOrder); PDR2_PRINT_PARAM(fPreproc);
    PDR2_PRINT_PARAM(nPreprocTime); PDR2_PRINT_PARAM(fVerify); PDR2_PRINT_PARAM(fVerifyComplete);
    PDR2_PRINT_PARAM(fDumpInv); PDR2_PRINT_PARAM(fVerbose); PDR2_PRINT_PARAM(fVeryVerbose);
    PDR2_PRINT_PARAM(fSilent);
#undef PDR2_PRINT_PARAM
    Abc_Print(1, "}\n");
}

/**Function*************************************************************

  Synopsis    [Adapts the caller's stop callback to rarity simulation.]

  Description []

***********************************************************************/
static int Pdr2_PolicySimStop( void * pData, int Kind, unsigned Frame )
{
    Pdr2_Par_t * pPars = (Pdr2_Par_t *)pData;
    (void)Kind;
    (void)Frame;
    return pPars->pFuncStop( pPars->RunId );
}

/**Function*************************************************************

  Synopsis    [Forwards cancellation from the bounded input search.]

  Description []

***********************************************************************/
static int Pdr2_PolicyBoundedStop( void * pData )
{
    Pdr2_Par_t * pPars = (Pdr2_Par_t *)pData;
    return pPars->pFuncStop(pPars->RunId);
}

/**Function*************************************************************

  Synopsis    [Searches for a concrete counterexample with manager-local rarity simulation.]

  Description []

***********************************************************************/
static int Pdr2_PolicySimulate( Aig_Man_t * pAig, Vec_Int_t * vInit, Pdr2_Par_t * pPars )
{
    Ssw_RarPars_t Pars;
    Gia_Man_t * pGia;
    int i;
    // Rarity simulation starts at the all-zero state.
    if ( !Aig_ManRegNum(pAig) || Saig_ManConstrNum(pAig) || Saig_ManPoNum(pAig) != 1 ) return -1;
    if ( vInit )
    {
        if ( Vec_IntSize(vInit) != Aig_ManRegNum(pAig) ) return -1;
        for ( i = 0; i < Vec_IntSize(vInit); i++ )
            if ( Vec_IntEntry(vInit, i) != 0 ) return -1;
    }
    Ssw_RarSetDefaultParams(&Pars);
    Pars.TimeOut = pPars->nTimeOut;
    Pars.fVerbose = pPars->fVerbose;
    Pars.fSilent = pPars->fSilent;
    Pars.pFuncProgress = pPars->pFuncStop ? Pdr2_PolicySimStop : NULL;
    Pars.pProgress = pPars;
    pGia = Gia_ManFromAigSimple( pAig );
    Abc_CexFreeP( &pAig->pSeqModel );
    pAig->pSeqModel = Ssw_RarFindCexGia( pGia, &Pars );
    Gia_ManStop( pGia );
    if ( pAig->pSeqModel == NULL )
        return -1;
    pPars->iFrame = pAig->pSeqModel->iFrame;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Runs incremental bounded search over groups of consecutive frames.]

  Description [Only returns a witness that replays on the supplied graph.]

  SideEffects []

***********************************************************************/
int Pdr2_ManWindowBmc( Aig_Man_t * pAig, Vec_Int_t * vInit, Pdr2_Par_t * pPars, int Seconds, int nGroup )
{
    Bmc_GiaPar_t Pars;
    Gia_Man_t * pGia;
    int i, Result = -1;
    if ( vInit )
        for ( i = 0; i < Vec_IntSize(vInit); ++i ) if ( Vec_IntEntry(vInit, i) ) return -1;
    Bmc_GiaSetDefaultParams(&Pars);
    Pars.nTimeOut = Seconds;
    Pars.nMemoryLimit = 1536;
    Pars.fSilent = 1;
    Pars.fVerbose = pPars->fVerbose && !pPars->fSilent;
    Pars.pFuncStop = pPars->pFuncStop ? Pdr2_PolicyBoundedStop : NULL;
    Pars.pStopData = pPars;
    pGia = Gia_ManFromAigSimple(pAig);
    if ( Bmc_GiaPerformWindow(pGia, &Pars, nGroup) == 0 && pGia->pCexSeq &&
         Saig_ManVerifyCex(pAig, pGia->pCexSeq) )
    {
        Abc_CexFreeP(&pAig->pSeqModel);
        pAig->pSeqModel = pGia->pCexSeq;
        pGia->pCexSeq = NULL;
        pPars->iFrame = pAig->pSeqModel->iFrame;
        Result = 0;
    }
    Gia_ManStop(pGia);
    return Result;
}

/**Function*************************************************************

  Synopsis    [Searches for a witness with correlated primary inputs.]

  Description [Groups nearby low-fanout inputs while preserving independent
  controls. Every input trace of the reduced machine expands to a trace of
  the original. A proof of the reduced machine does not establish safety.]

  SideEffects [Returns a counterexample in the original input coordinates.]

***********************************************************************/
static int Pdr2_PolicyInputWitness( Aig_Man_t * pAig, Vec_Int_t * vInit, Pdr2_Par_t * pPars )
{
    int Width = atoi(Gip_OptionGet("PDR2_INPUT_WIDTH"));
    int Lanes = Gip_OptionGet("PDR2_INPUT_LANES") ? atoi(Gip_OptionGet("PDR2_INPUT_LANES")) : 0;
    int nPis = Saig_ManPiNum(pAig), nRegs = Aig_ManRegNum(pAig), nNew = 0, Shared = -1;
    int i, f, Ret = -1, * pMap = ABC_ALLOC(int, nPis);
    Vec_Int_t * vLanes = Lanes ? Vec_IntStartFull(Width) : NULL;
    Aig_Obj_t * pObj;
    Aig_Man_t * pNew = NULL;
    Abc_Cex_t * pSmall = NULL, * pBig;
    abctime Stop = Abc_Clock() + (abctime)pPars->nTimeOut * CLOCKS_PER_SEC;
    Saig_ManForEachPi(pAig, pObj, i)
    {
        if ( i % Width == 0 ) Shared = -1;
        if ( Aig_ObjRefs(pObj) > 3 ) pMap[i] = Abc_Var2Lit(nNew++, 0);
        else if ( vLanes )
        {
            int Lane = i % Width, Var = Vec_IntEntry(vLanes, Lane);
            if ( Var < 0 ) Vec_IntWriteEntry(vLanes, Lane, (Var = nNew++));
            pMap[i] = Abc_Var2Lit(Var, Lanes == 2 && (((unsigned)i * 2654435761u) >> 31));
        }
        else
        {
            if ( Shared < 0 ) Shared = nNew++;
            pMap[i] = Abc_Var2Lit(Shared, 0);
        }
    }
    if ( nNew == nPis || Aig_ManBufNum(pAig) || Aig_ManExorNum(pAig) ) goto done;
    pNew = Aig_ManStart(Aig_ManNodeNum(pAig));
    pNew->pName = Abc_UtilStrsav(pAig->pName);
    Aig_ManConst1(pAig)->pData = Aig_ManConst1(pNew);
    for ( i = 0; i < nNew; ++i ) Aig_ObjCreateCi(pNew);
    Saig_ManForEachPi(pAig, pObj, i)
        pObj->pData = Aig_NotCond(Aig_ManCi(pNew, Abc_Lit2Var(pMap[i])), Abc_LitIsCompl(pMap[i]));
    Saig_ManForEachLo(pAig, pObj, i) pObj->pData = Aig_ObjCreateCi(pNew);
    Aig_ManForEachNode(pAig, pObj, i)
        pObj->pData = Aig_And(pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj));
    Aig_ManForEachCo(pAig, pObj, i) Aig_ObjCreateCo(pNew, Aig_ObjChild0Copy(pObj));
    Aig_ManSetRegNum(pNew, nRegs);
    Aig_ManCleanup(pNew);
    if ( pPars->fVerbose )
        Abc_Print(1, "Correlated input search: %d inputs reduced to %d, %d nodes.\n", nPis, nNew, Aig_ManNodeNum(pNew));
    if ( Aig_ObjChild0(Aig_ManCo(pNew, 0)) == Aig_ManConst0(pNew) ||
         (pPars->pFuncStop && pPars->pFuncStop(pPars->RunId)) ) goto done;
    if ( atoi(Gip_OptionGet("PDR2_INPUT_BOUNDED")) )
    {
        Bmc_GiaPar_t Pars;
        Gia_Man_t * pGia;
        if ( vInit )
            for ( i = 0; i < nRegs; ++i ) if ( Vec_IntEntry(vInit, i) ) goto done;
        pGia = Gia_ManFromAigSimple(pNew);
        Bmc_GiaSetDefaultParams(&Pars);
        Pars.TimeToStop = pPars->nTimeOut ? Stop : 0;
        Pars.nMemoryLimit = 1536;
        Pars.fSilent = 1;
        Pars.pFuncStop = pPars->pFuncStop ? Pdr2_PolicyBoundedStop : NULL;
        Pars.pStopData = pPars;
        if ( Bmc_GiaPerform(pGia, &Pars) == 0 )
        {
            pSmall = pGia->pCexSeq;
            pGia->pCexSeq = NULL;
        }
        Gia_ManStop(pGia);
    }
    else
    {
        Pdr2_Par_t Child = *pPars;
        if ( Child.nTimeOut )
        {
            if ( Stop - Abc_Clock() < CLOCKS_PER_SEC ) goto done;
            Child.nTimeOut = (int)((Stop - Abc_Clock()) / CLOCKS_PER_SEC);
        }
        if ( Pdr2_ManSolveInit(pNew, vInit, &Child) == 0 )
        {
            pSmall = pNew->pSeqModel;
            pNew->pSeqModel = NULL;
        }
    }
    if ( !pSmall || pSmall->iFrame < 0 || pSmall->nRegs != nRegs || pSmall->nPis != nNew ||
         ((ABC_INT64_T)pSmall->iFrame + 1) * nPis + nRegs >= INT_MAX ) goto done;
    pBig = Abc_CexAlloc(nRegs, nPis, pSmall->iFrame + 1);
    pBig->iPo = 0;
    pBig->iFrame = pSmall->iFrame;
    for ( i = 0; i < nRegs; ++i )
        if ( Abc_InfoHasBit(pSmall->pData, i) ) Abc_InfoSetBit(pBig->pData, i);
    for ( f = 0; f <= pSmall->iFrame; ++f )
        for ( i = 0; i < nPis; ++i )
            if ( Abc_InfoHasBit(pSmall->pData, nRegs + nNew*f + Abc_Lit2Var(pMap[i])) ^ Abc_LitIsCompl(pMap[i]) )
                Abc_InfoSetBit(pBig->pData, nRegs + nPis*f + i);
    // The caller checks the expanded trace, including the original reset.
    Abc_CexFreeP(&pAig->pSeqModel);
    pAig->pSeqModel = pBig;
    pPars->iFrame = pBig->iFrame;
    Ret = 0;
done:
    Abc_CexFreeP(&pSmall);
    Vec_IntFreeP(&vLanes);
    if ( pNew ) Aig_ManStop(pNew);
    ABC_FREE(pMap);
    return Ret;
}

/**Function*************************************************************

  Synopsis    [Checks the witness interface and initial state, then replays the original AIG.]

  Description []

***********************************************************************/
static int Pdr2_PolicyCheckCex( Aig_Man_t * pAig, Vec_Int_t * vInit, Abc_Cex_t * pCex, int fFirst )
{
    int i, Init;
    if ( !pCex || pCex->iPo != 0 || pCex->iFrame < 0 ||
         pCex->nRegs != Aig_ManRegNum(pAig) || pCex->nPis != Saig_ManPiNum(pAig) ||
         pCex->nBits != pCex->nRegs + ((ABC_INT64_T)pCex->iFrame + 1) * pCex->nPis )
        return 0;
    for ( i = 0; i < pCex->nRegs; i++ )
    {
        Init = vInit ? Vec_IntEntry(vInit, i) : 0;
        if ( Init != 2 && Init != Abc_InfoHasBit(pCex->pData, i) )
            return 0;
    }
    // A bounded query may choose a later bad frame. Trim the original trace before replay.
    if ( fFirst && !Pdr2_ManFirstBad(pAig, pCex) ) return 0;
    return Saig_ManVerifyCex(pAig, pCex);
}

/**Function*************************************************************

  Synopsis    [Runs the selected stages within a shared deadline and transfers checked results.]

  Description []

***********************************************************************/
int Pdr2_ManSolvePolicy( Aig_Man_t * pAig, Vec_Int_t * vInit, Pdr2_Par_t * pPars )
{
    if ( pPars->fVerify && pPars->fVerifyComplete )
        return Pdr2_ManSolveInit(pAig, vInit, pPars);
    Pdr2_Policy_t * p = ABC_CALLOC(Pdr2_Policy_t, 1);
    Pdr2_Par_t Child;
    Gip_Options_t Options;
    const char * Keys[36], * Values[36];
    abctime Start = Abc_Clock(), Deadline = pPars->nTimeOut ? Start + (abctime)pPars->nTimeOut * CLOCKS_PER_SEC : 0;
    int Count, Mode = Gip_OptionGet("PDR2_JOINT_MONITOR") ? atoi(Gip_OptionGet("PDR2_JOINT_MONITOR")) : 0;
    Aig_Man_t * pFirst = Mode ? Pdr2_PolicyFirstFail(pAig, vInit, &Count) : NULL;
    Aig_Man_t * pModel = pFirst ? pFirst : pAig;
    int F[12], fValid = Pdr2_PolicyFeatures(Mode == 2 ? pAig : pModel, F), i, k, nOptions, Budget, Result = -1;
    int fPrintParams = Gip_OptionGet("PDR2_POLICY_PARAMS") != NULL;
    Pdr2_PolicyBuild(p, fValid ? F : NULL);
    if ( fValid ) Pdr2_PolicyMuxFirst(p, Mode == 2 ? pAig : pModel, pPars, Deadline);
    if ( pFirst && fValid && pPars->fVerbose )
        Abc_Print(1, "First-failure cofactor: %d monitor flops, bad cone %d flops and %d nodes.\n", Count, F[3], F[5]);
    pPars->nPhasesRun = pPars->nRestartsRun = pPars->fBmcDecided = 0;
    if ( pPars->fVerbose )
        Abc_Print(1, "Native structural policy: one active engine, shared deadline, %d stages.\n", p->nStages);
    for ( i = 0; i < p->nStages; i++ )
    {
        Pdr2_PolicyStage_t * s = &p->Stages[i];
        Aig_Man_t * pWork;
        abctime StageStart = Abc_Clock(), StageStop;
        int fLast = i == p->nStages - 1;
        if ( pPars->pFuncStop && pPars->pFuncStop(pPars->RunId) ) break;
        Budget = s->nSeconds;
        if ( Deadline )
        {
            abctime Left = Deadline - StageStart;
            if ( Left <= 0 || (i > 0 && Left < CLOCKS_PER_SEC) ) break;
            Budget = Abc_MaxInt(1, (int)((Left - CLOCKS_PER_SEC / 5) / CLOCKS_PER_SEC));
            if ( !fLast ) Budget = Abc_MinInt(Budget, s->nSeconds);
        }
        else if ( fLast ) Budget = 0;
        StageStop = Budget ? StageStart + (abctime)Budget * CLOCKS_PER_SEC : 0;
        // Stage values precede defaults, so an explicit scheduled BMC budget
        // overrides the common zero budget without touching the environment.
        nOptions = 0;
        for ( k = 0; k < s->nOptions; k++ )
        {
            Keys[nOptions] = s->pKeys[k]; Values[nOptions++] = s->Values[k];
        }
        Keys[nOptions] = "PDR2_BMC"; Values[nOptions++] = "0";
        Keys[nOptions] = "PDR2_ABS_EPOCH"; Values[nOptions++] = "0";
        Keys[nOptions] = "PDR2_ABS_SCRATCH"; Values[nOptions++] = "1";
        memset(&Options, 0, sizeof(Options));
        Options.nOptions = nOptions; Options.pKeys = Keys; Options.pValues = Values; Options.fIsolate = 1;
        Gip_OptionsPush(&Options);
        Pdr2_ManSetDefaultParams(&Child);
        Child.nRandomSeed = pPars->nRandomSeed;
        Child.nTimeOut = Budget;
        Child.timePolicyStop = Deadline;
        Child.fVerbose = pPars->fVerbose; Child.fVeryVerbose = pPars->fVeryVerbose; Child.fSilent = pPars->fSilent;
        Child.fVerify = pPars->fVerify; Child.fVerifyComplete = pPars->fVerifyComplete;
        Child.fDumpInv = pPars->fDumpInv; Child.pInvFileName = pPars->pInvFileName;
        Child.RunId = pPars->RunId; Child.pFuncStop = pPars->pFuncStop;
        Child.nPropUnit = pPars->nPropUnit;
        if ( !Pdr2_PolicySetFlags(&Child, s->pFlags) )
        {
            Gip_OptionsPop(&Options);
            Abc_Print(1, "Internal error: invalid structural policy flags.\n");
            break;
        }
        if ( fPrintParams )
        {
            Abc_Print(1, "POLICY_PARAMS_STAGE %s\n", s->pName);
            Pdr2_ManPrintPolicyParams(&Child);
            Gip_OptionsPop(&Options);
            continue;
        }
        if ( pPars->fVerbose ) Abc_Print(1, "POLICY_STAGE %s budget=%d\n", s->pName, Budget);
        // Each stage gets fresh object metadata while retaining the original
        // PI, latch, and output interface for counterexample transfer.
        pWork = Aig_ManDupSimple(pModel);
        assert(Aig_ManCiNum(pWork) == Aig_ManCiNum(pAig) && Aig_ManCoNum(pWork) == Aig_ManCoNum(pAig));
        assert(Aig_ManRegNum(pWork) == Aig_ManRegNum(pAig));
        if ( s->pCommand && !strcmp(s->pCommand, "input-latches") )
            Result = Pdr2_ManSolveInputLatches(pWork, vInit, &Child);
        else if ( s->pCommand && !strcmp(s->pCommand, "mutex") )
            Result = Pdr2_ManSolveMutex(pWork, vInit, &Child, atoi(Gip_OptionGet("PDR2_MUTEX_MIN")));
        else if ( s->pCommand && !strcmp(s->pCommand, "comb-safe") )
            Result = Pdr2_ManCombSafe(pWork, &Child, StageStop, pWork, vInit);
        else if ( s->pCommand && !strcmp(s->pCommand, "comb-projection") )
            Result = Pdr2_ManProjectedComb(pWork, vInit, &Child, StageStop, atoi(Gip_OptionGet("PDR2_PROJECT")));
        else if ( s->pCommand && !strcmp(s->pCommand, "gates") )
            Result = Pdr2_ManSolveGla(pWork, vInit, &Child, atoi(Gip_OptionGet("PDR2_GATE_LAYERS")));
        else if ( s->pCommand && !strcmp(s->pCommand, "sample") )
            Result = Pdr2_ManSampleProperty(pWork, vInit, &Child, atoi(Gip_OptionGet("PDR2_SAMPLE")));
        else if ( s->pCommand && !strcmp(s->pCommand, "tail") )
            Result = Pdr2_ManSolveTail(pWork, vInit, &Child, atoi(Gip_OptionGet("PDR2_TAIL_DEPTH")));
        else if ( s->pCommand && !strcmp(s->pCommand, "window") )
            Result = Pdr2_ManWindowBmc(pWork, vInit, &Child, Budget, atoi(Gip_OptionGet("PDR2_WINDOW")));
        else if ( s->pCommand && !strcmp(s->pCommand, "input-probe") ) Result = Pdr2_PolicyInputWitness(pWork, vInit, &Child);
        else Result = s->pCommand ? Pdr2_PolicySimulate(pWork, vInit, &Child) : Pdr2_ManSolveInit(pWork, vInit, &Child);
        pPars->iFrame = Child.iFrame;
        pPars->nPhasesRun += Child.nPhasesRun; pPars->nRestartsRun += Child.nRestartsRun;
        pPars->fBmcDecided = Child.fBmcDecided;
        if ( Result == 0 )
        {
            if ( Pdr2_PolicyCheckCex(pAig, vInit, pWork->pSeqModel, Mode != 0) )
            {
                Abc_CexFreeP( &pAig->pSeqModel );
                pAig->pSeqModel = pWork->pSeqModel;
                pPars->iFrame = pAig->pSeqModel->iFrame;
                pWork->pSeqModel = NULL;
            }
            else
            {
                Abc_Print( 1, "Internal error: structural policy counterexample failed verification.\n" );
                Result = -1;
            }
        }
        Aig_ManStop(pWork);
        Gip_OptionsPop(&Options);
        if ( pPars->fVerbose )
            Abc_Print(1, "POLICY_STAGE_DONE %s seconds=%.3f result=%d\n", s->pName,
                      (double)(Abc_Clock() - StageStart) / CLOCKS_PER_SEC, Result);
        if ( Result != -1 ) break;
    }
    if ( pPars->fVerbose )
        Abc_Print(1, "Native structural policy total wall seconds = %.3f\n", (double)(Abc_Clock() - Start) / CLOCKS_PER_SEC);
    if ( Result == -1 && Deadline && Deadline - Abc_Clock() < 11 * CLOCKS_PER_SEC / 10 && !pPars->fSilent )
        Abc_Print(1, "Reached structural policy time limit (%d seconds).\n", pPars->nTimeOut);
    if ( pFirst ) Aig_ManStop(pFirst);
    ABC_FREE(p);
    return Result;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
