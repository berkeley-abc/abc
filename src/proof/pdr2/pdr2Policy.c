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
    const char * pKeys[16];
    char Values[16][32];
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
    assert(i < 16);
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

  Synopsis    [Selects sequential verification stages from structural measurements.]

  Description []

***********************************************************************/
// Version 9 of the corpus-tuned research policy. This function only selects
// stages from structural measurements; it has no instance names or answers.
static void Pdr2_PolicyBuild( Pdr2_Policy_t * p, int * pFeatures )
{
    double nPis, nRegs, nAnds, nConeRegs, nTerms0, nTerms2, nWidth0, nWidth2;
    Pdr2_PolicyStage_t * s;
    if ( pFeatures == NULL ) goto ordinary;
    nPis = pFeatures[0];
    nRegs = pFeatures[1];
    nAnds = pFeatures[2];
    nConeRegs = pFeatures[3];
    nTerms0 = pFeatures[6];
    nWidth0 = pFeatures[7];
    nTerms2 = pFeatures[9];
    nWidth2 = pFeatures[10];
    if ( 0 < nRegs && nRegs <= 64 && nAnds < 30000 )
    {
        s = Pdr2_PolicyAdd(p, "bdd-square", 2, NULL);
        Pdr2_PolicyOption(s, "PDR2_BDDSQUARE", 2); Pdr2_PolicyOption(s, "PDR2_BDD_ONLY", 1);
        if ( nConeRegs >= .8*nRegs && nTerms0 >= 64 ) Pdr2_PolicySplit(p, 80, 0, 2, 1024, 1);
    }
    if ( nRegs >= 20000 )
    {
        Pdr2_PolicyBmc(p, 15);
        if ( nWidth2 <= 2 || nConeRegs > 8 ) Pdr2_PolicyInputs(p, 45, 0);
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
        s = Pdr2_PolicyAdd(p, "temporal-stride", 180, NULL);
        Pdr2_PolicyOption(s, "PDR2_STRIDE", 8); Pdr2_PolicyOption(s, "PDR2_STRIDE_TIME", 180);
        Pdr2_PolicyOption(s, "PDR2_STRIDE_ONLY", 1);
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
            {
                s = Pdr2_PolicyAdd(p, "temporal-stride", 180, NULL);
                Pdr2_PolicyOption(s, "PDR2_STRIDE", 2);
                Pdr2_PolicyOption(s, "PDR2_STRIDE_TIME", 180);
                Pdr2_PolicyOption(s, "PDR2_STRIDE_ONLY", 1);
            }
            if ( nWidth2 > 16 ) Pdr2_PolicyAbs(p, 900, 0);
            else if ( nConeRegs >= 80 ) { Pdr2_PolicyInputs(p, 60, 0); Pdr2_PolicyZero(p, 300); }
            else { Pdr2_PolicyAbs(p, 30, 0); Pdr2_PolicyInputs(p, 20, 0); Pdr2_PolicyZero(p, 40); }
        }
        else if ( nPis < nRegs && nAnds >= 65000 )
        {
            // Grouping two transitions also shortens proofs in designs with
            // compact interfaces. Leave the remaining budget for ordinary PDR.
            s = Pdr2_PolicyAdd(p, "temporal-stride", 180, NULL);
            Pdr2_PolicyOption(s, "PDR2_STRIDE", 2);
            Pdr2_PolicyOption(s, "PDR2_STRIDE_TIME", 180);
            Pdr2_PolicyOption(s, "PDR2_STRIDE_ONLY", 1);
            goto ordinary;
        }
        else if ( nPis <= 1.5*nRegs && nTerms2 <= 2 && nAnds > 15*nRegs && nConeRegs < nRegs/5 ) Pdr2_PolicyAbs(p, 900, 1);
        else if ( nPis >= 1.5*nRegs || nAnds < 65000 ) Pdr2_PolicyInputs(p, 45, 0);
    }
ordinary:
    Pdr2_PolicyAdd(p, "ordinary", 900, NULL);
}

/**Function*************************************************************

  Synopsis    [Writes the measured features and selected stages as JSON.]

  Description []

***********************************************************************/
void Pdr2_ManPrintPolicy( Aig_Man_t * pAig )
{
    Pdr2_Policy_t * p = ABC_CALLOC(Pdr2_Policy_t, 1);
    int F[12], fValid = Pdr2_PolicyFeatures(pAig, F), i, k;
    Pdr2_PolicyBuild(p, fValid ? F : NULL);
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

  Synopsis    [Checks the witness interface and initial state, then replays the original AIG.]

  Description []

***********************************************************************/
static int Pdr2_PolicyCheckCex( Aig_Man_t * pAig, Vec_Int_t * vInit, Abc_Cex_t * pCex )
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
    return Saig_ManVerifyCex( pAig, pCex );
}

/**Function*************************************************************

  Synopsis    [Runs the selected stages within a shared deadline and transfers checked results.]

  Description []

***********************************************************************/
int Pdr2_ManSolvePolicy( Aig_Man_t * pAig, Vec_Int_t * vInit, Pdr2_Par_t * pPars )
{
    Pdr2_Policy_t * p = ABC_CALLOC(Pdr2_Policy_t, 1);
    Pdr2_Par_t Child;
    Gip_Options_t Options;
    const char * Keys[24], * Values[24];
    abctime Start = Abc_Clock(), Deadline = pPars->nTimeOut ? Start + (abctime)pPars->nTimeOut * CLOCKS_PER_SEC : 0;
    int F[12], fValid = Pdr2_PolicyFeatures(pAig, F), i, k, nOptions, Budget, Result = -1;
    int fPrintParams = Gip_OptionGet("PDR2_POLICY_PARAMS") != NULL;
    Pdr2_PolicyBuild(p, fValid ? F : NULL);
    pPars->nPhasesRun = pPars->nRestartsRun = pPars->fBmcDecided = 0;
    if ( pPars->fVerbose )
        Abc_Print(1, "Native structural policy: one active engine, shared deadline, %d stages.\n", p->nStages);
    for ( i = 0; i < p->nStages; i++ )
    {
        Pdr2_PolicyStage_t * s = &p->Stages[i];
        Aig_Man_t * pWork;
        abctime StageStart = Abc_Clock();
        if ( pPars->pFuncStop && pPars->pFuncStop(pPars->RunId) ) break;
        Budget = s->nSeconds;
        if ( Deadline )
        {
            abctime Left = Deadline - StageStart;
            if ( Left <= 0 || (i > 0 && Left < CLOCKS_PER_SEC) ) break;
            Budget = Abc_MaxInt(1, Abc_MinInt(Budget, (int)((Left - CLOCKS_PER_SEC / 5) / CLOCKS_PER_SEC)));
        }
        else if ( i == p->nStages - 1 ) Budget = 0;
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
        pWork = Aig_ManDupSimple(pAig);
        assert(Aig_ManCiNum(pWork) == Aig_ManCiNum(pAig) && Aig_ManCoNum(pWork) == Aig_ManCoNum(pAig));
        assert(Aig_ManRegNum(pWork) == Aig_ManRegNum(pAig));
        Result = s->pCommand ? Pdr2_PolicySimulate(pWork, vInit, &Child) : Pdr2_ManSolveInit(pWork, vInit, &Child);
        pPars->iFrame = Child.iFrame;
        pPars->nPhasesRun += Child.nPhasesRun; pPars->nRestartsRun += Child.nRestartsRun;
        pPars->fBmcDecided = Child.fBmcDecided;
        if ( Result == 0 )
        {
            if ( Pdr2_PolicyCheckCex(pAig, vInit, pWork->pSeqModel) )
            {
                Abc_CexFreeP( &pAig->pSeqModel );
                pAig->pSeqModel = pWork->pSeqModel;
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
    ABC_FREE(p);
    return Result;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
