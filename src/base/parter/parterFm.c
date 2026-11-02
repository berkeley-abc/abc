/**CFile****************************************************************

  FileName    [parterFm.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Acyclic word-level partitioning.]

  Synopsis    [Acyclic hypergraph FM with indexed gains and best-prefix rollback.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: parterFm.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
#include "parterInt.h"

ABC_NAMESPACE_IMPL_START

typedef struct Prt_FmWeight_t_
{
    double Weight;
    unsigned Object;
} Prt_FmWeight_t;

typedef struct Prt_Fm_t_
{
    const Prt_Graph_t * pGraph;
    const Prt_Options_t * pOptions;
    unsigned * pParts, * pCounts[2], * pPredB, * pSuccA;
    unsigned * pReady, * pRank, * pMoves, * pBest[2];
    Prt_FmWeight_t * pOrder;
    unsigned char * pLocked;
    double * pGain;
    unsigned nLeaves, nObjects[2];
    double Total, WeightA, Cut, Low, High, Slack;
} Prt_Fm_t;

/**Function*************************************************************

  Synopsis    [Sets modest deterministic defaults without global random state.]

***********************************************************************/
void Prt_OptionsDefault( Prt_Options_t * p )
{
    if ( !p ) return;
    memset(p,0,sizeof(*p));
    p->BalanceTolerance = 0.10;
    p->nPasses = 4;
    p->Seed = 1;
}

/**Function*************************************************************

  Synopsis    [Checks cancellation only through the caller's optional callback.]

***********************************************************************/
static int Prt_FmCancelled( const Prt_Options_t * p )
{
    return p->pCancel && p->pCancel(p->pUser);
}

/**Function*************************************************************

  Synopsis    [Advances a seeded unsigned generator with defined wraparound.]

***********************************************************************/
static unsigned Prt_FmRandom( unsigned * pState )
{
    *pState ^= *pState << 13;
    *pState ^= *pState >> 17;
    *pState ^= *pState << 5;
    return *pState;
}

/**Function*************************************************************

  Synopsis    [Counts each hypernet once, using distinct driver and sink vertices.]

***********************************************************************/
double Prt_CutWeight( const Prt_Graph_t * p, const unsigned * pParts )
{
    unsigned e, i, Part, Other;
    double Cut = 0;
    for ( e = 0; e < p->nNets; ++e )
    {
        Part = p->pDriver[e] == PRT_NONE ? PRT_NONE : pParts[p->pDriver[e]];
        for ( i = p->pSinkStart[e]; i < p->pSinkStart[e+1]; ++i )
        {
            Other = pParts[p->pSinks[i]];
            if ( Part == PRT_NONE ) Part = Other;
            else if ( Part != Other ) { Cut += p->pNetWeight[e]; break; }
        }
    }
    return Cut;
}

/**Function*************************************************************

  Synopsis    [Builds a seeded topological order and its nearest balanced prefix.]

***********************************************************************/
static int Prt_FmInitial( Prt_Fm_t * p, char * pError, unsigned nError )
{
    const Prt_Graph_t * g = p->pGraph;
    unsigned * pCount = p->pPredB, * pReady = p->pReady, * pOrder = p->pMoves;
    unsigned v, w, e, i, j, k, nReady = 0, nOrder = 0, Best = 0;
    unsigned State = p->pOptions->Seed ? p->pOptions->Seed : 1;
    double Weight = 0, Delta, BestDelta = DBL_MAX, CountDelta, BestCount = DBL_MAX;
    for ( v = 0; v < g->nObjs; ++v )
    {
        pCount[v] = 0;
        for ( i = g->pInStart[v]; i < g->pInStart[v+1]; ++i )
            pCount[v] += g->pDriver[g->pInNets[i]] != PRT_NONE;
        if ( !pCount[v] ) pReady[nReady++] = v;
    }
    while ( nReady )
    {
        if ( Prt_FmCancelled(p->pOptions) ) return Prt_Error(pError,nError,"Partitioning cancelled.");
        k = p->pOptions->Seed ? Prt_FmRandom(&State) % nReady : 0;
        v = pReady[k];
        pReady[k] = pReady[--nReady];
        pOrder[nOrder++] = v;
        for ( i = g->pOutStart[v]; i < g->pOutStart[v+1]; ++i )
        {
            e = g->pOutNets[i];
            for ( j = g->pSinkStart[e]; j < g->pSinkStart[e+1]; ++j )
            {
                w = g->pSinks[j];
                if ( --pCount[w] == 0 ) pReady[nReady++] = w;
            }
        }
    }
    if ( nOrder != g->nObjs ) return Prt_Error(pError,nError,"Bisection requires an acyclic graph.");
    for ( i = 1; i < nOrder; ++i )
    {
        Weight += g->pObjWeight[pOrder[i-1]];
        Delta = fabs(Weight-p->Total/2);
        CountDelta = fabs((double)i-(double)nOrder/2);
        if ( Delta < BestDelta || (Delta == BestDelta && CountDelta < BestCount) )
        { Best = i; BestDelta = Delta; BestCount = CountDelta; }
    }
    for ( i = 0; i < nOrder; ++i ) p->pParts[pOrder[i]] = i >= Best;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Compares gains with a stable original-object tie-break.]

***********************************************************************/
static int Prt_FmBetter( const Prt_Fm_t * p, unsigned A, unsigned B )
{
    return p->pGain[A] > p->pGain[B] || (p->pGain[A] == p->pGain[B] && A < B);
}

/**Function*************************************************************

  Synopsis    [Orders fixed weights once, with deterministic equal-weight ranks.]

***********************************************************************/
static int Prt_FmWeightCompare( const void * pA, const void * pB )
{
    const Prt_FmWeight_t * a = (const Prt_FmWeight_t *)pA;
    const Prt_FmWeight_t * b = (const Prt_FmWeight_t *)pB;
    if ( a->Weight != b->Weight ) return a->Weight < b->Weight ? -1 : 1;
    return (a->Object > b->Object) - (a->Object < b->Object);
}

/**Function*************************************************************

  Synopsis    [Chooses the best present candidate without changing gain tie-breaks.]

***********************************************************************/
static unsigned Prt_FmBest( const Prt_Fm_t * p, unsigned A, unsigned B )
{
    if ( A == PRT_NONE ) return B;
    if ( B == PRT_NONE ) return A;
    return Prt_FmBetter(p,A,B) ? A : B;
}

/**Function*************************************************************

  Synopsis    [Updates one direction's indexed selection tree in logarithmic time.]

***********************************************************************/
static void Prt_FmTreeSet( Prt_Fm_t * p, unsigned v, unsigned Value )
{
    unsigned * pTree = p->pBest[p->pParts[v]];
    unsigned Index = p->nLeaves+p->pRank[v];
    pTree[Index] = Value;
    while ( (Index >>= 1) != 0 )
        pTree[Index] = Prt_FmBest(p,pTree[2*Index],pTree[2*Index+1]);
}

/**Function*************************************************************

  Synopsis    [Includes exactly unlocked vertices movable without a reverse edge.]

***********************************************************************/
static void Prt_FmUpdate( Prt_Fm_t * p, unsigned v )
{
    int Eligible = !p->pLocked[v] && (p->pParts[v] ? !p->pPredB[v] : !p->pSuccA[v]);
    Prt_FmTreeSet(p,v,Eligible ? v : PRT_NONE);
}

/**Function*************************************************************

  Synopsis    [Computes a net's exact contribution to a vertex's move gain.]

***********************************************************************/
static double Prt_FmTerm( unsigned A, unsigned B, unsigned Part, double Weight )
{
    unsigned Here = Part ? B : A, There = Part ? A : B;
    return (Here == 1 ? Weight : 0) - (There == 0 ? Weight : 0);
}

/**Function*************************************************************

  Synopsis    [Rebuilds all mutable counters from immutable topology and part labels.]

***********************************************************************/
static int Prt_FmPrepare( Prt_Fm_t * p, char * pError, unsigned nError )
{
    const Prt_Graph_t * g = p->pGraph;
    unsigned v, w, e, i, Part;
    p->nObjects[0] = p->nObjects[1] = 0;
    memset(p->pBest[0],0xff,(size_t)2*p->nLeaves*sizeof(unsigned));
    memset(p->pBest[1],0xff,(size_t)2*p->nLeaves*sizeof(unsigned));
    p->WeightA = p->Cut = 0;
    memset(p->pPredB,0,(size_t)g->nObjs*sizeof(unsigned));
    memset(p->pSuccA,0,(size_t)g->nObjs*sizeof(unsigned));
    memset(p->pGain,0,(size_t)g->nObjs*sizeof(double));
    memset(p->pLocked,0,(size_t)g->nObjs*sizeof(unsigned char));
    memset(p->pCounts[0],0,(size_t)g->nNets*sizeof(unsigned));
    memset(p->pCounts[1],0,(size_t)g->nNets*sizeof(unsigned));
    for ( v = 0; v < g->nObjs; ++v )
    {
        Part = p->pParts[v];
        if ( Part > 1 ) return Prt_Error(pError,nError,"Invalid initial part at object %u.",v);
        ++p->nObjects[Part];
        if ( !Part ) p->WeightA += g->pObjWeight[v];
    }
    if ( !p->nObjects[0] || !p->nObjects[1] )
        return Prt_Error(pError,nError,"Bisection requires two nonempty parts.");
    for ( e = 0; e < g->nNets; ++e )
    {
        v = g->pDriver[e];
        if ( v != PRT_NONE ) ++p->pCounts[p->pParts[v]][e];
        for ( i = g->pSinkStart[e]; i < g->pSinkStart[e+1]; ++i )
        {
            w = g->pSinks[i]; ++p->pCounts[p->pParts[w]][e];
            if ( v == PRT_NONE ) continue;
            if ( p->pParts[v] > p->pParts[w] )
                return Prt_Error(pError,nError,"Initial parts contain a backward dependency.");
            p->pPredB[w] += p->pParts[v] == 1;
            p->pSuccA[v] += p->pParts[w] == 0;
        }
        if ( p->pCounts[0][e] && p->pCounts[1][e] ) p->Cut += g->pNetWeight[e];
        if ( v != PRT_NONE ) p->pGain[v] += Prt_FmTerm(p->pCounts[0][e],p->pCounts[1][e],p->pParts[v],g->pNetWeight[e]);
        for ( i = g->pSinkStart[e]; i < g->pSinkStart[e+1]; ++i )
        {
            w = g->pSinks[i];
            p->pGain[w] += Prt_FmTerm(p->pCounts[0][e],p->pCounts[1][e],p->pParts[w],g->pNetWeight[e]);
        }
    }
    for ( v = 0; v < g->nObjs; ++v ) Prt_FmUpdate(p,v);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Adjusts one unlocked neighbor's gain after a net population changes.]

***********************************************************************/
static void Prt_FmAdjust( Prt_Fm_t * p, unsigned v, unsigned e, unsigned A, unsigned B )
{
    double Weight = p->pGraph->pNetWeight[e];
    if ( p->pLocked[v] ) return;
    p->pGain[v] -= Prt_FmTerm(A,B,p->pParts[v],Weight);
    p->pGain[v] += Prt_FmTerm(p->pCounts[0][e],p->pCounts[1][e],p->pParts[v],Weight);
    if ( p->pBest[p->pParts[v]][p->nLeaves+p->pRank[v]] != PRT_NONE )
        Prt_FmTreeSet(p,v,v);
}

/**Function*************************************************************

  Synopsis    [Updates hypernet counts, cut weight, and all incident gain keys.]

***********************************************************************/
static void Prt_FmMoveNet( Prt_Fm_t * p, unsigned e, unsigned Old )
{
    const Prt_Graph_t * g = p->pGraph;
    unsigned i, A = p->pCounts[0][e], B = p->pCounts[1][e];
    if ( A && B ) p->Cut -= g->pNetWeight[e];
    --p->pCounts[Old][e]; ++p->pCounts[1-Old][e];
    if ( p->pCounts[0][e] && p->pCounts[1][e] ) p->Cut += g->pNetWeight[e];
    // Interior populations contribute zero to every remaining move gain.
    if ( (Old ? B : A) > 2 && (Old ? A : B) > 1 ) return;
    if ( g->pDriver[e] != PRT_NONE ) Prt_FmAdjust(p,g->pDriver[e],e,A,B);
    for ( i = g->pSinkStart[e]; i < g->pSinkStart[e+1]; ++i )
        Prt_FmAdjust(p,g->pSinks[i],e,A,B);
}

/**Function*************************************************************

  Synopsis    [Moves and locks a vertex, updating directed counts independently of gains.]

***********************************************************************/
static void Prt_FmMove( Prt_Fm_t * p, unsigned v )
{
    const Prt_Graph_t * g = p->pGraph;
    unsigned Old = p->pParts[v], i, j, e, w;
    Prt_FmTreeSet(p,v,PRT_NONE);
    p->pLocked[v] = 1; p->pParts[v] = 1-Old;
    --p->nObjects[Old]; ++p->nObjects[1-Old];
    p->WeightA += Old ? g->pObjWeight[v] : -g->pObjWeight[v];
    for ( i = g->pInStart[v]; i < g->pInStart[v+1]; ++i )
    {
        e = g->pInNets[i]; Prt_FmMoveNet(p,e,Old);
        w = g->pDriver[e];
        if ( w == PRT_NONE ) continue;
        if ( Old ) ++p->pSuccA[w]; else --p->pSuccA[w];
        Prt_FmUpdate(p,w);
    }
    for ( i = g->pOutStart[v]; i < g->pOutStart[v+1]; ++i )
    {
        e = g->pOutNets[i]; Prt_FmMoveNet(p,e,Old);
        for ( j = g->pSinkStart[e]; j < g->pSinkStart[e+1]; ++j )
        {
            w = g->pSinks[j];
            if ( Old ) --p->pPredB[w]; else ++p->pPredB[w];
            Prt_FmUpdate(p,w);
        }
    }
}

/**Function*************************************************************

  Synopsis    [Returns the highest-gain movable vertex that respects the weight window.]

***********************************************************************/
static unsigned Prt_FmSelect( Prt_Fm_t * p )
{
    unsigned Part, Low, High, Mid, Left, Right, Best = PRT_NONE;
    double Weight;
    for ( Part = 0; Part < 2; ++Part )
    {
        if ( p->nObjects[Part] < 2 ) continue;
        Low = 0; High = p->pGraph->nObjs;
        // Compare the actual post-move sum, avoiding threshold rounding changes.
        while ( Low < High )
        {
            Mid = Low+(High-Low)/2;
            Weight = p->WeightA + (Part ? p->pOrder[Mid].Weight : -p->pOrder[Mid].Weight);
            if ( Part ? Weight <= p->High+p->Slack : Weight >= p->Low-p->Slack ) Low = Mid+1;
            else High = Mid;
        }
        Left = p->nLeaves; Right = p->nLeaves+Low;
        while ( Left < Right )
        {
            if ( Left & 1 ) Best = Prt_FmBest(p,Best,p->pBest[Part][Left++]);
            if ( Right & 1 ) Best = Prt_FmBest(p,Best,p->pBest[Part][--Right]);
            Left >>= 1; Right >>= 1;
        }
    }
    return Best;
}

/**Function*************************************************************

  Synopsis    [Measures excess over the requested balanced window.]

***********************************************************************/
static double Prt_FmViolation( const Prt_Fm_t * p, double Weight )
{
    double Limit = p->Total * (0.5 + 0.5*p->pOptions->BalanceTolerance);
    double Excess = Weight > p->Total/2 ? Weight-Limit : p->Total-Weight-Limit;
    return Excess > p->Slack ? Excess : 0;
}

/**Function*************************************************************

  Synopsis    [Releases every workspace array, including partial allocations.]

***********************************************************************/
static void Prt_FmFree( Prt_Fm_t * p )
{
    free(p->pParts); free(p->pCounts[0]); free(p->pCounts[1]);
    free(p->pPredB); free(p->pSuccA); free(p->pReady); free(p->pRank);
    free(p->pMoves); free(p->pOrder); free(p->pLocked); free(p->pGain);
    free(p->pBest[0]); free(p->pBest[1]);
}

#ifdef ABC_PARTER_FM_TEST
unsigned Prt_FmOracleChecks = 0;

/**Function*************************************************************

  Synopsis    [Checks incremental state against independent cut and dependency scans.]

***********************************************************************/
static void Prt_FmOracle( Prt_Fm_t * p )
{
    const Prt_Graph_t * g = p->pGraph;
    unsigned v, i, e, w;
    double Before, After, Scale = 0;
    int Legal, Eligible;
    if ( g->nObjs > 8 ) return;
    Before = Prt_CutWeight(g,p->pParts);
    for ( e = 0; e < g->nNets; ++e ) Scale += g->pNetWeight[e];
    for ( v = 0; v < g->nObjs; ++v )
    {
        if ( p->pLocked[v] ) continue;
        p->pParts[v] ^= 1;
        After = Prt_CutWeight(g,p->pParts);
        Legal = 1;
        for ( e = 0; e < g->nNets; ++e )
            if ( g->pDriver[e] != PRT_NONE )
                for ( i = g->pSinkStart[e]; i < g->pSinkStart[e+1]; ++i )
                    if ( p->pParts[g->pDriver[e]] > p->pParts[g->pSinks[i]] ) Legal = 0;
        p->pParts[v] ^= 1;
        Eligible = p->pParts[v] ? !p->pPredB[v] : !p->pSuccA[v];
        ++Prt_FmOracleChecks;
        if ( fabs((Before-After)-p->pGain[v]) > 256*DBL_EPSILON*Scale ||
             !(p->pGain[v] >= -DBL_MAX && p->pGain[v] <= DBL_MAX) ||
             Legal != Eligible || Eligible != (p->pBest[p->pParts[v]][p->nLeaves+p->pRank[v]] != PRT_NONE) )
        { fprintf(stderr,"FM gain/legality oracle failed at vertex %u.\n",v); abort(); }
    }
    w = PRT_NONE;
    for ( v = 0; v < g->nObjs; ++v )
    {
        double Weight = p->WeightA + (p->pParts[v] ? g->pObjWeight[v] : -g->pObjWeight[v]);
        if ( p->pLocked[v] || (p->pParts[v] ? p->pPredB[v] : p->pSuccA[v]) ||
             p->nObjects[p->pParts[v]] < 2 || Weight < p->Low-p->Slack || Weight > p->High+p->Slack ) continue;
        w = Prt_FmBest(p,w,v);
    }
    ++Prt_FmOracleChecks;
    if ( Prt_FmSelect(p) != w )
    { fprintf(stderr,"FM weighted selection oracle failed.\n"); abort(); }

}
#endif

/**Function*************************************************************

  Synopsis    [Refines a legal prefix and publishes only a fully checked result.]

***********************************************************************/
static int Prt_FmRun( const Prt_Graph_t * g, const Prt_Options_t * pOptions,
    unsigned * pParts, Prt_Stats_t * pStats, int fInitial, char * pError, unsigned nError )
{
    Prt_Options_t Default;
    Prt_Stats_t Stats;
    Prt_Fm_t Fm, * p = &Fm;
    unsigned v, Pass, nMoves, nBest, i;
    double BestCut, BestViolation, Violation, CutSlack, InitialViolation, StartCut, StartViolation;
    int Result = 0, Improved;
    if ( !pOptions ) { Prt_OptionsDefault(&Default); pOptions = &Default; }
    if ( !Prt_GraphCheck(g,pError,nError) ) return 0;
    if ( !pParts || g->nObjs < 2 || !(pOptions->BalanceTolerance >= 0 && pOptions->BalanceTolerance <= 1) )
        return Prt_Error(pError,nError,"Invalid bisection options or fewer than two objects.");
    memset(p,0,sizeof(*p)); memset(&Stats,0,sizeof(Stats));
    p->pGraph = g; p->pOptions = pOptions;
    p->pParts = (unsigned *)Prt_Alloc(g->nObjs,sizeof(unsigned));
    p->pCounts[0] = (unsigned *)Prt_Alloc(g->nNets,sizeof(unsigned));
    p->pCounts[1] = (unsigned *)Prt_Alloc(g->nNets,sizeof(unsigned));
    p->pPredB = (unsigned *)Prt_Alloc(g->nObjs,sizeof(unsigned));
    p->pSuccA = (unsigned *)Prt_Alloc(g->nObjs,sizeof(unsigned));
    p->pReady = (unsigned *)Prt_Alloc(g->nObjs,sizeof(unsigned));
    p->pRank = (unsigned *)Prt_Alloc(g->nObjs,sizeof(unsigned));
    p->pMoves = (unsigned *)Prt_Alloc(g->nObjs,sizeof(unsigned));
    p->pOrder = (Prt_FmWeight_t *)Prt_Alloc(g->nObjs,sizeof(Prt_FmWeight_t));
    p->nLeaves = 1;
    while ( p->nLeaves < g->nObjs && p->nLeaves <= PRT_NONE/4 ) p->nLeaves *= 2;
    if ( p->nLeaves < g->nObjs ) { Prt_Error(pError,nError,"FM selection tree size overflow."); goto cleanup; }
    p->pBest[0] = (unsigned *)Prt_Alloc((size_t)2*p->nLeaves,sizeof(unsigned));
    p->pBest[1] = (unsigned *)Prt_Alloc((size_t)2*p->nLeaves,sizeof(unsigned));
    p->pLocked = (unsigned char *)Prt_Alloc(g->nObjs,sizeof(unsigned char));
    p->pGain = (double *)Prt_Alloc(g->nObjs,sizeof(double));
    if ( !p->pParts || !p->pCounts[0] || !p->pCounts[1] || !p->pPredB || !p->pSuccA ||
        !p->pReady || !p->pRank || !p->pMoves || !p->pOrder || !p->pLocked || !p->pGain || !p->pBest[0] || !p->pBest[1] )
    { Prt_Error(pError,nError,"FM allocation failed."); goto cleanup; }
    for ( v = 0; v < g->nObjs; ++v )
    {
        p->Total += g->pObjWeight[v];
        p->pOrder[v].Weight = g->pObjWeight[v]; p->pOrder[v].Object = v;
    }
    qsort(p->pOrder,g->nObjs,sizeof(Prt_FmWeight_t),Prt_FmWeightCompare);
    for ( v = 0; v < g->nObjs; ++v ) p->pRank[p->pOrder[v].Object] = v;
    p->Slack = 64*DBL_EPSILON*p->Total;
    if ( Prt_FmCancelled(pOptions) ) { Prt_Error(pError,nError,"Partitioning cancelled."); goto cleanup; }
    if ( fInitial )
    {
        if ( !Prt_FmInitial(p,pError,nError) ) goto cleanup;
    }
    else
    {
        if ( !Prt_GraphTopoChecked(g,p->pMoves,pError,nError) ) goto cleanup;
        memcpy(p->pParts,pParts,(size_t)g->nObjs*sizeof(unsigned));
    }
    if ( !Prt_FmPrepare(p,pError,nError) ) goto cleanup;
    Stats.InitialCut = p->Cut;
    p->High = p->Total*(0.5+0.5*pOptions->BalanceTolerance);
    if ( p->WeightA > p->High ) p->High = p->WeightA;
    if ( p->Total-p->WeightA > p->High ) p->High = p->Total-p->WeightA;
    p->Low = p->Total-p->High;
    CutSlack = 64*DBL_EPSILON*Stats.InitialCut;
    InitialViolation = Prt_FmViolation(p,p->WeightA);
    for ( Pass = 0; Pass < pOptions->nPasses; ++Pass )
    {
        if ( Pass && !Prt_FmPrepare(p,pError,nError) ) goto cleanup;
#ifdef ABC_PARTER_FM_TEST
        Prt_FmOracle(p);
#endif
        StartCut = BestCut = p->Cut;
        StartViolation = BestViolation = Prt_FmViolation(p,p->WeightA);
        nMoves = nBest = 0; Improved = 0;
        ++Stats.nPasses;
        while ( (v = Prt_FmSelect(p)) != PRT_NONE )
        {
            if ( Prt_FmCancelled(pOptions) ) { Prt_Error(pError,nError,"Partitioning cancelled."); goto cleanup; }
            if ( Stats.nMoves == PRT_NONE )
            { Prt_Error(pError,nError,"FM move count overflow."); goto cleanup; }
            p->pMoves[nMoves++] = v; ++Stats.nMoves;
            Prt_FmMove(p,v);
#ifdef ABC_PARTER_FM_TEST
            Prt_FmOracle(p);
#endif
            Violation = Prt_FmViolation(p,p->WeightA);
            if ( Violation < BestViolation-p->Slack ||
                (fabs(Violation-BestViolation) <= p->Slack && p->Cut < BestCut-CutSlack) )
            { BestCut = p->Cut; BestViolation = Violation; nBest = nMoves; Improved = 1; }
        }
        for ( i = nMoves; i > nBest; --i ) p->pParts[p->pMoves[i-1]] ^= 1;
        if ( Improved )
        {
            // Recompute before accepting so accumulated floating-point updates
            // cannot turn a non-improving prefix into an accepted change.
            if ( !Prt_FmPrepare(p,pError,nError) ) goto cleanup;
            Violation = Prt_FmViolation(p,p->WeightA);
            if ( !(Violation < StartViolation-p->Slack ||
                (fabs(Violation-StartViolation) <= p->Slack && p->Cut < StartCut-CutSlack)) )
            {
                for ( i = nBest; i > 0; --i ) p->pParts[p->pMoves[i-1]] ^= 1;
                Improved = 0;
            }
        }
        if ( !Improved ) break;
    }
    if ( !Prt_FmPrepare(p,pError,nError) ) goto cleanup;
    Stats.FinalCut = Prt_CutWeight(g,p->pParts);
    Stats.Weight[0] = p->WeightA; Stats.Weight[1] = p->Total-p->WeightA;
    Stats.fBalanced = Prt_FmViolation(p,p->WeightA) == 0;
    if ( Prt_FmViolation(p,p->WeightA) > InitialViolation+p->Slack )
    { Prt_Error(pError,nError,"FM internal balance check failed."); goto cleanup; }
    if ( pOptions->fHardBalance && !Stats.fBalanced )
    { Prt_Error(pError,nError,"No split meeting the requested balance was found."); goto cleanup; }
    if ( Prt_FmCancelled(pOptions) ) { Prt_Error(pError,nError,"Partitioning cancelled."); goto cleanup; }
    memcpy(pParts,p->pParts,(size_t)g->nObjs*sizeof(unsigned));
    if ( pStats ) *pStats = Stats;
    if ( pError && nError ) pError[0] = 0;
    Result = 1;
cleanup:
    Prt_FmFree(p);
    return Result;
}

/**Function*************************************************************

  Synopsis    [Initializes and refines a deterministic acyclic bisection.]

***********************************************************************/
int Prt_Bisect( const Prt_Graph_t * p, const Prt_Options_t * pOptions,
    unsigned * pParts, Prt_Stats_t * pStats, char * pError, unsigned nError )
{
    return Prt_FmRun(p,pOptions,pParts,pStats,1,pError,nError);
}

/**Function*************************************************************

  Synopsis    [Refines caller-supplied legal part labels transactionally.]

***********************************************************************/
int Prt_Refine( const Prt_Graph_t * p, const Prt_Options_t * pOptions,
    unsigned * pParts, Prt_Stats_t * pStats, char * pError, unsigned nError )
{
    return Prt_FmRun(p,pOptions,pParts,pStats,0,pError,nError);
}

ABC_NAMESPACE_IMPL_END
