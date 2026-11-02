/**CFile****************************************************************

  FileName    [parterRun.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Acyclic word-level partitioning.]

  Synopsis    [Bounded recursive size normalization on a private design.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: parterRun.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
#include "parterRun.h"
#include "parterExtract.h"
#include "parterInt.h"
#include "base/sn/snCheck.h"

ABC_NAMESPACE_IMPL_START

typedef struct Prt_RunJob_t_
{
    unsigned Master, ParentObjects;
} Prt_RunJob_t;

/**Function*************************************************************

  Synopsis    [Initializes the size and work budgets.]

***********************************************************************/
void Prt_RunOptionsDefault( Prt_RunOptions_t * p )
{
    memset(p,0,sizeof(*p));
    p->Top = PRT_NONE;
    p->MaxArea = 100000;
    p->FlopArea = 8;
    p->SramArea = 0.5;
    p->nMaxSplits = 1024;
    Prt_OptionsDefault(&p->Partition);
    p->Partition.fHardBalance = 0;
}

/**Function*************************************************************

  Synopsis    [Polls cancellation at transactional phase boundaries.]

***********************************************************************/
static int Prt_RunCancel( const Prt_RunOptions_t * p, char * pError, unsigned nError )
{
    if ( !p->Partition.pCancel || !p->Partition.pCancel(p->Partition.pUser) ) return 0;
    Prt_Error(pError,nError,"Partitioning cancelled; design unchanged.");
    return 1;
}

/**Function*************************************************************

  Synopsis    [Names the indivisible group that prevents the requested cap.]

***********************************************************************/
static int Prt_RunFeasible( const sn_design_t * pDesign, unsigned Master,
    const Prt_SnModel_t * pModel, double Cap, char * pError, unsigned nError )
{
    const sn_module_t * pModule = sn_design_get_module_const(pDesign,Master);
    const char * pName = sn_name_get(&pDesign->names,pModule->name);
    if ( pModel->MaxSccWeight > Cap )
        return Prt_Error(pError,nError,"Master %s (m%u) has indivisible SCC at o%u with area %.9g above cap %.9g.",
            pName,Master,pModel->MaxSccObject,pModel->MaxSccWeight,Cap);
    if ( pModel->nScc < 2 )
        return Prt_Error(pError,nError,"Master %s (m%u) has fewer than two indivisible groups.",pName,Master);
    return 1;
}

typedef struct Prt_RunInput_t_
{
    double Price;
    unsigned Count, Driver;
} Prt_RunInput_t;

/**Function*************************************************************

  Synopsis    [Orders input removal costs for a conservative fractional bound.]

***********************************************************************/
static int Prt_RunInputCompare( const void * pA, const void * pB )
{
    const Prt_RunInput_t * a = (const Prt_RunInput_t *)pA;
    const Prt_RunInput_t * b = (const Prt_RunInput_t *)pB;
    if ( a->Price != b->Price ) return a->Price < b->Price ? -1 : 1;
    return (a->Driver > b->Driver)-(a->Driver < b->Driver);
}

/**Function*************************************************************

  Synopsis    [Rejects unavoidable SCC input overflow under the estimated area cap.]

  Description [An SCC's incoming signals disappear only if their drivers join
  its part. Fractional packing of driver groups, ignoring all dependencies,
  overestimates the removable signals. Thus it cannot reject a feasible
  integral assignment in this area model. Floating slack favors acceptance.]

***********************************************************************/
static int Prt_RunPorts( const sn_design_t * pDesign, unsigned Master,
    const Prt_SnModel_t * pModel, double Cap, char * pError, unsigned nError )
{
    const Prt_Graph_t * g = pModel->pGraph;
    unsigned * pCount = NULL;
    Prt_RunInput_t * pInputs = NULL;
    unsigned v, i, w, e, nDrivers, nInputs;
    int Ok = 1;
    for ( v = 0; v < g->nObjs; ++v )
    {
        double Budget, Removed = 0, Slack = 1e-9*(1+g->nNets);
        if ( g->pInStart[v+1]-g->pInStart[v] <= UINT16_MAX ) continue;
        if ( !pCount )
        {
            pCount = (unsigned *)Prt_Alloc(g->nObjs,sizeof(unsigned));
            pInputs = (Prt_RunInput_t *)Prt_Alloc(g->nObjs,sizeof(*pInputs));
            if ( !pCount || !pInputs )
            { Ok = Prt_Error(pError,nError,"Port-bound allocation failed."); break; }
        }
        memset(pCount,0,(size_t)g->nObjs*sizeof(unsigned));
        nInputs = 0;
        for ( i = g->pInStart[v]; i < g->pInStart[v+1]; ++i )
        {
            e = g->pInNets[i]; w = g->pDriver[e];
            if ( w == v ) continue;
            ++nInputs;
            if ( w != PRT_NONE ) ++pCount[w];
        }
        for ( w = nDrivers = 0; w < g->nObjs; ++w )
            if ( pCount[w] )
            {
                pInputs[nDrivers].Price = g->pObjWeight[w]/pCount[w];
                pInputs[nDrivers].Count = pCount[w];
                pInputs[nDrivers++].Driver = w;
            }
        qsort(pInputs,nDrivers,sizeof(*pInputs),Prt_RunInputCompare);
        Budget = Cap-g->pObjWeight[v]+1e-9*(1+Cap);
        if ( Budget < 0 ) Budget = 0;
        for ( i = 0; i < nDrivers; ++i )
        {
            double Weight = g->pObjWeight[pInputs[i].Driver];
            if ( Weight <= Budget ) { Removed += pInputs[i].Count; Budget -= Weight; }
            else
            {
                Removed += Budget/Weight*pInputs[i].Count;
                break;
            }
        }
        if ( nInputs-Removed > UINT16_MAX+Slack )
        {
            const sn_module_t * m = sn_design_get_module_const(pDesign,Master);
            Ok = Prt_Error(pError,nError,
                "Master %s (m%u), SCC o%u needs at least %.0f input ports under estimated cap %.9g; SN supports %u. No FM search performed.",
                sn_name_get(&pDesign->names,m->name),Master,pModel->pVertexObject[v],
                ceil(nInputs-Removed-Slack),Cap,(unsigned)UINT16_MAX);
            break;
        }
    }
    free(pCount); free(pInputs);
    return Ok;
}

/**Function*************************************************************

  Synopsis    [Splits on a clone, remeasures lost sharing, and publishes once.]

***********************************************************************/
int Prt_SnPartition( const sn_design_t * pDesign, const Prt_RunOptions_t * pOptions,
    sn_design_t ** ppResult, Prt_RunStats_t * pStats, char * pError, unsigned nError )
{
    Prt_RunOptions_t Defaults;
    Prt_RunStats_t Stats;
    Prt_Stats_t SplitStats;
    Prt_ExtractStats_t ExtractStats;
    Sn_AigCost_t * pInitial = NULL, * pFinal = NULL;
    Sn_AigCostModule_t * pCurrent = NULL;
    const Sn_AigCostModule_t * pCost;
    Prt_SnModel_t * pModel = NULL;
    sn_design_t * pWork = NULL, * pNext = NULL;
    Prt_RunJob_t * pJobs = NULL, Job;
    unsigned * pLabels = NULL, * pObjectParts = NULL;
    unsigned char * pRetained = NULL;
    size_t Capacity, Read = 0, Write = 0;
    unsigned Top, i, v, First, Child;
    int Result = 0;
    if ( !ppResult ) return Prt_Error(pError,nError,"Missing partition result.");
    *ppResult = NULL;
    if ( pError && nError ) pError[0] = 0;
    Prt_RunOptionsDefault(&Defaults);
    if ( !pOptions ) pOptions = &Defaults;
    memset(&Stats,0,sizeof(Stats));
    if ( !pDesign || !pDesign->modules.size || pDesign->modules.size >= PRT_NONE ||
         !(pOptions->MaxArea > 0 && pOptions->MaxArea <= DBL_MAX) ||
         !(pOptions->FlopArea > 0 && pOptions->FlopArea <= DBL_MAX) ||
         !(pOptions->SramArea > 0 && pOptions->SramArea <= DBL_MAX) ||
         pOptions->nCoarseLevels > 16 ||
         !(pOptions->Partition.BalanceTolerance >= 0 && pOptions->Partition.BalanceTolerance <= 1) )
        return Prt_Error(pError,nError,"Invalid partition design, cap, coefficients, or balance tolerance.");
    Top = pOptions->Top == PRT_NONE ? (unsigned)pDesign->modules.size-1 : pOptions->Top;
    if ( Top >= pDesign->modules.size ) return Prt_Error(pError,nError,"Invalid top master.");
    if ( Prt_RunCancel(pOptions,pError,nError) ) goto cleanup;
    if ( !Sn_AigCostCompute(pDesign,Top,pOptions->fAll,pOptions->FlopArea,pOptions->SramArea,
                           &pInitial,pError,nError) ) goto cleanup;
    Stats.InitialArea = pInitial->LocalArea;
    Stats.nUnknown = pInitial->nOpaque;
    Capacity = pDesign->modules.size;
    if ( pOptions->nMaxSplits > (PRT_NONE-Capacity-1)/2 )
    { Prt_Error(pError,nError,"Partition module budget overflow."); goto cleanup; }
    if ( pOptions->nMaxSplits > (SIZE_MAX-Capacity)/2 )
    { Prt_Error(pError,nError,"Partition job budget overflow."); goto cleanup; }
    Capacity += (size_t)pOptions->nMaxSplits*2;
    pJobs = (Prt_RunJob_t *)Prt_Alloc(Capacity,sizeof(Prt_RunJob_t));
    pRetained = (unsigned char *)Prt_Alloc(Capacity,1);
    if ( !pJobs || !pRetained ) { Prt_Error(pError,nError,"Partition job allocation failed."); goto cleanup; }
    for ( i = 0; i < pInitial->nModules; ++i )
    {
        pCost = pInitial->pModules+i;
        if ( !pCost->fSelected ) continue;
        if ( !pCost->Known )
        {
            if ( pOptions->pLog ) fprintf(pOptions->pLog,"  m%u: unknown cost retained (%s).\n",i,pCost->UnknownReason);
            continue;
        }
        if ( pCost->LocalArea <= pOptions->MaxArea ) continue;
        if ( Prt_RunCancel(pOptions,pError,nError) ||
             !Prt_SnBuild(sn_design_get_module_const(pDesign,i),pCost,&pModel,pError,nError) ) goto cleanup;
        if ( !Prt_RunFeasible(pDesign,i,pModel,pOptions->MaxArea,pError,nError) )
        {
            if ( pOptions->pLog ) fprintf(pOptions->pLog,"  retained: %s\n",pError && nError ? pError : "indivisible master");
            pRetained[i] = 1; ++Stats.nIndivisible;
            if ( pError && nError ) pError[0] = 0;
            Prt_SnFree(pModel); pModel = NULL;
            continue;
        }
        if ( !Prt_RunPorts(pDesign,i,pModel,pOptions->MaxArea,pError,nError) ) goto cleanup;
        Prt_SnFree(pModel); pModel = NULL;
        pJobs[Write].Master = i; pJobs[Write++].ParentObjects = PRT_NONE;
    }
    pWork = sn_design_dup(pDesign);
    if ( !pWork ) { Prt_Error(pError,nError,"Design clone failed."); goto cleanup; }
    while ( Read < Write )
    {
        Job = pJobs[Read++];
        if ( Prt_RunCancel(pOptions,pError,nError) ) goto cleanup;
        if ( Job.Master < pInitial->nModules ) pCost = pInitial->pModules+Job.Master;
        else
        {
            if ( !Sn_AigCostComputeModuleLocal(pWork,Job.Master,pOptions->FlopArea,pOptions->SramArea,
                                   &pCurrent,pError,nError) ) goto cleanup;
            pCost = pCurrent;
        }
        if ( !pCost->Known )
        { Prt_Error(pError,nError,"Extracted master m%u has unknown cost: %s.",Job.Master,pCost->UnknownReason); goto cleanup; }
        if ( pCost->LocalArea <= pOptions->MaxArea )
        { Sn_AigCostModuleFree(pCurrent); pCurrent = NULL; continue; }
        if ( !Prt_SnBuild(sn_design_get_module_const(pWork,Job.Master),pCost,&pModel,pError,nError) ) goto cleanup;
        if ( !Prt_RunFeasible(pWork,Job.Master,pModel,pOptions->MaxArea,pError,nError) )
        {
            if ( pOptions->pLog ) fprintf(pOptions->pLog,"  retained: %s\n",pError && nError ? pError : "indivisible master");
            pRetained[Job.Master] = 1; ++Stats.nIndivisible;
            if ( pError && nError ) pError[0] = 0;
            Prt_SnFree(pModel); pModel = NULL;
            Sn_AigCostModuleFree(pCurrent); pCurrent = NULL;
            continue;
        }
        if ( !Prt_RunPorts(pWork,Job.Master,pModel,pOptions->MaxArea,pError,nError) ) goto cleanup;
        if ( Job.ParentObjects != PRT_NONE && pModel->nMovable >= Job.ParentObjects )
        { Prt_Error(pError,nError,"Partition m%u did not reduce indivisible membership.",Job.Master); goto cleanup; }
        if ( Stats.nSplits == pOptions->nMaxSplits )
        { Prt_Error(pError,nError,"Partition split budget %u exhausted at m%u; design unchanged.",pOptions->nMaxSplits,Job.Master); goto cleanup; }
        pLabels = (unsigned *)Prt_Alloc(pModel->nScc,sizeof(unsigned));
        pObjectParts = (unsigned *)Prt_Alloc(pModel->nObjects,sizeof(unsigned));
        if ( !pLabels || !pObjectParts )
        { Prt_Error(pError,nError,"Partition label allocation failed."); goto cleanup; }
        if ( !Prt_BisectMulti(pModel->pGraph,&pOptions->Partition,pOptions->nCoarseLevels,pLabels,&SplitStats,pError,nError) ) goto cleanup;
        for ( v = 0; v < pModel->nObjects; ++v )
            pObjectParts[v] = pModel->pObjToVertex[v] == PRT_NONE ? PRT_NONE : pLabels[pModel->pObjToVertex[v]];
        First = (unsigned)pWork->modules.size;
        if ( Prt_RunCancel(pOptions,pError,nError) ||
             !Prt_SnExtractPrivateMapped(pWork,Job.Master,pObjectParts,2,&pNext,&ExtractStats,NULL,pError,nError) ) goto cleanup;
        assert(pNext == pWork); pNext = NULL;
        if ( UINT64_MAX-Stats.InputBits < ExtractStats.InputBits || UINT64_MAX-Stats.OutputBits < ExtractStats.OutputBits )
        { Prt_Error(pError,nError,"Generated port-bit count overflow."); goto cleanup; }
        Stats.InputBits += ExtractStats.InputBits;
        Stats.OutputBits += ExtractStats.OutputBits;
        ++Stats.nSplits;
        Stats.nParts += 2;
        Stats.nRelaxed += !SplitStats.fBalanced;
        if ( pOptions->pLog ) fprintf(pOptions->pLog,
            "  m%u -> m%u,m%u: local %.9g; estimated %.9g + %.9g; cut %.9g -> %.9g%s.\n",
            Job.Master,First,First+1,pCost->LocalArea,SplitStats.Weight[0],SplitStats.Weight[1],
            SplitStats.InitialCut,SplitStats.FinalCut,SplitStats.fBalanced ? "" : "; relaxed balance");
        for ( Child = 0; Child < 2; ++Child )
        {
            assert(Write < Capacity);
            pJobs[Write].Master = First+Child;
            pJobs[Write++].ParentObjects = pModel->nMovable;
        }
        Prt_SnFree(pModel); pModel = NULL;
        Sn_AigCostModuleFree(pCurrent); pCurrent = NULL;
        free(pLabels); pLabels = NULL;
        free(pObjectParts); pObjectParts = NULL;
    }
    if ( Prt_RunCancel(pOptions,pError,nError) ) goto cleanup;
    if ( !Sn_AigCostCompute(pWork,Top,pOptions->fAll,pOptions->FlopArea,pOptions->SramArea,
                           &pFinal,pError,nError) ) goto cleanup;
    for ( i = 0; i < pFinal->nModules; ++i )
        if ( pFinal->pModules[i].fSelected && pFinal->pModules[i].Known &&
             pFinal->pModules[i].LocalArea > pOptions->MaxArea && !pRetained[i] )
        { Prt_Error(pError,nError,"Final master m%u area %.9g exceeds cap %.9g.",i,pFinal->pModules[i].LocalArea,pOptions->MaxArea); goto cleanup; }
    if ( Prt_RunCancel(pOptions,pError,nError) ) goto cleanup;
    Stats.FinalArea = pFinal->LocalArea;
    if ( pStats ) *pStats = Stats;
    *ppResult = pWork; pWork = NULL;
    if ( pError && nError ) pError[0] = 0;
    Result = 1;
cleanup:
    if ( pNext ) sn_design_destroy(pNext);
    if ( pWork ) sn_design_destroy(pWork);
    Sn_AigCostFree(pInitial); Sn_AigCostModuleFree(pCurrent); Sn_AigCostFree(pFinal);
    Prt_SnFree(pModel);
    free(pRetained); free(pJobs); free(pLabels); free(pObjectParts);
    return Result;
}

ABC_NAMESPACE_IMPL_END
