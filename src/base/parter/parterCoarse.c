/**CFile****************************************************************

  FileName    [parterCoarse.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Acyclic word-level partitioning.]

  Synopsis    [Conservative bounded multilevel acyclic hypergraph refinement.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: parterCoarse.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
#include "parterInt.h"

ABC_NAMESPACE_IMPL_START

/**Function*************************************************************

  Synopsis    [Computes strict longest-path ranks from a validated topological order.]

***********************************************************************/
static int Prt_CoarseRanks( const Prt_Graph_t * p, unsigned * pRank,
    unsigned * pOrder, char * pError, unsigned nError )
{
    unsigned k, v, e, i, w;
    if ( !Prt_GraphTopoChecked(p,pOrder,pError,nError) ) return 0;
    memset(pRank,0,(size_t)p->nObjs*sizeof(unsigned));
    for ( k = 0; k < p->nObjs; ++k )
    {
        v = pOrder[k];
        for ( i = p->pInStart[v]; i < p->pInStart[v+1]; ++i )
        {
            e = p->pInNets[i]; w = p->pDriver[e];
            if ( w != PRT_NONE && pRank[v] < pRank[w]+1 ) pRank[v] = pRank[w]+1;
        }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Finds the sole distinct successor, independent of parallel net count.]

***********************************************************************/
static unsigned Prt_CoarseSuccessor( const Prt_Graph_t * p, unsigned v )
{
    unsigned i, j, e, Result = PRT_NONE;
    for ( i = p->pOutStart[v]; i < p->pOutStart[v+1]; ++i )
    {
        e = p->pOutNets[i];
        for ( j = p->pSinkStart[e]; j < p->pSinkStart[e+1]; ++j )
        {
            if ( Result != PRT_NONE && Result != p->pSinks[j] ) return PRT_NONE;
            Result = p->pSinks[j];
        }
    }
    return Result;
}

/**Function*************************************************************

  Synopsis    [Matches equal-rank neighbors or sole-successor edges in separate batches.]

***********************************************************************/
static unsigned Prt_CoarseMatch( const Prt_Graph_t * p, const unsigned * pRank,
    double Limit, unsigned * pMap, unsigned * pFirst, int fSuccessor )
{
    unsigned v, w, e, i, j, Tried, Best, nObjects = 0, Count;
    double Score, BestScore;
    for ( v = 0; v < p->nObjs; ++v ) pMap[v] = PRT_NONE;
    for ( e = 0; e < p->nNets; ++e ) pFirst[e] = p->pSinkStart[e];
    for ( v = 0; v < p->nObjs; ++v )
    {
        if ( pMap[v] != PRT_NONE ) continue;
        Best = PRT_NONE; BestScore = -1;
        if ( fSuccessor )
        {
            w = Prt_CoarseSuccessor(p,v);
            if ( w != PRT_NONE && pMap[w] == PRT_NONE &&
                p->pObjWeight[v] <= Limit-p->pObjWeight[w] ) Best = w;
        }
        else
        {
            for ( i = p->pInStart[v]; i < p->pInStart[v+1]; ++i )
            {
                e = p->pInNets[i];
                while ( pFirst[e] < p->pSinkStart[e+1] && pMap[p->pSinks[pFirst[e]]] != PRT_NONE ) ++pFirst[e];
                Count = p->pSinkStart[e+1]-p->pSinkStart[e];
                Score = p->pNetWeight[e]/(Count > 1 ? Count-1 : 1);
                // Bound candidate probes per incident net; a high-fanout clock
                // must not turn matching into a quadratic pair expansion.
                for ( j = pFirst[e], Tried = 0; j < p->pSinkStart[e+1] && Tried < 64; ++j, ++Tried )
                {
                    w = p->pSinks[j];
                    if ( w == v || pMap[w] != PRT_NONE || pRank[v] != pRank[w] ||
                        p->pObjWeight[v] > Limit-p->pObjWeight[w] ) continue;
                    if ( Score > BestScore || (Score == BestScore && w < Best) )
                    { Best = w; BestScore = Score; }
                }
            }
        }
        pMap[v] = nObjects;
        if ( Best != PRT_NONE ) pMap[Best] = nObjects;
        ++nObjects;
    }
    return nObjects;
}

/**Function*************************************************************

  Synopsis    [Measures balanced-window excess consistently across candidate levels.]

***********************************************************************/
static double Prt_CoarseExcess( const Prt_Stats_t * p, const Prt_Options_t * o, double Total )
{
    double Limit = Total*(0.5+0.5*o->BalanceTolerance);
    if ( p->fBalanced ) return 0;
    return p->Weight[0] > Total/2 ? p->Weight[0]-Limit : Total-p->Weight[0]-Limit;
}

/**Function*************************************************************

  Synopsis    [Accumulates attempted work without wrapping public counters.]

***********************************************************************/
static int Prt_CoarseStats( Prt_Stats_t * p, const Prt_Stats_t * q, char * pError, unsigned nError )
{
    if ( p->nMoves > PRT_NONE-q->nMoves || p->nPasses > PRT_NONE-q->nPasses )
        return Prt_Error(pError,nError,"Multilevel statistics overflow.");
    p->nMoves += q->nMoves; p->nPasses += q->nPasses;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Builds bounded coarse graphs, uncoarsens, and retains only a quality win.]

***********************************************************************/
int Prt_BisectMulti( const Prt_Graph_t * pGraph, const Prt_Options_t * pOptions,
    unsigned nLevels, unsigned * pParts, Prt_Stats_t * pStats, char * pError, unsigned nError )
{
    Prt_Options_t Default, Relaxed;
    Prt_Stats_t Flat, Candidate, Work;
    Prt_Graph_t * pGraphs[17];
    unsigned * pMaps[16];
    unsigned * pBest = NULL, * pCurrent = NULL, * pNext = NULL;
    unsigned * pRank = NULL, * pOrder = NULL, * pFirst = NULL, * pSwap;
    unsigned Level = 0, nObjects, v, i;
    double Total = 0, Limit;
    int Result = 0;
    if ( !nLevels ) return Prt_Bisect(pGraph,pOptions,pParts,pStats,pError,nError);
    if ( nLevels > 16 ) return Prt_Error(pError,nError,"Multilevel limit must be at most 16.");
    if ( !pOptions ) { Prt_OptionsDefault(&Default); pOptions = &Default; }
    if ( !Prt_GraphCheck(pGraph,pError,nError) ) return 0;
    if ( !pParts ) return Prt_Error(pError,nError,"Missing multilevel result labels.");
    memset(pGraphs,0,sizeof(pGraphs)); memset(pMaps,0,sizeof(pMaps));
    pGraphs[0] = (Prt_Graph_t *)pGraph;
    pBest = (unsigned *)Prt_Alloc(pGraph->nObjs,sizeof(unsigned));
    pCurrent = (unsigned *)Prt_Alloc(pGraph->nObjs,sizeof(unsigned));
    pNext = (unsigned *)Prt_Alloc(pGraph->nObjs,sizeof(unsigned));
    pRank = (unsigned *)Prt_Alloc(pGraph->nObjs,sizeof(unsigned));
    pOrder = (unsigned *)Prt_Alloc(pGraph->nObjs,sizeof(unsigned));
    pFirst = (unsigned *)Prt_Alloc(pGraph->nNets,sizeof(unsigned));
    if ( !pBest || !pCurrent || !pNext || !pRank || !pOrder || !pFirst )
    { Prt_Error(pError,nError,"Multilevel workspace allocation failed."); goto cleanup; }
    if ( !Prt_Bisect(pGraph,pOptions,pBest,&Flat,pError,nError) ) goto cleanup;
    Work = Flat;
    for ( v = 0; v < pGraph->nObjs; ++v ) Total += pGraph->pObjWeight[v];
    Limit = Total*(0.5+0.5*pOptions->BalanceTolerance);
    while ( Level < nLevels && pGraphs[Level]->nObjs >= 4 )
    {
        if ( pOptions->pCancel && pOptions->pCancel(pOptions->pUser) )
        { Prt_Error(pError,nError,"Partitioning cancelled."); goto cleanup; }
        if ( !Prt_CoarseRanks(pGraphs[Level],pRank,pOrder,pError,nError) ) goto cleanup;
        pMaps[Level] = (unsigned *)Prt_Alloc(pGraphs[Level]->nObjs,sizeof(unsigned));
        if ( !pMaps[Level] ) { Prt_Error(pError,nError,"Multilevel mapping allocation failed."); goto cleanup; }
        nObjects = Prt_CoarseMatch(pGraphs[Level],pRank,Limit,pMaps[Level],pFirst,0);
        if ( nObjects > pGraphs[Level]->nObjs-pGraphs[Level]->nObjs/5 )
            nObjects = Prt_CoarseMatch(pGraphs[Level],pRank,Limit,pMaps[Level],pFirst,1);
        // Keep a level only when it removes at least one fifth of the objects.
        if ( nObjects < 2 || nObjects > pGraphs[Level]->nObjs-pGraphs[Level]->nObjs/5 ||
             nObjects == pGraphs[Level]->nObjs ) break;
        if ( !Prt_GraphContract(pGraphs[Level],nObjects,pMaps[Level],&pGraphs[Level+1],pError,nError) ) goto cleanup;
        if ( !Prt_GraphTopoChecked(pGraphs[Level+1],pOrder,pError,nError) ) goto cleanup;
        ++Level;
    }
    if ( Level )
    {
        Relaxed = *pOptions; Relaxed.fHardBalance = 0;
        if ( !Prt_Bisect(pGraphs[Level],&Relaxed,pCurrent,&Candidate,pError,nError) ||
             !Prt_CoarseStats(&Work,&Candidate,pError,nError) ) goto cleanup;
        for ( i = Level; i > 0; --i )
        {
            for ( v = 0; v < pGraphs[i-1]->nObjs; ++v ) pNext[v] = pCurrent[pMaps[i-1][v]];
            if ( !Prt_Refine(pGraphs[i-1],&Relaxed,pNext,&Candidate,pError,nError) ||
                 !Prt_CoarseStats(&Work,&Candidate,pError,nError) ) goto cleanup;
            pSwap = pCurrent; pCurrent = pNext; pNext = pSwap;
        }
        if ( Prt_CoarseExcess(&Candidate,pOptions,Total) <= Prt_CoarseExcess(&Flat,pOptions,Total) &&
             Candidate.FinalCut < Flat.FinalCut )
        {
            memcpy(pBest,pCurrent,(size_t)pGraph->nObjs*sizeof(unsigned));
            Work.FinalCut = Candidate.FinalCut;
            Work.Weight[0] = Candidate.Weight[0]; Work.Weight[1] = Candidate.Weight[1];
            Work.fBalanced = Candidate.fBalanced;
        }
    }
    if ( pOptions->pCancel && pOptions->pCancel(pOptions->pUser) )
    { Prt_Error(pError,nError,"Partitioning cancelled."); goto cleanup; }
    memcpy(pParts,pBest,(size_t)pGraph->nObjs*sizeof(unsigned));
    if ( pStats ) *pStats = Work;
    if ( pError && nError ) pError[0] = 0;
    Result = 1;
cleanup:
    for ( i = 1; i < 17; ++i ) Prt_GraphFree(pGraphs[i]);
    for ( i = 0; i < 16; ++i ) free(pMaps[i]);
    free(pBest); free(pCurrent); free(pNext); free(pRank); free(pOrder); free(pFirst);
    return Result;
}

ABC_NAMESPACE_IMPL_END
