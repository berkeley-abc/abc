/**CFile****************************************************************

  FileName    [parterGraph.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Acyclic word-level partitioning.]

  Synopsis    [Immutable indexed hypergraphs, contraction, and iterative SCCs.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: parterGraph.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
#include "parterInt.h"

ABC_NAMESPACE_IMPL_START

/**Function*************************************************************

  Synopsis    [Formats a bounded diagnostic and returns failure.]

***********************************************************************/
int Prt_Error( char * pError, unsigned nError, const char * pFormat, ... )
{
    va_list Args;
    va_start(Args, pFormat);
    if ( pError && nError )
        vsnprintf(pError, nError, pFormat, Args);
    va_end(Args);
    return 0;
}

/**Function*************************************************************

  Synopsis    [Allocates checked zero-filled storage, including empty arrays.]

***********************************************************************/
void * Prt_Alloc( size_t nItems, size_t ItemSize )
{
    if ( !ItemSize || nItems > ((size_t)-1) / ItemSize )
        return NULL;
    return calloc(nItems ? nItems : 1, ItemSize);
}

/**Function*************************************************************

  Synopsis    [Compares object IDs without unsigned subtraction overflow.]

***********************************************************************/
static int Prt_CompareId( const void * pA, const void * pB )
{
    unsigned A = *(const unsigned *)pA, B = *(const unsigned *)pB;
    return A < B ? -1 : A > B;
}

/**Function*************************************************************

  Synopsis    [Releases graph storage, accepting NULL and partial graphs.]

***********************************************************************/
void Prt_GraphFree( Prt_Graph_t * p )
{
    if ( !p ) return;
    free(p->pInStart); free(p->pInNets);
    free(p->pOutStart); free(p->pOutNets);
    free(p->pDriver); free(p->pSinkStart); free(p->pSinks);
    free(p->pObjWeight); free(p->pNetWeight);
    free(p);
}

/**Function*************************************************************

  Synopsis    [Copies, canonicalizes, and cross-indexes a weighted hypergraph.]

***********************************************************************/
int Prt_GraphCreate( unsigned nObjs, unsigned nNets,
    const unsigned * pDriver, const unsigned * pSinkStart, const unsigned * pSinks,
    const double * pObjWeight, const double * pNetWeight,
    Prt_Graph_t ** ppGraph, char * pError, unsigned nError )
{
    Prt_Graph_t * p = NULL;
    unsigned * pInNext = NULL, * pOutNext = NULL;
    unsigned e, v, i, j, nRaw, nUsed = 0, nOut = 0;
    double Weight, Sum = 0;
    if ( !ppGraph ) return Prt_Error(pError,nError,"Missing graph result.");
    *ppGraph = NULL;
    if ( nObjs == PRT_NONE || nNets == PRT_NONE ||
        (nNets && (!pDriver || !pSinkStart)) || (pSinkStart && pSinkStart[0]) )
        return Prt_Error(pError,nError,"Invalid graph dimensions or net spans.");
    nRaw = nNets ? pSinkStart[nNets] : 0;
    if ( nRaw && !pSinks ) return Prt_Error(pError,nError,"Missing net consumers.");
    for ( e = 0; e < nNets; ++e )
    {
        if ( pSinkStart[e] > pSinkStart[e+1] ||
            (pDriver[e] != PRT_NONE && pDriver[e] >= nObjs) )
            return Prt_Error(pError,nError,"Invalid net %u driver or span.",e);
        Weight = pNetWeight ? pNetWeight[e] : 1;
        if ( !(Weight >= 0 && Weight <= DBL_MAX) || Weight > DBL_MAX-Sum )
            return Prt_Error(pError,nError,"Invalid or overflowing net weight at %u.",e);
        Sum += Weight;
    }
    for ( i = 0; i < nRaw; ++i )
        if ( pSinks[i] >= nObjs )
            return Prt_Error(pError,nError,"Invalid consumer object %u.",pSinks[i]);
    Sum = 0;
    for ( v = 0; v < nObjs; ++v )
    {
        Weight = pObjWeight ? pObjWeight[v] : 1;
        if ( !(Weight >= 0 && Weight <= DBL_MAX) || Weight > DBL_MAX-Sum )
            return Prt_Error(pError,nError,"Invalid or overflowing object weight at %u.",v);
        Sum += Weight;
    }
    p = (Prt_Graph_t *)Prt_Alloc(1,sizeof(Prt_Graph_t));
    if ( !p ) goto memory;
    p->nObjs = nObjs; p->nNets = nNets;
    p->pInStart = (unsigned *)Prt_Alloc((size_t)nObjs+1,sizeof(unsigned));
    p->pOutStart = (unsigned *)Prt_Alloc((size_t)nObjs+1,sizeof(unsigned));
    p->pSinkStart = (unsigned *)Prt_Alloc((size_t)nNets+1,sizeof(unsigned));
    p->pDriver = (unsigned *)Prt_Alloc(nNets,sizeof(unsigned));
    p->pSinks = (unsigned *)Prt_Alloc(nRaw,sizeof(unsigned));
    p->pObjWeight = (double *)Prt_Alloc(nObjs,sizeof(double));
    p->pNetWeight = (double *)Prt_Alloc(nNets,sizeof(double));
    if ( !p->pInStart || !p->pOutStart || !p->pSinkStart || !p->pDriver ||
         !p->pSinks || !p->pObjWeight || !p->pNetWeight ) goto memory;
    if ( nRaw ) memcpy(p->pSinks,pSinks,(size_t)nRaw*sizeof(unsigned));
    for ( e = 0; e < nNets; ++e )
    {
        p->pDriver[e] = pDriver[e];
        p->pNetWeight[e] = pNetWeight ? pNetWeight[e] : 1;
        p->pSinkStart[e] = nUsed;
        i = pSinkStart[e]; j = pSinkStart[e+1];
        if ( j-i > 1 ) qsort(p->pSinks+i,j-i,sizeof(unsigned),Prt_CompareId);
        for ( ; i < j; ++i )
        {
            v = p->pSinks[i];
            if ( v == pDriver[e] || (nUsed > p->pSinkStart[e] && p->pSinks[nUsed-1] == v) )
                continue;
            p->pSinks[nUsed++] = v;
            ++p->pInStart[v+1];
        }
        if ( pDriver[e] != PRT_NONE ) ++p->pOutStart[pDriver[e]+1];
    }
    p->pSinkStart[nNets] = p->nPins = nUsed;
    for ( v = 0; v < nObjs; ++v )
    {
        p->pObjWeight[v] = pObjWeight ? pObjWeight[v] : 1;
        p->pInStart[v+1] += p->pInStart[v];
        p->pOutStart[v+1] += p->pOutStart[v];
    }
    nOut = p->pOutStart[nObjs];
    p->pInNets = (unsigned *)Prt_Alloc(nUsed,sizeof(unsigned));
    p->pOutNets = (unsigned *)Prt_Alloc(nOut,sizeof(unsigned));
    pInNext = (unsigned *)Prt_Alloc(nObjs,sizeof(unsigned));
    pOutNext = (unsigned *)Prt_Alloc(nObjs,sizeof(unsigned));
    if ( !p->pInNets || !p->pOutNets || !pInNext || !pOutNext ) goto memory;
    for ( e = 0; e < nNets; ++e )
    {
        v = pDriver[e];
        if ( v != PRT_NONE ) p->pOutNets[p->pOutStart[v]+pOutNext[v]++] = e;
        for ( i = p->pSinkStart[e]; i < p->pSinkStart[e+1]; ++i )
        {
            v = p->pSinks[i];
            p->pInNets[p->pInStart[v]+pInNext[v]++] = e;
        }
    }
    free(pInNext); free(pOutNext);
    *ppGraph = p;
    if ( pError && nError ) pError[0] = 0;
    return 1;
memory:
    free(pInNext); free(pOutNext); Prt_GraphFree(p);
    return Prt_Error(pError,nError,"Graph allocation failed.");
}

/**Function*************************************************************

  Synopsis    [Checks all spans, weights, and the two reverse incidence arrays.]

***********************************************************************/
int Prt_GraphCheck( const Prt_Graph_t * p, char * pError, unsigned nError )
{
    unsigned * pIn = NULL, * pOut = NULL;
    unsigned v, e, i, Index;
    double ObjSum = 0, NetSum = 0;
    int Result = 0;
    if ( !p || p->nObjs == PRT_NONE || p->nNets == PRT_NONE || !p->pInStart ||
        !p->pOutStart || !p->pSinkStart || !p->pDriver || !p->pSinks ||
        !p->pInNets || !p->pOutNets || !p->pObjWeight || !p->pNetWeight )
        return Prt_Error(pError,nError,"Missing graph arrays.");
    if ( p->pInStart[0] || p->pOutStart[0] || p->pSinkStart[0] ||
        p->pInStart[p->nObjs] != p->nPins || p->pSinkStart[p->nNets] != p->nPins ||
        p->pOutStart[p->nObjs] > p->nNets )
        return Prt_Error(pError,nError,"Inconsistent graph endpoints.");
    for ( v = 0; v < p->nObjs; ++v )
    {
        if ( p->pInStart[v] > p->pInStart[v+1] || p->pInStart[v+1] > p->nPins ||
            p->pOutStart[v] > p->pOutStart[v+1] || p->pOutStart[v+1] > p->nNets ||
            !(p->pObjWeight[v] >= 0 && p->pObjWeight[v] <= DBL_MAX-ObjSum) )
            return Prt_Error(pError,nError,"Invalid object %u span or weight.",v);
        ObjSum += p->pObjWeight[v];
    }
    pIn = (unsigned *)Prt_Alloc(p->nObjs,sizeof(unsigned));
    pOut = (unsigned *)Prt_Alloc(p->nObjs,sizeof(unsigned));
    if ( !pIn || !pOut ) { Prt_Error(pError,nError,"Graph check allocation failed."); goto cleanup; }
    for ( e = 0; e < p->nNets; ++e )
    {
        v = p->pDriver[e];
        if ( p->pSinkStart[e] > p->pSinkStart[e+1] || p->pSinkStart[e+1] > p->nPins ||
            (v != PRT_NONE && v >= p->nObjs) ||
            !(p->pNetWeight[e] >= 0 && p->pNetWeight[e] <= DBL_MAX-NetSum) ) goto invalid;
        NetSum += p->pNetWeight[e];
        if ( v != PRT_NONE )
        {
            Index = p->pOutStart[v]+pOut[v]++;
            if ( Index >= p->pOutStart[v+1] || p->pOutNets[Index] != e ) goto invalid;
        }
        for ( i = p->pSinkStart[e]; i < p->pSinkStart[e+1]; ++i )
        {
            v = p->pSinks[i];
            if ( v >= p->nObjs || v == p->pDriver[e] ||
                (i > p->pSinkStart[e] && v <= p->pSinks[i-1]) ) goto invalid;
            Index = p->pInStart[v]+pIn[v]++;
            if ( Index >= p->pInStart[v+1] || p->pInNets[Index] != e ) goto invalid;
        }
    }
    for ( v = 0; v < p->nObjs; ++v )
        if ( pIn[v] != p->pInStart[v+1]-p->pInStart[v] ||
             pOut[v] != p->pOutStart[v+1]-p->pOutStart[v] ) goto invalid;
    Result = 1;
    if ( pError && nError ) pError[0] = 0;
    goto cleanup;
invalid:
    Prt_Error(pError,nError,"Inconsistent net incidences or weights.");
cleanup:
    free(pIn); free(pOut);
    return Result;
}

/**Function*************************************************************

  Synopsis    [Computes a deterministic topological order without recursion.]

***********************************************************************/
int Prt_GraphTopoChecked( const Prt_Graph_t * p, unsigned * pOrder, char * pError, unsigned nError )
{
    unsigned * pCounts = NULL, * pQueue = NULL;
    unsigned v, e, i, j, nRead = 0, nWrite = 0;
    int Result = 0;
    if ( p->nObjs && !pOrder ) return Prt_Error(pError,nError,"Missing topological order output.");
    pCounts = (unsigned *)Prt_Alloc(p->nObjs,sizeof(unsigned));
    pQueue = (unsigned *)Prt_Alloc(p->nObjs,sizeof(unsigned));
    if ( !pCounts || !pQueue ) { Prt_Error(pError,nError,"Topological order allocation failed."); goto cleanup; }
    for ( v = 0; v < p->nObjs; ++v )
    {
        for ( i = p->pInStart[v]; i < p->pInStart[v+1]; ++i )
            pCounts[v] += p->pDriver[p->pInNets[i]] != PRT_NONE;
        if ( !pCounts[v] ) pQueue[nWrite++] = v;
    }
    while ( nRead < nWrite )
    {
        v = pQueue[nRead++];
        for ( i = p->pOutStart[v]; i < p->pOutStart[v+1]; ++i )
        {
            e = p->pOutNets[i];
            for ( j = p->pSinkStart[e]; j < p->pSinkStart[e+1]; ++j )
                if ( --pCounts[p->pSinks[j]] == 0 ) pQueue[nWrite++] = p->pSinks[j];
        }
    }
    if ( nWrite != p->nObjs ) { Prt_Error(pError,nError,"Directed dependency graph contains a cycle."); goto cleanup; }
    if ( p->nObjs ) memcpy(pOrder,pQueue,(size_t)p->nObjs*sizeof(unsigned));
    Result = 1;
cleanup:
    free(pCounts); free(pQueue);
    return Result;
}

/**Function*************************************************************

  Synopsis    [Validates an external graph before computing its order.]

***********************************************************************/
int Prt_GraphTopo( const Prt_Graph_t * p, unsigned * pOrder, char * pError, unsigned nError )
{
    return Prt_GraphCheck(p,pError,nError) && Prt_GraphTopoChecked(p,pOrder,pError,nError);
}

/**Function*************************************************************

  Synopsis    [Contracts dense object groups while preserving signal net IDs.]

***********************************************************************/
int Prt_GraphContract( const Prt_Graph_t * p, unsigned nObjs,
    const unsigned * pMap, Prt_Graph_t ** ppGraph, char * pError, unsigned nError )
{
    unsigned * pDrivers = NULL, * pSinks = NULL, * pUsed = NULL;
    double * pWeights = NULL;
    unsigned v, e, i;
    int Result = 0;
    if ( !ppGraph ) return Prt_Error(pError,nError,"Missing contracted graph output.");
    *ppGraph = NULL;
    if ( !Prt_GraphCheck(p,pError,nError) ) return 0;
    if ( nObjs > p->nObjs || (p->nObjs && !pMap) )
        return Prt_Error(pError,nError,"Invalid contraction dimensions.");
    pDrivers = (unsigned *)Prt_Alloc(p->nNets,sizeof(unsigned));
    pSinks = (unsigned *)Prt_Alloc(p->nPins,sizeof(unsigned));
    pUsed = (unsigned *)Prt_Alloc(nObjs,sizeof(unsigned));
    pWeights = (double *)Prt_Alloc(nObjs,sizeof(double));
    if ( !pDrivers || !pSinks || !pUsed || !pWeights )
    { Prt_Error(pError,nError,"Contraction allocation failed."); goto cleanup; }
    for ( v = 0; v < p->nObjs; ++v )
    {
        if ( pMap[v] >= nObjs ) { Prt_Error(pError,nError,"Invalid group for object %u.",v); goto cleanup; }
        pWeights[pMap[v]] += p->pObjWeight[v];
        pUsed[pMap[v]] = 1;
    }
    for ( v = 0; v < nObjs; ++v )
        if ( !pUsed[v] ) { Prt_Error(pError,nError,"Contraction has empty group %u.",v); goto cleanup; }
    for ( e = 0; e < p->nNets; ++e )
        pDrivers[e] = p->pDriver[e] == PRT_NONE ? PRT_NONE : pMap[p->pDriver[e]];
    for ( i = 0; i < p->nPins; ++i ) pSinks[i] = pMap[p->pSinks[i]];
    Result = Prt_GraphCreate(nObjs,p->nNets,pDrivers,p->pSinkStart,pSinks,
        pWeights,p->pNetWeight,ppGraph,pError,nError);
cleanup:
    free(pDrivers); free(pSinks); free(pUsed); free(pWeights);
    return Result;
}

/**Function*************************************************************

  Synopsis    [Computes canonical SCC labels using two iterative traversals.]

***********************************************************************/
int Prt_GraphScc( const Prt_Graph_t * p, unsigned * pComponents,
    unsigned * pnComponents, char * pError, unsigned nError )
{
    unsigned * pStack = NULL, * pOrder = NULL, * pOut = NULL, * pSink = NULL;
    unsigned * pLabels = NULL, * pRename = NULL;
    unsigned char * pSeen = NULL;
    unsigned v, w, e, i, nStack = 0, nOrder = 0, nComps = 0, nDense = 0;
    int Result = 0;
    if ( !Prt_GraphCheck(p,pError,nError) ) return 0;
    if ( !pnComponents || (p->nObjs && !pComponents) )
        return Prt_Error(pError,nError,"Missing SCC output.");
    pStack = (unsigned *)Prt_Alloc(p->nObjs,sizeof(unsigned));
    pOrder = (unsigned *)Prt_Alloc(p->nObjs,sizeof(unsigned));
    pOut = (unsigned *)Prt_Alloc(p->nObjs,sizeof(unsigned));
    pSink = (unsigned *)Prt_Alloc(p->nObjs,sizeof(unsigned));
    pLabels = (unsigned *)Prt_Alloc(p->nObjs,sizeof(unsigned));
    pRename = (unsigned *)Prt_Alloc(p->nObjs,sizeof(unsigned));
    pSeen = (unsigned char *)Prt_Alloc(p->nObjs,sizeof(unsigned char));
    if ( !pStack || !pOrder || !pOut || !pSink || !pLabels || !pRename || !pSeen )
    { Prt_Error(pError,nError,"SCC allocation failed."); goto cleanup; }
    for ( v = 0; v < p->nObjs; ++v )
    {
        pOut[v] = p->pOutStart[v];
        pSink[v] = pOut[v] < p->pOutStart[v+1] ? p->pSinkStart[p->pOutNets[pOut[v]]] : 0;
        pLabels[v] = pRename[v] = PRT_NONE;
    }
    for ( i = 0; i < p->nObjs; ++i )
    {
        if ( pSeen[i] ) continue;
        pSeen[i] = 1; pStack[nStack++] = i;
        while ( nStack )
        {
            v = pStack[nStack-1];
            while ( pOut[v] < p->pOutStart[v+1] )
            {
                e = p->pOutNets[pOut[v]];
                if ( pSink[v] < p->pSinkStart[e+1] ) break;
                if ( ++pOut[v] < p->pOutStart[v+1] )
                    pSink[v] = p->pSinkStart[p->pOutNets[pOut[v]]];
            }
            if ( pOut[v] == p->pOutStart[v+1] )
            { pOrder[nOrder++] = v; --nStack; continue; }
            w = p->pSinks[pSink[v]++];
            if ( !pSeen[w] ) { pSeen[w] = 1; pStack[nStack++] = w; }
        }
    }
    while ( nOrder )
    {
        v = pOrder[--nOrder];
        if ( pLabels[v] != PRT_NONE ) continue;
        pLabels[v] = nComps; pStack[nStack++] = v;
        while ( nStack )
        {
            v = pStack[--nStack];
            for ( i = p->pInStart[v]; i < p->pInStart[v+1]; ++i )
            {
                w = p->pDriver[p->pInNets[i]];
                if ( w == PRT_NONE || pLabels[w] != PRT_NONE ) continue;
                pLabels[w] = nComps; pStack[nStack++] = w;
            }
        }
        ++nComps;
    }
    for ( v = 0; v < p->nObjs; ++v )
    {
        if ( pRename[pLabels[v]] == PRT_NONE ) pRename[pLabels[v]] = nDense++;
        pComponents[v] = pRename[pLabels[v]];
    }
    *pnComponents = nDense;
    Result = 1;
cleanup:
    free(pStack); free(pOrder); free(pOut); free(pSink);
    free(pLabels); free(pRename); free(pSeen);
    return Result;
}

ABC_NAMESPACE_IMPL_END
