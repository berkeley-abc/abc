/**HFile****************************************************************

  FileName    [extraUtilFlow.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Extra utilities.]

  Synopsis    [Weighted minimum cuts using breadth-first augmenting paths.]

  Description [Each caller owns a residual graph and its work arrays.]

  Author      [Alan Mishchenko (original flow implementation in lmsOne.c)]

***********************************************************************/

#ifndef ABC__misc__extra__extraUtilFlow_h
#define ABC__misc__extra__extraUtilFlow_h

#include "misc/util/abc_global.h"
#include <limits.h>

ABC_NAMESPACE_HEADER_START

// Residual graph for area-weighted cuts of critical paths.
typedef struct Extra_FlowEdge_t_
{
    int To, Next;
    word Cap;
} Extra_FlowEdge_t;

typedef struct Extra_Flow_t_
{
    int * pHeads, * pParents, * pQueue;
    Extra_FlowEdge_t * pEdges;
    int nVertices, nEdges;
} Extra_Flow_t;

/**Function*************************************************************

  Synopsis    [Frees the residual graph and its work arrays.]

***********************************************************************/
static inline void Extra_FlowStop( Extra_Flow_t * p )
{
    ABC_FREE( p->pHeads );
    ABC_FREE( p->pParents );
    ABC_FREE( p->pQueue );
    ABC_FREE( p->pEdges );
}

/**Function*************************************************************

  Synopsis    [Allocates an indexed residual graph for at most nArcs directed arcs.]

***********************************************************************/
static inline int Extra_FlowStart( Extra_Flow_t * p, int nVertices, size_t nArcs )
{
    memset( p, 0, sizeof(*p) );
    if ( nVertices < 2 || (size_t)nVertices > (size_t)-1 / sizeof(int) ||
         nArcs > INT_MAX / 2 || nArcs > (size_t)-1 / (2 * sizeof(Extra_FlowEdge_t)) )
        return 0;
    p->nVertices = nVertices;
    p->pHeads = ABC_ALLOC( int, nVertices );
    p->pParents = ABC_ALLOC( int, nVertices );
    p->pQueue = ABC_ALLOC( int, nVertices );
    p->pEdges = ABC_CALLOC( Extra_FlowEdge_t, 2*nArcs );
    if ( !p->pHeads || !p->pParents || !p->pQueue || (nArcs && !p->pEdges) )
    {
        Extra_FlowStop( p );
        return 0;
    }
    memset( p->pHeads, 0xFF, (size_t)nVertices * sizeof(int) );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Adds a capacity edge and its reverse residual edge.]

***********************************************************************/
static inline void Extra_FlowAdd( Extra_Flow_t * p, int From, int To, word Cap )
{
    int e = p->nEdges;
    assert( From >= 0 && From < p->nVertices && To >= 0 && To < p->nVertices );
    p->pEdges[e].To = To;
    p->pEdges[e].Next = p->pHeads[From];
    p->pEdges[e].Cap = Cap;
    p->pEdges[e+1].To = From;
    p->pEdges[e+1].Next = p->pHeads[To];
    p->pEdges[e+1].Cap = 0;
    p->pHeads[From] = e;
    p->pHeads[To] = e+1;
    p->nEdges += 2;
}

/**Function*************************************************************

  Synopsis    [Augments flow until the sink is unreachable or the limit is met.]

  Description [For a flow below the limit, pParents marks exactly the
  vertices reachable from the source. Reaching the limit returns the
  accumulated flow. Reaching a nonzero wall-clock deadline returns Limit.]

***********************************************************************/
static inline word Extra_FlowSolveTimed( Extra_Flow_t * p, int Source, int Sink, word Limit, abctime Deadline )
{
    int From, To, e, Head, Tail;
    word Flow = 0, Delta;
    assert( Source >= 0 && Source < p->nVertices && Sink >= 0 && Sink < p->nVertices && Source != Sink );
    for ( ;; )
    {
        if ( Deadline && Abc_ClockHr() >= Deadline ) return Limit;
        memset( p->pParents, 0xFF, (size_t)p->nVertices * sizeof(int) );
        Head = 0;
        Tail = 1;
        p->pQueue[0] = Source;
        p->pParents[Source] = -2;
        while ( Head < Tail && p->pParents[Sink] == -1 )
        {
            if ( Deadline && !(Head & 1023) && Abc_ClockHr() >= Deadline ) return Limit;
            From = p->pQueue[Head++];
            for ( e = p->pHeads[From]; e >= 0; e = p->pEdges[e].Next )
            {
                assert( e < p->nEdges );
                To = p->pEdges[e].To;
                if ( !p->pEdges[e].Cap || p->pParents[To] != -1 )
                    continue;
                p->pParents[To] = e;
                p->pQueue[Tail++] = To;
            }
        }
        if ( p->pParents[Sink] == -1 )
            return Flow;
        Delta = Limit;
        for ( To = Sink; To != Source; To = p->pEdges[e^1].To )
        {
            e = p->pParents[To];
            assert( e >= 0 && e < p->nEdges );
            if ( Delta > p->pEdges[e].Cap )
                Delta = p->pEdges[e].Cap;
        }
        Flow += Delta;
        if ( Flow >= Limit )
            return Flow;
        for ( To = Sink; To != Source; To = p->pEdges[e^1].To )
        {
            e = p->pParents[To];
            assert( e >= 0 && e < p->nEdges );
            p->pEdges[e].Cap -= Delta;
            p->pEdges[e^1].Cap += Delta;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Marks vertices with a residual path to the sink after maximum flow.]

  Description [Their complement gives the other extreme minimum cut of the
  same flow. Reuses the BFS work arrays after the caller reads the source cut.]

***********************************************************************/
static inline void Extra_FlowMarkSinkSide( Extra_Flow_t * f, int sink )
{
    int head = 0, tail = 0, e, pred;
    memset( f->pParents, 0xFF, (size_t)f->nVertices * sizeof(int) );
    f->pParents[sink] = sink;
    f->pQueue[tail++] = sink;
    while ( head < tail )
    {
        int current = f->pQueue[head++];
        for ( e = f->pHeads[current]; e >= 0; e = f->pEdges[e].Next )
        {
            assert( e < f->nEdges );
            pred = f->pEdges[e].To;
            if ( !f->pEdges[e^1].Cap || f->pParents[pred] != -1 ) continue;
            f->pParents[pred] = e;
            f->pQueue[tail++] = pred;
        }
    }
}

ABC_NAMESPACE_HEADER_END

#endif
