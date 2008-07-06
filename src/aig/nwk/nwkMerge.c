/**CFile****************************************************************

  FileName    [nwkMerge.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [LUT merging algorithm.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: nwkMerge.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "nwk.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Marks the fanins of the node with the current trav ID.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nwk_ManMarkFanins_rec( Nwk_Obj_t * pLut, int nLevMin )
{
    Nwk_Obj_t * pNext;
    int i;
    if ( !Nwk_ObjIsNode(pLut) )
        return;
    if ( Nwk_ObjIsTravIdCurrent( pLut ) )
        return;
    Nwk_ObjSetTravIdCurrent( pLut );
    if ( Nwk_ObjLevel(pLut) < nLevMin )
        return;
    Nwk_ObjForEachFanin( pLut, pNext, i )
        Nwk_ManMarkFanins_rec( pNext, nLevMin );
}

/**Function*************************************************************

  Synopsis    [Marks the fanouts of the node with the current trav ID.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nwk_ManMarkFanouts_rec( Nwk_Obj_t * pLut, int nLevMax, int nFanMax )
{
    Nwk_Obj_t * pNext;
    int i;
    if ( !Nwk_ObjIsNode(pLut) )
        return;
    if ( Nwk_ObjIsTravIdCurrent( pLut ) )
        return;
    Nwk_ObjSetTravIdCurrent( pLut );
    if ( Nwk_ObjLevel(pLut) > nLevMax )
        return;
    if ( Nwk_ObjFanoutNum(pLut) > nFanMax )
        return;
    Nwk_ObjForEachFanout( pLut, pNext, i )
        Nwk_ManMarkFanouts_rec( pNext, nLevMax, nFanMax );
}

/**Function*************************************************************

  Synopsis    [Collects the circle of nodes around the given set.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nwk_ManCollectCircle( Vec_Ptr_t * vStart, Vec_Ptr_t * vNext, int nFanMax )
{
    Nwk_Obj_t * pObj, * pNext;
    int i, k;
    Vec_PtrClear( vNext );
    Vec_PtrForEachEntry( vStart, pObj, i )
    {
        Nwk_ObjForEachFanin( pObj, pNext, k )
        {
            if ( !Nwk_ObjIsNode(pNext) )
                continue;
            if ( Nwk_ObjIsTravIdCurrent( pNext ) )
                continue;
            Nwk_ObjSetTravIdCurrent( pNext );
            Vec_PtrPush( vNext, pNext );
        }
        Nwk_ObjForEachFanout( pObj, pNext, k )
        {
            if ( !Nwk_ObjIsNode(pNext) )
                continue;
            if ( Nwk_ObjIsTravIdCurrent( pNext ) )
                continue;
            Nwk_ObjSetTravIdCurrent( pNext );
            if ( Nwk_ObjFanoutNum(pNext) > nFanMax )
                continue;
            Vec_PtrPush( vNext, pNext );
        }
    }
}

/**Function*************************************************************

  Synopsis    [Collects the circle of nodes removes from the given one.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nwk_ManCollectNonOverlapCands( Nwk_Obj_t * pLut, Vec_Ptr_t * vStart, Vec_Ptr_t * vNext, Vec_Ptr_t * vCands, Nwk_LMPars_t * pPars )
{
    Vec_Ptr_t * vTemp;
    Nwk_Obj_t * pObj;
    int i, k;
    Vec_PtrClear( vCands );
    if ( pPars->nMaxSuppSize - Nwk_ObjFaninNum(pLut) <= 1 )
        return;

    // collect nodes removed by this distance
    assert( pPars->nMaxDistance > 0 );
    Vec_PtrClear( vStart );
    Vec_PtrPush( vStart, pLut );
    Nwk_ManIncrementTravId( pLut->pMan );
    Nwk_ObjSetTravIdCurrent( pLut );
    for ( i = 1; i < pPars->nMaxDistance; i++ )
    {
        Nwk_ManCollectCircle( vStart, vNext, pPars->nMaxFanout );
        vTemp = vStart;
        vStart = vNext;
        vNext = vTemp;
        // collect the nodes in vStart
        Vec_PtrForEachEntry( vStart, pObj, k )
            Vec_PtrPush( vCands, pObj );
    }

    // mark the TFI/TFO nodes
    Nwk_ManIncrementTravId( pLut->pMan );
    if ( pPars->fUseTfiTfo )
        Nwk_ObjSetTravIdCurrent( pLut );
    else
    {
        Nwk_ObjSetTravIdPrevious( pLut );
        Nwk_ManMarkFanins_rec( pLut, Nwk_ObjLevel(pLut) - pPars->nMaxDistance );
        Nwk_ObjSetTravIdPrevious( pLut );
        Nwk_ManMarkFanouts_rec( pLut, Nwk_ObjLevel(pLut) + pPars->nMaxDistance, pPars->nMaxFanout );
    }

    // collect nodes satisfying the following conditions:
    // - they are close enough in terms of distance
    // - they are not in the TFI/TFO of the LUT
    // - they have no more than the given number of fanins
    // - they have no more than the given diff in delay
    k = 0;
    Vec_PtrForEachEntry( vCands, pObj, i )
    {
        if ( Nwk_ObjIsTravIdCurrent(pObj) )
            continue;
        if ( Nwk_ObjFaninNum(pLut) + Nwk_ObjFaninNum(pObj) > pPars->nMaxSuppSize )
            continue;
        if ( Nwk_ObjLevel(pLut) - Nwk_ObjLevel(pObj) > pPars->nMaxLevelDiff || 
             Nwk_ObjLevel(pObj) - Nwk_ObjLevel(pLut) > pPars->nMaxLevelDiff )
             continue;
        Vec_PtrWriteEntry( vCands, k++, pObj );
    }
    Vec_PtrShrink( vCands, k );
}


/**Function*************************************************************

  Synopsis    [Count the total number of fanins.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Nwk_ManCountTotalFanins( Nwk_Obj_t * pLut, Nwk_Obj_t * pCand )
{
    Nwk_Obj_t * pFanin;
    int i, nCounter = Nwk_ObjFaninNum(pLut);
    Nwk_ObjForEachFanin( pCand, pFanin, i )
        nCounter += !pFanin->MarkC;
    return nCounter;
}

/**Function*************************************************************

  Synopsis    [Collects overlapping candidates.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nwl_ManCollectOverlapCands( Nwk_Obj_t * pLut, Vec_Ptr_t * vCands, Nwk_LMPars_t * pPars )
{
    Nwk_Obj_t * pFanin, * pObj;
    int i, k;
    // mark fanins of pLut
    Nwk_ObjForEachFanin( pLut, pFanin, i )
        pFanin->MarkC = 1;
    // collect the matching fanouts of each fanin of the node
    Vec_PtrClear( vCands );
    Nwk_ManIncrementTravId( pLut->pMan );
    Nwk_ObjSetTravIdCurrent( pLut );
    Nwk_ObjForEachFanin( pLut, pFanin, i )
    {
        if ( !Nwk_ObjIsNode(pFanin) )
            continue;
        if ( Nwk_ObjFanoutNum(pFanin) > pPars->nMaxFanout )
            continue;
        Nwk_ObjForEachFanout( pFanin, pObj, k )
        {
            if ( !Nwk_ObjIsNode(pObj) )
                continue;
            if ( Nwk_ObjIsTravIdCurrent( pObj ) )
                continue;
            Nwk_ObjSetTravIdCurrent( pObj );
            // check the difference in delay
            if ( Nwk_ObjLevel(pLut) - Nwk_ObjLevel(pObj) > pPars->nMaxLevelDiff || 
                 Nwk_ObjLevel(pObj) - Nwk_ObjLevel(pLut) > pPars->nMaxLevelDiff )
                 continue;
            // check the total number of fanins of the node
            if ( Nwk_ManCountTotalFanins(pLut, pObj) > pPars->nMaxSuppSize )
                continue;
            Vec_PtrPush( vCands, pObj );
        }
    }
    // unmark fanins of pLut
    Nwk_ObjForEachFanin( pLut, pFanin, i )
        pFanin->MarkC = 0;
}



#define MAX_LIST  16

// edge of the graph
typedef struct Nwk_Edg_t_  Nwk_Edg_t;
struct Nwk_Edg_t_
{
    int             iNode1;      // the first node
    int             iNode2;      // the second node
    Nwk_Edg_t *     pNext;       // the next edge
};

// vertex of the graph
typedef struct Nwk_Vrt_t_  Nwk_Vrt_t;
struct Nwk_Vrt_t_
{
    int             Id;          // the vertex number
    int             iPrev;       // the previous vertex in the list
    int             iNext;       // the next vertex in the list
    int             nEdges;      // the number of edges
    int             pEdges[0];   // the array of edges
};

// the connectivity graph
typedef struct Nwk_Grf_t_  Nwk_Grf_t;
struct Nwk_Grf_t_
{
    // preliminary graph representation
    int             nObjs;       // the number of objects
    int             nVertsPre;   // the upper bound on the number of vertices
    int             nEdgeHash;   // approximate number of edges
    Nwk_Edg_t **    pEdgeHash;   // hash table for edges
    Aig_MmFixed_t * pMemEdges;   // memory for edges
    // graph representation
    int             nEdges;      // the number of edges
    int             nVerts;      // the number of vertices
    Nwk_Vrt_t **    pVerts;      // the array of vertices
    Aig_MmFlex_t *  pMemVerts;   // memory for vertices
    // intermediate data
    int             pLists1[MAX_LIST+1];
    int             pLists2[MAX_LIST+1];
    // the results of matching
    Vec_Int_t *     vPairs;
    // mappings graph into LUTs and back
    int *           pMapLut2Id;
    int *           pMapId2Lut;
};

/**Function*************************************************************

  Synopsis    [Deallocates the graph.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nwk_ManGraphFree( Nwk_Grf_t * p )
{
    if ( p->vPairs )    Vec_IntFree( p->vPairs );
    if ( p->pMemEdges ) Aig_MmFixedStop( p->pMemEdges, 0 );
    if ( p->pMemVerts ) Aig_MmFlexStop( p->pMemVerts, 0 );
    FREE( p->pEdgeHash );
    FREE( p->pVerts );
    FREE( p->pMapLut2Id );
    FREE( p->pMapId2Lut );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Allocates the graph.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Nwk_Grf_t * Nwk_ManGraphAlloc( int nObjs, int nVertsPre )
{
    Nwk_Grf_t * p;
    p = ALLOC( Nwk_Grf_t, 1 );
    memset( p, 0, sizeof(Nwk_Grf_t) );
    p->nObjs      = nObjs;
    p->nVertsPre  = nVertsPre;
    p->nEdgeHash  = Aig_PrimeCudd(10 * nVertsPre);
    p->pEdgeHash  = CALLOC( Nwk_Edg_t *, p->nEdgeHash );
    p->pMemEdges  = Aig_MmFixedStart( sizeof(Nwk_Edg_t), p->nEdgeHash );
    p->pMapLut2Id = ALLOC( int, nObjs );
    p->pMapId2Lut = ALLOC( int, nVertsPre );
    p->vPairs     = Vec_IntAlloc( 1000 );
    memset( p->pMapLut2Id, 0xff, sizeof(int) * nObjs );
    memset( p->pMapId2Lut, 0xff, sizeof(int) * nVertsPre );
    return p;
}

/**Function*************************************************************

  Synopsis    [Finds or adds the edge to the graph.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Nwk_ManGraphSetMapping( Nwk_Grf_t * p, int iLut )
{
    p->nVerts++;
    p->pMapId2Lut[p->nVerts] = iLut;
    p->pMapLut2Id[iLut] = p->nVerts;
}

/**Function*************************************************************

  Synopsis    [Finds or adds the edge to the graph.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Nwk_ManGraphHashEdge( Nwk_Grf_t * p, int iLut1, int iLut2 )
{
    Nwk_Edg_t * pEntry;
    int Key;
    if ( iLut1 == iLut2 )
        return;
    if ( iLut1 > iLut2 )
    {
        Key = iLut1;
        iLut1 = iLut2;
        iLut2 = Key;
    }
    assert( iLut1 < iLut2 );
    Key = (741457 * iLut1 + 4256249 * iLut2) % p->nEdgeHash;
    for ( pEntry = p->pEdgeHash[Key]; pEntry; pEntry = pEntry->pNext )
        if ( pEntry->iNode1 == iLut1 && pEntry->iNode2 == iLut2 )
            return;
    pEntry = (Nwk_Edg_t *)Aig_MmFixedEntryFetch( p->pMemEdges );
    pEntry->iNode1 = iLut1;
    pEntry->iNode2 = iLut2;
    pEntry->pNext = p->pEdgeHash[Key];
    p->pEdgeHash[Key] = pEntry;
    p->nEdges++;
}

/**Function*************************************************************

  Synopsis    [Prepares the graph for solving the problem.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Nwk_ManGraphListAdd( Nwk_Grf_t * p, int * pList, Nwk_Vrt_t * pVertex )
{
    if ( *pList )
    {
        Nwk_Vrt_t * pHead;
        pHead = p->pVerts[*pList];
        pVertex->iPrev = 0;
        pVertex->iNext = pHead->Id;
        pHead->iPrev = pVertex->Id;
    }
    *pList = pVertex->Id;
}

/**Function*************************************************************

  Synopsis    [Prepares the graph for solving the problem.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Nwk_ManGraphListDelete( Nwk_Grf_t * p, int * pList, Nwk_Vrt_t * pVertex )
{
    assert( *pList );
    if ( pVertex->iPrev )
        p->pVerts[pVertex->iPrev]->iNext = pVertex->iNext;
    if ( pVertex->iNext )
        p->pVerts[pVertex->iNext]->iNext = pVertex->iPrev;
    if ( *pList == pVertex->Id )
        *pList = pVertex->iNext;
    pVertex->iPrev = pVertex->iNext = 0;
}

/**Function*************************************************************

  Synopsis    [Inserts the edge into one of the linked lists.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Nwk_ManGraphListInsert( Nwk_Grf_t * p, Nwk_Vrt_t * pVertex )
{
    Nwk_Vrt_t * pNext;
    assert( pVertex->nEdges > 0 );
    if ( pVertex->nEdges == 1 )
    {
        pNext = p->pVerts[ pVertex->pEdges[0] ];
        if ( pNext->nEdges >= MAX_LIST )
            Nwk_ManGraphListAdd( p, p->pLists1 + MAX_LIST, pVertex );
        else
            Nwk_ManGraphListAdd( p, p->pLists1 + pNext->nEdges, pVertex );
    }
    else
    {
        if ( pVertex->nEdges >= MAX_LIST )
            Nwk_ManGraphListAdd( p, p->pLists1 + MAX_LIST, pVertex );
        else
            Nwk_ManGraphListAdd( p, p->pLists1 + pVertex->nEdges, pVertex );
    }
}

/**Function*************************************************************

  Synopsis    [Extracts the edge from one of the linked lists.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Nwk_ManGraphListExtract( Nwk_Grf_t * p, Nwk_Vrt_t * pVertex )
{
    Nwk_Vrt_t * pNext;
    assert( pVertex->nEdges > 0 );
    if ( pVertex->nEdges == 1 )
    {
        pNext = p->pVerts[ pVertex->pEdges[0] ];
        if ( pNext->nEdges >= MAX_LIST )
            Nwk_ManGraphListDelete( p, p->pLists1 + MAX_LIST, pVertex );
        else
            Nwk_ManGraphListDelete( p, p->pLists1 + pNext->nEdges, pVertex );
    }
    else
    {
        if ( pVertex->nEdges >= MAX_LIST )
            Nwk_ManGraphListDelete( p, p->pLists1 + MAX_LIST, pVertex );
        else
            Nwk_ManGraphListDelete( p, p->pLists1 + pVertex->nEdges, pVertex );
    }
}

/**Function*************************************************************

  Synopsis    [Prepares the graph for solving the problem.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nwk_ManGraphPrepare( Nwk_Grf_t * p )
{
    Nwk_Edg_t * pEntry;
    Nwk_Vrt_t * pVertex;
    int * pnEdges, Key, nBytes, i;
    // count the edges
    pnEdges = CALLOC( int, p->nVerts );
    for ( Key = 0; Key < p->nEdgeHash; Key++ )
        for ( pEntry = p->pEdgeHash[Key]; pEntry; pEntry = pEntry->pNext )
        {
            // translate into vertices
            assert( pEntry->iNode1 < p->nObjs );
            assert( pEntry->iNode2 < p->nObjs );
            pEntry->iNode1 = p->pMapLut2Id[pEntry->iNode1];
            pEntry->iNode2 = p->pMapLut2Id[pEntry->iNode2];
            // count the edges
            assert( pEntry->iNode1 < p->nVerts );
            assert( pEntry->iNode2 < p->nVerts );
            pnEdges[pEntry->iNode1]++;
            pnEdges[pEntry->iNode2]++;
        }
    // allocate the real graph
    p->pMemVerts  = Aig_MmFlexStart();
    p->pVerts = ALLOC( Nwk_Vrt_t *, p->nVerts + 1 );
    p->pVerts[0] = NULL;
    for ( i = 1; i <= p->nVerts; i++ )
    {
        assert( pnEdges[i] > 0 );
        nBytes = sizeof(Nwk_Vrt_t) + sizeof(int) * pnEdges[i];
        p->pVerts[i] = (Nwk_Vrt_t *)Aig_MmFlexEntryFetch( p->pMemVerts, nBytes );
        memset( p->pVerts[i], 0, nBytes );
        p->pVerts[i]->Id = i;
    }
    // add edges to the real graph
    for ( Key = 0; Key < p->nEdgeHash; Key++ )
        for ( pEntry = p->pEdgeHash[Key]; pEntry; pEntry = pEntry->pNext )
        {
            pVertex = p->pVerts[pEntry->iNode1];
            pVertex->pEdges[ pVertex->nEdges++ ] = pEntry->iNode2;
            pVertex = p->pVerts[pEntry->iNode2];
            pVertex->pEdges[ pVertex->nEdges++ ] = pEntry->iNode1;
        }
    // put vertices into the data structure
    for ( i = 1; i <= p->nVerts; i++ )
    {
        assert( p->pVerts[i]->nEdges == pnEdges[i] );
        Nwk_ManGraphListInsert( p, p->pVerts[i] );
    }
    // clean up
    Aig_MmFixedStop( p->pMemEdges, 0 ); p->pMemEdges = NULL;
    FREE( p->pEdgeHash );
    p->nEdgeHash = 0;
    free( pnEdges );
}

/**Function*************************************************************

  Synopsis    [Updates the problem after pulling out one edge.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nwk_ManGraphUpdate( Nwk_Grf_t * p, Nwk_Vrt_t * pVertex, Nwk_Vrt_t * pNext )
{
    Nwk_Vrt_t * pChanged;
    int i, k;
    // update neibors of pVertex
    for ( i = 0; i < pVertex->nEdges; i++ )
    {
        pChanged = p->pVerts[ pVertex->pEdges[i] ];
        Nwk_ManGraphListExtract( p, pChanged );
        for ( k = 0; k < pChanged->nEdges; k++ )
            if ( pChanged->pEdges[k] == pVertex->Id )
                break;
        assert( k < pChanged->nEdges );
        pChanged->nEdges--;
        for ( ; k < pChanged->nEdges; k++ )
            pChanged->pEdges[k] = pChanged->pEdges[k+1];
        if ( pChanged->nEdges > 0 )
            Nwk_ManGraphListInsert( p, pChanged );
    }
    // update neibors of pNext
    for ( i = 0; i < pNext->nEdges; i++ )
    {
        pChanged = p->pVerts[ pNext->pEdges[i] ];
        Nwk_ManGraphListExtract( p, pChanged );
        for ( k = 0; k < pChanged->nEdges; k++ )
            if ( pChanged->pEdges[k] == pNext->Id )
                break;
        assert( k < pChanged->nEdges );
        pChanged->nEdges--;
        for ( ; k < pChanged->nEdges; k++ )
            pChanged->pEdges[k] = pChanged->pEdges[k+1];
        if ( pChanged->nEdges > 0 )
            Nwk_ManGraphListInsert( p, pChanged );
    }
    // add to the result
    if ( pVertex->Id < pNext->Id )
    {
        Vec_IntPush( p->vPairs, p->pMapId2Lut[pVertex->Id] ); 
        Vec_IntPush( p->vPairs, p->pMapId2Lut[pNext->Id] ); 
    }
    else
    {
        Vec_IntPush( p->vPairs, p->pMapId2Lut[pNext->Id] ); 
        Vec_IntPush( p->vPairs, p->pMapId2Lut[pVertex->Id] ); 
    }
}

/**Function*************************************************************

  Synopsis    [Solves the problem.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nwk_ManGraphSolve( Nwk_Grf_t * p )
{
    Nwk_Vrt_t * pVertex, * pNext;
    int i, j;
    while ( 1 )
    {
        // find the next vertext to extract
        for ( i = 1; i <= MAX_LIST; i++ )
            if ( p->pLists1[i] )
            {
                pVertex = p->pVerts[ p->pLists1[i] ];
                assert( pVertex->nEdges == 1 );
                pNext = p->pVerts[ pVertex->pEdges[0] ];
                // update the data-structures
                Nwk_ManGraphUpdate( p, pVertex, pNext );
                break;
            }
        // find the next vertext to extract
        for ( j = 2; j <= MAX_LIST; j++ )
            if ( p->pLists2[j] )
            {
                pVertex = p->pVerts[ p->pLists2[j] ];
                assert( pVertex->nEdges == j || j == MAX_LIST );
                // update the data-structures
                Nwk_ManGraphUpdate( p, pVertex, pNext );
                break;
            }
        if ( i == MAX_LIST + 1 && j == MAX_LIST + 1 )
            break;
    }
}


/**Function*************************************************************

  Synopsis    [Performs LUT merging with parameters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Nwk_ManLutMerge( Nwk_Man_t * pNtk, Nwk_LMPars_t * pPars )
{
    Nwk_Grf_t * p;
    Vec_Int_t * vResult;
    Vec_Ptr_t * vStart, * vNext, * vCands1, * vCands2;
    Nwk_Obj_t * pLut, * pCand;
    int i, k, nVertsPre;
    // count the number of vertices
    nVertsPre = 0;
    Nwk_ManForEachNode( pNtk, pLut, i )
        nVertsPre += (int)(Nwk_ObjFaninNum(pLut) <= pPars->nMaxLutSize);
    p = Nwk_ManGraphAlloc( Nwk_ManObjNumMax(pNtk), nVertsPre );
    // create graph
    vStart  = Vec_PtrAlloc( 1000 );
    vNext   = Vec_PtrAlloc( 1000 );
    vCands1 = Vec_PtrAlloc( 1000 );
    vCands2 = Vec_PtrAlloc( 1000 );
    Nwk_ManForEachNode( pNtk, pLut, i )
    {
        if ( Nwk_ObjFaninNum(pLut) > pPars->nMaxLutSize )
            continue;
        Nwl_ManCollectOverlapCands( pLut, vCands1, pPars );
        Nwk_ManCollectNonOverlapCands( pLut, vStart, vNext, vCands2, pPars );
        if ( Vec_PtrSize(vCands1) == 0 && Vec_PtrSize(vCands2) == 0 )
            continue;
        // save candidates
        Nwk_ManGraphSetMapping( p, Nwk_ObjId(pLut) );
        Vec_PtrForEachEntry( vCands1, pCand, k )
            Nwk_ManGraphHashEdge( p, Nwk_ObjId(pLut), Nwk_ObjId(pCand) );
        Vec_PtrForEachEntry( vCands2, pCand, k )
            Nwk_ManGraphHashEdge( p, Nwk_ObjId(pLut), Nwk_ObjId(pCand) );
        // print statistics about this node
        printf( "Node %6d : Fanins = %d. Fanouts = %3d.  Cand1 = %3d. Cand2 = %3d.\n",
            Nwk_ObjId(pLut), Nwk_ObjFaninNum(pLut), Nwk_ObjFaninNum(pLut), 
            Vec_PtrSize(vCands1), Vec_PtrSize(vCands2) );
    }
    Vec_PtrFree( vStart );
    Vec_PtrFree( vNext );
    Vec_PtrFree( vCands1 );
    Vec_PtrFree( vCands2 );
    // solve the graph problem
    Nwk_ManGraphPrepare( p );
    Nwk_ManGraphSolve( p );
    vResult = p->vPairs; p->vPairs = NULL;
    Nwk_ManGraphFree( p );
    return vResult;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


