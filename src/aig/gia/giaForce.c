/**CFile****************************************************************

  FileName    [gia.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: gia.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

/* 
    The code is based on the paper by F. A. Aloul, I. L. Markov, and K. A. Sakallah.
    "FORCE: A Fast and Easy-To-Implement Variable-Ordering Heuristic", Proc. GLSVLSI’03.
*/

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct For_Obj_t_ For_Obj_t;
struct For_Obj_t_
{
    int            iObj;
    float          lNode;
};

typedef struct For_Man_t_ For_Man_t;
struct For_Man_t_
{
    Gia_Man_t *    pGia;             // the original AIG manager
    int            nObjs;            // the number of objects
    int            iObj;             // the last added object
    int *          pPlace;           // coordinates of objects
    int *          piNext;           // array of next pointers
    int *          piRoot;           // array of root pointers
    float *        plEdge;           // edge coordinates
    For_Obj_t *    pNodes;           // the array of nodes
};

static inline int  Gia_ObjPlace( For_Man_t * p, Gia_Obj_t * pObj )        { return p->pPlace[Gia_ObjId(p->pGia, pObj)];         }
static inline int  Gia_ObjPlaceFanin0( For_Man_t * p, Gia_Obj_t * pObj )  { return p->pPlace[Gia_ObjFaninId0p(p->pGia, pObj)];  }
static inline int  Gia_ObjPlaceFanin1( For_Man_t * p, Gia_Obj_t * pObj )  { return p->pPlace[Gia_ObjFaninId1p(p->pGia, pObj)];  }

static inline int  Gia_ObjEdge( For_Man_t * p, Gia_Obj_t * pObj )         { return p->plEdge[Gia_ObjId(p->pGia, pObj)];         }
static inline int  Gia_ObjEdgeFanin0( For_Man_t * p, Gia_Obj_t * pObj )   { return p->plEdge[Gia_ObjFaninId0p(p->pGia, pObj)];  }
static inline int  Gia_ObjEdgeFanin1( For_Man_t * p, Gia_Obj_t * pObj )   { return p->plEdge[Gia_ObjFaninId1p(p->pGia, pObj)];  }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
For_Man_t * For_ManStart( Gia_Man_t * pGia )
{
    For_Man_t * p;
    p = ABC_CALLOC( For_Man_t, 1 );
    p->pGia   = pGia;
    p->nObjs  = Gia_ManObjNum(pGia);
    p->pPlace = ABC_ALLOC( int, p->nObjs );
    p->piNext = ABC_ALLOC( int, p->nObjs );
    p->piRoot = ABC_ALLOC( int, p->nObjs );
    p->plEdge = ABC_ALLOC( float, p->nObjs );
    p->pNodes = ABC_ALLOC( For_Obj_t, p->nObjs );
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void For_ManStop( For_Man_t * p )
{
    ABC_FREE( p->pPlace );
    ABC_FREE( p->piNext );
    ABC_FREE( p->piRoot );
    ABC_FREE( p->plEdge );
    ABC_FREE( p->pNodes );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Derives random ordering of nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void For_ManSetInitPlaceRandom( For_Man_t * p )
{
    int i, Temp, iNext;
    Aig_ManRandom( 1 );
    for ( i = 0; i < p->nObjs; i++ )
        p->pPlace[i] = i;
    for ( i = 0; i < p->nObjs; i++ )
    {
        iNext = Aig_ManRandom( 0 ) % p->nObjs;
        Temp = p->pPlace[i];
        p->pPlace[i] = p->pPlace[iNext];
        p->pPlace[iNext] = Temp;
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void For_ManSetInitPlaceDfs_rec( For_Man_t * p, Gia_Obj_t * pObj, int fRev )
{
    if ( pObj->fMark0 )
        return;
    pObj->fMark0 = 1;
    if ( Gia_ObjIsCi(pObj) || Gia_ObjIsConst0(pObj) )
    {
        p->pPlace[ Gia_ObjId(p->pGia, pObj) ] = p->iObj++;
        return;
    }
    if ( Gia_ObjIsCo(pObj) )
    {
        For_ManSetInitPlaceDfs_rec( p, Gia_ObjFanin0(pObj), fRev );
        p->pPlace[ Gia_ObjId(p->pGia, pObj) ] = p->iObj++;
        return;
    }
    assert( Gia_ObjIsAnd(pObj) );
    if ( fRev )
    {
        For_ManSetInitPlaceDfs_rec( p, Gia_ObjFanin1(pObj), fRev );
        For_ManSetInitPlaceDfs_rec( p, Gia_ObjFanin0(pObj), fRev );
    }
    else
    {
        For_ManSetInitPlaceDfs_rec( p, Gia_ObjFanin0(pObj), fRev );
        For_ManSetInitPlaceDfs_rec( p, Gia_ObjFanin1(pObj), fRev );
    }
    p->pPlace[ Gia_ObjId(p->pGia, pObj) ] = p->iObj++;
}

/**Function*************************************************************

  Synopsis    [Derives DFS ordering of nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void For_ManSetInitPlaceDfs( For_Man_t * p, int fRev )
{
    Gia_Obj_t * pObj;
    int i;
    p->iObj = 0;
    Gia_ManCleanMark0( p->pGia );
    For_ManSetInitPlaceDfs_rec( p, Gia_ManConst0(p->pGia), fRev );
    Gia_ManForEachCo( p->pGia, pObj, i )
        For_ManSetInitPlaceDfs_rec( p, pObj, fRev );
    Gia_ManForEachCi( p->pGia, pObj, i )
        if ( pObj->fMark0 == 0 )
            For_ManSetInitPlaceDfs_rec( p, pObj, fRev );
    assert( p->iObj == p->nObjs );
    Gia_ManCleanMark0( p->pGia );
}

/**Function*************************************************************

  Synopsis    [Computes span for the given placement.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
double For_ManGetEdgeSpan( For_Man_t * p )
{
    double Result = 0.0;
    Gia_Obj_t * pObj;
    int i, Diff;
    Gia_ManForEachAnd( p->pGia, pObj, i )
    {
        Diff    = Gia_ObjPlace(p, pObj) - Gia_ObjPlaceFanin0(p, pObj);
        Result += (double)ABC_ABS(Diff);
        Diff    = Gia_ObjPlace(p, pObj) - Gia_ObjPlaceFanin1(p, pObj);
        Result += (double)ABC_ABS(Diff);
    }
    Gia_ManForEachCo( p->pGia, pObj, i )
    {
        Diff    = Gia_ObjPlace(p, pObj) - Gia_ObjPlaceFanin0(p, pObj);
        Result += (double)ABC_ABS(Diff);
    }
    return Result;
}

/**Function*************************************************************

  Synopsis    [Computes max cut of the given placement.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int For_ManGetMaxCut( For_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i, iObj, iFan, * pTemp;
    int nCutCut, nCutMax;
    pTemp = ABC_CALLOC( int, p->nObjs );
    Gia_ManForEachAnd( p->pGia, pObj, i )
    {
        iObj = Gia_ObjPlace(p, pObj);
        iFan = Gia_ObjPlaceFanin0(p, pObj);
        if ( iObj < iFan )
        {
            pTemp[iObj]++;
            pTemp[iFan]--;
        }
        else
        {
            pTemp[iObj]--;
            pTemp[iFan]++;
        }
        iObj = Gia_ObjPlace(p, pObj);
        iFan = Gia_ObjPlaceFanin1(p, pObj);
        if ( iObj < iFan )
        {
            pTemp[iObj]++;
            pTemp[iFan]--;
        }
        else
        {
            pTemp[iObj]--;
            pTemp[iFan]++;
        }
    }
    Gia_ManForEachCo( p->pGia, pObj, i )
    {
        iObj = Gia_ObjPlace(p, pObj);
        iFan = Gia_ObjPlaceFanin0(p, pObj);
        if ( iObj < iFan )
        {
            pTemp[iObj]++;
            pTemp[iFan]--;
        }
        else
        {
            pTemp[iObj]--;
            pTemp[iFan]++;
        }
    }
    nCutCut = nCutMax = 0;
    for ( i = 0; i < p->nObjs; i++ )
    {
        nCutCut += pTemp[i];
        nCutMax = ABC_MAX( nCutCut, nCutMax );
    }
    ABC_FREE( pTemp );
    assert( nCutCut == 0 );
    return nCutMax;
}

/**Function*************************************************************

  Synopsis    [Computes hyper-edge centers.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void For_ManEdgeCenters( For_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i;
    memset( p->plEdge, 0, sizeof(float) * p->nObjs );
    Gia_ManForEachObj( p->pGia, pObj, i )
    {
        p->plEdge[i] = Gia_ObjPlace(p, pObj);
        if ( Gia_ObjIsAnd(pObj) )
        {
            p->plEdge[Gia_ObjFaninId0p(p->pGia, pObj)] += Gia_ObjPlace(p, pObj);
            p->plEdge[Gia_ObjFaninId1p(p->pGia, pObj)] += Gia_ObjPlace(p, pObj);
        }
        else if ( Gia_ObjIsCo(pObj) )
        {
            p->plEdge[Gia_ObjFaninId0p(p->pGia, pObj)] += Gia_ObjPlace(p, pObj);
        }
    }
    Gia_ManForEachObj( p->pGia, pObj, i )
        p->plEdge[i] /= 1.0 + Gia_ObjRefs( p->pGia, pObj );
}

/**Function*************************************************************

  Synopsis    [Computes object centers.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void For_ManObjCenters( For_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i;
    Gia_ManForEachObj( p->pGia, pObj, i )
    {
        p->pNodes[i].lNode = Gia_ObjEdge(p, pObj);
        if ( Gia_ObjIsAnd(pObj) )
        {
            p->pNodes[i].lNode += Gia_ObjEdgeFanin0(p, pObj);
            p->pNodes[i].lNode += Gia_ObjEdgeFanin1(p, pObj);
            p->pNodes[i].lNode /= 3.0;
        }
        else if ( Gia_ObjIsCo(pObj) )
        {
            p->pNodes[i].lNode += Gia_ObjEdgeFanin0(p, pObj);
            p->pNodes[i].lNode /= 2.0;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Sorts objects by their new centers.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int For_ObjCompare( For_Obj_t ** pp0, For_Obj_t ** pp1 )
{
    if ( (*pp0)->lNode < (*pp1)->lNode )
        return -1;
    if ( (*pp0)->lNode > (*pp1)->lNode )
        return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Sorts objects by their new centers.]

  Description []
               
  SideEffects []

  SeeAlso     []
 
***********************************************************************/
void For_ManSortObjects( For_Man_t * p )
{
    For_Obj_t * pNode, * pPrev;
    Vec_Ptr_t * vArray;
    int i, k, iPlace;
    // link the nodes into lists by cost
    memset( p->piRoot, 0xff, sizeof(int) * p->nObjs );
    for ( i = 0; i < p->nObjs; i++ )
    {
        p->pNodes[i].iObj = i;
        iPlace = (int)p->pNodes[i].lNode;
        assert( iPlace >= 0 && iPlace < p->nObjs );
        p->piNext[i] = p->piRoot[iPlace];
        p->piRoot[iPlace] = i;        
    }
    // reconstruct the order
    p->iObj = 0;
    pPrev = NULL;
    vArray = Vec_PtrAlloc( 100 );
    for ( i = 0; i < p->nObjs; i++ )
    {
        Vec_PtrClear( vArray );
        for ( k = p->piRoot[i]; ~((unsigned)k); k = p->piNext[k] )
            Vec_PtrPush( vArray, p->pNodes + k );
        Vec_PtrSort( vArray, (int (*)())For_ObjCompare ); 
        Vec_PtrForEachEntry( vArray, pNode, k )
        {
            p->pPlace[ pNode->iObj ] = p->iObj++;
            assert( !pPrev || pPrev->lNode <= pNode->lNode );
            pPrev = pNode;
        }
    }
    Vec_PtrFree( vArray );
    assert( p->iObj == p->nObjs );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void For_ManPlaceByForce( For_Man_t * p )
{
    int clk, Iter, fUseCut = 1;
    double iCostThis, iCostPrev;
    iCostThis = fUseCut? For_ManGetMaxCut(p) : For_ManGetEdgeSpan(p);
    printf( "Init = %12.0f. \n", iCostThis );
    Iter = 0;
    do {
        Iter++;
        iCostPrev = iCostThis;
clk = clock();
        For_ManEdgeCenters( p );
//ABC_PRT( "Time", clock() - clk );
clk = clock();
        For_ManObjCenters( p );
//ABC_PRT( "Time", clock() - clk );
clk = clock();
        For_ManSortObjects( p );
//ABC_PRT( "Time", clock() - clk );
        iCostThis = fUseCut? For_ManGetMaxCut(p) : For_ManGetEdgeSpan(p);
        printf( "%4d = %12.0f. \n", Iter, iCostThis );
    } while ( iCostPrev > iCostThis );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void For_ManExperiment( Gia_Man_t * pGia )
{
    For_Man_t * p;
    int clk = clock();
    p = For_ManStart( pGia );
    Gia_ManCreateRefs( pGia );

    // use DSF order
clk = clock();
    For_ManSetInitPlaceDfs( p, 0 );
    printf( "Tot span = %12.0f  ", For_ManGetEdgeSpan(p) );
    printf( "Max span = %8d  ", For_ManGetMaxCut(p) );
ABC_PRT( "Time", clock() - clk );

clk = clock();
    For_ManPlaceByForce( p );
ABC_PRT( "Time", clock() - clk );

    // use modified DFS order
clk = clock();
    For_ManSetInitPlaceDfs( p, 1 );
    printf( "Tot span = %12.0f  ", For_ManGetEdgeSpan(p) );
    printf( "Max span = %8d  ", For_ManGetMaxCut(p) );
ABC_PRT( "Time", clock() - clk );

clk = clock();
    For_ManPlaceByForce( p );
ABC_PRT( "Time", clock() - clk );

    // use random order
clk = clock();
    For_ManSetInitPlaceRandom( p );
    printf( "Tot span = %12.0f  ", For_ManGetEdgeSpan(p) );
    printf( "Max span = %8d  ", For_ManGetMaxCut(p) );
ABC_PRT( "Time", clock() - clk );

clk = clock();
    For_ManPlaceByForce( p );
ABC_PRT( "Time", clock() - clk );

    For_ManStop( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


