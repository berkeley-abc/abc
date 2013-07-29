/**CFile****************************************************************

  FileName    [sclBuffer.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Standard-cell library representation.]

  Synopsis    [Buffering algorithms.]

  Author      [Alan Mishchenko, Niklas Een]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 24, 2012.]

  Revision    [$Id: sclBuffer.c,v 1.0 2012/08/24 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sclSize.h"
#include "map/mio/mio.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define BUF_SCALE 1000

typedef struct Buf_Man_t_ Buf_Man_t;
struct Buf_Man_t_
{
    // parameters
    int            nFanMin;   // the smallest fanout count to consider
    int            nFanMax;   // the largest fanout count allowed off CP
    // internal deta
    Abc_Ntk_t *    pNtk;      // logic network
    Vec_Int_t *    vOffsets;  // offsets into edge delays
    Vec_Int_t *    vEdges;    // edge delays
    Vec_Int_t *    vArr;      // arrival times
    Vec_Int_t *    vDep;      // departure times
    Vec_Flt_t *    vCounts;   // fanout counts
    Vec_Que_t *    vQue;      // queue by fanout count
    int            nObjStart; // the number of starting objects
    int            nObjAlloc; // the number of allocated objects
    int            DelayMax;  // maximum delay (percentage of inverter delay)
    float          DelayInv;  // inverter delay
    // sorting fanouts
    Vec_Int_t *    vOrder;    // ordering of fanouts
    Vec_Int_t *    vDelays;   // fanout delays
    Vec_Int_t *    vNonCrit;  // non-critical fanouts
    Vec_Int_t *    vTfCone;   // TFI/TFO cone of the node including the node
    Vec_Ptr_t *    vFanouts;  // temp storage for fanouts
    // statistics
    int            nSeparate;
    int            nDuplicate;
    int            nBranch0;
    int            nBranch1;
};

static inline int  Abc_BufNodeArr( Buf_Man_t * p, Abc_Obj_t * pObj )                     { return Vec_IntEntry( p->vArr, Abc_ObjId(pObj) );                                   }
static inline int  Abc_BufNodeDep( Buf_Man_t * p, Abc_Obj_t * pObj )                     { return Vec_IntEntry( p->vDep, Abc_ObjId(pObj) );                                   }
static inline void Abc_BufSetNodeArr( Buf_Man_t * p, Abc_Obj_t * pObj, int f )           { Vec_IntWriteEntry( p->vArr, Abc_ObjId(pObj), f );                                  }
static inline void Abc_BufSetNodeDep( Buf_Man_t * p, Abc_Obj_t * pObj, int f )           { Vec_IntWriteEntry( p->vDep, Abc_ObjId(pObj), f );                                  }
static inline int  Abc_BufEdgeDelay( Buf_Man_t * p, Abc_Obj_t * pObj, int i )            { return Vec_IntEntry( p->vEdges, Vec_IntEntry(p->vOffsets, Abc_ObjId(pObj)) + i );  }
static inline void Abc_BufSetEdgeDelay( Buf_Man_t * p, Abc_Obj_t * pObj, int i, int f )  { Vec_IntWriteEntry( p->vEdges, Vec_IntEntry(p->vOffsets, Abc_ObjId(pObj)) + i, f ); }
static inline int  Abc_BufNodeSlack( Buf_Man_t * p, Abc_Obj_t * pObj )                   { return p->DelayMax - Abc_BufNodeArr(p, pObj) - Abc_BufNodeDep(p, pObj);            }
static inline int  Abc_BufEdgeSlack( Buf_Man_t * p, Abc_Obj_t * pObj, Abc_Obj_t * pFan ) { return p->DelayMax - Abc_BufNodeArr(p, pObj) - Abc_BufNodeDep(p, pFan) - Abc_BufEdgeDelay(p, pFan, Abc_NodeFindFanin(pFan, pObj)); }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float Abc_BufComputeArr( Buf_Man_t * p, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanin;
    int i;
    float DelayF, Delay = -ABC_INFINITY;
    Abc_ObjForEachFanin( pObj, pFanin, i )
    {
        DelayF = Abc_BufNodeArr(p, pFanin) + Abc_BufEdgeDelay(p, pObj, i);
        if ( Delay < DelayF )
            Delay = DelayF;
    }
    Abc_BufSetNodeArr( p, pObj, Delay );
    return Delay;
}
float Abc_BufComputeDep( Buf_Man_t * p, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanout;
    int i;
    float DelayF, Delay = -ABC_INFINITY;
    Abc_ObjForEachFanout( pObj, pFanout, i )
    {
        DelayF = Abc_BufNodeDep(p, pFanout) + Abc_BufEdgeDelay(p, pFanout, Abc_NodeFindFanin(pFanout, pObj));
        if ( Delay < DelayF )
            Delay = DelayF;
    }
    Abc_BufSetNodeDep( p, pObj, Delay );
    return Delay;
}
void Abc_BufUpdateGlobal( Buf_Man_t * p )
{
    Abc_Obj_t * pObj;
    int i;
    p->DelayMax = 0;
    Abc_NtkForEachCo( p->pNtk, pObj, i )
        p->DelayMax = Abc_MaxInt( p->DelayMax, Abc_BufNodeArr(p, Abc_ObjFanin0(pObj)) );
}
void Abc_BufCreateEdges( Buf_Man_t * p, Abc_Obj_t * pObj )
{
    int k;
    Mio_Gate_t * pGate = Abc_ObjIsCo(pObj) ? NULL : (Mio_Gate_t *)pObj->pData;
    Vec_IntWriteEntry( p->vOffsets, Abc_ObjId(pObj), Vec_IntSize(p->vEdges) );
    for ( k = 0; k < Abc_ObjFaninNum(pObj); k++ )
        Vec_IntPush( p->vEdges, pGate ? (int)(1.0 * BUF_SCALE * Mio_GateReadPinDelay(pGate, k) / p->DelayInv) : 0 );
}
void Abc_BufAddToQue( Buf_Man_t * p, Abc_Obj_t * pObj )
{
    if ( Abc_ObjFanoutNum(pObj) < p->nFanMin )
        return;
    Vec_FltWriteEntry( p->vCounts, Abc_ObjId(pObj), Abc_ObjFanoutNum(pObj) );
    assert( !Vec_QueIsMember(p->vQue, Abc_ObjId(pObj)) );
    Vec_QuePush( p->vQue, Abc_ObjId(pObj) );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_BufCollectTfoCone_rec( Abc_Obj_t * pNode, Vec_Int_t * vNodes )
{
    Abc_Obj_t * pNext;
    int i;
    if ( Abc_NodeIsTravIdCurrent( pNode ) )
        return;
    Abc_NodeSetTravIdCurrent( pNode );
    if ( Abc_ObjIsCo(pNode) )
        return;
    assert( Abc_ObjIsCi(pNode) || Abc_ObjIsNode(pNode) );
    Abc_ObjForEachFanout( pNode, pNext, i )
        Abc_BufCollectTfoCone_rec( pNext, vNodes );
    if ( Abc_ObjIsNode(pNode) )
        Vec_IntPush( vNodes, Abc_ObjId(pNode) );
}
void Abc_BufCollectTfoCone( Buf_Man_t * p, Abc_Obj_t * pObj )
{
    Vec_IntClear( p->vTfCone );
    Abc_NtkIncrementTravId( p->pNtk );
    Abc_BufCollectTfoCone_rec( pObj, p->vTfCone );
}
void Abc_BufUpdateArr( Buf_Man_t * p, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pNext;
    int i, Delay;
//    assert( Abc_ObjIsNode(pObj) );
    Abc_BufCollectTfoCone( p, pObj );
    Vec_IntReverseOrder( p->vTfCone );
    Abc_NtkForEachObjVec( p->vTfCone, p->pNtk, pNext, i )
    {
        Delay = Abc_BufComputeArr( p, pNext );
        p->DelayMax = Abc_MaxInt( p->DelayMax, Delay );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_BufCollectTfiCone_rec( Abc_Obj_t * pNode, Vec_Int_t * vNodes )
{
    Abc_Obj_t * pNext;
    int i;
    if ( Abc_NodeIsTravIdCurrent( pNode ) )
        return;
    Abc_NodeSetTravIdCurrent( pNode );
    if ( Abc_ObjIsCi(pNode) )
        return;
    assert( Abc_ObjIsNode(pNode) );
    Abc_ObjForEachFanin( pNode, pNext, i )
        Abc_BufCollectTfiCone_rec( pNext, vNodes );
    Vec_IntPush( vNodes, Abc_ObjId(pNode) );
}
void Abc_BufCollectTfiCone( Buf_Man_t * p, Abc_Obj_t * pObj )
{
    Vec_IntClear( p->vTfCone );
    Abc_NtkIncrementTravId( p->pNtk );
    Abc_BufCollectTfiCone_rec( pObj, p->vTfCone );
}
void Abc_BufUpdateDep( Buf_Man_t * p, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pNext;
    int i, Delay;
//    assert( Abc_ObjIsNode(pObj) );
    Abc_BufCollectTfiCone( p, pObj );
    Vec_IntReverseOrder( p->vTfCone );
    Abc_NtkForEachObjVec( p->vTfCone, p->pNtk, pNext, i )
    {
        Delay = Abc_BufComputeDep( p, pNext );
        p->DelayMax = Abc_MaxInt( p->DelayMax, Delay );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Buf_Man_t * Buf_ManStart( Abc_Ntk_t * pNtk )
{
    Buf_Man_t * p;
    Abc_Obj_t * pObj;
    Vec_Ptr_t * vNodes;
    int i;
    p = ABC_CALLOC( Buf_Man_t, 1 );
    p->pNtk      = pNtk;
    p->nFanMin   = 6;
//    p->nFanMax   = 16;
    // allocate arrays
    p->nObjStart = Abc_NtkObjNumMax(p->pNtk);
    p->nObjAlloc = (6 * Abc_NtkObjNumMax(p->pNtk) / 3) + 100;
    p->vOffsets  = Vec_IntAlloc( p->nObjAlloc );
    p->vArr      = Vec_IntAlloc( p->nObjAlloc );
    p->vDep      = Vec_IntAlloc( p->nObjAlloc );
    p->vCounts   = Vec_FltAlloc( p->nObjAlloc );
    p->vQue      = Vec_QueAlloc( p->nObjAlloc );
    Vec_IntFill( p->vOffsets, p->nObjAlloc, -ABC_INFINITY );
    Vec_IntFill( p->vArr,     p->nObjAlloc, 0 );
    Vec_IntFill( p->vDep,     p->nObjAlloc, 0 );
    Vec_FltFill( p->vCounts,  p->nObjAlloc, -ABC_INFINITY );
    Vec_QueSetCosts( p->vQue, Vec_FltArrayP(p->vCounts) );
    // collect edge delays
    p->DelayInv  = Mio_GateReadPinDelay( Mio_LibraryReadInv((Mio_Library_t *)pNtk->pManFunc), 0 );
    p->vEdges    = Vec_IntAlloc( 1000 );
    // create edges
    vNodes = Abc_NtkDfs( p->pNtk, 0 );
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pObj, i )
        Abc_BufCreateEdges( p, pObj );
    Abc_NtkForEachCo( p->pNtk, pObj, i )
        Abc_BufCreateEdges( p, pObj );
    // derive delays
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pObj, i )
        Abc_BufComputeArr( p, pObj );
    Vec_PtrForEachEntryReverse( Abc_Obj_t *, vNodes, pObj, i )
        Abc_BufComputeDep( p, pObj );
    Abc_BufUpdateGlobal( p );
    // create fanout queue
    Abc_NtkForEachCi( p->pNtk, pObj, i )
        Abc_BufAddToQue( p, pObj );
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pObj, i )
        Abc_BufAddToQue( p, pObj );
    Vec_PtrFree( vNodes );
    // print everything
//    Abc_NtkForEachNode( p->pNtk, pObj, i )
//        printf( "%4d : %4d %4d\n", i, Abc_BufNodeArr(p, pObj), Abc_BufNodeDep(p, pObj) );
    p->vDelays  = Vec_IntAlloc( 100 );
    p->vOrder   = Vec_IntAlloc( 100 );
    p->vNonCrit = Vec_IntAlloc( 100 );
    p->vTfCone  = Vec_IntAlloc( 100 );
    p->vFanouts = Vec_PtrAlloc( 100 );
    return p;
}
void Buf_ManStop( Buf_Man_t * p )
{
    printf( "Sep = %d. Dup = %d. Br0 = %d. Br1 = %d.   ", 
        p->nSeparate, p->nDuplicate, p->nBranch0, p->nBranch1 );
    printf( "Orig = %d. Add = %d. Rem = %d.\n", 
        p->nObjStart, Abc_NtkObjNumMax(p->pNtk) - p->nObjStart, 
        p->nObjAlloc - Abc_NtkObjNumMax(p->pNtk) );
    Vec_PtrFree( p->vFanouts );
    Vec_IntFree( p->vTfCone );
    Vec_IntFree( p->vNonCrit );
    Vec_IntFree( p->vDelays );
    Vec_IntFree( p->vOrder );
    Vec_IntFree( p->vOffsets );
    Vec_IntFree( p->vEdges );
    Vec_IntFree( p->vArr );
    Vec_IntFree( p->vDep );
//    Vec_QueCheck( p->vQue );
    Vec_QueFree( p->vQue );
    Vec_FltFree( p->vCounts );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_BufSortByDelay( Buf_Man_t * p, int iPivot )
{
    Abc_Obj_t * pObj, * pFanout;
    int i, * pOrder;
    Vec_IntClear( p->vDelays );
    pObj = Abc_NtkObj( p->pNtk, iPivot );
    Abc_ObjForEachFanout( pObj, pFanout, i )
    {
        int Slack = Abc_BufEdgeSlack(p, pObj, pFanout);
        if ( Slack < 0 )
            printf( "%d  ", Slack );
        Vec_IntPush( p->vDelays, Abc_MaxInt(0, Slack) );
    }
    pOrder = Abc_QuickSortCost( Vec_IntArray(p->vDelays), Vec_IntSize(p->vDelays), 0 );
//Vec_IntPrint( p->vDelays );
    Vec_IntClear( p->vOrder );
    for ( i = 0; i < Vec_IntSize(p->vDelays); i++ )
        Vec_IntPush( p->vOrder, Abc_ObjId(Abc_ObjFanout(pObj, pOrder[i])) );
    ABC_FREE( pOrder );
    // print
//    for ( i = 0; i < Vec_IntSize(p->vDelays); i++ )
//        printf( "%5d - %5d   ", Vec_IntEntry(p->vOrder, i), Abc_BufEdgeSlack(p, pObj, Abc_NtkObj(p->pNtk, Vec_IntEntry(p->vOrder, i))) );
    return p->vOrder;        
}
void Abc_BufPrintOne( Buf_Man_t * p, int iPivot )
{
    Abc_Obj_t * pObj, * pFanout;
    Vec_Int_t * vOrder;
    int i, Slack;
    pObj = Abc_NtkObj( p->pNtk, iPivot );
    vOrder = Abc_BufSortByDelay( p, iPivot );
    printf( "Node %5d  Fi = %d  Fo = %3d  Lev = %3d : {", iPivot, Abc_ObjFaninNum(pObj), Abc_ObjFanoutNum(pObj), Abc_ObjLevel(pObj) );
    Abc_NtkForEachObjVec( vOrder, p->pNtk, pFanout, i )
    {
        Slack = Abc_BufEdgeSlack( p, pObj, pFanout );
        printf( " %d(%d)", Abc_ObjId(pFanout), Slack );
    }
    printf( " }\n" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_BufComputeAverage( Buf_Man_t * p, int iPivot, Vec_Int_t * vOrder )
{
    Abc_Obj_t * pObj, * pFanout;
    int i, Average = 0;
    pObj = Abc_NtkObj( p->pNtk, iPivot );
    Abc_NtkForEachObjVec( vOrder, p->pNtk, pFanout, i )
        Average += Abc_BufEdgeSlack( p, pObj, pFanout );
    return Average / Vec_IntSize(vOrder);
}
int Abc_BufCountNonCritical_( Buf_Man_t * p, int iPivot, Vec_Int_t * vOrder )
{
    Abc_Obj_t * pObj, * pFanout;
    int i;
    Vec_IntClear( p->vNonCrit );
    pObj = Abc_NtkObj( p->pNtk, iPivot );
    Abc_NtkForEachObjVec( vOrder, p->pNtk, pFanout, i )
        if ( Abc_BufEdgeSlack( p, pObj, pFanout ) > 5*BUF_SCALE/2 )
            Vec_IntPush( p->vNonCrit, Abc_ObjId(pFanout) );
    return Vec_IntSize(p->vNonCrit);
}
Abc_Obj_t * Abc_BufFindNonBuffDriver( Buf_Man_t * p, Abc_Obj_t * pObj )
{
    return (Abc_ObjIsNode(pObj) && Abc_NodeIsBuf(pObj)) ? Abc_BufFindNonBuffDriver(p, Abc_ObjFanin0(pObj)) : pObj;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_BufCountNonCritical( Buf_Man_t * p, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanout;
    int i;
    Vec_IntClear( p->vNonCrit );
    Abc_ObjForEachFanout( pObj, pFanout, i )
        if ( Abc_BufEdgeSlack( p, pObj, pFanout ) > 3*BUF_SCALE )
            Vec_IntPush( p->vNonCrit, Abc_ObjId(pFanout) );
    return Vec_IntSize(p->vNonCrit);
}
void Abc_BufPerformOne( Buf_Man_t * p, int iPivot, int fVerbose )
{
    Abc_Obj_t * pObj, * pFanout;
    Vec_Int_t * vOrder;
    int Fastest, Slowest, Average;
    int i, j, nCrit, nNonCrit;
    int DelayMax = p->DelayMax;
    pObj     = Abc_NtkObj( p->pNtk, iPivot );
    nNonCrit = Abc_BufCountNonCritical( p, pObj );
    nCrit    = Abc_ObjFanoutNum(pObj) - nNonCrit;
if ( fVerbose )
{
vOrder = Abc_BufSortByDelay( p, iPivot );
//Abc_BufPrintOne( p, iPivot );
Fastest  = Abc_BufEdgeSlack( p, pObj, Abc_NtkObj(p->pNtk, Vec_IntEntry(vOrder,0)) );
Slowest  = Abc_BufEdgeSlack( p, pObj, Abc_NtkObj(p->pNtk, Vec_IntEntryLast(vOrder)) );
Average  = Abc_BufComputeAverage( p, iPivot, vOrder );
printf( "FI =%2d. FO =%4d. ", Abc_ObjFaninNum(pObj), Abc_ObjFanoutNum(pObj) );
printf( "Fastest =%5d. Slowest =%5d. Ave =%5d.  Crit =%3d. NonCrit =%3d.  ", Fastest, Slowest, Average, nCrit, nNonCrit );
}
    // decide based on these
    assert( Abc_NtkObjNumMax(p->pNtk) + 30 < p->nObjAlloc );
    if ( nCrit > 0 && nNonCrit > 1 )
    {
        // separate using buffer
        Abc_Obj_t * pBuffer = Abc_NtkCreateNodeBuf( p->pNtk, pObj );
        Abc_NtkForEachObjVec( p->vNonCrit, p->pNtk, pFanout, i )
            Abc_ObjPatchFanin( pFanout, pObj, pBuffer );
        // update timing
        Abc_BufCreateEdges( p, pBuffer );
        Abc_BufUpdateArr( p, pBuffer );
        Abc_BufUpdateDep( p, pBuffer );
        Abc_BufAddToQue( p, pObj );
        Abc_BufAddToQue( p, pBuffer );
        p->nSeparate++;
if ( fVerbose )
printf( "Adding buffer\n" );
    }

    else if ( nNonCrit < 2 && Abc_ObjFanoutNum(pObj) > 4 && Abc_ObjFanoutNum(pObj) < 12 && Abc_ObjIsNode(pObj) )
    {
        // duplicate
        Abc_Obj_t * pClone = Abc_NtkDupObj( p->pNtk, pObj, 0 );
        Abc_ObjForEachFanin( pObj, pFanout, i )
            Abc_ObjAddFanin( pClone, pFanout );
        Abc_NodeCollectFanouts( pObj, p->vFanouts );
        Vec_PtrForEachEntryStop( Abc_Obj_t *, p->vFanouts, pFanout, i, Vec_PtrSize(p->vFanouts)/2 )
            Abc_ObjPatchFanin( pFanout, pObj, pClone );
        // update timing
        Abc_BufCreateEdges( p, pClone );
        Abc_BufSetNodeArr( p, pClone, Abc_BufNodeArr(p, pObj) );
        Abc_BufUpdateDep( p, pObj );
        Abc_BufUpdateDep( p, pClone );
        Abc_BufAddToQue( p, pObj );
        Abc_BufAddToQue( p, pClone );
        p->nDuplicate++;
        // add fanins to queue
if ( fVerbose )
printf( "Duplicating node\n" );
    }

    else if ( Abc_ObjFanoutNum(pObj) >= 12 )
    {
        // branch (consider buffer)
//        int nFan     = Abc_ObjFanoutNum(pObj);
        int nFan     = 64;
        double Res   = pow(nFan, 0.34);
        int Temp     = (int)pow(Abc_ObjFanoutNum(pObj), 0.34);
        int nDegree  = Abc_MinInt( 4, (int)pow(Abc_ObjFanoutNum(pObj), 0.34) );
        int n1Degree = Abc_ObjFanoutNum(pObj) / nDegree + 1;
        int n1Number = Abc_ObjFanoutNum(pObj) % nDegree;
        int nFirst   = n1Degree * n1Number;
//        Abc_Obj_t * pNonBuff = Abc_BufFindNonBuffDriver( p, pObj );
        // create inverters
        int iFirstBuf = Abc_NtkObjNumMax( p->pNtk );
        Abc_NodeCollectFanouts( pObj, p->vFanouts );
        if ( Abc_ObjIsNode(pObj) && Abc_NodeIsBuf(pObj) )
        {
            p->nBranch0++;
            pObj->pData = Mio_LibraryReadInv((Mio_Library_t *)p->pNtk->pManFunc);
            Abc_BufSetEdgeDelay( p, pObj, 0, BUF_SCALE );
            assert( Abc_NodeIsInv(pObj) );
            for ( i = 0; i < nDegree; i++ )
                Abc_NtkCreateNodeInv( p->pNtk, pObj );
if ( fVerbose )
printf( "Adding %d inverters\n", nDegree );
        }
        else
        {
            p->nBranch1++;
            for ( i = 0; i < nDegree; i++ )
                Abc_NtkCreateNodeBuf( p->pNtk, pObj );
if ( fVerbose )
printf( "Adding %d buffers\n", nDegree );
        }
        // create inverters
        Vec_PtrForEachEntry( Abc_Obj_t *, p->vFanouts, pFanout, i )
        {
            j = (i < nFirst) ? i/n1Degree : n1Number + ((i - nFirst)/(n1Degree - 1));
            assert( j >= 0 && j < nDegree );
            Abc_ObjPatchFanin( pFanout, pObj, Abc_NtkObj(p->pNtk, iFirstBuf + j) );
        }
        // remove node
//        if ( Abc_ObjIsNode(pObj) && Abc_ObjFanoutNum(pObj) == 0 )
//            Abc_NtkDeleteObj_rec( pObj, 1 );
        // update timing
        for ( i = 0; i < nDegree; i++ )
            Abc_BufCreateEdges( p, Abc_NtkObj(p->pNtk, iFirstBuf + i) );
        Abc_BufUpdateArr( p, pObj );
        for ( i = 0; i < nDegree; i++ )
            Abc_BufComputeDep( p, Abc_NtkObj(p->pNtk, iFirstBuf + i) );
        Abc_BufUpdateDep( p, pObj );
        for ( i = 0; i < nDegree; i++ )
            Abc_BufAddToQue( p, Abc_NtkObj(p->pNtk, iFirstBuf + i) );
    }
    else
    {
if ( fVerbose )
printf( "Doing nothing\n" );
    }
//    if ( DelayMax != p->DelayMax )
//        printf( "%d (%.2f)  ", p->DelayMax, 1.0 * p->DelayMax * p->DelayInv / BUF_SCALE );
}
Abc_Ntk_t * Abc_SclBufPerform( Abc_Ntk_t * pNtk, int fVerbose )
{
    Abc_Ntk_t * pNew;
    Buf_Man_t * p = Buf_ManStart( pNtk );
    int i, Limit = ABC_INFINITY;
//    int i, Limit = 3;
    for ( i = 0; i < Limit && Vec_QueSize(p->vQue); i++ )
        Abc_BufPerformOne( p, Vec_QuePop(p->vQue), fVerbose );
    Buf_ManStop( p );
    // duplication in topo order
    pNew = Abc_NtkDupDfs( pNtk );
    Abc_SclCheckNtk( pNew, fVerbose );
//    Abc_NtkDelete( pNew );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

