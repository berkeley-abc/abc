/**CFile****************************************************************

  FileName    [sfmTime.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based optimization using internal don't-cares.]

  Synopsis    [Timing manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: sfmTime.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sfmInt.h"
#include "misc/st/st.h"
#include "map/mio/mio.h"
#include "base/abc/abc.h"
#include "misc/util/utilNam.h"
#include "map/scl/sclCon.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Sfm_Tim_t_ Sfm_Tim_t;
struct Sfm_Tim_t_
{
    // external
    Mio_Library_t *   pLib;        // library
    Scl_Con_t *       pExt;        // external timing
    Abc_Ntk_t *       pNtk;        // mapped network
    int               Delay;       // the largest delay
    // timing info
    Vec_Int_t         vTimArrs;    // arrivals (rise/fall)
    Vec_Int_t         vTimReqs;    // required (rise/fall)
    Vec_Int_t         vTimSlews;   // slews (rise/fall)
    Vec_Int_t         vTimLoads;   // loads (rise/fall)
    // timing edges
    Vec_Int_t         vObjOffs;    // object offsets
    Vec_Int_t         vTimEdges;   // edge timings (rise/fall)
    // critical path
    Vec_Int_t         vPath;       // critical path
};

static inline int * Sfm_TimArr( Sfm_Tim_t * p, Abc_Obj_t * pNode )           { return Vec_IntEntryP( &p->vTimArrs,  Abc_Var2Lit(Abc_ObjId(pNode), 0) ); }
static inline int * Sfm_TimReq( Sfm_Tim_t * p, Abc_Obj_t * pNode )           { return Vec_IntEntryP( &p->vTimReqs,  Abc_Var2Lit(Abc_ObjId(pNode), 0) ); }
static inline int * Sfm_TimSlew( Sfm_Tim_t * p, Abc_Obj_t * pNode )          { return Vec_IntEntryP( &p->vTimSlews, Abc_Var2Lit(Abc_ObjId(pNode), 0) ); }
static inline int * Sfm_TimLoad( Sfm_Tim_t * p, Abc_Obj_t * pNode )          { return Vec_IntEntryP( &p->vTimLoads, Abc_Var2Lit(Abc_ObjId(pNode), 0) ); }

static inline int   Sfm_TimArrMax( Sfm_Tim_t * p, Abc_Obj_t * pNode )        { int * a = Sfm_TimArr(p, pNode); return Abc_MaxInt(a[0], a[1]);           }
static inline void  Sfm_TimSetReq( Sfm_Tim_t * p, Abc_Obj_t * pNode, int t ) { int * r = Sfm_TimReq(p, pNode); r[0] = r[1] = t;                         }
static inline int   Sfm_TimSlack( Sfm_Tim_t * p, Abc_Obj_t * pNode )         { int * r = Sfm_TimReq(p, pNode), * a = Sfm_TimArr(p, pNode); return Abc_MinInt(r[0]-a[0], r[1]-a[1]); }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sfm_TimEdgeArrival( Sfm_Tim_t * p, Abc_Obj_t * pNode, int iEdge, Mio_Pin_t * pPin )
{
    Mio_PinPhase_t PinPhase = Mio_PinReadPhase(pPin);
    int tDelayBlockRise = (int)(MIO_NUM*Mio_PinReadDelayBlockRise(pPin));  
    int tDelayBlockFall = (int)(MIO_NUM*Mio_PinReadDelayBlockFall(pPin));  
    int * pTimeOut = Sfm_TimArr(p, pNode);
    int * pTimeIn  = Sfm_TimArr(p, Abc_ObjFanin(pNode, iEdge));
    if ( PinPhase != MIO_PHASE_INV )  // NONINV phase is present
    {
        pTimeOut[0] = Abc_MaxInt( pTimeOut[0], pTimeIn[0] + tDelayBlockRise );
        pTimeOut[1] = Abc_MaxInt( pTimeOut[1], pTimeIn[1] + tDelayBlockFall );
    }
    if ( PinPhase != MIO_PHASE_NONINV )  // INV phase is present
    {
        pTimeOut[0] = Abc_MaxInt( pTimeOut[0], pTimeIn[1] + tDelayBlockRise );
        pTimeOut[1] = Abc_MaxInt( pTimeOut[1], pTimeIn[0] + tDelayBlockFall );
    }
}
void Sfm_TimGateArrival( Sfm_Tim_t * p, Abc_Obj_t * pNode )
{
    Mio_Gate_t * pGate = (Mio_Gate_t *)pNode->pData;
    Mio_Pin_t * pPin;  int i = 0;
    Mio_GateForEachPin( pGate, pPin )
        Sfm_TimEdgeArrival( p, pNode, i++, pPin );
    assert( i == Mio_GateReadPinNum(pGate) );
}

void Sfm_TimEdgeRequired( Sfm_Tim_t * p, Abc_Obj_t * pNode, int iEdge, Mio_Pin_t * pPin )
{
    Mio_PinPhase_t PinPhase = Mio_PinReadPhase(pPin);
    int tDelayBlockRise = (int)(MIO_NUM*Mio_PinReadDelayBlockRise(pPin));  
    int tDelayBlockFall = (int)(MIO_NUM*Mio_PinReadDelayBlockFall(pPin));  
    int * pTimeOut = Sfm_TimReq(p, pNode);
    int * pTimeIn  = Sfm_TimReq(p, Abc_ObjFanin(pNode, iEdge));
    if ( PinPhase != MIO_PHASE_INV )  // NONINV phase is present
    {
        pTimeIn[0] = Abc_MinInt( pTimeIn[0], pTimeOut[0] - tDelayBlockRise );
        pTimeIn[1] = Abc_MinInt( pTimeIn[1], pTimeOut[1] - tDelayBlockFall );
    }
    if ( PinPhase != MIO_PHASE_NONINV )  // INV phase is present
    {
        pTimeIn[0] = Abc_MinInt( pTimeIn[0], pTimeOut[1] - tDelayBlockRise );
        pTimeIn[1] = Abc_MinInt( pTimeIn[1], pTimeOut[0] - tDelayBlockFall );
    }
}
void Sfm_TimGateRequired( Sfm_Tim_t * p, Abc_Obj_t * pNode )
{
    Mio_Gate_t * pGate = (Mio_Gate_t *)pNode->pData;
    Mio_Pin_t * pPin;  int i = 0;
    Mio_GateForEachPin( pGate, pPin )
        Sfm_TimEdgeRequired( p, pNode, i++, pPin );
    assert( i == Mio_GateReadPinNum(pGate) );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sfm_TimCriticalPath_int( Sfm_Tim_t * p, Abc_Obj_t * pObj, Vec_Int_t * vPath, int SlackMax )
{
    Abc_Obj_t * pNext; int i;
    if ( Abc_NodeIsTravIdCurrent( pObj ) )
        return;
    Abc_NodeSetTravIdCurrent( pObj );
    assert( Abc_ObjIsNode(pObj) );
    Abc_ObjForEachFanin( pObj, pNext, i )
    {
        if ( Abc_ObjIsCi(pNext) || Abc_ObjFaninNum(pNext) == 0 )
            continue;
        assert( Abc_ObjIsNode(pNext) );
        if ( Sfm_TimSlack(p, pNext) <= SlackMax )
            Sfm_TimCriticalPath_int( p, pNext, vPath, SlackMax );
    }
    if ( Abc_ObjFaninNum(pObj) > 0 )
        Vec_IntPush( vPath, Abc_ObjId(pObj) );
}
int Sfm_TimCriticalPath( Sfm_Tim_t * p, int Window )
{
    int i, SlackMax = p->Delay * Window / 100;
    Abc_Obj_t * pObj, * pNext; 
    Vec_IntClear( &p->vPath );
    Abc_NtkIncrementTravId( p->pNtk ); 
    Abc_NtkForEachCo( p->pNtk, pObj, i )
    {
        pNext = Abc_ObjFanin0(pObj);
        if ( Abc_ObjIsCi(pNext) || Abc_ObjFaninNum(pNext) == 0 )
            continue;
        assert( Abc_ObjIsNode(pNext) );
        if ( Sfm_TimSlack(p, pNext) <= SlackMax )
            Sfm_TimCriticalPath_int( p, pNext, &p->vPath, SlackMax );
    }
    return Vec_IntSize(&p->vPath);
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sfm_TimTrace( Sfm_Tim_t * p )
{
    Abc_Obj_t * pObj; int i, Delay = 0;
    Vec_Ptr_t * vNodes = Abc_NtkDfs( p->pNtk, 1 );
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pObj, i )
        Sfm_TimGateArrival( p, pObj );
    Abc_NtkForEachCo( p->pNtk, pObj, i )
        Delay = Abc_MaxInt( Delay, Sfm_TimArrMax(p, Abc_ObjFanin0(pObj)) );
    Abc_NtkForEachCo( p->pNtk, pObj, i )
        Sfm_TimSetReq( p, Abc_ObjFanin0(pObj), Delay );
    Vec_PtrForEachEntryReverse( Abc_Obj_t *, vNodes, pObj, i )
        Sfm_TimGateRequired( p, pObj );
    Vec_PtrFree( vNodes );
    return Delay;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Sfm_Tim_t * Sfm_TimStart( Mio_Library_t * pLib, Scl_Con_t * pExt, Abc_Ntk_t * pNtk )
{
//    Abc_Obj_t * pObj; int i;
    Sfm_Tim_t * p = ABC_CALLOC( Sfm_Tim_t, 1 );
    p->pLib = pLib;
    p->pExt = pExt;
    p->pNtk = pNtk;
    Vec_IntFill( &p->vTimArrs,  2*Abc_NtkObjNumMax(pNtk), 0 );
    Vec_IntFill( &p->vTimReqs,  2*Abc_NtkObjNumMax(pNtk), 0 );
//    Vec_IntFill( &p->vTimSlews, 2*Abc_NtkObjNumMax(pNtk), 0 );
//    Vec_IntFill( &p->vTimLoads, 2*Abc_NtkObjNumMax(pNtk), 0 );
//    Vec_IntFill( &p->vObjOffs,  Abc_NtkObjNumMax(pNtk), 0 );
//    Abc_NtkForEachNode( pNtk, pObj, i )
//    {
//        Vec_IntWriteEntry( &p->vObjOffs, i, Vec_IntSize(Vec_IntSize(&p->vTimEdges)) );
//        Vec_IntFillExtra( &p->vTimEdges, Vec_IntSize(Vec_IntSize(&p->vTimEdges)) + Abc_ObjFaninNum(pObj), 0 );
//    }
    return p;
}
void Sfm_TimStop( Sfm_Tim_t * p )
{
    Vec_IntErase( &p->vTimArrs );
    Vec_IntErase( &p->vTimReqs );
    Vec_IntErase( &p->vTimSlews );
    Vec_IntErase( &p->vTimLoads );
    Vec_IntErase( &p->vObjOffs );
    Vec_IntErase( &p->vTimEdges );
    Vec_IntErase( &p->vPath );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sfm_TimTest( Abc_Ntk_t * pNtk )
{
    Mio_Library_t * pLib = (Mio_Library_t *)pNtk->pManFunc;
    Sfm_Tim_t * p = Sfm_TimStart( pLib, NULL, pNtk );
    p->Delay = Sfm_TimTrace( p );
    printf( "Max delay = %.2f.  Path = %d (%d).\n", MIO_NUMINV*p->Delay, Sfm_TimCriticalPath(p, 1), Abc_NtkNodeNum(p->pNtk) );
    Sfm_TimStop( p );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

