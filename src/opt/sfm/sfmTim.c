/**CFile****************************************************************

  FileName    [sfmTim.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based optimization using internal don't-cares.]

  Synopsis    [Timing manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: sfmTim.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sfmInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

struct Sfm_Tim_t_
{
    // external
    Mio_Library_t *   pLib;        // library
    Scl_Con_t *       pExt;        // external timing
    Abc_Ntk_t *       pNtk;        // mapped network
    int               Delay;       // the largest delay
    int               DeltaCrit;   // critical delay delta
    int               fAreaTarget; // use fixed output requirements for area recovery
    int               AreaTarget;  // fixed output requirement for area recovery
    int               nObjsOld;
    Vec_Int_t         vAffected;
    Vec_Ptr_t         vCone;
    Vec_Ptr_t         vSupport;
    // timing info
    Vec_Int_t         vTimArrs;    // arrivals (rise/fall)
    Vec_Int_t         vTimReqs;    // required (rise/fall)
    // incremental timing
    Vec_Wec_t         vLevels;     // levels
    // critical path
    Vec_Int_t         vPath;       // critical path
    Vec_Wrd_t         vSortData;   // node priority order
    // speculative timing of polarity changes, without modifying the network
    Vec_Int_t         vTrialArrs;
    Vec_Int_t         vTrialSeen;
    Vec_Int_t         vTrialPlans;
    int               nTrial;
    Abc_Obj_t *       pTrialPivot;
    Vec_Int_t *       pTrialPlan;
    Vec_Ptr_t *       pTrialHandles;
    int               TrialRoot[2];
    int               TrialInv[2];
};

static inline int * Sfm_TimArrId( Sfm_Tim_t * p, int Id )                    { return Vec_IntEntryP( &p->vTimArrs,  Abc_Var2Lit(Id, 0) );               }
static inline int * Sfm_TimReqId( Sfm_Tim_t * p, int Id )                    { return Vec_IntEntryP( &p->vTimReqs,  Abc_Var2Lit(Id, 0) );               }

static inline int * Sfm_TimArr( Sfm_Tim_t * p, Abc_Obj_t * pNode )           { return Vec_IntEntryP( &p->vTimArrs,  Abc_Var2Lit(Abc_ObjId(pNode), 0) ); }
static inline int * Sfm_TimReq( Sfm_Tim_t * p, Abc_Obj_t * pNode )           { return Vec_IntEntryP( &p->vTimReqs,  Abc_Var2Lit(Abc_ObjId(pNode), 0) ); }

static inline int   Sfm_TimArrMaxId( Sfm_Tim_t * p, int Id )                 { int * a = Sfm_TimArrId(p, Id); return Abc_MaxInt(a[0], a[1]);            }

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
static inline void Sfm_TimEdgeArrival( Sfm_Tim_t * p, Mio_Pin_t * pPin, int * pTimeIn, int * pTimeOut )
{
    Mio_PinPhase_t PinPhase = Mio_PinReadPhase(pPin);
    int tDelayBlockRise = Scl_Flt2Int(Mio_PinReadDelayBlockRise(pPin));  
    int tDelayBlockFall = Scl_Flt2Int(Mio_PinReadDelayBlockFall(pPin));  
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
static inline void Sfm_TimGateArrival( Sfm_Tim_t * p, Mio_Gate_t * pGate, int ** pTimesIn, int * pTimeOut )
{
    Mio_Pin_t * pPin;  int i = 0;
    pTimeOut[0] = pTimeOut[1] = 0;
    Mio_GateForEachPin( pGate, pPin )
        Sfm_TimEdgeArrival( p, pPin, pTimesIn[i++], pTimeOut );
    assert( i == Mio_GateReadPinNum(pGate) );
}
static inline void Sfm_TimNodeArrival( Sfm_Tim_t * p, Abc_Obj_t * pNode )
{
    int i, iFanin, * pTimesIn[6];
    int * pTimeOut = Sfm_TimArr(p, pNode);
    assert( Abc_ObjFaninNum(pNode) <= 6 );
    Abc_ObjForEachFaninId( pNode, iFanin, i )
        pTimesIn[i] = Sfm_TimArrId( p, iFanin );
    Sfm_TimGateArrival( p, (Mio_Gate_t *)pNode->pData, pTimesIn, pTimeOut );
}

static inline void Sfm_TimEdgeRequired( Sfm_Tim_t * p, Mio_Pin_t * pPin, int * pTimeIn, int * pTimeOut )
{
    Mio_PinPhase_t PinPhase = Mio_PinReadPhase(pPin);
    int tDelayBlockRise = Scl_Flt2Int(Mio_PinReadDelayBlockRise(pPin));  
    int tDelayBlockFall = Scl_Flt2Int(Mio_PinReadDelayBlockFall(pPin));  
    if ( PinPhase != MIO_PHASE_INV )  // NONINV phase is present
    {
        pTimeIn[0] = Abc_MinInt( pTimeIn[0], pTimeOut[0] - tDelayBlockRise );
        pTimeIn[1] = Abc_MinInt( pTimeIn[1], pTimeOut[1] - tDelayBlockFall );
    }
    if ( PinPhase != MIO_PHASE_NONINV )  // INV phase is present
    {
        pTimeIn[0] = Abc_MinInt( pTimeIn[0], pTimeOut[1] - tDelayBlockFall );
        pTimeIn[1] = Abc_MinInt( pTimeIn[1], pTimeOut[0] - tDelayBlockRise );
    }
}
static inline void Sfm_TimGateRequired( Sfm_Tim_t * p, Mio_Gate_t * pGate, int ** pTimesIn, int * pTimeOut )
{
    Mio_Pin_t * pPin;  int i = 0;
    Mio_GateForEachPin( pGate, pPin )
        Sfm_TimEdgeRequired( p, pPin, pTimesIn[i++], pTimeOut );
    assert( i == Mio_GateReadPinNum(pGate) );
}
void Sfm_TimNodeRequired( Sfm_Tim_t * p, Abc_Obj_t * pNode )
{
    int i, iFanin, * pTimesIn[6];
    int * pTimeOut = Sfm_TimReq(p, pNode);
    assert( Abc_ObjFaninNum(pNode) <= 6 );
    Abc_ObjForEachFaninId( pNode, iFanin, i )
        pTimesIn[i] = Sfm_TimReqId( p, iFanin );
    Sfm_TimGateRequired( p, (Mio_Gate_t *)pNode->pData, pTimesIn, pTimeOut );
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
        Sfm_TimNodeArrival( p, pObj );
    Abc_NtkForEachCo( p->pNtk, pObj, i )
        Delay = Abc_MaxInt( Delay, Sfm_TimArrMax(p, Abc_ObjFanin0(pObj)) );
    Vec_IntFill( &p->vTimReqs, 2*Abc_NtkObjNumMax(p->pNtk), ABC_INFINITY );
    Abc_NtkForEachCo( p->pNtk, pObj, i )
        Sfm_TimSetReq( p, Abc_ObjFanin0(pObj), p->fAreaTarget ? p->AreaTarget : Delay );
    Vec_PtrForEachEntryReverse( Abc_Obj_t *, vNodes, pObj, i )
        Sfm_TimNodeRequired( p, pObj );
    Vec_PtrFree( vNodes );
    return Delay;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Sfm_Tim_t * Sfm_TimStart( Mio_Library_t * pLib, Scl_Con_t * pExt, Abc_Ntk_t * pNtk, int DeltaCrit )
{
    Sfm_Tim_t * p = ABC_CALLOC( Sfm_Tim_t, 1 );
    p->pLib = pLib;
    p->pExt = pExt;
    p->pNtk = pNtk;
    Vec_IntFill( &p->vTimArrs,  3*Abc_NtkObjNumMax(pNtk), 0 );
    Vec_IntFill( &p->vTimReqs,  3*Abc_NtkObjNumMax(pNtk), 0 );
    p->Delay = Sfm_TimTrace( p );
    assert( DeltaCrit > 0 && DeltaCrit < Scl_Flt2Int(1000.0) );
    p->DeltaCrit = DeltaCrit;
    return p;
}
void Sfm_TimStop( Sfm_Tim_t * p )
{
    Vec_IntErase( &p->vTimArrs );
    Vec_IntErase( &p->vTimReqs );
    Vec_WecErase( &p->vLevels );
    Vec_IntErase( &p->vPath );
    Vec_WrdErase( &p->vSortData );
    Vec_IntErase( &p->vAffected );
    Vec_PtrErase( &p->vCone );
    Vec_PtrErase( &p->vSupport );
    Vec_IntErase( &p->vTrialArrs );
    Vec_IntErase( &p->vTrialSeen );
    Vec_IntErase( &p->vTrialPlans );
    ABC_FREE( p );
}
int Sfm_TimReadNtkDelay( Sfm_Tim_t * p )
{
    return p->Delay;
}
int Sfm_TimReadObjDelay( Sfm_Tim_t * p, int iObj )
{
    return Sfm_TimArrMaxId(p, iObj);
}

/**Function*************************************************************

  Synopsis    [Fixes the initial maximum delay as the area-recovery bound.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sfm_TimSetAreaTarget( Sfm_Tim_t * p )
{
    p->fAreaTarget = 1;
    p->AreaTarget = p->Delay;
}

/**Function*************************************************************

  Synopsis    [Collects the timing boundary before replacing a cone.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sfm_TimPrepareArea( Sfm_Tim_t * p, Abc_Obj_t * pPivot )
{
    Abc_Obj_t * pObj, * pNext;
    int i, k;
    p->nObjsOld = Abc_NtkObjNumMax(p->pNtk);
    Vec_IntClear( &p->vAffected );
    // Include the boundary of the removed cone, so its requirements can relax.
    Abc_NodeDeref_rec( pPivot );
    Abc_NodeMffcConeSupp( pPivot, &p->vCone, &p->vSupport );
    Abc_NodeRef_rec( pPivot );
    Vec_PtrForEachEntry( Abc_Obj_t *, &p->vCone, pObj, i )
        Vec_IntPush( &p->vAffected, Abc_ObjId(pObj) );
    Vec_PtrForEachEntry( Abc_Obj_t *, &p->vSupport, pObj, i )
        Vec_IntPush( &p->vAffected, Abc_ObjId(pObj) );
    Abc_ObjForEachFanout( pPivot, pObj, i )
    {
        Vec_IntPush( &p->vAffected, Abc_ObjId(pObj) );
        // A fanout inverter can disappear during a polarity change.
        Abc_ObjForEachFanout( pObj, pNext, k )
            Vec_IntPush( &p->vAffected, Abc_ObjId(pNext) );
    }
}

/**Function*************************************************************

  Synopsis    [Queues an affected node once at its current logic level.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Sfm_TimQueueArea( Sfm_Tim_t * p, Abc_Obj_t * pObj )
{
    if ( pObj == NULL || !Abc_ObjIsNode(pObj) || pObj->fMarkC )
        return;
    pObj->fMarkC = 1;
    Vec_WecPush( &p->vLevels, pObj->Level, Abc_ObjId(pObj) );
}

/**Function*************************************************************

  Synopsis    [Derives rise/fall requirements from the current fanouts.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Sfm_TimRequiredFromFanouts( Sfm_Tim_t * p, Abc_Obj_t * pObj, int * pReq )
{
    Abc_Obj_t * pFanout;
    Mio_Pin_t * pPin;
    int i, k;
    pReq[0] = pReq[1] = ABC_INFINITY;
    Abc_ObjForEachFanout( pObj, pFanout, i )
    {
        if ( Abc_ObjIsCo(pFanout) )
        {
            pReq[0] = Abc_MinInt( pReq[0], p->AreaTarget );
            pReq[1] = Abc_MinInt( pReq[1], p->AreaTarget );
            continue;
        }
        k = 0;
        Mio_GateForEachPin( (Mio_Gate_t *)pFanout->pData, pPin )
        {
            if ( Abc_ObjFanin(pFanout, k) == pObj )
                Sfm_TimEdgeRequired( p, pPin, pReq, Sfm_TimReq(p, pFanout) );
            k++;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Propagates timing after an accepted area replacement.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sfm_TimUpdateArea( Sfm_Tim_t * p )
{
    extern void Abc_NtkUpdateIncLevel_rec( Abc_Obj_t * pObj );
    Abc_Obj_t * pObj, * pNext;
    int i, k, Id, Old[2], New[2], * pTime;
    Vec_IntFillExtra( &p->vTimArrs, 2*Abc_NtkObjNumMax(p->pNtk), 0 );
    Vec_IntFillExtra( &p->vTimReqs, 2*Abc_NtkObjNumMax(p->pNtk), ABC_INFINITY );
    for ( i = p->nObjsOld; i < Abc_NtkObjNumMax(p->pNtk); i++ )
    {
        Vec_IntPush( &p->vAffected, i );
        pObj = Abc_NtkObj( p->pNtk, i );
        if ( pObj && Abc_ObjIsNode(pObj) )
            Abc_NtkUpdateIncLevel_rec( pObj );
    }
    Vec_IntForEachEntry( &p->vAffected, Id, i )
    {
        pObj = Abc_NtkObj( p->pNtk, Id );
        if ( pObj && Abc_ObjIsNode(pObj) )
            Abc_NtkUpdateIncLevel_rec( pObj );
    }
    Vec_IntForEachEntry( &p->vAffected, Id, i )
        Sfm_TimQueueArea( p, Abc_NtkObj(p->pNtk, Id) );
    for ( i = 0; i < Vec_WecSize(&p->vLevels); i++ )
        while ( Vec_IntSize(Vec_WecEntry(&p->vLevels, i)) )
        {
            pObj = Abc_NtkObj( p->pNtk, Vec_IntPop(Vec_WecEntry(&p->vLevels, i)) );
            pObj->fMarkC = 0;
            pTime = Sfm_TimArr(p, pObj);
            Old[0] = pTime[0]; Old[1] = pTime[1];
            Sfm_TimNodeArrival( p, pObj );
            if ( Old[0] != pTime[0] || Old[1] != pTime[1] )
                Abc_ObjForEachFanout( pObj, pNext, k )
                    Sfm_TimQueueArea( p, pNext );
        }
    Vec_IntForEachEntry( &p->vAffected, Id, i )
    {
        pObj = Abc_NtkObj( p->pNtk, Id );
        if ( pObj == NULL )
            continue;
        Sfm_TimQueueArea( p, pObj );
        // Changed cells may tighten input requirements even when their own
        // output requirements stay the same.
        Abc_ObjForEachFanin( pObj, pNext, k )
            Sfm_TimQueueArea( p, pNext );
    }
    for ( i = Vec_WecSize(&p->vLevels)-1; i >= 0; i-- )
        while ( Vec_IntSize(Vec_WecEntry(&p->vLevels, i)) )
        {
            pObj = Abc_NtkObj( p->pNtk, Vec_IntPop(Vec_WecEntry(&p->vLevels, i)) );
            pObj->fMarkC = 0;
            pTime = Sfm_TimReq(p, pObj);
            Sfm_TimRequiredFromFanouts( p, pObj, New );
            if ( New[0] == pTime[0] && New[1] == pTime[1] )
                continue;
            pTime[0] = New[0]; pTime[1] = New[1];
            Abc_ObjForEachFanin( pObj, pNext, k )
                Sfm_TimQueueArea( p, pNext );
        }
    p->Delay = 0;
    Abc_NtkForEachCo( p->pNtk, pObj, i )
        p->Delay = Abc_MaxInt( p->Delay, Sfm_TimArrMax(p, Abc_ObjFanin0(pObj)) );
    assert( p->Delay <= p->AreaTarget );
}

/**Function*************************************************************

  Synopsis    [Checks incremental timing against a full timing trace.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
#ifndef NDEBUG
void Sfm_TimCheckAreaEnd( Sfm_Tim_t * p )
{
    Vec_Int_t * vArrs = Vec_IntDup( &p->vTimArrs );
    Vec_Int_t * vReqs = Vec_IntDup( &p->vTimReqs );
    Abc_Obj_t * pObj; int i;
    int Delay = Sfm_TimTrace( p );
    assert( Delay == p->Delay && Delay <= p->AreaTarget );
    Abc_NtkForEachNode( p->pNtk, pObj, i )
    {
        assert( Vec_IntEntry(vArrs, 2*i) == Sfm_TimArr(p, pObj)[0] );
        assert( Vec_IntEntry(vArrs, 2*i+1) == Sfm_TimArr(p, pObj)[1] );
        assert( Vec_IntEntry(vReqs, 2*i) == Sfm_TimReq(p, pObj)[0] );
        assert( Vec_IntEntry(vReqs, 2*i+1) == Sfm_TimReq(p, pObj)[1] );
    }
    Vec_IntFree( vArrs );
    Vec_IntFree( vReqs );
}
#endif

/**Function*************************************************************

  Synopsis    [Computes speculative arrival times for a polarity plan.]

  Description [Recomputes reconvergent inputs of changed fanouts because
  their old arrival times may change with the pivot or another fanout.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int * Sfm_TimTrialArrival( Sfm_Tim_t * p, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanin;
    Mio_Gate_t * pGate;
    int * pTimes[6], * pPermuted[6], * pOut, * pPlan = NULL, i, Plan;
    if ( pObj == p->pTrialPivot )
        return p->TrialInv;
    if ( Abc_ObjIsCi(pObj) || pObj->Level < p->pTrialPivot->Level )
        return Sfm_TimArr(p, pObj);
    pOut = Vec_IntEntryP( &p->vTrialArrs, 2*Abc_ObjId(pObj) );
    if ( Vec_IntEntry(&p->vTrialSeen, Abc_ObjId(pObj)) == p->nTrial )
        return pOut;
    Plan = Vec_IntEntry( &p->vTrialPlans, Abc_ObjId(pObj) );
    if ( Plan >= 0 )
        pPlan = Vec_IntEntryP( p->pTrialPlan, Plan );
    if ( pPlan && pPlan[1] == -1 )
    {
        pOut[0] = p->TrialRoot[0];
        pOut[1] = p->TrialRoot[1];
    }
    else
    {
        assert( Abc_ObjFaninNum(pObj) <= 6 );
        Abc_ObjForEachFanin( pObj, pFanin, i )
            pTimes[i] = pPlan && i == pPlan[2] ? p->TrialRoot : Sfm_TimTrialArrival(p, pFanin);
        if ( pPlan )
            for ( i = 0; i < Abc_ObjFaninNum(pObj); i++ )
                pPermuted[i] = pTimes[(pPlan[3] >> (4*i)) & 15];
        pGate = pPlan ? (Mio_Gate_t *)Vec_PtrEntry(p->pTrialHandles, pPlan[1]) : (Mio_Gate_t *)pObj->pData;
        Sfm_TimGateArrival( p, pGate, pPlan ? pPermuted : pTimes, pOut );
    }
    Vec_IntWriteEntry( &p->vTrialSeen, Abc_ObjId(pObj), p->nTrial );
    return pOut;
}

/**Function*************************************************************

  Synopsis    [Checks both transitions against a node's required times.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Sfm_TimMeetsRequired( Sfm_Tim_t * p, Abc_Obj_t * pObj, int * pArr )
{
    int * pReq = Sfm_TimReq(p, pObj);
    return pArr[0] <= pReq[0] && pArr[1] <= pReq[1];
}

/**Function*************************************************************

  Synopsis    [Checks a proposed area replacement without changing logic.]

  Description [Includes the candidate gates, an optional output inverter,
  and the proposed changes to fanout cells and their pin order.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sfm_TimCheckArea( Sfm_Tim_t * p, Abc_Obj_t * pPivot, Vec_Int_t * vGates, Vec_Wec_t * vFanins, Vec_Int_t * vMap, Vec_Ptr_t * vHandles, int GateBuf, int fCompl, int fKeepInv, Vec_Int_t * vPlan )
{
    int Times[2][2], * pInputs[6], * pOut, i, k, Gate, Fanin, fPass = 1;
    int Limit = Vec_IntSize(vMap), nNew = Vec_IntSize(vGates) - Limit;
    assert( nNew > 0 && nNew <= 2 );
    Vec_IntForEachEntryStart( vGates, Gate, i, Limit )
    {
        Vec_IntForEachEntry( Vec_WecEntry(vFanins, i), Fanin, k )
            pInputs[k] = Fanin < Limit ? Sfm_TimArrId(p, Vec_IntEntry(vMap, Fanin)) : Times[Fanin-Limit];
        if ( nNew == 1 && Gate == GateBuf ) // insertion bypasses this buffer
        {
            Times[0][0] = pInputs[0][0];
            Times[0][1] = pInputs[0][1];
        }
        else
            Sfm_TimGateArrival( p, (Mio_Gate_t *)Vec_PtrEntry(vHandles, Gate), pInputs, Times[i-Limit] );
    }
    pOut = Times[nNew-1];
    if ( !fCompl )
        return Sfm_TimMeetsRequired(p, pPivot, pOut);
    p->TrialRoot[0] = pOut[0];
    p->TrialRoot[1] = pOut[1];
    pInputs[0] = pOut;
    Sfm_TimGateArrival( p, Mio_LibraryReadInv(p->pLib), pInputs, p->TrialInv );
    if ( fKeepInv && !Sfm_TimMeetsRequired(p, pPivot, p->TrialInv) )
        return 0;
    Vec_IntFillExtra( &p->vTrialArrs, 2*Abc_NtkObjNumMax(p->pNtk), 0 );
    Vec_IntFillExtra( &p->vTrialSeen, Abc_NtkObjNumMax(p->pNtk), 0 );
    Vec_IntFillExtra( &p->vTrialPlans, Abc_NtkObjNumMax(p->pNtk), -1 );
    if ( ++p->nTrial == ABC_INFINITY )
    {
        Vec_IntFill( &p->vTrialSeen, Abc_NtkObjNumMax(p->pNtk), 0 );
        p->nTrial = 1;
    }
    p->pTrialPivot = pPivot;
    p->pTrialPlan = vPlan;
    p->pTrialHandles = vHandles;
    for ( i = 0; i < Vec_IntSize(vPlan); i += 5 )
        Vec_IntWriteEntry( &p->vTrialPlans, Vec_IntEntry(vPlan, i), i );
    for ( i = 0; i < Vec_IntSize(vPlan); i += 5 )
    {
        Abc_Obj_t * pFanout = Abc_NtkObj( p->pNtk, Vec_IntEntry(vPlan, i) );
        if ( !Sfm_TimMeetsRequired(p, pFanout, Sfm_TimTrialArrival(p, pFanout)) )
        {
            fPass = 0;
            break;
        }
    }
    for ( i = 0; i < Vec_IntSize(vPlan); i += 5 )
        Vec_IntWriteEntry( &p->vTrialPlans, Vec_IntEntry(vPlan, i), -1 );
    return fPass;
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
    Sfm_Tim_t * p = Sfm_TimStart( pLib, NULL, pNtk, 100 );
    printf( "Max delay = %.2f.  Path = %d (%d).\n", Scl_Int2Flt(p->Delay), Sfm_TimCriticalPath(p, 1), Abc_NtkNodeNum(p->pNtk) );
    Sfm_TimStop( p );
}

/**Function*************************************************************

  Synopsis    [Levelized structure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Sfm_TimUpdateClean( Sfm_Tim_t * p )
{
    Vec_Int_t * vLevel;
    Abc_Obj_t * pObj;
    int i, k;
    Vec_WecForEachLevel( &p->vLevels, vLevel, i )
    {
        Abc_NtkForEachObjVec( vLevel, p->pNtk, pObj, k )
        {
            assert( pObj->fMarkC == 1 );
            pObj->fMarkC = 0;
        }
        Vec_IntClear( vLevel );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sfm_TimUpdateTiming( Sfm_Tim_t * p, Vec_Int_t * vTimeNodes )
{
    assert( Vec_IntSize(vTimeNodes) > 0 && Vec_IntSize(vTimeNodes) <= 2 );
    Vec_IntFillExtra( &p->vTimArrs, 2*Abc_NtkObjNumMax(p->pNtk), 0 );
    Vec_IntFillExtra( &p->vTimReqs, 2*Abc_NtkObjNumMax(p->pNtk), 0 );
    p->Delay = Sfm_TimTrace( p );
}

/**Function*************************************************************

  Synopsis    [Sort an array of nodes using their max arrival times.]

  Description [Returns the number of new divisor nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sfm_TimSortArrayByArrival( Sfm_Tim_t * p, Vec_Int_t * vNodes, int iPivot )
{
    word Entry; 
    int i, Id, Time, nDivNew = -1; 
    int MaxDelay = ABC_INFINITY/2+Sfm_TimArrMaxId(p, iPivot);
    assert( p->DeltaCrit > 0 );
    // collect nodes
    Vec_WrdClear( &p->vSortData );
    Vec_IntForEachEntry( vNodes, Id, i )
    {
        Time = Sfm_TimArrMaxId( p, Id );
        assert( -ABC_INFINITY/2 < Time && Time < ABC_INFINITY/2 );
        Vec_WrdPush( &p->vSortData, ((word)Id << 32) | (ABC_INFINITY/2+Time) );
    }
    // sort nodes by delay
    Abc_QuickSort3( Vec_WrdArray(&p->vSortData), Vec_WrdSize(&p->vSortData), 0 );
    // collect sorted nodes and find place where divisors end
    Vec_IntClear( vNodes );
    Vec_WrdForEachEntry( &p->vSortData, Entry, i )
    {
        Vec_IntPush( vNodes, (int)(Entry >> 32) );
        if ( nDivNew == -1 && ((int)Entry) + p->DeltaCrit > MaxDelay )
            nDivNew = i;
    }
    return nDivNew == -1 ? Vec_IntSize(vNodes) : nDivNew;
}

/**Function*************************************************************

  Synopsis    [Priority of nodes to try remapping for delay.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sfm_TimPriorityNodes( Sfm_Tim_t * p, Vec_Int_t * vCands, int Window )
{
    Vec_Int_t * vLevel;
    Abc_Obj_t * pObj;
    int i, k;
    assert( Window >= 0 && Window <= 100 );
    // collect critical path
    Sfm_TimCriticalPath( p, Window );
    // add nodes to the levelized structure
    Sfm_TimUpdateClean( p );
    Abc_NtkForEachObjVec( &p->vPath, p->pNtk, pObj, i )
    {
        assert( pObj->fMarkC == 0 );
        pObj->fMarkC = 1;
        Vec_WecPush( &p->vLevels, Abc_ObjLevel(pObj), Abc_ObjId(pObj) );
    }
    // prioritize nodes by expected gain
    Vec_WecSort( &p->vLevels, 0 );
    Vec_IntClear( vCands );
    Vec_WecForEachLevel( &p->vLevels, vLevel, i )
        Abc_NtkForEachObjVec( vLevel, p->pNtk, pObj, k )
            if ( !pObj->fMarkA )
                Vec_IntPush( vCands, Abc_ObjId(pObj) );
//    printf( "Path = %5d   Cand = %5d\n", Vec_IntSize(&p->vPath) );
    return Vec_IntSize(vCands) > 0;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if node is relatively non-critical compared to the pivot.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sfm_TimNodeIsNonCritical( Sfm_Tim_t * p, Abc_Obj_t * pPivot, Abc_Obj_t * pNode )
{
    return Sfm_TimArrMax(p, pNode) + p->DeltaCrit <= Sfm_TimArrMax(p, pPivot);
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sfm_TimEvalRemapping( Sfm_Tim_t * p, Vec_Int_t * vFanins, Vec_Int_t * vMap, Mio_Gate_t * pGate1, char * pFans1, Mio_Gate_t * pGate2, char * pFans2 )
{
    int TimeOut[2][2];
    int * pTimesIn1[6], * pTimesIn2[6];
    int i, nFanins1, nFanins2;
    // process the first gate
    nFanins1 = Mio_GateReadPinNum( pGate1 );
    for ( i = 0; i < nFanins1; i++ )
        pTimesIn1[i] = Sfm_TimArrId( p, Vec_IntEntry(vMap, Vec_IntEntry(vFanins, (int)pFans1[i])) );
    Sfm_TimGateArrival( p, pGate1, pTimesIn1, TimeOut[0] );
    if ( pGate2 == NULL )
        return Abc_MaxInt(TimeOut[0][0], TimeOut[0][1]);
    // process the second gate
    nFanins2 = Mio_GateReadPinNum( pGate2 );
    for ( i = 0; i < nFanins2; i++ )
        if ( (int)pFans2[i] == 16 )
            pTimesIn2[i] = TimeOut[0];
        else
            pTimesIn2[i] = Sfm_TimArrId( p, Vec_IntEntry(vMap, Vec_IntEntry(vFanins, (int)pFans2[i])) );
    Sfm_TimGateArrival( p, pGate2, pTimesIn2, TimeOut[1] );
    return Abc_MaxInt(TimeOut[1][0], TimeOut[1][1]);
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

