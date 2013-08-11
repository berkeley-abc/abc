/**CFile****************************************************************

  FileName    [sclBufSize.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Standard-cell library representation.]

  Synopsis    [Buffering and sizing combined.]

  Author      [Alan Mishchenko, Niklas Een]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 24, 2012.]

  Revision    [$Id: sclBufSize.c,v 1.0 2012/08/24 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sclSize.h"
#include "map/mio/mio.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Bus_Man_t_ Bus_Man_t;
struct Bus_Man_t_
{
    // user data
    SC_BusPars *   pPars;      // parameters    
    Abc_Ntk_t *    pNtk;       // user's network
    // library
    SC_Lib *       pLib;       // cell library
    SC_Cell *      pInv;       // base interter (largest/average/???)
    SC_WireLoad *  pWLoadUsed; // name of the used WireLoad model
    Vec_Flt_t *    vWireCaps;  // estimated wire loads
    // internal
    Vec_Flt_t *    vCins;      // input cap for fanouts
    Vec_Flt_t *    vETimes;    // fanout edge departures
    Vec_Flt_t *    vLoads;     // loads for all nodes
    Vec_Flt_t *    vDepts;     // departure times
    Vec_Ptr_t *    vFanouts;   // fanout array
};


static inline Bus_Man_t * Bus_SclObjMan( Abc_Obj_t * p )                     { return (Bus_Man_t *)p->pNtk->pBSMan;                                  }
static inline float       Bus_SclObjCin( Abc_Obj_t * p )                     { return Vec_FltEntry( Bus_SclObjMan(p)->vCins, Abc_ObjId(p) );         }
static inline void        Bus_SclObjSetCin( Abc_Obj_t * p, float cap )       { Vec_FltWriteEntry( Bus_SclObjMan(p)->vCins, Abc_ObjId(p), cap );      }
static inline float       Bus_SclObjETime( Abc_Obj_t * p )                   { return Vec_FltEntry( Bus_SclObjMan(p)->vETimes, Abc_ObjId(p) );       }
static inline void        Bus_SclObjSetETime( Abc_Obj_t * p, float time )    { Vec_FltWriteEntry( Bus_SclObjMan(p)->vETimes, Abc_ObjId(p), time );   }
static inline float       Bus_SclObjLoad( Abc_Obj_t * p )                    { return Vec_FltEntry( Bus_SclObjMan(p)->vLoads, Abc_ObjId(p) );        }
static inline void        Bus_SclObjSetLoad( Abc_Obj_t * p, float cap )      { Vec_FltWriteEntry( Bus_SclObjMan(p)->vLoads, Abc_ObjId(p), cap );     }
static inline float       Bus_SclObjDept( Abc_Obj_t * p )                    { return Vec_FltEntry( Bus_SclObjMan(p)->vDepts, Abc_ObjId(p) );        }
static inline void        Bus_SclObjUpdateDept( Abc_Obj_t * p, float time )  { float *q = Vec_FltEntryP( Bus_SclObjMan(p)->vDepts, Abc_ObjId(p) ); if (*q < time) *q = time;  }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Bus_Man_t * Bus_ManStart( Abc_Ntk_t * pNtk, SC_Lib * pLib, SC_BusPars * pPars )
{
    Bus_Man_t * p;
    p = ABC_CALLOC( Bus_Man_t, 1 );
    p->pPars     = pPars;
    p->pNtk      = pNtk;
    p->pLib      = pLib;
    p->pInv      = Abc_SclFindInvertor(pLib, pPars->fAddBufs)->pAve;
    if ( pPars->fUseWireLoads )
    { 
        if ( pNtk->pWLoadUsed == NULL )
        {            
            p->pWLoadUsed = Abc_SclFindWireLoadModel( pLib, Abc_SclGetTotalArea(pNtk) );
            pNtk->pWLoadUsed = Abc_UtilStrsav( p->pWLoadUsed->pName );
        }
        else
            p->pWLoadUsed = Abc_SclFetchWireLoadModel( pLib, pNtk->pWLoadUsed );
    }
    if ( p->pWLoadUsed )
    p->vWireCaps = Abc_SclFindWireCaps( p->pWLoadUsed );
    p->vCins     = Vec_FltStart( 2*Abc_NtkObjNumMax(pNtk) + 1000 );
    p->vETimes   = Vec_FltStart( 2*Abc_NtkObjNumMax(pNtk) + 1000 );
    p->vLoads    = Vec_FltStart( 2*Abc_NtkObjNumMax(pNtk) + 1000 );
    p->vDepts    = Vec_FltStart( 2*Abc_NtkObjNumMax(pNtk) + 1000 );
    p->vFanouts  = Vec_PtrAlloc( 100 );
    pNtk->pBSMan = p;
    return p;
}
void Bus_ManStop( Bus_Man_t * p )
{
    Vec_PtrFreeP( &p->vFanouts );
    Vec_FltFreeP( &p->vWireCaps );
    Vec_FltFreeP( &p->vCins );
    Vec_FltFreeP( &p->vETimes );
    Vec_FltFreeP( &p->vLoads );
    Vec_FltFreeP( &p->vDepts );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Bus_ManReadInOutLoads( Bus_Man_t * p )
{
    Abc_Time_t * pTime;
    Abc_Obj_t * pObj;
    int i;
    if ( p->pNtk->pManTime == NULL )
        return;
    // read input load
    pTime = Abc_NtkReadDefaultInputDrive( p->pNtk );
    if ( Abc_MaxFloat(pTime->Rise, pTime->Fall) != 0 )
    {
        printf( "Default input drive strength is specified (%.2f ff; %.2f ff).\n", pTime->Rise, pTime->Fall );
        Abc_NtkForEachPi( p->pNtk, pObj, i )
            Bus_SclObjSetCin( pObj, SC_LibCapFromFf(p->pLib, 0.5 * pTime->Rise + 0.5 * pTime->Fall) );
    }
    if ( Abc_NodeReadInputDrive(p->pNtk, 0) != NULL )
    {
        printf( "Input drive strengths for some primary inputs are specified.\n" );
        Abc_NtkForEachPi( p->pNtk, pObj, i )
        {
            pTime = Abc_NodeReadInputDrive(p->pNtk, i);
            Bus_SclObjSetCin( pObj, SC_LibCapFromFf(p->pLib, 0.5 * pTime->Rise + 0.5 * pTime->Fall) );
        }
    }
    // read output load
    pTime = Abc_NtkReadDefaultOutputLoad( p->pNtk );
    if ( Abc_MaxFloat(pTime->Rise, pTime->Fall) != 0 )
    {
        printf( "Default output load is specified (%.2f ff; %.2f ff).\n", pTime->Rise, pTime->Fall );
        Abc_NtkForEachPo( p->pNtk, pObj, i )
            Bus_SclObjSetCin( pObj, SC_LibCapFromFf(p->pLib, 0.5 * pTime->Rise + 0.5 * pTime->Fall) );
    }
    if ( Abc_NodeReadOutputLoad(p->pNtk, 0) != NULL )
    {
        printf( "Output loads for some primary outputs are specified.\n" );
        Abc_NtkForEachPo( p->pNtk, pObj, i )
        {
            pTime = Abc_NodeReadOutputLoad(p->pNtk, i);
            Bus_SclObjSetCin( pObj, SC_LibCapFromFf(p->pLib, 0.5 * pTime->Rise + 0.5 * pTime->Fall) );
        }
    }
    // read arrival/required times
}

/**Function*************************************************************

  Synopsis    [Compute load and departure times of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline float Abc_NtkComputeEdgeDept( Abc_Obj_t * pFanout, int iFanin, float Slew )
{
    float Load = Bus_SclObjLoad( pFanout );
    float Dept = Bus_SclObjDept( pFanout );
    float Edge = Scl_LibPinArrivalEstimate( Abc_SclObjCell(pFanout), iFanin, Slew, Load );
//if ( Abc_ObjFaninNum(pFanout) == 0 )
//printf( "Edge = %.2f\n", Edge );
    assert( Edge > 0 );
    return Dept + Edge;
}
float Abc_NtkComputeNodeDeparture( Abc_Obj_t * pObj, float Slew )
{
    Abc_Obj_t * pFanout;
    int i;
    assert( Bus_SclObjDept(pObj) == 0 );
    Abc_ObjForEachFanout( pObj, pFanout, i )
        if ( !Abc_ObjIsCo(pFanout) ) // add required times here
            Bus_SclObjUpdateDept( pObj, Abc_NtkComputeEdgeDept(pFanout, Abc_NodeFindFanin(pFanout, pObj), Slew) );
    return Bus_SclObjDept( pObj );
}
void Abc_NtkComputeFanoutInfo( Abc_Obj_t * pObj, float Slew )
{
    Abc_Obj_t * pFanout;
    int i;
    Abc_ObjForEachFanout( pObj, pFanout, i )
        if ( !Abc_ObjIsCo(pFanout) )
        {
            int iFanin = Abc_NodeFindFanin(pFanout, pObj);;
            Bus_SclObjSetETime( pFanout, Abc_NtkComputeEdgeDept(pFanout, iFanin, Slew) );
            Bus_SclObjSetCin( pFanout, SC_CellPinCap( Abc_SclObjCell(pFanout), iFanin ) );
        }
}
float Abc_NtkComputeNodeLoad( Bus_Man_t * p, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanout;
    float Load;
    int i;
    assert( Bus_SclObjLoad(pObj) == 0 );
    Load = Abc_SclFindWireLoad( p->vWireCaps, Abc_ObjFanoutNum(pObj) );
    Abc_ObjForEachFanout( pObj, pFanout, i )
        Load += Bus_SclObjCin( pFanout );
    Bus_SclObjSetLoad( pObj, Load );
    return Load;
}
float Abc_NtkComputeFanoutLoad( Bus_Man_t * p, Vec_Ptr_t * vFanouts )
{
    Abc_Obj_t * pFanout;
    float Load;
    int i;
    Load = Abc_SclFindWireLoad( p->vWireCaps, Vec_PtrSize(vFanouts) );
    Vec_PtrForEachEntry( Abc_Obj_t *, vFanouts, pFanout, i )
        Load += Bus_SclObjCin( pFanout );
    return Load;
}
void Abc_NtkPrintFanoutProfile( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanout;
    int i;
    printf( "Obj %6d fanouts (%d): ", Abc_ObjId(pObj), Abc_ObjFanoutNum(pObj) );
    Abc_ObjForEachFanout( pObj, pFanout, i )
        printf( "%3d : time = %7.2f ps   load = %7.2f ff\n", i, Bus_SclObjETime(pFanout), Bus_SclObjCin(pFanout) );
    printf( "\n" );
}
void Abc_NtkPrintFanoutProfileVec( Vec_Ptr_t * vFanouts )
{
    Abc_Obj_t * pFanout;
    int i;
    printf( "Fanout profile (%d):\n", Vec_PtrSize(vFanouts) );
    Vec_PtrForEachEntry( Abc_Obj_t *, vFanouts, pFanout, i )
        printf( "%3d : time = %7.2f ps   load = %7.2f ff\n", i, Bus_SclObjETime(pFanout), Bus_SclObjCin(pFanout) );
}

/**Function*************************************************************

  Synopsis    [Compare two fanouts by their departure times.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Bus_SclCompareFanouts( Abc_Obj_t ** pp1, Abc_Obj_t ** pp2 )
{
    float Espilon = 0;//10; // 10 ps
    if ( Bus_SclObjETime(*pp1) < Bus_SclObjETime(*pp2) - Espilon )
        return -1;
    if ( Bus_SclObjETime(*pp1) > Bus_SclObjETime(*pp2) + Espilon )
        return 1;
    if ( Bus_SclObjCin(*pp1) > Bus_SclObjCin(*pp2) )
        return -1;
    if ( Bus_SclObjCin(*pp1) < Bus_SclObjCin(*pp2) )
        return 1;
    return -1;
}
void Bus_SclInsertFanout( Vec_Ptr_t * vFanouts, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pCur;
    int i, k;
    // compact array
    for ( i = k = 0; i < Vec_PtrSize(vFanouts); i++ )
        if ( Vec_PtrEntry(vFanouts, i) != NULL )
            Vec_PtrWriteEntry( vFanouts, k++, Vec_PtrEntry(vFanouts, i) );
    Vec_PtrShrink( vFanouts, k );
    // insert new entry
    Vec_PtrPush( vFanouts, pObj );
    for ( i = Vec_PtrSize(vFanouts) - 1; i > 0; i-- )
    {
        pCur = (Abc_Obj_t *)Vec_PtrEntry(vFanouts, i-1);
        pObj = (Abc_Obj_t *)Vec_PtrEntry(vFanouts, i);
        if ( Bus_SclCompareFanouts( &pCur, &pObj ) == -1 )
            break;
        ABC_SWAP( void *, Vec_PtrArray(vFanouts)[i-1], Vec_PtrArray(vFanouts)[i] );
    }
}
void Bus_SclCheckSortedFanout( Vec_Ptr_t * vFanouts )
{
    Abc_Obj_t * pObj, * pNext;
    int i;
    for ( i = 0; i < Vec_PtrSize(vFanouts) - 1; i++ )
    {
        pObj  = (Abc_Obj_t *)Vec_PtrEntry(vFanouts, i);
        pNext = (Abc_Obj_t *)Vec_PtrEntry(vFanouts, i+1);
        if ( Bus_SclCompareFanouts( &pObj, &pNext ) != -1 )
        {
            printf( "Fanouts %d and %d are out of order.\n", i, i+1 );
            Abc_NtkPrintFanoutProfileVec( vFanouts );
            return;
        }
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SclOneNodePrint( Bus_Man_t * p, Abc_Obj_t * pObj )
{
    SC_Cell * pCell = Abc_SclObjCell(pObj);
    printf( "%s%7d :  ",        (Abc_ObjFaninNum(pObj) == 0) ? " Inv" : "Node", Abc_ObjId(pObj) );
    printf( "%d/%2d   ",        Abc_ObjFaninNum(pObj) ? Abc_ObjFaninNum(pObj) : 1, Abc_ObjFanoutNum(pObj) );
    printf( "%12s ",            pCell->pName );
    printf( "(%2d/%2d)  ",      pCell->Order, pCell->nGates );
    printf( "gain =%5d  ",      (int)(100.0 * Bus_SclObjLoad(pObj) / SC_CellPinCapAve(pCell)) );
    printf( "dept =%7.0f ps  ", SC_LibTimePs(p->pLib, Bus_SclObjDept(pObj)) );
    printf( "\n" );
}
Abc_Obj_t * Abc_SclAddOneInv( Bus_Man_t * p, Abc_Obj_t * pObj, Vec_Ptr_t * vFanouts, float Gain )
{
    SC_Cell * pCellNew;
    Abc_Obj_t * pFanout, * pInv;
    float Target = SC_CellPinCap(p->pInv, 0) * Gain;
    float LoadWirePrev, LoadWireThis, LoadNew, Load = 0;
    int Limit = Abc_MinInt( p->pPars->nDegree, Vec_PtrSize(vFanouts) );
    int i, iStop;
    Bus_SclCheckSortedFanout( vFanouts );
    Vec_PtrForEachEntryStop( Abc_Obj_t *, vFanouts, pFanout, iStop, Limit )
    {
        LoadWirePrev = p->vWireCaps ? Vec_FltEntry(p->vWireCaps, iStop) : 0;
        LoadWireThis = p->vWireCaps ? Vec_FltEntry(p->vWireCaps, iStop+1) : 0;
        Load += Bus_SclObjCin( pFanout ) - LoadWirePrev + LoadWireThis;
        if ( Load > Target )
        {
            iStop++;
            break;
        }
    }
    // create inverter
    if ( p->pPars->fAddBufs )
        pInv = Abc_NtkCreateNodeBuf( p->pNtk, NULL );
    else
        pInv = Abc_NtkCreateNodeInv( p->pNtk, NULL );
    assert( (int)Abc_ObjId(pInv) < Vec_FltSize(p->vDepts) );
    Limit = Abc_MinInt( iStop, Vec_PtrSize(vFanouts) );
    Vec_PtrForEachEntryStop( Abc_Obj_t *, vFanouts, pFanout, i, Limit )
    {
        Vec_PtrWriteEntry( vFanouts, i, NULL );
        if ( Abc_ObjFaninNum(pFanout) == 0 )
            Abc_ObjAddFanin( pFanout, pInv );
        else
            Abc_ObjPatchFanin( pFanout, pObj, pInv );
    }
    // set the gate
    pCellNew = Abc_SclFindSmallestGate( p->pInv, Load / Gain );
    Vec_IntSetEntry( p->pNtk->vGates, Abc_ObjId(pInv), pCellNew->Id );
    // set departure and load
    Abc_NtkComputeNodeDeparture( pInv, p->pPars->Slew );
    LoadNew = Abc_NtkComputeNodeLoad( p, pInv );
    assert( LoadNew - Load < 1 && Load - LoadNew < 1 );
    // set fanout info for the inverter
    Bus_SclObjSetCin( pInv, SC_CellPinCap(pCellNew, 0) );
    Bus_SclObjSetETime( pInv, Abc_NtkComputeEdgeDept(pInv, 0, p->pPars->Slew) );
    // update phases
    if ( p->pNtk->vPhases && Abc_SclIsInv(pInv) )
        Abc_NodeInvUpdateFanPolarity( pInv );
    return pInv;
}
void Abc_SclBufSize( Bus_Man_t * p )
{
    SC_Cell * pCell, * pCellNew;
    Abc_Obj_t * pObj, * pFanout;
    abctime clk = Abc_Clock();
    float GainInv = 0.01 * p->pPars->GainRatio;
    float GainGate = (float)1.0 * GainInv;
    float Load, LoadNew, Cin, DeptMax = 0;
    int i, k, nObjOld = Abc_NtkObjNumMax(p->pNtk);
    Abc_SclMioGates2SclGates( p->pLib, p->pNtk );
    Abc_NtkForEachNodeReverse1( p->pNtk, pObj, i )
    {
        // compute load
        Abc_NtkComputeFanoutInfo( pObj, p->pPars->Slew );
        Load = Abc_NtkComputeNodeLoad( p, pObj );
        // consider the gate
        pCell = Abc_SclObjCell( pObj );
        Cin = SC_CellPinCapAve( pCell->pAve );
//        Cin = SC_CellPinCapAve( pCell->pRepr->pNext );
        // consider upsizing the gate
        if ( !p->pPars->fSizeOnly && (Abc_ObjFanoutNum(pObj) > p->pPars->nDegree || Load > GainGate * Cin) )
        {
            // add one or more inverters
            Abc_NodeCollectFanouts( pObj, p->vFanouts );
            Vec_PtrSort( p->vFanouts, (int(*)(void))Bus_SclCompareFanouts );
            do 
            {
                Abc_Obj_t * pInv;
                if ( p->pPars->fVeryVerbose )
                    Abc_NtkPrintFanoutProfileVec( p->vFanouts );
                pInv = Abc_SclAddOneInv( p, pObj, p->vFanouts, GainInv );
                if ( p->pPars->fVeryVerbose )
                    Abc_SclOneNodePrint( p, pInv );
                Bus_SclInsertFanout( p->vFanouts, pInv );
                Load = Abc_NtkComputeFanoutLoad( p, p->vFanouts );
            }
            while ( Vec_PtrSize(p->vFanouts) > p->pPars->nDegree || Load > GainGate * Cin );
            // update node fanouts
            Vec_PtrForEachEntry( Abc_Obj_t *, p->vFanouts, pFanout, k )
                if ( Abc_ObjFaninNum(pFanout) == 0 )
                    Abc_ObjAddFanin( pFanout, pObj );
            Bus_SclObjSetLoad( pObj, 0 );
            LoadNew = Abc_NtkComputeNodeLoad( p, pObj );
            assert( LoadNew - Load < 1 && Load - LoadNew < 1 );
        } 
        Abc_NtkComputeNodeDeparture( pObj, p->pPars->Slew );
        // create cell
        pCellNew = Abc_SclFindSmallestGate( pCell, Load / GainGate );
        Abc_SclObjSetCell( pObj, pCellNew );
        if ( p->pPars->fVeryVerbose )
            Abc_SclOneNodePrint( p, pObj );
        assert( p->pPars->fSizeOnly || Abc_ObjFanoutNum(pObj) <= p->pPars->nDegree );
    }
    Abc_NtkForEachCi( p->pNtk, pObj, i )
        DeptMax = Abc_MaxFloat( DeptMax, Abc_NtkComputeNodeDeparture(pObj, p->pPars->Slew) );
    Abc_SclSclGates2MioGates( p->pLib, p->pNtk );
    if ( p->pPars->fVerbose )
    {
        printf( "WireLoads = %d. Degree = %d.  Target gain =%5d  Slew =%5d   Inv = %6d  Delay =%7.0f ps   ", 
            p->pPars->fUseWireLoads, p->pPars->nDegree, p->pPars->GainRatio, p->pPars->Slew, 
            Abc_NtkObjNumMax(p->pNtk) - nObjOld, SC_LibTimePs(p->pLib, DeptMax) );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    }
}
Abc_Ntk_t * Abc_SclBufSizePerform( Abc_Ntk_t * pNtk, SC_Lib * pLib, SC_BusPars * pPars )
{
    Abc_Ntk_t * pNtkNew;
    Bus_Man_t * p;
    if ( !Abc_SclCheckNtk( pNtk, 0 ) )
        return NULL;
    Abc_SclReportDupFanins( pNtk );
    p = Bus_ManStart( pNtk, pLib, pPars );
    Bus_ManReadInOutLoads( p );
    Abc_SclBufSize( p );
    Bus_ManStop( p );
    if ( pNtk->vPhases )
        Vec_IntFillExtra( pNtk->vPhases, Abc_NtkObjNumMax(pNtk), 0 );
    pNtkNew = Abc_NtkDupDfs( pNtk );
    return pNtkNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

