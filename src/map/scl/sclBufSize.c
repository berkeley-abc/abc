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
    SC_BusPars *   pPars;     // parameters    
    Abc_Ntk_t *    pNtk;      // user's network
    // library
    SC_Lib *       pLib;      // cell library
    SC_Cell *      pInv;      // base interter (largest/average/???)
    // internal
    Vec_Flt_t *    vCins;     // input cap for fanouts
    Vec_Flt_t *    vLoads;    // loads for all nodes
    Vec_Flt_t *    vDepts;    // departure times
};


static inline Bus_Man_t * Bus_SclObjMan( Abc_Obj_t * p )                     { return (Bus_Man_t *)p->pNtk->pBSMan;                                  }
static inline float       Bus_SclObjCin( Abc_Obj_t * p )                     { return Vec_FltEntry( Bus_SclObjMan(p)->vCins, Abc_ObjId(p) );         }
static inline void        Bus_SclObjSetCin( Abc_Obj_t * p, float cap )       { Vec_FltWriteEntry( Bus_SclObjMan(p)->vCins, Abc_ObjId(p), cap );      }
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
    p->vCins     = Vec_FltStart( 2*Abc_NtkObjNumMax(pNtk) );
    p->vLoads    = Vec_FltStart( 2*Abc_NtkObjNumMax(pNtk) );
    p->vDepts    = Vec_FltStart( 2*Abc_NtkObjNumMax(pNtk) );
    pNtk->pBSMan = p;
    return p;
}
void Bus_ManStop( Bus_Man_t * p )
{
    Vec_FltFree( p->vCins );
    Vec_FltFree( p->vLoads );
    Vec_FltFree( p->vDepts );
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
void Abc_NtkComputeFanoutCins( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanout;
    int i;
    Abc_ObjForEachFanout( pObj, pFanout, i )
        if ( Abc_ObjIsNode(pFanout) )
        {
            float cap = SC_CellPinCap( Abc_SclObjCell(pFanout), Abc_NodeFindFanin(pFanout, pObj) );
            assert( cap > 0 );
            Bus_SclObjSetCin( pFanout, cap );
        }
}
float Abc_NtkComputeNodeLoad( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanout;
    float Load = 0;
    int i;
    assert( Bus_SclObjLoad(pObj) == 0 );
    Abc_ObjForEachFanout( pObj, pFanout, i )
        Load += Bus_SclObjCin( pFanout );
    Bus_SclObjSetLoad( pObj, Load );
    return Load;
}
float Abc_NtkComputeNodeDept( Abc_Obj_t * pObj, float Slew )
{
    Abc_Obj_t * pFanout;
    float Load, Dept, Edge;
    int i;
    assert( Bus_SclObjDept(pObj) == 0 );
    Abc_ObjForEachFanout( pObj, pFanout, i )
    {
        if ( Abc_ObjIsCo(pFanout) ) // add required times here
            continue;
        Load = Bus_SclObjLoad( pFanout );
        Dept = Bus_SclObjDept( pFanout );
        Edge = Scl_LibPinArrivalEstimate( Abc_SclObjCell(pFanout), Abc_NodeFindFanin(pFanout, pObj), Slew, Load );
        Bus_SclObjUpdateDept( pObj, Dept + Edge );
        assert( Edge > 0 );
//        assert( Load > 0 );
    }
    return Bus_SclObjDept( pObj );
}
/*
void Abc_NtkUpdateFaninDeparture( Bus_Man_t * p, Abc_Obj_t * pObj, float Load )
{
    SC_Cell * pCell = Abc_SclObjCell( pObj );
    Abc_Obj_t * pFanin;
    float Dept, Edge;
    int i;
    Dept = Bus_SclObjDept( pObj );
    Abc_ObjForEachFanin( pObj, pFanin, i )
    {
        Edge = Scl_LibPinArrivalEstimate( pCell, i, Load );
        Bus_SclObjUpdateDept( pFanin, Dept + Edge );
    }
}
*/

/**Function*************************************************************

  Synopsis    [Compare two fanouts by their departure times.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Bus_SclCompareFanouts( Abc_Obj_t ** pp1, Abc_Obj_t ** pp2 )
{
    float Espilon = 10; // 10 ps
    if ( Bus_SclObjDept(*pp1) < Bus_SclObjDept(*pp2) - Espilon )
        return -1;
    if ( Bus_SclObjDept(*pp1) > Bus_SclObjDept(*pp2) + Espilon )
        return 1;
    if ( Bus_SclObjCin(*pp1) > Bus_SclObjCin(*pp2) - Espilon )
        return -1;
    if ( Bus_SclObjCin(*pp1) < Bus_SclObjCin(*pp2) + Espilon )
        return 1;
    return -1;
}
void Bus_SclInsertFanout( Vec_Ptr_t * vFanouts, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pCur;
    int i, k;
    assert( Bus_SclObjDept(pObj) > 0 );
    assert( Bus_SclObjLoad(pObj) > 0 );
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

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_SclAddOneInv( Bus_Man_t * p, Abc_Obj_t * pObj, Vec_Ptr_t * vFanouts, float Gain, int Degree )
{
    SC_Cell * pCellNew;
    Abc_Obj_t * pFanout, * pInv;
    float Target = SC_CellPinCap(p->pInv, 0) * Gain;
    float Load = 0;
    int i, iStop;
    Vec_PtrForEachEntryStop( Abc_Obj_t *, vFanouts, pFanout, iStop, Degree )
    {
        Load += Bus_SclObjCin( pFanout );
        if ( Load > Target )
            break;
    }
    // create inverter
    if ( p->pPars->fAddBufs )
        pInv = Abc_NtkCreateNodeBuf( p->pNtk, NULL );
    else
        pInv = Abc_NtkCreateNodeInv( p->pNtk, NULL );
    assert( (int)Abc_ObjId(pInv) < Vec_FltSize(p->vDepts) );
    Vec_PtrForEachEntryStop( Abc_Obj_t *, vFanouts, pFanout, i, iStop )
    {
        Vec_PtrWriteEntry( vFanouts, i, NULL );
        if ( Abc_ObjFanin0(pFanout) == NULL )
            Abc_ObjAddFanin( pFanout, pInv );
        else
            Abc_ObjPatchFanin( pFanout, pObj, pInv );
    }
    // set the gate
    pCellNew = Abc_SclFindSmallestGate( p->pInv, Load / Gain );
    Vec_IntSetEntry( p->pNtk->vGates, Abc_ObjId(pInv), pCellNew->Id );
    Bus_SclObjSetCin( pInv, SC_CellPinCap(pCellNew, 0) );
    // update timing
    Abc_NtkComputeNodeLoad( pInv );
    Abc_NtkComputeNodeDept( pInv, p->pPars->Slew );
    // update phases
    if ( p->pNtk->vPhases && Abc_SclIsInv(pInv) )
        Abc_NodeInvUpdateFanPolarity( pInv );
    return pInv;
}
void Abc_SclBufSize( Bus_Man_t * p )
{
    SC_Cell * pCell, * pCellNew;
    Vec_Ptr_t * vFanouts;
    Abc_Obj_t * pObj, * pInv;
    abctime clk = Abc_Clock();
    float Gain = 0.01 * p->pPars->GainRatio;
    float Load, Cin, Dept, DeptMax = 0;
    int i;
    vFanouts = Vec_PtrAlloc( 100 );
    Abc_SclMioGates2SclGates( p->pLib, p->pNtk );
    Abc_NtkForEachNodeReverse1( p->pNtk, pObj, i )
    {
        // compute load
        Abc_NtkComputeFanoutCins( pObj );
        Load = Abc_NtkComputeNodeLoad( pObj );
        // consider the gate
        pCell = Abc_SclObjCell( pObj );
        Cin = SC_CellPinCapAve( pCell->pAve );
        // consider upsizing the gate
        if ( !p->pPars->fSizeOnly && Load > Gain * Cin )
        {
            // add one or more inverters
            Abc_NodeCollectFanouts( pObj, vFanouts );
            Vec_PtrSort( vFanouts, (int(*)(void))Bus_SclCompareFanouts );
            do 
            {
                pInv = Abc_SclAddOneInv( p, pObj, vFanouts, Gain, p->pPars->nDegree );
                Bus_SclInsertFanout( vFanouts, pInv );
                Load = Bus_SclObjCin( pInv );
            }
            while ( Vec_PtrSize(vFanouts) > 1 || Load > Gain * Cin );
            // connect last inverter
            assert( Abc_ObjFanin0(pInv) == NULL );
            Abc_ObjAddFanin( pInv, pObj );
            Bus_SclObjSetLoad( pObj, Load );
        } 
        // create cell
        pCellNew = Abc_SclFindSmallestGate( pCell, Load / Gain );
        Abc_SclObjSetCell( pObj, pCellNew );
        Dept = Abc_NtkComputeNodeDept( pObj, p->pPars->Slew );
        DeptMax = Abc_MaxFloat( DeptMax, Dept );
        if ( p->pPars->fVerbose )
        {
            printf( "Node %7d : ", i );
            printf( "%12s ", pCellNew->pName );
            printf( "(%2d/%2d)  ", pCellNew->Order, pCellNew->nGates );
            printf( "gain =%5d  ", (int)(100.0 * Load / SC_CellPinCapAve(pCellNew)) );
            printf( "dept =%7.0f ps  ", SC_LibTimePs(p->pLib, Dept) );
            printf( "\n" );
        }
    }
    Abc_SclSclGates2MioGates( p->pLib, p->pNtk );
    Vec_PtrFree( vFanouts );
    if ( p->pPars->fVerbose )
    {
        printf( "Target gain =%5d. Target slew =%5d.  Delay =%7.0f ps  ", 
            p->pPars->GainRatio, p->pPars->Slew, SC_LibTimePs(p->pLib, DeptMax) );
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

