/**CFile****************************************************************

  FileName    [sclIo.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  Synopsis    [Standard-cell library representation.]

  Author      [Alan Mishchenko, Niklas Een]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 24, 2012.]

  Revision    [$Id: sclIo.c,v 1.0 2012/08/24 00:00:00 alanmi Exp $]

***********************************************************************/

#include "base/abc/abc.h"
#include "map/mio/mio.h"
#include "sclInt.h"
#include "sclMan.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float Abc_SclTotalArea( SC_Man * p )
{
    double Area = 0;
    Abc_Obj_t * pObj;
    int i;
    Abc_NtkForEachNode( p->pNtk, pObj, i )
        Area += Abc_SclObjCell( p, pObj )->area;
    return Area;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SclTimeNtkPrint( SC_Man * p )
{
    Abc_Obj_t * pObj;
    int i;
    printf( "Total area = %f.\n", Abc_SclTotalArea( p ) );
    printf( "WireLoad model = \"%s\".\n", p->pWLoadUsed );
    Abc_NtkForEachNode( p->pNtk, pObj, i )
    {
        printf( "Node %6d : ",  Abc_ObjId(pObj) );
        printf( "TimeR = %f. ", Abc_SclObjTime(p, pObj)->rise );
        printf( "RimeF = %f. ", Abc_SclObjTime(p, pObj)->fall );
        printf( "SlewR = %f. ", Abc_SclObjSlew(p, pObj)->rise );
        printf( "SlewF = %f. ", Abc_SclObjSlew(p, pObj)->fall );
        printf( "LoadR = %f. ", Abc_SclObjLoad(p, pObj)->rise );
        printf( "LoadF = %f. ", Abc_SclObjLoad(p, pObj)->fall );
        printf( "\n" );
    }
}
Abc_Obj_t * Abc_SclFindMostCritical( SC_Man * p, int * pfRise )
{
    Abc_Obj_t * pObj, * pPivot = NULL;
    float fMaxArr = 0;
    int i;
    Abc_NtkForEachCo( p->pNtk, pObj, i )
    {
        SC_Pair * pArr = Abc_SclObjTime( p, pObj );
        if ( fMaxArr < pArr->rise )  fMaxArr = pArr->rise, *pfRise = 1, pPivot = pObj;
        if ( fMaxArr < pArr->fall )  fMaxArr = pArr->fall, *pfRise = 0, pPivot = pObj;
    }
    assert( pPivot != NULL );
    return pPivot;
}
Abc_Obj_t * Abc_SclFindMostCriticalFanin( SC_Man * p, int * pfRise, Abc_Obj_t * pNode )
{
    Abc_Obj_t * pObj, * pPivot = NULL;
    float fMaxArr = 0;
    int i;
    Abc_ObjForEachFanin( pNode, pObj, i )
    {
        SC_Pair * pArr = Abc_SclObjTime( p, pObj );
        if ( fMaxArr < pArr->rise )  fMaxArr = pArr->rise, *pfRise = 1, pPivot = pObj;
        if ( fMaxArr < pArr->fall )  fMaxArr = pArr->fall, *pfRise = 0, pPivot = pObj;
    }
    return pPivot;
}
Vec_Int_t * Abc_SclCriticalPathFind( SC_Man * p )
{
    int fRise = 0;
    Abc_Obj_t * pPivot = Abc_SclFindMostCritical( p, &fRise );
    Vec_Int_t * vPath = Vec_IntAlloc( 100 );
    Vec_IntPush( vPath, Abc_ObjId(pPivot) );
    pPivot = Abc_ObjFanin0(pPivot);
    while ( pPivot && Abc_ObjIsNode(pPivot) )
    {
        Vec_IntPush( vPath, Abc_ObjId(pPivot) );
        pPivot = Abc_SclFindMostCriticalFanin( p, &fRise, pPivot );
    }
    return vPath;  
}
void Abc_SclCriticalPathPrint( SC_Man * p )
{
    int fRise = 0;
    Abc_Obj_t * pPivot = Abc_SclFindMostCritical( p, &fRise );    

    printf( "Total area = %10.2f.\n", Abc_SclTotalArea( p ) );
    printf( "WireLoad model = \"%s\".\n", p->pWLoadUsed );
    printf( "Critical delay = %.1f ps\n", Abc_SclObjTimePs(p, pPivot, fRise) );

    printf( "Critical path: \n" );
    pPivot = Abc_ObjFanin0(pPivot);
    while ( pPivot && Abc_ObjIsNode(pPivot) )
    {
        printf( "%5d : ",             Abc_ObjId(pPivot) );
        printf( "%-10s ",             Abc_SclObjCell(p, pPivot)->name );
        printf( "(%s)   ",            fRise ? "rise" : "fall" );
        printf( "delay =%6.1f ps   ", Abc_SclObjTimePs(p, pPivot, fRise) );
        printf( "load =%6.2f ff   ",  Abc_SclObjLoadFf(p, pPivot, fRise) );
        printf( "slew =%6.1f ps   ",  Abc_SclObjSlewPs(p, pPivot, fRise) );
        printf( "\n" );

        pPivot = Abc_SclFindMostCriticalFanin( p, &fRise, pPivot );
    }
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Flt_t * Abc_SclFindWireCaps( SC_Man * p )
{
    Vec_Flt_t * vCaps = NULL;
    SC_WireLoad * pWL = NULL;
    int i, Entry, EntryMax;
    float EntryPrev, EntryCur;
    p->pWLoadUsed = NULL;
    if ( p->pLib->default_wire_load_sel && strlen(p->pLib->default_wire_load_sel) )
    {
        float Area;
        SC_WireLoadSel * pWLS = NULL;
        Vec_PtrForEachEntry( SC_WireLoadSel *, p->pLib->vWireLoadSels, pWLS, i )
            if ( !strcmp(pWLS->name, p->pLib->default_wire_load_sel) )
                break;
        if ( i == Vec_PtrSize(p->pLib->vWireLoadSels) )
        {
            Abc_Print( -1, "Cannot find wire load selection model \"%s\".\n", p->pLib->default_wire_load_sel );
            exit(1);
        }
        Area = (float)Abc_SclTotalArea( p );
        for ( i = 0; i < Vec_FltSize(pWLS->vAreaFrom); i++)
            if ( Area >= Vec_FltEntry(pWLS->vAreaFrom, i) && Area <  Vec_FltEntry(pWLS->vAreaTo, i) )
            {
                p->pWLoadUsed = (char *)Vec_PtrEntry(pWLS->vWireLoadModel, i);
                break;
            }
        if ( i == Vec_FltSize(pWLS->vAreaFrom) )
            p->pWLoadUsed = (char *)Vec_PtrEntryLast(pWLS->vWireLoadModel);
    }
    else if ( p->pLib->default_wire_load && strlen(p->pLib->default_wire_load) )
        p->pWLoadUsed = p->pLib->default_wire_load;
    else
    {
        Abc_Print( 0, "No wire model given.\n" );
        return NULL;
    }
    // Get the actual table and reformat it for 'wire_cap' output:
    assert( p->pWLoadUsed != NULL );
    Vec_PtrForEachEntry( SC_WireLoad *, p->pLib->vWireLoads, pWL, i )
        if ( !strcmp(pWL->name, p->pWLoadUsed) )
            break;
    if ( i == Vec_PtrSize(p->pLib->vWireLoadSels) )
    {
        Abc_Print( -1, "Cannot find wire load model \"%s\".\n", p->pWLoadUsed );
        exit(1);
    }
    // find the biggest fanout
    EntryMax = 0;
    Vec_IntForEachEntry( pWL->vFanout, Entry, i )
        EntryMax = Abc_MaxInt( EntryMax, Entry );
    // create the array
    vCaps = Vec_FltStart( EntryMax + 1 );
    Vec_IntForEachEntry( pWL->vFanout, Entry, i )
        Vec_FltWriteEntry( vCaps, Entry, Vec_FltEntry(pWL->vLen, i) * pWL->cap );
    // reformat
    EntryPrev = 0;
    Vec_FltForEachEntry( vCaps, EntryCur, i )
    {
        if ( EntryCur )
            EntryPrev = EntryCur;
        else
            Vec_FltWriteEntry( vCaps, i, EntryPrev );
    }
    return vCaps;
}
void Abc_SclComputeLoad( SC_Man * p )
{
    Vec_Flt_t * vWireCaps;
    Abc_Obj_t * pObj, * pFanin;
    int i, k;
    Abc_NtkForEachNode( p->pNtk, pObj, i )
    {
        SC_Cell * pCell = Abc_SclObjCell( p, pObj );
        Abc_ObjForEachFanin( pObj, pFanin, k )
        {
            SC_Pair * pLoad = Abc_SclObjLoad( p, pFanin );
            SC_Pin * pPin = SC_CellPin( pCell, k );
            pLoad->rise += pPin->rise_cap;
            pLoad->fall += pPin->fall_cap;
        }
    }
    vWireCaps = Abc_SclFindWireCaps( p );
    if ( vWireCaps )
    {
        Abc_NtkForEachNode( p->pNtk, pObj, i )
        {
            SC_Pair * pLoad = Abc_SclObjLoad( p, pObj );
            k = Abc_MinInt( Vec_FltSize(vWireCaps)-1, Abc_ObjFanoutNum(pObj) );
            pLoad->rise += Vec_FltEntry(vWireCaps, k);
            pLoad->fall += Vec_FltEntry(vWireCaps, k);
        }
    }
    Vec_FltFree( vWireCaps );
}
void Abc_SclUpdateLoad( SC_Man * p, Abc_Obj_t * pObj, SC_Cell * pOld, SC_Cell * pNew )
{
    Abc_Obj_t * pFanin;
    int k;
    Abc_ObjForEachFanin( pObj, pFanin, k )
    {
        SC_Pair * pLoad = Abc_SclObjLoad( p, pFanin );
        SC_Pin * pPinOld = SC_CellPin( pOld, k );
        SC_Pin * pPinNew = SC_CellPin( pNew, k );
        pLoad->rise += pPinNew->rise_cap - pPinOld->rise_cap;
        pLoad->fall += pPinNew->fall_cap - pPinOld->fall_cap;
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline float Abc_SclLookup( SC_Surface * p, float slew, float load )
{
    float * pIndex0, * pIndex1, * pDataS, * pDataS1;
    float sfrac, lfrac, p0, p1;
    int s, l;

    // Find closest sample points in surface:
    pIndex0 = Vec_FltArray(p->vIndex0);
    for ( s = 1; s < Vec_FltSize(p->vIndex0)-1; s++ )
        if ( pIndex0[s] > slew )
            break;
    s--;

    pIndex1 = Vec_FltArray(p->vIndex1);
    for ( l = 1; l < Vec_FltSize(p->vIndex1)-1; l++ )
        if ( pIndex1[l] > load )
            break;
    l--;

    // Interpolate (or extrapolate) function value from sample points:
    sfrac = (slew - pIndex0[s]) / (pIndex0[s+1] - pIndex0[s]);
    lfrac = (load - pIndex1[l]) / (pIndex1[l+1] - pIndex1[l]);

    pDataS  = Vec_FltArray( (Vec_Flt_t *)Vec_PtrEntry(p->vData, s) );
    pDataS1 = Vec_FltArray( (Vec_Flt_t *)Vec_PtrEntry(p->vData, s+1) );

    p0 = pDataS [l] + lfrac * (pDataS [l+1] - pDataS [l]);
    p1 = pDataS1[l] + lfrac * (pDataS1[l+1] - pDataS1[l]);

    return p0 + sfrac * (p1 - p0);      // <<== multiply result with K factor here 
}
static inline void Abc_SclTimeGate( SC_Man * p, SC_Timing * pTime, Abc_Obj_t * pObj, Abc_Obj_t * pFanin )
{
    SC_Pair * pArrIn   = Abc_SclObjTime ( p, pFanin );
    SC_Pair * pSlewIn  = Abc_SclObjSlew( p, pFanin );
    SC_Pair * pLoad    = Abc_SclObjLoad( p, pObj );
    SC_Pair * pArrOut  = Abc_SclObjTime ( p, pObj ); // modified
    SC_Pair * pSlewOut = Abc_SclObjSlew( p, pObj ); // modified

    if (pTime->tsense == sc_ts_Pos || pTime->tsense == sc_ts_Non)
    {
        pArrOut->rise  = Abc_MaxFloat( pArrOut->rise, pArrIn->rise + Abc_SclLookup(pTime->pCellRise,  pSlewIn->rise, pLoad->rise) );
        pArrOut->fall  = Abc_MaxFloat( pArrOut->fall, pArrIn->fall + Abc_SclLookup(pTime->pCellFall,  pSlewIn->fall, pLoad->fall) );
        pSlewOut->rise = Abc_MaxFloat( pSlewOut->rise,               Abc_SclLookup(pTime->pRiseTrans, pSlewIn->rise, pLoad->rise) );
        pSlewOut->fall = Abc_MaxFloat( pSlewOut->fall,               Abc_SclLookup(pTime->pFallTrans, pSlewIn->fall, pLoad->fall) );
    }
    if (pTime->tsense == sc_ts_Neg || pTime->tsense == sc_ts_Non)
    {
        pArrOut->rise  = Abc_MaxFloat( pArrOut->rise, pArrIn->fall + Abc_SclLookup(pTime->pCellRise,  pSlewIn->fall, pLoad->rise) );
        pArrOut->fall  = Abc_MaxFloat( pArrOut->fall, pArrIn->rise + Abc_SclLookup(pTime->pCellFall,  pSlewIn->rise, pLoad->fall) );
        pSlewOut->rise = Abc_MaxFloat( pSlewOut->rise,               Abc_SclLookup(pTime->pRiseTrans, pSlewIn->fall, pLoad->rise) );
        pSlewOut->fall = Abc_MaxFloat( pSlewOut->fall,               Abc_SclLookup(pTime->pFallTrans, pSlewIn->rise, pLoad->fall) );
    }
}
void Abc_SclTimeObj( SC_Man * p, Abc_Obj_t * pObj )
{
    SC_Timings * pRTime;
    SC_Timing * pTime;
    SC_Pin * pPin;
    SC_Cell * pCell;
    int k;
    if ( Abc_ObjIsCo(pObj) )
    {
        Abc_SclObjDupFanin( p, pObj );
        return;
    }
    assert( Abc_ObjIsNode(pObj) );
    // get the library cell
    pCell = Abc_SclObjCell( p, pObj );
    // get the output pin
    assert( pCell->n_outputs == 1 );
    pPin = SC_CellPin( pCell, pCell->n_inputs );
    // compute timing using each fanin
    assert( Vec_PtrSize(pPin->vRTimings) == pCell->n_inputs );
    Vec_PtrForEachEntry( SC_Timings *, pPin->vRTimings, pRTime, k )
    {
        assert( Vec_PtrSize(pRTime->vTimings) == 1 );
        pTime = (SC_Timing *)Vec_PtrEntry( pRTime->vTimings, 0 );
        Abc_SclTimeGate( p, pTime, pObj, Abc_ObjFanin(pObj, k) );
    }
}
void Abc_SclTimeNtk( SC_Man * p )
{
    Abc_Obj_t * pObj;
    int i;
    Abc_NtkForEachNode( p->pNtk, pObj, i )
        Abc_SclTimeObj( p, pObj );
    Abc_NtkForEachCo( p->pNtk, pObj, i )
        Abc_SclObjDupFanin( p, pObj );
}
void Abc_SclTimeCone( SC_Man * p, Vec_Int_t * vCone )
{
    Abc_Obj_t * pObj;
    int i;
    Abc_NtkForEachObjVec( vCone, p->pNtk, pObj, i )
    {
        if ( Abc_ObjIsNode(pObj) )
        printf( "  Updating node with gate %s\n", Abc_SclObjCell(p, pObj)->name );

        printf( "    before %6.1f ps   ", Abc_SclObjTimePs(p, pObj, 0) );
        Abc_SclTimeObj( p, pObj );
        printf( "after %6.1f ps\n", Abc_SclObjTimePs(p, pObj, 0) );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
SC_Man * Abc_SclManStart( SC_Lib * pLib, Abc_Ntk_t * pNtk )
{
    extern Vec_Int_t * Abc_SclManFindGates( SC_Lib * pLib, Abc_Ntk_t * p );
    // prepare timing manager
    SC_Man * p = Abc_SclManAlloc( pLib, pNtk );
    assert( p->vGates == NULL );
    p->vGates = Abc_SclManFindGates( pLib, pNtk );
    p->SumArea = Abc_SclTotalArea( p );
    Abc_SclComputeLoad( p );
    Abc_SclTimeNtk( p );
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SclTimePerform( SC_Lib * pLib, void * pNtk )
{
    SC_Man * p;
    p = Abc_SclManStart( pLib, (Abc_Ntk_t *)pNtk );   
    Abc_SclCriticalPathPrint( p );
    Abc_SclManFree( p );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

