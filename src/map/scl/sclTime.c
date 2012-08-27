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

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct SC_Pair_         SC_Pair;
typedef struct SC_Man_          SC_Man;

struct SC_Pair_ 
{
    float          rise;
    float          fall;
};

struct SC_Man_ 
{
    SC_Lib *       pLib;     // library
    Abc_Ntk_t *    pNtk;     // network
    int            nObjs;    // allocated size
    Vec_Int_t *    vGates;   // mapping of objId into gateId
    SC_Pair *      pLoads;   // loads for each gate
    SC_Pair *      pArrs;    // arrivals for each gate
    SC_Pair *      pSlews;   // slews for each gate
    char *         pWireLoadUsed; // name of the used WireLoad model
};

static inline SC_Pair * Abc_SclObjLoad( SC_Man * p, Abc_Obj_t * pObj ) { return p->pLoads + Abc_ObjId(pObj); }
static inline SC_Pair * Abc_SclObjArr ( SC_Man * p, Abc_Obj_t * pObj ) { return p->pArrs  + Abc_ObjId(pObj); }
static inline SC_Pair * Abc_SclObjSlew( SC_Man * p, Abc_Obj_t * pObj ) { return p->pSlews + Abc_ObjId(pObj); }

static inline SC_Cell * Abc_SclObjCell( SC_Man * p, Abc_Obj_t * pObj ) { return SC_LibCell( p->pLib, Vec_IntEntry(p->vGates, Abc_ObjId(pObj)) ); }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Prepares STA manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SclManFindGates( SC_Man * p )
{
    Abc_Obj_t * pObj;
    char * pName;
    int i, gateId;
    assert( p->vGates == NULL );
    p->vGates = Vec_IntStartFull( p->nObjs );
    Abc_NtkForEachNode( p->pNtk, pObj, i )
    {
        pName = Mio_GateReadName((Mio_Gate_t *)pObj->pData);
        gateId = Abc_SclCellFind( p->pLib, pName );
        assert( gateId >= 0 );
        Vec_IntWriteEntry( p->vGates, i, gateId );
//printf( "Found gate %s\n", pName );
    }
}
SC_Man * Abc_SclManAlloc( SC_Lib * pLib, Abc_Ntk_t * pNtk )
{
    SC_Man * p;
    assert( Abc_NtkHasMapping(pNtk) );
    p = ABC_CALLOC( SC_Man, 1 );
    p->pLib   = pLib;
    p->pNtk   = pNtk;
    p->nObjs  = Abc_NtkObjNumMax(pNtk);
    p->pLoads = ABC_CALLOC( SC_Pair, p->nObjs );
    p->pArrs  = ABC_CALLOC( SC_Pair, p->nObjs );
    p->pSlews = ABC_CALLOC( SC_Pair, p->nObjs );
    Abc_SclManFindGates( p );
    return p;
}
void Abc_SclManFree( SC_Man * p )
{
    Vec_IntFree( p->vGates );
    ABC_FREE( p->pLoads );
    ABC_FREE( p->pArrs );
    ABC_FREE( p->pSlews );
    ABC_FREE( p );
}



/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float Abc_SclTotalArea( SC_Man * p, Vec_Ptr_t * vNodes )
{
    double Area = 0;
    Abc_Obj_t * pObj;
    int i;
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pObj, i )
        Area += Abc_SclObjCell( p, pObj )->area;
    return Area;
}
Vec_Flt_t * Abc_SclFindWireCaps( SC_Man * p, Vec_Ptr_t * vNodes )
{
    Vec_Flt_t * vCaps = NULL;
    SC_WireLoad * pWL = NULL;
    int i, Entry, EntryMax;
    float EntryPrev, EntryCur;
    p->pWireLoadUsed = NULL;
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
        Area = (float)Abc_SclTotalArea( p, vNodes );
        for ( i = 0; i < Vec_FltSize(pWLS->vAreaFrom); i++)
            if ( Area >= Vec_FltEntry(pWLS->vAreaFrom, i) && Area <  Vec_FltEntry(pWLS->vAreaTo, i) )
            {
                p->pWireLoadUsed = (char *)Vec_PtrEntry(pWLS->vWireLoadModel, i);
                break;
            }
        if ( i == Vec_FltSize(pWLS->vAreaFrom) )
            p->pWireLoadUsed = (char *)Vec_PtrEntryLast(pWLS->vWireLoadModel);
    }
    else if ( p->pLib->default_wire_load && strlen(p->pLib->default_wire_load) )
        p->pWireLoadUsed = p->pLib->default_wire_load;
    else
    {
        Abc_Print( 0, "No wire model given.\n" );
        return NULL;
    }
    // Get the actual table and reformat it for 'wire_cap' output:
    assert( p->pWireLoadUsed != NULL );
    Vec_PtrForEachEntry( SC_WireLoad *, p->pLib->vWireLoads, pWL, i )
        if ( !strcmp(pWL->name, p->pWireLoadUsed) )
            break;
    if ( i == Vec_PtrSize(p->pLib->vWireLoadSels) )
    {
        Abc_Print( -1, "Cannot find wire load model \"%s\".\n", p->pWireLoadUsed );
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

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SclComputeLoad( SC_Man * p, Vec_Ptr_t * vNodes, Vec_Flt_t * vWireCaps )
{
    Abc_Obj_t * pObj, * pFanin;
    int i, k;
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pObj, i )
    {
        SC_Cell * pCell = Abc_SclObjCell( p, pObj );
        Abc_ObjForEachFanin( pObj, pFanin, k )
        {
            SC_Pin * pPin = SC_CellPin( pCell, k );
            SC_Pair * pLoad = Abc_SclObjLoad( p, pFanin );
            pLoad->rise += pPin->rise_cap;
            pLoad->fall += pPin->fall_cap;
        }
    }
    if ( vWireCaps )
    {
        Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pObj, i )
        {
            SC_Pair * pLoad = Abc_SclObjLoad( p, pObj );
            k = Abc_MinInt( Vec_FltSize(vWireCaps)-1, Abc_ObjFanoutNum(pObj) );
            pLoad->rise += Vec_FltEntry(vWireCaps, k);
            pLoad->fall += Vec_FltEntry(vWireCaps, k);
        }
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_SclFindMostCritical( SC_Man * p, int * pfRise, Vec_Ptr_t * vNodes )
{
    Abc_Obj_t * pObj, * pPivot = NULL;
    float fMaxArr = 0;
    int i;
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pObj, i )
    {
        SC_Pair * pArr = Abc_SclObjArr( p, pObj );
        if ( fMaxArr < pArr->rise )  fMaxArr = pArr->rise, *pfRise = 1, pPivot = pObj;
        if ( fMaxArr < pArr->fall )  fMaxArr = pArr->fall, *pfRise = 0, pPivot = pObj;
    }
    assert( pPivot != NULL );
    return pPivot;
}
void Abc_SclTimeNtkPrint( SC_Man * p, Vec_Ptr_t * vNodes )
{
/*
    int fRise = 0;
    Abc_Obj_t * pPivot = Abc_SclFindMostCritical( p, &fRise, vNodes );    
    printf( "Critical delay: ObjId = %d. ", Abc_ObjId(pPivot) );
    printf( "Rise = %f. ", Abc_SclObjArr(p, pPivot)->rise );
    printf( "Fall = %f. ", Abc_SclObjArr(p, pPivot)->fall );
    printf( "\n" );
*/

    Abc_Obj_t * pObj;
    int i;
    printf( "WireLoad model = \"%s\".\n", p->pWireLoadUsed );
    printf( "Area = %f.\n", Abc_SclTotalArea( p, vNodes ) );
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pObj, i )
    {
        printf( "Node %6d : ",  Abc_ObjId(pObj) );
        printf( "TimeR = %f. ", Abc_SclObjArr(p, pObj)->rise );
        printf( "RimeF = %f. ", Abc_SclObjArr(p, pObj)->fall );
        printf( "SlewR = %f. ", Abc_SclObjSlew(p, pObj)->rise );
        printf( "SlewF = %f. ", Abc_SclObjSlew(p, pObj)->fall );
        printf( "LoadR = %f. ", Abc_SclObjLoad(p, pObj)->rise );
        printf( "LoadF = %f. ", Abc_SclObjLoad(p, pObj)->fall );
        printf( "\n" );
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
void Abc_SclTimeGate( SC_Man * p, SC_Timing * pTime, Abc_Obj_t * pObj, Abc_Obj_t * pFanin )
{
    SC_Pair * pArrIn   = Abc_SclObjArr ( p, pFanin );
    SC_Pair * pSlewIn  = Abc_SclObjSlew( p, pFanin );
    SC_Pair * pLoad    = Abc_SclObjLoad( p, pObj );
    SC_Pair * pArrOut  = Abc_SclObjArr ( p, pObj ); // modified
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
void Abc_SclTimeNtk( SC_Man * p )
{
    Vec_Flt_t * vWireCaps;
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pObj;
    int i, k;
    vNodes = Abc_NtkDfs( p->pNtk, 0 );
    vWireCaps = Abc_SclFindWireCaps( p, vNodes );
    Abc_SclComputeLoad( p, vNodes, vWireCaps );
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pObj, i )
    {
        SC_Timings * pRTime;
        SC_Timing * pTime;
        SC_Pin * pPin;
        // get the library cell
        SC_Cell * pCell = Abc_SclObjCell( p, pObj );
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
    Abc_SclTimeNtkPrint( p, vNodes );
    Vec_FltFree( vWireCaps );
    Vec_PtrFree( vNodes );
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
    p = Abc_SclManAlloc( pLib, (Abc_Ntk_t *)pNtk );
    Abc_SclTimeNtk( p );
    Abc_SclManFree( p );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

