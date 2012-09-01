/**CFile****************************************************************

  FileName    [sclTime.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Standard-cell library representation.]

  Synopsis    [Static timing analysis using Liberty delay model.]

  Author      [Alan Mishchenko, Niklas Een]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 24, 2012.]

  Revision    [$Id: sclTime.c,v 1.0 2012/08/24 00:00:00 alanmi Exp $]

***********************************************************************/

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

  Synopsis    [Finding most critical nodes/fanins/path.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_SclFindCriticalCo( SC_Man * p, int * pfRise )
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

/**Function*************************************************************

  Synopsis    [Printing timing information for the node/network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_SclTimeGatePrint( SC_Man * p, Abc_Obj_t * pObj, int fRise )
{
    printf( "%7d : ",             Abc_ObjId(pObj) );
    printf( "%d ",                Abc_ObjFaninNum(pObj) );
    printf( "%-12s ",             Abc_SclObjCell(p, pObj)->pName );
    if ( fRise >= 0 )
    printf( "(%s)   ",            fRise ? "rise" : "fall" );
    printf( "delay = (" );
    printf( "%7.1f ps ",          Abc_SclObjTimePs(p, pObj, 1) );
    printf( "%7.1f ps )  ",       Abc_SclObjTimePs(p, pObj, 0) );
    printf( "load =%6.2f ff   ",  Abc_SclObjLoadFf(p, pObj, fRise >= 0 ? fRise : 0 ) );
    printf( "slew =%6.1f ps   ",  Abc_SclObjSlewPs(p, pObj, fRise >= 0 ? fRise : 0 ) );
    printf( "\n" );
}
void Abc_SclTimeNtkPrint( SC_Man * p, int fShowAll )
{
    int i, fRise = 0;
    Abc_Obj_t * pObj = Abc_SclFindCriticalCo( p, &fRise );    

    printf( "WireLoad model = \"%s\".  ", p->pWLoadUsed );
    printf( "Total area = %10.2f.  ",     Abc_SclGetTotalArea( p ) );
    printf( "Critical delay = %.1f ps\n", Abc_SclObjTimePs(p, pObj, fRise) );

    if ( fShowAll )
    {
//        printf( "Timing information for all nodes: \n" );
        Abc_NtkForEachNodeReverse( p->pNtk, pObj, i )
            if ( Abc_ObjFaninNum(pObj) > 0 )
                Abc_SclTimeGatePrint( p, pObj, -1 );
    }
    else
    {
//        printf( "Critical path: \n" );
        pObj = Abc_ObjFanin0(pObj);
        while ( pObj && Abc_ObjIsNode(pObj) )
        {
            printf( "Critical path -- " );
            Abc_SclTimeGatePrint( p, pObj, fRise );
            pObj = Abc_SclFindMostCriticalFanin( p, &fRise, pObj );
        }
    }
}

/**Function*************************************************************

  Synopsis    [Timing computation for pin/gate/cone/network.]

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
void Abc_SclTimePin( SC_Man * p, SC_Timing * pTime, Abc_Obj_t * pObj, Abc_Obj_t * pFanin )
{
    SC_Pair * pArrIn   = Abc_SclObjTime( p, pFanin );
    SC_Pair * pSlewIn  = Abc_SclObjSlew( p, pFanin );
    SC_Pair * pLoad    = Abc_SclObjLoad( p, pObj );
    SC_Pair * pArrOut  = Abc_SclObjTime( p, pObj );   // modified
    SC_Pair * pSlewOut = Abc_SclObjSlew( p, pObj );   // modified

    if (pTime->tsense == sc_ts_Pos || pTime->tsense == sc_ts_Non)
    {
        pArrOut->rise  = Abc_MaxFloat( pArrOut->rise,  pArrIn->rise + Abc_SclLookup(pTime->pCellRise,  pSlewIn->rise, pLoad->rise) );
        pArrOut->fall  = Abc_MaxFloat( pArrOut->fall,  pArrIn->fall + Abc_SclLookup(pTime->pCellFall,  pSlewIn->fall, pLoad->fall) );
        pSlewOut->rise = Abc_MaxFloat( pSlewOut->rise,                Abc_SclLookup(pTime->pRiseTrans, pSlewIn->rise, pLoad->rise) );
        pSlewOut->fall = Abc_MaxFloat( pSlewOut->fall,                Abc_SclLookup(pTime->pFallTrans, pSlewIn->fall, pLoad->fall) );
    }
    if (pTime->tsense == sc_ts_Neg || pTime->tsense == sc_ts_Non)
    {
        pArrOut->rise  = Abc_MaxFloat( pArrOut->rise,  pArrIn->fall + Abc_SclLookup(pTime->pCellRise,  pSlewIn->fall, pLoad->rise) );
        pArrOut->fall  = Abc_MaxFloat( pArrOut->fall,  pArrIn->rise + Abc_SclLookup(pTime->pCellFall,  pSlewIn->rise, pLoad->fall) );
        pSlewOut->rise = Abc_MaxFloat( pSlewOut->rise,                Abc_SclLookup(pTime->pRiseTrans, pSlewIn->fall, pLoad->rise) );
        pSlewOut->fall = Abc_MaxFloat( pSlewOut->fall,                Abc_SclLookup(pTime->pFallTrans, pSlewIn->rise, pLoad->fall) );
    }
}
void Abc_SclTimeGate( SC_Man * p, Abc_Obj_t * pObj )
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
    SC_PinForEachRTiming( pPin, pRTime, k )
    {
        assert( Vec_PtrSize(pRTime->vTimings) == 1 );
        pTime = (SC_Timing *)Vec_PtrEntry( pRTime->vTimings, 0 );
        Abc_SclTimePin( p, pTime, pObj, Abc_ObjFanin(pObj, k) );
    }
}
void Abc_SclTimeCone( SC_Man * p, Vec_Int_t * vCone )
{
    int fVerbose = 0;
    Abc_Obj_t * pObj;
    int i;
    Abc_NtkForEachObjVec( vCone, p->pNtk, pObj, i )
    {
        if ( fVerbose && Abc_ObjIsNode(pObj) )
        printf( "  Updating node %d with gate %s\n", Abc_ObjId(pObj), Abc_SclObjCell(p, pObj)->pName );

        if ( fVerbose && Abc_ObjIsNode(pObj) )
        printf( "    before (%6.1f ps  %6.1f ps)   ", Abc_SclObjTimePs(p, pObj, 1), Abc_SclObjTimePs(p, pObj, 0) );

        Abc_SclTimeGate( p, pObj );

        if ( fVerbose && Abc_ObjIsNode(pObj) )
        printf( "after (%6.1f ps  %6.1f ps)\n", Abc_SclObjTimePs(p, pObj, 1), Abc_SclObjTimePs(p, pObj, 0) );
    }
}
void Abc_SclTimeNtk( SC_Man * p )
{
    Abc_Obj_t * pObj;
    int i;
    Abc_NtkForEachNode1( p->pNtk, pObj, i )
        Abc_SclTimeGate( p, pObj );
    Abc_NtkForEachCo( p->pNtk, pObj, i )
        Abc_SclObjDupFanin( p, pObj );
}

/**Function*************************************************************

  Synopsis    [Prepare timing manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
SC_Man * Abc_SclManStart( SC_Lib * pLib, Abc_Ntk_t * pNtk )
{
    SC_Man * p = Abc_SclManAlloc( pLib, pNtk );
    assert( p->vGates == NULL );
    p->vGates = Abc_SclManFindGates( pLib, pNtk );
//    Abc_SclManUpsize( p );
    Abc_SclComputeLoad( p );
    Abc_SclTimeNtk( p );
    p->SumArea = p->SumArea0 = Abc_SclGetTotalArea( p );
    p->MaxDelay0 = Abc_SclGetMaxDelay( p );
    return p;
}

/**Function*************************************************************

  Synopsis    [Printing out timing information for the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SclTimePerform( SC_Lib * pLib, Abc_Ntk_t * pNtk, int fShowAll )
{
    SC_Man * p;
    p = Abc_SclManStart( pLib, pNtk );   
    Abc_SclTimeNtkPrint( p, fShowAll );
    Abc_SclManFree( p );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

