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
#include "map/mio/mio.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Finding most critical objects.]

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
// assumes that slacks are not available (uses arrival times)
Abc_Obj_t * Abc_SclFindMostCriticalFanin2( SC_Man * p, int * pfRise, Abc_Obj_t * pNode )
{
    Abc_Obj_t * pFanin, * pPivot = NULL;
    float fMaxArr = 0;
    int i;
    Abc_ObjForEachFanin( pNode, pFanin, i )
    {
        SC_Pair * pArr = Abc_SclObjTime( p, pFanin );
        if ( fMaxArr < pArr->rise )  fMaxArr = pArr->rise, *pfRise = 1, pPivot = pFanin;
        if ( fMaxArr < pArr->fall )  fMaxArr = pArr->fall, *pfRise = 0, pPivot = pFanin;
    }
    return pPivot;
}
// assumes that slack are available
Abc_Obj_t * Abc_SclFindMostCriticalFanin( SC_Man * p, int * pfRise, Abc_Obj_t * pNode )
{
    Abc_Obj_t * pFanin, * pPivot = NULL;
    float fMinSlack = ABC_INFINITY;
    SC_Pair * pArr;
    int i;
    *pfRise = 0;
    // find min-slack node
    Abc_ObjForEachFanin( pNode, pFanin, i )
        if ( fMinSlack > Abc_SclObjSlack( p, pFanin ) )
        {
            fMinSlack = Abc_SclObjSlack( p, pFanin );
            pPivot = pFanin;
        }
    if ( pPivot == NULL )
        return NULL;
    // find its leading phase
    pArr = Abc_SclObjTime( p, pPivot );
    *pfRise = (pArr->rise >= pArr->fall);
    return pPivot;
}

/**Function*************************************************************

  Synopsis    [Printing timing information for the node/network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_SclTimeNodePrint( SC_Man * p, Abc_Obj_t * pObj, int fRise, int Length, float maxDelay )
{
    printf( "%7d : ",             Abc_ObjId(pObj) );
    printf( "%d ",                Abc_ObjFaninNum(pObj) );
    printf( "%2d ",               Abc_ObjFanoutNum(pObj) );
    printf( "%-*s ",              Length, Abc_ObjIsPi(pObj) ? "pi" : Abc_SclObjCell(p, pObj)->pName );
    if ( fRise >= 0 )
    printf( "(%s)   ",            fRise ? "rise" : "fall" );
    printf( "delay = (" );
    printf( "%8.2f ps ",          Abc_SclObjTimePs(p, pObj, 1) );
    printf( "%8.2f ps )  ",       Abc_SclObjTimePs(p, pObj, 0) );
    printf( "load =%7.2f ff   ",  Abc_SclObjLoadFf(p, pObj, fRise >= 0 ? fRise : 0 ) );
    printf( "slew =%7.2f ps   ",  Abc_SclObjSlewPs(p, pObj, fRise >= 0 ? fRise : 0 ) );
    printf( "slack =%6.2f ps",    Abc_SclObjSlack(p, pObj) );
    printf( "\n" );
}
void Abc_SclTimeNtkPrint( SC_Man * p, int fShowAll, int fShort )
{
    int i, nLength = 0, fRise = 0;
    Abc_Obj_t * pObj, * pPivot = Abc_SclFindCriticalCo( p, &fRise ); 
    float maxDelay = Abc_SclObjTimePs(p, pPivot, fRise);

    printf( "WireLoad model = \"%s\".  ", p->pWLoadUsed ? p->pWLoadUsed->pName : "none" );
    printf( "Gates = %d.  ",              Abc_NtkNodeNum(p->pNtk) );
    printf( "Area = %.2f.  ",             Abc_SclGetTotalArea( p ) );
    printf( "Critical delay = %.2f ps\n", maxDelay );
    if ( fShort )
        return;

    if ( fShowAll )
    {
//        printf( "Timing information for all nodes: \n" );
        // find the longest cell name
        Abc_NtkForEachNodeReverse( p->pNtk, pObj, i )
            if ( Abc_ObjFaninNum(pObj) > 0 )
                nLength = Abc_MaxInt( nLength, strlen(Abc_SclObjCell(p, pObj)->pName) );
        // print timing
        Abc_NtkForEachNodeReverse( p->pNtk, pObj, i )
            if ( Abc_ObjFaninNum(pObj) > 0 )
                Abc_SclTimeNodePrint( p, pObj, -1, nLength, maxDelay );
    }
    else
    {
//        printf( "Critical path: \n" );
        // find the longest cell name
        pObj = Abc_ObjFanin0(pPivot);
        i = 0;
        while ( pObj && Abc_ObjIsNode(pObj) )
        {
            i++;
            nLength = Abc_MaxInt( nLength, strlen(Abc_SclObjCell(p, pObj)->pName) );
            pObj = Abc_SclFindMostCriticalFanin( p, &fRise, pObj );
        }
        // print timing
        pObj = Abc_ObjFanin0(pPivot);
        while ( pObj )//&& Abc_ObjIsNode(pObj) )
        {
            printf( "C-path %3d -- ", i-- );
            Abc_SclTimeNodePrint( p, pObj, fRise, nLength, maxDelay );
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
void Abc_SclTimeFanin( SC_Man * p, SC_Timing * pTime, Abc_Obj_t * pObj, Abc_Obj_t * pFanin )
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
void Abc_SclDeptFanin( SC_Man * p, SC_Timing * pTime, Abc_Obj_t * pObj, Abc_Obj_t * pFanin )
{
    SC_Pair * pDepIn   = Abc_SclObjDept( p, pFanin );   // modified
    SC_Pair * pSlewIn  = Abc_SclObjSlew( p, pFanin );
    SC_Pair * pLoad    = Abc_SclObjLoad( p, pObj );
    SC_Pair * pDepOut  = Abc_SclObjDept( p, pObj );

    if (pTime->tsense == sc_ts_Pos || pTime->tsense == sc_ts_Non)
    {
        pDepIn->rise  = Abc_MaxFloat( pDepIn->rise,  pDepOut->rise + Abc_SclLookup(pTime->pCellRise,  pSlewIn->rise, pLoad->rise) );
        pDepIn->fall  = Abc_MaxFloat( pDepIn->fall,  pDepOut->fall + Abc_SclLookup(pTime->pCellFall,  pSlewIn->fall, pLoad->fall) );
    }
    if (pTime->tsense == sc_ts_Neg || pTime->tsense == sc_ts_Non)
    {
        pDepIn->fall  = Abc_MaxFloat( pDepIn->fall,  pDepOut->rise + Abc_SclLookup(pTime->pCellRise,  pSlewIn->fall, pLoad->rise) );
        pDepIn->rise  = Abc_MaxFloat( pDepIn->rise,  pDepOut->fall + Abc_SclLookup(pTime->pCellFall,  pSlewIn->rise, pLoad->fall) );
    }
}
void Abc_SclTimeNode( SC_Man * p, Abc_Obj_t * pObj, int fDept )
{
    SC_Timings * pRTime;
    SC_Timing * pTime;
    SC_Pin * pPin;
    SC_Cell * pCell;
    int k;
    if ( Abc_ObjIsCo(pObj) )
    {
        if ( !fDept )
            Abc_SclObjDupFanin( p, pObj );
        return;
    }
    assert( Abc_ObjIsNode(pObj) );
    // get the library cell
    pCell = Abc_SclObjCell( p, pObj );
    // get the output pin
//    assert( pCell->n_outputs == 1 );
    pPin = SC_CellPin( pCell, pCell->n_inputs );
    // compute timing using each fanin
    assert( Vec_PtrSize(pPin->vRTimings) == pCell->n_inputs );
    SC_PinForEachRTiming( pPin, pRTime, k )
    {
        assert( Vec_PtrSize(pRTime->vTimings) == 1 );
        pTime = (SC_Timing *)Vec_PtrEntry( pRTime->vTimings, 0 );
        if ( fDept )
            Abc_SclDeptFanin( p, pTime, pObj, Abc_ObjFanin(pObj, k) );
        else
            Abc_SclTimeFanin( p, pTime, pObj, Abc_ObjFanin(pObj, k) );
    }
}
void Abc_SclTimeCone( SC_Man * p, Vec_Int_t * vCone )
{
    int fVerbose = 0;
    Abc_Obj_t * pObj;
    int i;
    Abc_SclConeClear( p, vCone );
    Abc_NtkForEachObjVec( vCone, p->pNtk, pObj, i )
    {
        if ( fVerbose && Abc_ObjIsNode(pObj) )
        printf( "  Updating node %d with gate %s\n", Abc_ObjId(pObj), Abc_SclObjCell(p, pObj)->pName );
        if ( fVerbose && Abc_ObjIsNode(pObj) )
        printf( "    before (%6.1f ps  %6.1f ps)   ", Abc_SclObjTimePs(p, pObj, 1), Abc_SclObjTimePs(p, pObj, 0) );
        Abc_SclTimeNode( p, pObj, 0 );
        if ( fVerbose && Abc_ObjIsNode(pObj) )
        printf( "after (%6.1f ps  %6.1f ps)\n", Abc_SclObjTimePs(p, pObj, 1), Abc_SclObjTimePs(p, pObj, 0) );
    }
}
void Abc_SclTimeNtkRecompute( SC_Man * p, float * pArea, float * pDelay, int fReverse, float DUser )
{
    Abc_Obj_t * pObj;
    float D;
    int i;
    Abc_SclComputeLoad( p );
    Abc_SclManCleanTime( p );
    Abc_NtkForEachNode1( p->pNtk, pObj, i )
        Abc_SclTimeNode( p, pObj, 0 );
    Abc_NtkForEachCo( p->pNtk, pObj, i )
    {
        Abc_SclObjDupFanin( p, pObj );
        Vec_FltWriteEntry( p->vTimesOut, i, Abc_SclObjTimeMax(p, pObj) );
        Vec_QueUpdate( p->vQue, i );
    }
    D = Abc_SclReadMaxDelay( p );
    if ( fReverse && DUser > 0 && D < DUser )
        D = DUser;
    if ( pArea )
        *pArea = Abc_SclGetTotalArea( p );
    if ( pDelay )
        *pDelay = D;
    if ( fReverse )
    {
        Abc_NtkForEachNodeReverse1( p->pNtk, pObj, i )
            Abc_SclTimeNode( p, pObj, 1 );
        Abc_NtkForEachObj( p->pNtk, pObj, i )
            p->pSlack[i] = Abc_MaxFloat( 0.0, Abc_SclObjGetSlack(p, pObj, D) );
    }
}

/**Function*************************************************************

  Synopsis    [Read input slew and output load.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SclManReadSlewAndLoad( SC_Man * p, Abc_Ntk_t * pNtk )
{
    Abc_Time_t * pTime;
    Abc_Obj_t * pObj;
    int i;
    if ( pNtk->pManTime == NULL )
        return;
    // read input slew    
    pTime = Abc_NtkReadDefaultInputDrive( pNtk );
    if ( Abc_MaxFloat(pTime->Rise, pTime->Fall) != 0 )
    {
        printf( "Default input slew is specified (%.2f ps; %.2f ps).\n", pTime->Rise, pTime->Fall );
        Abc_NtkForEachPi( pNtk, pObj, i )
        {
            SC_Pair * pSlew = Abc_SclObjSlew( p, pObj );
            pSlew->rise = SC_LibTimeFromPs( p->pLib, pTime->Rise );
            pSlew->fall = SC_LibTimeFromPs( p->pLib, pTime->Fall );
        }
    }
    if ( Abc_NodeReadInputDrive(pNtk, 0) != NULL )
    {
        printf( "Input slews for some primary inputs are specified.\n" );
        Abc_NtkForEachPi( pNtk, pObj, i )
        {
            SC_Pair * pSlew = Abc_SclObjSlew( p, pObj );
            pTime = Abc_NodeReadInputDrive(pNtk, i);
            pSlew->rise = SC_LibTimeFromPs( p->pLib, pTime->Rise );
            pSlew->fall = SC_LibTimeFromPs( p->pLib, pTime->Fall );
        }
    }
    // read output load
    pTime = Abc_NtkReadDefaultOutputLoad( pNtk );
    if ( Abc_MaxFloat(pTime->Rise, pTime->Fall) != 0 )
    {
        printf( "Default output load is specified (%.2f ff; %.2f ff).\n", pTime->Rise, pTime->Fall );
        Abc_NtkForEachPo( pNtk, pObj, i )
        {
            SC_Pair * pSlew = Abc_SclObjLoad( p, pObj );
            pSlew->rise = SC_LibCapFromFf( p->pLib, pTime->Rise );
            pSlew->fall = SC_LibCapFromFf( p->pLib, pTime->Fall );
        }
    }
    if ( Abc_NodeReadOutputLoad(pNtk, 0) != NULL )
    {
        printf( "Output loads for some primary outputs are specified.\n" );
        Abc_NtkForEachPo( pNtk, pObj, i )
        {
            SC_Pair * pSlew = Abc_SclObjLoad( p, pObj );
            pTime = Abc_NodeReadOutputLoad(pNtk, i);
            pSlew->rise = SC_LibCapFromFf( p->pLib, pTime->Rise );
            pSlew->fall = SC_LibCapFromFf( p->pLib, pTime->Fall );
        }
    }
}

/**Function*************************************************************

  Synopsis    [Prepare timing manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
SC_Man * Abc_SclManStart( SC_Lib * pLib, Abc_Ntk_t * pNtk, int fUseWireLoads, int fDept, float DUser )
{
    SC_Man * p = Abc_SclManAlloc( pLib, pNtk );
    assert( p->vGates == NULL );
    p->vGates = Abc_SclManFindGates( pLib, pNtk );
    Abc_SclManReadSlewAndLoad( p, pNtk );
    if ( fUseWireLoads )
        p->pWLoadUsed = Abc_SclFindWireLoadModel( pLib, Abc_SclGetTotalArea(p) );
    Abc_SclTimeNtkRecompute( p, &p->SumArea0, &p->MaxDelay0, fDept, DUser );
    p->SumArea = p->SumArea0;
    return p;
}

/**Function*************************************************************

  Synopsis    [Printing out timing information for the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SclTimePerform( SC_Lib * pLib, Abc_Ntk_t * pNtk, int fUseWireLoads, int fShowAll, int fShort, int fDumpStats )
{
    SC_Man * p;
    p = Abc_SclManStart( pLib, pNtk, fUseWireLoads, 1, 0 );   
    Abc_SclTimeNtkPrint( p, fShowAll, fShort );
    if ( fDumpStats )
        Abc_SclDumpStats( p, "stats.txt", 0 );
    Abc_SclManFree( p );
}



/**Function*************************************************************

  Synopsis    [Printing out fanin information.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_SclCheckCommonInputs( Abc_Obj_t * pObj, Abc_Obj_t * pFanin )
{
    Abc_Obj_t * pTemp;
    int i;
    Abc_ObjForEachFanin( pObj, pTemp, i )
        if ( Abc_NodeFindFanin( pFanin, pTemp ) >= 0 )
        {
            printf( "Node %d and its fanin %d have common fanin %d.\n", Abc_ObjId(pObj), Abc_ObjId(pFanin), Abc_ObjId(pTemp) );

            printf( "%-16s : ", Mio_GateReadName((Mio_Gate_t *)pObj->pData) ); 
            Abc_ObjPrint( stdout, pObj );

            printf( "%-16s : ", Mio_GateReadName((Mio_Gate_t *)pFanin->pData) ); 
            Abc_ObjPrint( stdout, pFanin );

            if ( pTemp->pData )
            printf( "%-16s : ", Mio_GateReadName((Mio_Gate_t *)pTemp->pData) ); 
            Abc_ObjPrint( stdout, pTemp );
            return 1;
        }
    return 0;
}
void Abc_SclPrintFaninPairs( SC_Man * p, Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj, * pFanin;
    int i, k;
    Abc_NtkForEachNode( pNtk, pObj, i )
        Abc_ObjForEachFanin( pObj, pFanin, k )
            if ( Abc_ObjIsNode(pFanin) && Abc_ObjFanoutNum(pFanin) == 1 )
                Abc_SclCheckCommonInputs( pObj, pFanin );
}

/**Function*************************************************************

  Synopsis    [Printing out buffer information.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_ObjIsBuffer( Abc_Obj_t * pObj ) { return Abc_ObjIsNode(pObj) && Abc_ObjFaninNum(pObj) == 1; }
int Abc_SclCountNonBufferFanouts( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanout;
    int i, Counter = 0;
    if ( !Abc_ObjIsBuffer(pObj) )
        return 1;
    Abc_ObjForEachFanout( pObj, pFanout, i )
        Counter += Abc_SclCountNonBufferFanouts( pFanout );
    return Counter;
}
int Abc_SclHasBufferFanout( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanout;
    int i;
    Abc_ObjForEachFanout( pObj, pFanout, i )
        if ( Abc_ObjIsBuffer(pFanout) )
            return 1;
    return 0;
}
void Abc_Scl_PrintBuffers( SC_Man * p, Abc_Obj_t * pObj, int nOffset )
{
//    SC_Cell_t * pCell = Abc_SclObjCell(p, pObj);
    Abc_Obj_t * pFanout;
    int i;
    assert( Abc_ObjIsBuffer(pObj) );
    for ( i = 0; i < nOffset; i++ )
        printf( "    " );
    printf( "%6d: %-16s (%2d:%3d)  ", Abc_ObjId(pObj), Mio_GateReadName((Mio_Gate_t *)pObj->pData), 
        Abc_ObjFanoutNum(pObj), Abc_SclCountNonBufferFanouts(pObj) );
    for ( ; i < 4; i++ )
        printf( "    " );
    printf( "a =%5.2f  ",      Abc_SclObjCell(p, pObj)->area );
    printf( "d = (" );
    printf( "%7.2f ps; ",      Abc_SclObjTimePs(p, pObj, 1) );
    printf( "%7.2f ps)  ",     Abc_SclObjTimePs(p, pObj, 0) );
    printf( "l =%6.2f ff   ",  Abc_SclObjLoadFf(p, pObj, 0 ) );
    printf( "s =%6.2f ps   ",  Abc_SclObjSlewPs(p, pObj, 0 ) );
    printf( "sl =%6.2f ps",    Abc_SclObjSlack(p, pObj) );
    printf( "\n" );
    Abc_ObjForEachFanout( pObj, pFanout, i )
        if ( Abc_ObjIsBuffer(pFanout) )
            Abc_Scl_PrintBuffers( p, pFanout, nOffset + 1 );
}
void Abc_SclPrintBufferTrees( SC_Man * p, Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    int i;
    Abc_NtkForEachObj( pNtk, pObj, i )
        if ( Abc_ObjIsBuffer(pObj) && Abc_SclHasBufferFanout(pObj) )
            Abc_Scl_PrintBuffers( p, pObj, 0 ), printf( "\n" );
}
void Abc_SclPrintBuffers( SC_Lib * pLib, Abc_Ntk_t * pNtk, int fVerbose )
{
    int fUseWireLoads = 0;
    SC_Man * p;
    assert( Abc_NtkIsMappedLogic(pNtk) );
    p = Abc_SclManStart( pLib, pNtk, fUseWireLoads, 1, 0 ); 
    Abc_SclPrintBufferTrees( p, pNtk ); 
//    Abc_SclPrintFaninPairs( p, pNtk );
    Abc_SclManFree( p );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

