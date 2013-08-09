/**CFile****************************************************************

  FileName    [sclSize.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Standard-cell library representation.]

  Synopsis    [Core timing analysis used in gate-sizing.]

  Author      [Alan Mishchenko, Niklas Een]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 24, 2012.]

  Revision    [$Id: sclSize.c,v 1.0 2012/08/24 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sclSize.h"
#include "map/mio/mio.h"
#include "misc/vec/vecWec.h"

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
    SC_Cell * pCell = Abc_ObjIsNode(pObj) ? Abc_SclObjCell(pObj) : NULL;
    printf( "%6d : ",           Abc_ObjId(pObj) );
    printf( "%d ",              Abc_ObjFaninNum(pObj) );
    printf( "%4d ",             Abc_ObjFanoutNum(pObj) );
    printf( "%-*s ",            Length, pCell ? pCell->pName : "pi" );
    printf( "A =%7.2f  ",       pCell ? pCell->area : 0.0 );
    printf( "D%s =",            fRise ? "r" : "f" );
    printf( "%5.0f",            Abc_MaxFloat(Abc_SclObjTimePs(p, pObj, 0), Abc_SclObjTimePs(p, pObj, 1)) );
    printf( "%6.0f ps  ",       -Abc_AbsFloat(Abc_SclObjTimePs(p, pObj, 0) - Abc_SclObjTimePs(p, pObj, 1)) );
    printf( "S =%5.0f ps  ",    Abc_SclObjSlewPs(p, pObj, fRise >= 0 ? fRise : 0 ) );
    printf( "Cin =%4.0f ff  ",  pCell ? SC_CellPinCapAve(pCell) : 0.0 );
    printf( "Cout =%5.0f ff  ", Abc_SclObjLoadFf(p, pObj, fRise >= 0 ? fRise : 0 ) );
    printf( "Cmax =%5.0f ff  ", pCell ? SC_CellPin(pCell, pCell->n_inputs)->max_out_cap : 0.0 );
    printf( "G =%5.1f  ",       pCell ? Abc_SclObjLoadAve(p, pObj) / SC_CellPinCap(pCell, 0) : 0.0 );
    printf( "SL =%5.1f ps",     Abc_SclObjSlackPs(p, pObj) );
    printf( "\n" );
}
void Abc_SclTimeNtkPrint( SC_Man * p, int fShowAll, int fPrintPath )
{
    int i, nLength = 0, fRise = 0;
    Abc_Obj_t * pObj, * pPivot = Abc_SclFindCriticalCo( p, &fRise ); 
    float maxDelay = Abc_SclObjTimePs(p, pPivot, fRise);
    p->ReportDelay = maxDelay;

    printf( "WireLoad model = \"%s\"   ", p->pWLoadUsed ? p->pWLoadUsed->pName : "none" );
    printf( "Gates = %6d   ",             Abc_NtkNodeNum(p->pNtk) );
    printf( "Cave = %5.1f   ",            p->EstLoadAve );
    printf( "Min = %5.1f %%   ",          100.0 * Abc_SclCountMinSize(p->pLib, p->pNtk, 0) / Abc_NtkNodeNum(p->pNtk) );
    printf( "Area = %12.2f   ",           Abc_SclGetTotalArea( p ) );
    printf( "Delay = %8.2f ps  ",         maxDelay );
    printf( "Min = %5.1f %%\n",           100.0 * Abc_SclCountNearCriticalNodes(p) / Abc_NtkNodeNum(p->pNtk) );
    if ( !fPrintPath )
        return;

    if ( fShowAll )
    {
//        printf( "Timing information for all nodes: \n" );
        // find the longest cell name
        Abc_NtkForEachNodeReverse( p->pNtk, pObj, i )
            if ( Abc_ObjFaninNum(pObj) > 0 )
                nLength = Abc_MaxInt( nLength, strlen(Abc_SclObjCell(pObj)->pName) );
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
            nLength = Abc_MaxInt( nLength, strlen(Abc_SclObjCell(pObj)->pName) );
            pObj = Abc_SclFindMostCriticalFanin( p, &fRise, pObj );
        }
        // print timing
        pObj = Abc_ObjFanin0(pPivot);
        while ( pObj )//&& Abc_ObjIsNode(pObj) )
        {
            printf( "Path%3d -- ", i-- );
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
static inline void Abc_SclTimeFanin( SC_Man * p, SC_Timing * pTime, Abc_Obj_t * pObj, Abc_Obj_t * pFanin )
{
    SC_Pair * pArrIn   = Abc_SclObjTime( p, pFanin );
    SC_Pair * pSlewIn  = Abc_SclObjSlew( p, pFanin );
    SC_Pair * pLoad    = Abc_SclObjLoad( p, pObj );
    SC_Pair * pArrOut  = Abc_SclObjTime( p, pObj );   // modified
    SC_Pair * pSlewOut = Abc_SclObjSlew( p, pObj );   // modified
    Scl_LibPinArrival( pTime, pArrIn, pSlewIn, pLoad, pArrOut, pSlewOut );
}
static inline void Abc_SclDeptFanin( SC_Man * p, SC_Timing * pTime, Abc_Obj_t * pObj, Abc_Obj_t * pFanin )
{
    SC_Pair * pDepIn   = Abc_SclObjDept( p, pFanin );   // modified
    SC_Pair * pSlewIn  = Abc_SclObjSlew( p, pFanin );
    SC_Pair * pLoad    = Abc_SclObjLoad( p, pObj );
    SC_Pair * pDepOut  = Abc_SclObjDept( p, pObj );
    Scl_LibPinDeparture( pTime, pDepIn, pSlewIn, pLoad, pDepOut );
}
static inline float Abc_SclObjLoadValue( SC_Man * p, Abc_Obj_t * pObj )
{
//    float Value = Abc_MaxFloat(pLoad->fall, pLoad->rise) / (p->EstLoadAve * p->EstLoadMax);
    return 0.5 * (Abc_SclObjLoad(p, pObj)->fall + Abc_SclObjLoad(p, pObj)->rise) / (p->EstLoadAve * p->EstLoadMax);
}
void Abc_SclTimeNode( SC_Man * p, Abc_Obj_t * pObj, int fDept )
{
    SC_Timings * pRTime;
    SC_Timing * pTime;
    SC_Pin * pPin;
    SC_Cell * pCell;
    int k;
    SC_Pair * pLoad = Abc_SclObjLoad( p, pObj );
    float LoadRise = pLoad->rise;
    float LoadFall = pLoad->fall;
    float DeptRise = 0;
    float DeptFall = 0;
    float Value = p->EstLoadMax ? Abc_SclObjLoadValue( p, pObj ) : 0;
    if ( Abc_ObjIsCo(pObj) )
    {
        if ( !fDept )
            Abc_SclObjDupFanin( p, pObj );
        return;
    }
    assert( Abc_ObjIsNode(pObj) );
//    if ( !(Abc_ObjFaninNum(pObj) == 1 && Abc_ObjIsPi(Abc_ObjFanin0(pObj))) && p->EstLoadMax && Value > 1 )
    if ( p->EstLoadMax && Value > 1 )
    {
        pLoad->rise = p->EstLoadAve * p->EstLoadMax;
        pLoad->fall = p->EstLoadAve * p->EstLoadMax;
        if ( fDept )
        {
            SC_Pair * pDepOut  = Abc_SclObjDept( p, pObj );
            float EstDelta = p->EstLinear * log( Value );
            DeptRise = pDepOut->rise;
            DeptFall = pDepOut->fall;
            pDepOut->rise += EstDelta;
            pDepOut->fall += EstDelta;
        }
        p->nEstNodes++;
    }
    // get the library cell
    pCell = Abc_SclObjCell( pObj );
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
    if ( p->EstLoadMax && Value > 1 )
    {
        pLoad->rise = LoadRise;
        pLoad->fall = LoadFall;
        if ( fDept )
        {
            SC_Pair * pDepOut  = Abc_SclObjDept( p, pObj );
            pDepOut->rise = DeptRise;
            pDepOut->fall = DeptFall;
        }
        else
        {
            SC_Pair * pArrOut  = Abc_SclObjTime( p, pObj );
            float EstDelta = p->EstLinear * log( Value );
            pArrOut->rise += EstDelta;
            pArrOut->fall += EstDelta;
        }
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
        printf( "  Updating node %d with gate %s\n", Abc_ObjId(pObj), Abc_SclObjCell(pObj)->pName );
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
    p->nEstNodes = 0;
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
        p->nEstNodes = 0;
        Abc_NtkForEachNodeReverse1( p->pNtk, pObj, i )
            Abc_SclTimeNode( p, pObj, 1 );
        Abc_NtkForEachObj( p->pNtk, pObj, i )
        {
//            if ( Abc_SclObjGetSlack(p, pObj, D) < 0 )
//                printf( "%.2f ", Abc_SclObjGetSlack(p, pObj, D) );
            p->pSlack[i] = Abc_MaxFloat( 0.0, Abc_SclObjGetSlack(p, pObj, D) );
        }
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
/*
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
*/
    pTime = Abc_NtkReadDefaultInputDrive( pNtk );
    if ( Abc_MaxFloat(pTime->Rise, pTime->Fall) != 0 )
    {
        printf( "Default input drive strength is specified (%.2f ff; %.2f ff).\n", pTime->Rise, pTime->Fall );
        if ( p->pInDrive == NULL )
            p->pInDrive = ABC_CALLOC( float, Abc_NtkObjNumMax(pNtk) );
        Abc_NtkForEachPi( pNtk, pObj, i )
            p->pInDrive[Abc_ObjId(pObj)] = 0.5 * SC_LibCapFromFf( p->pLib, pTime->Rise ) + 0.5 * SC_LibCapFromFf( p->pLib, pTime->Fall );
    }
    if ( Abc_NodeReadInputDrive(pNtk, 0) != NULL )
    {
        printf( "Input drive strengths for some primary inputs are specified.\n" );
        if ( p->pInDrive == NULL )
            p->pInDrive = ABC_CALLOC( float, Abc_NtkObjNumMax(pNtk) );
        Abc_NtkForEachPi( pNtk, pObj, i )
        {
            pTime = Abc_NodeReadInputDrive(pNtk, i);
            p->pInDrive[Abc_ObjId(pObj)] = 0.5 * SC_LibCapFromFf( p->pLib, pTime->Rise ) + 0.5 * SC_LibCapFromFf( p->pLib, pTime->Fall );
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
SC_Man * Abc_SclManStart( SC_Lib * pLib, Abc_Ntk_t * pNtk, int fUseWireLoads, int fDept, float DUser, int nTreeCRatio )
{
    SC_Man * p = Abc_SclManAlloc( pLib, pNtk );
    if ( nTreeCRatio )
    {
        p->EstLoadMax = 0.01 * nTreeCRatio;  // max ratio of Cout/Cave when the estimation is used
        p->EstLinear  = 100;                  // linear coefficient
    }
    Abc_SclMioGates2SclGates( pLib, pNtk );
    Abc_SclManReadSlewAndLoad( p, pNtk );
    if ( fUseWireLoads )
    {
        if ( pNtk->pWLoadUsed == NULL )
        {            
            p->pWLoadUsed = Abc_SclFindWireLoadModel( pLib, Abc_SclGetTotalArea(p) );
            pNtk->pWLoadUsed = Abc_UtilStrsav( p->pWLoadUsed->pName );
        }
        else
            p->pWLoadUsed = Abc_SclFetchWireLoadModel( pLib, pNtk->pWLoadUsed );
    }
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
void Abc_SclTimePerform( SC_Lib * pLib, Abc_Ntk_t * pNtk, int nTreeCRatio, int fUseWireLoads, int fShowAll, int fPrintPath, int fDumpStats )
{
    SC_Man * p;
    p = Abc_SclManStart( pLib, pNtk, fUseWireLoads, 1, 0, nTreeCRatio );
    Abc_SclTimeNtkPrint( p, fShowAll, fPrintPath );
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
int Abc_SclHasBufferFanout( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanout;
    int i;
    Abc_ObjForEachFanout( pObj, pFanout, i )
        if ( Abc_ObjIsBuffer(pFanout) )
            return 1;
    return 0;
}
int Abc_SclCountBufferFanoutsInt( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanout;
    int i, Counter = 0;
    Abc_ObjForEachFanout( pObj, pFanout, i )
        if ( Abc_ObjIsBuffer(pFanout) )
            Counter += Abc_SclCountBufferFanoutsInt( pFanout );
    return Counter + Abc_ObjIsBuffer(pObj);
}
int Abc_SclCountBufferFanouts( Abc_Obj_t * pObj )
{
    return Abc_SclCountBufferFanoutsInt(pObj) - Abc_ObjIsBuffer(pObj);
}
int Abc_SclCountNonBufferFanoutsInt( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanout;
    int i, Counter = 0;
    if ( !Abc_ObjIsBuffer(pObj) )
        return 1;
    Abc_ObjForEachFanout( pObj, pFanout, i )
        Counter += Abc_SclCountNonBufferFanoutsInt( pFanout );
    return Counter;
}
int Abc_SclCountNonBufferFanouts( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanout;
    int i, Counter = 0;
    Abc_ObjForEachFanout( pObj, pFanout, i )
        Counter += Abc_SclCountNonBufferFanoutsInt( pFanout );
    return Counter;
}
float Abc_SclCountNonBufferDelayInt( SC_Man * p, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanout;
    float Delay = 0;
    int i; 
    if ( !Abc_ObjIsBuffer(pObj) )
        return Abc_SclObjTimePs(p, pObj, 1);
    Abc_ObjForEachFanout( pObj, pFanout, i )
        Delay += Abc_SclCountNonBufferDelayInt( p, pFanout );
    return Delay;
}
float Abc_SclCountNonBufferDelay( SC_Man * p, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanout;
    float Delay = 0;
    int i; 
    Abc_ObjForEachFanout( pObj, pFanout, i )
        Delay += Abc_SclCountNonBufferDelayInt( p, pFanout );
    return Delay;
}
float Abc_SclCountNonBufferLoadInt( SC_Man * p, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanout;
    float Load = 0;
    int i; 
    if ( !Abc_ObjIsBuffer(pObj) )
        return 0;
    Abc_ObjForEachFanout( pObj, pFanout, i )
        Load += Abc_SclCountNonBufferLoadInt( p, pFanout );
    Load += 0.5 * Abc_SclObjLoad(p, pObj)->rise + 0.5 * Abc_SclObjLoad(p, pObj)->fall;
    Load -= 0.5 * SC_CellPin(Abc_SclObjCell(pObj), 0)->rise_cap + 0.5 * SC_CellPin(Abc_SclObjCell(pObj), 0)->fall_cap;
    return Load;
}
float Abc_SclCountNonBufferLoad( SC_Man * p, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanout;
    float Load = 0;
    int i; 
    Abc_ObjForEachFanout( pObj, pFanout, i )
        Load += Abc_SclCountNonBufferLoadInt( p, pFanout );
    Load += 0.5 * Abc_SclObjLoad(p, pObj)->rise + 0.5 * Abc_SclObjLoad(p, pObj)->fall;
    return Load;
}
void Abc_SclPrintBuffersOne( SC_Man * p, Abc_Obj_t * pObj, int nOffset )
{
    int i;
    for ( i = 0; i < nOffset; i++ )
        printf( "    " );
    printf( "%6d: %-16s (%2d:%3d:%3d)  ", 
        Abc_ObjId(pObj), 
        Abc_ObjIsPi(pObj) ? "pi" : Mio_GateReadName((Mio_Gate_t *)pObj->pData), 
        Abc_ObjFanoutNum(pObj), 
        Abc_SclCountBufferFanouts(pObj), 
        Abc_SclCountNonBufferFanouts(pObj) );
    for ( ; i < 4; i++ )
        printf( "    " );
    printf( "a =%5.2f  ",      Abc_ObjIsPi(pObj) ? 0 : Abc_SclObjCell(pObj)->area );
    printf( "d = (" );
    printf( "%6.0f ps; ",      Abc_SclObjTimePs(p, pObj, 1) );
    printf( "%6.0f ps)  ",     Abc_SclObjTimePs(p, pObj, 0) );
    printf( "l =%5.0f ff  ",   Abc_SclObjLoadFf(p, pObj, 0 ) );
    printf( "s =%5.0f ps   ",  Abc_SclObjSlewPs(p, pObj, 0 ) );
    printf( "sl =%5.0f ps   ", Abc_SclObjSlackPs(p, pObj) );
    if ( nOffset == 0 )
    {
    printf( "L =%5.0f ff   ",  SC_LibCapFf( p->pLib, Abc_SclCountNonBufferLoad(p, pObj) ) );
    printf( "Lx =%5.0f ff  ",  100.0*Abc_SclCountNonBufferLoad(p, pObj)/p->EstLoadAve );
    printf( "Dx =%5.0f ps  ",  Abc_SclCountNonBufferDelay(p, pObj)/Abc_SclCountNonBufferFanouts(pObj) - Abc_SclObjTimePs(p, pObj, 1) );
    printf( "Cx =%5.0f ps",    (Abc_SclCountNonBufferDelay(p, pObj)/Abc_SclCountNonBufferFanouts(pObj) - Abc_SclObjTimePs(p, pObj, 1))/log(Abc_SclCountNonBufferLoad(p, pObj)/p->EstLoadAve) );
    }
    printf( "\n" );
}
void Abc_SclPrintBuffersInt( SC_Man * p, Abc_Obj_t * pObj, int nOffset )
{
    Abc_Obj_t * pFanout;
    int i;
    Abc_SclPrintBuffersOne( p, pObj, nOffset );
    assert( Abc_ObjIsBuffer(pObj) );
    Abc_ObjForEachFanout( pObj, pFanout, i )
        if ( Abc_ObjIsBuffer(pFanout) )
            Abc_SclPrintBuffersInt( p, pFanout, nOffset + 1 );
}
void Abc_SclPrintBufferTrees( SC_Man * p, Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj, * pFanout;
    int i, k;
    Abc_NtkForEachObj( pNtk, pObj, i )
    {
        if ( !Abc_ObjIsBuffer(pObj) && Abc_SclCountBufferFanouts(pObj) > 3 )
        {           
            Abc_SclPrintBuffersOne( p, pObj, 0 );
            Abc_ObjForEachFanout( pObj, pFanout, k )
                if ( Abc_ObjIsBuffer(pFanout) )
                    Abc_SclPrintBuffersInt( p, pFanout, 1 );
            printf( "\n" );
        }
    }
}
void Abc_SclPrintBuffers( SC_Lib * pLib, Abc_Ntk_t * pNtk, int fVerbose )
{
    int fUseWireLoads = 0;
    SC_Man * p;
    assert( Abc_NtkIsMappedLogic(pNtk) );
    p = Abc_SclManStart( pLib, pNtk, fUseWireLoads, 1, 0, 10000 ); 
    Abc_SclPrintBufferTrees( p, pNtk ); 
//    Abc_SclPrintFaninPairs( p, pNtk );
    Abc_SclManFree( p );
}


/**Function*************************************************************

  Synopsis    [Checks if the input drive capability is ok.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_SclInputDriveOk( SC_Man * p, Abc_Obj_t * pObj, SC_Cell * pCell )
{
    Abc_Obj_t * pFanin;
    int i;
    assert( Abc_ObjFaninNum(pObj) == pCell->n_inputs );
    Abc_ObjForEachFanin( pObj, pFanin, i )
        if ( Abc_ObjIsPi(pFanin) && p->pInDrive[Abc_ObjId(pFanin)] > 0 && 
            (p->pInDrive[Abc_ObjId(pFanin)] / Abc_ObjFanoutNum(pFanin)) < 
            Abc_MaxFloat(SC_CellPin(pCell, i)->rise_cap, SC_CellPin(pCell, i)->fall_cap) )
                return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Select nodes that need to be buffered.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Wec_t * Abc_SclSelectSplitNodes( SC_Man * p, Abc_Ntk_t * pNtk )
{
    Vec_Wec_t * vSplits;
    Vec_Int_t * vCrits, * vNonCrits, * vLevel;
    Abc_Obj_t * pObj, * pFanout;
    int i, k;
    assert( p->EstLoadMax > 0 );
    vCrits = Vec_IntAlloc( 1000 );
    vNonCrits = Vec_IntAlloc( 1000 );
    vSplits = Vec_WecAlloc( 1000 );
    Abc_NtkForEachNodeCi( pNtk, pObj, i )
    {
        if ( Abc_SclObjLoadValue(p, pObj) < 1 )
        {
//            printf( "%d ", Abc_ObjFanoutNum(pObj) );
            continue;
        }
/*
        printf( "%d : %.0f   ", i, 0.5 * (Abc_SclObjLoad(p, pObj)->fall + Abc_SclObjLoad(p, pObj)->rise) );
        Abc_ObjForEachFanout( pObj, pFanout, k )
            printf( "%.1f ", SC_CellPinCapAve(Abc_SclObjCell(pFanout)) );
        printf( "\n" );
*/
        // skip non-critical nodes
//        if ( Abc_SclObjSlack(p, pObj) > 100 )
//            continue;
        // collect non-critical fanouts of the node
        Vec_IntClear( vCrits );
        Vec_IntClear( vNonCrits );
        Abc_ObjForEachFanout( pObj, pFanout, k )
            if ( Abc_SclObjSlack(p, pFanout) < 100 )
                Vec_IntPush( vCrits, Abc_ObjId(pFanout) );
            else
                Vec_IntPush( vNonCrits, Abc_ObjId(pFanout) );
//        assert( Vec_IntSize(vNonCrits) < Abc_ObjFanoutNum(pObj) );
        // skip if there is nothing to split
//        if ( Vec_IntSize(vNonCrits) < 2 )
//            continue;
        // remember them
        vLevel = Vec_WecPushLevel( vSplits );
        Vec_IntPush( vLevel, i );
        Vec_IntAppend( vLevel, vCrits );
        // remember them
        vLevel = Vec_WecPushLevel( vSplits );
        Vec_IntPush( vLevel, i );
        Vec_IntAppend( vLevel, vNonCrits );
    }
    Vec_IntFree( vCrits );
    Vec_IntFree( vNonCrits );
    // print out
    printf( "Collected %d nodes to split.\n", Vec_WecSize(vSplits) );
    return vSplits;
}
void Abc_SclPerformSplit( SC_Man * p, Abc_Ntk_t * pNtk, Vec_Wec_t * vSplits )
{
    Abc_Obj_t * pObj, * pObjInv, * pFanout;
    Vec_Int_t * vLevel;
    int i, k;
    assert( pNtk->vPhases != NULL );
    Vec_WecForEachLevel( vSplits, vLevel, i )
    {
        pObj = Abc_NtkObj( pNtk, Vec_IntEntry(vLevel, 0) );
        pObjInv = Abc_NtkCreateNodeInv( pNtk, pObj );
        Abc_NtkForEachObjVecStart( vLevel, pNtk, pFanout, k, 1 )
        {
            Abc_ObjFaninFlipPhase( pFanout, Abc_NodeFindFanin(pFanout, pObj) );
            Abc_ObjPatchFanin( pFanout, pObj, pObjInv );
        }
    }
    Vec_IntFillExtra( pNtk->vPhases, Abc_NtkObjNumMax(pNtk), 0 );
}
Abc_Ntk_t * Abc_SclBuffSizeStep( SC_Lib * pLib, Abc_Ntk_t * pNtk, int nTreeCRatio, int fUseWireLoads )
{
    SC_Man * p;
    Vec_Wec_t * vSplits;
    p = Abc_SclManStart( pLib, pNtk, fUseWireLoads, 1, 0, nTreeCRatio );
    Abc_SclTimeNtkPrint( p, 0, 0 );
    if ( p->nEstNodes )
        printf( "Estimated nodes = %d.\n", p->nEstNodes );
    vSplits = Abc_SclSelectSplitNodes( p, pNtk );
    Abc_SclPerformSplit( p, pNtk, vSplits );
    Vec_WecFree( vSplits );
    Abc_SclManFree( p );
    return Abc_NtkDupDfs( pNtk );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

