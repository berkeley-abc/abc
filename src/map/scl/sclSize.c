/**CFile****************************************************************

  FileName    [sclSize.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Standard-cell library representation.]

  Synopsis    [Gate sizing algorithms.]

  Author      [Alan Mishchenko, Niklas Een]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 24, 2012.]

  Revision    [$Id: sclSize.c,v 1.0 2012/08/24 00:00:00 alanmi Exp $]

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

  Synopsis    [Collect nodes in network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_SclCollectNodes( Abc_Ntk_t * p )
{
    Vec_Int_t * vRes;
    Abc_Obj_t * pObj;
    int i;
    vRes = Vec_IntAlloc( Abc_NtkNodeNum(p) );
    Abc_NtkForEachNode( p, pObj, i )
        Vec_IntPush( vRes, i );
    return vRes;
}

/**Function*************************************************************

  Synopsis    [Collect near-critical CO nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_SclFindCriticalCoRange( SC_Man * p, int Range )
{
    float fMaxArr = Abc_SclGetMaxDelay( p );
    Vec_Int_t * vPivots;
    Abc_Obj_t * pObj;
    int i;
    vPivots = Vec_IntAlloc( 100 );
    Abc_NtkForEachCo( p->pNtk, pObj, i )
        if ( Abc_SclObjTimeMax(p, pObj) >= fMaxArr * (100 - Range) / 100 )
            Vec_IntPush( vPivots, Abc_ObjId(pObj) );
    assert( Vec_IntSize(vPivots) > 0 );
    return vPivots;
}

/**Function*************************************************************

  Synopsis    [Collect nodes in cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SclFindCriticalCone_rec( Abc_Obj_t * pObj, Vec_Int_t * vVisited )
{
    Abc_Obj_t * pNext;
    int i;
    if ( Abc_ObjIsCi(pObj) )
        return;
    if ( Abc_NodeIsTravIdCurrent( pObj ) )
        return;
    Abc_NodeSetTravIdCurrent( pObj );
    assert( Abc_ObjIsNode(pObj) );
    Abc_ObjForEachFanin( pObj, pNext, i )
        Abc_SclFindCriticalCone_rec( pNext, vVisited );
    Vec_IntPush( vVisited, Abc_ObjId(pObj) );
}
Vec_Int_t * Abc_SclFindCriticalCone( SC_Man * p, int Range, Vec_Int_t ** pvPivots )
{
    Vec_Int_t * vPivots = Abc_SclFindCriticalCoRange( p, Range );
    Vec_Int_t * vPath = Vec_IntAlloc( 100 );
    Abc_Obj_t * pObj;
    int i;
    Abc_NtkIncrementTravId( p->pNtk ); 
    Abc_NtkForEachObjVec( vPivots, p->pNtk, pObj, i )
        Abc_SclFindCriticalCone_rec( Abc_ObjFanin0(pObj), vPath );
    if ( pvPivots ) 
        *pvPivots = vPivots;
    else
        Vec_IntFree( vPivots );
    return vPath;  
}

/**Function*************************************************************

  Synopsis    [Collect nodes in critical path.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_SclFindCriticalPath( SC_Man * p, int Range, Vec_Int_t ** pvPivots )
{
    Vec_Int_t * vPivots = Abc_SclFindCriticalCoRange( p, Range );
    Vec_Int_t * vPath = Vec_IntAlloc( 100 );
    Abc_Obj_t * pObj;
    int i, fRise = 0;
    Abc_NtkForEachObjVec( vPivots, p->pNtk, pObj, i )
    {
        pObj = Abc_ObjFanin0(pObj);
        while ( pObj && Abc_ObjIsNode(pObj) )
        {
            Vec_IntPush( vPath, Abc_ObjId(pObj) );
            pObj = Abc_SclFindMostCriticalFanin( p, &fRise, pObj );
        }
    }
    if ( pvPivots ) 
        *pvPivots = vPivots;
    else
        Vec_IntFree( vPivots );
    return vPath;  
}

/**Function*************************************************************

  Synopsis    [Collect TFO of the fanins of the object.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SclCollectTfo_rec( Abc_Obj_t * pObj, Vec_Int_t * vVisited )
{
    Abc_Obj_t * pNext;
    int i;
//    if ( Abc_ObjIsCo(pObj) )
//        return;
    if ( Abc_NodeIsTravIdCurrent( pObj ) )
        return;
    Abc_NodeSetTravIdCurrent( pObj );
    Abc_ObjForEachFanout( pObj, pNext, i )
        Abc_SclCollectTfo_rec( pNext, vVisited );
    Vec_IntPush( vVisited, Abc_ObjId(pObj) );
}
void Abc_SclMarkTfi_rec( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pNext;
    int i;
    if ( Abc_ObjIsCi(pObj) )
        return; 
    if ( !Abc_NodeIsTravIdPrevious( pObj ) )
        return;
    if ( Abc_NodeIsTravIdCurrent( pObj ) )
        return;
    Abc_NodeSetTravIdCurrent( pObj );
    assert( Abc_ObjIsNode(pObj) || Abc_ObjIsCo(pObj) );
    Abc_ObjForEachFanin( pObj, pNext, i )
        Abc_SclMarkTfi_rec( pNext );
}
Vec_Int_t * Abc_SclCollectTfo( Abc_Ntk_t * p, Abc_Obj_t * pObj, Vec_Int_t * vPivots )
{
    Vec_Int_t * vVisited;
    Abc_Obj_t * pFanin;
    int i, k;
    assert( Abc_ObjIsNode(pObj) );
    vVisited = Vec_IntAlloc( 100 );
    // collect nodes in the TFO
    Abc_NtkIncrementTravId( p ); 
    Abc_SclCollectTfo_rec( pObj, vVisited );
    Abc_ObjForEachFanin( pObj, pFanin, i )
        if ( Abc_ObjIsNode(pFanin) )
            Abc_SclCollectTfo_rec( pFanin, vVisited );
    if ( vPivots )
    {
        // mark nodes in the TFI
        Abc_NtkIncrementTravId( p ); 
        Abc_NtkForEachObjVec( vPivots, p, pObj, i )
            Abc_SclMarkTfi_rec( pObj );
        // remove unmarked nodes
        k = 0;
        Abc_NtkForEachObjVec( vVisited, p, pObj, i )
            if ( Abc_NodeIsTravIdCurrent( pObj ) )
                Vec_IntWriteEntry( vVisited, k++, Abc_ObjId(pObj) );
        Vec_IntShrink( vVisited, k );
    }
    // reverse order
    Vec_IntReverseOrder( vVisited );
    return vVisited;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
SC_Cell * Abc_SclObjResiable( SC_Man * p, Abc_Obj_t * pObj )
{
    SC_Cell * pOld = Abc_SclObjCell( p, pObj );
    return pOld->pNext != pOld ? pOld->pNext : NULL;
}
float Abc_SclSizingGain( SC_Man * p, Abc_Obj_t * pPivot, Vec_Int_t * vPivots )
{
    double dGain = 0;
    Vec_Int_t * vCone;
    Abc_Obj_t * pObj;
    int i;
    assert( Abc_ObjIsNode(pPivot) );
    vCone = Abc_SclCollectTfo( p->pNtk, pPivot, vPivots );
    Abc_SclConeStore( p, vCone );
    Abc_SclTimeCone( p, vCone );
//    Abc_NtkForEachObjVec( vCone, p->pNtk, pObj, i )
    Abc_NtkForEachObjVec( vPivots, p->pNtk, pObj, i )
        if ( Abc_ObjIsCo(pObj) )
        {
            Abc_SclObjDupFanin( p, pObj );
            dGain += Abc_SclObjGain( p, pObj );
        }
    Abc_SclConeRestore( p, vCone );
    Vec_IntFree( vCone );
    return dGain;
}
Abc_Obj_t * Abc_SclChooseBiggestGain( SC_Man * p, Vec_Int_t * vPath, Vec_Int_t * vPivots )
{
    SC_Cell * pOld, * pNew;
    Abc_Obj_t * pPivot = NULL, * pObj;
    double dGainBest = 0.00001, dGain;
    int i, gateId;
    Abc_NtkForEachObjVec( vPath, p->pNtk, pObj, i )
    {
        if ( Abc_ObjIsCo(pObj) )
            continue;
        pOld = Abc_SclObjCell( p, pObj );
        pNew = Abc_SclObjResiable( p, pObj );
        if ( pNew == NULL )
            continue;
//printf( "changing %s for %s at node %d   ", pOld->pName, pNew->pName, Abc_ObjId(pObj) );
        gateId = Vec_IntEntry(p->vGates, Abc_ObjId(pObj));
        Vec_IntWriteEntry( p->vGates, Abc_ObjId(pObj), Abc_SclCellFind(p->pLib, pNew->pName) );
        
        Abc_SclUpdateLoad( p, pObj, pOld, pNew );
        dGain = Abc_SclSizingGain( p, pObj, vPivots );
        Abc_SclUpdateLoad( p, pObj, pNew, pOld );
//printf( "gain is %f\n", dGain );
        Vec_IntWriteEntry( p->vGates, Abc_ObjId(pObj), Abc_SclCellFind(p->pLib, pOld->pName) );
        assert( gateId == Vec_IntEntry(p->vGates, Abc_ObjId(pObj)) );
        if ( dGainBest < dGain )
        {
            dGainBest = dGain;
            pPivot = pObj;
        }
    }
    return pPivot;
}
void Abc_SclUpdateNetwork( SC_Man * p, Abc_Obj_t * pObj, int iStep, int fVerbose )
{
    Vec_Int_t * vCone;
    SC_Cell * pOld, * pNew;
    // find new gate
    pOld = Abc_SclObjCell( p, pObj );
    pNew = Abc_SclObjResiable( p, pObj );
    assert( pNew != NULL );
    // update gate
    Abc_SclUpdateLoad( p, pObj, pOld, pNew );
    p->SumArea += pNew->area - pOld->area;
    Vec_IntWriteEntry( p->vGates, Abc_ObjId(pObj), Abc_SclCellFind(p->pLib, pNew->pName) );
    // update info
    vCone = Abc_SclCollectTfo( p->pNtk, pObj, NULL );
    Abc_SclConeStore( p, vCone );
    Abc_SclTimeCone( p, vCone );
    Vec_IntFree( vCone );
    // print output
    if ( fVerbose )
    {
        printf( "%5d : ",              iStep );
        printf( "%5d  ",               Abc_ObjId(pObj) );
        printf( "%-12s->  %-12s  ",    pOld->pName, pNew->pName );
        printf( "delay =%8.2f ps    ", SC_LibTimePs(p->pLib, Abc_SclGetMaxDelay(p)) );
        printf( "area =%10.2f   ",     p->SumArea );
//        Abc_PrintTime( 1, "Time",      clock() - p->clkStart );
        ABC_PRTr( "Time", clock() - p->clkStart );
    }
}
 
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SclSizingPerform( SC_Lib * pLib, Abc_Ntk_t * pNtk, int nSteps, int nRange, int fTryAll, int fPrintCP, int fVerbose )
{
    SC_Man * p;
    Vec_Int_t * vPath, * vPivots;
    Abc_Obj_t * pBest;
    int i, nCones = 0;
    p = Abc_SclManStart( pLib, pNtk );
    if ( fPrintCP )
        Abc_SclTimeNtkPrint( p, 0 );
    if ( fVerbose )
        printf( "Iterative gate-sizing of network \"%s\" with library \"%s\":\n", Abc_NtkName(pNtk), pLib->pName );
    if ( fVerbose )
    {
//        printf( "%5d :                                      ", 0 );
        printf( "Starting parameters of current mapping:      " );
        printf( "delay =%8.2f ps    ", SC_LibTimePs(p->pLib, Abc_SclGetMaxDelay(p)) );
        printf( "area =%10.2f   ",     p->SumArea );
        Abc_PrintTime( 1, "Time",      clock() - p->clkStart );
    }
    for ( i = 0; i < nSteps; i++ )
    {
        vPath = Abc_SclFindCriticalPath( p, nRange, &vPivots );
        pBest = Abc_SclChooseBiggestGain( p, vPath, vPivots );
        Vec_IntFree( vPath );
        Vec_IntFree( vPivots );
        if ( pBest == NULL )
        {
            if ( fTryAll )
            {
                vPath = Abc_SclFindCriticalCone( p, nRange, &vPivots );
//                vPath = Abc_SclFindCriticalPath( p, nRange+5, &vPivots );
                pBest = Abc_SclChooseBiggestGain( p, vPath, vPivots );
                Vec_IntFree( vPath );
                Vec_IntFree( vPivots );
                nCones++;
            }
            if ( pBest == NULL )
                break;
        }
        Abc_SclUpdateNetwork( p, pBest, i+1, fVerbose );
        // recompute loads every 100 steps
        if ( i && i % 100 == 0 )
            Abc_SclComputeLoad( p );
    }
    p->MaxDelay = Abc_SclGetMaxDelay(p);
    if ( fPrintCP )
        Abc_SclTimeNtkPrint( p, 0 );
    // print cumulative statistics
    printf( "Cones: %d. ",       nCones );
    printf( "Resized: %d. ",     i );
    printf( "Delay: " );
    printf( "%.2f -> %.2f ps ",  SC_LibTimePs(p->pLib, p->MaxDelay0), SC_LibTimePs(p->pLib, p->MaxDelay) );
    printf( "(%+.1f %%).  ",     100.0 * (p->MaxDelay - p->MaxDelay0)/ p->MaxDelay0 );
    printf( "Area: " );
    printf( "%.2f -> %.2f ",     p->SumArea0, p->SumArea );
    printf( "(%+.1f %%).  ",     100.0 * (p->SumArea - p->SumArea0)/ p->SumArea0 );
    Abc_PrintTime( 1, "Time",    clock() - p->clkStart );
    // save the result and quit
    Abc_SclManSetGates( pLib, pNtk, p->vGates ); // updates gate pointers
    Abc_SclManFree( p );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

