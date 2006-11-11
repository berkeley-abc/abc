/**CFile****************************************************************

  FileName    [retFlow.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Implementation of maximum flow (min-area retiming).]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - Oct 31, 2006.]

  Revision    [$Id: retFlow.c,v 1.00 2006/10/31 00:00:00 alanmi Exp $]

***********************************************************************/

#include "retInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline int         Abc_ObjSetPath( Abc_Obj_t * pObj, Abc_Obj_t * pNext ) { pObj->pCopy = pNext; return 1;   }
static inline Abc_Obj_t * Abc_ObjGetPath( Abc_Obj_t * pObj )                    { return pObj->pCopy;              }
static inline Abc_Obj_t * Abc_ObjGetFanoutPath( Abc_Obj_t * pObj ) 
{ 
    Abc_Obj_t * pFanout;
    int i;
    assert( Abc_ObjGetPath(pObj) ); 
    Abc_ObjForEachFanout( pObj, pFanout, i )
        if ( Abc_ObjGetPath(pFanout) == pObj )
            return pFanout;
    return NULL;
}
static inline Abc_Obj_t * Abc_ObjGetFaninPath( Abc_Obj_t * pObj ) 
{ 
    Abc_Obj_t * pFanin;
    int i;
    assert( Abc_ObjGetPath(pObj) ); 
    Abc_ObjForEachFanin( pObj, pFanin, i )
        if ( Abc_ObjGetPath(pFanin) == pObj )
            return pFanin;
    return NULL;
}

static int         Abc_NtkMaxFlowPath( Abc_Ntk_t * pNtk, int * pStart, int fForward );
static int         Abc_NtkMaxFlowBwdPath_rec( Abc_Obj_t * pObj );
static int         Abc_NtkMaxFlowFwdPath_rec( Abc_Obj_t * pObj );
static Vec_Ptr_t * Abc_NtkMaxFlowMinCut( Abc_Ntk_t * pNtk );
static int         Abc_NtkMaxFlowVerifyCut( Abc_Ntk_t * pNtk, Vec_Ptr_t * vMinCut, int fForward );
static void        Abc_NtkMaxFlowPrintFlow( Abc_Ntk_t * pNtk, int fForward );
static void        Abc_NtkMaxFlowPrintCut( Vec_Ptr_t * vMinCut );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Test-bench for the max-flow computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkMaxFlowTest( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vMinCut;
    Abc_Obj_t * pObj;
    int i;

    // forward flow
    Abc_NtkForEachPo( pNtk, pObj, i )
        pObj->fMarkA = 1;
    Abc_NtkForEachLatch( pNtk, pObj, i )
        pObj->fMarkA = Abc_ObjFanin0(pObj)->fMarkA = 1;
    vMinCut = Abc_NtkMaxFlow( pNtk, 1, 1 );
    Vec_PtrFree( vMinCut );
    Abc_NtkCleanMarkA( pNtk );

    // backward flow
    Abc_NtkForEachPi( pNtk, pObj, i )
        pObj->fMarkA = 1;
    Abc_NtkForEachLatch( pNtk, pObj, i )
        pObj->fMarkA = Abc_ObjFanout0(pObj)->fMarkA = 1;
    vMinCut = Abc_NtkMaxFlow( pNtk, 0, 1 );
    Vec_PtrFree( vMinCut );
    Abc_NtkCleanMarkA( pNtk );
}

/**Function*************************************************************

  Synopsis    [Implementation of max-flow/min-cut computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkMaxFlow( Abc_Ntk_t * pNtk, int fForward, int fVerbose )
{
    Vec_Ptr_t * vMinCut;
    int Flow, RetValue;
    int clk = clock();
    int Start = 0;

    // find the max-flow
    Abc_NtkCleanCopy( pNtk );
    for ( Flow = 0; Abc_NtkMaxFlowPath( pNtk, &Start, fForward ); Flow++ );
//    Abc_NtkMaxFlowPrintFlow( pNtk, fForward );

    // find the min-cut with the smallest volume
    RetValue = Abc_NtkMaxFlowPath( pNtk, NULL, fForward );
    assert( RetValue == 0 );
    vMinCut = Abc_NtkMaxFlowMinCut( pNtk );
    if ( !Abc_NtkMaxFlowVerifyCut(pNtk, vMinCut, fForward) )
        printf( "Abc_NtkMaxFlow() error! The computed min-cut is not a cut!\n" );

    // report the results
    if ( fVerbose )
    {
    printf( "Latches = %6d. %s max-flow = %6d.  Min-cut = %6d.  ", 
        Abc_NtkLatchNum(pNtk), fForward? "Forward " : "Backward", Flow, Vec_PtrSize(vMinCut) );
PRT( "Time", clock() - clk );
    }

//    Abc_NtkMaxFlowPrintCut( vMinCut );
    return vMinCut;
}

/**Function*************************************************************

  Synopsis    [Finds and augments one path.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkMaxFlowPath( Abc_Ntk_t * pNtk, int * pStart, int fForward )
{
    Abc_Obj_t * pLatch;
    int i, LatchStart = pStart? *pStart : 0;
    Abc_NtkIncrementTravId(pNtk);
    Vec_PtrForEachEntryStart( pNtk->vBoxes, pLatch, i, LatchStart )
    {
        if ( !Abc_ObjIsLatch(pLatch) )
            continue;
        if ( fForward )
        {
            assert( !Abc_ObjFanout0(pLatch)->fMarkA );
            if ( Abc_NtkMaxFlowFwdPath_rec( Abc_ObjFanout0(pLatch) ) )
            {
                if ( pStart ) *pStart = i + 1;
                return 1;
            }
        }
        else
        {
            assert( !Abc_ObjFanin0(pLatch)->fMarkA );
            if ( Abc_NtkMaxFlowBwdPath_rec( Abc_ObjFanin0(pLatch) ) )
            {
                if ( pStart ) *pStart = i + 1;
                return 1;
            }
        }
    }
    if ( pStart ) *pStart = 0;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Tries to find an augmenting path originating in this node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkMaxFlowBwdPath_rec( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanout, * pFanin;
    int i;
    // skip visited nodes
    if ( Abc_NodeIsTravIdCurrent(pObj) )
        return 0;
    Abc_NodeSetTravIdCurrent(pObj);
    // process node without flow
    if ( !Abc_ObjGetPath(pObj) )
    {
        // start the path if we reached a terminal node
        if ( pObj->fMarkA )
            return Abc_ObjSetPath( pObj, (void *)1 );
        // explore the fanins
        Abc_ObjForEachFanin( pObj, pFanin, i )
            if ( Abc_NtkMaxFlowBwdPath_rec(pFanin) )
                return Abc_ObjSetPath( pObj, pFanin );
        return 0;
    }
    // pObj has flow - find the fanout with flow
    pFanout = Abc_ObjGetFanoutPath( pObj );
    if ( pFanout == NULL )
        return 0;
    // go through the fanins of the fanout with flow
    Abc_ObjForEachFanin( pFanout, pFanin, i )
        if ( pFanin != pObj && Abc_NtkMaxFlowBwdPath_rec( pFanin ) )
            return Abc_ObjSetPath( pFanout, pFanin );
    // try the fanout
    if ( Abc_NtkMaxFlowBwdPath_rec( pFanout ) )
        return Abc_ObjSetPath( pFanout, NULL );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Tries to find an augmenting path originating in this node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkMaxFlowFwdPath_rec( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanout, * pFanin;
    int i;
    // skip visited nodes
    if ( Abc_NodeIsTravIdCurrent(pObj) )
        return 0;
    Abc_NodeSetTravIdCurrent(pObj);
    // process node without flow
    if ( !Abc_ObjGetPath(pObj) )
    { 
        // start the path if we reached a terminal node
        if ( pObj->fMarkA )
            return Abc_ObjSetPath( pObj, (void *)1 );
        // explore the fanins
        Abc_ObjForEachFanout( pObj, pFanout, i )
            if ( Abc_NtkMaxFlowFwdPath_rec(pFanout) )
                return Abc_ObjSetPath( pObj, pFanout );
        return 0;
    }
    // pObj has flow - find the fanout with flow
    pFanin = Abc_ObjGetFaninPath( pObj );
    if ( pFanin == NULL )
        return 0;
    // go through the fanins of the fanout with flow
    Abc_ObjForEachFanout( pFanin, pFanout, i )
        if ( pFanout != pObj && Abc_NtkMaxFlowFwdPath_rec( pFanout ) )
            return Abc_ObjSetPath( pFanin, pFanout );
    // try the fanout
    if ( Abc_NtkMaxFlowFwdPath_rec( pFanin ) )
        return Abc_ObjSetPath( pFanin, NULL );
    return 0;
}


/**Function*************************************************************

  Synopsis    [Find one minumum cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkMaxFlowMinCut( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vMinCut;
    Abc_Obj_t * pObj;
    int i;
    // collect the cut nodes
    vMinCut = Vec_PtrAlloc( Abc_NtkLatchNum(pNtk) );
    Abc_NtkForEachObj( pNtk, pObj, i )
    {
        // node without flow is not a cut node
        if ( !Abc_ObjGetPath(pObj) )
            continue;
        // unvisited node is below the cut
        if ( !Abc_NodeIsTravIdCurrent(pObj) )
            continue;
        // add terminal with flow or node whose path is not visited
        if ( pObj->fMarkA || !Abc_NodeIsTravIdCurrent( Abc_ObjGetPath(pObj) ) )
            Vec_PtrPush( vMinCut, pObj );
    }
    return vMinCut;
}

/**Function*************************************************************

  Synopsis    [Verifies the min-cut is indeed a cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkMaxFlowVerifyCut_rec( Abc_Obj_t * pObj, int fForward )
{
    Abc_Obj_t * pNext;
    int i;
    // skip visited nodes
    if ( Abc_NodeIsTravIdCurrent(pObj) )
        return 1;
    Abc_NodeSetTravIdCurrent(pObj);
    // visit the node
    if ( fForward )
    {
        if ( Abc_ObjIsCo(pObj) )
            return 0;
        // explore the fanouts
        Abc_ObjForEachFanout( pObj, pNext, i )
            if ( !Abc_NtkMaxFlowVerifyCut_rec(pNext, fForward) )
                return 0;
    }
    else
    {
        if ( Abc_ObjIsCi(pObj) )
            return 0;
        // explore the fanins
        Abc_ObjForEachFanin( pObj, pNext, i )
            if ( !Abc_NtkMaxFlowVerifyCut_rec(pNext, fForward) )
                return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Verifies the min-cut is indeed a cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkMaxFlowVerifyCut( Abc_Ntk_t * pNtk, Vec_Ptr_t * vMinCut, int fForward )
{
    Abc_Obj_t * pObj;
    int i;
    // mark the cut with the current traversal ID
    Abc_NtkIncrementTravId(pNtk);
    Vec_PtrForEachEntry( vMinCut, pObj, i )
        Abc_NodeSetTravIdCurrent( pObj );
    // search from the latches for a path to the COs/CIs
    Abc_NtkForEachLatch( pNtk, pObj, i )
    {
        if ( fForward )
        {
            assert( !Abc_ObjFanout0(pObj)->fMarkA );
            if ( !Abc_NtkMaxFlowVerifyCut_rec( Abc_ObjFanout0(pObj), fForward ) )
                return 0;
        }
        else
        {
            assert( !Abc_ObjFanin0(pObj)->fMarkA );
            if ( !Abc_NtkMaxFlowVerifyCut_rec( Abc_ObjFanin0(pObj), fForward ) )
                return 0;
        }
    }
/*
    {
        // count the volume of the cut
        int Counter = 0;
        Abc_NtkForEachObj( pNtk, pObj, i )
            Counter += Abc_NodeIsTravIdCurrent( pObj );
        printf( "Volume = %d.\n", Counter );
    }
*/
    return 1;
}

/**Function*************************************************************

  Synopsis    [Prints the flows.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkMaxFlowPrintFlow( Abc_Ntk_t * pNtk, int fForward )
{
    Abc_Obj_t * pLatch, * pNext, * pPrev;
    int i;
    if ( fForward )
    {
        Vec_PtrForEachEntry( pNtk->vBoxes, pLatch, i )
        {
            assert( !Abc_ObjFanout0(pLatch)->fMarkA );
            if ( Abc_ObjGetPath(Abc_ObjFanout0(pLatch)) == NULL ) // no flow through this latch
                continue;
            printf( "Path = " );
            for ( pNext = Abc_ObjFanout0(pLatch); pNext != (void *)1; pNext = Abc_ObjGetPath(pNext) )
            {
                printf( "%s(%d) ", Abc_ObjName(pNext), pNext->Id );
                pPrev = pNext;
            }
            if ( !Abc_ObjIsPo(pPrev) )
            printf( "%s(%d) ", Abc_ObjName(Abc_ObjFanout0(pPrev)), Abc_ObjFanout0(pPrev)->Id );
            printf( "\n" );
        }
    }
    else
    {
        Vec_PtrForEachEntry( pNtk->vBoxes, pLatch, i )
        {
            assert( !Abc_ObjFanin0(pLatch)->fMarkA );
            if ( Abc_ObjGetPath(Abc_ObjFanin0(pLatch)) == NULL ) // no flow through this latch
                continue;
            printf( "Path = " );
            for ( pNext = Abc_ObjFanin0(pLatch); pNext != (void *)1; pNext = Abc_ObjGetPath(pNext) )
            {
                printf( "%s(%d) ", Abc_ObjName(pNext), pNext->Id );
                pPrev = pNext;
            }
            if ( !Abc_ObjIsPi(pPrev) )
            printf( "%s(%d) ", Abc_ObjName(Abc_ObjFanin0(pPrev)), Abc_ObjFanin0(pPrev)->Id );
            printf( "\n" );
        }
    }
}

/**Function*************************************************************

  Synopsis    [Prints the min-cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkMaxFlowPrintCut( Vec_Ptr_t * vMinCut )
{
    Abc_Obj_t * pObj;
    int i;
    printf( "Min-cut: " );
    Vec_PtrForEachEntry( vMinCut, pObj, i )
        printf( "%d ", pObj->Id );
    printf( "\n" );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


