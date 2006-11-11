/**CFile****************************************************************

  FileName    [retDelay.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Retiming package.]

  Synopsis    [Incremental retiming for optimum delay.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - Oct 31, 2006.]

  Revision    [$Id: retDelay.c,v 1.00 2006/10/31 00:00:00 alanmi Exp $]

***********************************************************************/

#include "retInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int Abc_NtkRetimeMinDelayTry( Abc_Ntk_t * pNtk, int fForward, int fInitial, int nIterLimit, int * pIterBest, int fVerbose );
static int Abc_NtkRetimeTiming( Abc_Ntk_t * pNtk, int fForward, Vec_Ptr_t * vCritical );
static int Abc_NtkRetimeTiming_rec( Abc_Obj_t * pObj, int fForward );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Retimes incrementally for minimum delay.]

  Description [This procedure cannot be called in the application code
  because it assumes that the network is preprocessed by removing LIs/LOs.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRetimeMinDelay( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkCopy, int nIterLimit, int fForward, int fVerbose )
{
    int IterBest, DelayBest;
    int IterBest2, DelayBest2;
    // try to find the best delay iteration on a copy
    DelayBest = Abc_NtkRetimeMinDelayTry( pNtkCopy, fForward, 0, nIterLimit, &IterBest, fVerbose );
    if ( IterBest == 0 )
        return 1;
    // perform the given number of iterations on the original network
    DelayBest2 = Abc_NtkRetimeMinDelayTry( pNtk, fForward, 1, IterBest, &IterBest2, fVerbose );
    assert( DelayBest == DelayBest2 );
    assert( IterBest == IterBest2 );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Returns the best delay and the number of best iteration.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRetimeMinDelayTry( Abc_Ntk_t * pNtk, int fForward, int fInitial, int nIterLimit, int * pIterBest, int fVerbose )
{
    Abc_Ntk_t * pNtkNew = NULL;
    Vec_Ptr_t * vCritical;
    Vec_Int_t * vValues;
    Abc_Obj_t * pObj;
    int i, k, IterBest, DelayCur, DelayBest, DelayStart;
    // transfer intitial values
    if ( fInitial )
    {
        if ( fForward )
            Abc_NtkRetimeTranferToCopy( pNtk );
        else
        {
            // save initial value of the latches
            vValues = Abc_NtkRetimeCollectLatchValues( pNtk );
            // start the network for initial value computation
            pNtkNew = Abc_NtkRetimeBackwardInitialStart( pNtk );
        }
    }
    // find the best iteration
    DelayBest = ABC_INFINITY; IterBest = 0;
    vCritical = Vec_PtrAlloc( 100 );
    for ( i = 0; ; i++ )
    {
        // perform moves for the timing-critical nodes
        DelayCur = Abc_NtkRetimeTiming( pNtk, fForward, vCritical );
        if ( i == 0 )
            DelayStart = DelayCur;
        // record this position if it has the best delay
        if ( DelayBest > DelayCur )
        {
            DelayBest = DelayCur;
            IterBest = i;
        }
        // quit after timing analysis
        if ( i == nIterLimit )
            break;
        // try retiming to improve the delay
        Vec_PtrForEachEntry( vCritical, pObj, k )
            if ( Abc_NtkRetimeNodeIsEnabled(pObj, fForward) )
                Abc_NtkRetimeNode( pObj, fForward, fInitial );
    }
    Vec_PtrFree( vCritical );
    // transfer the initial state back to the latches
    if ( fInitial )
    {
        if ( fForward )
            Abc_NtkRetimeTranferFromCopy( pNtk );
        else
        {
            Abc_NtkRetimeBackwardInitialFinish( pNtk, pNtkNew, vValues, fVerbose );
            Abc_NtkDelete( pNtkNew );
            Vec_IntFree( vValues );
        }
    }
    if ( !fInitial && fVerbose )
        printf( "%s : Starting delay = %3d.  Final delay = %3d.  IterBest = %2d (out of %2d).\n", 
            fForward? "Forward " : "Backward", DelayStart, DelayBest, IterBest, nIterLimit );
    *pIterBest = IterBest;
    return DelayBest;
}

/**Function*************************************************************

  Synopsis    [Returns the set of timing-critical nodes.]

  Description [Performs static timing analysis on the network. Uses 
  unit-delay model.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRetimeTiming( Abc_Ntk_t * pNtk, int fForward, Vec_Ptr_t * vCritical )
{
    Vec_Ptr_t * vLatches;
    Abc_Obj_t * pObj, * pNext;
    int i, k, LevelCur, LevelMax = 0;
    // mark all objects except nodes
    Abc_NtkIncrementTravId(pNtk);
    vLatches = Vec_PtrAlloc( Abc_NtkLatchNum(pNtk) );
    Abc_NtkForEachObj( pNtk, pObj, i )
    {
        if ( Abc_ObjIsLatch(pObj) )
            Vec_PtrPush( vLatches, pObj );
        if ( Abc_ObjIsNode(pObj) )
            continue;
        pObj->Level = 0;
        Abc_NodeSetTravIdCurrent( pObj );
    }
    // perform analysis from CIs/COs
    if ( fForward )
    {
        Vec_PtrForEachEntry( vLatches, pObj, i )
        {
            Abc_ObjForEachFanout( pObj, pNext, k )
            {
                LevelCur = Abc_NtkRetimeTiming_rec( pNext, fForward );
                if ( LevelMax < LevelCur )
                    LevelMax = LevelCur;
            }
        }
        Abc_NtkForEachPi( pNtk, pObj, i )
        {
            Abc_ObjForEachFanout( pObj, pNext, k )
            {
                LevelCur = Abc_NtkRetimeTiming_rec( pNext, fForward );
                if ( LevelMax < LevelCur )
                    LevelMax = LevelCur;
            }
        }
    }
    else
    {
        Vec_PtrForEachEntry( vLatches, pObj, i )
        {
            LevelCur = Abc_NtkRetimeTiming_rec( Abc_ObjFanin0(pObj), fForward );
            if ( LevelMax < LevelCur )
                LevelMax = LevelCur;
        }
        Abc_NtkForEachPo( pNtk, pObj, i )
        {
            LevelCur = Abc_NtkRetimeTiming_rec( Abc_ObjFanin0(pObj), fForward );
            if ( LevelMax < LevelCur )
                LevelMax = LevelCur;
        }
    }
    // collect timing critical nodes, which should be retimed forward/backward
    Vec_PtrClear( vCritical );
    Abc_NtkIncrementTravId(pNtk);
    if ( fForward )
    {
        Vec_PtrForEachEntry( vLatches, pObj, i )
        {
            Abc_ObjForEachFanout( pObj, pNext, k )
            {
                if ( Abc_NodeIsTravIdCurrent(pNext) )
                    continue;
                if ( LevelMax != (int)pNext->Level )
                    continue;
                // new critical node
                Vec_PtrPush( vCritical, pNext );
                Abc_NodeSetTravIdCurrent( pNext );
            }
        }
    }
    else
    {
        Vec_PtrForEachEntry( vLatches, pObj, i )
        {
            Abc_ObjForEachFanin( pObj, pNext, k )
            {
                if ( Abc_NodeIsTravIdCurrent(pNext) )
                    continue;
                if ( LevelMax != (int)pNext->Level )
                    continue;
                // new critical node
                Vec_PtrPush( vCritical, pNext );
                Abc_NodeSetTravIdCurrent( pNext );
            }
        }
    }
    Vec_PtrFree( vLatches );
    return LevelMax;
}

/**Function*************************************************************

  Synopsis    [Recursively performs timing analysis.]

  Description [Performs static timing analysis on the network. Uses 
  unit-delay model.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRetimeTiming_rec( Abc_Obj_t * pObj, int fForward )
{
    Abc_Obj_t * pNext;
    int i, LevelCur, LevelMax = 0;
    // skip visited nodes
    if ( Abc_NodeIsTravIdCurrent(pObj) )
        return pObj->Level;
    Abc_NodeSetTravIdCurrent(pObj);
    // visit the next nodes
    if ( fForward )
    {
        Abc_ObjForEachFanout( pObj, pNext, i )
        {
            LevelCur = Abc_NtkRetimeTiming_rec( pNext, fForward );
            if ( LevelMax < LevelCur )
                LevelMax = LevelCur;
        }
    }
    else
    {
        Abc_ObjForEachFanin( pObj, pNext, i )
        {
            LevelCur = Abc_NtkRetimeTiming_rec( pNext, fForward );
            if ( LevelMax < LevelCur )
                LevelMax = LevelCur;
        }
    }
//    printf( "Node %3d -> Level %3d.\n", pObj->Id, LevelMax + 1 );
    pObj->Level = LevelMax + 1;
    return pObj->Level;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


