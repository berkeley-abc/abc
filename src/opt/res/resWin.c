/**CFile****************************************************************

  FileName    [resWin.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Resynthesis package.]

  Synopsis    [Windowing algorithm.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - January 15, 2007.]

  Revision    [$Id: resWin.c,v 1.00 2007/01/15 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "resInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Allocates the window.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Res_Win_t * Res_WinAlloc()
{
    Res_Win_t * p;
    p = ALLOC( Res_Win_t, 1 );
    memset( p, 0, sizeof(Res_Win_t) );
    p->vLevels = Vec_VecStart( 128 );
    p->vLeaves = Vec_PtrAlloc( 512 );
    p->vRoots  = Vec_PtrAlloc( 512 );
    p->vDivs   = Vec_PtrAlloc( 512 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Frees the window.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Res_WinFree( Res_Win_t * p )
{
    Vec_VecFree( p->vLevels );
    Vec_PtrFree( p->vLeaves );
    Vec_PtrFree( p->vRoots  );
    Vec_PtrFree( p->vDivs   );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Collects nodes in the limited TFI of the node.]

  Description [Marks the collected nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Res_WinCollectNodeTfi( Res_Win_t * p )
{
    Vec_Ptr_t * vFront;
    Abc_Obj_t * pObj, * pFanin;
    int i, k, m;
    // expand storage for levels
    if ( Vec_VecSize( p->vLevels ) <= (int)p->pNode->Level + p->nWinTfoMax )
        Vec_VecExpand( p->vLevels, (int)p->pNode->Level + p->nWinTfoMax );
    // start the frontier
    Vec_VecClear( p->vLevels );
    Res_WinAddNode( p, p->pNode );
    // add one level at a time
    Vec_VecForEachLevelReverseStartStop( p->vLevels, vFront, i, p->pNode->Level, p->nLevLeaves + 1 )
    {
        Vec_PtrForEachEntry( vFront, pObj, k )
            Abc_ObjForEachFanin( pObj, pFanin, m )
                if ( !pFanin->fMarkA )
                    Res_WinAddNode( p, pFanin );
    }
}

/**Function*************************************************************

  Synopsis    [Collect all the nodes that fanin into the window nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Res_WinCollectLeaves( Res_Win_t * p )
{
    Vec_Ptr_t * vLevel;
    Abc_Obj_t * pObj;
    int i, k;
    // add the leaves
    Vec_PtrClear( p->vLeaves );
    // collect the nodes below the given level
    Vec_VecForEachEntryStartStop( p->vLevels, pObj, i, k, 0, p->nLevLeaves )
        Vec_PtrPush( p->vLeaves, pObj );
    // remove leaves from the set
    Vec_VecForEachLevelStartStop( p->vLevels, vLevel, i, 0, p->nLevLeaves )
        Vec_PtrClear( vLevel );
}

/**Function*************************************************************

  Synopsis    [Marks the TFO of the collected nodes up to the given level.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Res_WinSweepLeafTfo_rec( Abc_Obj_t * pObj, int nLevelLimit, Abc_Obj_t * pNode )
{
    Abc_Obj_t * pFanout;
    int i;
    if ( Abc_ObjIsCo(pObj) || (int)pObj->Level > nLevelLimit || pObj == pNode )
        return;
    if ( Abc_NodeIsTravIdCurrent(pObj) )
        return;
    Abc_NodeSetTravIdCurrent( pObj );
    Abc_ObjForEachFanout( pObj, pFanout, i )
        Res_WinSweepLeafTfo_rec( pFanout, nLevelLimit, pNode );
}

/**Function*************************************************************

  Synopsis    [Marks the TFO of the collected nodes up to the given level.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Res_WinSweepLeafTfo( Res_Win_t * p )
{
    Abc_Obj_t * pObj;
    int i;
    Abc_NtkIncrementTravId( p->pNode->pNtk );
    Vec_PtrForEachEntry( p->vLeaves, pObj, i )
        Res_WinSweepLeafTfo_rec( pObj, p->pNode->Level + p->nWinTfoMax, p->pNode );
}

/**Function*************************************************************

  Synopsis    [Recursively collects the roots.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Res_WinCollectRoots_rec( Abc_Obj_t * pObj, Vec_Ptr_t * vRoots )
{
    Abc_Obj_t * pFanout;
    int i;
    assert( Abc_ObjIsNode(pObj) );
    // check if the node has all fanouts marked
    Abc_ObjForEachFanout( pObj, pFanout, i )
        if ( !Abc_NodeIsTravIdCurrent(pFanout) )
            break;
    // if some of the fanouts are unmarked, add the node to the root
    if ( i < Abc_ObjFanoutNum(pObj) ) 
    {
        Vec_PtrPushUnique( vRoots, pObj );
        return;
    }
    // otherwise, call recursively
    Abc_ObjForEachFanout( pObj, pFanout, i )
        Res_WinCollectRoots_rec( pFanout, vRoots );
}

/**Function*************************************************************

  Synopsis    [Collects the roots of the window.]

  Description [Roots of the window are the nodes that have at least
  one fanout that it not in the TFO of the leaves.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Res_WinCollectRoots( Res_Win_t * p )
{
    assert( !Abc_NodeIsTravIdCurrent(p->pNode) );
    Vec_PtrClear( p->vRoots );
    Res_WinCollectRoots_rec( p->pNode, p->vRoots );
}

/**Function*************************************************************

  Synopsis    [Recursively adds missing nodes and leaves.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Res_WinAddMissing_rec( Res_Win_t * p, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanin;
    int i;
    if ( pObj->fMarkA )
        return;
    if ( !Abc_NodeIsTravIdCurrent(pObj) || (int)pObj->Level <= p->nLevLeaves )
    {
        Vec_PtrPush( p->vLeaves, pObj );
        pObj->fMarkA = 1;
        return;
    }
    Res_WinAddNode( p, pObj );
    // visit the fanins of the node
    Abc_ObjForEachFanin( pObj, pFanin, i )
        Res_WinAddMissing_rec( p, pFanin );
}

/**Function*************************************************************

  Synopsis    [Adds to the window nodes and leaves in the TFI of the roots.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Res_WinAddMissing( Res_Win_t * p )
{
    Abc_Obj_t * pObj;
    int i;
    Vec_PtrForEachEntry( p->vRoots, pObj, i )
        Res_WinAddMissing_rec( p, pObj );
}

/**Function*************************************************************

  Synopsis    [Unmarks the leaves and nodes of the window.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Res_WinUnmark( Res_Win_t * p )
{
    Abc_Obj_t * pObj;
    int i, k;
    Vec_VecForEachEntry( p->vLevels, pObj, i, k )
        pObj->fMarkA = 0;
    Vec_PtrForEachEntry( p->vLeaves, pObj, i )
        pObj->fMarkA = 0;
}

/**Function*************************************************************

  Synopsis    [Verifies the window.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Res_WinVerify( Res_Win_t * p )
{
    Abc_Obj_t * pObj, * pFanin;
    int i, k, f;
    // make sure the nodes are not marked
    Abc_NtkForEachObj( p->pNode->pNtk, pObj, i )
        assert( !pObj->fMarkA );
    // mark the leaves
    Vec_PtrForEachEntry( p->vLeaves, pObj, i )
        pObj->fMarkA = 1;
    // make sure all nodes in the topological order have their fanins in the set
    Vec_VecForEachEntryStartStop( p->vLevels, pObj, i, k, p->nLevLeaves + 1, (int)p->pNode->Level + p->nWinTfoMax )
    {
        assert( (int)pObj->Level == i );
        assert( !pObj->fMarkA );
        Abc_ObjForEachFanin( pObj, pFanin, f )
            assert( pFanin->fMarkA );
        pObj->fMarkA = 1;
    }
    // make sure the roots are marked
    Vec_PtrForEachEntry( p->vRoots, pObj, i )
        assert( pObj->fMarkA );
    // unmark 
    Res_WinUnmark( p );
}

/**Function*************************************************************

  Synopsis    [Computes the window.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Res_WinCompute( Abc_Obj_t * pNode, int nWinTfiMax, int nWinTfoMax, Res_Win_t * p )
{
    assert( Abc_ObjIsNode(pNode) );
    assert( nWinTfiMax > 0 && nWinTfoMax > 0 );
    // initialize the window
    p->pNode = pNode;
    p->nWinTfiMax = nWinTfiMax;
    p->nWinTfoMax = nWinTfoMax;
    p->nLevLeaves = ABC_MAX( 0, ((int)p->pNode->Level) - p->nWinTfiMax - 1 );
    // collect the nodes in TFI cone of pNode above the level of leaves (p->nLevLeaves)
    Res_WinCollectNodeTfi( p );
    // find the leaves of the window
    Res_WinCollectLeaves( p );
    // mark the TFO of the collected nodes up to the given level (p->pNode->Level + p->nWinTfoMax)
    Res_WinSweepLeafTfo( p );
    // find the roots of the window
    Res_WinCollectRoots( p );
    // add the nodes in the TFI of the roots that are not yet in the window
    Res_WinAddMissing( p );
    // unmark window nodes
    Res_WinUnmark( p );
    // clear the divisor information
    p->nLevDivMax = 0;
    p->nDivsPlus = 0;
    Vec_PtrClear( p->vDivs );
    // verify the resulting window
//    Res_WinVerify( p );
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


