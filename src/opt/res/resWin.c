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
#include "res.h"

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

  Synopsis    [Adds one node to the window.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Res_WinAddNode( Res_Win_t * p, Abc_Obj_t * pObj )
{
    assert( !pObj->fMarkA );
    pObj->fMarkA = 1;
    Vec_VecPush( p->vLevels, pObj->Level, pObj );
}

/**Function*************************************************************

  Synopsis    [Expands the frontier by one level.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Res_WinCollectTfiOne( Res_Win_t * p, int Level )
{
    Vec_Ptr_t * vFront;
    Abc_Obj_t * pObj, * pFanin;
    int i, k;
    assert( Level > 0 );
    vFront = Vec_VecEntry( p->vLevels, Level );
    Vec_PtrForEachEntry( vFront, pObj, i )
    {
        Abc_ObjForEachFanin( pObj, pFanin, k )
        {
            if ( !pFanin->fMarkA )
                Res_WinAddNode( p, pFanin );
        }
    }
}

/**Function*************************************************************

  Synopsis    [Collects nodes in the limited TFI of the node.]

  Description [Marks the collected nodes with the current trav ID.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Res_WinCollectTfi( Res_Win_t * p )
{
    int i;
    // expand storage for levels
    if ( Vec_VecSize( p->vLevels ) <= (int)p->pNode->Level + p->nWinTfoMax )
        Vec_VecExpand( p->vLevels, (int)p->pNode->Level + p->nWinTfoMax );
    // start the frontier
    Vec_VecClear( p->vLevels );
    Res_WinAddNode( p, p->pNode );
    // add one level at a time
    for ( i = p->pNode->Level; i > p->nLevLeaves; i-- )
        Res_WinCollectTfiOne( p, i );
}

/**Function*************************************************************

  Synopsis    [Marks the TFO of the collected nodes up to the given level.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Res_WinSweepTfo_rec( Abc_Obj_t * pObj, int nLevelLimit, Abc_Obj_t * pNode )
{
    Abc_Obj_t * pFanout;
    int i;
    if ( Abc_ObjIsCo(pObj) || (int)pObj->Level > nLevelLimit || pObj == pNode )
        return;
    if ( Abc_NodeIsTravIdCurrent(pObj) )
        return;
    Abc_NodeSetTravIdCurrent( pObj );
    Abc_ObjForEachFanout( pObj, pFanout, i )
        Res_WinSweepTfo_rec( pFanout, nLevelLimit, pNode );
}

/**Function*************************************************************

  Synopsis    [Marks the TFO of the collected nodes up to the given level.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Res_WinSweepTfo( Res_Win_t * p )
{
    Abc_Obj_t * pObj;
    int i, k;
    Abc_NtkIncrementTravId( p->pNode->pNtk );
    Vec_VecForEachEntryStartStop( p->vLevels, pObj, i, k, 0, p->nLevLeaves )
        Res_WinSweepTfo_rec( pObj, p->pNode->Level + p->nWinTfoMax, p->pNode );
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
    assert( Abc_NodeIsTravIdCurrent(pObj) );
    // check if the node has all fanouts marked
    Abc_ObjForEachFanout( pObj, pFanout, i )
        if ( !Abc_NodeIsTravIdCurrent(pObj) )
            break;
    // if some of the fanouts are unmarked, add the node to the root
    if ( i < Abc_ObjFanoutNum(pObj) ) 
    {
        Vec_PtrPush( vRoots, pObj );
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
    Vec_PtrClear( p->vRoots );
    Res_WinCollectRoots_rec( p->pNode, p->vRoots );
}

/**Function*************************************************************

  Synopsis    [Recursively augments the window.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Res_WinAddMissing_rec( Res_Win_t * p, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanin;
    int i;
    if ( !Abc_NodeIsTravIdCurrent(pObj) )
        return;
    if ( pObj->fMarkA )
        return;
    Res_WinAddNode( p, pObj );
    // visit the fanins of the node
    Abc_ObjForEachFanin( pObj, pFanin, i )
        Res_WinAddMissing_rec( p, pObj );
}

/**Function*************************************************************

  Synopsis    [Adds to the window visited nodes in the TFI of the roots.]

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

  Synopsis    [Collect all the nodes that fanin into the window nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Res_WinCollectLeaves( Res_Win_t * p )
{
    Abc_Obj_t * pObj, * pFanin;
    int i, k, f;
    // add the leaves
    Vec_PtrClear( p->vLeaves );
    // collect the nodes below the given level
    Vec_VecForEachEntryStartStop( p->vLevels, pObj, i, k, 0, p->nLevLeaves )
        Vec_PtrPush( p->vLeaves, pObj );
    // add to leaves the fanins of the nodes above the given level
    Vec_VecForEachEntryStart( p->vLevels, pObj, i, k, p->nLevLeaves + 1 )
    {
        Abc_ObjForEachFanin( pObj, pFanin, f )
        {
            if ( !pFanin->fMarkA )
            {
                pFanin->fMarkA = 1;
                Vec_PtrPush( p->vLeaves, pFanin );
            }
        }
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Res_WinVisitNodeTfo( Res_Win_t * p )
{
    // mark the TFO of the node
    Abc_NtkIncrementTravId( p->pNode->pNtk );
    Res_WinSweepTfo_rec( p->pNode, p->nLevDivMax, NULL );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Res_WinCollectDivisors( Res_Win_t * p )
{
    Abc_Obj_t * pObj, * pFanout, * pFanin;
    int i, k, f, m;
    // mark the TFO of the node
    Res_WinVisitNodeTfo( p );
    // go through all the legal levels and check if their fanouts can be divisors
    Vec_VecForEachEntryStartStop( p->vLevels, pObj, i, k, 0, p->nLevDivMax - 1 )
    {
        Abc_ObjForEachFanout( pObj, pFanout, f )
        {
            // skip COs
            if ( !Abc_ObjIsNode(pFanout) ) 
                continue;
            // skip nodes in the TFO of node
            if ( Abc_NodeIsTravIdCurrent(pFanout) )
                continue;
            // skip nodes that are already added
            if ( pFanout->fMarkA )
                continue;
            // skip nodes with large level
            if ( (int)pFanout->Level > p->nLevDivMax )
                continue;
            // skip nodes whose fanins are not in the cone
            Abc_ObjForEachFanin( pFanout, pFanin, m )
                if ( !pFanin->fMarkA )
                    break;
            if ( m < Abc_ObjFaninNum(pFanin) )
                continue;
            // add the node
            Res_WinAddNode( p, pFanout );
        }
    }
    // collect the divisors below the line
    Vec_PtrClear( p->vDivs );
    Vec_VecForEachEntryStartStop( p->vLevels, pObj, i, k, 0, p->nLevDivMax )
        Vec_PtrPush( p->vDivs, pObj );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Res_WinUnmark( Res_Win_t * p )
{
    Vec_Ptr_t * vLevel;
    Abc_Obj_t * pObj;
    int i, k;
    Vec_VecForEachEntry( p->vLevels, pObj, i, k )
        pObj->fMarkA = 0;
    Vec_PtrForEachEntry( p->vLeaves, pObj, i )
        pObj->fMarkA = 0;
    // remove leaves from the set
    Vec_VecForEachLevelStartStop( p->vLevels, vLevel, i, 0, p->nLevLeaves )
        Vec_PtrClear( vLevel );
}

/**Function*************************************************************

  Synopsis    [Computes the window.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Res_WinCompute( Abc_Obj_t * pNode, int nWinTfiMax, int nWinTfoMax, int nLevDivMax, Res_Win_t * p )
{
    assert( Abc_ObjIsNode(pNode) );
    assert( nWinTfiMax > 0 && nWinTfoMax > 0 );
    // initialize the window
    p->pNode = pNode;
    p->nWinTfiMax = nWinTfiMax;
    p->nWinTfoMax = nWinTfoMax;
    p->nLevDivMax = nLevDivMax;
    p->nLevLeaves = ABC_MAX( 0, p->pNode->Level - p->nWinTfiMax - 1 );
    // collect the nodes in TFI cone of pNode down to the given level (nWinTfiMax)
    Res_WinCollectTfi( p );
    // mark the TFO of the collected nodes up to the given level (nWinTfoMax)
    Res_WinSweepTfo( p );
    // find the roots of the window
    Res_WinCollectRoots( p );
    // add the nodes in the TFI of the roots that are not yet in the window
    Res_WinAddMissing( p );
    // find the leaves of the window
    Res_WinCollectLeaves( p );
    // collect the divisors up to the given maximum divisor level (nLevDivMax)
    if ( nLevDivMax >= 0 )
        Res_WinCollectDivisors( p );
    else
        Vec_PtrClear( p->vDivs );
    // unmark window nodes
    Res_WinUnmark( p );
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


