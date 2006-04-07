/**CFile****************************************************************

  FileName    [abcRr.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Redundancy removal.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcRr.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "fraig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Abc_RRMan_t_ Abc_RRMan_t;
struct Abc_RRMan_t_
{
    // the parameters
    Abc_Ntk_t *      pNtk;             // the network
    int              nFaninLevels;     // the number of fanin levels
    int              nFanoutLevels;    // the number of fanout levels
    // the node/fanin/fanout
    Abc_Obj_t *      pNode;            // the node
    Abc_Obj_t *      pFanin;           // the fanin
    Abc_Obj_t *      pFanout;          // the fanout
    // the intermediate cones
    Vec_Ptr_t *      vFaninLeaves;     // the leaves of the fanin cone
    Vec_Ptr_t *      vFanoutRoots;     // the roots of the fanout cone
    // the window
    Vec_Ptr_t *      vLeaves;          // the leaves of the window
    Vec_Ptr_t *      vCone;            // the internal nodes of the window
    Vec_Ptr_t *      vRoots;           // the roots of the window
    Abc_Ntk_t *      pWnd;             // the window derived for the edge
    // the miter 
    Abc_Ntk_t *      pMiter;           // the miter derived from the window
    Prove_Params_t * pParams;          // the miter proving parameters
};

static Abc_RRMan_t * Abc_RRManStart();
static void          Abc_RRManStop( Abc_RRMan_t * p );
static void          Abc_RRManClean( Abc_RRMan_t * p );
static int           Abc_NtkRRProve( Abc_RRMan_t * p );
static int           Abc_NtkRRUpdate( Abc_Ntk_t * pNtk, Abc_Obj_t * pNode, Abc_Obj_t * pFanin, Abc_Obj_t * pFanout );
static int           Abc_NtkRRWindow( Abc_RRMan_t * p );

static int           Abc_NtkRRTfi_int( Vec_Ptr_t * vFaninLeaves, int LevelLimit );
static int           Abc_NtkRRTfo_int( Vec_Ptr_t * vFanoutRoots, int LevelLimit, Abc_Obj_t * pEdgeFanin, Abc_Obj_t * pEdgeFanout );
static int           Abc_NtkRRTfo_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vRoots, int LevelLimit );
static void          Abc_NtkRRTfi_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vLeaves, Vec_Ptr_t * vCone );
static Abc_Ntk_t *   Abc_NtkWindow( Abc_Ntk_t * pNtk, Vec_Ptr_t * vLeaves, Vec_Ptr_t * vCone, Vec_Ptr_t * vRoots );


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Removes stuck-at redundancies.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRR( Abc_Ntk_t * pNtk, int nFaninLevels, int nFanoutLevels, int fUseFanouts, int fVerbose )
{
    ProgressBar * pProgress;
    Abc_RRMan_t * p;
    Abc_Obj_t * pNode, * pFanin, * pFanout;
    int i, k, m, nNodes;
    // start the manager
    p = Abc_RRManStart( nFaninLevels, nFanoutLevels );
    p->pNtk = pNtk;
    p->nFaninLevels  = nFaninLevels;
    p->nFanoutLevels = nFanoutLevels;
    // go through the nodes
    nNodes = Abc_NtkObjNumMax(pNtk);
    pProgress = Extra_ProgressBarStart( stdout, nNodes );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        // stop if all nodes have been tried once
        if ( i >= nNodes )
            break;
        // skip the constant node
        if ( Abc_NodeIsConst(pNode) )
            continue;
        // skip the nodes with many fanouts
        if ( Abc_ObjFanoutNum(pNode) > 1000 )
            continue;
        // construct the window
        if ( !fUseFanouts )
        {
            Abc_ObjForEachFanin( pNode, pFanin, k )
            {
                Abc_RRManClean( p );
                p->pNode   = pNode;
                p->pFanin  = pFanin;
                p->pFanout = NULL;
                if ( !Abc_NtkRRWindow( p ) )
                    continue;
                if ( !Abc_NtkRRProve( p ) )
                    continue;
                Abc_NtkRRUpdate( pNtk, p->pNode, p->pFanin, p->pFanout );
                break;
            }
            continue;
        }
        // use the fanouts
        Abc_ObjForEachFanout( pNode, pFanout, m )
        Abc_ObjForEachFanin( pNode, pFanin, k )
        {
            Abc_RRManClean( p );
            p->pNode   = pNode;
            p->pFanin  = pFanin;
            p->pFanout = pFanout;
            if ( !Abc_NtkRRWindow( p ) )
                continue;
            if ( !Abc_NtkRRProve( p ) )
                continue;
            Abc_NtkRRUpdate( pNtk, p->pNode, p->pFanin, p->pFanout );
            break;
        }
    }
    Extra_ProgressBarStop( pProgress );
    Abc_RRManStop( p );
    // put the nodes into the DFS order and reassign their IDs
    Abc_NtkReassignIds( pNtk );
    Abc_NtkGetLevelNum( pNtk );
    // check
    if ( !Abc_NtkCheck( pNtk ) )
    {
        printf( "Abc_NtkRR: The network check has failed.\n" );
        return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Start the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_RRMan_t * Abc_RRManStart()
{
    Abc_RRMan_t * p;
    p = ALLOC( Abc_RRMan_t, 1 );
    memset( p, 0, sizeof(Abc_RRMan_t) );
    p->vFaninLeaves  = Vec_PtrAlloc( 100 );  // the leaves of the fanin cone
    p->vFanoutRoots  = Vec_PtrAlloc( 100 );  // the roots of the fanout cone
    p->vLeaves       = Vec_PtrAlloc( 100 );  // the leaves of the window
    p->vCone         = Vec_PtrAlloc( 100 );  // the internal nodes of the window
    p->vRoots        = Vec_PtrAlloc( 100 );  // the roots of the window
    p->pParams       = ALLOC( Prove_Params_t, 1 );
    memset( p->pParams, 0, sizeof(Prove_Params_t) );
    Prove_ParamsSetDefault( p->pParams );
    return p;
}

/**Function*************************************************************

  Synopsis    [Stop the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_RRManStop( Abc_RRMan_t * p )
{
    Abc_RRManClean( p );
    Vec_PtrFree( p->vFaninLeaves  );  
    Vec_PtrFree( p->vFanoutRoots  );  
    Vec_PtrFree( p->vLeaves );  
    Vec_PtrFree( p->vCone );  
    Vec_PtrFree( p->vRoots );  
    free( p->pParams );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Clean the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_RRManClean( Abc_RRMan_t * p )
{
    p->pNode   = NULL; 
    p->pFanin  = NULL; 
    p->pFanout = NULL; 
    Vec_PtrClear( p->vFaninLeaves  );  
    Vec_PtrClear( p->vFanoutRoots  );  
    Vec_PtrClear( p->vLeaves );  
    Vec_PtrClear( p->vCone );  
    Vec_PtrClear( p->vRoots );  
    if ( p->pWnd )   Abc_NtkDelete( p->pWnd );
    if ( p->pMiter ) Abc_NtkDelete( p->pMiter );
    p->pWnd   = NULL;
    p->pMiter = NULL;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the miter is constant 0.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRRProve( Abc_RRMan_t * p )
{
    Abc_Ntk_t * pWndCopy;
    int RetValue;
    pWndCopy = Abc_NtkDup( p->pWnd );
    Abc_NtkRRUpdate( pWndCopy, p->pNode->pCopy, p->pFanin->pCopy, p->pFanout? p->pFanout->pCopy : NULL );
    p->pMiter = Abc_NtkMiter( p->pWnd, pWndCopy, 1 );
    RetValue  = Abc_NtkMiterProve( &p->pMiter, p->pParams );
    if ( RetValue == 1 )
        return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Updates the network after redundancy removal.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRRUpdate( Abc_Ntk_t * pNtk, Abc_Obj_t * pNode, Abc_Obj_t * pFanin, Abc_Obj_t * pFanout )
{
    Abc_Obj_t * pNodeNew, * pFanoutNew;
    assert( pFanout == NULL );
    assert( !Abc_ObjIsComplement(pNode) );
    assert( !Abc_ObjIsComplement(pFanin) );
    assert( !Abc_ObjIsComplement(pFanout) );
    // find the node after redundancy removal
    if ( pFanin == Abc_ObjFanin0(pNode) )
        pNodeNew = Abc_ObjChild1(pNode);
    else if ( pFanin == Abc_ObjFanin1(pNode) )
        pNodeNew = Abc_ObjChild0(pNode);
    else assert( 0 );
    // replace
    if ( pFanout == NULL )
    {
        Abc_AigReplace( pNtk->pManFunc, pNode, pNodeNew, 0 );
        return 1;
    }
    // find the fanout after redundancy removal
    if ( pNode == Abc_ObjFanin0(pFanout) )
        pFanoutNew = Abc_AigAnd( pNtk->pManFunc, Abc_ObjNotCond(pNodeNew,Abc_ObjFaninC0(pFanout)), Abc_ObjChild1(pFanout) );
    else if ( pNode == Abc_ObjFanin1(pFanout) )
        pFanoutNew = Abc_AigAnd( pNtk->pManFunc, Abc_ObjNotCond(pNodeNew,Abc_ObjFaninC1(pFanout)), Abc_ObjChild0(pFanout) );
    else assert( 0 );
    // replace
    Abc_AigReplace( pNtk->pManFunc, pFanout, pFanoutNew, 0 );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Constructs window for checking RR.]

  Description [If the window (p->pWnd) with the given scope (p->nFaninLevels, 
  p->nFanoutLevels) cannot be constructed, returns 0. Otherwise, returns 1.
  The levels are measured from the fanin node (pFanin) and the fanout node
  (pEdgeFanout), respectively.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRRWindow( Abc_RRMan_t * p )
{
    Abc_Obj_t * pObj, * pFanout, * pEdgeFanin, * pEdgeFanout;
    int i, k;

    // get the edge
    pEdgeFanout = p->pFanout? p->pFanout : p->pNode;
    pEdgeFanin  = p->pFanout? p->pNode : p->pFanin;

    // start the TFI leaves with the fanin
    Abc_NtkIncrementTravId( p->pNtk );
    Abc_NodeSetTravIdCurrent( p->pFanin );
    Vec_PtrPush( p->vFaninLeaves, p->pFanin );
    // mark the TFI cone and collect the leaves down to the given level
    while ( Abc_NtkRRTfi_int(p->vFaninLeaves, p->pFanin->Level - p->nFaninLevels) );

    // collect the TFO cone of the leaves
    Abc_NtkIncrementTravId( p->pNtk );
    Vec_PtrForEachEntry( p->vFaninLeaves, pObj, i )
    {
        Abc_ObjForEachFanout( pObj, pFanout, k )
        {
            if ( !Abc_ObjIsNode(pFanout) )
                continue;
            if ( pFanout->Level > pEdgeFanout->Level + p->nFanoutLevels )
                continue;
            if ( Abc_NodeIsTravIdCurrent(pFanout) )
                continue;
            Abc_NodeSetTravIdCurrent( pFanout );
            Vec_PtrPush( p->vFanoutRoots, pFanout );
        }
    }
    // mark the TFO cone and collect the leaves up to the given level (while skipping the edge)
    while ( Abc_NtkRRTfo_int(p->vFanoutRoots, pEdgeFanout->Level + p->nFanoutLevels, pEdgeFanin, pEdgeFanout) );
    // unmark the nodes
    Vec_PtrForEachEntry( p->vFanoutRoots, pObj, i )
        pObj->fMarkA = 0;

    // mark the current roots
    Abc_NtkIncrementTravId( p->pNtk );
    Vec_PtrForEachEntry( p->vFanoutRoots, pObj, i )
        Abc_NodeSetTravIdCurrent( pObj );
    // collect roots reachable from the fanout (p->vRoots)
    if ( !Abc_NtkRRTfo_rec( pEdgeFanout, p->vRoots, pEdgeFanout->Level + p->nFanoutLevels + 5 ) )
        return 0;

    // collect the DFS-ordered new cone (p->vCone) and new leaves (p->vLeaves)
    // using the previous marks coming from the TFO cone
    Vec_PtrForEachEntry( p->vRoots, pObj, i )
        Abc_NtkRRTfi_rec( pObj, p->vLeaves, p->vCone );
    // unmark the nodes
    Vec_PtrForEachEntry( p->vCone, pObj, i )
        pObj->fMarkA = 0;
    Vec_PtrForEachEntry( p->vLeaves, pObj, i )
        pObj->fMarkA = 0;

    // create a new network
    p->pWnd = Abc_NtkWindow( p->pNtk, p->vLeaves, p->vCone, p->vRoots );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Marks the nodes in the TFI and collects their leaves.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRRTfi_int( Vec_Ptr_t * vFaninLeaves, int LevelLimit )
{
    Abc_Obj_t * pObj, * pNext;
    int i, k, LevelMax, nSize;
    // find the maximum level of leaves
    LevelMax = 0;
    Vec_PtrForEachEntry( vFaninLeaves, pObj, i )
        if ( LevelMax < (int)pObj->Level )
            LevelMax = pObj->Level;
    // if the nodes are all PIs, LevelMax == 0
    if ( LevelMax == 0 || LevelMax <= LevelLimit )
        return 0;
    // expand the nodes with the minimum level
    nSize = Vec_PtrSize(vFaninLeaves);
    Vec_PtrForEachEntryStop( vFaninLeaves, pObj, i, nSize )
    {
        if ( LevelMax != (int)pObj->Level )
            continue;
        Abc_ObjForEachFanin( pObj, pNext, k )
        {
            if ( Abc_NodeIsTravIdCurrent(pNext) )
                continue;
            Abc_NodeSetTravIdCurrent( pNext );
            Vec_PtrPush( vFaninLeaves, pNext );
        }
    }
    // remove old nodes (cannot remove a PI)
    k = 0;
    Vec_PtrForEachEntry( vFaninLeaves, pObj, i )
    {
        if ( LevelMax == (int)pObj->Level )
            continue;
        Vec_PtrWriteEntry( vFaninLeaves, k++, pObj );
    }
    Vec_PtrShrink( vFaninLeaves, k );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Marks the nodes in the TFO and collects their roots.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRRTfo_int( Vec_Ptr_t * vFanoutRoots, int LevelLimit, Abc_Obj_t * pEdgeFanin, Abc_Obj_t * pEdgeFanout )
{
    Abc_Obj_t * pObj, * pNext;
    int i, k, LevelMin, nSize;
    // find the minimum level of roots
    LevelMin = ABC_INFINITY;
    Vec_PtrForEachEntry( vFanoutRoots, pObj, i )
        if ( Abc_ObjIsNode(pObj) && !pObj->fMarkA && LevelMin > (int)pObj->Level )
            LevelMin = pObj->Level;
    // if the nodes are all POs, LevelMin == ABC_INFINITY
    if ( LevelMin == ABC_INFINITY || LevelMin > LevelLimit )
        return 0;
    // expand the nodes with the minimum level
    nSize = Vec_PtrSize(vFanoutRoots);
    Vec_PtrForEachEntryStop( vFanoutRoots, pObj, i, nSize )
    {
        if ( LevelMin != (int)pObj->Level )
            continue;
        Abc_ObjForEachFanout( pObj, pNext, k )
        {
            if ( !Abc_ObjIsNode(pNext) || pNext->Level > (unsigned)LevelLimit )
            {
                pObj->fMarkA = 1;
                continue;
            }
            if ( pObj == pEdgeFanin && pNext == pEdgeFanout )
                continue;
            if ( Abc_NodeIsTravIdCurrent(pNext) )
                continue;
            Abc_NodeSetTravIdCurrent( pNext );
            Vec_PtrPush( vFanoutRoots, pNext );
        }
    }
    // remove old nodes
    k = 0;
    Vec_PtrForEachEntry( vFanoutRoots, pObj, i )
    {
        if ( LevelMin == (int)pObj->Level )
        {
            // check if the node has external fanouts
            Abc_ObjForEachFanout( pObj, pNext, k )
            {
                if ( pObj == pEdgeFanin && pNext == pEdgeFanout )
                    continue;
                if ( !Abc_NodeIsTravIdCurrent(pNext) )
                    break;
            }
            // if external fanout is found, do not remove the node
            if ( pNext )
                continue;
        }
        Vec_PtrWriteEntry( vFanoutRoots, k++, pObj );
    }
    Vec_PtrShrink( vFanoutRoots, k );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Collects the roots in the TFO of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRRTfo_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vRoots, int LevelLimit )
{
    Abc_Obj_t * pFanout;
    int i;
    if ( Abc_ObjIsCo(pNode) || pNode->Level > (unsigned)LevelLimit )
        return 0;
    if ( Abc_NodeIsTravIdCurrent(pNode) )
    {
        Vec_PtrPushUnique( vRoots, pNode );
        return 1;
    }
    Abc_NodeSetTravIdCurrent( pNode );
    Abc_ObjForEachFanout( pNode, pFanout, i )
        if ( !Abc_NtkRRTfo_rec( pFanout, vRoots, LevelLimit ) )
            return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRRTfi_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vLeaves, Vec_Ptr_t * vCone )
{
    Abc_Obj_t * pFanin;
    int i;
    // skip visited nodes
    if ( pNode->fMarkA )
        return;
    pNode->fMarkA = 1;
    // add the node if it was not visited in the previus run
    if ( !Abc_NodeIsTravIdPrevious(pNode) )
    {
        Vec_PtrPush( vLeaves, pNode );
        return;
    }
    Abc_ObjForEachFanin( pNode, pFanin, i )
        Abc_NtkRRTfi_rec( pFanin, vLeaves, vCone );
    Vec_PtrPush( vCone, pNode );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkWindow( Abc_Ntk_t * pNtk, Vec_Ptr_t * vLeaves, Vec_Ptr_t * vCone, Vec_Ptr_t * vRoots )
{
    Abc_Ntk_t * pNtkNew; 
    Abc_Obj_t * pObj;
    int i;
    assert( Abc_NtkIsStrash(pNtk) );
    // start the network
    pNtkNew = Abc_NtkAlloc( pNtk->ntkType, pNtk->ntkFunc );
    // duplicate the name and the spec
    pNtkNew->pName = Extra_UtilStrsav( "temp" );
    // map the constant nodes
    if ( Abc_NtkConst1(pNtk) )
        Abc_NtkConst1(pNtk)->pCopy = Abc_NtkConst1(pNtkNew);
    // create and map the PIs
    Vec_PtrForEachEntry( vLeaves, pObj, i )
        pObj->pCopy = Abc_NtkCreatePi(pNtkNew);
    // copy the AND gates
    Vec_PtrForEachEntry( vCone, pObj, i )
        pObj->pCopy = Abc_AigAnd( pNtkNew->pManFunc, Abc_ObjChild0Copy(pObj), Abc_ObjChild1Copy(pObj) );
    // compare the number of nodes before and after
    if ( Vec_PtrSize(vCone) != Abc_NtkNodeNum(pNtkNew) )
        printf( "Warning: Structural hashing during windowing reduced %d nodes (this is a bug).\n",
            Vec_PtrSize(vCone) - Abc_NtkNodeNum(pNtkNew) );
    // create the POs
    Vec_PtrForEachEntry( vRoots, pObj, i )
        Abc_ObjAddFanin( Abc_NtkCreatePo(pNtkNew), pObj->pCopy );
    // add the PI/PO names
    Abc_NtkAddDummyPiNames( pNtkNew );
    Abc_NtkAddDummyPoNames( pNtkNew );
    // check
    if ( !Abc_NtkCheck( pNtkNew ) )
    {
        printf( "Abc_NtkWindow: The network check has failed.\n" );
        return NULL;
    }
    return pNtkNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


