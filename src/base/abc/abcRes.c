/**CFile****************************************************************

  FileName    [abcRes.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Technology-independent resynthesis of the AIG.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcRes.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "ft.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
 
static void        Abc_NodeResyn( Abc_ManRes_t * p );

static void        Abc_NodeFindCut( Abc_ManRes_t * p );
static int         Abc_NodeFindCut_int( Vec_Ptr_t * vInside, Vec_Ptr_t * vFanins, int nSizeLimit );
static int         Abc_NodeGetFaninCost( Abc_Obj_t * pNode );
static void        Abc_NodeConeMarkCollect_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vVisited );
static void        Abc_NodeConeMark( Vec_Ptr_t * vVisited );
static void        Abc_NodeConeUnmark( Vec_Ptr_t * vVisited );

static Vec_Int_t * Abc_NodeRefactor( Abc_ManRes_t * p );
static DdNode *    Abc_NodeConeBdd( DdManager * dd, DdNode ** pbVars, Abc_Obj_t * pNode, Vec_Ptr_t * vFanins, Vec_Ptr_t * vVisited );

static int         Abc_NodeDecide( Abc_ManRes_t * p );
static void        Abc_NodeUpdate( Abc_ManRes_t * p );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs incremental resynthesis of the AIG.]

  Description [Starting from each node, computes a reconvergence-driven cut, 
  derives BDD of the cut function, constructs ISOP, factors the cover, 
  and replaces the current implementation of the MFFC of the cut by the 
  new factored form if the number of AIG nodes is reduced. Returns the
  number of AIG nodes saved.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkAigResynthesize( Abc_Ntk_t * pNtk, Abc_ManRes_t * p )
{
    int fCheck = 1;
    ProgressBar * pProgress;
    Abc_Obj_t * pNode;
    int i, Counter, Approx;

    assert( Abc_NtkIsAig(pNtk) );

    // start the BDD manager
    p->dd = Cudd_Init( p->nNodeSizeMax + p->nConeSizeMax, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );
    Cudd_zddVarsFromBddVars( p->dd, 2 );
    p->bCubeX = Extra_bddComputeRangeCube( p->dd, p->nNodeSizeMax, p->dd->size );   Cudd_Ref( p->bCubeX );

    // remember the number of nodes
    Counter = Abc_NtkNodeNum( pNtk );
    // resynthesize each node
    pProgress = Extra_ProgressBarStart( stdout, 100 );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        Approx = (int)(100.0 * i / Abc_NtkObjNumMax(pNtk) );
        Extra_ProgressBarUpdate( pProgress, Approx, NULL );
        p->pNode = pNode;
        Abc_NodeResyn( p );
    }
    Extra_ProgressBarStop( pProgress );
    Abc_NtkManResStop( p );

    // check
    if ( fCheck && !Abc_NtkCheck( pNtk ) )
    {
        printf( "Abc_NtkAigResynthesize: The network check has failed.\n" );
        return -1;
    }
    return Abc_NtkNodeNum(pNtk) - Counter;
}

/**Function*************************************************************

  Synopsis    [Performs resynthesis of one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeResyn( Abc_ManRes_t * p )
{
    int RetValue;
    int clk;

    assert( Abc_ObjIsNode(p->pNode) );

clk = clock();
    // detect the cut
    Abc_NodeFindCut( p );
p->time1 += clock() - clk;

    // refactor the cut
clk = clock();
    p->vForm = Abc_NodeRefactor( p );
p->time2 += clock() - clk;

    // accept or reject the factored form
clk = clock();
    RetValue = Abc_NodeDecide( p );
p->time3 += clock() - clk;

    // modify the network
clk = clock();
    if ( RetValue )
        Abc_NodeUpdate( p );
p->time4 += clock() - clk;

    // cleanup
    Vec_IntFree( p->vForm );
    p->vForm = NULL;
}

/**Function*************************************************************

  Synopsis    [Finds a reconvergence-driven cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeFindCut( Abc_ManRes_t * p )
{
    Abc_Obj_t * pNode = p->pNode;
    int i;

    // mark TFI using fMarkA
    Vec_PtrClear( p->vVisited );
    Abc_NodeConeMarkCollect_rec( pNode, p->vVisited );

    // start the reconvergence-driven node
    Vec_PtrClear( p->vInsideNode );
    Vec_PtrClear( p->vFaninsNode );
    Vec_PtrPush( p->vFaninsNode, pNode );
    pNode->fMarkB = 1;

    // compute reconvergence-driven node
    while ( Abc_NodeFindCut_int( p->vInsideNode, p->vFaninsNode, p->nNodeSizeMax ) );

    // compute reconvergence-driven cone
    Vec_PtrClear( p->vInsideCone );
    Vec_PtrClear( p->vFaninsCone );
    if ( p->nConeSizeMax > p->nNodeSizeMax )
    {
        // copy the node into the cone
        Vec_PtrForEachEntry( p->vInsideNode, pNode, i )
            Vec_PtrPush( p->vInsideCone, pNode );
        Vec_PtrForEachEntry( p->vFaninsNode, pNode, i )
            Vec_PtrPush( p->vFaninsCone, pNode );
        // compute reconvergence-driven cone
        while ( Abc_NodeFindCut_int( p->vInsideCone, p->vFaninsCone, p->nConeSizeMax ) );
        // unmark the nodes of the sets
        Vec_PtrForEachEntry( p->vInsideCone, pNode, i )
            pNode->fMarkB = 0;
        Vec_PtrForEachEntry( p->vFaninsCone, pNode, i )
            pNode->fMarkB = 0;
    }
    else
    {
        // unmark the nodes of the sets
        Vec_PtrForEachEntry( p->vInsideNode, pNode, i )
            pNode->fMarkB = 0;
        Vec_PtrForEachEntry( p->vFaninsNode, pNode, i )
            pNode->fMarkB = 0;
    }

    // unmark TFI using fMarkA
    Abc_NodeConeUnmark( p->vVisited );
}

/**Function*************************************************************

  Synopsis    [Finds a reconvergence-driven cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeFindCut_int( Vec_Ptr_t * vInside, Vec_Ptr_t * vFanins, int nSizeLimit )
{
    Abc_Obj_t * pNode, * pFaninBest, * pNext;
    int CostBest, CostCur, i;
    // find the best fanin
    CostBest   = 100;
    pFaninBest = NULL;
    Vec_PtrForEachEntry( vFanins, pNode, i )
    {
        CostCur = Abc_NodeGetFaninCost( pNode );
        if ( CostBest > CostCur )
        {
            CostBest   = CostCur;
            pFaninBest = pNode;
        }
    }
    if ( pFaninBest == NULL )
        return 0;
    assert( CostBest < 3 );
    if ( vFanins->nSize - 1 + CostBest > nSizeLimit )
        return 0;
    assert( Abc_ObjIsNode(pFaninBest) );
    // remove the node from the array
    Vec_PtrRemove( vFanins, pFaninBest );
    // add the node to the set
    Vec_PtrPush( vInside, pFaninBest );
    // add the left child to the fanins
    pNext = Abc_ObjFanin0(pFaninBest);
    if ( !pNext->fMarkB )
    {
        pNext->fMarkB = 1;
        Vec_PtrPush( vFanins, pNext );
    }
    // add the right child to the fanins
    pNext = Abc_ObjFanin1(pFaninBest);
    if ( !pNext->fMarkB )
    {
        pNext->fMarkB = 1;
        Vec_PtrPush( vFanins, pNext );
    }
    assert( vFanins->nSize <= nSizeLimit );
    // keep doing this
    return 1;
}

/**Function*************************************************************

  Synopsis    [Evaluate the fanin cost.]

  Description [Returns the number of fanins that will be brought in.
  Returns large number if the node cannot be added.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeGetFaninCost( Abc_Obj_t * pNode )
{
    Abc_Obj_t * pFanout;
    int i;
    assert( pNode->fMarkA == 1 );  // this node is in the TFI
    assert( pNode->fMarkB == 1 );  // this node is in the constructed cone
    // check the PI node
    if ( !Abc_ObjIsNode(pNode) )
        return 999;
    // check the fanouts
    Abc_ObjForEachFanout( pNode, pFanout, i )
        if ( pFanout->fMarkA && pFanout->fMarkB == 0 ) // in the cone but not in the set
            return 999;
    // the fanouts are in the TFI and inside the constructed cone
    // return the number of fanins that will be on the boundary if this node is added
    return (!Abc_ObjFanin0(pNode)->fMarkB) + (!Abc_ObjFanin1(pNode)->fMarkB);
}

/**Function*************************************************************

  Synopsis    [Marks the TFI cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeConeMarkCollect_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vVisited )
{
    if ( pNode->fMarkA == 1 )
        return;
    // visit transitive fanin 
    if ( Abc_ObjIsNode(pNode) )
    {
        Abc_NodeConeMarkCollect_rec( Abc_ObjFanin0(pNode), vVisited );
        Abc_NodeConeMarkCollect_rec( Abc_ObjFanin1(pNode), vVisited );
    }
    assert( pNode->fMarkA == 0 );
    pNode->fMarkA = 1;
    Vec_PtrPush( vVisited, pNode );
}

/**Function*************************************************************

  Synopsis    [Unmarks the TFI cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeConeMark( Vec_Ptr_t * vVisited )
{
    int i;
    for ( i = 0; i < vVisited->nSize; i++ )
        ((Abc_Obj_t *)vVisited->pArray)->fMarkA = 1;
}

/**Function*************************************************************

  Synopsis    [Unmarks the TFI cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeConeUnmark( Vec_Ptr_t * vVisited )
{
    int i;
    for ( i = 0; i < vVisited->nSize; i++ )
        ((Abc_Obj_t *)vVisited->pArray)->fMarkA = 0;
}


/**Function*************************************************************

  Synopsis    [Derives the factored form of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_NodeRefactor( Abc_ManRes_t * p )
{
    Vec_Int_t * vForm;
    DdManager * dd = p->dd;
    DdNode * bFuncNode, * bFuncCone, * bCare, * bFuncOn, * bFuncOnDc;
    char * pSop;
    int nFanins;

    assert( p->vFaninsNode->nSize < p->nNodeSizeMax );
    assert( p->vFaninsCone->nSize < p->nConeSizeMax );

    // get the function of the node
    bFuncNode = Abc_NodeConeBdd( dd, p->dd->vars, p->pNode, p->vFaninsNode, p->vVisited );  
    Cudd_Ref( bFuncNode );
    nFanins = p->vFaninsNode->nSize;
    if ( p->nConeSizeMax > p->nNodeSizeMax )
    {
        // get the function of the cone
        bFuncCone = Abc_NodeConeBdd( dd, p->dd->vars + p->nNodeSizeMax, p->pNode, p->vFaninsCone, p->vVisited );  
        Cudd_Ref( bFuncCone );
        // get the care set
        bCare = Cudd_bddXorExistAbstract( p->dd, Cudd_Not(bFuncNode), bFuncCone, p->bCubeX );   Cudd_Ref( bCare );
        Cudd_RecursiveDeref( dd, bFuncCone );
        // compute the on-set and off-set of the function of the node
        bFuncOn   = Cudd_bddAnd( dd, bFuncNode, bCare );                Cudd_Ref( bFuncOn );
        bFuncOnDc = Cudd_bddAnd( dd, Cudd_Not(bFuncNode), bCare );      Cudd_Ref( bFuncOnDc );
        bFuncOnDc = Cudd_Not( bFuncOnDc );
        Cudd_RecursiveDeref( dd, bCare );
        // get the cover
        pSop = Abc_ConvertBddToSop( NULL, dd, bFuncOn, bFuncOnDc, nFanins, p->vCube, -1 );
        Cudd_RecursiveDeref( dd, bFuncOn );
        Cudd_RecursiveDeref( dd, bFuncOnDc );
    }
    else
    {
        // get the cover
        pSop = Abc_ConvertBddToSop( NULL, dd, bFuncNode, bFuncNode, nFanins, p->vCube, -1 );
    }
    Cudd_RecursiveDeref( dd, bFuncNode );
    // derive the factored form
    vForm = Ft_Factor( pSop );
    free( pSop );
    return vForm;
}

/**Function*************************************************************

  Synopsis    [Returns BDD representing the logic function of the cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdNode * Abc_NodeConeBdd( DdManager * dd, DdNode ** pbVars, Abc_Obj_t * pNode, Vec_Ptr_t * vFanins, Vec_Ptr_t * vVisited )
{
    DdNode * bFunc0, * bFunc1, * bFunc;
    int i;
    // mark the fanins of the cone
    Abc_NodeConeMark( vFanins );
    // collect the nodes in the DFS order
    Vec_PtrClear( vVisited );
    Abc_NodeConeMarkCollect_rec( pNode, vVisited );
    // unmark both sets
    Abc_NodeConeUnmark( vFanins );
    Abc_NodeConeUnmark( vVisited );
    // set the elementary BDDs
    Vec_PtrForEachEntry( vFanins, pNode, i )
        pNode->pCopy = (Abc_Obj_t *)pbVars[i];
    // compute the BDDs for the collected nodes
    Vec_PtrForEachEntry( vVisited, pNode, i )
    {
        bFunc0 = Cudd_NotCond( Abc_ObjFanin0(pNode)->pCopy, Abc_ObjFaninC0(pNode) );
        bFunc1 = Cudd_NotCond( Abc_ObjFanin1(pNode)->pCopy, Abc_ObjFaninC1(pNode) );
        bFunc  = Cudd_bddAnd( dd, bFunc0, bFunc1 );    Cudd_Ref( bFunc );
        pNode->pCopy = (Abc_Obj_t *)bFunc;
    }
    Cudd_Ref( bFunc );
    // dereference the intermediate ones
    Vec_PtrForEachEntry( vVisited, pNode, i )
        Cudd_RecursiveDeref( dd, (DdNode *)pNode->pCopy );
    Cudd_Deref( bFunc );
    return bFunc;
}


/**Function*************************************************************

  Synopsis    [Decides whether to accept the given factored form.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int  Abc_NodeDecide( Abc_ManRes_t * p )
{
    return 0;
}

/**Function*************************************************************

  Synopsis    [Replaces MFFC of the node by the new factored.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeUpdate( Abc_ManRes_t * p )
{
}




/**Function*************************************************************

  Synopsis    [Starts the resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_ManRes_t * Abc_NtkManResStart()
{
    Abc_ManRes_t * p;
    p = ALLOC( Abc_ManRes_t, 1 );
    p->vFaninsNode = Vec_PtrAlloc( 100 );
    p->vInsideNode = Vec_PtrAlloc( 100 );
    p->vFaninsCone = Vec_PtrAlloc( 100 );
    p->vInsideCone = Vec_PtrAlloc( 100 );
    p->vVisited    = Vec_PtrAlloc( 100 );
    p->vCube       = Vec_StrAlloc( 100 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Stops the resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkManResStop( Abc_ManRes_t * p )
{
    if ( p->bCubeX ) Cudd_RecursiveDeref( p->dd, p->bCubeX );
    if ( p->dd )     Extra_StopManager( p->dd );
    Vec_PtrFree( p->vFaninsNode );
    Vec_PtrFree( p->vInsideNode );
    Vec_PtrFree( p->vFaninsCone );
    Vec_PtrFree( p->vInsideCone );
    Vec_PtrFree( p->vVisited    );
    Vec_StrFree( p->vCube       );
    free( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


