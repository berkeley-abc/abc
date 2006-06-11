/**CFile****************************************************************

  FileName    [abcVanEijk.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Implementation of van Eijk's method for finding
  signal correspondence: C. A. J. van Eijk. "Sequential equivalence 
  checking based on structural similarities", IEEE Trans. CAD, 
  vol. 19(7), July 2000, pp. 814-819.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 2, 2005.]

  Revision    [$Id: abcVanEijk.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "fraig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Vec_Ptr_t *    Abc_NtkVanEijkClasses( Abc_Ntk_t * pNtk, int nFrames, int fVerbose );
static Vec_Ptr_t *    Abc_NtkVanEijkClassesDeriveBase( Abc_Ntk_t * pNtk, Vec_Ptr_t * vCorresp, int nFrames );
static Vec_Ptr_t *    Abc_NtkVanEijkClassesDeriveFirst( Abc_Ntk_t * pNtk, Vec_Ptr_t * vCorresp, int iFrame );
static int            Abc_NtkVanEijkClassesRefine( Abc_Ntk_t * pNtk, Vec_Ptr_t * vCorresp, int iFrame, Vec_Ptr_t * vClasses );
static void           Abc_NtkVanEijkClassesOrder( Vec_Ptr_t * vClasses );
static int            Abc_NtkVanEijkClassesCountPairs( Vec_Ptr_t * vClasses );
static void           Abc_NtkVanEijkClassesTest( Abc_Ntk_t * pNtkSingle, Vec_Ptr_t * vClasses );

extern Abc_Ntk_t *    Abc_NtkVanEijkFrames( Abc_Ntk_t * pNtk, Vec_Ptr_t * vCorresp, int nFrames, int fAddLast, int fShortNames );
extern void           Abc_NtkVanEijkAddFrame( Abc_Ntk_t * pNtkFrames, Abc_Ntk_t * pNtk, int iFrame, Vec_Ptr_t * vCorresp, Vec_Ptr_t * vOrder, int fShortNames );
extern Fraig_Man_t *  Abc_NtkVanEijkFraig( Abc_Ntk_t * pMulti, int fInit );

static Abc_Ntk_t *    Abc_NtkVanEijkDeriveExdc( Abc_Ntk_t * pNtk, Vec_Ptr_t * vClasses );

////////////////////////////////////////////////////////////////////////
///                     INLINED FUNCTIONS                            ///
////////////////////////////////////////////////////////////////////////

// sets the correspondence of the node in the frame
static inline void        Abc_NodeVanEijkWriteCorresp( Abc_Obj_t * pNode, Vec_Ptr_t * vCorresp, int iFrame, Abc_Obj_t * pEntry ) 
{
    Vec_PtrWriteEntry( vCorresp, iFrame * Abc_NtkObjNumMax(pNode->pNtk) + pNode->Id, pEntry ); 
}
// returns the correspondence of the node in the frame
static inline Abc_Obj_t * Abc_NodeVanEijkReadCorresp( Abc_Obj_t * pNode, Vec_Ptr_t * vCorresp, int iFrame ) 
{
    return Vec_PtrEntry( vCorresp, iFrame * Abc_NtkObjNumMax(pNode->pNtk) + pNode->Id ); 
}
// returns the hash value of the node in the frame
static inline Abc_Obj_t * Abc_NodeVanEijkHash( Abc_Obj_t * pNode, Vec_Ptr_t * vCorresp, int iFrame ) 
{
    return Abc_ObjRegular( Abc_NodeVanEijkReadCorresp(pNode, vCorresp, iFrame)->pCopy );  
}
// returns the representative node of the class to which the node belongs
static inline Abc_Obj_t * Abc_NodeVanEijkRepr( Abc_Obj_t * pNode ) 
{
    if ( pNode->pNext == NULL )
        return NULL;
    while ( pNode->pNext )   
        pNode = pNode->pNext;
    return pNode;
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Derives classes of sequentially equivalent nodes.]

  Description [Performs sequential sweep by combining the equivalent
  nodes. Adds EXDC network to the current network to record the subset
  of unreachable states computed by identifying the equivalent nodes.]
               
  SideEffects []
 
  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkVanEijk( Abc_Ntk_t * pNtk, int nFrames, int fExdc, int fVerbose )
{
    Fraig_Params_t Params;
    Abc_Ntk_t * pNtkSingle;
    Vec_Ptr_t * vClasses;
    Abc_Ntk_t * pNtkNew;

    assert( Abc_NtkIsStrash(pNtk) );

    // FRAIG the network to get rid of combinational equivalences
    Fraig_ParamsSetDefaultFull( &Params );
    pNtkSingle = Abc_NtkFraig( pNtk, &Params, 0, 0 );
    Abc_AigSetNodePhases( pNtkSingle );
    Abc_NtkCleanNext(pNtkSingle);

    // get the equivalence classes
    vClasses = Abc_NtkVanEijkClasses( pNtkSingle, nFrames, fVerbose );
    if ( Vec_PtrSize(vClasses) > 0 )
    {
        // transform the network by merging nodes in the equivalence classes
        pNtkNew = Abc_NtkVanEijkFrames( pNtkSingle, NULL, 1, 0, 1 );
//        pNtkNew = Abc_NtkDup( pNtkSingle );  
        // derive the EXDC network if asked
        if ( fExdc )
            pNtkNew->pExdc = Abc_NtkVanEijkDeriveExdc( pNtkSingle, vClasses );
    }
    else
        pNtkNew = Abc_NtkDup( pNtkSingle );  
    Abc_NtkVanEijkClassesTest( pNtkSingle, vClasses );
    Vec_PtrFree( vClasses );

    Abc_NtkDelete( pNtkSingle );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Derives the classes of sequentially equivalent nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkVanEijkClasses( Abc_Ntk_t * pNtkSingle, int nFrames, int fVerbose )
{
    Fraig_Man_t * pFraig;
    Abc_Ntk_t * pNtkMulti;
    Vec_Ptr_t * vCorresp, * vClasses;
    int nIter, RetValue;
    int nAddFrames = 0;

    if ( fVerbose )
        printf( "The number of ANDs after FRAIGing = %d.\n", Abc_NtkNodeNum(pNtkSingle) );

    // get the AIG of the base case
    vCorresp = Vec_PtrAlloc( 100 );
    pNtkMulti = Abc_NtkVanEijkFrames( pNtkSingle, vCorresp, nFrames + nAddFrames, 0, 0 );
    if ( fVerbose )
        printf( "The number of ANDs in %d timeframes = %d.\n", nFrames + nAddFrames, Abc_NtkNodeNum(pNtkMulti) );

    // FRAIG the initialized frames (labels the nodes of pNtkMulti with FRAIG nodes to be used as hash keys)
    pFraig = Abc_NtkVanEijkFraig( pNtkMulti, 1 );
    Fraig_ManFree( pFraig );

    // find initial equivalence classes
    vClasses = Abc_NtkVanEijkClassesDeriveBase( pNtkSingle, vCorresp, nFrames + nAddFrames );
    if ( fVerbose )
        printf( "The number of classes in the base case    = %5d.  Pairs = %8d.\n", Vec_PtrSize(vClasses), Abc_NtkVanEijkClassesCountPairs(vClasses) );
    Abc_NtkDelete( pNtkMulti );

    // refine the classes using iterative FRAIGing
    for ( nIter = 1; Vec_PtrSize(vClasses) > 0; nIter++ )
    {
        // derive the network with equivalence classes
        Abc_NtkVanEijkClassesOrder( vClasses );
        pNtkMulti = Abc_NtkVanEijkFrames( pNtkSingle, vCorresp, nFrames, 1, 0 );
        // simulate with classes (TO DO)

        // FRAIG the unitialized frames (labels the nodes of pNtkMulti with FRAIG nodes to be used as hash keys)
        pFraig = Abc_NtkVanEijkFraig( pNtkMulti, 0 );
        Fraig_ManFree( pFraig );

        // refine the classes
        RetValue = Abc_NtkVanEijkClassesRefine( pNtkSingle, vCorresp, nFrames, vClasses );
        Abc_NtkDelete( pNtkMulti );
        if ( fVerbose )
            printf( "The number of classes after %2d iterations = %5d.  Pairs = %8d.\n", nIter, Vec_PtrSize(vClasses), Abc_NtkVanEijkClassesCountPairs(vClasses) );
        // quit if there is no change
        if ( RetValue == 0 )
            break;
    }
    Vec_PtrFree( vCorresp );

    if ( fVerbose )
    {
        Abc_Obj_t * pObj, * pClass;
        int i, Counter;
        printf( "The classes are: " );
        Vec_PtrForEachEntry( vClasses, pClass, i )
        {
            Counter = 0;
            for ( pObj = pClass; pObj; pObj = pObj->pNext )
                Counter++;
            printf( " %d", Counter );
/*
            printf( " = {" );
            for ( pObj = pClass; pObj; pObj = pObj->pNext )
                printf( " %d", pObj->Id );
            printf( " } " );
*/
        }
        printf( "\n" );
    }
    return vClasses;
}

/**Function*************************************************************

  Synopsis    [Computes the equivalence classes of nodes using the base case.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkVanEijkClassesDeriveBase( Abc_Ntk_t * pNtkSingle, Vec_Ptr_t * vCorresp, int nFrames )
{
    Vec_Ptr_t * vClasses;
    int i, RetValue;
    // derive the classes for the last frame
    vClasses = Abc_NtkVanEijkClassesDeriveFirst( pNtkSingle, vCorresp, nFrames - 1 );
    // refine the classes using other timeframes
    for ( i = 0; i < nFrames - 1; i++ )
    {
        if ( Vec_PtrSize(vClasses) == 0 )
            break;
        RetValue = Abc_NtkVanEijkClassesRefine( pNtkSingle, vCorresp, i, vClasses );
//        if ( RetValue )
//            printf( " yes%s", (i==nFrames-2 ? "\n":"") );
//        else
//            printf( " no%s", (i==nFrames-2 ? "\n":"") );
    }
    return vClasses;
}


/**Function*************************************************************

  Synopsis    [Computes the equivalence classes of nodes.]

  Description [Original network (pNtk) is mapped into the unfolded frames 
  using given array of nodes (vCorresp). Each node in the unfolded frames 
  is mapped into a FRAIG node (pNode->pCopy). This procedure uses next 
  pointers (pNode->pNext) to combine the nodes into equivalence classes.
  Each class is represented by its representative node with the minimum level.
  Only the last frame is considered.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkVanEijkClassesDeriveFirst( Abc_Ntk_t * pNtk, Vec_Ptr_t * vCorresp, int iFrame )
{
    Abc_Obj_t * pNode, * pKey, ** ppSlot;
    stmm_table * tTable;
    stmm_generator * gen;
    Vec_Ptr_t * vClasses;
    int i;
    // start the table hashing FRAIG nodes into classes of original network nodes
    tTable = stmm_init_table( st_ptrcmp, st_ptrhash );
    // create the table
    Abc_NtkCleanNext( pNtk );
    Abc_NtkForEachObj( pNtk, pNode, i )
    {
        if ( Abc_ObjIsPo(pNode) )
            continue;
        pKey = Abc_NodeVanEijkHash( pNode, vCorresp, iFrame );
        if ( !stmm_find_or_add( tTable, (char *)pKey, (char ***)&ppSlot ) )
            *ppSlot = NULL;
        pNode->pNext = *ppSlot;
        *ppSlot = pNode;
    }
    // collect only non-trivial classes
    vClasses = Vec_PtrAlloc( 100 );
    stmm_foreach_item( tTable, gen, (char **)&pKey, (char **)&pNode )
        if ( pNode->pNext )
            Vec_PtrPush( vClasses, pNode );
    stmm_free_table( tTable );
    return vClasses;
}

/**Function*************************************************************

  Synopsis    [Refines the classes using one frame.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkVanEijkClassesRefine( Abc_Ntk_t * pNtk, Vec_Ptr_t * vCorresp, int iFrame, Vec_Ptr_t * vClasses )
{
    Abc_Obj_t * pHeadSame, ** ppTailSame;
    Abc_Obj_t * pHeadDiff, ** ppTailDiff;
    Abc_Obj_t * pNode, * pClass, * pKey;
    int i, k, fChange = 0;
    Vec_PtrForEachEntry( vClasses, pClass, i )
    {
//        assert( pClass->pNext );
        pKey = Abc_NodeVanEijkHash( pClass, vCorresp, iFrame );
        for ( pNode = pClass->pNext; pNode; pNode = pNode->pNext )
            if ( Abc_NodeVanEijkHash(pNode, vCorresp, iFrame) != pKey )
                break;
        if ( pNode == NULL )
            continue;
        fChange = 1;
        // create two classes
        pHeadSame = NULL; ppTailSame = &pHeadSame;
        pHeadDiff = NULL; ppTailDiff = &pHeadDiff;
        for ( pNode = pClass; pNode; pNode = pNode->pNext )
            if ( Abc_NodeVanEijkHash(pNode, vCorresp, iFrame) != pKey )
                *ppTailDiff = pNode, ppTailDiff = &pNode->pNext;
            else
                *ppTailSame = pNode, ppTailSame = &pNode->pNext;
        *ppTailSame = NULL;
        *ppTailDiff = NULL;
        assert( pHeadSame && pHeadDiff );
        // put the updated class back
        Vec_PtrWriteEntry( vClasses, i, pHeadSame );
        // append the new class to be processed later
        Vec_PtrPush( vClasses, pHeadDiff );
    }
    // remove trivial classes
    k = 0;
    Vec_PtrForEachEntry( vClasses, pClass, i )
        if ( pClass->pNext )
            Vec_PtrWriteEntry( vClasses, k++, pClass );
    Vec_PtrShrink( vClasses, k );
    return fChange;
}

/**Function*************************************************************

  Synopsis    [Orders nodes in the equivalence classes.]

  Description [Finds a min-level representative of each class and puts it last.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkVanEijkClassesOrder( Vec_Ptr_t * vClasses )
{
    Abc_Obj_t * pClass, * pNode, * pPrev, * pNodeMin, * pPrevMin;
    int i;
    // go through the classes
    Vec_PtrForEachEntry( vClasses, pClass, i )
    {
        assert( pClass->pNext );
        pPrevMin = NULL;
        pNodeMin = pClass;
        for ( pPrev = pClass, pNode = pClass->pNext; pNode; pPrev = pNode, pNode = pNode->pNext )
            if ( pNodeMin->Level >= pNode->Level )
            {
                pPrevMin = pPrev;
                pNodeMin = pNode;
            }
        if ( pNodeMin->pNext == NULL ) // already last
            continue;
        // update the class
        if ( pNodeMin == pClass )
            Vec_PtrWriteEntry( vClasses, i, pNodeMin->pNext );
        else
            pPrevMin->pNext = pNodeMin->pNext;
        // attach the min node
        assert( pPrev->pNext == NULL );
        pPrev->pNext = pNodeMin;
        pNodeMin->pNext = NULL;
    }
    Vec_PtrForEachEntry( vClasses, pClass, i )
        assert( pClass->pNext );
}

/**Function*************************************************************

  Synopsis    [Counts pairs of equivalent nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkVanEijkClassesCountPairs( Vec_Ptr_t * vClasses ) 
{
    Abc_Obj_t * pClass, * pNode;
    int i, nPairs = 0;
    Vec_PtrForEachEntry( vClasses, pClass, i )
    {
        assert( pClass->pNext );
        for ( pNode = pClass->pNext; pNode; pNode = pNode->pNext )
            nPairs++;
    }
    return nPairs;
}

/**Function*************************************************************

  Synopsis    [Sanity check for the class representation.]

  Description [Checks that pNode->pNext is only used in the classes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkVanEijkClassesTest( Abc_Ntk_t * pNtkSingle, Vec_Ptr_t * vClasses )
{
    Abc_Obj_t * pClass, * pObj;
    int i;
    Abc_NtkCleanCopy( pNtkSingle );
    Vec_PtrForEachEntry( vClasses, pClass, i )
        for ( pObj = pClass; pObj; pObj = pObj->pNext )
            if ( pObj->pNext )
                pObj->pCopy = (Abc_Obj_t *)1;
    Abc_NtkForEachObj( pNtkSingle, pObj, i )
        assert( (pObj->pCopy != NULL) == (pObj->pNext != NULL) );
    Abc_NtkCleanCopy( pNtkSingle );
}


/**Function*************************************************************

  Synopsis    [Performs DFS for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkVanEijkDfs_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vNodes )
{
    Abc_Obj_t * pRepr;
    // skip CI and const
    if ( Abc_ObjFaninNum(pNode) < 2 )
        return;
    // if this node is already visited, skip
    if ( Abc_NodeIsTravIdCurrent( pNode ) )
        return;
    // mark the node as visited
    Abc_NodeSetTravIdCurrent( pNode );
    assert( Abc_ObjIsNode( pNode ) );
    // check if the node belongs to the class
    if ( pRepr = Abc_NodeVanEijkRepr(pNode) )
        Abc_NtkVanEijkDfs_rec( pRepr, vNodes );
    else
    {
        Abc_NtkVanEijkDfs_rec( Abc_ObjFanin0(pNode), vNodes );
        Abc_NtkVanEijkDfs_rec( Abc_ObjFanin1(pNode), vNodes );
    }
    // add the node after the fanins have been added
    Vec_PtrPush( vNodes, pNode );
}

/**Function*************************************************************

  Synopsis    [Finds DFS ordering of nodes using equivalence classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkVanEijkDfs( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pObj;
    int i;
    vNodes = Vec_PtrAlloc( 100 );
    Abc_NtkIncrementTravId( pNtk );
    Abc_NtkForEachCo( pNtk, pObj, i )
        Abc_NtkVanEijkDfs_rec( Abc_ObjFanin0(pObj), vNodes );
    return vNodes;
}


/**Function*************************************************************

  Synopsis    [Derives the timeframes of the network.]

  Description [Returns mapping of the orig nodes into the frame nodes (vCorresp).]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkVanEijkFrames( Abc_Ntk_t * pNtk, Vec_Ptr_t * vCorresp, int nFrames, int fAddLast, int fShortNames )
{
    char Buffer[100];
    Abc_Ntk_t * pNtkFrames;
    Abc_Obj_t * pLatch, * pLatchNew;
    Vec_Ptr_t * vOrder;
    int i;
    assert( nFrames > 0 );
    assert( Abc_NtkIsStrash(pNtk) );
    assert( Abc_NtkIsDfsOrdered(pNtk) );
    // clean the array of connections
    if ( vCorresp )
        Vec_PtrFill( vCorresp, (nFrames + fAddLast)*Abc_NtkObjNumMax(pNtk), NULL );
    // start the new network
    pNtkFrames = Abc_NtkAlloc( ABC_NTK_STRASH, ABC_FUNC_AIG );
    if ( fShortNames )
    {
        pNtkFrames->pName = Extra_UtilStrsav(pNtk->pName);
        pNtkFrames->pSpec = Extra_UtilStrsav(pNtk->pSpec);
    }
    else
    {
        sprintf( Buffer, "%s_%d_frames", pNtk->pName, nFrames + fAddLast );
        pNtkFrames->pName = Extra_UtilStrsav(Buffer);
    }
    // map the constant nodes
    Abc_NtkConst1(pNtk)->pCopy = Abc_NtkConst1(pNtkFrames);
    // create new latches and remember them in the new latches
    Abc_NtkForEachLatch( pNtk, pLatch, i )
        Abc_NtkDupObj( pNtkFrames, pLatch );
    // collect nodes in such a way each class representative goes first
    vOrder = Abc_NtkVanEijkDfs( pNtk );
    // create the timeframes
    for ( i = 0; i < nFrames; i++ )
        Abc_NtkVanEijkAddFrame( pNtkFrames, pNtk, i, vCorresp, vOrder, fShortNames );
    Vec_PtrFree( vOrder );
    // add one more timeframe without class info
    if ( fAddLast )
        Abc_NtkVanEijkAddFrame( pNtkFrames, pNtk, nFrames, vCorresp, NULL, fShortNames );
    // connect the new latches to the outputs of the last frame
    Abc_NtkForEachLatch( pNtk, pLatch, i )
    {
        pLatchNew = Abc_NtkLatch(pNtkFrames, i);
        Abc_ObjAddFanin( pLatchNew, pLatch->pCopy );
        Abc_NtkLogicStoreName( pLatchNew, Abc_ObjName(pLatch) );
        pLatch->pNext = NULL;
    }
    // remove dangling nodes
//    Abc_AigCleanup( pNtkFrames->pManFunc );
    // otherwise some external nodes may have dandling pointers

    // make sure that everything is okay
    if ( !Abc_NtkCheck( pNtkFrames ) )
        printf( "Abc_NtkVanEijkFrames: The network check has failed.\n" );
    return pNtkFrames;
}

/**Function*************************************************************

  Synopsis    [Adds one time frame to the new network.]

  Description [If the ordering of nodes is given, uses it. Otherwise, 
  uses the DSF order of the nodes in the network.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkVanEijkAddFrame( Abc_Ntk_t * pNtkFrames, Abc_Ntk_t * pNtk, int iFrame, Vec_Ptr_t * vCorresp, Vec_Ptr_t * vOrder, int fShortNames )
{
    char Buffer[10];
    Abc_Obj_t * pNode, * pLatch, * pRepr;
    Vec_Ptr_t * vTemp;
    int i;
    // create the prefix to be added to the node names
    sprintf( Buffer, "_%02d", iFrame );
    // add the new PI nodes
    Abc_NtkForEachPi( pNtk, pNode, i )
    {
        pNode->pCopy = Abc_NtkCreatePi(pNtkFrames);       
        if ( fShortNames )
            Abc_NtkLogicStoreName( pNode->pCopy, Abc_ObjName(pNode) );
        else         
            Abc_NtkLogicStoreNamePlus( pNode->pCopy, Abc_ObjName(pNode), Buffer );
    }
    // remember the CI mapping 
    if ( vCorresp )
    {
        pNode = Abc_NtkConst1(pNtk);
        Abc_NodeVanEijkWriteCorresp( pNode, vCorresp, iFrame, Abc_ObjRegular(pNode->pCopy) );
        Abc_NtkForEachCi( pNtk, pNode, i )
            Abc_NodeVanEijkWriteCorresp( pNode, vCorresp, iFrame, Abc_ObjRegular(pNode->pCopy) );
    }
    // go through the nodes in the given order or in the natural order
    if ( vOrder )
    {
        // add the internal nodes
        Vec_PtrForEachEntry( vOrder, pNode, i )
        {
            if ( pRepr = Abc_NodeVanEijkRepr(pNode) )
                pNode->pCopy = Abc_ObjNotCond( pRepr->pCopy, pNode->fPhase ^ pRepr->fPhase );
            else
                pNode->pCopy = Abc_AigAnd( pNtkFrames->pManFunc, Abc_ObjChild0Copy(pNode), Abc_ObjChild1Copy(pNode) );
            assert( Abc_ObjRegular(pNode->pCopy) != NULL );
            if ( vCorresp )
                Abc_NodeVanEijkWriteCorresp( pNode, vCorresp, iFrame, Abc_ObjRegular(pNode->pCopy) );
        }
    }
    else
    {
        // add the internal nodes
        Abc_AigForEachAnd( pNtk, pNode, i )
        {
            pNode->pCopy = Abc_AigAnd( pNtkFrames->pManFunc, Abc_ObjChild0Copy(pNode), Abc_ObjChild1Copy(pNode) );
            assert( Abc_ObjRegular(pNode->pCopy) != NULL );
            if ( vCorresp )
                Abc_NodeVanEijkWriteCorresp( pNode, vCorresp, iFrame, Abc_ObjRegular(pNode->pCopy) );
        }
    }
    // add the new POs
    Abc_NtkForEachPo( pNtk, pNode, i )
    {
        pNode->pCopy = Abc_NtkCreatePo(pNtkFrames);       
        Abc_ObjAddFanin( pNode->pCopy, Abc_ObjChild0Copy(pNode) );
        if ( fShortNames )
            Abc_NtkLogicStoreName( pNode->pCopy, Abc_ObjName(pNode) );
        else         
            Abc_NtkLogicStoreNamePlus( pNode->pCopy, Abc_ObjName(pNode), Buffer );
    }
    // transfer the implementation of the latch drivers to the latches
    vTemp = Vec_PtrAlloc( 100 );
    Abc_NtkForEachLatch( pNtk, pLatch, i )
        Vec_PtrPush( vTemp, Abc_ObjChild0Copy(pLatch) );
    Abc_NtkForEachLatch( pNtk, pLatch, i )
        pLatch->pCopy = Vec_PtrEntry( vTemp, i );
    Vec_PtrFree( vTemp );

    Abc_AigForEachAnd( pNtk, pNode, i )
        pNode->pCopy = NULL;
}

/**Function*************************************************************

  Synopsis    [Fraigs the network with or without initialization.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Fraig_Man_t * Abc_NtkVanEijkFraig( Abc_Ntk_t * pMulti, int fInit )
{
    Fraig_Man_t * pMan;
    Fraig_Params_t Params;
    ProgressBar * pProgress;
    Abc_Obj_t * pNode;
    int i;
    assert( Abc_NtkIsStrash(pMulti) );
    // create the FRAIG manager
    Fraig_ParamsSetDefaultFull( &Params );
    pMan = Fraig_ManCreate( &Params );
    // clean the copy fields in the old network
    Abc_NtkCleanCopy( pMulti );
    // map the constant nodes
    Abc_NtkConst1(pMulti)->pCopy = (Abc_Obj_t *)Fraig_ManReadConst1(pMan);
    if ( fInit )
    {
        // map the PI nodes
        Abc_NtkForEachPi( pMulti, pNode, i )
            pNode->pCopy = (Abc_Obj_t *)Fraig_ManReadIthVar(pMan, i);
        // map the latches
        Abc_NtkForEachLatch( pMulti, pNode, i )
           pNode->pCopy = (Abc_Obj_t *)Fraig_NotCond( Fraig_ManReadConst1(pMan), !Abc_LatchIsInit1(pNode) );
    }
    else
    {
        // map the CI nodes
        Abc_NtkForEachCi( pMulti, pNode, i )
            pNode->pCopy = (Abc_Obj_t *)Fraig_ManReadIthVar(pMan, i);
    }
    // perform fraiging
    pProgress = Extra_ProgressBarStart( stdout, Abc_NtkObjNumMax(pMulti) );
    Abc_AigForEachAnd( pMulti, pNode, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        pNode->pCopy = (Abc_Obj_t *)Fraig_NodeAnd( pMan, 
                Fraig_NotCond( Abc_ObjFanin0(pNode)->pCopy, Abc_ObjFaninC0(pNode) ),
                Fraig_NotCond( Abc_ObjFanin1(pNode)->pCopy, Abc_ObjFaninC1(pNode) ) );
    }
    Extra_ProgressBarStop( pProgress );
    return pMan;
}


/**Function*************************************************************

  Synopsis    [Create EXDC from the equivalence classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkVanEijkDeriveExdc( Abc_Ntk_t * pNtk, Vec_Ptr_t * vClasses )
{
    Abc_Ntk_t * pNtkNew; 
    Abc_Obj_t * pClass, * pNode, * pRepr, * pObj;//, *pObjNew;
    Abc_Obj_t * pMiter, * pTotal;
    Vec_Ptr_t * vCone;
    int i, k;

    assert( Abc_NtkIsStrash(pNtk) );

    // start the network
    pNtkNew = Abc_NtkAlloc( pNtk->ntkType, pNtk->ntkFunc );
    pNtkNew->pName = Extra_UtilStrsav("exdc");
    pNtkNew->pSpec = NULL;

    // map the constant nodes
    Abc_NtkConst1(pNtk)->pCopy = Abc_NtkConst1(pNtkNew);
    // for each CI, create PI
    Abc_NtkForEachCi( pNtk, pObj, i )
        Abc_NtkLogicStoreName( pObj->pCopy = Abc_NtkCreatePi(pNtkNew), Abc_ObjName(pObj) );
    // cannot add latches here because pLatch->pCopy pointers are used

    // create the cones for each pair of nodes in an equivalence class
    pTotal = Abc_ObjNot( Abc_NtkConst1(pNtkNew) );
    Vec_PtrForEachEntry( vClasses, pClass, i )
    {
        assert( pClass->pNext );
        // get the cone for the representative node
        pRepr = Abc_NodeVanEijkRepr( pClass );
        if ( Abc_ObjFaninNum(pRepr) == 2 )
        {
            vCone = Abc_NtkDfsNodes( pNtk, &pRepr, 1 );
            Vec_PtrForEachEntry( vCone, pObj, k )
                pObj->pCopy = Abc_AigAnd( pNtkNew->pManFunc, Abc_ObjChild0Copy(pObj), Abc_ObjChild1Copy(pObj) );
            Vec_PtrFree( vCone );
            assert( pObj == pRepr );
        }
        // go through the node pairs (representative is last in the list)
        for ( pNode = pClass; pNode != pRepr; pNode = pNode->pNext )
        {
            // get the cone for the node
            assert( Abc_ObjFaninNum(pNode) == 2 );
            vCone = Abc_NtkDfsNodes( pNtk, &pNode, 1 );
            Vec_PtrForEachEntry( vCone, pObj, k )
                pObj->pCopy = Abc_AigAnd( pNtkNew->pManFunc, Abc_ObjChild0Copy(pObj), Abc_ObjChild1Copy(pObj) );
            Vec_PtrFree( vCone );
            assert( pObj == pNode );
            // complement if there is phase difference
            pNode->pCopy = Abc_ObjNotCond( pNode->pCopy, pNode->fPhase ^ pRepr->fPhase );
            // add the miter
            pMiter = Abc_AigXor( pNtkNew->pManFunc, pRepr->pCopy, pNode->pCopy );
        }
        // add the miter to the final
        pTotal = Abc_AigOr( pNtkNew->pManFunc, pTotal, pMiter );
    }

/*
    // create the only PO
    pObjNew = Abc_NtkCreatePo( pNtkNew );
    // add the PO name
    Abc_NtkLogicStoreName( pObjNew, "DC" );
    // add the PO
    Abc_ObjAddFanin( pObjNew, pTotal );

    // quontify the PIs existentially
    pNtkNew = Abc_NtkMiterQuantifyPis( pNtkNew );

    // get the new PO
    pObjNew = Abc_NtkPo( pNtkNew, 0 );
    // remember the miter output
    pTotal = Abc_ObjChild0( pObjNew );
    // remove the PO
    Abc_NtkDeleteObj( pObjNew );

    // make the old network point to the new things
    Abc_NtkConst1(pNtk)->pCopy = Abc_NtkConst1(pNtkNew);
    Abc_NtkForEachCi( pNtk, pObj, i )
        pObj->pCopy = Abc_NtkPi( pNtkNew, i );
*/

    // for each CO, create PO (skip POs equal to CIs because of name conflict)
    Abc_NtkForEachPo( pNtk, pObj, i )
        if ( !Abc_ObjIsCi(Abc_ObjFanin0(pObj)) )
            Abc_NtkLogicStoreName( pObj->pCopy = Abc_NtkCreatePo(pNtkNew), Abc_ObjName(pObj) );
    Abc_NtkForEachLatch( pNtk, pObj, i )
        Abc_NtkLogicStoreName( pObj->pCopy = Abc_NtkCreatePo(pNtkNew), Abc_ObjNameSuffix( pObj, "_in") );

    // link to the POs of the network
    Abc_NtkForEachPo( pNtk, pObj, i )
        if ( !Abc_ObjIsCi(Abc_ObjFanin0(pObj)) )
            Abc_ObjAddFanin( pObj->pCopy, pTotal );
    Abc_NtkForEachLatch( pNtk, pObj, i )
        Abc_ObjAddFanin( pObj->pCopy, pTotal );

    // remove the extra nodes
    Abc_AigCleanup( pNtkNew->pManFunc );

    // check the result
    if ( !Abc_NtkCheck( pNtkNew ) )
    {
        printf( "Abc_NtkVanEijkDeriveExdc: The network check has failed.\n" );
        Abc_NtkDelete( pNtkNew );
        return NULL;
    }
    return pNtkNew;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


