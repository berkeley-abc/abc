/**CFile****************************************************************

  FileName    [abcAig.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Simple structural hashing package.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcAig.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

/*
    AIG is an And-Inv Graph with structural hashing.
    It is always structurally hashed. It means that at any time:
    - for each AND gate, there are no other AND gates with the same children
    - the constants are propagated
    - there is no single-input nodes (inverters/buffers)
    Additionally the following invariants are satisfied:
    - there are no dangling nodes (the nodes without fanout)
    - the level of each AND gate reflects the levels of this fanins
    - the EXOR-status of each node is up-to-date
    The operations that are performed on AIGs:
    - building new nodes (Abc_AigAnd)
    - performing elementary Boolean operations (Abc_AigOr, Abc_AigXor, etc)
    - replacing one node by another (Abc_AigReplace)
    - propagating constants (Abc_AigReplace)
    When AIG is duplicated, the new graph is structurally hashed too.
    If this repeated hashing leads to fewer nodes, it means the original
    AIG was not strictly hashed (one of the conditions above is violated).
*/

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// the simple AIG manager
struct Abc_Aig_t_
{
    Abc_Ntk_t *       pNtkAig;           // the AIG network
    Abc_Obj_t *       pConst1;           // the constant 1 node
    Abc_Obj_t *       pReset;            // the sequential reset node
    Abc_Obj_t **      pBins;             // the table bins
    int               nBins;             // the size of the table
    int               nEntries;          // the total number of entries in the table
    Vec_Ptr_t *       vNodes;            // the temporary array of nodes
    Vec_Ptr_t *       vStackDelete;      // the nodes to be deleted
    Vec_Ptr_t *       vStackReplaceOld;  // the nodes to be replaced
    Vec_Ptr_t *       vStackReplaceNew;  // the nodes to be used for replacement
    Vec_Vec_t *       vLevels;           // the nodes to be updated
    Vec_Vec_t *       vLevelsR;          // the nodes to be updated
};

// iterators through the entries in the linked lists of nodes
#define Abc_AigBinForEachEntry( pBin, pEnt )                   \
    for ( pEnt = pBin;                                         \
          pEnt;                                                \
          pEnt = pEnt->pNext )
#define Abc_AigBinForEachEntrySafe( pBin, pEnt, pEnt2 )        \
    for ( pEnt = pBin,                                         \
          pEnt2 = pEnt? pEnt->pNext: NULL;                     \
          pEnt;                                                \
          pEnt = pEnt2,                                        \
          pEnt2 = pEnt? pEnt->pNext: NULL )

// hash key for the structural hash table
static inline unsigned Abc_HashKey2( Abc_Obj_t * p0, Abc_Obj_t * p1, int TableSize ) { return ((unsigned)(p0) + (unsigned)(p1) * 12582917) % TableSize; }
//static inline unsigned Abc_HashKey2( Abc_Obj_t * p0, Abc_Obj_t * p1, int TableSize ) { return ((unsigned)((a)->Id + (b)->Id) * ((a)->Id + (b)->Id + 1) / 2) % TableSize; }

// structural hash table procedures
static Abc_Obj_t * Abc_AigAndCreate( Abc_Aig_t * pMan, Abc_Obj_t * p0, Abc_Obj_t * p1 );
static Abc_Obj_t * Abc_AigAndCreateFrom( Abc_Aig_t * pMan, Abc_Obj_t * p0, Abc_Obj_t * p1, Abc_Obj_t * pAnd );
static void        Abc_AigAndDelete( Abc_Aig_t * pMan, Abc_Obj_t * pThis );
static void        Abc_AigResize( Abc_Aig_t * pMan );
// incremental AIG procedures
static void        Abc_AigReplace_int( Abc_Aig_t * pMan );
static void        Abc_AigDelete_int( Abc_Aig_t * pMan );
static void        Abc_AigUpdateLevel_int( Abc_Aig_t * pMan );
static void        Abc_AigUpdateLevelR_int( Abc_Aig_t * pMan );
static void        Abc_AigRemoveFromLevelStructure( Vec_Vec_t * vStruct, Abc_Obj_t * pNode );
static void        Abc_AigRemoveFromLevelStructureR( Vec_Vec_t * vStruct, Abc_Obj_t * pNode );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Allocates the local AIG manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Aig_t * Abc_AigAlloc( Abc_Ntk_t * pNtkAig )
{
    Abc_Aig_t * pMan;
    // start the manager
    pMan = ALLOC( Abc_Aig_t, 1 );
    memset( pMan, 0, sizeof(Abc_Aig_t) );
    // allocate the table
    pMan->nBins    = Cudd_PrimeCopy( 10000 );
    pMan->pBins    = ALLOC( Abc_Obj_t *, pMan->nBins );
    memset( pMan->pBins, 0, sizeof(Abc_Obj_t *) * pMan->nBins );
    pMan->vNodes   = Vec_PtrAlloc( 100 );
    pMan->vStackDelete     = Vec_PtrAlloc( 100 );
    pMan->vStackReplaceOld = Vec_PtrAlloc( 100 );
    pMan->vStackReplaceNew = Vec_PtrAlloc( 100 );
    pMan->vLevels          = Vec_VecAlloc( 100 );
    pMan->vLevelsR         = Vec_VecAlloc( 100 );
    // save the current network
    pMan->pNtkAig = pNtkAig;
    // allocate constant nodes
    pMan->pConst1 = Abc_NtkCreateNode( pNtkAig );    
    pMan->pConst1->fPhase = 1;
    pMan->pReset  = Abc_NtkCreateNode( pNtkAig );
    // subtract these nodes from the total number
    pNtkAig->nNodes -= 2;
    return pMan;
}

/**Function*************************************************************

  Synopsis    [Duplicated the AIG manager.]

  Description [Assumes that CI/CO nodes are already created.
  Transfers the latch attributes on the edges.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Aig_t * Abc_AigDup( Abc_Aig_t * pMan, Abc_Aig_t * pManNew )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pObj;
    int i;
    assert( Abc_NtkCiNum(pMan->pNtkAig)    == Abc_NtkCiNum(pManNew->pNtkAig) );
    assert( Abc_NtkCoNum(pMan->pNtkAig)    == Abc_NtkCoNum(pManNew->pNtkAig) );
    assert( Abc_NtkLatchNum(pMan->pNtkAig) == Abc_NtkLatchNum(pManNew->pNtkAig) );
    // set mapping of the constant nodes
    Abc_AigConst1( pMan )->pCopy = Abc_AigConst1( pManNew );
    Abc_AigReset( pMan )->pCopy  = Abc_AigReset( pManNew );
    // set the mapping of CIs/COs
    Abc_NtkForEachPi( pMan->pNtkAig, pObj, i )
        pObj->pCopy = Abc_NtkPi( pManNew->pNtkAig, i );
    Abc_NtkForEachPo( pMan->pNtkAig, pObj, i )
        pObj->pCopy = Abc_NtkPo( pManNew->pNtkAig, i );
    Abc_NtkForEachLatch( pMan->pNtkAig, pObj, i )
        pObj->pCopy = Abc_NtkLatch( pManNew->pNtkAig, i );
    // copy internal nodes
    vNodes = Abc_AigDfs( pMan->pNtkAig, 1, 0 );
    Vec_PtrForEachEntry( vNodes, pObj, i )
    {
        if ( !Abc_NodeIsAigAnd(pObj) )
            continue;
        pObj->pCopy = Abc_AigAnd( pManNew, Abc_ObjChild0Copy(pObj), Abc_ObjChild1Copy(pObj) );
        // transfer latch attributes
        Abc_ObjSetFaninL0( pObj->pCopy, Abc_ObjFaninL0(pObj) );
        Abc_ObjSetFaninL1( pObj->pCopy, Abc_ObjFaninL1(pObj) );
    }
    // relink the choice nodes
    Vec_PtrForEachEntry( vNodes, pObj, i )
        if ( pObj->pData )
            pObj->pCopy->pData = ((Abc_Obj_t *)pObj->pData)->pCopy;
    Vec_PtrFree( vNodes );
    // relink the CO nodes
    Abc_NtkForEachCo( pMan->pNtkAig, pObj, i )
    {
        Abc_ObjAddFanin( pObj->pCopy, Abc_ObjChild0Copy(pObj) );
        Abc_ObjSetFaninL0( pObj->pCopy, Abc_ObjFaninL0(pObj) );
    }
    // get the number of nodes before and after
    if ( Abc_NtkNodeNum(pMan->pNtkAig) != Abc_NtkNodeNum(pManNew->pNtkAig) )
        printf( "Warning: Structural hashing reduced %d nodes (should not happen).\n",
            Abc_NtkNodeNum(pMan->pNtkAig) - Abc_NtkNodeNum(pManNew->pNtkAig) );
    return pManNew;
}

/**Function*************************************************************

  Synopsis    [Deallocates the local AIG manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_AigFree( Abc_Aig_t * pMan )
{
    assert( Vec_PtrSize( pMan->vStackDelete )     == 0 );
    assert( Vec_PtrSize( pMan->vStackReplaceOld ) == 0 );
    assert( Vec_PtrSize( pMan->vStackReplaceNew ) == 0 );
    // free the table
    Vec_VecFree( pMan->vLevels );
    Vec_VecFree( pMan->vLevelsR );
    Vec_PtrFree( pMan->vStackDelete );
    Vec_PtrFree( pMan->vStackReplaceOld );
    Vec_PtrFree( pMan->vStackReplaceNew );
    Vec_PtrFree( pMan->vNodes );
    free( pMan->pBins );
    free( pMan );
}

/**Function*************************************************************

  Synopsis    [Returns the number of dangling nodes removed.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_AigCleanup( Abc_Aig_t * pMan )
{
    Abc_Obj_t * pAnd;
    int i, Counter;
    // collect the AND nodes that do not fanout
    assert( Vec_PtrSize( pMan->vStackDelete ) == 0 );
    for ( i = 0; i < pMan->nBins; i++ )
        Abc_AigBinForEachEntry( pMan->pBins[i], pAnd )
            if ( Abc_ObjFanoutNum(pAnd) == 0 )
                Vec_PtrPush( pMan->vStackDelete, pAnd );
    // process the dangling nodes and their MFFCs
    for ( Counter = 0; Vec_PtrSize(pMan->vStackDelete) > 0; Counter++ )
        Abc_AigDelete_int( pMan );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Makes sure that every node in the table is in the network and vice versa.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_AigCheck( Abc_Aig_t * pMan )
{
    Abc_Obj_t * pObj, * pAnd;
    int i, nFanins, Counter;
    Abc_NtkForEachNode( pMan->pNtkAig, pObj, i )
    {
        nFanins = Abc_ObjFaninNum(pObj);
        if ( nFanins == 0 )
        {
            if ( pObj != pMan->pConst1 && pObj != pMan->pReset )
            {
                printf( "Abc_AigCheck: The AIG has non-standard constant nodes.\n" );
                return 0;
            }
            continue;
        }
        if ( nFanins == 1 )
        {
            printf( "Abc_AigCheck: The AIG has single input nodes.\n" );
            return 0;
        }
        if ( nFanins > 2 )
        {
            printf( "Abc_AigCheck: The AIG has non-standard nodes.\n" );
            return 0;
        }
        if ( pObj->Level != 1 + ABC_MAX( Abc_ObjFanin0(pObj)->Level, Abc_ObjFanin1(pObj)->Level ) )
            printf( "Abc_AigCheck: Node \"%s\" has level that does not agree with the fanin levels.\n", Abc_ObjName(pObj) );
        pAnd = Abc_AigAndLookup( pMan, Abc_ObjChild0(pObj), Abc_ObjChild1(pObj) );
        if ( pAnd != pObj )
            printf( "Abc_AigCheck: Node \"%s\" is not in the structural hashing table.\n", Abc_ObjName(pObj) );
    }
    // count the number of nodes in the table
    Counter = 0;
    for ( i = 0; i < pMan->nBins; i++ )
        Abc_AigBinForEachEntry( pMan->pBins[i], pAnd )
            Counter++;
    if ( Counter != Abc_NtkNodeNum(pMan->pNtkAig) )
    {
        printf( "Abc_AigCheck: The number of nodes in the structural hashing table is wrong.\n" );
        return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Computes the number of logic levels not counting PIs/POs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_AigGetLevelNum( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    int i, LevelsMax;
    assert( Abc_NtkIsStrash(pNtk) );
    // perform the traversal
    LevelsMax = 0;
    Abc_NtkForEachCo( pNtk, pNode, i )
        if ( LevelsMax < (int)Abc_ObjFanin0(pNode)->Level )
            LevelsMax = (int)Abc_ObjFanin0(pNode)->Level;
    return LevelsMax;
}

/**Function*************************************************************

  Synopsis    [Read the constant 1 node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_AigConst1( Abc_Aig_t * pMan )  
{ 
    return pMan->pConst1; 
} 

/**Function*************************************************************

  Synopsis    [Read the reset node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_AigReset( Abc_Aig_t * pMan )  
{ 
    return pMan->pReset; 
} 



/**Function*************************************************************

  Synopsis    [Performs canonicization step.]

  Description [The argument nodes can be complemented.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_AigAndCreate( Abc_Aig_t * pMan, Abc_Obj_t * p0, Abc_Obj_t * p1 )
{
    Abc_Obj_t * pAnd;
    unsigned Key;
    // check if it is a good time for table resizing
    if ( pMan->nEntries > 2 * pMan->nBins )
        Abc_AigResize( pMan );
    // order the arguments
    if ( Abc_ObjRegular(p0)->Id > Abc_ObjRegular(p1)->Id )
        pAnd = p0, p0 = p1, p1 = pAnd;
    // create the new node
    pAnd = Abc_NtkCreateNode( pMan->pNtkAig );
    Abc_ObjAddFanin( pAnd, p0 );
    Abc_ObjAddFanin( pAnd, p1 );
    // set the level of the new node
    pAnd->Level      = 1 + ABC_MAX( Abc_ObjRegular(p0)->Level, Abc_ObjRegular(p1)->Level ); 
    pAnd->fExor      = Abc_NodeIsExorType(pAnd);
    pAnd->fPhase     = (Abc_ObjIsComplement(p0) ^ Abc_ObjRegular(p0)->fPhase) & (Abc_ObjIsComplement(p1) ^ Abc_ObjRegular(p1)->fPhase);
    // add the node to the corresponding linked list in the table
    Key = Abc_HashKey2( p0, p1, pMan->nBins );
    pAnd->pNext      = pMan->pBins[Key];
    pMan->pBins[Key] = pAnd;
    pMan->nEntries++;
    // create the cuts if defined
//    if ( pAnd->pNtk->pManCut )
//        Abc_NodeGetCuts( pAnd->pNtk->pManCut, pAnd );
    return pAnd;
}

/**Function*************************************************************

  Synopsis    [Performs canonicization step.]

  Description [The argument nodes can be complemented.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_AigAndCreateFrom( Abc_Aig_t * pMan, Abc_Obj_t * p0, Abc_Obj_t * p1, Abc_Obj_t * pAnd )
{
    Abc_Obj_t * pTemp;
    unsigned Key;
    assert( !Abc_ObjIsComplement(pAnd) );
    // order the arguments
    if ( Abc_ObjRegular(p0)->Id > Abc_ObjRegular(p1)->Id )
        pTemp = p0, p0 = p1, p1 = pTemp;
    // create the new node
    Abc_ObjAddFanin( pAnd, p0 );
    Abc_ObjAddFanin( pAnd, p1 );
    // set the level of the new node
    pAnd->Level      = 1 + ABC_MAX( Abc_ObjRegular(p0)->Level, Abc_ObjRegular(p1)->Level ); 
    pAnd->fExor      = Abc_NodeIsExorType(pAnd);
    // add the node to the corresponding linked list in the table
    Key = Abc_HashKey2( p0, p1, pMan->nBins );
    pAnd->pNext      = pMan->pBins[Key];
    pMan->pBins[Key] = pAnd;
    // create the cuts if defined
//    if ( pAnd->pNtk->pManCut )
//        Abc_NodeGetCuts( pAnd->pNtk->pManCut, pAnd );
    return pAnd;
}

/**Function*************************************************************

  Synopsis    [Performs canonicization step.]

  Description [The argument nodes can be complemented.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_AigAndLookup( Abc_Aig_t * pMan, Abc_Obj_t * p0, Abc_Obj_t * p1 )
{
    Abc_Obj_t * pAnd;
    unsigned Key;
    // check for trivial cases
    if ( p0 == p1 )
        return p0;
    if ( p0 == Abc_ObjNot(p1) )
        return Abc_ObjNot(pMan->pConst1);
    if ( Abc_ObjRegular(p0) == pMan->pConst1 )
    {
        if ( p0 == pMan->pConst1 )
            return p1;
        return Abc_ObjNot(pMan->pConst1);
    }
    if ( Abc_ObjRegular(p1) == pMan->pConst1 )
    {
        if ( p1 == pMan->pConst1 )
            return p0;
        return Abc_ObjNot(pMan->pConst1);
    }
    // order the arguments
    if ( Abc_ObjRegular(p0)->Id > Abc_ObjRegular(p1)->Id )
        pAnd = p0, p0 = p1, p1 = pAnd;
    // get the hash key for these two nodes
    Key = Abc_HashKey2( p0, p1, pMan->nBins );
    // find the matching node in the table
    Abc_AigBinForEachEntry( pMan->pBins[Key], pAnd )
        if ( p0 == Abc_ObjChild0(pAnd) && p1 == Abc_ObjChild1(pAnd) )
             return pAnd;
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Deletes an AIG node from the hash table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_AigAndDelete( Abc_Aig_t * pMan, Abc_Obj_t * pThis )
{
    Abc_Obj_t * pAnd, ** ppPlace;
    unsigned Key;
    assert( !Abc_ObjIsComplement(pThis) );
    assert( Abc_ObjIsNode(pThis) );
    assert( Abc_ObjFaninNum(pThis) == 2 );
    assert( pMan->pNtkAig == pThis->pNtk );
    // get the hash key for these two nodes
    Key = Abc_HashKey2( Abc_ObjChild0(pThis), Abc_ObjChild1(pThis), pMan->nBins );
    // find the matching node in the table
    ppPlace = pMan->pBins + Key;
    Abc_AigBinForEachEntry( pMan->pBins[Key], pAnd )
    {
        if ( pAnd != pThis )
        {
            ppPlace = &pAnd->pNext;
            continue;
        }
        *ppPlace = pAnd->pNext;
        break;
    }
    assert( pAnd == pThis );
    pMan->nEntries--;
    // delete the cuts if defined
    if ( pThis->pNtk->pManCut )
        Abc_NodeFreeCuts( pThis->pNtk->pManCut, pThis );
}

/**Function*************************************************************

  Synopsis    [Resizes the hash table of AIG nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_AigResize( Abc_Aig_t * pMan )
{
    Abc_Obj_t ** pBinsNew;
    Abc_Obj_t * pEnt, * pEnt2;
    int nBinsNew, Counter, i, clk;
    unsigned Key;

clk = clock();
    // get the new table size
    nBinsNew = Cudd_PrimeCopy( 3 * pMan->nBins ); 
    // allocate a new array
    pBinsNew = ALLOC( Abc_Obj_t *, nBinsNew );
    memset( pBinsNew, 0, sizeof(Abc_Obj_t *) * nBinsNew );
    // rehash the entries from the old table
    Counter = 0;
    for ( i = 0; i < pMan->nBins; i++ )
        Abc_AigBinForEachEntrySafe( pMan->pBins[i], pEnt, pEnt2 )
        {
            Key = Abc_HashKey2( Abc_ObjChild0(pEnt), Abc_ObjChild1(pEnt), nBinsNew );
            pEnt->pNext   = pBinsNew[Key];
            pBinsNew[Key] = pEnt;
            Counter++;
        }
    assert( Counter == pMan->nEntries );
//    printf( "Increasing the structural table size from %6d to %6d. ", pMan->nBins, nBinsNew );
//    PRT( "Time", clock() - clk );
    // replace the table and the parameters
    free( pMan->pBins );
    pMan->pBins = pBinsNew;
    pMan->nBins = nBinsNew;
}





/**Function*************************************************************

  Synopsis    [Performs canonicization step.]

  Description [The argument nodes can be complemented.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_AigAnd( Abc_Aig_t * pMan, Abc_Obj_t * p0, Abc_Obj_t * p1 )
{
    Abc_Obj_t * pAnd;
    if ( pAnd = Abc_AigAndLookup( pMan, p0, p1 ) )
        return pAnd;
    return Abc_AigAndCreate( pMan, p0, p1 );
}

/**Function*************************************************************

  Synopsis    [Implements Boolean OR.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_AigOr( Abc_Aig_t * pMan, Abc_Obj_t * p0, Abc_Obj_t * p1 )
{
    return Abc_ObjNot( Abc_AigAnd( pMan, Abc_ObjNot(p0), Abc_ObjNot(p1) ) );
}

/**Function*************************************************************

  Synopsis    [Implements Boolean XOR.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_AigXor( Abc_Aig_t * pMan, Abc_Obj_t * p0, Abc_Obj_t * p1 )
{
    return Abc_AigOr( pMan, Abc_AigAnd(pMan, p0, Abc_ObjNot(p1)), 
                            Abc_AigAnd(pMan, p1, Abc_ObjNot(p0)) );
}

/**Function*************************************************************

  Synopsis    [Implements the miter.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_AigMiter( Abc_Aig_t * pMan, Vec_Ptr_t * vPairs )
{
    Abc_Obj_t * pMiter, * pXor;
    int i;
    assert( vPairs->nSize % 2 == 0 );
    // go through the cubes of the node's SOP
    pMiter = Abc_ObjNot(pMan->pConst1);
    for ( i = 0; i < vPairs->nSize; i += 2 )
    {
        pXor   = Abc_AigXor( pMan, vPairs->pArray[i], vPairs->pArray[i+1] );
        pMiter = Abc_AigOr( pMan, pMiter, pXor );
    }
    return pMiter;
}




/**Function*************************************************************

  Synopsis    [Replaces one AIG node by the other.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_AigReplace( Abc_Aig_t * pMan, Abc_Obj_t * pOld, Abc_Obj_t * pNew )
{
    assert( Vec_PtrSize(pMan->vStackReplaceOld) == 0 );
    assert( Vec_PtrSize(pMan->vStackReplaceNew) == 0 );
    assert( Vec_PtrSize(pMan->vStackDelete)     == 0 );
    Vec_PtrPush( pMan->vStackReplaceOld, pOld );
    Vec_PtrPush( pMan->vStackReplaceNew, pNew );
    while ( Vec_PtrSize(pMan->vStackReplaceOld) )
        Abc_AigReplace_int( pMan );
    Abc_AigUpdateLevel_int( pMan );
    Abc_AigUpdateLevelR_int( pMan );
}

/**Function*************************************************************

  Synopsis    [Performs internal replacement step.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_AigReplace_int( Abc_Aig_t * pMan )
{
    Abc_Obj_t * pOld, * pNew, * pFanin1, * pFanin2, * pFanout, * pFanoutNew, * pFanoutFanout;
    int k, v, iFanin;
    // get the pair of nodes to replace
    assert( Vec_PtrSize(pMan->vStackReplaceOld) > 0 );
    pOld = Vec_PtrPop( pMan->vStackReplaceOld );
    pNew = Vec_PtrPop( pMan->vStackReplaceNew );
    // make sure the old node is regular and has fanouts
    // (the new node can be complemented and can have fanouts)
    assert( !Abc_ObjIsComplement(pOld) );
    assert( Abc_ObjFanoutNum(pOld) > 0 );
    // look at the fanouts of old node
    Abc_NodeCollectFanouts( pOld, pMan->vNodes );
    Vec_PtrForEachEntry( pMan->vNodes, pFanout, k )
    {
        if ( Abc_ObjIsCo(pFanout) )
        {
            Abc_ObjPatchFanin( pFanout, pOld, pNew );
            continue;
        }
        // find the old node as a fanin of this fanout
        iFanin = Vec_FanFindEntry( &pFanout->vFanins, pOld->Id );
        assert( iFanin == 0 || iFanin == 1 );
        // get the new fanin
        pFanin1 = Abc_ObjNotCond( pNew, Abc_ObjFaninC(pFanout, iFanin) );
        assert( Abc_ObjRegular(pFanin1) != pFanout );
        // get another fanin
        pFanin2 = Abc_ObjChild( pFanout, iFanin ^ 1 );
        assert( Abc_ObjRegular(pFanin2) != pFanout );
        // check if the node with these fanins exists
        if ( pFanoutNew = Abc_AigAndLookup( pMan, pFanin1, pFanin2 ) )
        { // such node exists (it may be a constant)
            // schedule replacement of the old fanout by the new fanout
            Vec_PtrPush( pMan->vStackReplaceOld, pFanout );
            Vec_PtrPush( pMan->vStackReplaceNew, pFanoutNew );
            continue;
        }
        // such node does not exist - modify the old fanout node 
        // (this way the change will not propagate all the way to the COs)
        assert( Abc_ObjRegular(pFanin1) != Abc_ObjRegular(pFanin2) );             

        // if the node is in the level structure, remove it
        if ( pFanout->fMarkA )
            Abc_AigRemoveFromLevelStructure( pMan->vLevels, pFanout );
        // if the node is in the level structure, remove it
        if ( pFanout->fMarkB )
            Abc_AigRemoveFromLevelStructureR( pMan->vLevelsR, pFanout );

        // remove the old fanout node from the structural hashing table
        Abc_AigAndDelete( pMan, pFanout );
        // remove the fanins of the old fanout
        Abc_ObjRemoveFanins( pFanout );
        // recreate the old fanout with new fanins and add it to the table
        Abc_AigAndCreateFrom( pMan, pFanin1, pFanin2, pFanout );
        assert( Abc_AigNodeIsAcyclic(pFanout, pFanout) );

        // schedule the updated fanout for updating direct level
        assert( pFanout->fMarkA == 0 );
        pFanout->fMarkA = 1;
        Vec_VecPush( pMan->vLevels, pFanout->Level, pFanout );
        // schedule the updated fanout for updating reverse level
        assert( pFanout->fMarkB == 0 );
        pFanout->fMarkB = 1;
        Vec_VecPush( pMan->vLevelsR, Abc_NodeReadReverseLevel(pFanout), pFanout );

        // the fanout has changed, update EXOR status of its fanouts
        Abc_ObjForEachFanout( pFanout, pFanoutFanout, v )
            if ( Abc_NodeIsAigAnd(pFanoutFanout) )
                pFanoutFanout->fExor = Abc_NodeIsExorType(pFanoutFanout);
    }
    // if the node has no fanouts left, remove its MFFC
    if ( Abc_ObjFanoutNum(pOld) == 0 )
        Abc_AigDeleteNode( pMan, pOld );
}

/**Function*************************************************************

  Synopsis    [Performs internal deletion step.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_AigDeleteNode( Abc_Aig_t * pMan, Abc_Obj_t * pOld )
{
    assert( Vec_PtrSize(pMan->vStackDelete) == 0 );
    Vec_PtrPush( pMan->vStackDelete, pOld );
    while ( Vec_PtrSize(pMan->vStackDelete) )
        Abc_AigDelete_int( pMan );
}

/**Function*************************************************************

  Synopsis    [Performs internal deletion step.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_AigDelete_int( Abc_Aig_t * pMan )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pRoot, * pObj;
    int k;
    // get the node to delete
    assert( Vec_PtrSize(pMan->vStackDelete) > 0 );
    pRoot = Vec_PtrPop( pMan->vStackDelete );

    // make sure the node is regular and dangling
    assert( !Abc_ObjIsComplement(pRoot) );
    assert( Abc_ObjIsNode(pRoot) );
    assert( Abc_ObjFaninNum(pRoot) == 2 );
    assert( Abc_ObjFanoutNum(pRoot) == 0 );

    // collect the MFFC
    vNodes = Abc_NodeMffcCollect( pRoot );

    // if reverse levels are specified, schedule fanins of MFFC for updating
    // currently, we do not do it because we do not know the correct level of the fanins
    // also, it is unlikely that this will make a difference since we are
    // processing the network forward while at this point fanins are left behind...
/*
    if ( pObj->pNtk->vLevelsR )
        Vec_PtrForEachEntry( vNodes, pObj, k )
        {
            Abc_Obj_t * pFanin;
            if ( Abc_ObjIsCi(pObj) )
                continue;
            pFanin = Abc_ObjFanin0(pObj);
            if ( pFanin->fMarkB == 0 )
            {
                pFanin->fMarkB = 1;
                Vec_VecPush( pMan->vLevelsR, Abc_NodeReadReverseLevel(pFanin), pFanin );
            }
            pFanin = Abc_ObjFanin1(pObj);
            if ( pFanin->fMarkB == 0 )
            {
                pFanin->fMarkB = 1;
                Vec_VecPush( pMan->vLevelsR, Abc_NodeReadReverseLevel(pFanin), pFanin );
            }
        }
*/

    // delete the nodes in MFFC
    Vec_PtrForEachEntry( vNodes, pObj, k )
    {
        if ( Abc_ObjIsCi(pObj) )
            continue;
        assert( Abc_ObjFanoutNum(pObj) == 0 );
        // remove the node from the table
        Abc_AigAndDelete( pMan, pObj );
        // if the node is in the level structure, remove it
        if ( pObj->fMarkA )
            Abc_AigRemoveFromLevelStructure( pMan->vLevels, pObj );
        if ( pObj->fMarkB )
            Abc_AigRemoveFromLevelStructureR( pMan->vLevelsR, pObj );
        // remove the node from the network
        Abc_NtkDeleteObj( pObj );
    }
    Vec_PtrFree( vNodes );
}

/**Function*************************************************************

  Synopsis    [Updates the level of the node after it has changed.]

  Description [This procedure is based on the observation that
  after the node's level has changed, the fanouts levels can change too, 
  but the new fanout levels are always larger than the node's level.
  As a result, we can accumulate the nodes to be updated in the queue
  and process them in the increasing order of levels.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_AigUpdateLevel_int( Abc_Aig_t * pMan )
{
    Abc_Obj_t * pNode, * pFanout;
    Vec_Ptr_t * vVec;
    int LevelNew, i, k, v;

    // go through the nodes and update the level of their fanouts
    Vec_VecForEachLevel( pMan->vLevels, vVec, i )
    {
        if ( Vec_PtrSize(vVec) == 0 )
            continue;
        Vec_PtrForEachEntry( vVec, pNode, k )
        {
            if ( pNode == NULL )
                continue;
            assert( Abc_ObjIsNode(pNode) );
            assert( (int)pNode->Level == i );
            // clean the mark
            assert( pNode->fMarkA == 1 );
            pNode->fMarkA = 0;
            // iterate through the fanouts
            Abc_ObjForEachFanout( pNode, pFanout, v )
            {
                if ( Abc_ObjIsCo(pFanout) )
                    continue;
                // get the new level of this fanout
                LevelNew = 1 + ABC_MAX( Abc_ObjFanin0(pFanout)->Level, Abc_ObjFanin1(pFanout)->Level );
                assert( LevelNew > i );
                if ( (int)pFanout->Level == LevelNew ) // no change
                    continue;
                // if the fanout is present in the data structure, pull it out
                if ( pFanout->fMarkA )
                    Abc_AigRemoveFromLevelStructure( pMan->vLevels, pFanout );
                // update the fanout level
                pFanout->Level = LevelNew;
                // add the fanout to the data structure to update its fanouts
                assert( pFanout->fMarkA == 0 );
                pFanout->fMarkA = 1;
                Vec_VecPush( pMan->vLevels, pFanout->Level, pFanout );
            }
        }
        Vec_PtrClear( vVec );
    }
}

/**Function*************************************************************

  Synopsis    [Updates the level of the node after it has changed.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_AigUpdateLevelR_int( Abc_Aig_t * pMan )
{
    Abc_Obj_t * pNode, * pFanin, * pFanout;
    Vec_Ptr_t * vVec;
    int LevelNew, i, k, v, j;

    // go through the nodes and update the level of their fanouts
    Vec_VecForEachLevel( pMan->vLevelsR, vVec, i )
    {
        if ( Vec_PtrSize(vVec) == 0 )
            continue;
        Vec_PtrForEachEntry( vVec, pNode, k )
        {
            if ( pNode == NULL )
                continue;
            assert( Abc_ObjIsNode(pNode) );
            assert( Abc_NodeReadReverseLevel(pNode) == i );
            // clean the mark
            assert( pNode->fMarkB == 1 );
            pNode->fMarkB = 0;
            // iterate through the fanins
            Abc_ObjForEachFanin( pNode, pFanin, v )
            {
                if ( Abc_ObjIsCi(pFanin) )
                    continue;
                // get the new reverse level of this fanin
                LevelNew = 0;
                Abc_ObjForEachFanout( pFanin, pFanout, j )
                    if ( LevelNew < Abc_NodeReadReverseLevel(pFanout) )
                        LevelNew = Abc_NodeReadReverseLevel(pFanout);
                LevelNew += 1;
                assert( LevelNew > i );
                if ( Abc_NodeReadReverseLevel(pFanin) == LevelNew ) // no change
                    continue;
                // if the fanin is present in the data structure, pull it out
                if ( pFanin->fMarkB )
                    Abc_AigRemoveFromLevelStructureR( pMan->vLevelsR, pFanin );
                // update the reverse level
                Abc_NodeSetReverseLevel( pFanin, LevelNew );
                // add the fanin to the data structure to update its fanins
                assert( pFanin->fMarkB == 0 );
                pFanin->fMarkB = 1;
                Vec_VecPush( pMan->vLevelsR, LevelNew, pFanin );
            }
        }
        Vec_PtrClear( vVec );
    }
}

/**Function*************************************************************

  Synopsis    [Removes the node from the level structure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_AigRemoveFromLevelStructure( Vec_Vec_t * vStruct, Abc_Obj_t * pNode )
{
    Vec_Ptr_t * vVecTemp;
    Abc_Obj_t * pTemp;
    int m;
    assert( pNode->fMarkA );
    vVecTemp = Vec_VecEntry( vStruct, pNode->Level );
    Vec_PtrForEachEntry( vVecTemp, pTemp, m )
    {
        if ( pTemp != pNode )
            continue;
        Vec_PtrWriteEntry( vVecTemp, m, NULL );
        break;
    }
    assert( m < Vec_PtrSize(vVecTemp) ); // found
    pNode->fMarkA = 0;
}

/**Function*************************************************************

  Synopsis    [Removes the node from the level structure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_AigRemoveFromLevelStructureR( Vec_Vec_t * vStruct, Abc_Obj_t * pNode )
{
    Vec_Ptr_t * vVecTemp;
    Abc_Obj_t * pTemp;
    int m;
    assert( pNode->fMarkB );
    vVecTemp = Vec_VecEntry( vStruct, Abc_NodeReadReverseLevel(pNode) );
    Vec_PtrForEachEntry( vVecTemp, pTemp, m )
    {
        if ( pTemp != pNode )
            continue;
        Vec_PtrWriteEntry( vVecTemp, m, NULL );
        break;
    }
    assert( m < Vec_PtrSize(vVecTemp) ); // found
    pNode->fMarkB = 0;
}




/**Function*************************************************************

  Synopsis    [Returns 1 if the node has at least one complemented fanout.]

  Description [A fanout is complemented if the fanout's fanin edge pointing
  to the given node is complemented.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_AigNodeHasComplFanoutEdge( Abc_Obj_t * pNode )
{
    Abc_Obj_t * pFanout;
    int i, iFanin;
    Abc_ObjForEachFanout( pNode, pFanout, i )
    {
        iFanin = Vec_FanFindEntry( &pFanout->vFanins, pNode->Id );
        assert( iFanin >= 0 );
        if ( Abc_ObjFaninC( pFanout, iFanin ) )
            return 1;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the node has at least one complemented fanout.]

  Description [A fanout is complemented if the fanout's fanin edge pointing
  to the given node is complemented. Only the fanouts with current TravId
  are counted.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_AigNodeHasComplFanoutEdgeTrav( Abc_Obj_t * pNode )
{
    Abc_Obj_t * pFanout;
    int i, iFanin;
    Abc_ObjForEachFanout( pNode, pFanout, i )
    {
        if ( !Abc_NodeIsTravIdCurrent(pFanout) )
            continue;
        iFanin = Vec_FanFindEntry( &pFanout->vFanins, pNode->Id );
        assert( iFanin >= 0 );
        if ( Abc_ObjFaninC( pFanout, iFanin ) )
            return 1;
    }
    return 0;
}


/**Function*************************************************************

  Synopsis    [Prints the AIG node for debugging purposes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_AigPrintNode( Abc_Obj_t * pNode )
{
    Abc_Obj_t * pNodeR = Abc_ObjRegular(pNode);
    if ( Abc_ObjIsCi(pNodeR) )
    {
        printf( "CI %4s%s.\n", Abc_ObjName(pNodeR), Abc_ObjIsComplement(pNode)? "\'" : "" );
        return;
    }
    if ( Abc_NodeIsConst(pNodeR) )
    {
        printf( "Constant 1 %s.\n", Abc_ObjIsComplement(pNode)? "(complemented)" : ""  );
        return;
    }
    // print the node's function
    printf( "%7s%s", Abc_ObjName(pNodeR),                Abc_ObjIsComplement(pNode)? "\'" : "" );
    printf( " = " );
    printf( "%7s%s", Abc_ObjName(Abc_ObjFanin0(pNodeR)), Abc_ObjFaninC0(pNodeR)?     "\'" : "" );
    printf( " * " );
    printf( "%7s%s", Abc_ObjName(Abc_ObjFanin1(pNodeR)), Abc_ObjFaninC1(pNodeR)?     "\'" : "" );
    printf( "\n" );
}


/**Function*************************************************************

  Synopsis    [Check if the node has a combination loop of depth 1 or 2.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_AigNodeIsAcyclic( Abc_Obj_t * pNode, Abc_Obj_t * pRoot )
{
    Abc_Obj_t * pFanin0, * pFanin1;
    Abc_Obj_t * pChild00, * pChild01;
    Abc_Obj_t * pChild10, * pChild11;
    if ( !Abc_NodeIsAigAnd(pNode) )
        return 1;
    pFanin0 = Abc_ObjFanin0(pNode);
    pFanin1 = Abc_ObjFanin1(pNode);
    if ( pRoot == pFanin0 || pRoot == pFanin1 )
        return 0;
    if ( Abc_ObjIsCi(pFanin0) )
    {
        pChild00 = NULL;
        pChild01 = NULL;
    }
    else
    {
        pChild00 = Abc_ObjFanin0(pFanin0);
        pChild01 = Abc_ObjFanin1(pFanin0);
        if ( pRoot == pChild00 || pRoot == pChild01 )
            return 0;
    }
    if ( Abc_ObjIsCi(pFanin1) )
    {
        pChild10 = NULL;
        pChild11 = NULL;
    }
    else
    {
        pChild10 = Abc_ObjFanin0(pFanin1);
        pChild11 = Abc_ObjFanin1(pFanin1);
        if ( pRoot == pChild10 || pRoot == pChild11 )
            return 0;
    }
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


