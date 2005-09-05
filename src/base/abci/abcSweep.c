/**CFile****************************************************************

  FileName    [abcDsd.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Technology dependent sweep.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcDsd.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "fraig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern Fraig_Man_t *  Abc_NtkToFraig( Abc_Ntk_t * pNtk, Fraig_Params_t * pParams, int fAllNodes );

static stmm_table *   Abc_NtkFraigEquiv( Fraig_Man_t * p, Abc_Ntk_t * pNtk, int fUseInv, bool fVerbose );
static void           Abc_NtkFraigTransform( Abc_Ntk_t * pNtk, stmm_table * tEquiv, int fUseInv, bool fVerbose );
static void           Abc_NtkFraigMergeClassMapped( Abc_Ntk_t * pNtk, Abc_Obj_t * pChain, int fVerbose, int fUseInv );
static void           Abc_NtkFraigMergeClass( Abc_Ntk_t * pNtk, Abc_Obj_t * pChain, int fVerbose, int fUseInv );
static int            Abc_NodeDroppingCost( Abc_Obj_t * pNode );

static void           Abc_NodeSweep( Abc_Obj_t * pNode, int fVerbose );
static void           Abc_NodeConstantInput( Abc_Obj_t * pNode, Abc_Obj_t * pFanin, bool fConst0 );
static void           Abc_NodeComplementInput( Abc_Obj_t * pNode, Abc_Obj_t * pFanin );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Sweping functionally equivalence nodes.]

  Description [Removes gates with equivalent functionality. Works for 
  both technology-independent and mapped networks. If the flag is set, 
  allows adding inverters at the gate outputs.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkFraigSweep( Abc_Ntk_t * pNtk, int fUseInv, int fVerbose )
{
    Fraig_Params_t Params;
    Abc_Ntk_t * pNtkAig;
    Fraig_Man_t * pMan;
    stmm_table * tEquiv;

    assert( !Abc_NtkIsStrash(pNtk) );

    // derive the AIG
    pNtkAig = Abc_NtkStrash( pNtk, 0, 1 );
    // perform fraiging of the AIG
    Fraig_ParamsSetDefault( &Params );
    pMan = Abc_NtkToFraig( pNtkAig, &Params, 0 );    
    // collect the classes of equivalent nets
    tEquiv = Abc_NtkFraigEquiv( pMan, pNtk, fUseInv, fVerbose );

    // transform the network into the equivalent one
    Abc_NtkFraigTransform( pNtk, tEquiv, fUseInv, fVerbose );
    stmm_free_table( tEquiv );

    // free the manager
    Fraig_ManFree( pMan );
    Abc_NtkDelete( pNtkAig );

    // cleanup the dangling nodes
    Abc_NtkCleanup( pNtk, fVerbose );
    // check
    if ( !Abc_NtkCheck( pNtk ) )
    {
        printf( "Abc_NtkFraigSweep: The network check has failed.\n" );
        return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Collects equivalence classses of node in the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
stmm_table * Abc_NtkFraigEquiv( Fraig_Man_t * p, Abc_Ntk_t * pNtk, int fUseInv, bool fVerbose )
{
    Abc_Obj_t * pList, * pNode, * pNodeAig;
    Fraig_Node_t * gNode;
    Abc_Obj_t ** ppSlot;
    stmm_table * tStrash2Net;
    stmm_table * tResult;
    stmm_generator * gen;
    int c, Counter;

    // create mapping of strashed nodes into the corresponding network nodes
    tStrash2Net = stmm_init_table(stmm_ptrcmp,stmm_ptrhash);
    Abc_NtkForEachNode( pNtk, pNode, c )
    {
        // get the strashed node
        pNodeAig = pNode->pCopy;
        // skip the dangling nodes
        if ( pNodeAig == NULL )
            continue;
        // skip the constant input nodes
        if ( Abc_ObjFaninNum(pNode) == 0 )
            continue;
        // skip the nodes that fanout into POs
        if ( Abc_NodeHasUniqueCoFanout(pNode) )
            continue;
        // get the FRAIG node
        gNode = Fraig_NotCond( Abc_ObjRegular(pNodeAig)->pCopy, Abc_ObjIsComplement(pNodeAig) );
        if ( !stmm_find_or_add( tStrash2Net, (char *)Fraig_Regular(gNode), (char ***)&ppSlot ) )
            *ppSlot = NULL;
        // add the node to the list
        pNode->pNext = *ppSlot;
        *ppSlot = pNode;
        // mark the node if it is complemented
        pNode->fPhase = Fraig_IsComplement(gNode);
    }

    // print the classes
    c = 0;
    Counter = 0;
    tResult = stmm_init_table(stmm_ptrcmp,stmm_ptrhash);
    stmm_foreach_item( tStrash2Net, gen, (char **)&gNode, (char **)&pList )
    {
        // skip the trival classes
        if ( pList == NULL || pList->pNext == NULL )
            continue;
        // add the non-trival class
        stmm_insert( tResult, (char *)pList, NULL );
        // count nodes in the non-trival classes
        for ( pNode = pList; pNode; pNode = pNode->pNext )
            Counter++;
/*
        if ( fVerbose )
        {
            printf( "Class %2d : {", c );
            for ( pNode = pList; pNode; pNode = pNode->pNext )
            {
                pNode->pCopy = NULL;
                printf( " %s", Abc_ObjName(pNode) );
                if ( pNode->fPhase )  printf( "(*)" );
            }
            printf( " }\n" );
            c++;
        }
*/
    }
    if ( fVerbose )
    {
        printf( "Sweeping stats for network \"%s\":\n", pNtk->pName );
        printf( "Internal nodes = %d. Different functions (up to compl) = %d.\n", Abc_NtkNodeNum(pNtk), stmm_count(tStrash2Net) );
        printf( "Non-trivial classes = %d. Nodes in non-trivial classes = %d.\n", stmm_count(tResult), Counter );
    }
    stmm_free_table( tStrash2Net );
    return tResult;
}


/**Function*************************************************************

  Synopsis    [Transforms the network using the equivalence relation on nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkFraigTransform( Abc_Ntk_t * pNtk, stmm_table * tEquiv, int fUseInv, bool fVerbose )
{
    stmm_generator * gen;
    Abc_Obj_t * pList;
    if ( stmm_count(tEquiv) == 0 )
        return;
    // assign levels to the nodes of the network
    Abc_NtkGetLevelNum( pNtk );
    // merge nodes in the classes
    if ( Abc_NtkHasMapping( pNtk ) )
    {
        Abc_NtkDelayTrace( pNtk );
        stmm_foreach_item( tEquiv, gen, (char **)&pList, NULL )
            Abc_NtkFraigMergeClassMapped( pNtk, pList, fUseInv, fVerbose );
    }
    else 
    {
        stmm_foreach_item( tEquiv, gen, (char **)&pList, NULL )
            Abc_NtkFraigMergeClass( pNtk, pList, fUseInv, fVerbose );
    }
}


/**Function*************************************************************

  Synopsis    [Transforms the list of one-phase equivalent nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkFraigMergeClassMapped( Abc_Ntk_t * pNtk, Abc_Obj_t * pChain, int fUseInv, int fVerbose )
{
    Abc_Obj_t * pListDir, * pListInv;
    Abc_Obj_t * pNodeMin, * pNode, * pNext;
    float Arrival1, Arrival2;

    assert( pChain );
    assert( pChain->pNext );

    // divide the nodes into two parts: 
    // those that need the invertor and those that don't need
    pListDir = pListInv = NULL;
    for ( pNode = pChain, pNext = pChain->pNext; 
          pNode; 
          pNode = pNext, pNext = pNode? pNode->pNext : NULL )
    {
        // check to which class the node belongs
        if ( pNode->fPhase == 1 )
        {
            pNode->pNext = pListDir;
            pListDir = pNode;
        }
        else
        {
            pNode->pNext = pListInv;
            pListInv = pNode;
        }
    }

    // find the node with the smallest number of logic levels
    pNodeMin = pListDir;
    for ( pNode = pListDir; pNode; pNode = pNode->pNext )
    {
        Arrival1 = Abc_NodeReadArrival(pNodeMin)->Worst;
        Arrival2 = Abc_NodeReadArrival(pNode   )->Worst;
        assert( Abc_ObjIsCi(pNodeMin) || Arrival1 > 0 );
        assert( Abc_ObjIsCi(pNode)    || Arrival2 > 0 );
        if (  Arrival1 > Arrival2 ||
              Arrival1 == Arrival2 && pNodeMin->Level >  pNode->Level || 
              Arrival1 == Arrival2 && pNodeMin->Level == pNode->Level && 
              Abc_NodeDroppingCost(pNodeMin) < Abc_NodeDroppingCost(pNode)  )
            pNodeMin = pNode;
    }

    // move the fanouts of the direct nodes
    for ( pNode = pListDir; pNode; pNode = pNode->pNext )
        if ( pNode != pNodeMin )
            Abc_ObjTransferFanout( pNode, pNodeMin );

    // find the node with the smallest number of logic levels
    pNodeMin = pListInv;
    for ( pNode = pListInv; pNode; pNode = pNode->pNext )
    {
        Arrival1 = Abc_NodeReadArrival(pNodeMin)->Worst;
        Arrival2 = Abc_NodeReadArrival(pNode   )->Worst;
        assert( Abc_ObjIsCi(pNodeMin) || Arrival1 > 0 );
        assert( Abc_ObjIsCi(pNode)    || Arrival2 > 0 );
        if (  Arrival1 > Arrival2 ||
              Arrival1 == Arrival2 && pNodeMin->Level >  pNode->Level || 
              Arrival1 == Arrival2 && pNodeMin->Level == pNode->Level && 
              Abc_NodeDroppingCost(pNodeMin) < Abc_NodeDroppingCost(pNode)  )
            pNodeMin = pNode;
    }

    // move the fanouts of the direct nodes
    for ( pNode = pListInv; pNode; pNode = pNode->pNext )
        if ( pNode != pNodeMin )
            Abc_ObjTransferFanout( pNode, pNodeMin );
}

/**Function*************************************************************

  Synopsis    [Process one equivalence class of nodes.]

  Description [This function does not remove the nodes. It only switches 
  around the connections.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkFraigMergeClass( Abc_Ntk_t * pNtk, Abc_Obj_t * pChain, int fUseInv, int fVerbose )
{
    Abc_Obj_t * pListDir, * pListInv;
    Abc_Obj_t * pNodeMin, * pNodeMinInv;
    Abc_Obj_t * pNode, * pNext;

    assert( pChain );
    assert( pChain->pNext );

    // find the node with the smallest number of logic levels
    pNodeMin = pChain;
    for ( pNode = pChain->pNext; pNode; pNode = pNode->pNext )
        if (  pNodeMin->Level >  pNode->Level || 
            ( pNodeMin->Level == pNode->Level && 
              Abc_NodeDroppingCost(pNodeMin) < Abc_NodeDroppingCost(pNode) ) )
            pNodeMin = pNode;

    // divide the nodes into two parts: 
    // those that need the invertor and those that don't need
    pListDir = pListInv = NULL;
    for ( pNode = pChain, pNext = pChain->pNext; 
          pNode; 
          pNode = pNext, pNext = pNode? pNode->pNext : NULL )
    {
        if ( pNode == pNodeMin )
            continue;
        // check to which class the node belongs
        if ( pNodeMin->fPhase == pNode->fPhase )
        {
            pNode->pNext = pListDir;
            pListDir = pNode;
        }
        else
        {
            pNode->pNext = pListInv;
            pListInv = pNode;
        }
    }

    // move the fanouts of the direct nodes
    for ( pNode = pListDir; pNode; pNode = pNode->pNext )
        Abc_ObjTransferFanout( pNode, pNodeMin );

    // skip if there are no inverted nodes
    if ( pListInv == NULL )
        return;

    // add the invertor
    pNodeMinInv = Abc_NodeCreateInv( pNtk, pNodeMin );
   
    // move the fanouts of the inverted nodes
    for ( pNode = pListInv; pNode; pNode = pNode->pNext )
        Abc_ObjTransferFanout( pNode, pNodeMinInv );
}


/**Function*************************************************************

  Synopsis    [Returns the number of literals saved if this node becomes useless.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeDroppingCost( Abc_Obj_t * pNode )
{ 
    return 1;
}





/**Function*************************************************************

  Synopsis    [Removes dangling nodes.]

  Description [Returns the number of nodes removed.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkCleanup( Abc_Ntk_t * pNtk, int fVerbose )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pNode;
    int i, Counter;
    // mark the nodes reachable from the POs
    vNodes = Abc_NtkDfs( pNtk, 0 );
    for ( i = 0; i < vNodes->nSize; i++ )
    {
        pNode = vNodes->pArray[i];
        pNode->fMarkA = 1;
    }
    Vec_PtrFree( vNodes );
    // if it is an AIG, also mark the constant 1 node
    if ( Abc_NtkIsStrash(pNtk) )
        Abc_AigConst1(pNtk->pManFunc)->fMarkA = 1;
    // remove the non-marked nodes
    Counter = 0;
    Abc_NtkForEachNode( pNtk, pNode, i )
        if ( pNode->fMarkA == 0 )
        {
            Abc_NtkDeleteObj( pNode );
            Counter++;
        }
    // unmark the remaining nodes
    Abc_NtkForEachNode( pNtk, pNode, i )
        pNode->fMarkA = 0;
    if ( fVerbose )
        printf( "Cleanup removed %d dangling nodes.\n", Counter );
    // check
    if ( !Abc_NtkCheck( pNtk ) )
    {
        printf( "Abc_NtkCleanup: The network check has failed.\n" );
        return -1;
    }
    return Counter;
}




/**Function*************************************************************

  Synopsis    [Tranditional sweep of the network.]

  Description [Propagates constant and single-input node, removes dangling nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkSweep( Abc_Ntk_t * pNtk, int fVerbose )
{
    Abc_Obj_t * pNode;
    int i, fConvert, nSwept, nSweptNew;
    assert( Abc_NtkIsSopLogic(pNtk) || Abc_NtkIsBddLogic(pNtk) ); 
    // convert to the BDD representation
    fConvert = 0;
    if ( Abc_NtkIsSopLogic(pNtk) )
        Abc_NtkSopToBdd(pNtk), fConvert = 1;
    // perform cleanup to get rid of dangling nodes
    nSwept = Abc_NtkCleanup( pNtk, 0 );
    // make the network minimum base
    Abc_NtkRemoveDupFanins(pNtk);
    Abc_NtkMinimumBase(pNtk);
    do
    {
        // sweep constants and single-input nodes
        Abc_NtkForEachNode( pNtk, pNode, i )
            if ( Abc_ObjFaninNum(pNode) < 2 )
                Abc_NodeSweep( pNode, fVerbose );
        // make the network minimum base
        Abc_NtkRemoveDupFanins(pNtk);
        Abc_NtkMinimumBase(pNtk);
        // perform final clean up (in case new danglies are created)
        nSweptNew = Abc_NtkCleanup( pNtk, 0 );
        nSwept += nSweptNew;
    }
    while ( nSweptNew );
    // conver back to BDD
    if ( fConvert )
        Abc_NtkBddToSop(pNtk);
    // report
    if ( fVerbose )
        printf( "Sweep removed %d nodes.\n", nSwept );
    // check
    if ( !Abc_NtkCheck( pNtk ) )
    {
        printf( "Abc_NtkSweep: The network check has failed.\n" );
        return -1;
    }
    return nSwept;
}

/**Function*************************************************************

  Synopsis    [Tranditional sweep of the network.]

  Description [Propagates constant and single-input node, removes dangling nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeSweep( Abc_Obj_t * pNode, int fVerbose )
{
    Vec_Ptr_t * vFanout = pNode->pNtk->vPtrTemp;
    Abc_Obj_t * pFanout, * pDriver;
    int i;
    assert( Abc_ObjFaninNum(pNode) < 2 );
    assert( Abc_ObjFanoutNum(pNode) > 0 );
    // iterate through the fanouts
    Abc_NodeCollectFanouts( pNode, vFanout );
    Vec_PtrForEachEntry( vFanout, pFanout, i )
    {
        if ( Abc_ObjIsCo(pFanout) )
        {
            if ( Abc_ObjFaninNum(pNode) == 1 )
            {
                pDriver = Abc_ObjFanin0(pNode);
                if ( Abc_ObjIsCi(pDriver) || Abc_ObjFanoutNum(pDriver) > 1 || Abc_ObjFanoutNum(pNode) > 1 )
                    continue;
                // the driver is a node and its only fanout is this node
                if ( Abc_NodeIsInv(pNode) )
                    pDriver->pData = Cudd_Not(pDriver->pData);
                // replace the fanin of the fanout
                Abc_ObjPatchFanin( pFanout, pNode, pDriver );
            }
            continue;
        }
        // the fanout is a regular node
        if ( Abc_ObjFaninNum(pNode) == 0 )
            Abc_NodeConstantInput( pFanout, pNode, Abc_NodeIsConst0(pNode) );
        else 
        {
            assert( Abc_ObjFaninNum(pNode) == 1 );
            pDriver = Abc_ObjFanin0(pNode);
            if ( Abc_NodeIsInv(pNode) )
                Abc_NodeComplementInput( pFanout, pNode );
            Abc_ObjPatchFanin( pFanout, pNode, pDriver );
        }
    }
}

/**Function*************************************************************

  Synopsis    [Replaces the local function by its cofactor.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeConstantInput( Abc_Obj_t * pNode, Abc_Obj_t * pFanin, bool fConst0 )
{
    DdManager * dd = pNode->pNtk->pManFunc;
    DdNode * bVar, * bTemp;
    int iFanin;
    assert( Abc_NtkIsBddLogic(pNode->pNtk) ); 
    if ( (iFanin = Vec_FanFindEntry( &pNode->vFanins, pFanin->Id )) == -1 )
    {
        printf( "Node %s should be among", Abc_ObjName(pFanin) );
        printf( " the fanins of node %s...\n", Abc_ObjName(pNode) );
        return;
    }
    bVar = Cudd_NotCond( Cudd_bddIthVar(dd, iFanin), fConst0 );
    pNode->pData = Cudd_Cofactor( dd, bTemp = pNode->pData, bVar );   Cudd_Ref( pNode->pData );
    Cudd_RecursiveDeref( dd, bTemp );
}

/**Function*************************************************************

  Synopsis    [Changes the polarity of one fanin.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeComplementInput( Abc_Obj_t * pNode, Abc_Obj_t * pFanin )
{
    DdManager * dd = pNode->pNtk->pManFunc;
    DdNode * bVar, * bCof0, * bCof1;
    int iFanin;
    assert( Abc_NtkIsBddLogic(pNode->pNtk) ); 
    if ( (iFanin = Vec_FanFindEntry( &pNode->vFanins, pFanin->Id )) == -1 )
    {
        printf( "Node %s should be among", Abc_ObjName(pFanin) );
        printf( " the fanins of node %s...\n", Abc_ObjName(pNode) );
        return;
    }
    bVar = Cudd_bddIthVar( dd, iFanin );
    bCof0 = Cudd_Cofactor( dd, pNode->pData, Cudd_Not(bVar) );   Cudd_Ref( bCof0 );
    bCof1 = Cudd_Cofactor( dd, pNode->pData, bVar );             Cudd_Ref( bCof1 );
    Cudd_RecursiveDeref( dd, pNode->pData );
    pNode->pData = Cudd_bddIte( dd, bVar, bCof0, bCof1 );        Cudd_Ref( pNode->pData );
    Cudd_RecursiveDeref( dd, bCof0 );
    Cudd_RecursiveDeref( dd, bCof1 );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


