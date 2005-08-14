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

static stmm_table *   Abc_NtkFraigEquiv( Fraig_Man_t * p, Abc_Ntk_t * pNtk, int fUseInv, bool fVerbose );
static void           Abc_NtkFraigTransform( Abc_Ntk_t * pNtk, stmm_table * tEquiv, int fUseInv, bool fVerbose );
static void           Abc_NtkFraigMergeClassMapped( Abc_Ntk_t * pNtk, Abc_Obj_t * pChain, int fVerbose, int fUseInv );
static void           Abc_NtkFraigMergeClass( Abc_Ntk_t * pNtk, Abc_Obj_t * pChain, int fVerbose, int fUseInv );
static int            Abc_NodeDroppingCost( Abc_Obj_t * pNode );

extern Fraig_Man_t *  Abc_NtkToFraig( Abc_Ntk_t * pNtk, Fraig_Params_t * pParams, int fAllNodes );

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
    int fCheck = 1;
    Fraig_Params_t Params;
    Abc_Ntk_t * pNtkAig;
    Fraig_Man_t * pMan;
    stmm_table * tEquiv;

    assert( !Abc_NtkIsAig(pNtk) );

    // derive the AIG
    pNtkAig = Abc_NtkStrash( pNtk, 0 );
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
    if ( fCheck && !Abc_NtkCheck( pNtk ) )
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
    if ( Abc_NtkIsLogicMap( pNtk ) )
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
    int fCheck = 1;
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
    if ( Abc_NtkIsAig(pNtk) )
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
    if ( fCheck && !Abc_NtkCheck( pNtk ) )
    {
        printf( "Abc_NtkCleanup: The network check has failed.\n" );
        return -1;
    }
    return Counter;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


