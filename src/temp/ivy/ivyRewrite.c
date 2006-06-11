/**CFile****************************************************************

  FileName    [ivyRewrite.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    [AIG rewriting.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: ivyRewrite.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ivy.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static unsigned    Ivy_ManSeqFindTruth( Ivy_Obj_t * pNode, Vec_Int_t * vFront );
static void        Ivy_ManSeqCollectCone( Ivy_Obj_t * pNode, Vec_Int_t * vCone );
static int         Ivy_ManSeqGetCost( Ivy_Man_t * p, Vec_Int_t * vCone );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs Boolean rewriting of sequential AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_ManSeqRewrite( Ivy_Man_t * p, int fUpdateLevel, int fUseZeroCost )
{
    Vec_Int_t * vNodes, * vFront, * vInside, * vTree;
    Ivy_Obj_t * pNode, * pNodeNew, * pTemp;
    int i, k, nCostOld, nCostInt, nCostInt2, nCostNew, RetValue, Entry, nRefsSaved, nInputs;
    int clk, clkCut = 0, clkTru = 0, clkDsd = 0, clkUpd = 0, clkStart = clock();
    unsigned uTruth;

    nInputs  = 4;
    vTree    = Vec_IntAlloc( 8 );
    vFront   = Vec_IntAlloc( 8 );
    vInside  = Vec_IntAlloc( 50 );
    vNodes   = Ivy_ManDfs( p );
    Ivy_ManForEachNodeVec( p, vNodes, pNode, i )
    {
        if ( Ivy_ObjIsBuf(pNode) )
            continue;
        // fix the fanin buffer problem
        Ivy_NodeFixBufferFanins( pNode );
        if ( Ivy_ObjIsBuf(pNode) )
            continue;

        // find one sequential cut rooted at this node
clk = clock();
        Ivy_ManSeqFindCut( pNode, vFront, vInside, nInputs );
clkCut += clock() - clk;
        // compute the truth table of the cut
clk = clock();
        uTruth = Ivy_ManSeqFindTruth( pNode, vFront );
clkTru += clock() - clk;
        // decompose the truth table
clk = clock();
        RetValue = Ivy_TruthDsd( uTruth, vTree );
clkDsd += clock() - clk;
        if ( !RetValue )
            continue; // DSD does not exist
//        Ivy_TruthDsdPrint( stdout, vTree );

clk = clock();
        // remember the cost of the current network
        nCostOld = Ivy_ManGetCost(p);
        // increment references of the cut variables
        Vec_IntForEachEntry( vFront, Entry, k )
        {
            pTemp = Ivy_ManObj(p, Ivy_LeafId(Entry));
            Ivy_ObjRefsInc( pTemp );
        }
        // dereference and record undo
        nRefsSaved = pNode->nRefs; pNode->nRefs = 0;
        Ivy_ManUndoStart( p );
        Ivy_ObjDelete_rec( pNode, 0 );
        Ivy_ManUndoStop( p );
        pNode->nRefs = nRefsSaved;

        // get the intermediate cost
        nCostInt = Ivy_ManGetCost(p);

//        printf( "Removed by dereferencing = %d.\n", nCostOld - nCostInt );

        // construct the new logic cone
        pNodeNew = Ivy_ManDsdConstruct( p, vFront, vTree );
        // remember the cost
        nCostNew = Ivy_ManGetCost(p);

//        printf( "Added by dereferencing = %d.\n", nCostInt - nCostNew );
//        nCostNew = nCostNew;

/*
        if ( Ivy_Regular(pNodeNew)->nRefs == 0 )
            Ivy_ObjDelete_rec( Ivy_Regular(pNodeNew), 1 );
        // get the intermediate cost
        nCostInt2 = Ivy_ManGetCost(p);
        assert( nCostInt == nCostInt2 );

        Ivy_ManUndoPerform( p, pNode );
        pNode->nRefs = nRefsSaved;

        Vec_IntForEachEntry( vFront, Entry, k )
        {
//            pTemp = Ivy_ManObj(p, Ivy_LeafId(Entry));
            pTemp = Ivy_ManObj(p, Entry);
            Ivy_ObjRefsDec( pTemp );
        }
clkUpd += clock() - clk;
        continue;
*/

        // detect the case when they are exactly the same
//        if ( pNodeNew == pNode )
//            continue;

        // compare the costs
        if ( nCostOld > nCostNew || nCostOld == nCostNew && fUseZeroCost )
        { // accept the change
//            printf( "NODES GAINED = %d\n", nCostOld - nCostNew );

            Ivy_ObjReplace( pNode, pNodeNew, 0, 1 );
            pNode->nRefs = nRefsSaved;
        }
        else
        { // reject change
//            printf( "Rejected\n" );

            if ( Ivy_Regular(pNodeNew)->nRefs == 0 )
                Ivy_ObjDelete_rec( Ivy_Regular(pNodeNew), 1 );

            // get the intermediate cost
            nCostInt2 = Ivy_ManGetCost(p);
            assert( nCostInt == nCostInt2 );

            // reconstruct the old node
            Ivy_ManUndoPerform( p, pNode );
            pNode->nRefs = nRefsSaved;
        }
        // decrement references of the cut variables
        Vec_IntForEachEntry( vFront, Entry, k )
        {
//            pTemp = Ivy_ManObj(p, Ivy_LeafId(Entry));
            pTemp = Ivy_ManObj(p, Entry);
            if ( Ivy_ObjIsNone(pTemp) )
                continue;
            Ivy_ObjRefsDec( pTemp );
            if ( Ivy_ObjRefs(pTemp) == 0 )
                Ivy_ObjDelete_rec( pTemp, 1 );
        }

clkUpd += clock() - clk;
    }

PRT( "Cut    ", clkCut );
PRT( "Truth  ", clkTru );
PRT( "DSD    ", clkDsd );
PRT( "Update ", clkUpd );
PRT( "TOTAL  ", clock() - clkStart );

    Vec_IntFree( vTree  );
    Vec_IntFree( vFront );
    Vec_IntFree( vInside );
    Vec_IntFree( vNodes );

    if ( !Ivy_ManCheck(p) )
    {
        printf( "Ivy_ManSeqRewrite(): The check has failed.\n" );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Computes the truth table of the sequential cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned Ivy_ManSeqFindTruth_rec( Ivy_Man_t * p, unsigned Node, Vec_Int_t * vFront )
{
    static unsigned uMasks[5] = { 0xAAAAAAAA, 0xCCCCCCCC, 0xF0F0F0F0, 0xFF00FF00, 0xFFFF0000 };
    unsigned uTruth0, uTruth1;
    Ivy_Obj_t * pNode;
    int nLatches, Number;
    // consider the case of a constant
    if ( Node == 0 )
        return ~((unsigned)0);
    // try to find this node in the frontier
    Number = Vec_IntFind( vFront, Node );
    if ( Number >= 0 )
        return uMasks[Number];
    // get the node
    pNode = Ivy_ManObj( p, Ivy_LeafId(Node) );
    assert( !Ivy_ObjIsPi(pNode) && !Ivy_ObjIsConst1(pNode) );
    // get the number of latches
    nLatches = Ivy_LeafLat(Node) + Ivy_ObjIsLatch(pNode);
    // expand the first fanin
    uTruth0 = Ivy_ManSeqFindTruth_rec( p, Ivy_LeafCreate(Ivy_ObjFaninId0(pNode), nLatches), vFront );
    if ( Ivy_ObjFaninC0(pNode) )
        uTruth0 = ~uTruth0;
    // quit if this is the one fanin node
    if ( Ivy_ObjIsLatch(pNode) || Ivy_ObjIsBuf(pNode) )
        return uTruth0;
    assert( Ivy_ObjIsNode(pNode) );
    // expand the second fanin
    uTruth1 = Ivy_ManSeqFindTruth_rec( p, Ivy_LeafCreate(Ivy_ObjFaninId1(pNode), nLatches), vFront );
    if ( Ivy_ObjFaninC1(pNode) )
        uTruth1 = ~uTruth1;
    // return the truth table
    return Ivy_ObjIsAnd(pNode)? uTruth0 & uTruth1 : uTruth0 ^ uTruth1;
}

/**Function*************************************************************

  Synopsis    [Computes the truth table of the sequential cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned Ivy_ManSeqFindTruth( Ivy_Obj_t * pNode, Vec_Int_t * vFront )
{
    assert( Ivy_ObjIsNode(pNode) );
    return Ivy_ManSeqFindTruth_rec( Ivy_ObjMan(pNode), Ivy_LeafCreate(pNode->Id, 0), vFront );
}


/**Function*************************************************************

  Synopsis    [Recursively dereferences the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManSeqDeref_rec( Ivy_Obj_t * pNode, Vec_Int_t * vCone )
{
    Ivy_Obj_t * pFan;
    assert( !Ivy_IsComplement(pNode) );
    assert( !Ivy_ObjIsNone(pNode) );
    if ( Ivy_ObjIsPi(pNode) )
        return;
    // deref the first fanin
    pFan = Ivy_ObjFanin0(pNode);
    Ivy_ObjRefsDec( pFan );
    if ( Ivy_ObjRefs( pFan ) == 0 )
        Ivy_ManSeqDeref_rec( pFan, vCone );
    // deref the second fanin
    pFan = Ivy_ObjFanin1(pNode);
    Ivy_ObjRefsDec( pFan );
    if ( Ivy_ObjRefs( pFan ) == 0 )
        Ivy_ManSeqDeref_rec( pFan, vCone );
    // save the node
    Vec_IntPush( vCone, pNode->Id );
}

/**Function*************************************************************

  Synopsis    [Recursively references the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManSeqRef_rec( Ivy_Obj_t * pNode )
{
    Ivy_Obj_t * pFan;
    assert( !Ivy_IsComplement(pNode) );
    assert( !Ivy_ObjIsNone(pNode) );
    if ( Ivy_ObjIsPi(pNode) )
        return;
    // ref the first fanin
    pFan = Ivy_ObjFanin0(pNode);
    if ( Ivy_ObjRefs( pFan ) == 0 )
        Ivy_ManSeqRef_rec( pFan );
    Ivy_ObjRefsInc( pFan );
    // ref the second fanin
    pFan = Ivy_ObjFanin1(pNode);
    if ( Ivy_ObjRefs( pFan ) == 0 )
        Ivy_ManSeqRef_rec( pFan );
    Ivy_ObjRefsInc( pFan );
}

/**Function*************************************************************

  Synopsis    [Collect MFFC of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManSeqCollectCone( Ivy_Obj_t * pNode, Vec_Int_t * vCone )
{
    Vec_IntClear( vCone );
    Ivy_ManSeqDeref_rec( pNode, vCone );
    Ivy_ManSeqRef_rec( pNode );
}

/**Function*************************************************************

  Synopsis    [Computes the cost of the logic cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_ManSeqGetCost( Ivy_Man_t * p, Vec_Int_t * vCone )
{
    Ivy_Obj_t * pObj;
    int i, Cost = 0;
    Ivy_ManForEachNodeVec( p, vCone, pObj, i )
    {
        if ( Ivy_ObjIsAnd(pObj) )
            Cost += 1;
        else if ( Ivy_ObjIsExor(pObj) )
            Cost += 2;
    }
    return 0;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


