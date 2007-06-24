/**CFile****************************************************************

  FileName    [darTruth.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting.]

  Synopsis    [Computes the truth table of a cut.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: darTruth.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "dar.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computes truth table of the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ManCollectCut_rec( Dar_Man_t * p, Dar_Obj_t * pNode, Vec_Int_t * vNodes )
{
    if ( pNode->fMarkA )
        return;
    pNode->fMarkA = 1;
    assert( Dar_ObjIsAnd(pNode) || Dar_ObjIsExor(pNode) );
    Dar_ManCollectCut_rec( p, Dar_ObjFanin0(pNode), vNodes );
    Dar_ManCollectCut_rec( p, Dar_ObjFanin1(pNode), vNodes );
    Vec_IntPush( vNodes, pNode->Id );
}

/**Function*************************************************************

  Synopsis    [Computes truth table of the cut.]

  Description [Does not modify the array of leaves. Uses array vTruth to store 
  temporary truth tables. The returned pointer should be used immediately.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ManCollectCut( Dar_Man_t * p, Dar_Obj_t * pRoot, Vec_Int_t * vLeaves, Vec_Int_t * vNodes )
{
    int i, Leaf;
    // collect and mark the leaves
    Vec_IntClear( vNodes );
    Vec_IntForEachEntry( vLeaves, Leaf, i )
    {
        Vec_IntPush( vNodes, Leaf );
        Dar_ManObj(p, Leaf)->fMarkA = 1;
    }
    // collect and mark the nodes
    Dar_ManCollectCut_rec( p, pRoot, vNodes );
    // clean the nodes
    Vec_IntForEachEntry( vNodes, Leaf, i )
        Dar_ManObj(p, Leaf)->fMarkA = 0;
}

/**Function*************************************************************

  Synopsis    [Returns the pointer to the truth table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned * Dar_ObjGetTruthStore( int ObjNum, Vec_Int_t * vTruth )
{
   return ((unsigned *)Vec_IntArray(vTruth)) + 8 * ObjNum;
}

/**Function*************************************************************

  Synopsis    [Computes truth table of the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ManCutTruthOne( Dar_Man_t * p, Dar_Obj_t * pNode, Vec_Int_t * vTruth, int nWords )
{
    unsigned * pTruth, * pTruth0, * pTruth1;
    int i;
    pTruth  = Dar_ObjGetTruthStore( pNode->Level, vTruth );
    pTruth0 = Dar_ObjGetTruthStore( Dar_ObjFanin0(pNode)->Level, vTruth );
    pTruth1 = Dar_ObjGetTruthStore( Dar_ObjFanin1(pNode)->Level, vTruth );
    if ( Dar_ObjIsExor(pNode) )
        for ( i = 0; i < nWords; i++ )
            pTruth[i] = pTruth0[i] ^ pTruth1[i];
    else if ( !Dar_ObjFaninC0(pNode) && !Dar_ObjFaninC1(pNode) )
        for ( i = 0; i < nWords; i++ )
            pTruth[i] = pTruth0[i] & pTruth1[i];
    else if ( !Dar_ObjFaninC0(pNode) && Dar_ObjFaninC1(pNode) )
        for ( i = 0; i < nWords; i++ )
            pTruth[i] = pTruth0[i] & ~pTruth1[i];
    else if ( Dar_ObjFaninC0(pNode) && !Dar_ObjFaninC1(pNode) )
        for ( i = 0; i < nWords; i++ )
            pTruth[i] = ~pTruth0[i] & pTruth1[i];
    else // if ( Dar_ObjFaninC0(pNode) && Dar_ObjFaninC1(pNode) )
        for ( i = 0; i < nWords; i++ )
            pTruth[i] = ~pTruth0[i] & ~pTruth1[i];
}

/**Function*************************************************************

  Synopsis    [Computes truth table of the cut.]

  Description [Does not modify the array of leaves. Uses array vTruth to store 
  temporary truth tables. The returned pointer should be used immediately.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned * Dar_ManCutTruth( Dar_Man_t * p, Dar_Obj_t * pRoot, Vec_Int_t * vLeaves, Vec_Int_t * vNodes, Vec_Int_t * vTruth )
{
    static unsigned uTruths[8][8] = { // elementary truth tables
        { 0xAAAAAAAA,0xAAAAAAAA,0xAAAAAAAA,0xAAAAAAAA,0xAAAAAAAA,0xAAAAAAAA,0xAAAAAAAA,0xAAAAAAAA },
        { 0xCCCCCCCC,0xCCCCCCCC,0xCCCCCCCC,0xCCCCCCCC,0xCCCCCCCC,0xCCCCCCCC,0xCCCCCCCC,0xCCCCCCCC },
        { 0xF0F0F0F0,0xF0F0F0F0,0xF0F0F0F0,0xF0F0F0F0,0xF0F0F0F0,0xF0F0F0F0,0xF0F0F0F0,0xF0F0F0F0 },
        { 0xFF00FF00,0xFF00FF00,0xFF00FF00,0xFF00FF00,0xFF00FF00,0xFF00FF00,0xFF00FF00,0xFF00FF00 },
        { 0xFFFF0000,0xFFFF0000,0xFFFF0000,0xFFFF0000,0xFFFF0000,0xFFFF0000,0xFFFF0000,0xFFFF0000 }, 
        { 0x00000000,0xFFFFFFFF,0x00000000,0xFFFFFFFF,0x00000000,0xFFFFFFFF,0x00000000,0xFFFFFFFF }, 
        { 0x00000000,0x00000000,0xFFFFFFFF,0xFFFFFFFF,0x00000000,0x00000000,0xFFFFFFFF,0xFFFFFFFF }, 
        { 0x00000000,0x00000000,0x00000000,0x00000000,0xFFFFFFFF,0xFFFFFFFF,0xFFFFFFFF,0xFFFFFFFF } 
    };
    int i, Leaf;
    // collect the cut
//    Dar_ManCollectCut( p, pRoot, vLeaves, vNodes );
    // set the node numbers
    Vec_IntForEachEntry( vNodes, Leaf, i )
        Dar_ManObj(p, Leaf)->Level = i;
    // alloc enough memory
    Vec_IntClear( vTruth );
    Vec_IntGrow( vTruth, 8 * Vec_IntSize(vNodes) );
    // set the elementary truth tables
    Vec_IntForEachEntry( vLeaves, Leaf, i )
        memcpy( Dar_ObjGetTruthStore(i, vTruth), uTruths[i], 8 * sizeof(unsigned) );
    // compute truths for other nodes
    Vec_IntForEachEntryStart( vNodes, Leaf, i, Vec_IntSize(vLeaves) )
        Dar_ManCutTruthOne( p, Dar_ManObj(p, Leaf), vTruth, 8 );
    return Dar_ObjGetTruthStore( pRoot->Level, vTruth );
}

static inline int          Kit_TruthWordNum( int nVars )  { return nVars <= 5 ? 1 : (1 << (nVars - 5));                             }
static inline void Kit_TruthNot( unsigned * pOut, unsigned * pIn, int nVars )
{
    int w;
    for ( w = Kit_TruthWordNum(nVars)-1; w >= 0; w-- )
        pOut[w] = ~pIn[w];
}

/**Function*************************************************************

  Synopsis    [Computes the cost based on two ISOPs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_ManLargeCutEvalIsop( unsigned * pTruth, int nVars, Vec_Int_t * vMemory )
{
    extern int Kit_TruthIsop( unsigned * puTruth, int nVars, Vec_Int_t * vMemory, int fTryBoth );
    int RetValue, nClauses;
    // compute ISOP for the positive phase
    RetValue = Kit_TruthIsop( pTruth, nVars, vMemory, 0 );
    if ( RetValue == -1 )
        return DAR_INFINITY;
    assert( RetValue == 0 || RetValue == 1 );
    nClauses = Vec_IntSize( vMemory );
    // compute ISOP for the negative phase
    Kit_TruthNot( pTruth, pTruth, nVars );
    RetValue = Kit_TruthIsop( pTruth, nVars, vMemory, 0 );
    if ( RetValue == -1 )
        return DAR_INFINITY;
    Kit_TruthNot( pTruth, pTruth, nVars );
    assert( RetValue == 0 || RetValue == 1 );
    nClauses += Vec_IntSize( vMemory );
    return nClauses;
}

/**Function*************************************************************

  Synopsis    [Computes truth table of the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ManLargeCutCollect_rec( Dar_Man_t * p, Dar_Obj_t * pNode, Vec_Int_t * vLeaves, Vec_Int_t * vNodes )
{
    if ( Dar_ObjIsTravIdCurrent(p, pNode) )
        return;
    if ( Dar_ObjIsTravIdPrevious(p, pNode) )
    {
        Vec_IntPush( vLeaves, pNode->Id );
//        Vec_IntPush( vNodes, pNode->Id );
        Dar_ObjSetTravIdCurrent( p, pNode );
        return;
    }
    assert( Dar_ObjIsAnd(pNode) || Dar_ObjIsExor(pNode) );
    Dar_ObjSetTravIdCurrent( p, pNode );
    Dar_ManLargeCutCollect_rec( p, Dar_ObjFanin0(pNode), vLeaves, vNodes );
    Dar_ManLargeCutCollect_rec( p, Dar_ObjFanin1(pNode), vLeaves, vNodes );
    Vec_IntPush( vNodes, pNode->Id );
}

/**Function*************************************************************

  Synopsis    [Collect leaves and nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ManLargeCutCollect( Dar_Man_t * p, Dar_Obj_t * pRoot, Dar_Cut_t * pCutR, Dar_Cut_t * pCutL, int Leaf, 
                        Vec_Int_t * vLeaves, Vec_Int_t * vNodes )
{
    Vec_Int_t * vTemp;
    Dar_Obj_t * pObj;
    int Node, i;

    Dar_ManIncrementTravId( p );
    Dar_CutForEachLeaf( p, pCutR, pObj, i )
        if ( pObj->Id != Leaf )
           Dar_ObjSetTravIdCurrent( p, pObj );
    Dar_CutForEachLeaf( p, pCutL, pObj, i )
        Dar_ObjSetTravIdCurrent( p, pObj );

    // collect the internal nodes and leaves
    Dar_ManIncrementTravId( p );
    vTemp = Vec_IntAlloc( 100 );
    Dar_ManLargeCutCollect_rec( p, pRoot, vLeaves, vTemp );

    Vec_IntForEachEntry( vLeaves, Node, i )
        Vec_IntPush( vNodes, Node );
    Vec_IntForEachEntry( vTemp, Node, i )
        Vec_IntPush( vNodes, Node );

    Vec_IntFree( vTemp );

}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_ManLargeCutEval( Dar_Man_t * p, Dar_Obj_t * pRoot, Dar_Cut_t * pCutR, Dar_Cut_t * pCutL, int Leaf )
{
    Vec_Int_t * vLeaves, * vNodes, * vTruth, * vMemory;
    unsigned * pTruth;
    int RetValue;
//    Dar_Obj_t * pObj;

    vMemory = Vec_IntAlloc( 1 << 16 );
    vTruth = Vec_IntAlloc( 1 << 16 );
    vLeaves = Vec_IntAlloc( 100 );
    vNodes = Vec_IntAlloc( 100 );

    Dar_ManLargeCutCollect( p, pRoot, pCutR, pCutL, Leaf, vLeaves, vNodes );
/*
    // collect the nodes
    Dar_CutForEachLeaf( p, pCutR, pObj, i )
    {
        if ( pObj->Id == Leaf )
            continue;
        if ( pObj->fMarkA )
            continue;
        pObj->fMarkA = 1;
        Vec_IntPush( vLeaves, pObj->Id );
        Vec_IntPush( vNodes, pObj->Id );
    }
    Dar_CutForEachLeaf( p, pCutL, pObj, i )
    {
        if ( pObj->fMarkA )
            continue;
        pObj->fMarkA = 1;
        Vec_IntPush( vLeaves, pObj->Id );
        Vec_IntPush( vNodes, pObj->Id );
    }
    // collect and mark the nodes
    Dar_ManCollectCut_rec( p, pRoot, vNodes );
    // clean the nodes
    Vec_IntForEachEntry( vNodes, Leaf, i )
        Dar_ManObj(p, Leaf)->fMarkA = 0;
*/

    pTruth = Dar_ManCutTruth( p, pRoot, vLeaves, vNodes, vTruth );
    RetValue = Dar_ManLargeCutEvalIsop( pTruth, Vec_IntSize(vLeaves), vMemory );

    Vec_IntFree( vLeaves );
    Vec_IntFree( vNodes );
    Vec_IntFree( vTruth );
    Vec_IntFree( vMemory );

    return RetValue;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


