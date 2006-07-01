/**CFile****************************************************************

  FileName    [ivyUtil.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    [Various procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: ivyUtil.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ivy.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Increments the current traversal ID of the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManIncrementTravId( Ivy_Man_t * p )
{
    if ( p->nTravIds >= (1<<30)-1 - 1000 )
        Ivy_ManCleanTravId( p );
    p->nTravIds++;
}

/**Function*************************************************************

  Synopsis    [Sets the DFS ordering of the nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManCleanTravId( Ivy_Man_t * p )
{
    Ivy_Obj_t * pObj;
    int i;
    p->nTravIds = 1;
    Ivy_ManForEachObj( p, pObj, i )
        pObj->TravId = 0;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the node is the root of MUX or EXOR/NEXOR.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_ObjIsMuxType( Ivy_Obj_t * pNode )
{
    Ivy_Obj_t * pNode0, * pNode1;
    // check that the node is regular
    assert( !Ivy_IsComplement(pNode) );
    // if the node is not AND, this is not MUX
    if ( !Ivy_ObjIsAnd(pNode) )
        return 0;
    // if the children are not complemented, this is not MUX
    if ( !Ivy_ObjFaninC0(pNode) || !Ivy_ObjFaninC1(pNode) )
        return 0;
    // get children
    pNode0 = Ivy_ObjFanin0(pNode);
    pNode1 = Ivy_ObjFanin1(pNode);
    // if the children are not ANDs, this is not MUX
    if ( !Ivy_ObjIsAnd(pNode0) || !Ivy_ObjIsAnd(pNode1) )
        return 0;
    // otherwise the node is MUX iff it has a pair of equal grandchildren
    return (Ivy_ObjFaninId0(pNode0) == Ivy_ObjFaninId0(pNode1) && (Ivy_ObjFaninC0(pNode0) ^ Ivy_ObjFaninC0(pNode1))) || 
           (Ivy_ObjFaninId0(pNode0) == Ivy_ObjFaninId1(pNode1) && (Ivy_ObjFaninC0(pNode0) ^ Ivy_ObjFaninC1(pNode1))) ||
           (Ivy_ObjFaninId1(pNode0) == Ivy_ObjFaninId0(pNode1) && (Ivy_ObjFaninC1(pNode0) ^ Ivy_ObjFaninC0(pNode1))) ||
           (Ivy_ObjFaninId1(pNode0) == Ivy_ObjFaninId1(pNode1) && (Ivy_ObjFaninC1(pNode0) ^ Ivy_ObjFaninC1(pNode1)));
}

/**Function*************************************************************

  Synopsis    [Recognizes what nodes are control and data inputs of a MUX.]

  Description [If the node is a MUX, returns the control variable C.
  Assigns nodes T and E to be the then and else variables of the MUX. 
  Node C is never complemented. Nodes T and E can be complemented.
  This function also recognizes EXOR/NEXOR gates as MUXes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ivy_Obj_t * Ivy_ObjRecognizeMux( Ivy_Obj_t * pNode, Ivy_Obj_t ** ppNodeT, Ivy_Obj_t ** ppNodeE )
{
    Ivy_Obj_t * pNode0, * pNode1;
    assert( !Ivy_IsComplement(pNode) );
    assert( Ivy_ObjIsMuxType(pNode) );
    // get children
    pNode0 = Ivy_ObjFanin0(pNode);
    pNode1 = Ivy_ObjFanin1(pNode);
    // find the control variable
//    if ( pNode1->p1 == Fraig_Not(pNode2->p1) )
    if ( Ivy_ObjFaninId0(pNode0) == Ivy_ObjFaninId0(pNode1) && (Ivy_ObjFaninC0(pNode0) ^ Ivy_ObjFaninC0(pNode1)) )
    {
//        if ( Fraig_IsComplement(pNode1->p1) )
        if ( Ivy_ObjFaninC0(pNode0) )
        { // pNode2->p1 is positive phase of C
            *ppNodeT = Ivy_Not(Ivy_ObjChild1(pNode1));//pNode2->p2);
            *ppNodeE = Ivy_Not(Ivy_ObjChild1(pNode0));//pNode1->p2);
            return Ivy_ObjChild0(pNode1);//pNode2->p1;
        }
        else
        { // pNode1->p1 is positive phase of C
            *ppNodeT = Ivy_Not(Ivy_ObjChild1(pNode0));//pNode1->p2);
            *ppNodeE = Ivy_Not(Ivy_ObjChild1(pNode1));//pNode2->p2);
            return Ivy_ObjChild0(pNode0);//pNode1->p1;
        }
    }
//    else if ( pNode1->p1 == Fraig_Not(pNode2->p2) )
    else if ( Ivy_ObjFaninId0(pNode0) == Ivy_ObjFaninId1(pNode1) && (Ivy_ObjFaninC0(pNode0) ^ Ivy_ObjFaninC1(pNode1)) )
    {
//        if ( Fraig_IsComplement(pNode1->p1) )
        if ( Ivy_ObjFaninC0(pNode0) )
        { // pNode2->p2 is positive phase of C
            *ppNodeT = Ivy_Not(Ivy_ObjChild0(pNode1));//pNode2->p1);
            *ppNodeE = Ivy_Not(Ivy_ObjChild1(pNode0));//pNode1->p2);
            return Ivy_ObjChild1(pNode1);//pNode2->p2;
        }
        else
        { // pNode1->p1 is positive phase of C
            *ppNodeT = Ivy_Not(Ivy_ObjChild1(pNode0));//pNode1->p2);
            *ppNodeE = Ivy_Not(Ivy_ObjChild0(pNode1));//pNode2->p1);
            return Ivy_ObjChild0(pNode0);//pNode1->p1;
        }
    }
//    else if ( pNode1->p2 == Fraig_Not(pNode2->p1) )
    else if ( Ivy_ObjFaninId1(pNode0) == Ivy_ObjFaninId0(pNode1) && (Ivy_ObjFaninC1(pNode0) ^ Ivy_ObjFaninC0(pNode1)) )
    {
//        if ( Fraig_IsComplement(pNode1->p2) )
        if ( Ivy_ObjFaninC1(pNode0) )
        { // pNode2->p1 is positive phase of C
            *ppNodeT = Ivy_Not(Ivy_ObjChild1(pNode1));//pNode2->p2);
            *ppNodeE = Ivy_Not(Ivy_ObjChild0(pNode0));//pNode1->p1);
            return Ivy_ObjChild0(pNode1);//pNode2->p1;
        }
        else
        { // pNode1->p2 is positive phase of C
            *ppNodeT = Ivy_Not(Ivy_ObjChild0(pNode0));//pNode1->p1);
            *ppNodeE = Ivy_Not(Ivy_ObjChild1(pNode1));//pNode2->p2);
            return Ivy_ObjChild1(pNode0);//pNode1->p2;
        }
    }
//    else if ( pNode1->p2 == Fraig_Not(pNode2->p2) )
    else if ( Ivy_ObjFaninId1(pNode0) == Ivy_ObjFaninId1(pNode1) && (Ivy_ObjFaninC1(pNode0) ^ Ivy_ObjFaninC1(pNode1)) )
    {
//        if ( Fraig_IsComplement(pNode1->p2) )
        if ( Ivy_ObjFaninC1(pNode0) )
        { // pNode2->p2 is positive phase of C
            *ppNodeT = Ivy_Not(Ivy_ObjChild0(pNode1));//pNode2->p1);
            *ppNodeE = Ivy_Not(Ivy_ObjChild0(pNode0));//pNode1->p1);
            return Ivy_ObjChild1(pNode1);//pNode2->p2;
        }
        else
        { // pNode1->p2 is positive phase of C
            *ppNodeT = Ivy_Not(Ivy_ObjChild0(pNode0));//pNode1->p1);
            *ppNodeE = Ivy_Not(Ivy_ObjChild0(pNode1));//pNode2->p1);
            return Ivy_ObjChild1(pNode0);//pNode1->p2;
        }
    }
    assert( 0 ); // this is not MUX
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Computes truth table of the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManCollectCut_rec( Ivy_Obj_t * pNode, Vec_Int_t * vNodes )
{
    if ( pNode->fMarkA )
        return;
    pNode->fMarkA = 1;
    assert( Ivy_ObjIsAnd(pNode) || Ivy_ObjIsExor(pNode) );
    Ivy_ManCollectCut_rec( Ivy_ObjFanin0(pNode), vNodes );
    Ivy_ManCollectCut_rec( Ivy_ObjFanin1(pNode), vNodes );
    Vec_IntPush( vNodes, pNode->Id );
}

/**Function*************************************************************

  Synopsis    [Computes truth table of the cut.]

  Description [Does not modify the array of leaves. Uses array vTruth to store 
  temporary truth tables. The returned pointer should be used immediately.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManCollectCut( Ivy_Obj_t * pRoot, Vec_Int_t * vLeaves, Vec_Int_t * vNodes )
{
    int i, Leaf;
    // collect and mark the leaves
    Vec_IntClear( vNodes );
    Vec_IntForEachEntry( vLeaves, Leaf, i )
    {
        Vec_IntPush( vNodes, Leaf );
        Ivy_ObjObj(pRoot, Leaf)->fMarkA = 1;
    }
    // collect and mark the nodes
    Ivy_ManCollectCut_rec( pRoot, vNodes );
    // clean the nodes
    Vec_IntForEachEntry( vNodes, Leaf, i )
        Ivy_ObjObj(pRoot, Leaf)->fMarkA = 0;
}

/**Function*************************************************************

  Synopsis    [Returns the pointer to the truth table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned * Ivy_ObjGetTruthStore( int ObjNum, Vec_Int_t * vTruth )
{
   return ((unsigned *)Vec_IntArray(vTruth)) + 8 * ObjNum;
}

/**Function*************************************************************

  Synopsis    [Computes truth table of the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManCutTruthOne( Ivy_Obj_t * pNode, Vec_Int_t * vTruth, int nWords )
{
    unsigned * pTruth, * pTruth0, * pTruth1;
    int i;
    pTruth  = Ivy_ObjGetTruthStore( pNode->TravId, vTruth );
    pTruth0 = Ivy_ObjGetTruthStore( Ivy_ObjFanin0(pNode)->TravId, vTruth );
    pTruth1 = Ivy_ObjGetTruthStore( Ivy_ObjFanin1(pNode)->TravId, vTruth );
    if ( Ivy_ObjIsExor(pNode) )
        for ( i = 0; i < nWords; i++ )
            pTruth[i] = pTruth0[i] ^ pTruth1[i];
    else if ( !Ivy_ObjFaninC0(pNode) && !Ivy_ObjFaninC1(pNode) )
        for ( i = 0; i < nWords; i++ )
            pTruth[i] = pTruth0[i] & pTruth1[i];
    else if ( !Ivy_ObjFaninC0(pNode) && Ivy_ObjFaninC1(pNode) )
        for ( i = 0; i < nWords; i++ )
            pTruth[i] = pTruth0[i] & ~pTruth1[i];
    else if ( Ivy_ObjFaninC0(pNode) && !Ivy_ObjFaninC1(pNode) )
        for ( i = 0; i < nWords; i++ )
            pTruth[i] = ~pTruth0[i] & pTruth1[i];
    else // if ( Ivy_ObjFaninC0(pNode) && Ivy_ObjFaninC1(pNode) )
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
unsigned * Ivy_ManCutTruth( Ivy_Obj_t * pRoot, Vec_Int_t * vLeaves, Vec_Int_t * vNodes, Vec_Int_t * vTruth )
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
    Ivy_ManCollectCut( pRoot, vLeaves, vNodes );
    // set the node numbers
    Vec_IntForEachEntry( vNodes, Leaf, i )
        Ivy_ObjObj(pRoot, Leaf)->TravId = i;
    // alloc enough memory
    Vec_IntClear( vTruth );
    Vec_IntGrow( vTruth, 8 * Vec_IntSize(vNodes) );
    // set the elementary truth tables
    Vec_IntForEachEntry( vLeaves, Leaf, i )
        memcpy( Ivy_ObjGetTruthStore(i, vTruth), uTruths[i], 8 * sizeof(unsigned) );
    // compute truths for other nodes
    Vec_IntForEachEntryStart( vNodes, Leaf, i, Vec_IntSize(vLeaves) )
        Ivy_ManCutTruthOne( Ivy_ObjObj(pRoot, Leaf), vTruth, 8 );
    return Ivy_ObjGetTruthStore( pRoot->TravId, vTruth );
}

/**Function*************************************************************

  Synopsis    [Collect the latches.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Ivy_ManLatches( Ivy_Man_t * p )
{
    Vec_Int_t * vLatches;
    Ivy_Obj_t * pObj;
    int i;
    vLatches = Vec_IntAlloc( Ivy_ManLatchNum(p) );
    Ivy_ManForEachLatch( p, pObj, i )
        Vec_IntPush( vLatches, pObj->Id );
    return vLatches;
}

/**Function*************************************************************

  Synopsis    [Collect the latches.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_ManReadLevels( Ivy_Man_t * p )
{
    Ivy_Obj_t * pObj;
    int i, LevelMax = 0;
    Ivy_ManForEachPo( p, pObj, i )
    {
        pObj = Ivy_ObjFanin0(pObj);
        LevelMax = IVY_MAX( LevelMax, (int)pObj->Level );
    }
    return LevelMax;
}

/**Function*************************************************************

  Synopsis    [Returns the real fanin.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ivy_Obj_t * Ivy_ObjReal( Ivy_Obj_t * pObj )
{
    Ivy_Obj_t * pFanin;
    if ( !Ivy_ObjIsBuf( Ivy_Regular(pObj) ) )
        return pObj;
    pFanin = Ivy_ObjReal( Ivy_ObjChild0(Ivy_Regular(pObj)) );
    return Ivy_NotCond( pFanin, Ivy_IsComplement(pObj) );
}



/**Function*************************************************************

  Synopsis    [Checks if the cube has exactly one 1.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Ivy_TruthHasOneOne( unsigned uCube )
{
    return (uCube & (uCube - 1)) == 0;
}

/**Function*************************************************************

  Synopsis    [Checks if two cubes are distance-1.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Ivy_TruthCubesDist1( unsigned uCube1, unsigned uCube2 )
{
    unsigned uTemp = uCube1 | uCube2;
    return Ivy_TruthHasOneOne( (uTemp >> 1) & uTemp & 0x55555555 );
}

/**Function*************************************************************

  Synopsis    [Checks if two cubes differ in only one literal.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Ivy_TruthCubesDiff1( unsigned uCube1, unsigned uCube2 )
{
    unsigned uTemp = uCube1 ^ uCube2;
    return Ivy_TruthHasOneOne( ((uTemp >> 1) | uTemp) & 0x55555555 );
}

/**Function*************************************************************

  Synopsis    [Combines two distance 1 cubes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned Ivy_TruthCubesMerge( unsigned uCube1, unsigned uCube2 )
{
    unsigned uTemp;
    uTemp = uCube1 | uCube2;
    uTemp &= (uTemp >> 1) & 0x55555555;
    assert( Ivy_TruthHasOneOne(uTemp) );
    uTemp |= (uTemp << 1);
    return (uCube1 | uCube2) ^ uTemp;
}

/**Function*************************************************************

  Synopsis    [Estimates the number of AIG nodes in the truth table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_TruthEstimateNodes( unsigned * pTruth, int nVars )
{
    static unsigned short uResult[256];
    static unsigned short uCover[81*81];
    static char pVarCount[81*81];
    int nMints, uCube, uCubeNew, i, k, c, nCubes, nRes, Counter;
    assert( nVars <= 8 );
    // create the cover
    nCubes = 0;
    nMints = (1 << nVars);
    for ( i = 0; i < nMints; i++ )
        if ( pTruth[i/32] & (1 << (i & 31)) )
        {
            uCube = 0;
            for ( k = 0; k < nVars; k++ )
                if ( i & (1 << k) )
                    uCube |= (1 << ((k<<1)+1));
                else
                    uCube |= (1 << ((k<<1)+0));
            uCover[nCubes] = uCube;
            pVarCount[nCubes] = nVars;
            nCubes++;
//            Extra_PrintBinary( stdout, &uCube, 8 ); printf( "\n" );
        }
    assert( nCubes <= 256 );
    // reduce the cover by building larger cubes
    for ( i = 1; i < nCubes; i++ )
        for ( k = 0; k < i; k++ )
            if ( pVarCount[i] && pVarCount[i] == pVarCount[k] && Ivy_TruthCubesDist1(uCover[i], uCover[k]) )
            {
                uCubeNew = Ivy_TruthCubesMerge(uCover[i], uCover[k]);
                for ( c = i; c < nCubes; c++ )
                    if ( uCubeNew == uCover[c] )
                        break;
                if ( c != nCubes )
                    continue;
                uCover[nCubes] = uCubeNew;
                pVarCount[nCubes] = pVarCount[i] - 1;
                nCubes++;
                assert( nCubes < 81*81 );
//                Extra_PrintBinary( stdout, &uCubeNew, 8 ); printf( "\n" );
//                c = c;
            }
    // compact the cover
    nRes = 0;
    for ( i = nCubes -1; i >= 0; i-- )
    {
        for ( k = 0; k < nRes; k++ )
            if ( (uCover[i] & uResult[k]) == uResult[k] )
                break;
        if ( k != nRes )
            continue;
        uResult[nRes++] = uCover[i];
    }
    // count the number of literals
    Counter = 0;
    for ( i = 0; i < nRes; i++ )
    {
        for ( k = 0; k < nVars; k++ )
            if ( uResult[i] & (3 << (k<<1)) )
                Counter++;
    }
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Tests the cover procedure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_TruthEstimateNodesTest()
{
    unsigned uTruth[8];
    int i;
    for ( i = 0; i < 8; i++ )
        uTruth[i] = ~(unsigned)0;
    uTruth[3] ^= (1 << 13);
//    uTruth[4] = 0xFFFFF;
//    uTruth[0] = 0xFF;
//    uTruth[0] ^= (1 << 3);
    printf( "Number = %d.\n", Ivy_TruthEstimateNodes(uTruth, 8) );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


