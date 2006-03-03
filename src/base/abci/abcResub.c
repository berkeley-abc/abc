/**CFile****************************************************************

  FileName    [abcResub.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Resubstitution manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcResub.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "dec.h"
 
////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Abc_ResubMan_t_ Abc_ResubMan_t;
struct Abc_ResubMan_t_
{
    // paramers
    int                nLeavesMax; // the max number of leaves in the cone
    int                nDivsMax;   // the max number of divisors in the cone
    // representation of the cone
    Abc_Obj_t *        pRoot;      // the root of the cone
    int                nLeaves;    // the number of leaves
    int                nDivs;      // the number of all divisor (including leaves)
    int                nMffc;      // the size of MFFC
    Vec_Ptr_t *        vDivs;      // the divisors
    // representation of the simulation info
    int                nBits;      // the number of simulation bits
    int                nWords;     // the number of unsigneds for siminfo
    Vec_Ptr_t        * vSims;      // simulation info
    unsigned         * pInfo;      // pointer to simulation info
    // internal divisor storage
    Vec_Ptr_t        * vDivs1U;    // the single-node unate divisors
    Vec_Ptr_t        * vDivs1B;    // the single-node binate divisors
    Vec_Ptr_t        * vDivs2U0;   // the double-node unate divisors
    Vec_Ptr_t        * vDivs2U1;   // the double-node unate divisors
    // other data
    Vec_Ptr_t        * vTemp;      // temporary array of nodes
};


// external procedures
extern Abc_ResubMan_t * Abc_ResubManStart( int nLeavesMax, int nDivsMax );
extern void             Abc_ResubManStop( Abc_ResubMan_t * p );
extern Dec_Graph_t *    Abc_ResubManEval( Abc_ResubMan_t * p, Abc_Obj_t * pRoot, Vec_Ptr_t * vLeaves, int nSteps );


static int  Abc_ResubManCollectDivs( Abc_ResubMan_t * p, Abc_Obj_t * pRoot, Vec_Ptr_t * vLeaves );
static int  Abc_ResubManMffc( Abc_ResubMan_t * p, Vec_Ptr_t * vDivs, Abc_Obj_t * pRoot, int nLeaves );
static void Abc_ResubManSimulate( Vec_Ptr_t * vDivs, int nLeaves, Vec_Ptr_t * vSims, int nLeavesMax, int nWords );

static Dec_Graph_t * Abc_ResubManQuit( Abc_ResubMan_t * p );
static Dec_Graph_t * Abc_ResubManDivs0( Abc_ResubMan_t * p );
static Dec_Graph_t * Abc_ResubManDivs1( Abc_ResubMan_t * p );
static Dec_Graph_t * Abc_ResubManDivsD( Abc_ResubMan_t * p );
static Dec_Graph_t * Abc_ResubManDivs2( Abc_ResubMan_t * p );
static Dec_Graph_t * Abc_ResubManDivs3( Abc_ResubMan_t * p );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_ResubMan_t * Abc_ResubManStart( int nLeavesMax, int nDivsMax )
{
    Abc_ResubMan_t * p;
    unsigned * pData;
    int i, k;
    p = ALLOC( Abc_ResubMan_t, 1 );
    memset( p, 0, sizeof(Abc_ResubMan_t) );
    p->nLeavesMax = nLeavesMax;
    p->nDivsMax   = nDivsMax;
    p->vDivs      = Vec_PtrAlloc( p->nDivsMax );
    // allocate simulation info
    p->nBits      = (1 << p->nLeavesMax);
    p->nWords     = (p->nBits <= 32)? 1 : p->nBits / sizeof(unsigned) / 8;
    p->pInfo      = ALLOC( unsigned, p->nWords * p->nDivsMax );
    memset( p->pInfo, 0, sizeof(unsigned) * p->nWords * p->nLeavesMax );
    p->vSims      = Vec_PtrAlloc( p->nDivsMax );
    for ( i = 0; i < p->nDivsMax; i++ )
        Vec_PtrPush( p->vSims, p->pInfo + i * p->nWords );
    // set elementary truth tables
    for ( k = 0; k < p->nLeavesMax; k++ )
    {
        pData = p->vSims->pArray[k];
        for ( i = 0; i < p->nBits; i++ )
            if ( i & (1 << k) )
                pData[i/32] |= (1 << (i%32));
    }
    // create the remaining divisors
    p->vDivs1U  = Vec_PtrAlloc( p->nDivsMax );
    p->vDivs1B  = Vec_PtrAlloc( p->nDivsMax );
    p->vDivs2U0 = Vec_PtrAlloc( p->nDivsMax );
    p->vDivs2U1 = Vec_PtrAlloc( p->nDivsMax );
    p->vTemp    = Vec_PtrAlloc( p->nDivsMax );
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ResubManStop( Abc_ResubMan_t * p )
{
    Vec_PtrFree( p->vDivs );
    Vec_PtrFree( p->vSims );
    Vec_PtrFree( p->vDivs1U );
    Vec_PtrFree( p->vDivs1B );
    Vec_PtrFree( p->vDivs2U0 );
    Vec_PtrFree( p->vDivs2U1 );
    Vec_PtrFree( p->vTemp );
    free( p->pInfo );
    free( p );
}


/**Function*************************************************************

  Synopsis    [Evaluates resubstution of one cut.]

  Description [Returns the graph to add if any.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Graph_t * Abc_ResubManEval( Abc_ResubMan_t * p, Abc_Obj_t * pRoot, Vec_Ptr_t * vLeaves, int nSteps )
{
    Dec_Graph_t * pGraph;
    assert( nSteps >= 0 );
    assert( nSteps <= 3 );
    // get the number of leaves
    p->pRoot = pRoot;
    p->nLeaves = Vec_PtrSize(vLeaves);
    // collect the divisor nodes
    Abc_ResubManCollectDivs( p, pRoot, vLeaves );
    // quit if the number of divisors collected is too large
    if ( Vec_PtrSize(p->vDivs) - p->nLeaves > p->nDivsMax - p->nLeavesMax )
        return NULL;
    // get the number nodes in its MFFC (and reorder the nodes)
    p->nMffc = Abc_ResubManMffc( p, p->vDivs, pRoot, p->nLeaves );
    assert( p->nMffc > 0 );
    // get the number of divisors
    p->nDivs = Vec_PtrSize(p->vDivs) - p->nMffc;
    // simulate the nodes
    Abc_ResubManSimulate( p->vDivs, p->nLeaves, p->vSims, p->nLeavesMax, p->nWords );

    // consider constants
    if ( pGraph = Abc_ResubManQuit( p ) )
        return pGraph;

    // consider equal nodes
    if ( pGraph = Abc_ResubManDivs0( p ) )
        return pGraph;
    if ( nSteps == 0 || p->nLeavesMax == 1 )
        return NULL;

    // consider one node
    if ( pGraph = Abc_ResubManDivs1( p ) )
        return pGraph;
    if ( nSteps == 1 || p->nLeavesMax == 2 )
        return NULL;

    // get the two level divisors
    Abc_ResubManDivsD( p );

    // consider two nodes
    if ( pGraph = Abc_ResubManDivs2( p ) )
        return pGraph;
    if ( nSteps == 2 || p->nLeavesMax == 3 )
        return NULL;

    // consider two nodes
    if ( pGraph = Abc_ResubManDivs3( p ) )
        return pGraph;
    if ( nSteps == 3 || p->nLeavesMax == 4 )
        return NULL;
    return NULL;
}



/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_ResubManCollectDivs( Abc_ResubMan_t * p, Abc_Obj_t * pRoot, Vec_Ptr_t * vLeaves )
{
    Abc_Obj_t * pNode, * pFanout;
    int i, k;
    // collect the leaves of the cut
    Vec_PtrClear( p->vDivs );
    Abc_NtkIncrementTravId( pRoot->pNtk );
    Vec_PtrForEachEntry( vLeaves, pNode, i )
    {
        Vec_PtrPush( p->vDivs, pNode );
        Abc_NodeSetTravIdCurrent( pNode );        
    }
    // explore the fanouts
    Vec_PtrForEachEntry( p->vDivs, pNode, i )
    {
        // if the fanout has both fanins in the set, add it
        Abc_ObjForEachFanout( pNode, pFanout, k )
        {
            if ( Abc_NodeIsTravIdCurrent(pFanout) || Abc_ObjIsPo(pFanout) )
                continue;
            if ( Abc_NodeIsTravIdCurrent(Abc_ObjFanin0(pFanout)) && Abc_NodeIsTravIdCurrent(Abc_ObjFanin1(pFanout)) )
            {
                Vec_PtrPush( p->vDivs, pFanout );
                Abc_NodeSetTravIdCurrent( pFanout );     
            }
        }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_ResubManMffc_rec( Abc_Obj_t * pNode )
{
    if ( Abc_NodeIsTravIdCurrent(pNode) )
        return 0;
    Abc_NodeSetTravIdCurrent( pNode ); 
    return 1 + Abc_ResubManMffc_rec( Abc_ObjFanin0(pNode) ) +
        Abc_ResubManMffc_rec( Abc_ObjFanin1(pNode) );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_ResubManMffc( Abc_ResubMan_t * p, Vec_Ptr_t * vDivs, Abc_Obj_t * pRoot, int nLeaves )
{
    Abc_Obj_t * pObj;
    int Counter, i, k;
    // increment the traversal ID for the leaves
    Abc_NtkIncrementTravId( pRoot->pNtk );
    // label the leaves
    Vec_PtrForEachEntryStop( vDivs, pObj, i, nLeaves )
        Abc_NodeSetTravIdCurrent( pObj ); 
    // make sure the node is in the cone and is no one of the leaves
    assert( Abc_NodeIsTravIdPrevious(pRoot) );
    Counter = Abc_ResubManMffc_rec( pRoot );
    // move the labeled nodes to the end 
    Vec_PtrClear( p->vTemp );
    k = 0;
    Vec_PtrForEachEntryStart( vDivs, pObj, i, nLeaves )
        if ( Abc_NodeIsTravIdCurrent(pObj) )
            Vec_PtrPush( p->vTemp, pObj );
        else
            Vec_PtrWriteEntry( vDivs, k++, pObj );
    // add the labeled nodes
    Vec_PtrForEachEntry( p->vTemp, pObj, i )
        Vec_PtrWriteEntry( vDivs, k++, pObj );
    assert( k == Vec_PtrSize(p->vDivs) );
    assert( pRoot == Vec_PtrEntryLast(p->vDivs) );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Performs simulation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ResubManSimulate( Vec_Ptr_t * vDivs, int nLeaves, Vec_Ptr_t * vSims, int nLeavesMax, int nWords )
{
    Abc_Obj_t * pObj;
    unsigned * puData0, * puData1, * puData;
    int i, k;
    // initialize random simulation data
    Vec_PtrForEachEntryStop( vDivs, pObj, i, nLeaves )
        pObj->pData = Vec_PtrEntry( vSims, i );
    // simulate
    Vec_PtrForEachEntryStart( vDivs, pObj, i, nLeaves )
    {
        pObj->pData = Vec_PtrEntry( vSims, i + nLeavesMax );
        puData0 = Abc_ObjFanin0(pObj)->pData;
        puData1 = Abc_ObjFanin1(pObj)->pData;
        puData  = pObj->pData;
        // simulate
        if ( Abc_ObjFaninC0(pObj) && Abc_ObjFaninC1(pObj) )
            for ( k = 0; k < nWords; k++ )
                puData[k] = ~puData0[k] & ~puData1[k];
        else if ( Abc_ObjFaninC0(pObj) )
            for ( k = 0; k < nWords; k++ )
                puData[k] = ~puData0[k] & puData1[k];
        else if ( Abc_ObjFaninC1(pObj) )
            for ( k = 0; k < nWords; k++ )
                puData[k] = puData0[k] & ~puData1[k];
        else 
            for ( k = 0; k < nWords; k++ )
                puData[k] = puData0[k] & puData1[k];
    }
    // complement if needed
    Vec_PtrForEachEntry( vDivs, pObj, i )
    {
        puData = pObj->pData;
        pObj->fPhase = (puData[0] & 1);
        if ( pObj->fPhase )
            for ( k = 0; k < nWords; k++ )
                puData[k] = ~puData[k];
    }
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Graph_t * Abc_ResubManQuit( Abc_ResubMan_t * p )
{
    Dec_Graph_t * pGraph;
    unsigned * upData;
    int w;
    upData = p->pRoot->pData;
    for ( w = 0; w < p->nWords; w++ )
        if ( upData[0] == 0 )
            break;
    if ( w != p->nWords )
        return NULL;
    // get the graph if the node looks constant
    if ( p->pRoot->fPhase )
        pGraph = Dec_GraphCreateConst1();
    else 
        pGraph = Dec_GraphCreateConst0();
    return pGraph;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Graph_t * Abc_ResubManQuit0( Abc_Obj_t * pRoot, Abc_Obj_t * pObj )
{
    Dec_Graph_t * pGraph;
    Dec_Edge_t eRoot;
    pGraph = Dec_GraphCreate( 1 );
    Dec_GraphNode( pGraph, 0 )->pFunc = pObj;
    eRoot = Dec_EdgeCreate( 0, pObj->fPhase );
    Dec_GraphSetRoot( pGraph, eRoot );
    if ( pRoot->fPhase )
        Dec_GraphComplement( pGraph );
    return pGraph;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Graph_t * Abc_ResubManQuit1( Abc_Obj_t * pRoot, Abc_Obj_t * pObj0, Abc_Obj_t * pObj1 )
{
    Dec_Graph_t * pGraph;
    Dec_Edge_t eRoot, eNode0, eNode1;
    assert( !Abc_ObjIsComplement(pObj0) );
    assert( !Abc_ObjIsComplement(pObj1) );
    pGraph = Dec_GraphCreate( 2 );
    Dec_GraphNode( pGraph, 0 )->pFunc = pObj0;
    Dec_GraphNode( pGraph, 1 )->pFunc = pObj1;
    eNode0 = Dec_EdgeCreate( 0, pObj0->fPhase );
    eNode1 = Dec_EdgeCreate( 1, pObj1->fPhase );
    eRoot  = Dec_GraphAddNodeOr( pGraph, eNode0, eNode1 );
    Dec_GraphSetRoot( pGraph, eRoot );
    if ( pRoot->fPhase )
        Dec_GraphComplement( pGraph );
    return pGraph;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Graph_t * Abc_ResubManQuit2( Abc_Obj_t * pRoot, Abc_Obj_t * pObj0, Abc_Obj_t * pObj1, Abc_Obj_t * pObj2 )
{
    Dec_Graph_t * pGraph;
    Dec_Edge_t eRoot, eAnd, eNode0, eNode1, eNode2;
    assert( !Abc_ObjIsComplement(pObj0) );
    pGraph = Dec_GraphCreate( 3 );
    Dec_GraphNode( pGraph, 0 )->pFunc = Abc_ObjRegular(pObj0);
    Dec_GraphNode( pGraph, 1 )->pFunc = Abc_ObjRegular(pObj1);
    Dec_GraphNode( pGraph, 2 )->pFunc = Abc_ObjRegular(pObj2);
    eNode0 = Dec_EdgeCreate( 0, Abc_ObjIsComplement(pObj0) ^ pObj0->fPhase );
    eNode1 = Dec_EdgeCreate( 1, Abc_ObjIsComplement(pObj1) ^ pObj1->fPhase );
    eNode2 = Dec_EdgeCreate( 2, Abc_ObjIsComplement(pObj2) ^ pObj2->fPhase );
    eAnd   = Dec_GraphAddNodeAnd( pGraph, eNode1, eNode2 );
    eRoot  = Dec_GraphAddNodeOr( pGraph, eNode0, eAnd );
    Dec_GraphSetRoot( pGraph, eRoot );
    if ( pRoot->fPhase )
        Dec_GraphComplement( pGraph );
    return pGraph;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Graph_t * Abc_ResubManQuit3( Abc_Obj_t * pRoot, Abc_Obj_t * pObj0, Abc_Obj_t * pObj1, Abc_Obj_t * pObj2, Abc_Obj_t * pObj3 )
{
    Dec_Graph_t * pGraph;
    Dec_Edge_t eRoot, eAnd0, eAnd1, eNode0, eNode1, eNode2, eNode3;
    pGraph = Dec_GraphCreate( 4 );
    Dec_GraphNode( pGraph, 0 )->pFunc = Abc_ObjRegular(pObj0);
    Dec_GraphNode( pGraph, 1 )->pFunc = Abc_ObjRegular(pObj1);
    Dec_GraphNode( pGraph, 2 )->pFunc = Abc_ObjRegular(pObj2);
    Dec_GraphNode( pGraph, 3 )->pFunc = Abc_ObjRegular(pObj3);
    eNode0 = Dec_EdgeCreate( 0, Abc_ObjIsComplement(pObj0) ^ pObj0->fPhase );
    eNode1 = Dec_EdgeCreate( 1, Abc_ObjIsComplement(pObj1) ^ pObj1->fPhase );
    eNode2 = Dec_EdgeCreate( 2, Abc_ObjIsComplement(pObj2) ^ pObj2->fPhase );
    eNode3 = Dec_EdgeCreate( 3, Abc_ObjIsComplement(pObj3) ^ pObj3->fPhase );
    eAnd0  = Dec_GraphAddNodeAnd( pGraph, eNode0, eNode1 );
    eAnd1  = Dec_GraphAddNodeAnd( pGraph, eNode2, eNode3 );
    eRoot  = Dec_GraphAddNodeOr( pGraph, eAnd0, eAnd1 );
    Dec_GraphSetRoot( pGraph, eRoot );
    if ( pRoot->fPhase )
        Dec_GraphComplement( pGraph );
    return pGraph;
}


/**Function*************************************************************

  Synopsis    [Derives unate/binate divisors.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Graph_t * Abc_ResubManDivs0( Abc_ResubMan_t * p )
{
    Abc_Obj_t * pObj;
    unsigned * puData, * puDataR;
    int i, w;
    Vec_PtrClear( p->vDivs1U );
    Vec_PtrClear( p->vDivs1B );
    puDataR = p->pRoot->pData;
    Vec_PtrForEachEntryStop( p->vDivs, pObj, i, p->nDivs )
    {
        puData = pObj->pData;
        for ( w = 0; w < p->nWords; w++ )
            if ( puData[w] != puDataR[w] )
                break;
        if ( w == p->nWords )
            return Abc_ResubManQuit0( p->pRoot, pObj );
        for ( w = 0; w < p->nWords; w++ )
            if ( puData[w] & ~puDataR[w] )
                break;
        if ( w == p->nWords )
            Vec_PtrPush( p->vDivs1U, pObj );
        else
            Vec_PtrPush( p->vDivs1B, pObj );
    }
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Derives unate/binate divisors.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Graph_t * Abc_ResubManDivs1( Abc_ResubMan_t * p )
{
    Abc_Obj_t * pObj0, * pObj1;
    unsigned * puData0, * puData1, * puDataR;
    int i, k, w;
    puDataR = p->pRoot->pData;
    Vec_PtrForEachEntry( p->vDivs1U, pObj0, i )
    {
        puData0 = pObj0->pData;
        Vec_PtrForEachEntryStart( p->vDivs1U, pObj1, k, i + 1 )
        {
            puData1 = pObj1->pData;
            for ( w = 0; w < p->nWords; w++ )
                if ( (puData0[w] | puData1[w]) != puDataR[w] )
                    break;
            if ( w == p->nWords )
                return Abc_ResubManQuit1( p->pRoot, pObj0, pObj1 );
        }
    }
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Derives unate/binate divisors.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Graph_t * Abc_ResubManDivsD( Abc_ResubMan_t * p )
{
    Abc_Obj_t * pObj0, * pObj1;
    unsigned * puData0, * puData1, * puDataR;
    int i, k, w;
    Vec_PtrClear( p->vDivs2U0 );
    Vec_PtrClear( p->vDivs2U1 );
    puDataR = p->pRoot->pData;
    Vec_PtrForEachEntry( p->vDivs1U, pObj0, i )
    {
        puData0 = pObj0->pData;
        Vec_PtrForEachEntryStart( p->vDivs1U, pObj1, k, i + 1 )
        {
            puData1 = pObj1->pData;

            for ( w = 0; w < p->nWords; w++ )
                if ( (puData0[w] & puData1[w]) & ~puDataR[w] )
                    break;
            if ( w == p->nWords )
            {
                Vec_PtrPush( p->vDivs2U0, pObj0 );
                Vec_PtrPush( p->vDivs2U1, pObj1 );
            }

            for ( w = 0; w < p->nWords; w++ )
                if ( (~puData0[w] & puData1[w]) & ~puDataR[w] )
                    break;
            if ( w == p->nWords )
            {
                Vec_PtrPush( p->vDivs2U0, Abc_ObjNot(pObj0) );
                Vec_PtrPush( p->vDivs2U1, pObj1 );
            }

            for ( w = 0; w < p->nWords; w++ )
                if ( (puData0[w] & ~puData1[w]) & ~puDataR[w] )
                    break;
            if ( w == p->nWords )
            {
                Vec_PtrPush( p->vDivs2U0, pObj0 );
                Vec_PtrPush( p->vDivs2U1, Abc_ObjNot(pObj1) );
            }
        }
    }
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Derives unate/binate divisors.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Graph_t * Abc_ResubManDivs2( Abc_ResubMan_t * p )
{
    Abc_Obj_t * pObj0, * pObj1, * pObj2;
    unsigned * puData0, * puData1, * puData2, * puDataR;
    int i, k, w;
    puDataR = p->pRoot->pData;
    Vec_PtrForEachEntry( p->vDivs1U, pObj0, i )
    {
        puData0 = pObj0->pData;
        Vec_PtrForEachEntryStart( p->vDivs2U0, pObj1, k, i + 1 )
        {
            pObj2 = Vec_PtrEntry( p->vDivs2U1, k );
            puData1 = Abc_ObjRegular(pObj1)->pData;
            puData2 = Abc_ObjRegular(pObj2)->pData;

            if ( !Abc_ObjFaninC0(pObj1) && !Abc_ObjFaninC1(pObj2) )
            {
                for ( w = 0; w < p->nWords; w++ )
                    if ( (puData0[w] | (puData1[w] & puData2[w])) != puDataR[w] )
                        break;
            }
            else if ( Abc_ObjFaninC0(pObj1) )
            {
                for ( w = 0; w < p->nWords; w++ )
                    if ( (puData0[w] | (~puData1[w] & puData2[w])) != puDataR[w] )
                        break;
            }
            else if ( Abc_ObjFaninC1(pObj2) )
            {
                for ( w = 0; w < p->nWords; w++ )
                    if ( (puData0[w] | (puData1[w] & ~puData2[w])) != puDataR[w] )
                        break;
            }
            else assert( 0 );
            if ( w == p->nWords )
                return Abc_ResubManQuit2( p->pRoot, pObj0, pObj1, pObj2 );
        }
    }
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Derives unate/binate divisors.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Graph_t * Abc_ResubManDivs3( Abc_ResubMan_t * p )
{
    Abc_Obj_t * pObj0, * pObj1, * pObj2, * pObj3;
    unsigned * puData0, * puData1, * puData2, * puData3, * puDataR;
    int i, k, w;
    puDataR = p->pRoot->pData;
    Vec_PtrForEachEntry( p->vDivs2U0, pObj0, i )
    {
        pObj1 = Vec_PtrEntry( p->vDivs2U1, i );
        puData0 = Abc_ObjRegular(pObj0)->pData;
        puData1 = Abc_ObjRegular(pObj1)->pData;

        Vec_PtrForEachEntryStart( p->vDivs2U0, pObj2, k, i + 1 )
        {
            pObj3 = Vec_PtrEntry( p->vDivs2U1, k );
            puData2 = Abc_ObjRegular(pObj2)->pData;
            puData3 = Abc_ObjRegular(pObj3)->pData;

            if ( !Abc_ObjFaninC0(pObj0) && !Abc_ObjFaninC1(pObj1) )
            {
                if ( !Abc_ObjFaninC0(pObj2) && !Abc_ObjFaninC1(pObj3) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ((puData0[w] & puData1[w]) | (puData2[w] & puData3[w])) != puDataR[w] )
                            break;
                }
                else if ( Abc_ObjFaninC0(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ((puData0[w] & puData1[w]) | (~puData2[w] & puData3[w])) != puDataR[w] )
                            break;
                }
                else if ( Abc_ObjFaninC0(pObj3) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ((puData0[w] & puData1[w]) | (puData2[w] & ~puData3[w])) != puDataR[w] )
                            break;
                }
                else assert( 0 );
            }
            else if ( Abc_ObjFaninC0(pObj0) )
            {
                if ( !Abc_ObjFaninC0(pObj2) && !Abc_ObjFaninC1(pObj3) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ((~puData0[w] & puData1[w]) | (puData2[w] & puData3[w])) != puDataR[w] )
                            break;
                }
                else if ( Abc_ObjFaninC0(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ((~puData0[w] & puData1[w]) | (~puData2[w] & puData3[w])) != puDataR[w] )
                            break;
                }
                else if ( Abc_ObjFaninC0(pObj3) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ((~puData0[w] & puData1[w]) | (puData2[w] & ~puData3[w])) != puDataR[w] )
                            break;
                }
                else assert( 0 );
            }
            else if ( Abc_ObjFaninC1(pObj1) )
            {
                if ( !Abc_ObjFaninC0(pObj2) && !Abc_ObjFaninC1(pObj3) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ((puData0[w] & ~puData1[w]) | (puData2[w] & puData3[w])) != puDataR[w] )
                            break;
                }
                else if ( Abc_ObjFaninC0(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ((puData0[w] & ~puData1[w]) | (~puData2[w] & puData3[w])) != puDataR[w] )
                            break;
                }
                else if ( Abc_ObjFaninC0(pObj3) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ((puData0[w] & ~puData1[w]) | (puData2[w] & ~puData3[w])) != puDataR[w] )
                            break;
                }
                else assert( 0 );
            }
            else assert( 0 );
            if ( w == p->nWords )
                return Abc_ResubManQuit3( p->pRoot, pObj0, pObj1, pObj2, pObj3 );
        }
    }
    return NULL;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


