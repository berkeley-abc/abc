/**CFile****************************************************************

  FileName    [abcDsdRes.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcDsdRes.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "kit.h"
#include "if.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define LUT_SIZE_MAX     16   // the largest size of the function
#define LUT_CUTS_MAX   1024   // the largest number of cuts considered

typedef struct Lut_Man_t_ Lut_Man_t;
typedef struct Lut_Cut_t_ Lut_Cut_t;

struct Lut_Cut_t_
{
    unsigned     nLeaves       : 6;     // (L) the number of leaves
    unsigned     nNodes        : 6;     // (M) the number of nodes
    unsigned     nNodesDup     : 6;     // (Q) nodes outside of MFFC
    unsigned     nLuts         : 6;     // (N) the number of LUTs to try
    unsigned     unused        : 6;     // unused
    unsigned     fHasDsd       : 1;     // set to 1 if the cut has structural DSD (and so cannot be used)
    unsigned     fMark         : 1;     // multipurpose mark
    unsigned     uSign[2];              // the signature
    float        Weight;                // the weight of the cut: (M - Q)/N(V)   (the larger the better)
    int          Gain;                  // the gain achieved using this cut
    int          pLeaves[LUT_SIZE_MAX]; // the leaves of the cut
    int          pNodes[LUT_SIZE_MAX];  // the nodes of the cut
};

struct Lut_Man_t_
{
    // parameters
    Lut_Par_t *  pPars;                 // the set of parameters
    // current representation
    Abc_Ntk_t *  pNtk;                  // the network
    Abc_Obj_t *  pObj;                  // the node to resynthesize 
    // cut representation
    int          nMffc;                 // the size of MFFC of the node
    int          nCuts;                 // the total number of cuts    
    int          nCutsMax;              // the largest possible number of cuts
    int          nEvals;                // the number of good cuts
    Lut_Cut_t    pCuts[LUT_CUTS_MAX];   // the storage for cuts
    int          pEvals[LUT_CUTS_MAX];  // the good cuts
    // visited nodes 
    Vec_Vec_t *  vVisited;
    // mapping manager
    If_Man_t *   pIfMan;
    Vec_Int_t *  vCover; 
    Vec_Vec_t *  vLevels;
    // temporary variables
    int          pRefs[LUT_SIZE_MAX];   // fanin reference counters 
    int          pCands[LUT_SIZE_MAX];  // internal nodes pointing only to the leaves
    // truth table representation
    Vec_Ptr_t *  vTtElems;              // elementary truth tables
    Vec_Ptr_t *  vTtNodes;              // storage for temporary truth tables of the nodes 
    // statistics
    int          nNodesTotal;           // total number of nodes
    int          nNodesOver;            // nodes with cuts over the limit 
    int          nCutsTotal;            // total number of cuts
    int          nCutsUseful;           // useful cuts 
    int          nGainTotal;            // the gain in LUTs
    int          nChanges;              // the number of changed nodes
    // counter of non-DSD blocks
    int          nBlocks[17];
    // rutime
    int          timeCuts;
    int          timeTruth;
    int          timeEval;
    int          timeMap;
    int          timeOther;
    int          timeTotal;
};

#define Abc_LutCutForEachLeaf( pNtk, pCut, pObj, i )                                        \
    for ( i = 0; (i < (int)(pCut)->nLeaves) && (((pObj) = Abc_NtkObj(pNtk, (pCut)->pLeaves[i])), 1); i++ )
#define Abc_LutCutForEachNode( pNtk, pCut, pObj, i )                                        \
    for ( i = 0; (i < (int)(pCut)->nNodes) && (((pObj) = Abc_NtkObj(pNtk, (pCut)->pNodes[i])), 1); i++ )
#define Abc_LutCutForEachNodeReverse( pNtk, pCut, pObj, i )                                 \
    for ( i = (int)(pCut)->nNodes - 1; (i >= 0) && (((pObj) = Abc_NtkObj(pNtk, (pCut)->pNodes[i])), 1); i-- )

static inline If_Obj_t *  If_Regular( If_Obj_t * p )        { return (If_Obj_t *)((unsigned long)(p) & ~01);  }
static inline If_Obj_t *  If_Not( If_Obj_t * p )            { return (If_Obj_t *)((unsigned long)(p) ^  01);  }
static inline If_Obj_t *  If_NotCond( If_Obj_t * p, int c ) { return (If_Obj_t *)((unsigned long)(p) ^ (c));  }
static inline int         If_IsComplement( If_Obj_t * p )   { return (int )(((unsigned long)p) & 01);         }

extern void Res_UpdateNetworkLevel( Abc_Obj_t * pObjNew, Vec_Vec_t * vLevels );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Lut_Man_t * Abc_LutManStart( Lut_Par_t * pPars )
{
    Lut_Man_t * p;
    assert( pPars->nLutsMax <= 16 );
    assert( pPars->nVarsMax > 0 );
    p = ALLOC( Lut_Man_t, 1 );
    memset( p, 0, sizeof(Lut_Man_t) );
    p->pPars = pPars;
    p->nCutsMax = LUT_CUTS_MAX;
    p->vTtElems = Vec_PtrAllocTruthTables( pPars->nVarsMax );
    p->vTtNodes = Vec_PtrAllocSimInfo( 256, Abc_TruthWordNum(pPars->nVarsMax) );
    p->vCover = Vec_IntAlloc( 1 << 12 );
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_LutManStop( Lut_Man_t * p )
{
    if ( p->pIfMan )
    {
        void * pPars = p->pIfMan->pPars;
        If_ManStop( p->pIfMan );
        free( pPars );
    }
    if ( p->vLevels )
        Vec_VecFree( p->vLevels );
    if ( p->vVisited )
        Vec_VecFree( p->vVisited );
    Vec_IntFree( p->vCover );
    Vec_PtrFree( p->vTtElems );
    Vec_PtrFree( p->vTtNodes );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Returns 1 if at least one entry has changed.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_LutNodeHasChanged( Lut_Man_t * p, int iNode )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pTemp;
    int i;
    vNodes = Vec_VecEntry( p->vVisited, iNode );
    if ( Vec_PtrSize(vNodes) == 0 )
        return 1;
    Vec_PtrForEachEntry( vNodes, pTemp, i )
    {
        // check if the node has changed
        pTemp = Abc_NtkObj( p->pNtk, (int)pTemp );
        if ( pTemp == NULL )
            return 1;
        // check if the number of fanouts has changed
//        if ( Abc_ObjFanoutNum(pTemp) != (int)Vec_PtrEntry(vNodes, i+1) )
//            return 1;
        i++;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if at least one entry has changed.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_LutNodeRecordImpact( Lut_Man_t * p )
{
    Lut_Cut_t * pCut;
    Vec_Ptr_t * vNodes = Vec_VecEntry( p->vVisited, p->pObj->Id );
    Abc_Obj_t * pNode;
    int i, k;
    // collect the nodes that impact the given node
    Vec_PtrClear( vNodes );
    for ( i = 0; i < p->nCuts; i++ )
    {
        pCut = p->pCuts + i;
        for ( k = 0; k < (int)pCut->nLeaves; k++ )
        {
            pNode = Abc_NtkObj( p->pNtk, pCut->pLeaves[k] );
            if ( pNode->fMarkC )
                continue;
            pNode->fMarkC = 1;
            Vec_PtrPush( vNodes, (void *)pNode->Id );
            Vec_PtrPush( vNodes, (void *)Abc_ObjFanoutNum(pNode) );
        }
    }
    // clear the marks
    Vec_PtrForEachEntry( vNodes, pNode, i )
    {
        pNode = Abc_NtkObj( p->pNtk, (int)pNode );
        pNode->fMarkC = 0;
        i++;
    }
//printf( "%d ", Vec_PtrSize(vNodes) );
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the cut has structural DSD.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_LutNodeCutsCheckDsd( Lut_Man_t * p, Lut_Cut_t * pCut )
{
    Abc_Obj_t * pObj, * pFanin;
    int i, k, nCands, fLeavesOnly, RetValue;
    assert( pCut->nLeaves > 0 );
    // clear ref counters
    memset( p->pRefs, 0, sizeof(int) * pCut->nLeaves );
    // mark cut leaves
    Abc_LutCutForEachLeaf( p->pNtk, pCut, pObj, i )
    {
        assert( pObj->fMarkA == 0 );
        pObj->fMarkA = 1;
        pObj->pCopy = (void *)i;
    }
    // ref leaves pointed from the internal nodes
    nCands = 0;
    Abc_LutCutForEachNode( p->pNtk, pCut, pObj, i )
    {
        fLeavesOnly = 1;
        Abc_ObjForEachFanin( pObj, pFanin, k )
            if ( pFanin->fMarkA )
                p->pRefs[(int)pFanin->pCopy]++;
            else
                fLeavesOnly = 0;
        if ( fLeavesOnly )
            p->pCands[nCands++] = pObj->Id;
    }
    // look at the nodes that only point to the leaves
    RetValue = 0;
    for ( i = 0; i < nCands; i++ )
    {
        pObj = Abc_NtkObj( p->pNtk, p->pCands[i] );
        Abc_ObjForEachFanin( pObj, pFanin, k )
        {
            assert( pFanin->fMarkA == 1 );
            if ( p->pRefs[(int)pFanin->pCopy] > 1 )
                break;
        }
        if ( k == Abc_ObjFaninNum(pObj) )
        {
            RetValue = 1;
            break;
        }
    }
    // unmark cut leaves
    Abc_LutCutForEachLeaf( p->pNtk, pCut, pObj, i )
        pObj->fMarkA = 0;
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if pDom is contained in pCut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_LutNodeCutsOneDominance( Lut_Cut_t * pDom, Lut_Cut_t * pCut )
{
    int i, k;
    for ( i = 0; i < (int)pDom->nLeaves; i++ )
    {
        for ( k = 0; k < (int)pCut->nLeaves; k++ )
            if ( pDom->pLeaves[i] == pCut->pLeaves[k] )
                break;
        if ( k == (int)pCut->nLeaves ) // node i in pDom is not contained in pCut
            return 0;
    }
    // every node in pDom is contained in pCut
    return 1;
}

/**Function*************************************************************

  Synopsis    [Check if the cut exists.]

  Description [Returns 1 if the cut exists.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_LutNodeCutsOneFilter( Lut_Cut_t * pCuts, int nCuts, Lut_Cut_t * pCutNew )
{
    Lut_Cut_t * pCut;
    int i, k;
    assert( pCutNew->uSign[0] || pCutNew->uSign[1] );
    // try to find the cut
    for ( i = 0; i < nCuts; i++ )
    {
        pCut = pCuts + i;
        if ( pCut->nLeaves == 0 )
            continue;
        if ( pCut->nLeaves == pCutNew->nLeaves )
        {
            if ( pCut->uSign[0] == pCutNew->uSign[0] && pCut->uSign[1] == pCutNew->uSign[1] )
            {
                for ( k = 0; k < (int)pCutNew->nLeaves; k++ )
                    if ( pCut->pLeaves[k] != pCutNew->pLeaves[k] )
                        break;
                if ( k == (int)pCutNew->nLeaves )
                    return 1;
            }
            continue;
        }
        if ( pCut->nLeaves < pCutNew->nLeaves )
        {
            // skip the non-contained cuts
            if ( (pCut->uSign[0] & pCutNew->uSign[0]) != pCut->uSign[0] )
                continue;
            if ( (pCut->uSign[1] & pCutNew->uSign[1]) != pCut->uSign[1] )
                continue;
            // check containment seriously
            if ( Abc_LutNodeCutsOneDominance( pCut, pCutNew ) )
                return 1;
            continue;
        }
        // check potential containment of other cut

        // skip the non-contained cuts
        if ( (pCut->uSign[0] & pCutNew->uSign[0]) != pCutNew->uSign[0] )
            continue;
        if ( (pCut->uSign[1] & pCutNew->uSign[1]) != pCutNew->uSign[1] )
            continue;
        // check containment seriously
        if ( Abc_LutNodeCutsOneDominance( pCutNew, pCut ) )
            pCut->nLeaves = 0; // removed
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Prints the given cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_LutNodePrintCut( Lut_Man_t * p, Lut_Cut_t * pCut )
{
    Abc_Obj_t * pObj;
    int i;
    printf( "LEAVES:\n" );
    Abc_LutCutForEachLeaf( p->pNtk, pCut, pObj, i )
    {
        Abc_ObjPrint( stdout, pObj );
    }
    printf( "NODES:\n" );
    Abc_LutCutForEachNode( p->pNtk, pCut, pObj, i )
    {
        Abc_ObjPrint( stdout, pObj );
        assert( Abc_ObjIsNode(pObj) );
    }
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    [Set the cut signature.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_LutNodeCutSignature( Lut_Cut_t * pCut )
{
    unsigned i;
    pCut->uSign[0] = pCut->uSign[1] = 0;
    for ( i = 0; i < pCut->nLeaves; i++ )
    {
        pCut->uSign[(pCut->pLeaves[i] & 32) > 0] |= (1 << (pCut->pLeaves[i] & 31));
        if ( i != pCut->nLeaves - 1 )
            assert( pCut->pLeaves[i] < pCut->pLeaves[i+1] );
    }
}


/**Function*************************************************************

  Synopsis    [Computes the set of all cuts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_LutNodeCutsOne( Lut_Man_t * p, Lut_Cut_t * pCut, int Node )
{
    Lut_Cut_t * pCutNew;
    Abc_Obj_t * pObj, * pFanin;
    int i, k, j, nLeavesNew;

    // check if the cut can stand adding one more internal node
    if ( pCut->nNodes == LUT_SIZE_MAX )
        return;

    // if the node is a PI, quit
    pObj = Abc_NtkObj( p->pNtk, Node );
    if ( Abc_ObjIsCi(pObj) )
        return;
    assert( Abc_ObjIsNode(pObj) );
    assert( Abc_ObjFaninNum(pObj) <= p->pPars->nLutSize );

    // if the node is not in the MFFC, check the limit
    if ( !Abc_NodeIsTravIdCurrent(pObj) )
    {
        if ( (int)pCut->nNodesDup == p->pPars->nLutsOver )
            return;
        assert( (int)pCut->nNodesDup < p->pPars->nLutsOver );
    }

    // check the possibility of adding this node using the signature
    nLeavesNew = pCut->nLeaves - 1;
    Abc_ObjForEachFanin( pObj, pFanin, i )
    {
        if ( (pCut->uSign[(pFanin->Id & 32) > 0] & (1 << (pFanin->Id & 31))) )
            continue;
        if ( ++nLeavesNew > p->pPars->nVarsMax )
            return;
    }

    // initialize the set of leaves to the nodes in the cut
    assert( p->nCuts < LUT_CUTS_MAX );
    pCutNew = p->pCuts + p->nCuts;
/*
if ( p->pObj->Id == 31 && Node == 38 && pCut->pNodes[0] == 31 && pCut->pNodes[1] == 34 && pCut->pNodes[2] == 35 )//p->nCuts == 48 )
{
    int x = 0;
    printf( "Start:\n" );
    Abc_LutNodePrintCut( p, pCut );
}
*/
    pCutNew->nLeaves = 0;
    for ( i = 0; i < (int)pCut->nLeaves; i++ )
        if ( pCut->pLeaves[i] != Node )
            pCutNew->pLeaves[pCutNew->nLeaves++] = pCut->pLeaves[i];

    // add new nodes
    Abc_ObjForEachFanin( pObj, pFanin, i )
    {
        // find the place where this node belongs
        for ( k = 0; k < (int)pCutNew->nLeaves; k++ )
            if ( pCutNew->pLeaves[k] >= pFanin->Id )
                break;
        if ( k < (int)pCutNew->nLeaves && pCutNew->pLeaves[k] == pFanin->Id )
            continue;
        // check if there is room
        if ( (int)pCutNew->nLeaves == p->pPars->nVarsMax )
            return;
        // move all the nodes
        for ( j = pCutNew->nLeaves; j > k; j-- )
            pCutNew->pLeaves[j] = pCutNew->pLeaves[j-1];
        pCutNew->pLeaves[k] = pFanin->Id;
        pCutNew->nLeaves++;
        assert( pCutNew->nLeaves <= LUT_SIZE_MAX );
    }
    
    // skip the contained cuts
    Abc_LutNodeCutSignature( pCutNew );
    if ( Abc_LutNodeCutsOneFilter( p->pCuts, p->nCuts, pCutNew ) )
        return;

    // update the set of internal nodes
    assert( pCut->nNodes < LUT_SIZE_MAX );
    memcpy( pCutNew->pNodes, pCut->pNodes, pCut->nNodes * sizeof(int) );
    pCutNew->nNodes = pCut->nNodes;
    pCutNew->pNodes[ pCutNew->nNodes++ ] = Node;

    // add the marked node
    pCutNew->nNodesDup = pCut->nNodesDup + !Abc_NodeIsTravIdCurrent(pObj);
/*
if ( p->pObj->Id == 31 && Node == 38 )//p->nCuts == 48 )
{
    int x = 0;
    printf( "Finish:\n" );
    Abc_LutNodePrintCut( p, pCutNew );
}
*/
    // add the cut to storage
    assert( p->nCuts < LUT_CUTS_MAX );
    p->nCuts++;

    assert( pCut->nNodes <= p->nMffc + pCutNew->nNodesDup );
}

/**Function*************************************************************

  Synopsis    [Computes the set of all cuts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_LutNodeCuts( Lut_Man_t * p )
{
    Lut_Cut_t * pCut, * pCut2;
    int i, k, Temp, nMffc, fChanges;

    // mark the MFFC of the node with the current trav ID
    nMffc = p->nMffc = Abc_NodeMffcLabel( p->pObj );
    assert( nMffc > 0 );
    if ( nMffc == 1 )
        return 0;

    // initialize the first cut
    pCut = p->pCuts; p->nCuts = 1;
    pCut->nNodes = 0; 
    pCut->nNodesDup = 0;
    pCut->nLeaves = 1;
    pCut->pLeaves[0] = p->pObj->Id;
    // assign the signature
    Abc_LutNodeCutSignature( pCut );

    // perform the cut computation
    for ( i = 0; i < p->nCuts; i++ )
    {
        pCut = p->pCuts + i;
        if ( pCut->nLeaves == 0 )
            continue;
        // try to expand the fanins of this cut
        for ( k = 0; k < (int)pCut->nLeaves; k++ )
        {
            // create a new cut
            Abc_LutNodeCutsOne( p, pCut, pCut->pLeaves[k] );
            // quit if the number of cuts has exceeded the limit
            if ( p->nCuts == LUT_CUTS_MAX )
                break;
        }
        if ( p->nCuts == LUT_CUTS_MAX )
            break;
    }
    if ( p->nCuts == LUT_CUTS_MAX ) 
        p->nNodesOver++;

    // record the impact of this node
    if ( p->pPars->fSatur )
        Abc_LutNodeRecordImpact( p );

    // compress the cuts by removing empty ones, those with negative Weight, and decomposable ones
    p->nEvals = 0;
    for ( i = 0; i < p->nCuts; i++ )
    {
        pCut = p->pCuts + i;
        if ( pCut->nLeaves < 2 )
            continue;
        // compute the number of LUTs neede to implement this cut
        // V = N * (K-1) + 1  ~~~~~  N = Ceiling[(V-1)/(K-1)] = (V-1)/(K-1) + [(V-1)%(K-1) > 0]
        pCut->nLuts = (pCut->nLeaves-1)/(p->pPars->nLutSize-1) + ( (pCut->nLeaves-1)%(p->pPars->nLutSize-1) > 0 ); 
        pCut->Weight = (float)1.0 * (pCut->nNodes - pCut->nNodesDup) / pCut->nLuts; //p->pPars->nLutsMax;
        if ( pCut->Weight <= 1.0 )
            continue;
        pCut->fHasDsd = Abc_LutNodeCutsCheckDsd( p, pCut );
        if ( pCut->fHasDsd )
            continue;
        p->pEvals[p->nEvals++] = i;
    }
    if ( p->nEvals == 0 )
        return 0;

    // sort the cuts by Weight
    do {
        fChanges = 0;
        for ( i = 0; i < p->nEvals - 1; i++ )
        {
            pCut = p->pCuts + p->pEvals[i];
            pCut2 = p->pCuts + p->pEvals[i+1];
            if ( pCut->Weight >= pCut2->Weight )
                continue;
            Temp = p->pEvals[i];
            p->pEvals[i] = p->pEvals[i+1];
            p->pEvals[i+1] = Temp;
            fChanges = 1;
        }
    } while ( fChanges );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Computes the truth able of one cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned * Abc_LutCutTruth_rec( Hop_Man_t * pMan, Hop_Obj_t * pObj, int nVars, Vec_Ptr_t * vTtNodes, int * iCount )
{
    unsigned * pTruth, * pTruth0, * pTruth1;
    assert( !Hop_IsComplement(pObj) );
    if ( pObj->pData )
    {
        assert( ((unsigned)pObj->pData) & 0xffff0000 );
        return pObj->pData;
    }
    // get the plan for a new truth table
    pTruth = Vec_PtrEntry( vTtNodes, (*iCount)++ );
    if ( Hop_ObjIsConst1(pObj) )
        Extra_TruthFill( pTruth, nVars );
    else
    {
        assert( Hop_ObjIsAnd(pObj) );
        // compute the truth tables of the fanins
        pTruth0 = Abc_LutCutTruth_rec( pMan, Hop_ObjFanin0(pObj), nVars, vTtNodes, iCount );
        pTruth1 = Abc_LutCutTruth_rec( pMan, Hop_ObjFanin1(pObj), nVars, vTtNodes, iCount );
        // creat the truth table of the node
        Extra_TruthAndPhase( pTruth, pTruth0, pTruth1, nVars, Hop_ObjFaninC0(pObj), Hop_ObjFaninC1(pObj) );
    }
    pObj->pData = pTruth;
    return pTruth;
}

/**Function*************************************************************

  Synopsis    [Computes the truth able of one cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned * Abc_LutCutTruth( Lut_Man_t * p, Lut_Cut_t * pCut )
{
    Hop_Man_t * pManHop = p->pNtk->pManFunc;
    Hop_Obj_t * pObjHop;
    Abc_Obj_t * pObj, * pFanin;
    unsigned * pTruth;
    int i, k, iCount = 0;
//    Abc_LutNodePrintCut( p, pCut );

    // initialize the leaves
    Abc_LutCutForEachLeaf( p->pNtk, pCut, pObj, i )
        pObj->pCopy = Vec_PtrEntry( p->vTtElems, i );

    // construct truth table in the topological order
    Abc_LutCutForEachNodeReverse( p->pNtk, pCut, pObj, i )
    {
        // get the local AIG
        pObjHop = Hop_Regular(pObj->pData);
        // clean the data field of the nodes in the AIG subgraph
        Hop_ObjCleanData_rec( pObjHop );
        // set the initial truth tables at the fanins
        Abc_ObjForEachFanin( pObj, pFanin, k )
        {
            assert( ((unsigned)pFanin->pCopy) & 0xffff0000 );
            Hop_ManPi( pManHop, k )->pData = pFanin->pCopy;
        }
        // compute the truth table of internal nodes
        pTruth = Abc_LutCutTruth_rec( pManHop, pObjHop, pCut->nLeaves, p->vTtNodes, &iCount );
        if ( Hop_IsComplement(pObj->pData) )
            Extra_TruthNot( pTruth, pTruth, pCut->nLeaves );
        // set the truth table at the node
        pObj->pCopy = (Abc_Obj_t *)pTruth;
    }

    return pTruth;
}



/**Function*************************************************************

  Synopsis    [Prepares the mapping manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_LutIfManStart( Lut_Man_t * p )
{
    If_Par_t * pPars;
    assert( p->pIfMan == NULL );
    // set defaults
    pPars = ALLOC( If_Par_t, 1 );
    memset( pPars, 0, sizeof(If_Par_t) );
    // user-controlable paramters
    pPars->nLutSize    =  p->pPars->nLutSize;
    pPars->nCutsMax    =  8;
    pPars->nFlowIters  =  0; // 1
    pPars->nAreaIters  =  0; // 1 
    pPars->DelayTarget = -1;
    pPars->fPreprocess =  0;
    pPars->fArea       =  1;
    pPars->fFancy      =  0;
    pPars->fExpRed     =  0; //
    pPars->fLatchPaths =  0;
    pPars->fSeqMap     =  0;
    pPars->fVerbose    =  0;
    // internal parameters
    pPars->fTruth      =  0;
    pPars->fUsePerm    =  0; 
    pPars->nLatches    =  0;
    pPars->pLutLib     =  NULL; // Abc_FrameReadLibLut();
    pPars->pTimesArr   =  NULL; 
    pPars->pTimesArr   =  NULL;   
    pPars->fUseBdds    =  0;
    pPars->fUseSops    =  0;
    pPars->fUseCnfs    =  0;
    pPars->fUseMv      =  0;
    // start the mapping manager and set its parameters
    p->pIfMan = If_ManStart( pPars );
    If_ManSetupSetAll( p->pIfMan, 1000 );
    p->pIfMan->pPars->pTimesArr = ALLOC( float, 32 );
}

/**Function*************************************************************

  Synopsis    [Transforms the decomposition graph into the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
If_Obj_t * Abc_LutIfManMapPrimeInternal( If_Man_t * pIfMan, Kit_Graph_t * pGraph )
{
    Kit_Node_t * pNode;
    If_Obj_t * pAnd0, * pAnd1;
    int i;
    // check for constant function
    if ( Kit_GraphIsConst(pGraph) )
        return If_ManConst1(pIfMan);
    // check for a literal
    if ( Kit_GraphIsVar(pGraph) )
        return Kit_GraphVar(pGraph)->pFunc;
    // build the AIG nodes corresponding to the AND gates of the graph
    Kit_GraphForEachNode( pGraph, pNode, i )
    {
        pAnd0 = Kit_GraphNode(pGraph, pNode->eEdge0.Node)->pFunc; 
        pAnd1 = Kit_GraphNode(pGraph, pNode->eEdge1.Node)->pFunc; 
        pNode->pFunc = If_ManCreateAnd( pIfMan, 
            If_Regular(pAnd0), If_IsComplement(pAnd0) ^ pNode->eEdge0.fCompl, 
            If_Regular(pAnd1), If_IsComplement(pAnd1) ^ pNode->eEdge1.fCompl );
    }
    return pNode->pFunc;
}

/**Function*************************************************************

  Synopsis    [Strashes one logic node using its SOP.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
If_Obj_t * Abc_LutIfManMapPrime( If_Man_t * pIfMan, If_Obj_t ** ppLeaves, Kit_Graph_t * pGraph )
{
    Kit_Node_t * pNode;
    If_Obj_t * pRes;
    int i;
    // collect the fanins
    Kit_GraphForEachLeaf( pGraph, pNode, i )
        pNode->pFunc = ppLeaves[i];
    // perform strashing
    pRes = Abc_LutIfManMapPrimeInternal( pIfMan, pGraph );
    return If_NotCond( pRes, Kit_GraphIsComplement(pGraph) );
}

/**Function*************************************************************

  Synopsis    [Creates the choice node for the given number.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
If_Obj_t * Abc_LutIfManChoiceOne( If_Man_t * pIfMan, If_Obj_t ** pNodes, int iNode, int nLeaves, int fXor )
{
    If_Obj_t * pPrev, * pAnd, * pOne, * pMany;
    int v;
    pPrev = NULL;
    for ( v = 0; v < nLeaves; v++ )
    {
        if ( (iNode & (1 << v)) == 0 )
            continue;
        pOne  = pNodes[1 << v];
        pMany = pNodes[iNode & ~(1 << v)];
        if ( fXor )
            pAnd = If_ManCreateXnor( pIfMan, If_Regular(pOne), pMany ); 
        else
            pAnd = If_ManCreateAnd( pIfMan, If_Regular(pOne), If_IsComplement(pOne), If_Regular(pMany), If_IsComplement(pMany) ); 
        pAnd->pEquiv = pPrev;
        pPrev = pAnd;
    }
    return pPrev;
}

/**Function*************************************************************

  Synopsis    [Creates the choice node for the given number.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
If_Obj_t * Abc_LutIfManChoice( If_Man_t * pIfMan, If_Obj_t ** pLeaves, int nLeaves, int fXor )
{
    If_Obj_t ** pNodes, * pRes;
    int v, m, nMints;
    // allocate room for nodes
    assert( nLeaves >= 2 );
    nMints = (1 << nLeaves);
    pNodes = ALLOC( If_Obj_t *, nMints );
    // set elementary ones
    pNodes[0] = NULL;
    for ( v = 0; v < nLeaves; v++ )
        pNodes[1<<v] = pLeaves[v];
    // set triples and so on
    for ( v = 2; v <= nLeaves; v++ )
        for ( m = 0; m < nMints; m++ )
            if ( Kit_WordCountOnes(m) == v )
            {
                pNodes[m] = Abc_LutIfManChoiceOne( pIfMan, pNodes, m, nLeaves, fXor );
                if ( v > 2 )
                    If_ManCreateChoice( pIfMan, pNodes[m] );
            }
    pRes = pNodes[nMints-1];
    free( pNodes );
    return pRes;
}

/**Function*************************************************************

  Synopsis    [Creates the choice node for the given number.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
If_Obj_t * Abc_LutIfManPart_rec( If_Man_t * pIfMan, If_Obj_t ** pLeaves, int nLeaves, int fXor )
{
    If_Obj_t * pObjNew1, * pObjNew2;
    if ( nLeaves <= 5 )
        return Abc_LutIfManChoice( pIfMan, pLeaves, nLeaves, fXor );
    pObjNew1 = Abc_LutIfManPart_rec( pIfMan, pLeaves,               nLeaves / 2,             fXor );
    pObjNew2 = Abc_LutIfManPart_rec( pIfMan, pLeaves + nLeaves / 2, nLeaves - (nLeaves / 2), fXor );
    if ( fXor )
        return If_ManCreateXnor( pIfMan, pObjNew1, pObjNew2 ); 
    else
        return If_ManCreateAnd( pIfMan, pObjNew1, 0, pObjNew2, 0 ); 
}

/**Function*************************************************************

  Synopsis    [Prepares the mapping manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
If_Obj_t * Abc_LutIfManMap_New_rec( Lut_Man_t * p, Kit_DsdNtk_t * pNtk, int iLit )
{
    Kit_Graph_t * pGraph;
    Kit_DsdObj_t * pObj;
    If_Obj_t * pObjNew, * pFansNew[16];
    unsigned i, iLitFanin, fCompl;

    // remember the complement
    fCompl = Kit_DsdLitIsCompl(iLit); 
    iLit = Kit_DsdLitRegular(iLit); 
    assert( !Kit_DsdLitIsCompl(iLit) );

    // consider the case of simple gate
    pObj = Kit_DsdNtkObj( pNtk, Kit_DsdLit2Var(iLit) );
    if ( pObj == NULL )
    {
        pObjNew = If_ManCi( p->pIfMan, Kit_DsdLit2Var(iLit) );
        return If_NotCond( pObjNew, fCompl );
    }

    // solve for the inputs
    Kit_DsdObjForEachFanin( pNtk, pObj, iLitFanin, i )
        pFansNew[i] = Abc_LutIfManMap_New_rec( p, pNtk, iLitFanin );

    // generate choices for multi-input gate
    if ( pObj->Type == KIT_DSD_AND || pObj->Type == KIT_DSD_XOR )
    {
        assert( pObj->nFans >= 2 );
        if ( pObj->Type == KIT_DSD_XOR )
        {
            fCompl ^= ((pObj->nFans-1) & 1); // flip if the number of operations is odd
            for ( i = 0; i < pObj->nFans; i++ )
            {
                fCompl ^= If_IsComplement(pFansNew[i]);
                pFansNew[i] = If_Regular(pFansNew[i]);
            }
        }
        pObjNew = Abc_LutIfManPart_rec( p->pIfMan, pFansNew, pObj->nFans, pObj->Type == KIT_DSD_XOR );
        return If_NotCond( pObjNew, fCompl );
    }
    assert( pObj->Type == KIT_DSD_PRIME );

    // derive the factored form
    pGraph = Kit_TruthToGraph( Kit_DsdObjTruth(pObj), pObj->nFans, p->vCover );
    // convert factored form into the AIG
    pObjNew = Abc_LutIfManMapPrime( p->pIfMan, pFansNew, pGraph ); 
    Kit_GraphFree( pGraph );
    return If_NotCond( pObjNew, fCompl );
}

/**Function*************************************************************

  Synopsis    [Prepares the mapping manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
If_Obj_t * Abc_LutIfManMap_rec( Lut_Man_t * p, Kit_DsdNtk_t * pNtk, int iLit )
{
    Kit_Graph_t * pGraph;
    Kit_DsdObj_t * pObj;
    If_Obj_t * pObjNew, * pFansNew[16];
    unsigned i, iLitFanin, fCompl;

    // remember the complement
    fCompl = Kit_DsdLitIsCompl(iLit); 
    iLit = Kit_DsdLitRegular(iLit); 
    assert( !Kit_DsdLitIsCompl(iLit) );

    // consider the case of simple gate
    pObj = Kit_DsdNtkObj( pNtk, Kit_DsdLit2Var(iLit) );
    if ( pObj == NULL )
    {
        pObjNew = If_ManCi( p->pIfMan, Kit_DsdLit2Var(iLit) );
        return If_NotCond( pObjNew, fCompl );
    }
    if ( pObj->Type == KIT_DSD_AND )
    {
        assert( pObj->nFans == 2 );
        pFansNew[0] = Abc_LutIfManMap_rec( p, pNtk, pObj->pFans[0] );
        pFansNew[1] = Abc_LutIfManMap_rec( p, pNtk, pObj->pFans[1] );
        if ( pFansNew[0] == NULL || pFansNew[1] == NULL )
            return NULL;
        pObjNew = If_ManCreateAnd( p->pIfMan, If_Regular(pFansNew[0]), If_IsComplement(pFansNew[0]), If_Regular(pFansNew[1]), If_IsComplement(pFansNew[1]) ); 
        return If_NotCond( pObjNew, fCompl );
    }
    if ( pObj->Type == KIT_DSD_XOR )
    {
        assert( pObj->nFans == 2 );
        pFansNew[0] = Abc_LutIfManMap_rec( p, pNtk, pObj->pFans[0] );
        pFansNew[1] = Abc_LutIfManMap_rec( p, pNtk, pObj->pFans[1] );
        if ( pFansNew[0] == NULL || pFansNew[1] == NULL )
            return NULL;
        fCompl ^= 1 ^ If_IsComplement(pFansNew[0]) ^ If_IsComplement(pFansNew[1]);
        pObjNew = If_ManCreateXnor( p->pIfMan, If_Regular(pFansNew[0]), If_Regular(pFansNew[1]) );
        return If_NotCond( pObjNew, fCompl );
    }
    assert( pObj->Type == KIT_DSD_PRIME );
    p->nBlocks[pObj->nFans]++;

    // solve for the inputs
    Kit_DsdObjForEachFanin( pNtk, pObj, iLitFanin, i )
    {
        pFansNew[i] = Abc_LutIfManMap_rec( p, pNtk, iLitFanin );
        if ( pFansNew[i] == NULL )
            return NULL;
    }

    // derive the factored form
    pGraph = Kit_TruthToGraph( Kit_DsdObjTruth(pObj), pObj->nFans, p->vCover );
    if ( pGraph == NULL )
        return NULL;
    // convert factored form into the AIG
    pObjNew = Abc_LutIfManMapPrime( p->pIfMan, pFansNew, pGraph ); 
    Kit_GraphFree( pGraph );
    return If_NotCond( pObjNew, fCompl );
}

/**Function*************************************************************

  Synopsis    [Prepares the mapping manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_LutCutUpdate( Lut_Man_t * p, Lut_Cut_t * pCut, Kit_DsdNtk_t * pNtk )
{
    extern Abc_Obj_t * Abc_NodeFromIf_rec( Abc_Ntk_t * pNtkNew, If_Man_t * pIfMan, If_Obj_t * pIfObj, Vec_Int_t * vCover );
    Kit_DsdObj_t * pRoot;
    If_Obj_t * pDriver;
    Abc_Obj_t * pLeaf, * pObjNew;
    int nGain, i;

    // check special cases
    pRoot = Kit_DsdNtkRoot( pNtk );
    if ( pRoot->Type == KIT_DSD_CONST1 )
    {
        pObjNew = Abc_NtkCreateNodeConst1( p->pNtk );
        pObjNew = Abc_ObjNotCond( pObjNew, Kit_DsdLitIsCompl(pNtk->Root) );

        // perform replacement
        pObjNew->Level = p->pObj->Level;
        Abc_ObjReplace( p->pObj, pObjNew );
        Res_UpdateNetworkLevel( pObjNew, p->vLevels );
        p->nGainTotal += pCut->nNodes - pCut->nNodesDup;
        return 1;
    }
    if ( pRoot->Type == KIT_DSD_VAR )
    {
        pObjNew = Abc_NtkObj( p->pNtk, pCut->pLeaves[ Kit_DsdLit2Var(pRoot->pFans[0]) ] );
        pObjNew = Abc_ObjNotCond( pObjNew, Kit_DsdLitIsCompl(pNtk->Root) ^ Kit_DsdLitIsCompl(pRoot->pFans[0]) );

        // perform replacement
        pObjNew->Level = p->pObj->Level;
        Abc_ObjReplace( p->pObj, pObjNew );
        Res_UpdateNetworkLevel( pObjNew, p->vLevels );
        p->nGainTotal += pCut->nNodes - pCut->nNodesDup;
        return 1;
    }
    assert( pRoot->Type == KIT_DSD_AND || pRoot->Type == KIT_DSD_XOR || pRoot->Type == KIT_DSD_PRIME );

    // start the mapping manager
    if ( p->pIfMan == NULL )
        Abc_LutIfManStart( p );

    // prepare the mapping manager
    If_ManRestart( p->pIfMan );
    // create the PI variables
    for ( i = 0; i < p->pPars->nVarsMax; i++ )
        If_ManCreateCi( p->pIfMan );
    // set the arrival times
    Abc_LutCutForEachLeaf( p->pNtk, pCut, pLeaf, i )
        p->pIfMan->pPars->pTimesArr[i] = (float)pLeaf->Level;
    // prepare the PI cuts
    If_ManSetupCiCutSets( p->pIfMan );
    // create the internal nodes
//    pDriver = Abc_LutIfManMap_New_rec( p, pNtk, pNtk->Root );
    pDriver = Abc_LutIfManMap_rec( p, pNtk, pNtk->Root );
    if ( pDriver == NULL )
        return 0;
    // create the PO node
    If_ManCreateCo( p->pIfMan, If_Regular(pDriver), 0 );

    // perform mapping
    p->pIfMan->pPars->fAreaOnly = 1;
    If_ManPerformMappingComb( p->pIfMan );

    // compute the gain in area
    nGain = pCut->nNodes - pCut->nNodesDup - (int)p->pIfMan->AreaGlo;
    if ( p->pPars->fVeryVerbose )
        printf( "       Mffc = %2d. Mapped = %2d. Gain = %3d. Depth increase = %d.\n", 
            pCut->nNodes - pCut->nNodesDup, (int)p->pIfMan->AreaGlo, nGain, (int)p->pIfMan->RequiredGlo - (int)p->pObj->Level );

    // quit if there is no gain
    if ( !(nGain > 0 || (p->pPars->fZeroCost && nGain == 0)) )
        return 0;
    // quit if depth increases too much
    if ( (int)p->pIfMan->RequiredGlo - (int)p->pObj->Level > p->pPars->nGrowthLevel )
        return 0;

    // perform replacement
    p->nGainTotal += nGain;
    p->nChanges++;

    // prepare the mapping manager
    If_ManCleanNodeCopy( p->pIfMan );
    If_ManCleanCutData( p->pIfMan );
    // set the PIs of the cut
    Abc_LutCutForEachLeaf( p->pNtk, pCut, pLeaf, i )
        If_ObjSetCopy( If_ManCi(p->pIfMan, i), pLeaf );
    // get the area of mapping
    pObjNew = Abc_NodeFromIf_rec( p->pNtk, p->pIfMan, If_Regular(pDriver), p->vCover );
    pObjNew->pData = Hop_NotCond( pObjNew->pData, If_IsComplement(pDriver) );

    // perform replacement
    pObjNew->Level = p->pObj->Level;
    Abc_ObjReplace( p->pObj, pObjNew );
    Res_UpdateNetworkLevel( pObjNew, p->vLevels );
    return 1;
}



/**Function*************************************************************

  Synopsis    [Performs resynthesis for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_LutResynthesizeNode( Lut_Man_t * p )
{
    extern void Kit_DsdTest( unsigned * pTruth, int nVars );
    extern int Kit_DsdEval( unsigned * pTruth, int nVars, int nLutSize );

    Kit_DsdNtk_t * pDsdNtk;
    Lut_Cut_t * pCut;
    unsigned * pTruth;
    void * pDsd = NULL;
//    int Result, Gain;
    int i, RetValue, clk;

    // compute the cuts
clk = clock();
    if ( !Abc_LutNodeCuts( p ) )
    {
p->timeCuts += clock() - clk;
        return 0;
    }
p->timeCuts += clock() - clk;

    if ( p->pPars->fVeryVerbose )
    printf( "Node %5d : Mffc size = %5d. Cuts = %5d.\n", p->pObj->Id, p->nMffc, p->nEvals );
    // try the good cuts
    p->nCutsTotal  += p->nCuts;
    p->nCutsUseful += p->nEvals;
    for ( i = 0; i < p->nEvals; i++ )
    {
        // get the cut
        pCut = p->pCuts + p->pEvals[i];

        // compute the truth table
clk = clock();
        pTruth = Abc_LutCutTruth( p, pCut );
p->timeTruth += clock() - clk;

/*
        // evaluate the result of decomposition        
        Result = Kit_DsdEval( pTruth, pCut->nLeaves, 3 );
        // calculate expected gain
        Gain = (Result < 0) ? -1 : pCut->nNodes - pCut->nNodesDup - Result;
        if ( !(Gain < 0 || (Gain == 0 && p->pPars->fZeroCost)) )
            continue;
*/

clk = clock();
//        Kit_DsdTest( pTruth, pCut->nLeaves );
        pDsdNtk = Kit_DsdDeriveNtk( pTruth, pCut->nLeaves, p->pPars->nLutSize );
p->timeEval += clock() - clk;

        if ( Kit_DsdNtkRoot(pDsdNtk)->nFans == 16 ) // skip 16-input non-DSD because ISOP will not work
        {
            Kit_DsdNtkFree( pDsdNtk );
            continue;
        }
/*
        // skip large non-DSD blocks
        if ( Kit_DsdNonDsdSizeMax(pDsdNtk) > 7 )
        {
            Kit_DsdNtkFree( pDsdNtk );
            continue;
        }
*/
        if ( p->pPars->fVeryVerbose )
        {
//            Extra_PrintHexadecimal( stdout, pTruth, pCut->nLeaves ); printf( "\n" );
//            printf( "    Cut %2d : L = %2d. S = %2d. Vol = %2d. Q = %d. N = %d. W = %4.2f. New = %2d. Gain = %2d.\n", 
//                i, pCut->nLeaves, Extra_TruthSupportSize(pTruth, pCut->nLeaves), pCut->nNodes, pCut->nNodesDup, pCut->nLuts, pCut->Weight, Result, Gain );
            printf( "  C%02d: L= %2d/%2d  V= %2d/%d  N= %d  W= %4.2f  ", 
                i, pCut->nLeaves, Extra_TruthSupportSize(pTruth, pCut->nLeaves), pCut->nNodes, pCut->nNodesDup, pCut->nLuts, pCut->Weight );
            Kit_DsdPrint( stdout, pDsdNtk );
        }

        // update the network
clk = clock();
        RetValue = Abc_LutCutUpdate( p, pCut, pDsdNtk );
        Kit_DsdNtkFree( pDsdNtk );
p->timeMap += clock() - clk;
        if ( RetValue )
            break;
    }
    return 1;
}


/**Function*************************************************************

  Synopsis    [Performs resynthesis for one network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_LutResynthesize( Abc_Ntk_t * pNtk, Lut_Par_t * pPars )
{
    ProgressBar * pProgress;
    Lut_Man_t * p;
    Abc_Obj_t * pObj;
    double Delta;
    int i, Iter, nNodes, nNodesPrev, clk = clock();
    assert( Abc_NtkIsLogic(pNtk) );

    // get the number of inputs
    pPars->nLutSize = Abc_NtkGetFaninMax( pNtk );
    pPars->nVarsMax = pPars->nLutsMax * (pPars->nLutSize - 1) + 1; // V = N * (K-1) + 1
    if ( pPars->fVerbose )
    {
        printf( "Resynthesis for %d %d-LUTs with %d non-MFFC LUTs, %d crossbars, and %d-input cuts.\n",
            pPars->nLutsMax, pPars->nLutSize, pPars->nLutsOver, pPars->nVarsShared, pPars->nVarsMax );
    }
    if ( pPars->nVarsMax > 16 )
    {
        printf( "Currently cannot handle resynthesis with more than %d inputs (reduce \"-N <num>\").\n", 16 );
        return 1;
    }
 
    // convert logic to AIGs
    Abc_NtkToAig( pNtk );

    // start the manager
    p = Abc_LutManStart( pPars );
    p->pNtk = pNtk;
    p->nNodesTotal = Abc_NtkNodeNum(pNtk);
    p->vLevels = Vec_VecStart( 3 * Abc_NtkLevel(pNtk) ); // computes levels of all nodes
    if ( p->pPars->fSatur )
        p->vVisited = Vec_VecStart( 0 );

    // iterate over the network
    nNodesPrev = p->nNodesTotal;
    for ( Iter = 1; ; Iter++ )
    {
        // expand storage for changed nodes
        if ( p->pPars->fSatur )
            Vec_VecExpand( p->vVisited, Abc_NtkObjNumMax(pNtk) + 1 );

        // consider all nodes
        nNodes = Abc_NtkObjNumMax(pNtk);
        if ( !pPars->fVeryVerbose )
            pProgress = Extra_ProgressBarStart( stdout, nNodes );
        Abc_NtkForEachNode( pNtk, pObj, i )
        {
            if ( i >= nNodes )
                break;
            if ( !pPars->fVeryVerbose )
                Extra_ProgressBarUpdate( pProgress, i, NULL );
            // skip the nodes that did not change
            if ( p->pPars->fSatur && !Abc_LutNodeHasChanged(p, pObj->Id) )
                continue;
            // resynthesize
            p->pObj = pObj;
            Abc_LutResynthesizeNode( p );
        }
        if ( !pPars->fVeryVerbose )
            Extra_ProgressBarStop( pProgress );

        // check the increase
        Delta = 100.00 * (nNodesPrev - Abc_NtkNodeNum(pNtk)) / p->nNodesTotal;
        if ( Delta < 0.05 )
            break;
        nNodesPrev = Abc_NtkNodeNum(pNtk);
        if ( !p->pPars->fSatur )
            break;
    }

    if ( pPars->fVerbose )
    {
        printf( "N = %5d (%3d)  Cut = %5d (%4d)  Change = %5d  Gain = %5d  (%5.2f %%) Iter = %2d\n", 
            p->nNodesTotal, p->nNodesOver, p->nCutsTotal, p->nCutsUseful, p->nChanges, p->nGainTotal, 100.0 * p->nGainTotal / p->nNodesTotal, Iter );
        printf( "Non_DSD blocks: " );
        for ( i = 3; i <= pPars->nVarsMax; i++ )
            if ( p->nBlocks[i] )
                printf( "%d=%d  ", i, p->nBlocks[i] );
        printf( "\n" );
        p->timeTotal = clock() - clk;
        p->timeOther = p->timeTotal - p->timeCuts - p->timeTruth - p->timeEval - p->timeMap;
        PRTP( "Cuts  ", p->timeCuts,  p->timeTotal );
        PRTP( "Truth ", p->timeTruth, p->timeTotal );
        PRTP( "Eval  ", p->timeEval,  p->timeTotal );
        PRTP( "Map   ", p->timeMap,   p->timeTotal );
        PRTP( "Other ", p->timeOther, p->timeTotal );
        PRTP( "TOTAL ", p->timeTotal, p->timeTotal );
    }

    Abc_LutManStop( p );
    // check the resulting network
    if ( !Abc_NtkCheck( pNtk ) )
    {
        printf( "Abc_LutResynthesize: The network check has failed.\n" );
        return 0;
    }
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


