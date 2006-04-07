/**CFile****************************************************************

  FileName    [pgaMatch.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapper.]

  Synopsis    [Mapping procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: pgaMatch.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "pgaInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static char * s_Modes[4] = { "Delay", "Flow", "Area", "Switch" };

static int Pga_MappingMatchNode( Pga_Man_t * p, int NodeId, Cut_Cut_t * pList, int Mode );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs mapping for delay, area-flow, area, switching.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pga_MappingMatches( Pga_Man_t * p, int Mode )
{
    ProgressBar * pProgress;
    Abc_Ntk_t * pNtk;
    Abc_Obj_t * pObj;
    Cut_Cut_t * pList;
    int i, clk;

    assert( Mode >= 0 && Mode <= 2 );

    // match LUTs with nodes in the topological order
    pNtk = p->pParams->pNtk;
    pProgress = Extra_ProgressBarStart( stdout, Abc_NtkObjNumMax(pNtk) );
    Abc_NtkForEachObj( pNtk, pObj, i )
    {
        // skip the CIs
        if ( Abc_ObjIsCi(pObj) )
            continue;
        // when we reached a CO, it is time to deallocate the cuts
        if ( Abc_ObjIsCo(pObj) )
        {
            if ( p->pParams->fDropCuts )
                Cut_NodeTryDroppingCuts( p->pManCut, Abc_ObjFaninId0(pObj) );
            continue;
        }
        // skip constant node, it has no cuts
        if ( Abc_NodeIsConst(pObj) )
            continue;
        // get the cuts
clk = clock();
        pList = Abc_NodeGetCutsRecursive( p->pManCut, pObj, 0, 0 );
p->timeCuts += clock() - clk;
        // match the node
        Pga_MappingMatchNode( p, pObj->Id, pList, Mode );
        Extra_ProgressBarUpdate( pProgress, i, s_Modes[Mode] );
    }
    Extra_ProgressBarStop( pProgress );
}




/**Function*************************************************************

  Synopsis    [Computes the match of the cut.]

  Description [Returns 1 if feasible.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline float Pga_CutGetArrival( Pga_Man_t * p, Cut_Cut_t * pCut )
{
    float DelayCur, DelayWorst;
    unsigned i;
    assert( pCut->nLeaves > 1 );
    DelayWorst = -ABC_INFINITY;
    for ( i = 0; i < pCut->nLeaves; i++ )
    {
        DelayCur = Pga_Node(p, pCut->pLeaves[i])->Match.Delay;
        if ( DelayWorst < DelayCur )
             DelayWorst = DelayCur;
    }
    DelayWorst += p->pLutDelays[pCut->nLeaves];
    return DelayWorst;
}

/**Function*************************************************************

  Synopsis    [Computes the match of the cut.]

  Description [Returns 1 if feasible.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline float Pga_CutGetAreaFlow( Pga_Man_t * p, Cut_Cut_t * pCut )
{
    float Flow;
    Pga_Node_t * pNode;
    unsigned i;
    assert( pCut->nLeaves > 1 );
    Flow = p->pLutAreas[pCut->nLeaves];
    for ( i = 0; i < pCut->nLeaves; i++ )
    {
        pNode = Pga_Node(p, pCut->pLeaves[i]);
        assert( pNode->EstRefs > 0 );
        Flow += pNode->Match.Area / pNode->EstRefs;
    }
    return Flow;
}

/**function*************************************************************

  synopsis    [References the cut.]

  description [This procedure is similar to the procedure NodeReclaim.]
               
  sideeffects []

  seealso     []

***********************************************************************/
float Pga_CutRef( Pga_Man_t * p, Pga_Node_t * pNode, Cut_Cut_t * pCut )
{
    Pga_Node_t * pFanin;
    float aArea;
    unsigned i;
    // start the area of this cut
    aArea = p->pLutAreas[pCut->nLeaves];
    // go through the children
    for ( i = 0; i < pCut->nLeaves; i++ )
    {
        pFanin = Pga_Node(p, pCut->pLeaves[i]);
        assert( pFanin->nRefs >= 0 );
        if ( pFanin->nRefs++ > 0 )  
            continue;
        if ( pFanin->Match.pCut == NULL ) 
            continue;
        aArea += Pga_CutRef( p, pFanin, pFanin->Match.pCut );
    }
    return aArea;
}

/**function*************************************************************

  synopsis    [Dereferences the cut.]

  description [This procedure is similar to the procedure NodeRecusiveDeref.]
               
  sideeffects []

  seealso     []

***********************************************************************/
float Pga_CutDeref( Pga_Man_t * p, Pga_Node_t * pNode, Cut_Cut_t * pCut )
{
    Pga_Node_t * pFanin;
    float aArea;
    unsigned i;
    // start the area of this cut
    aArea = p->pLutAreas[pCut->nLeaves];
    // go through the children
    for ( i = 0; i < pCut->nLeaves; i++ )
    {
        pFanin = Pga_Node(p, pCut->pLeaves[i]);
        assert( pFanin->nRefs > 0 );
        if ( --pFanin->nRefs > 0 )  
            continue;
        if ( pFanin->Match.pCut == NULL ) 
            continue;
        aArea += Pga_CutDeref( p, pFanin, pFanin->Match.pCut );
    }
    return aArea;
}

/**function*************************************************************

  synopsis    [Computes the exact area associated with the cut.]

  description [Assumes that the cut is deferenced.]
               
  sideeffects []

  seealso     []

***********************************************************************/
static inline float Pga_CutGetAreaDerefed( Pga_Man_t * p, Pga_Node_t * pNode, Cut_Cut_t * pCut )
{
    float aResult, aResult2;
    assert( pCut->nLeaves > 1 );
    aResult2 = Pga_CutRef( p, pNode, pCut );
    aResult  = Pga_CutDeref( p, pNode, pCut );
    assert( aResult == aResult2 );
    return aResult;
}



/**Function*************************************************************

  Synopsis    [Computes the match of the cut.]

  Description [Returns 1 if feasible.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Pga_MappingMatchCut( Pga_Man_t * p, Pga_Node_t * pNode, Cut_Cut_t * pCut, int Mode, Pga_Match_t * pMatch )
{
    // compute the arrival time of the cut and its area flow
    pMatch->Delay = Pga_CutGetArrival( p, pCut );
    // drop the cut if it does not meet the required times
    if ( pMatch->Delay > pNode->Required + p->Epsilon )
        return 0;
    // get the second parameter
    if ( Mode == 0 || Mode == 1 )
        pMatch->Area = Pga_CutGetAreaFlow( p, pCut );
    else if ( Mode == 2 )
        pMatch->Area = Pga_CutGetAreaDerefed( p, pNode, pCut );
//    else if ( Mode == 3 )
//        pMatch->Area = Pga_CutGetSwitching( p, pNode, pCut );
    // if no cut is assigned, use the current one
    pMatch->pCut = pCut;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Compares two matches.]

  Description [Returns 1 if the second match is better.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Pga_MappingCompareMatches( Pga_Man_t * p, Pga_Match_t * pMatchBest, Pga_Match_t * pMatchCur, int Mode )
{
    if ( pMatchBest->pCut == NULL )
        return 1;
    if ( Mode == 0 )
    {
        // compare delays
        if ( pMatchBest->Delay < pMatchCur->Delay - p->Epsilon )
            return 0;
        if ( pMatchBest->Delay > pMatchCur->Delay + p->Epsilon )
            return 1;
        // compare areas
        if ( pMatchBest->Area < pMatchCur->Area - p->Epsilon )
            return 0;
        if ( pMatchBest->Area > pMatchCur->Area + p->Epsilon )
            return 1;
        // if equal, do not update
        return 0;
    }
    else
    {
        // compare areas
        if ( pMatchBest->Area < pMatchCur->Area - p->Epsilon )
            return 0;
        if ( pMatchBest->Area > pMatchCur->Area + p->Epsilon )
            return 1;
        // compare delays
        if ( pMatchBest->Delay < pMatchCur->Delay - p->Epsilon )
            return 0;
        if ( pMatchBest->Delay > pMatchCur->Delay + p->Epsilon )
            return 1;
        // if equal, do not update
        return 0;
    }
}


/**Function*************************************************************

  Synopsis    [Computes the best matching for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pga_MappingMatchNode( Pga_Man_t * p, int NodeId, Cut_Cut_t * pList, int Mode )
{
    Pga_Match_t MatchCur,  * pMatchCur = &MatchCur;
    Pga_Match_t MatchBest, * pMatchBest = &MatchBest;
    Pga_Node_t * pNode;
    Cut_Cut_t * pCut;

    // get the mapping node
    pNode = Pga_Node( p, NodeId );

    // prepare for mapping
    if ( Mode == 0 )
        pNode->EstRefs = (float)pNode->nRefs;
    else if ( Mode == 1 )
        pNode->EstRefs = (float)((2.0 * pNode->EstRefs + pNode->nRefs) / 3.0);
    else if ( Mode == 2 && pNode->nRefs > 0 )
        Pga_CutDeref( p, pNode, pNode->Match.pCut );
//    else if ( Mode == 3 && pNode->nRefs > 0 )
//        Pga_CutDerefSwitch( p, pNode, pNode->Match.pCut );

    // start the best match
    pMatchBest->pCut = NULL;

    // go through the other cuts
    assert( pList->pNext );
    for ( pCut = pList->pNext; pCut; pCut = pCut->pNext )
    {
        // compute match for this cut
        if ( !Pga_MappingMatchCut( p, pNode, pCut, Mode, pMatchCur ) )
            continue;
        // compare matches
        if ( !Pga_MappingCompareMatches( p, pMatchBest, pMatchCur, Mode ) )
            continue;
        // the best match should be updated
        *pMatchBest = *pMatchCur;
    }

    // make sure the match is found
    if ( pMatchBest->pCut != NULL )
        pNode->Match = *pMatchBest;
    else
    {
        assert( 0 );
//        Pga_MappingMatchCut( p, pNode, pCut, Mode, pNode->Match );
    }

    // reference the best cut
    if ( Mode == 2 && pNode->nRefs > 0 )
        Pga_CutRef( p, pNode, pNode->Match.pCut );
//    else if ( Mode == 3 && pNode->nRefs > 0 )
//        Pga_CutRefSwitch( p, pNode, pNode->Match.pCut );
    return 1;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


