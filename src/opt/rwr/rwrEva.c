/**CFile****************************************************************

  FileName    [rwrDec.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting package.]

  Synopsis    [Evaluation and decomposition procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: rwrDec.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "rwr.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void Rwr_CutEvaluate( Abc_ManRwr_t * p, Rwr_Cut_t * pCut );
static void Rwr_CutDecompose( Abc_ManRwr_t * p, Rwr_Cut_t * pCut, Vec_Int_t * vForm );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs rewriting for one node.]

  Description [This procedure considers all the cuts computed for the node
  and tries to rewrite each of them using the "forest" of different AIG
  structures precomputed and stored in the RWR manager. 
  Determines the best rewriting and computes the gain in the number of AIG
  nodes in the final network. In the end, p->vFanins contains information 
  about the best cut that can be used for rewriting, while p->vForm gives 
  the decomposition tree (represented using factored form data structure).
  Returns gain in the number of nodes or -1 if node cannot be rewritten.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeRwrRewrite( Abc_ManRwr_t * p, Abc_Obj_t * pNode )
{
    Vec_Ptr_t Vector = {0,0,0}, * vFanins = &Vector;
    Rwr_Cut_t * pCut, * pCutBest;
    int BestGain = -1;
    int i, Required = Vec_IntEntry( p->vReqTimes, pNode->Id );

    // go through the cuts
    for ( pCut = (Rwr_Cut_t *)pNode->pCopy, pCut = pCut->pNext; pCut; pCut = pCut->pNext )
    {
        // collect the TFO
        vFanins->nSize  = pCut->nLeaves;
        vFanins->pArray = pCut->ppLeaves;
        Abc_NodeCollectTfoCands( pNode->pNtk, pNode, vFanins, Required, p->vLevels, p->vTfo );
        // evaluate the cut
        Rwr_CutEvaluate( p, pCut );
        // check if the cut is the best
        if ( pCut->fTime && pCut->fGain )
        {
            pCutBest = pCut;
            BestGain = pCut->Volume;
        }
    }
    if ( BestGain == -1 )
        return -1;
    // we found a good cut

    // prepare the fanins
    Vec_PtrClear( p->vFanins );
    for ( i = 0; i < (int)pCutBest->nLeaves; i++ )
        Vec_PtrPush( p->vFanins, pCutBest->ppLeaves[i] );
    // collect the TFO again
    Abc_NodeCollectTfoCands( pNode->pNtk, pNode, p->vFanins, Required, p->vLevels, p->vTfo );
    // perform the decomposition
    Rwr_CutDecompose( p, pCutBest, p->vForm );
    // the best fanins are in p->vFanins, the result of decomposition is in p->vForm
    return BestGain;
}

/**Function*************************************************************

  Synopsis    [Evaluates one cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwr_CutEvaluate( Abc_ManRwr_t * p, Rwr_Cut_t * pCut )
{
}

/**Function*************************************************************

  Synopsis    [Evaluates one cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwr_CutDecompose( Abc_ManRwr_t * p, Rwr_Cut_t * pCut, Vec_Int_t * vForm )
{
}





////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


