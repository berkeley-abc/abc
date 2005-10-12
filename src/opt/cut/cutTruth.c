/**CFile****************************************************************

  FileName    [cutTruth.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [K-feasible cut computation package.]

  Synopsis    [Incremental truth table computation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cutTruth.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cutInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs truth table computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned Cut_TruthPhase( Cut_Cut_t * pCut, Cut_Cut_t * pCut1 )
{
    unsigned uPhase = 0;
    int i, k;
    for ( i = k = 0; i < (int)pCut->nLeaves; i++ )
    {
        if ( k == (int)pCut1->nLeaves )
            break;
        if ( pCut->pLeaves[i] < pCut1->pLeaves[k] )
            continue;
        assert( pCut->pLeaves[i] == pCut1->pLeaves[k] );
        uPhase |= (1 << i);
        k++;
    }
    return uPhase;
}

/**Function*************************************************************

  Synopsis    [Performs truth table computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_TruthCompute( Cut_Cut_t * pCut, Cut_Cut_t * pCut0, Cut_Cut_t * pCut1, int fCompl0, int fCompl1 )
{
    static unsigned uTruth0[8], uTruth1[8];
    int nTruthWords = Cut_TruthWords( pCut->nVarsMax );
    unsigned * pTruthRes;
    int i, uPhase;

    // permute the first table
    uPhase = Cut_TruthPhase( pCut, pCut0 );
    Extra_TruthExpand( pCut->nVarsMax, nTruthWords, Cut_CutReadTruth(pCut0), uPhase, uTruth0 );
    if ( fCompl0 ) 
    {
        for ( i = 0; i < nTruthWords; i++ )
            uTruth0[i] = ~uTruth0[i];
    }

    // permute the second table
    uPhase = Cut_TruthPhase( pCut, pCut1 );
    Extra_TruthExpand( pCut->nVarsMax, nTruthWords, Cut_CutReadTruth(pCut1), uPhase, uTruth1 );
    if ( fCompl1 ) 
    {
        for ( i = 0; i < nTruthWords; i++ )
            uTruth1[i] = ~uTruth1[i];
    }

    // write the resulting table
    pTruthRes = Cut_CutReadTruth(pCut);

    if ( pCut->fCompl )
    {
        for ( i = 0; i < nTruthWords; i++ )
            pTruthRes[i] = ~(uTruth0[i] & uTruth1[i]);
    }
    else
    {
        for ( i = 0; i < nTruthWords; i++ )
            pTruthRes[i] = uTruth0[i] & uTruth1[i];
    }
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


