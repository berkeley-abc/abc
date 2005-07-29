/**CFile****************************************************************

  FileName    [mapperTruth.c]

  PackageName [MVSIS 1.3: Multi-valued logic synthesis system.]

  Synopsis    [Generic technology mapping engine.]

  Author      [MVSIS Group]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 2.0. Started - June 1, 2004.]

  Revision    [$Id: mapperTruth.c,v 1.8 2005/01/23 06:59:45 alanmi Exp $]

***********************************************************************/

#include "mapperInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

//static void  Map_TruthsCutDcs( Map_Man_t * p, Map_Cut_t * pCut, unsigned uTruth[] );
static void  Map_TruthsCut( Map_Man_t * pMan, Map_Cut_t * pCut );
static void  Map_TruthsCut_rec( Map_Cut_t * pCut, unsigned uTruth[] );
static void  Map_TruthsUnmark_rec( Map_Cut_t * pCut );

/*
static int s_Same = 0;
static int s_Diff = 0;
static int s_Same2 = 0;
static int s_Diff2 = 0;
static int s_Truth = 0;
static int s_Isop1 = 0;
static int s_Isop2 = 0;
*/
////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Derives truth tables for each cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Map_MappingTruths( Map_Man_t * pMan )
{
    ProgressBar * pProgress;
    Map_Node_t * pNode;
    Map_Cut_t * pCut;
    int nNodes, i;
    // compute the cuts for the POs
    nNodes = pMan->vAnds->nSize;
    pProgress = Extra_ProgressBarStart( stdout, nNodes );
    for ( i = 0; i < nNodes; i++ )
    {
        pNode = pMan->vAnds->pArray[i];
        if ( !Map_NodeIsAnd( pNode ) )
            continue;
        assert( pNode->pCuts );
        assert( pNode->pCuts->nLeaves == 1 );

        // match the simple cut
        pNode->pCuts->M[0].uPhase     = 0;
        pNode->pCuts->M[0].pSupers    = pMan->pSuperLib->pSuperInv;
        pNode->pCuts->M[0].uPhaseBest = 0;
        pNode->pCuts->M[0].pSuperBest = pMan->pSuperLib->pSuperInv;

        pNode->pCuts->M[1].uPhase     = 0;
        pNode->pCuts->M[1].pSupers    = pMan->pSuperLib->pSuperInv;
        pNode->pCuts->M[1].uPhaseBest = 1;
        pNode->pCuts->M[1].pSuperBest = pMan->pSuperLib->pSuperInv;

        // match the rest of the cuts
        for ( pCut = pNode->pCuts->pNext; pCut; pCut = pCut->pNext )
             Map_TruthsCut( pMan, pCut );
        Extra_ProgressBarUpdate( pProgress, i, "Tables ..." );
    }
    Extra_ProgressBarStop( pProgress );

//    printf( "Same  = %6d. Diff  = %6d.\n", s_Same, s_Diff );
//    printf( "Same2 = %6d. Diff2 = %6d.\n", s_Same2, s_Diff2 );
//    printf( "Truth = %6d. Isop1 = %6d. Isop2 = %6d.\n", s_Truth, s_Isop1, s_Isop2 );
}

/**Function*************************************************************

  Synopsis    [Derives the truth table for one cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Map_TruthsCut( Map_Man_t * p, Map_Cut_t * pCut )
{
    unsigned uTruth[2], uCanon[2];
    unsigned char uPhases[16];
    int i;

    // generally speaking, 1-input cut can be matched into a wire!
    if ( pCut->nLeaves == 1 )
        return;
    // set the leaf truth tables
    for ( i = 0; i < pCut->nLeaves; i++ )
    {
        pCut->ppLeaves[i]->pCuts->uTruthTemp[0] = p->uTruths[i][0];
        pCut->ppLeaves[i]->pCuts->uTruthTemp[1] = p->uTruths[i][1];
    }
    // recursively compute the truth table
    pCut->nVolume = 0;
    Map_TruthsCut_rec( pCut, uTruth );
    // recursively unmark the visited cuts
    Map_TruthsUnmark_rec( pCut );

    // compute the canonical form for the positive phase
    Map_CanonComputeSlow( p->uTruths, p->nVarsMax, pCut->nLeaves, uTruth, uPhases, uCanon );
    pCut->M[1].pSupers = Map_SuperTableLookupC( p->pSuperLib, uCanon );
    pCut->M[1].uPhase  = uPhases[0];
    p->nCanons++;

    // compute the canonical form for the negative phase
    uTruth[0] = ~uTruth[0];
    uTruth[1] = ~uTruth[1];
    Map_CanonComputeSlow( p->uTruths, p->nVarsMax, pCut->nLeaves, uTruth, uPhases, uCanon );
    pCut->M[0].pSupers = Map_SuperTableLookupC( p->pSuperLib, uCanon );
    pCut->M[0].uPhase  = uPhases[0];
    p->nCanons++;

    // restore the truth table
    uTruth[0] = ~uTruth[0];
    uTruth[1] = ~uTruth[1];
    // enable don't-care computation
//    Map_TruthsCutDcs( p, pCut, uTruth );
}

#if 0

/**Function*************************************************************

  Synopsis    [Adds several other choices using SDCs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Map_TruthsCutDcs( Map_Man_t * p, Map_Cut_t * pCut, unsigned uTruth[] )
{
    unsigned uIsop1[2], uIsop2[2], uCanon[2];
    unsigned char uPhases[16];

    // add several other supergate classes derived using don't-cares
    if ( pCut->uTruthDc[0] )
    {
        int nOnes;
        nOnes = Map_TruthCountOnes( pCut->uTruthDc, pCut->nLeaves );
        if ( nOnes == 1 )
        {
            uTruth[0] ^= pCut->uTruthDc[0];
            uTruth[1] ^= pCut->uTruthDc[1];

            // compute the canonical form for the positive phase
            Map_CanonComputeSlow( p->uTruths, p->nVarsMax, pCut->nLeaves, uTruth, uPhases, uCanon );
            pCut->M[1].pSupers = Map_SuperTableLookupC( p->pSuperLib, uCanon );
            pCut->M[1].uPhase  = uPhases[0];
            p->nCanons++;

            // compute the canonical form for the negative phase
            uTruth[0] = ~uTruth[0];
            uTruth[1] = ~uTruth[1];
            Map_CanonComputeSlow( p->uTruths, p->nVarsMax, pCut->nLeaves, uTruth, uPhases, uCanon );
            pCut->M[0].pSupers = Map_SuperTableLookupC( p->pSuperLib, uCanon );
            pCut->M[0].uPhase  = uPhases[0];
            p->nCanons++;
        }
        else if ( nOnes == 2 )
        {
            int Num1, Num2, RetValue;
            RetValue = Map_TruthDetectTwoFirst( pCut->uTruthDc, pCut->nLeaves );
            Num1 =  RetValue & 255;
            Num2 = (RetValue >> 8) & 255;

            // add the first bit
            Map_InfoFlipVar( uTruth, Num1 );

            // compute the canonical form for the positive phase
            Map_CanonComputeSlow( p->uTruths, p->nVarsMax, pCut->nLeaves, uTruth, uPhases, uCanon );
            pCut->M[1].pSupers = Map_SuperTableLookupC( p->pSuperLib, uCanon );
            pCut->M[1].uPhase  = uPhases[0];
            p->nCanons++;

            // compute the canonical form for the negative phase
            uTruth[0] = ~uTruth[0];
            uTruth[1] = ~uTruth[1];
            Map_CanonComputeSlow( p->uTruths, p->nVarsMax, pCut->nLeaves, uTruth, uPhases, uCanon );
            pCut->M[0].pSupers = Map_SuperTableLookupC( p->pSuperLib, uCanon );
            pCut->M[0].uPhase  = uPhases[0];
            p->nCanons++;

            // add the first bit
            Map_InfoFlipVar( uTruth, Num2 );

            // compute the canonical form for the positive phase
            Map_CanonComputeSlow( p->uTruths, p->nVarsMax, pCut->nLeaves, uTruth, uPhases, uCanon );
            pCut->M[1].pSupers = Map_SuperTableLookupC( p->pSuperLib, uCanon );
            pCut->M[1].uPhase  = uPhases[0];
            p->nCanons++;

            // compute the canonical form for the negative phase
            uTruth[0] = ~uTruth[0];
            uTruth[1] = ~uTruth[1];
            Map_CanonComputeSlow( p->uTruths, p->nVarsMax, pCut->nLeaves, uTruth, uPhases, uCanon );
            pCut->M[0].pSupers = Map_SuperTableLookupC( p->pSuperLib, uCanon );
            pCut->M[0].uPhase  = uPhases[0];
            p->nCanons++;

            // add the first bit
            Map_InfoFlipVar( uTruth, Num1 );

            // compute the canonical form for the positive phase
            Map_CanonComputeSlow( p->uTruths, p->nVarsMax, pCut->nLeaves, uTruth, uPhases, uCanon );
            pCut->M[1].pSupers = Map_SuperTableLookupC( p->pSuperLib, uCanon );
            pCut->M[1].uPhase  = uPhases[0];
            p->nCanons++;

            // compute the canonical form for the negative phase
            uTruth[0] = ~uTruth[0];
            uTruth[1] = ~uTruth[1];
            Map_CanonComputeSlow( p->uTruths, p->nVarsMax, pCut->nLeaves, uTruth, uPhases, uCanon );
            pCut->M[0].pSupers = Map_SuperTableLookupC( p->pSuperLib, uCanon );
            pCut->M[0].uPhase  = uPhases[0];
            p->nCanons++;
        }
        else
        {
            // compute the ISOPs
            uIsop1[0] = Map_ComputeIsop_rec( p, uTruth[0] & ~pCut->uTruthDc[0], uTruth[0] | pCut->uTruthDc[0], 0, pCut->nLeaves, 0 );
            uIsop1[1] = uIsop1[0];
            if ( uIsop1[0] != uTruth[0] )
            {
                // compute the canonical form for the positive phase
                Map_CanonComputeSlow( p->uTruths, p->nVarsMax, pCut->nLeaves, uIsop1, uPhases, uCanon );
                pCut->M[1].pSupers = Map_SuperTableLookupC( p->pSuperLib, uCanon );
                pCut->M[1].uPhase  = uPhases[0];
                p->nCanons++;

                // compute the canonical form for the negative phase
                uIsop1[0] = ~uIsop1[0];
                uIsop1[1] = ~uIsop1[1];
                Map_CanonComputeSlow( p->uTruths, p->nVarsMax, pCut->nLeaves, uIsop1, uPhases, uCanon );
                pCut->M[0].pSupers = Map_SuperTableLookupC( p->pSuperLib, uCanon );
                pCut->M[0].uPhase  = uPhases[0];
                p->nCanons++;
            }

            uIsop2[0] = Map_ComputeIsop_rec( p, uTruth[0] & ~pCut->uTruthDc[0], uTruth[0] | pCut->uTruthDc[0], pCut->nLeaves-1, pCut->nLeaves, 1 );
            uIsop2[1] = uIsop2[0];
            if ( uIsop2[0] != uTruth[0] && uIsop2[0] != uIsop1[0] )
            {
                // compute the canonical form for the positive phase
                Map_CanonComputeSlow( p->uTruths, p->nVarsMax, pCut->nLeaves, uIsop2, uPhases, uCanon );
                pCut->M[1].pSupers = Map_SuperTableLookupC( p->pSuperLib, uCanon );
                p->nCanons++;

                // compute the canonical form for the negative phase
                uIsop2[0] = ~uIsop2[0];
                uIsop2[1] = ~uIsop2[1];
                Map_CanonComputeSlow( p->uTruths, p->nVarsMax, pCut->nLeaves, uIsop2, uPhases, uCanon );
                pCut->M[0].pSupers = Map_SuperTableLookupC( p->pSuperLib, uCanon );
                pCut->M[0].uPhase  = uPhases[0];
                p->nCanons++;
            }
        }
    }
}

#endif

/**Function*************************************************************

  Synopsis    [Recursively derives the truth table for the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Map_TruthsCut_rec( Map_Cut_t * pCut, unsigned uTruthRes[] )
{
    unsigned uTruth1[2], uTruth2[2];
    // if this is the elementary cut, its truth table is already available
    if ( pCut->nLeaves == 1 )
    {
        uTruthRes[0] = pCut->uTruthTemp[0];
        uTruthRes[1] = pCut->uTruthTemp[1];
        return;
    }
    // if this node was already visited, return its computed truth table
    if ( pCut->fMark )
    {
        uTruthRes[0] = pCut->uTruthTemp[0];
        uTruthRes[1] = pCut->uTruthTemp[1];
        return;
    }
    pCut->fMark = 1;
    pCut->nVolume++;

    assert( !Map_IsComplement(pCut) );
    Map_TruthsCut_rec( Map_CutRegular(pCut->pOne), uTruth1 );
    if ( Map_CutIsComplement(pCut->pOne) )
    {
        uTruth1[0] = ~uTruth1[0];
        uTruth1[1] = ~uTruth1[1];
    }
    Map_TruthsCut_rec( Map_CutRegular(pCut->pTwo), uTruth2 );
    if ( Map_CutIsComplement(pCut->pTwo) )
    {
        uTruth2[0] = ~uTruth2[0];
        uTruth2[1] = ~uTruth2[1];
    }
    if ( !pCut->Phase )
    {
        uTruthRes[0] = pCut->uTruthTemp[0] = uTruth1[0] & uTruth2[0];
        uTruthRes[1] = pCut->uTruthTemp[1] = uTruth1[1] & uTruth2[1];
    }
    else
    {
        uTruthRes[0] = pCut->uTruthTemp[0] = ~(uTruth1[0] & uTruth2[0]);
        uTruthRes[1] = pCut->uTruthTemp[1] = ~(uTruth1[1] & uTruth2[1]);
    }
}

/**Function*************************************************************

  Synopsis    [Recursively derives the truth table for the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Map_TruthsUnmark_rec( Map_Cut_t * pCut )
{
    if ( pCut->nLeaves == 1 )
        return;
    // if this node was already visited, return its computed truth table
    if ( pCut->fMark == 0 )
        return;
    pCut->fMark = 0;
    Map_TruthsUnmark_rec( Map_CutRegular(pCut->pOne) );
    Map_TruthsUnmark_rec( Map_CutRegular(pCut->pTwo) );
}

/**Function*************************************************************

  Synopsis    [Returns the truth table of the don't-care set.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Map_TruthsCutDontCare( Map_Man_t * pMan, Map_Cut_t * pCut, unsigned * uTruthDc )
{
    if ( pCut->pOne || (pCut->uTruthZero[0] == 0 && pCut->uTruthZero[1] == 0) )
        return 0;
    assert( (pCut->uTruthTemp[0] & pCut->uTruthZero[0]) == 0 );
    assert( (pCut->uTruthTemp[1] & pCut->uTruthZero[1]) == 0 );
    uTruthDc[0] = ((~0) & (~pCut->uTruthTemp[0]) & (~pCut->uTruthZero[0]));
    uTruthDc[1] = ((~0) & (~pCut->uTruthTemp[1]) & (~pCut->uTruthZero[1]));
    if ( uTruthDc[0] == 0 && uTruthDc[1] == 0 )
        return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Expand the truth table]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Map_TruthCountOnes( unsigned * uTruth, int nLeaves )
{
    int i, nMints, Counter;
    nMints = (1 << nLeaves);
    Counter = 0;
    for ( i = 0; i < nMints; i++ )
        Counter += Map_InfoReadVar( uTruth, i );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Expand the truth table]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Map_TruthDetectTwoFirst( unsigned * uTruth, int nLeaves )
{
    int i, nMints, Num1 = -1, Num2 = -1;
    nMints = (1 << nLeaves);
    for ( i = 0; i < nMints; i++ )
        if ( Map_InfoReadVar( uTruth, i ) )
        {
            if ( Num1 == -1 )
                Num1 = i;
            else if ( Num2 == -1 )
                Num2 = i;
            else
                break;
        }
    assert( Num1 != -1 && Num2 != -1 );
    return (Num1 << 8) | Num2;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


