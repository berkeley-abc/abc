/**CFile****************************************************************

  FileName    [darCut.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting.]

  Synopsis    [Computation of 4-input cuts.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: darCut.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "dar.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns 1 if pDom is contained in pCut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Dar_CutCheckDominance( Dar_Cut_t * pDom, Dar_Cut_t * pCut )
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

  Synopsis    [Returns 1 if the cut is contained.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_CutFilter( Dar_Man_t * p, Dar_Cut_t * pCut )
{ 
    Dar_Cut_t * pTemp;
    int i, k;
    assert( p->pBaseCuts[p->nCutsUsed] == pCut );
    for ( i = 0; i < p->nCutsUsed; i++ )
    {
        pTemp = p->pBaseCuts[i];
        if ( pTemp->nLeaves > pCut->nLeaves )
        {
            // skip the non-contained cuts
            if ( (pTemp->uSign & pCut->uSign) != pCut->uSign )
                continue;
            // check containment seriously
            if ( Dar_CutCheckDominance( pCut, pTemp ) )
            {
//                p->ppCuts[i] = p->ppCuts[p->nCuts-1];
//                p->ppCuts[p->nCuts-1] = pTemp;
//                p->nCuts--;
//                i--;
                // remove contained cut
                for ( k = i; k < p->nCutsUsed; k++ )
                    p->pBaseCuts[k] = p->pBaseCuts[k+1];
                p->pBaseCuts[p->nCutsUsed] = pTemp;
                p->nCutsUsed--;
                i--;
                p->nCutsFiltered++;
            }
         }
        else
        {
            // skip the non-contained cuts
            if ( (pTemp->uSign & pCut->uSign) != pTemp->uSign )
                continue;
            // check containment seriously
            if ( Dar_CutCheckDominance( pTemp, pCut ) )
            {
                p->nCutsFiltered++;
                return 1;
            }
        }
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Merges two cuts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Dar_CutMergeOrdered( Dar_Cut_t * pC, Dar_Cut_t * pC0, Dar_Cut_t * pC1 )
{ 
    int i, k, c;
    assert( pC0->nLeaves >= pC1->nLeaves );

    // the case of the largest cut sizes
    if ( pC0->nLeaves == 4 && pC1->nLeaves == 4 )
    {
        if ( pC0->uSign != pC1->uSign )
            return 0;
        for ( i = 0; i < (int)pC0->nLeaves; i++ )
            if ( pC0->pLeaves[i] != pC1->pLeaves[i] )
                return 0;
        for ( i = 0; i < (int)pC0->nLeaves; i++ )
            pC->pLeaves[i] = pC0->pLeaves[i];
        pC->nLeaves = pC0->nLeaves;
        return 1;
    }

    // the case when one of the cuts is the largest
    if ( pC0->nLeaves == 4 )
    {
        if ( (pC0->uSign & pC1->uSign) != pC1->uSign )
            return 0;
        for ( i = 0; i < (int)pC1->nLeaves; i++ )
        {
            for ( k = (int)pC0->nLeaves - 1; k >= 0; k-- )
                if ( pC0->pLeaves[k] == pC1->pLeaves[i] )
                    break;
            if ( k == -1 ) // did not find
                return 0;
        }
        for ( i = 0; i < (int)pC0->nLeaves; i++ )
            pC->pLeaves[i] = pC0->pLeaves[i];
        pC->nLeaves = pC0->nLeaves;
        return 1;
    }

    // compare two cuts with different numbers
    i = k = 0;
    for ( c = 0; c < 4; c++ )
    {
        if ( k == (int)pC1->nLeaves )
        {
            if ( i == (int)pC0->nLeaves )
            {
                pC->nLeaves = c;
                return 1;
            }
            pC->pLeaves[c] = pC0->pLeaves[i++];
            continue;
        }
        if ( i == (int)pC0->nLeaves )
        {
            if ( k == (int)pC1->nLeaves )
            {
                pC->nLeaves = c;
                return 1;
            }
            pC->pLeaves[c] = pC1->pLeaves[k++];
            continue;
        }
        if ( pC0->pLeaves[i] < pC1->pLeaves[k] )
        {
            pC->pLeaves[c] = pC0->pLeaves[i++];
            continue;
        }
        if ( pC0->pLeaves[i] > pC1->pLeaves[k] )
        {
            pC->pLeaves[c] = pC1->pLeaves[k++];
            continue;
        }
        pC->pLeaves[c] = pC0->pLeaves[i++]; 
        k++;
    }
    if ( i < (int)pC0->nLeaves || k < (int)pC1->nLeaves )
        return 0;
    pC->nLeaves = c;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Prepares the object for FPGA mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_CutMerge( Dar_Cut_t * pCut, Dar_Cut_t * pCut0, Dar_Cut_t * pCut1 )
{ 
    // merge the nodes
    if ( pCut0->nLeaves <= pCut1->nLeaves )
    {
        if ( !Dar_CutMergeOrdered( pCut, pCut1, pCut0 ) )
            return 0;
    }
    else
    {
        if ( !Dar_CutMergeOrdered( pCut, pCut0, pCut1 ) )
            return 0;
    }
    pCut->uSign = pCut0->uSign | pCut1->uSign;
    return 1;
}


/**Function*************************************************************

  Synopsis    [Computes the stretching phase of the cut w.r.t. the merged cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned Dar_CutTruthPhase( Dar_Cut_t * pCut, Dar_Cut_t * pCut1 )
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

  Synopsis    [Swaps two advancent variables of the truth table.]

  Description [Swaps variable iVar and iVar+1.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned Dar_CutTruthSwapAdjacentVars( unsigned uTruth, int iVar )
{
    assert( iVar >= 0 && iVar <= 2 );
    if ( iVar == 0 )
        return (uTruth & 0x99999999) | ((uTruth & 0x22222222) << 1) | ((uTruth & 0x44444444) >> 1);
    if ( iVar == 1 )
        return (uTruth & 0xC3C3C3C3) | ((uTruth & 0x0C0C0C0C) << 2) | ((uTruth & 0x30303030) >> 2);
    if ( iVar == 2 )
        return (uTruth & 0xF00FF00F) | ((uTruth & 0x00F000F0) << 4) | ((uTruth & 0x0F000F00) >> 4);
    assert( 0 );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Expands the truth table according to the phase.]

  Description [The input and output truth tables are in pIn/pOut. The current number
  of variables is nVars. The total number of variables in nVarsAll. The last argument
  (Phase) contains shows where the variables should go.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned Dar_CutTruthStretch( unsigned uTruth, int nVars, unsigned Phase )
{
    int i, k, Var = nVars - 1;
    for ( i = 3; i >= 0; i-- )
        if ( Phase & (1 << i) )
        {
            for ( k = Var; k < i; k++ )
                uTruth = Dar_CutTruthSwapAdjacentVars( uTruth, k );
            Var--;
        }
    assert( Var == -1 );
    return uTruth;
}

/**Function*************************************************************

  Synopsis    [Shrinks the truth table according to the phase.]

  Description [The input and output truth tables are in pIn/pOut. The current number
  of variables is nVars. The total number of variables in nVarsAll. The last argument
  (Phase) contains shows what variables should remain.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned Dar_CutTruthShrink( unsigned uTruth, int nVars, unsigned Phase )
{
    int i, k, Var = 0;
    for ( i = 0; i < 4; i++ )
        if ( Phase & (1 << i) )
        {
            for ( k = i-1; k >= Var; k-- )
                uTruth = Dar_CutTruthSwapAdjacentVars( uTruth, k );
            Var++;
        }
    return uTruth;
}

/**Function*************************************************************

  Synopsis    [Performs truth table computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned Dar_CutTruth( Dar_Cut_t * pCut, Dar_Cut_t * pCut0, Dar_Cut_t * pCut1, int fCompl0, int fCompl1 )
{
    unsigned uTruth0 = fCompl0 ? ~pCut0->uTruth : pCut0->uTruth;
    unsigned uTruth1 = fCompl1 ? ~pCut1->uTruth : pCut1->uTruth;
    uTruth0 = Dar_CutTruthStretch( uTruth0, pCut0->nLeaves, Dar_CutTruthPhase(pCut, pCut0) );
    uTruth1 = Dar_CutTruthStretch( uTruth1, pCut1->nLeaves, Dar_CutTruthPhase(pCut, pCut1) );
    return uTruth0 & uTruth1;
}

/**Function*************************************************************

  Synopsis    [Minimize support of the cut.]

  Description [Returns 1 if the node's support has changed]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_CutSuppMinimize( Dar_Cut_t * pCut )
{
    unsigned uMasks[4][2] = {
        { 0x5555, 0xAAAA },
        { 0x3333, 0xCCCC },
        { 0x0F0F, 0xF0F0 },
        { 0x00FF, 0xFF00 }
    };
    unsigned uPhase = 0, uTruth = 0xFFFF & pCut->uTruth;
    int i, k, nLeaves;
    // compute the truth support of the cut's function
    nLeaves = pCut->nLeaves;
    for ( i = 0; i < (int)pCut->nLeaves; i++ )
        if ( (uTruth & uMasks[i][0]) == ((uTruth & uMasks[i][1]) >> (1 << i)) )
            nLeaves--;
        else
            uPhase |= (1 << i);
    if ( nLeaves == (int)pCut->nLeaves )
        return 0;
    // shrink the truth table
    uTruth = Dar_CutTruthShrink( uTruth, pCut->nLeaves, uPhase );
    pCut->uTruth = 0xFFFF & uTruth;
    // update leaves and signature
    pCut->uSign = 0;
    for ( i = k = 0; i < (int)pCut->nLeaves; i++ )
    {
        if ( !(uPhase & (1 << i)) )
            continue;    
        pCut->pLeaves[k] = pCut->pLeaves[i];
//        pCut->pIndices[k] = pCut->pIndices[i];
        pCut->uSign |= (1 << (pCut->pLeaves[i] & 31));
        k++;
    }
    assert( k == nLeaves );
    pCut->nLeaves = nLeaves;
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ObjSetupTrivial( Dar_Obj_t * pObj )
{
    Dar_Cut_t * pCut;
    pCut = pObj->pData;
    pCut->Cost = 0;
    pCut->nLeaves = 1;
    pCut->pLeaves[0] = pObj->Id;
//    pCut->pIndices[0] = 0;
    pCut->uSign = (1 << (pObj->Id & 31));
    pCut->uTruth = 0xAAAA;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ManSetupPis( Dar_Man_t * p )
{
    Dar_Obj_t * pObj;
    int i;
    Dar_ManForEachPi( p, pObj, i )
    {
        pObj->nCuts = 1;
        pObj->pData = (Dar_Cut_t *)Dar_MmFlexEntryFetch( p->pMemCuts, pObj->nCuts * sizeof(Dar_Cut_t) );
        Dar_ObjSetupTrivial( pObj );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ManCutsFree( Dar_Man_t * p )
{
    Dar_Obj_t * pObj;
    int i;
    Dar_ManForEachObj( p, pObj, i )
        pObj->pData = NULL;
    Dar_MmFlexStop( p->pMemCuts, 0 );
    p->pMemCuts = NULL;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Cut_t * Dar_ObjComputeCuts( Dar_Man_t * p, Dar_Obj_t * pObj )
{
    Dar_Obj_t * pFanin0 = Dar_ObjReal_rec( Dar_ObjChild0(pObj) );
    Dar_Obj_t * pFanin1 = Dar_ObjReal_rec( Dar_ObjChild1(pObj) );
    Dar_Cut_t * pStart0 = Dar_Regular(pFanin0)->pData;
    Dar_Cut_t * pStart1 = Dar_Regular(pFanin1)->pData;
    Dar_Cut_t * pStop0 = pStart0 + Dar_Regular(pFanin0)->nCuts;
    Dar_Cut_t * pStop1 = pStart1 + Dar_Regular(pFanin1)->nCuts;
    Dar_Cut_t * pCut0, * pCut1, * pCut;
    int i;
    assert( pObj->pData == NULL );
    // make sure fanins cuts are computed
    p->nCutsUsed = 0;
    for ( pCut0 = pStart0; pCut0 < pStop0; pCut0++ )
    for ( pCut1 = pStart1; pCut1 < pStop1; pCut1++ )
    {
        // get storage for the next cut
        if ( p->nCutsUsed == p->nBaseCuts )
            break;
        pCut = p->pBaseCuts[p->nCutsUsed];
        // create the new cut
        if ( !Dar_CutMerge( pCut, pCut0, pCut1 ) )
            continue;
        // check dominance
        if ( Dar_CutFilter( p, pCut ) )
            continue;
        // compute truth table
        pCut->uTruth = 0xFFFF & Dar_CutTruth( pCut, pCut0, pCut1, Dar_IsComplement(pFanin0), Dar_IsComplement(pFanin1) );

        // minimize support of the cut
        if ( Dar_CutSuppMinimize( pCut ) )
        {
            if ( Dar_CutFilter( p, pCut ) )
                continue;
        }

        // CNF mapping: assign the cut cost if needed
        if ( p->pSopSizes )
        {
            pCut->Cost = p->pSopSizes[pCut->uTruth] + p->pSopSizes[0xFFFF & ~pCut->uTruth];
            Dar_CutAssignAreaFlow( p, pCut );
        }

        // increment the number of cuts
        p->nCutsUsed++;
    }
    // get memory for the cuts of this node
    pObj->nCuts = p->nCutsUsed + 1;
    pObj->pData = pCut = (Dar_Cut_t *)Dar_MmFlexEntryFetch( p->pMemCuts, pObj->nCuts * sizeof(Dar_Cut_t) );
    // create elementary cut
    Dar_ObjSetupTrivial( pObj );
    // copy non-elementary cuts
    for ( i = 0; i < p->nCutsUsed; i++ )
        *++pCut = *(p->pBaseCuts[i]);

    // CNF mapping: assign the best cut if needed
    if ( p->pSopSizes )
        Dar_ObjSetBestCut( pObj, Dar_ObjFindBestCut(pObj) );
    return pObj->pData;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Cut_t * Dar_ObjComputeCuts_rec( Dar_Man_t * p, Dar_Obj_t * pObj )
{
    if ( pObj->pData )
        return pObj->pData;
    if ( Dar_ObjIsBuf(pObj) )
        return Dar_ObjComputeCuts_rec( p, Dar_ObjFanin0(pObj) );
    Dar_ObjComputeCuts_rec( p, Dar_ObjFanin0(pObj) );
    Dar_ObjComputeCuts_rec( p, Dar_ObjFanin1(pObj) );
    return Dar_ObjComputeCuts( p, pObj );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


