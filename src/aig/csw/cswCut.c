/**CFile****************************************************************

  FileName    [cswCut.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Cut sweeping.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - July 11, 2007.]

  Revision    [$Id: cswCut.c,v 1.00 2007/07/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cswInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Compute the cost of the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Csw_CutFindCost( Csw_Man_t * p, Csw_Cut_t * pCut )
{
    Dar_Obj_t * pObj;
    int i, Cost = 0;
    Csw_CutForEachLeaf( p->pManRes, pCut, pObj, i )
        Cost += pObj->nRefs;
    return Cost * 100 / pCut->nFanins;
}

/**Function*************************************************************

  Synopsis    [Returns the next free cut to use.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Csw_Cut_t * Csw_CutFindFree( Csw_Man_t * p, Dar_Obj_t * pObj )
{
    Csw_Cut_t * pCut, * pCutMax;
    int i;
    pCutMax = NULL;
    Csw_ObjForEachCut( p, pObj, pCut, i )
    {
        if ( pCut->nFanins == 0 )
            return pCut;
        if ( pCutMax == NULL || pCutMax->Cost < pCut->Cost )
            pCutMax = pCut;
    }
    assert( pCutMax != NULL );
    pCutMax->nFanins = 0;
    return pCutMax;
}

/**Function*************************************************************

  Synopsis    [Computes the stretching phase of the cut w.r.t. the merged cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned Cut_TruthPhase( Csw_Cut_t * pCut, Csw_Cut_t * pCut1 )
{
    unsigned uPhase = 0;
    int i, k;
    for ( i = k = 0; i < pCut->nFanins; i++ )
    {
        if ( k == pCut1->nFanins )
            break;
        if ( pCut->pFanins[i] < pCut1->pFanins[k] )
            continue;
        assert( pCut->pFanins[i] == pCut1->pFanins[k] );
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
unsigned * Csw_CutComputeTruth( Csw_Man_t * p, Csw_Cut_t * pCut, Csw_Cut_t * pCut0, Csw_Cut_t * pCut1, int fCompl0, int fCompl1 )
{
    // permute the first table
    if ( fCompl0 ) 
        Kit_TruthNot( p->puTemp[0], Csw_CutTruth(pCut0), p->nLeafMax );
    else
        Kit_TruthCopy( p->puTemp[0], Csw_CutTruth(pCut0), p->nLeafMax );
    Kit_TruthStretch( p->puTemp[2], p->puTemp[0], pCut0->nFanins, p->nLeafMax, Cut_TruthPhase(pCut, pCut0), 0 );
    // permute the second table
    if ( fCompl1 ) 
        Kit_TruthNot( p->puTemp[1], Csw_CutTruth(pCut1), p->nLeafMax );
    else
        Kit_TruthCopy( p->puTemp[1], Csw_CutTruth(pCut1), p->nLeafMax );
    Kit_TruthStretch( p->puTemp[3], p->puTemp[1], pCut1->nFanins, p->nLeafMax, Cut_TruthPhase(pCut, pCut1), 0 );
    // produce the resulting table
    Kit_TruthAnd( Csw_CutTruth(pCut), p->puTemp[2], p->puTemp[3], p->nLeafMax );
    return Csw_CutTruth(pCut);
}

/**Function*************************************************************

  Synopsis    [Merges two cuts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Csw_CutMergeOrdered( Csw_Man_t * p, Csw_Cut_t * pC0, Csw_Cut_t * pC1, Csw_Cut_t * pC )
{ 
    int i, k, c;
    assert( pC0->nFanins >= pC1->nFanins );
    // the case of the largest cut sizes
    if ( pC0->nFanins == p->nLeafMax && pC1->nFanins == p->nLeafMax )
    {
        for ( i = 0; i < pC0->nFanins; i++ )
            if ( pC0->pFanins[i] != pC1->pFanins[i] )
                return 0;
        for ( i = 0; i < pC0->nFanins; i++ )
            pC->pFanins[i] = pC0->pFanins[i];
        pC->nFanins = pC0->nFanins;
        return 1;
    }
    // the case when one of the cuts is the largest
    if ( pC0->nFanins == p->nLeafMax )
    {
        for ( i = 0; i < pC1->nFanins; i++ )
        {
            for ( k = pC0->nFanins - 1; k >= 0; k-- )
                if ( pC0->pFanins[k] == pC1->pFanins[i] )
                    break;
            if ( k == -1 ) // did not find
                return 0;
        }
        for ( i = 0; i < pC0->nFanins; i++ )
            pC->pFanins[i] = pC0->pFanins[i];
        pC->nFanins = pC0->nFanins;
        return 1;
    }

    // compare two cuts with different numbers
    i = k = 0;
    for ( c = 0; c < p->nLeafMax; c++ )
    {
        if ( k == pC1->nFanins )
        {
            if ( i == pC0->nFanins )
            {
                pC->nFanins = c;
                return 1;
            }
            pC->pFanins[c] = pC0->pFanins[i++];
            continue;
        }
        if ( i == pC0->nFanins )
        {
            if ( k == pC1->nFanins )
            {
                pC->nFanins = c;
                return 1;
            }
            pC->pFanins[c] = pC1->pFanins[k++];
            continue;
        }
        if ( pC0->pFanins[i] < pC1->pFanins[k] )
        {
            pC->pFanins[c] = pC0->pFanins[i++];
            continue;
        }
        if ( pC0->pFanins[i] > pC1->pFanins[k] )
        {
            pC->pFanins[c] = pC1->pFanins[k++];
            continue;
        }
        pC->pFanins[c] = pC0->pFanins[i++]; 
        k++;
    }
    if ( i < pC0->nFanins || k < pC1->nFanins )
        return 0;
    pC->nFanins = c;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Prepares the object for FPGA mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Csw_CutMerge( Csw_Man_t * p, Csw_Cut_t * pCut0, Csw_Cut_t * pCut1, Csw_Cut_t * pCut )
{ 
    assert( p->nLeafMax > 0 );
    // merge the nodes
    if ( pCut0->nFanins < pCut1->nFanins )
    {
        if ( !Csw_CutMergeOrdered( p, pCut1, pCut0, pCut ) )
            return 0;
    }
    else
    {
        if ( !Csw_CutMergeOrdered( p, pCut0, pCut1, pCut ) )
            return 0;
    }
    pCut->uSign = pCut0->uSign | pCut1->uSign;
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Csw_Cut_t * Csw_ObjPrepareCuts( Csw_Man_t * p, Dar_Obj_t * pObj, int fTriv )
{
    Csw_Cut_t * pCutSet, * pCut;
    int i;
    // create the cutset of the node
    pCutSet = (Csw_Cut_t *)Dar_MmFixedEntryFetch( p->pMemCuts );
    Csw_ObjSetCuts( p, pObj, pCutSet );
    Csw_ObjForEachCut( p, pObj, pCut, i )
    {
        pCut->nFanins = 0;
        pCut->iNode = pObj->Id;
    }
    // add unit cut if needed
    if ( fTriv )
    {
        pCut = pCutSet;
        pCut->Cost = 0;
        pCut->iNode = pObj->Id;
        pCut->nFanins = 1;
        pCut->pFanins[0] = pObj->Id;
        pCut->uSign = Csw_ObjCutSign( pObj->Id );
        memset( Csw_CutTruth(pCut), 0xAA, sizeof(unsigned) * p->nTruthWords );
    }
    return pCutSet;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Obj_t * Csw_ObjSweep( Csw_Man_t * p, Dar_Obj_t * pObj, int fTriv )
{
    Csw_Cut_t * pCut0, * pCut1, * pCut, * pCutSet;
    Dar_Obj_t * pFanin0 = Dar_ObjFanin0(pObj);
    Dar_Obj_t * pFanin1 = Dar_ObjFanin1(pObj);
    Dar_Obj_t * pObjNew;
    unsigned * pTruth;
    int i, k, nVars, iVar;

    assert( !Dar_IsComplement(pObj) );
    if ( !Dar_ObjIsNode(pObj) )
        return pObj;
    if ( Csw_ObjCuts(p, pObj) )
        return pObj;
    // the node is not processed yet
    assert( Csw_ObjCuts(p, pObj) == NULL );
    assert( Dar_ObjIsNode(pObj) );

    // set up the first cut
    pCutSet = Csw_ObjPrepareCuts( p, pObj, fTriv );

    // compute pair-wise cut combinations while checking table
    Csw_ObjForEachCut( p, pFanin0, pCut0, i )
    if ( pCut0->nFanins > 0 )
    Csw_ObjForEachCut( p, pFanin1, pCut1, k )
    if ( pCut1->nFanins > 0 )
    {
        // make sure K-feasible cut exists
        if ( Kit_WordCountOnes(pCut0->uSign | pCut1->uSign) > p->nLeafMax )
            continue;
        // get the next cut of this node
        pCut = Csw_CutFindFree( p, pObj );
        // assemble the new cut
        if ( !Csw_CutMerge( p, pCut0, pCut1, pCut ) )
        {
            assert( pCut->nFanins == 0 );
            continue;
        }
/*
        // check containment
        if ( Csw_CutFilter( p, pCutSet, pCut ) )
        {
            pCut->nFanins = 0;
            continue;
        }
*/
        // create its truth table
        pTruth = Csw_CutComputeTruth( p, pCut, pCut0, pCut1, Dar_ObjFaninC0(pObj), Dar_ObjFaninC1(pObj) );
        // check for trivial truth table
        nVars = Kit_TruthSupportSize( pTruth, p->nLeafMax );
        if ( nVars == 0 )
            return Dar_NotCond( Dar_ManConst1(p->pManRes), !(pTruth[0] & 1) );
        if ( nVars == 1 )
        {
            iVar = Kit_WordFindFirstBit( Kit_TruthSupport(pTruth, p->nLeafMax) );
            assert( iVar < pCut->nFanins );
            return Dar_NotCond( Dar_ManObj(p->pManRes, pCut->pFanins[iVar]), (pTruth[0] & 1) );
        }
        // check if an equivalent node with the same cut exists
        if ( pObjNew = Csw_TableCutLookup( p, pCut ) )
            return pObjNew;
        // assign the cost
        pCut->Cost = Csw_CutFindCost( p, pCut );
        assert( pCut->nFanins > 0 );
        assert( pCut->Cost > 0 );
    }

    // load the resulting cuts into the table
    Csw_ObjForEachCut( p, pObj, pCut, i )
        if ( pCut->nFanins > 2 )
        {
            assert( pCut->Cost > 0 );
            Csw_TableCutInsert( p, pCut );
        }

    // return the node if could not replace it
    return pObj;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


