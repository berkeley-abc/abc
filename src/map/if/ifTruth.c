/**CFile****************************************************************

  FileName    [ifTruth.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [Computation of truth tables of the cuts.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: ifTruth.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "if.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

//#define IF_TRY_NEW

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Sorts the pins in the decreasing order of delays.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_CutTruthPermute( word * pTruth, int nLeaves, int nVars, int nWords, float * pDelays, int * pVars )
{
    while ( 1 )
    {
        int i, fChange = 0;
        for ( i = 0; i < nLeaves - 1; i++ )
        {
            if ( pDelays[i] >= pDelays[i+1] )
                continue;
            ABC_SWAP( float, pDelays[i], pDelays[i+1] );
            ABC_SWAP( int, pVars[i], pVars[i+1] );
            if ( pTruth )
                Abc_TtSwapAdjacent( pTruth, nWords, i );
            fChange = 1;
        }
        if ( !fChange )
            return;
    }
}
void If_CutRotatePins( If_Man_t * p, If_Cut_t * pCut )
{
    If_Obj_t * pLeaf;
    float PinDelays[IF_MAX_LUTSIZE];
    int i, truthId;
    If_CutForEachLeaf( p, pCut, pLeaf, i )
        PinDelays[i] = If_ObjCutBest(pLeaf)->Delay;
    if ( p->vTtMem == NULL )
    {
        If_CutTruthPermute( NULL, If_CutLeaveNum(pCut), pCut->nLimit, p->nTruth6Words, PinDelays, If_CutLeaves(pCut) );
        return;
    }
    Abc_TtCopy( p->puTempW, If_CutTruthWR(p, pCut), p->nTruth6Words, 0 );
    If_CutTruthPermute( p->puTempW, If_CutLeaveNum(pCut), pCut->nLimit, p->nTruth6Words, PinDelays, If_CutLeaves(pCut) );
    truthId        = Vec_MemHashInsert( p->vTtMem, p->puTempW );
    pCut->iCutFunc = Abc_Var2Lit( truthId, If_CutTruthIsCompl(pCut) );
    assert( (p->puTempW[0] & 1) == 0 );
}

/**Function*************************************************************

  Synopsis    [Truth table computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CutComputeTruth( If_Man_t * p, If_Cut_t * pCut, If_Cut_t * pCut0, If_Cut_t * pCut1, int fCompl0, int fCompl1 )
{
    int fCompl, truthId, nLeavesNew;
    int iFuncLit0   = pCut0->iCutFunc;
    int iFuncLit1   = pCut1->iCutFunc;
    int nWords      = Abc_TtWordNum( pCut->nLimit );
    word * pTruth0s = Vec_MemReadEntry( p->vTtMem, Abc_Lit2Var(iFuncLit0) );
    word * pTruth1s = Vec_MemReadEntry( p->vTtMem, Abc_Lit2Var(iFuncLit1) );
    word * pTruth0  = (word *)p->puTemp[0];
    word * pTruth1  = (word *)p->puTemp[1];
    word * pTruth   = (word *)p->puTemp[2];
    Abc_TtCopy( pTruth0, pTruth0s, nWords, fCompl0 ^ pCut0->fCompl ^ Abc_LitIsCompl(iFuncLit0) );
    Abc_TtCopy( pTruth1, pTruth1s, nWords, fCompl1 ^ pCut1->fCompl ^ Abc_LitIsCompl(iFuncLit1) );
    Abc_TtStretch( pTruth0, pCut->nLimit, pCut0->pLeaves, pCut0->nLeaves, pCut->pLeaves, pCut->nLeaves );
    Abc_TtStretch( pTruth1, pCut->nLimit, pCut1->pLeaves, pCut1->nLeaves, pCut->pLeaves, pCut->nLeaves );
    fCompl         = (pTruth0[0] & pTruth1[0] & 1);
    Abc_TtAnd( pTruth, pTruth0, pTruth1, nWords, fCompl );
    if ( p->pPars->fCutMin )
    {
        nLeavesNew = Abc_TtMinBase( pTruth, pCut->pLeaves, pCut->nLeaves, pCut->nLimit );
        if ( nLeavesNew < If_CutLeaveNum(pCut) )
        {
            pCut->nLeaves = nLeavesNew;
            pCut->uSign   = If_ObjCutSignCompute( pCut );
        }
    }
    truthId        = Vec_MemHashInsert( p->vTtMem, pTruth );
    pCut->iCutFunc = Abc_Var2Lit( truthId, fCompl );
    assert( (pTruth[0] & 1) == 0 );
#ifdef IF_TRY_NEW
    {
        word pCopy[1024];
        char pCanonPerm[16];
        memcpy( pCopy, If_CutTruthW(pCut), sizeof(word) * nWords );
        Abc_TtCanonicize( pCopy, pCut->nLimit, pCanonPerm );
    }
#endif
    return 1;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

