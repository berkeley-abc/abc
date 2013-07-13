/**CFile****************************************************************

  FileName    [mpmTruth.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Configurable technology mapper.]

  Synopsis    [Truth table manipulation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 1, 2013.]

  Revision    [$Id: mpmTruth.c,v 1.00 2013/06/01 00:00:00 alanmi Exp $]

***********************************************************************/

#include "mpmInt.h"
#include "misc/util/utilTruth.h"

ABC_NAMESPACE_IMPL_START


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
static inline int Mpm_CutTruthMinimize6( Mpm_Man_t * p, Mpm_Cut_t * pCut )
{
    unsigned uSupport;
    int i, k, nSuppSize;
    word t = *Mpm_CutTruth( p, Abc_Lit2Var(pCut->iFunc) );
    // compute the support of the cut's function
    uSupport = Abc_Tt6SupportAndSize( t, Mpm_CutLeafNum(pCut), &nSuppSize );
    if ( nSuppSize == Mpm_CutLeafNum(pCut) )
        return 0;
    if ( nSuppSize < 2 )
        p->nSmallSupp++;
    // update leaves and signature
    for ( i = k = 0; i < Mpm_CutLeafNum(pCut); i++ )
    {
        if ( !(uSupport & (1 << i)) )
            continue;    
        if ( k < i )
        {
            pCut->pLeaves[k] = pCut->pLeaves[i];
            Abc_TtSwapVars( &t, p->nLutSize, k, i );
        }
        k++;
    }
    assert( k == nSuppSize );
    pCut->nLeaves = nSuppSize;
    assert( nSuppSize == Abc_TtSupportSize(&t, Mpm_CutLeafNum(pCut)) );
    // save the result
    if ( t & 1 )
    {
        t = ~t;
        pCut->iFunc = Abc_Var2Lit( Vec_MemHashInsert( p->vTtMem, &t ), 1 );
    }
    else
        pCut->iFunc = Abc_Var2Lit( Vec_MemHashInsert( p->vTtMem, &t ), 0 );
    return 1;
}
static inline word Mpm_TruthStretch6( word Truth, Mpm_Cut_t * pCut, Mpm_Cut_t * pCut0, int nLimit )
{
    int i, k;
    for ( i = (int)pCut->nLeaves - 1, k = (int)pCut0->nLeaves - 1; i >= 0 && k >= 0; i-- )
    {
        if ( pCut0->pLeaves[k] < pCut->pLeaves[i] )
            continue;
        assert( pCut0->pLeaves[k] == pCut->pLeaves[i] );
        if ( k < i )
            Abc_TtSwapVars( &Truth, nLimit, k, i );
        k--;
    }
    return Truth;
}
int Mpm_CutComputeTruth6( Mpm_Man_t * p, Mpm_Cut_t * pCut, Mpm_Cut_t * pCut0, Mpm_Cut_t * pCut1, Mpm_Cut_t * pCutC, int fCompl0, int fCompl1, int fComplC, int Type )
{
    word * pTruth0 = Mpm_CutTruth( p, Abc_Lit2Var(pCut0->iFunc) );
    word * pTruth1 = Mpm_CutTruth( p, Abc_Lit2Var(pCut1->iFunc) );
    word * pTruthC = NULL;
    word t0 = (fCompl0 ^ pCut0->fCompl ^ Abc_LitIsCompl(pCut0->iFunc)) ? ~*pTruth0 : *pTruth0;
    word t1 = (fCompl1 ^ pCut1->fCompl ^ Abc_LitIsCompl(pCut1->iFunc)) ? ~*pTruth1 : *pTruth1;
    word tC = 0, t = 0;
    t0 = Mpm_TruthStretch6( t0, pCut, pCut0, p->nLutSize );
    t1 = Mpm_TruthStretch6( t1, pCut, pCut1, p->nLutSize );
    if ( pCutC )
    {
        pTruthC = Mpm_CutTruth( p, Abc_Lit2Var(pCutC->iFunc) );
        tC = (fComplC ^ pCutC->fCompl ^ Abc_LitIsCompl(pCutC->iFunc)) ? ~*pTruthC : *pTruthC;
        tC = Mpm_TruthStretch6( tC, pCut, pCutC, p->nLutSize );
    }
    assert( p->nLutSize <= 6 );
    if ( Type == 1 )
        t = t0 & t1;
    else if ( Type == 2 )
        t = t0 ^ t1;
    else if ( Type == 3 )
        t = (tC & t1) | (~tC & t0);
    else assert( 0 );
    // save the result
    if ( t & 1 )
    {
        t = ~t;
        pCut->iFunc = Abc_Var2Lit( Vec_MemHashInsert( p->vTtMem, &t ), 1 );
    }
    else
        pCut->iFunc = Abc_Var2Lit( Vec_MemHashInsert( p->vTtMem, &t ), 0 );

#ifdef MPM_TRY_NEW
    {
        word tCopy = t;
        char pCanonPerm[16];
        Abc_TtCanonicize( &tCopy, pCut->nLimit, pCanonPerm );
    }
#endif

//    if ( p->pPars->fCutMin )
//        return Mpm_CutTruthMinimize6( p, pCut );
    return 0;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

