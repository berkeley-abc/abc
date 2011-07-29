/**CFile****************************************************************

  FileName    [giaAbs.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Counter-example-guided abstraction refinement.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaAbs.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#include "gia.h"
#include "giaAig.h"
#include "saig.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [This procedure sets default parameters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManAbsSetDefaultParams( Gia_ParAbs_t * p )
{
    memset( p, 0, sizeof(Gia_ParAbs_t) );
    p->Algo        =        0;    // algorithm: CBA
    p->nFramesMax  =       10;    // timeframes for PBA
    p->nConfMax    =    10000;    // conflicts for PBA
    p->fDynamic    =        1;    // dynamic unfolding for PBA
    p->fConstr     =        0;    // use constraints
    p->nFramesBmc  =      250;    // timeframes for BMC
    p->nConfMaxBmc =     5000;    // conflicts for BMC
    p->nStableMax  =  1000000;    // the number of stable frames to quit
    p->nRatio      =       10;    // ratio of flops to quit
    p->nBobPar     =  1000000;    // the number of frames before trying to quit
    p->fUseBdds    =        0;    // use BDDs to refine abstraction
    p->fUseDprove  =        0;    // use 'dprove' to refine abstraction
    p->fUseStart   =        1;    // use starting frame
    p->fVerbose    =        0;    // verbose output
    p->fVeryVerbose=        0;    // printing additional information
    p->Status      =       -1;    // the problem status
    p->nFramesDone =       -1;    // the number of rames covered
}

/**Function*************************************************************

  Synopsis    [Transform flop list into flop map.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_ManFlops2Classes( Gia_Man_t * pGia, Vec_Int_t * vFlops )
{
    Vec_Int_t * vFlopClasses;
    int i, Entry;
    vFlopClasses = Vec_IntStart( Gia_ManRegNum(pGia) );
    Vec_IntForEachEntry( vFlops, Entry, i )
        Vec_IntWriteEntry( vFlopClasses, Entry, 1 );
    return vFlopClasses;
}

/**Function*************************************************************

  Synopsis    [Transform flop map into flop list.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_ManClasses2Flops( Vec_Int_t * vFlopClasses )
{
    Vec_Int_t * vFlops;
    int i, Entry;
    vFlops = Vec_IntAlloc( 100 );
    Vec_IntForEachEntry( vFlopClasses, Entry, i )
        if ( Entry )
            Vec_IntPush( vFlops, i );
    return vFlops;
}


/**Function*************************************************************

  Synopsis    [Performs abstraction on the AIG manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDupAbstractionAig( Gia_Man_t * p, Vec_Int_t * vFlops )
{
    Gia_Man_t * pGia;
    Aig_Man_t * pNew, * pTemp;
    pNew = Gia_ManToAig( p, 0 );
    pNew = Saig_ManDupAbstraction( pTemp = pNew, vFlops );
    Aig_ManStop( pTemp );
    pGia = Gia_ManFromAig( pNew );
//    pGia->vCiNumsOrig = pNew->vCiNumsOrig; 
//    pNew->vCiNumsOrig = NULL;
    Aig_ManStop( pNew );
    return pGia;

}

/**Function*************************************************************

  Synopsis    [Starts abstraction by computing latch map.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCexAbstractionStart( Gia_Man_t * pGia, Gia_ParAbs_t * pPars )
{
    Vec_Int_t * vFlops;
    Aig_Man_t * pNew;
    if ( pGia->vFlopClasses != NULL )
    {
        printf( "Gia_ManCexAbstractionStart(): Abstraction latch map is present but will be rederived.\n" );
        Vec_IntFreeP( &pGia->vFlopClasses );
    }
    pNew = Gia_ManToAig( pGia, 0 );
    vFlops = Saig_ManCexAbstractionFlops( pNew, pPars );
    pGia->pCexSeq = pNew->pSeqModel; pNew->pSeqModel = NULL;
    Aig_ManStop( pNew );
    if ( vFlops )
    {
        pGia->vFlopClasses = Gia_ManFlops2Classes( pGia, vFlops );
        Vec_IntFree( vFlops );
    }
}

/**Function*************************************************************

  Synopsis    [Refines abstraction using the latch map.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManCexAbstractionRefine( Gia_Man_t * pGia, Abc_Cex_t * pCex, int fTryFour, int fSensePath, int fVerbose )
{
    Aig_Man_t * pNew;
    Vec_Int_t * vFlops;
    if ( pGia->vFlopClasses == NULL )
    {
        printf( "Gia_ManCexAbstractionRefine(): Abstraction latch map is missing.\n" );
        return -1;
    }
    pNew = Gia_ManToAig( pGia, 0 );
    vFlops = Gia_ManClasses2Flops( pGia->vFlopClasses );
    if ( !Saig_ManCexRefineStep( pNew, vFlops, pCex, fTryFour, fSensePath, fVerbose ) )
    {
        pGia->pCexSeq = pNew->pSeqModel; pNew->pSeqModel = NULL;
        Vec_IntFree( vFlops );
        Aig_ManStop( pNew );
        return 0;
    }
    Vec_IntFree( pGia->vFlopClasses );
    pGia->vFlopClasses = Gia_ManFlops2Classes( pGia, vFlops );
    Vec_IntFree( vFlops );
    Aig_ManStop( pNew );
    return -1;
}



/**Function*************************************************************

  Synopsis    [Transform flop list into flop map.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_ManFlopsSelect( Vec_Int_t * vFlops, Vec_Int_t * vFlopsNew )
{
    Vec_Int_t * vSelected;
    int i, Entry;
    vSelected = Vec_IntAlloc( Vec_IntSize(vFlopsNew) );
    Vec_IntForEachEntry( vFlopsNew, Entry, i )
        Vec_IntPush( vSelected, Vec_IntEntry(vFlops, Entry) );
    return vSelected;
}

/**Function*************************************************************

  Synopsis    [Derive unrolled timeframes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManPbaPerform( Gia_Man_t * pGia, int nFrames, int nConfLimit, int fVerbose )
{
    Gia_Man_t * pAbs;
    Aig_Man_t * pAig;
    Vec_Int_t * vFlops, * vFlopsNew, * vSelected;
    if ( pGia->vFlopClasses == NULL )
    {
        printf( "Gia_ManPbaPerform(): Abstraction flop map is missing.\n" );
        return 0;
    }
    // derive abstraction
    pAbs = Gia_ManDupAbstraction( pGia, pGia->vFlopClasses );
    // refine abstraction using PBA
    pAig = Gia_ManToAigSimple( pAbs );
    Gia_ManStop( pAbs );
    vFlopsNew = Saig_ManPbaDerive( pAig, nFrames, nConfLimit, fVerbose );
    Aig_ManStop( pAig );
    // derive new classes
    if ( vFlopsNew != NULL )
    {
        vFlops = Gia_ManClasses2Flops( pGia->vFlopClasses );
        vSelected = Gia_ManFlopsSelect( vFlops, vFlopsNew );
        Vec_IntFree( pGia->vFlopClasses );
        pGia->vFlopClasses = Saig_ManFlops2Classes( Gia_ManRegNum(pGia), vSelected );
        Vec_IntFree( vSelected );

        Vec_IntFree( vFlopsNew );
        Vec_IntFree( vFlops );
        return 1;
    }
    // found counter-eample for the abstracted model
    // or exceeded conflict limit
    return 0;
}

/**Function*************************************************************

  Synopsis    [Derive unrolled timeframes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManCbaPerform( Gia_Man_t * pGia, void * p )
{
    Saig_ParBmc_t * pPars = (Saig_ParBmc_t *)p;
    Gia_Man_t * pAbs;
    Aig_Man_t * pAig;
    Vec_Int_t * vFlops, * vFlopsNew, * vSelected;
    if ( pGia->vFlopClasses == NULL )
    {
        printf( "Gia_ManCbaPerform(): Empty abstraction is started.\n" );
        pGia->vFlopClasses = Vec_IntStart( Gia_ManRegNum(pGia) );
    }
    // derive abstraction
    pAbs = Gia_ManDupAbstraction( pGia, pGia->vFlopClasses );
    // refine abstraction using PBA
    pAig = Gia_ManToAigSimple( pAbs );
    Gia_ManStop( pAbs );
    vFlopsNew = Saig_ManCbaPerform( pAig, pPars );
    Aig_ManStop( pAig );
    // derive new classes
    if ( vFlopsNew != NULL )
    {
        vFlops = Gia_ManClasses2Flops( pGia->vFlopClasses );
//        vSelected = Saig_ManFlopsSelect( vFlops, vFlopsNew );
        vSelected = NULL;
        Vec_IntFree( pGia->vFlopClasses );
        pGia->vFlopClasses = Saig_ManFlops2Classes( Gia_ManRegNum(pGia), vSelected );
        Vec_IntFree( vSelected );

        Vec_IntFree( vFlopsNew );
        Vec_IntFree( vFlops );
        return 1;
    }
    // found counter-eample for the abstracted model
    // or exceeded conflict limit
    return 0;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

