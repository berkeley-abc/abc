/**CFile****************************************************************

  FileName    [saigAbsStart.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [Counter-example-based abstraction.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: saigAbsStart.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "saig.h"
#include "src/proof/ssw/ssw.h"
#include "src/proof/fra/fra.h"
#include "src/proof/bbr/bbr.h"
#include "src/proof/pdr/pdr.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Find the first PI corresponding to the flop.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_ManCexFirstFlopPi( Aig_Man_t * p, Aig_Man_t * pAbs )
{ 
    Aig_Obj_t * pObj;
    int i;
    assert( pAbs->vCiNumsOrig != NULL );
    Aig_ManForEachPi( p, pObj, i )
    {
        if ( Vec_IntEntry(pAbs->vCiNumsOrig, i) >= Saig_ManPiNum(p) )
            return i;
    }
    return -1;
}

/**Function*************************************************************

  Synopsis    [Refines abstraction using one step.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_ManCexRefine( Aig_Man_t * p, Aig_Man_t * pAbs, Vec_Int_t * vFlops, int nFrames, int nConfMaxOne, int fUseBdds, int fUseDprove, int fVerbose, int * pnUseStart, int * piRetValue, int * pnFrames )
{ 
    extern int Saig_BmcPerform( Aig_Man_t * pAig, int nStart, int nFramesMax, int nNodesMax, int nTimeOut, int nConfMaxOne, int nConfMaxAll, int fVerbose, int fVerbOverwrite, int * piFrames );
    Vec_Int_t * vFlopsNew;
    int i, Entry, RetValue;
    *piRetValue = -1;
    if ( fUseDprove && Aig_ManRegNum(pAbs) > 0 )
    {
/*
        Fra_Sec_t SecPar, * pSecPar = &SecPar;
        Fra_SecSetDefaultParams( pSecPar );
        pSecPar->fVerbose       = fVerbose;
        RetValue = Fra_FraigSec( pAbs, pSecPar, NULL );
*/
        Abc_Cex_t * pCex = NULL;
        Aig_Man_t * pAbsOrpos = Saig_ManDupOrpos( pAbs );
        Pdr_Par_t Pars, * pPars = &Pars;
        Pdr_ManSetDefaultParams( pPars );
        pPars->nTimeOut = 10;
        pPars->fVerbose = fVerbose;
        if ( pPars->fVerbose )
            printf( "Running property directed reachability...\n" );
        RetValue = Pdr_ManSolve( pAbsOrpos, pPars, &pCex );
        if ( pCex )
            pCex->iPo = Saig_ManFindFailedPoCex( pAbs, pCex );
        Aig_ManStop( pAbsOrpos );
        pAbs->pSeqModel = pCex;
        if ( RetValue )
            *piRetValue = 1;

    }
    else if ( fUseBdds && (Aig_ManRegNum(pAbs) > 0 && Aig_ManRegNum(pAbs) <= 80) )
    {
        Saig_ParBbr_t Pars, * pPars = &Pars;
        Bbr_ManSetDefaultParams( pPars );
        pPars->TimeLimit     = 0;
        pPars->nBddMax       = 1000000;
        pPars->nIterMax      = nFrames;
        pPars->fPartition    = 1;
        pPars->fReorder      = 1;
        pPars->fReorderImage = 1;
        pPars->fVerbose      = fVerbose;
        pPars->fSilent       = 0;
        RetValue = Aig_ManVerifyUsingBdds( pAbs, pPars );
        if ( RetValue )
            *piRetValue = 1;
    }
    else 
    {
        Saig_BmcPerform( pAbs, pnUseStart? *pnUseStart: 0, nFrames, 2000, 0, nConfMaxOne, 0, fVerbose, 0, pnFrames );
    }
    if ( pAbs->pSeqModel == NULL )
        return NULL;
    if ( pnUseStart )
        *pnUseStart = pAbs->pSeqModel->iFrame;
//    vFlopsNew = Saig_ManExtendCounterExampleTest( pAbs, Saig_ManCexFirstFlopPi(p, pAbs), pAbs->pSeqModel, 1, fVerbose );
    vFlopsNew = Saig_ManExtendCounterExampleTest3( pAbs, Saig_ManCexFirstFlopPi(p, pAbs), pAbs->pSeqModel, fVerbose );
    if ( vFlopsNew == NULL )
        return NULL;
    if ( Vec_IntSize(vFlopsNew) == 0 )
    {
        printf( "Discovered a true counter-example!\n" );
        p->pSeqModel = Saig_ManCexRemap( p, pAbs, pAbs->pSeqModel );
        Vec_IntFree( vFlopsNew );
        *piRetValue = 0;
        return NULL;
    }
    // vFlopsNew contains PI numbers that should be kept in pAbs
    if ( fVerbose )
        printf( "Adding %d registers to the abstraction (total = %d).\n\n", Vec_IntSize(vFlopsNew), Aig_ManRegNum(pAbs)+Vec_IntSize(vFlopsNew) );
    // add to the abstraction
    Vec_IntForEachEntry( vFlopsNew, Entry, i )
    {
        Entry = Vec_IntEntry(pAbs->vCiNumsOrig, Entry);
        assert( Entry >= Saig_ManPiNum(p) );
        assert( Entry < Aig_ManPiNum(p) );
        Vec_IntPush( vFlops, Entry-Saig_ManPiNum(p) );
    }
    Vec_IntFree( vFlopsNew );

    Vec_IntSort( vFlops, 0 );
    Vec_IntForEachEntryStart( vFlops, Entry, i, 1 )
        assert( Vec_IntEntry(vFlops, i-1) != Entry );

    return Saig_ManDupAbstraction( p, vFlops );
}
 
/**Function*************************************************************

  Synopsis    [Refines abstraction using one step.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_ManCexRefineStep( Aig_Man_t * p, Vec_Int_t * vFlops, Vec_Int_t * vFlopClasses, Abc_Cex_t * pCex, int nFfToAddMax, int fTryFour, int fSensePath, int fVerbose )
{
    Aig_Man_t * pAbs;
    Vec_Int_t * vFlopsNew;
    int i, Entry, clk = clock();
    pAbs = Saig_ManDupAbstraction( p, vFlops );
    if ( fSensePath )
        vFlopsNew = Saig_ManExtendCounterExampleTest2( pAbs, Saig_ManCexFirstFlopPi(p, pAbs), pCex, fVerbose );
    else
//        vFlopsNew = Saig_ManExtendCounterExampleTest( pAbs, Saig_ManCexFirstFlopPi(p, pAbs), pCex, fTryFour, fVerbose );
        vFlopsNew = Saig_ManExtendCounterExampleTest3( pAbs, Saig_ManCexFirstFlopPi(p, pAbs), pCex, fVerbose );
    if ( vFlopsNew == NULL )
    {
        Aig_ManStop( pAbs );
        return 0;
    }
    if ( Vec_IntSize(vFlopsNew) == 0 )
    {
        printf( "Refinement did not happen. Discovered a true counter-example.\n" );
        printf( "Remapping counter-example from %d to %d primary inputs.\n", Aig_ManPiNum(pAbs), Aig_ManPiNum(p) );
        p->pSeqModel = Saig_ManCexRemap( p, pAbs, pCex );
        Vec_IntFree( vFlopsNew );
        Aig_ManStop( pAbs );
        return 0;
    }
    if ( fVerbose )
    {
        printf( "Adding %d registers to the abstraction (total = %d).  ", Vec_IntSize(vFlopsNew), Aig_ManRegNum(p)+Vec_IntSize(vFlopsNew) );
        Abc_PrintTime( 1, "Time", clock() - clk );
    }
    // vFlopsNew contains PI numbers that should be kept in pAbs
    // select the most useful flops among those to be added
    if ( nFfToAddMax > 0 && Vec_IntSize(vFlopsNew) > nFfToAddMax )
    {
        Vec_Int_t * vFlopsNewBest;
        // shift the indices
        Vec_IntForEachEntry( vFlopsNew, Entry, i )
            Vec_IntAddToEntry( vFlopsNew, i, -Saig_ManPiNum(p) );
        // create new flops
        vFlopsNewBest = Saig_ManCbaFilterFlops( p, pCex, vFlopClasses, vFlopsNew, nFfToAddMax );
        assert( Vec_IntSize(vFlopsNewBest) == nFfToAddMax );
        printf( "Filtering flops based on cost (%d -> %d).\n", Vec_IntSize(vFlopsNew), Vec_IntSize(vFlopsNewBest) );
        // update
        Vec_IntFree( vFlopsNew );
        vFlopsNew = vFlopsNewBest;
        // shift the indices
        Vec_IntForEachEntry( vFlopsNew, Entry, i )
            Vec_IntAddToEntry( vFlopsNew, i, Saig_ManPiNum(p) );
    }
    // add to the abstraction
    Vec_IntForEachEntry( vFlopsNew, Entry, i )
    {
        Entry = Vec_IntEntry(pAbs->vCiNumsOrig, Entry);
        assert( Entry >= Saig_ManPiNum(p) );
        assert( Entry < Aig_ManPiNum(p) );
        Vec_IntPush( vFlops, Entry-Saig_ManPiNum(p) );
    }
    Vec_IntFree( vFlopsNew );
    Aig_ManStop( pAbs );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Computes the flops to remain after abstraction.]

  Description []
               
  SideEffects []

  SeeAlso     []
 
***********************************************************************/
Vec_Int_t * Saig_ManCexAbstractionFlops( Aig_Man_t * p, Gia_ParAbs_t * pPars )
{
    int nUseStart = 0;
    Aig_Man_t * pAbs, * pTemp;
    Vec_Int_t * vFlops;
    int Iter, clk = clock(), clk2 = clock();//, iFlop;
    assert( Aig_ManRegNum(p) > 0 );
    if ( pPars->fVerbose )
        printf( "Performing counter-example-based refinement.\n" );
    Aig_ManSetPioNumbers( p );
    vFlops = Vec_IntStartNatural( 1 );
/*
    iFlop = Saig_ManFindFirstFlop( p );
    assert( iFlop >= 0 );
    vFlops = Vec_IntAlloc( 1 );
    Vec_IntPush( vFlops, iFlop );
*/
    // create the resulting AIG
    pAbs = Saig_ManDupAbstraction( p, vFlops );
    if ( !pPars->fVerbose )
    {
        printf( "Init : " );
        Aig_ManPrintStats( pAbs );
    }
    printf( "Refining abstraction...\n" );
    for ( Iter = 0; ; Iter++ )
    {
        pTemp = Saig_ManCexRefine( p, pAbs, vFlops, pPars->nFramesBmc, pPars->nConfMaxBmc, pPars->fUseBdds, pPars->fUseDprove, pPars->fVerbose, pPars->fUseStart?&nUseStart:NULL, &pPars->Status, &pPars->nFramesDone );
        if ( pTemp == NULL )
        {
            ABC_FREE( p->pSeqModel );
            p->pSeqModel = pAbs->pSeqModel;
            pAbs->pSeqModel = NULL;
            Aig_ManStop( pAbs );
            break;
        }
        Aig_ManStop( pAbs );
        pAbs = pTemp;
        printf( "ITER %4d : ", Iter );
        if ( !pPars->fVerbose )
            Aig_ManPrintStats( pAbs );
        // output the intermediate result of abstraction
        Ioa_WriteAiger( pAbs, "gabs.aig", 0, 0 );
//            printf( "Intermediate abstracted model was written into file \"%s\".\n", "gabs.aig" );
        // check if the ratio is reached
        if ( 100.0*(Aig_ManRegNum(p)-Aig_ManRegNum(pAbs))/Aig_ManRegNum(p) < 1.0*pPars->nRatio )
        {
            printf( "Refinements is stopped because flop reduction is less than %d%%\n", pPars->nRatio );
            Aig_ManStop( pAbs );
            pAbs = NULL;
            Vec_IntFree( vFlops );
            vFlops = NULL;
            break;
        }
    }
    return vFlops;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

