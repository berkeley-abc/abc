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
#include "src/aig/saig/saig.h"

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
int Gia_ManCexAbstractionRefine( Gia_Man_t * pGia, Abc_Cex_t * pCex, int nFfToAddMax, int fTryFour, int fSensePath, int fVerbose )
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
    if ( !Saig_ManCexRefineStep( pNew, vFlops, pGia->vFlopClasses, pCex, nFfToAddMax, fTryFour, fSensePath, fVerbose ) )
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

  Synopsis    [Adds flops that should be present in the abstraction.]

  Description [The second argument (vAbsFfsToAdd) is the array of numbers
  of previously abstrated flops (flops replaced by PIs in the abstracted model)
  that should be present in the abstraction as real flops.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManFlopsAddToClasses( Vec_Int_t * vFlopClasses, Vec_Int_t * vAbsFfsToAdd )
{
    Vec_Int_t * vMapEntries;
    int i, Entry, iFlopNum;
    // map previously abstracted flops into their original numbers
    vMapEntries = Vec_IntAlloc( Vec_IntSize(vFlopClasses) );
    Vec_IntForEachEntry( vFlopClasses, Entry, i )
        if ( Entry == 0 )
            Vec_IntPush( vMapEntries, i );
    // add these flops as real flops
    Vec_IntForEachEntry( vAbsFfsToAdd, Entry, i )
    {
        iFlopNum = Vec_IntEntry( vMapEntries, Entry );
        assert( Vec_IntEntry( vFlopClasses, iFlopNum ) == 0 );
        Vec_IntWriteEntry( vFlopClasses, iFlopNum, 1 );
    }
    Vec_IntFree( vMapEntries );
}

/**Function*************************************************************

  Synopsis    [Derive unrolled timeframes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManCbaPerform( Gia_Man_t * pGia, void * pPars )
{
    Saig_ParBmc_t * p = (Saig_ParBmc_t *)pPars;
    Gia_Man_t * pAbs;
    Aig_Man_t * pAig, * pOrig;
    Vec_Int_t * vAbsFfsToAdd, * vAbsFfsToAddBest;
    // check if flop classes are given
    if ( pGia->vFlopClasses == NULL )
    {
        Abc_Print( 0, "Initial flop map is not given. Trivial abstraction is assumed.\n" );
        pGia->vFlopClasses = Vec_IntStart( Gia_ManRegNum(pGia) );
    }
    // derive abstraction
    pAbs = Gia_ManDupAbsFlops( pGia, pGia->vFlopClasses );
    pAig = Gia_ManToAigSimple( pAbs );
    Gia_ManStop( pAbs );
    // refine abstraction using CBA
    vAbsFfsToAdd = Saig_ManCbaPerform( pAig, Gia_ManPiNum(pGia), p );
    if ( vAbsFfsToAdd == NULL ) // found true CEX
    {
        assert( pAig->pSeqModel != NULL );
        printf( "Refinement did not happen. Discovered a true counter-example.\n" );
        printf( "Remapping counter-example from %d to %d primary inputs.\n", Aig_ManPiNum(pAig), Gia_ManPiNum(pGia) );
        // derive new counter-example
        pOrig = Gia_ManToAigSimple( pGia );
        pGia->pCexSeq = Saig_ManCexRemap( pOrig, pAig, pAig->pSeqModel );
        Aig_ManStop( pOrig );
        Aig_ManStop( pAig );
        return 0;
    }
    // select the most useful flops among those to be added
    if ( p->nFfToAddMax > 0 && Vec_IntSize(vAbsFfsToAdd) > p->nFfToAddMax )
    {
        // compute new flops
        Aig_Man_t * pAigBig = Gia_ManToAigSimple( pGia );
        vAbsFfsToAddBest = Saig_ManCbaFilterFlops( pAigBig, pAig->pSeqModel, pGia->vFlopClasses, vAbsFfsToAdd, p->nFfToAddMax );
        Aig_ManStop( pAigBig );
        assert( Vec_IntSize(vAbsFfsToAddBest) == p->nFfToAddMax );
        if ( p->fVerbose )
            printf( "Filtering flops based on cost (%d -> %d).\n", Vec_IntSize(vAbsFfsToAdd), Vec_IntSize(vAbsFfsToAddBest) );
        // update
        Vec_IntFree( vAbsFfsToAdd );
        vAbsFfsToAdd = vAbsFfsToAddBest;

    }
    Aig_ManStop( pAig );
    // update flop classes
    Gia_ManFlopsAddToClasses( pGia->vFlopClasses, vAbsFfsToAdd );
    Vec_IntFree( vAbsFfsToAdd );
    if ( p->fVerbose )
        Gia_ManPrintStats( pGia, 0 );
    return -1;
}

/**Function*************************************************************

  Synopsis    [Derive unrolled timeframes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManPbaPerform( Gia_Man_t * pGia, int nStart, int nFrames, int nConfLimit, int nTimeLimit, int fVerbose, int * piFrame )
{
    Gia_Man_t * pAbs;
    Aig_Man_t * pAig, * pOrig;
    Vec_Int_t * vFlops, * vFlopsNew, * vSelected;
    int RetValue;
    if ( pGia->vFlopClasses == NULL )
    {
        printf( "Gia_ManPbaPerform(): Abstraction flop map is missing.\n" );
        return 0;
    }
    // derive abstraction
    pAbs = Gia_ManDupAbsFlops( pGia, pGia->vFlopClasses );
    // refine abstraction using PBA
    pAig = Gia_ManToAigSimple( pAbs );
    Gia_ManStop( pAbs );
    vFlopsNew = Saig_ManPbaDerive( pAig, Gia_ManPiNum(pGia), nStart, nFrames, nConfLimit, nTimeLimit, fVerbose, piFrame );
    // derive new classes
    if ( pAig->pSeqModel == NULL )
    {
        // check if there is no timeout
        if ( vFlopsNew != NULL )
        {
            // the problem is UNSAT
            vFlops = Gia_ManClasses2Flops( pGia->vFlopClasses );
            vSelected = Gia_ManFlopsSelect( vFlops, vFlopsNew );
            Vec_IntFree( pGia->vFlopClasses );
            pGia->vFlopClasses = Saig_ManFlops2Classes( Gia_ManRegNum(pGia), vSelected );
            Vec_IntFree( vSelected );

            Vec_IntFree( vFlopsNew );
            Vec_IntFree( vFlops );
        }
        RetValue = -1;
    }
    else if ( vFlopsNew == NULL )
    {
        // found real counter-example
        assert( pAig->pSeqModel != NULL );
        printf( "Refinement did not happen. Discovered a true counter-example.\n" );
        printf( "Remapping counter-example from %d to %d primary inputs.\n", Aig_ManPiNum(pAig), Gia_ManPiNum(pGia) );
        // derive new counter-example
        pOrig = Gia_ManToAigSimple( pGia );
        pGia->pCexSeq = Saig_ManCexRemap( pOrig, pAig, pAig->pSeqModel );
        Aig_ManStop( pOrig );
        RetValue = 0;
    }
    else
    {
        // found counter-eample for the abstracted model
        // update flop classes
        Vec_Int_t * vAbsFfsToAdd = vFlopsNew;
        Gia_ManFlopsAddToClasses( pGia->vFlopClasses, vAbsFfsToAdd );
        Vec_IntFree( vAbsFfsToAdd );
        RetValue = -1;
    }
    Aig_ManStop( pAig );
    if ( fVerbose )
        Gia_ManPrintStats( pGia, 0 );
    return RetValue;
}


/**Function*************************************************************

  Synopsis    [Derive unrolled timeframes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManGlaCbaPerform( Gia_Man_t * pGia, void * pPars, int fNaiveCnf )
{
    extern Vec_Int_t * Aig_Gla1ManPerform( Aig_Man_t * pAig, Vec_Int_t * vGateClassesOld, int nStart, int nFramesMax, int nConfLimit, int TimeLimit, int fNaiveCnf, int fVerbose, int * piFrame );
    Saig_ParBmc_t * p = (Saig_ParBmc_t *)pPars;
    Vec_Int_t * vGateClasses, * vGateClassesOld = NULL;
    Aig_Man_t * pAig;

    // check if flop classes are given
    if ( pGia->vGateClasses == NULL )
        Abc_Print( 0, "Initial gate map is not given. Abstraction begins from scratch.\n" );
    else
    {
        Abc_Print( 0, "Initial gate map is given. Abstraction refines this map.\n" );
        vGateClassesOld = pGia->vGateClasses; pGia->vGateClasses = NULL;
        fNaiveCnf = 1;
    }

    // perform abstraction
    p->iFrame = -1;
    pAig = Gia_ManToAigSimple( pGia );
    assert( vGateClassesOld == NULL || Vec_IntSize(vGateClassesOld) == Aig_ManObjNumMax(pAig) );
    vGateClasses = Aig_Gla1ManPerform( pAig, vGateClassesOld, p->nStart, p->nFramesMax, p->nConfLimit, p->nTimeOut, fNaiveCnf, p->fVerbose, &p->iFrame );
    Aig_ManStop( pAig );

    // update the map
    Vec_IntFreeP( &vGateClassesOld );
    pGia->vGateClasses = vGateClasses;
    if ( p->fVerbose )
        Gia_ManPrintStats( pGia, 0 );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Derive unrolled timeframes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManGlaPbaPerform( Gia_Man_t * pGia, void * pPars, int fNewSolver )
{
    extern Vec_Int_t * Aig_Gla2ManPerform( Aig_Man_t * pAig, int nStart, int nFramesMax, int nConfLimit, int TimeLimit, int fSkipRand, int fVerbose );
    extern Vec_Int_t * Aig_Gla3ManPerform( Aig_Man_t * pAig, int nStart, int nFramesMax, int nConfLimit, int TimeLimit, int fSkipRand, int fVerbose );
    Saig_ParBmc_t * p = (Saig_ParBmc_t *)pPars;
    Vec_Int_t * vGateClasses;
    Gia_Man_t * pGiaAbs;
    Aig_Man_t * pAig;

    // check if flop classes are given
    if ( pGia->vGateClasses == NULL )
    {
        Abc_Print( 0, "Initial gate map is not given. Abstraction begins from scratch.\n" );
        pAig = Gia_ManToAigSimple( pGia );
    }
    else
    {
        Abc_Print( 0, "Initial gate map is given. Abstraction refines this map.\n" );
        pGiaAbs = Gia_ManDupAbsGates( pGia, pGia->vGateClasses );
        pAig = Gia_ManToAigSimple( pGiaAbs );
        Gia_ManStop( pGiaAbs );
    }

    // perform abstraction
    if ( fNewSolver )
        vGateClasses = Aig_Gla3ManPerform( pAig, p->nStart, p->nFramesMax, p->nConfLimit, p->nTimeOut, p->fSkipRand, p->fVerbose );
    else
        vGateClasses = Aig_Gla2ManPerform( pAig, p->nStart, p->nFramesMax, p->nConfLimit, p->nTimeOut, p->fSkipRand, p->fVerbose );
    Aig_ManStop( pAig );

    // update the BMC depth
    if ( vGateClasses )
        p->iFrame = p->nFramesMax;

    // update the abstraction map (hint: AIG and GIA have one-to-one obj ID match)
    if ( pGia->vGateClasses && vGateClasses )
    {
        Gia_Obj_t * pObj;
        int i, Counter = 0;
        Gia_ManForEachObj1( pGia, pObj, i )
        {
            if ( !~pObj->Value )
                continue;
            if ( !Vec_IntEntry(pGia->vGateClasses, i) )
                continue;
            // this obj was abstracted before
            assert( Gia_ObjIsAnd(pObj) || Gia_ObjIsRo(pGia, pObj) );
            // if corresponding AIG object is not abstracted, remove abstraction
            if ( !Vec_IntEntry(vGateClasses, Abc_Lit2Var(pObj->Value)) )
            {
                Vec_IntWriteEntry( pGia->vGateClasses, i, 0 );
                Counter++;
            }
        }
        Vec_IntFree( vGateClasses );
        if ( p->fVerbose )
            Abc_Print( 1, "Repetition of abstraction removed %d entries from the old abstraction map.\n", Counter );
    }
    else
    {
        Vec_IntFreeP( &pGia->vGateClasses );
        pGia->vGateClasses = vGateClasses;
    }
    // clean up the abstraction map
    if ( pGia->vGateClasses )
    {
        pGiaAbs = Gia_ManDupAbsGates( pGia, pGia->vGateClasses );
        Gia_ManStop( pGiaAbs );
    }
    if ( p->fVerbose )
        Gia_ManPrintStats( pGia, 0 );
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

