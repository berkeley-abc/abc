/**CFile****************************************************************

  FileName    [sswCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Inductive prover with constraints.]

  Synopsis    [The core procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 1, 2008.]

  Revision    [$Id: sswCore.c,v 1.00 2008/09/01 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sswInt.h"

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
void Ssw_ManSetDefaultParams( Ssw_Pars_t * p )
{
    memset( p, 0, sizeof(Ssw_Pars_t) );
    p->nPartSize      =       0;  // size of the partition
    p->nOverSize      =       0;  // size of the overlap between partitions
    p->nFramesK       =       1;  // the induction depth
    p->nFramesAddSim  =       2;  // additional frames to simulate
    p->nConstrs       =       0;  // treat the last nConstrs POs as seq constraints
    p->nBTLimit       =    1000;  // conflict limit at a node
    p->nBTLimitGlobal = 5000000;  // conflict limit for all runs
    p->nMinDomSize    =     100;  // min clock domain considered for optimization
    p->nItersStop     =      -1;  // stop after the given number of iterations
    p->nResimDelta    =    1000;  // the internal of nodes to resimulate
    p->fPolarFlip     =       0;  // uses polarity adjustment
    p->fLatchCorr     =       0;  // performs register correspondence
    p->fSemiFormal    =       0;  // enable semiformal filtering
    p->fUniqueness    =       0;  // enable uniqueness constraints
    p->fDynamic       =       0;  // dynamic partitioning
    p->fLocalSim      =       0;  // local simulation
    p->fVerbose       =       0;  // verbose stats
    // latch correspondence
    p->fLatchCorrOpt  =       0;  // performs optimized register correspondence
    p->nSatVarMax     =    1000;  // the max number of SAT variables
    p->nRecycleCalls  =      50;  // calls to perform before recycling SAT solver
    // signal correspondence
    p->nSatVarMax2    =    5000;  // the max number of SAT variables
    p->nRecycleCalls2 =     250;  // calls to perform before recycling SAT solver
    // return values
    p->nIters         =       0;  // the number of iterations performed
}

/**Function*************************************************************

  Synopsis    [This procedure sets default parameters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_ManSetDefaultParamsLcorr( Ssw_Pars_t * p )
{
    Ssw_ManSetDefaultParams( p );
    p->fLatchCorrOpt = 1;
    p->nBTLimit      = 10000;
}

/**Function*************************************************************

  Synopsis    [Performs computation of signal correspondence with constraints.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Ssw_SignalCorrespondenceRefine( Ssw_Man_t * p )
{
    int nSatProof, nSatCallsSat, nRecycles, nSatFailsReal, nUniques;
    Aig_Man_t * pAigNew;
    int RetValue, nIter;
    int clk, clkTotal = clock();
    // get the starting stats
    p->nLitsBeg  = Ssw_ClassesLitNum( p->ppClasses );
    p->nNodesBeg = Aig_ManNodeNum(p->pAig);
    p->nRegsBeg  = Aig_ManRegNum(p->pAig);
    // refine classes using BMC
    if ( p->pPars->fVerbose )
    {
        printf( "Before BMC: " );
        Ssw_ClassesPrint( p->ppClasses, 0 );
    }
    if ( !p->pPars->fLatchCorr )
    { 
        p->pMSat = Ssw_SatStart( 0 );
        Ssw_ManSweepBmc( p );
        if ( p->pPars->nFramesK > 1 && p->pPars->fUniqueness )
            Ssw_UniqueRegisterPairInfo( p );
        Ssw_SatStop( p->pMSat );
        p->pMSat = NULL;
        Ssw_ManCleanup( p );
    }
    if ( p->pPars->fVerbose )
    {
        printf( "After  BMC: " );
        Ssw_ClassesPrint( p->ppClasses, 0 );
    }
    // apply semi-formal filtering
/*
    if ( p->pPars->fSemiFormal )
    {
        Aig_Man_t * pSRed;
        Ssw_FilterUsingSemi( p, 0, 2000, p->pPars->fVerbose );
//        Ssw_FilterUsingSemi( p, 1, 100000, p->pPars->fVerbose );
        pSRed = Ssw_SpeculativeReduction( p );
        Aig_ManDumpBlif( pSRed, "srm.blif", NULL, NULL );
        Aig_ManStop( pSRed );
    }
*/
    // refine classes using induction
    nSatProof = nSatCallsSat = nRecycles = nSatFailsReal = nUniques = 0;
    for ( nIter = 0; ; nIter++ )
    {
        if ( p->pPars->nItersStop >= 0 && p->pPars->nItersStop == nIter )
        {
            Aig_Man_t * pSRed = Ssw_SpeculativeReduction( p );
            Aig_ManDumpBlif( pSRed, "srm.blif", NULL, NULL );
            Aig_ManStop( pSRed );
            printf( "Iterative refinement is stopped before iteration %d.\n", nIter );
            printf( "The network is reduced using candidate equivalences.\n" );
            printf( "Speculatively reduced miter is saved in file \"%s\".\n", "srm.blif" );
            printf( "If the miter is SAT, the reduced result is incorrect.\n" );
            break;
        }

clk = clock();
        p->pMSat = Ssw_SatStart( 0 );
        if ( p->pPars->fLatchCorrOpt )
        {
            RetValue = Ssw_ManSweepLatch( p );
            if ( p->pPars->fVerbose )
            {
                printf( "%3d : C =%7d. Cl =%7d. Pr =%6d. Cex =%5d. R =%4d. F =%4d. ", 
                    nIter, Ssw_ClassesCand1Num(p->ppClasses), Ssw_ClassesClassNum(p->ppClasses), 
                    p->nSatProof-nSatProof, p->nSatCallsSat-nSatCallsSat, 
                    p->nRecycles-nRecycles, p->nSatFailsReal-nSatFailsReal );
                ABC_PRT( "T", clock() - clk );
            } 
        }
        else
        {
            if ( p->pPars->fDynamic )
                RetValue = Ssw_ManSweepDyn( p );
            else
                RetValue = Ssw_ManSweep( p );
            p->pPars->nConflicts += p->pMSat->pSat->stats.conflicts;
            if ( p->pPars->fVerbose )
            {
                printf( "%3d : C =%7d. Cl =%7d. LR =%6d. NR =%6d. ", 
                    nIter, Ssw_ClassesCand1Num(p->ppClasses), Ssw_ClassesClassNum(p->ppClasses), 
                    p->nConstrReduced, Aig_ManNodeNum(p->pFrames) );
                if ( p->pPars->fUniqueness )
                    printf( "U =%4d. ", p->nUniques-nUniques );
                else if ( p->pPars->fDynamic )
                {
                    printf( "Cex =%5d. ", p->nSatCallsSat-nSatCallsSat );
                    printf( "R =%4d. ",   p->nRecycles-nRecycles );
                }
                printf( "F =%5d. %s ", p->nSatFailsReal-nSatFailsReal, 
                    (Saig_ManPoNum(p->pAig)==1 && Ssw_ObjIsConst1Cand(p->pAig,Aig_ObjFanin0(Aig_ManPo(p->pAig,0))))? "+" : "-" );
                ABC_PRT( "T", clock() - clk );
            } 
//            if ( p->pPars->fDynamic && p->nSatCallsSat-nSatCallsSat < 100 )
//                p->pPars->nBTLimit = 10000;
        }
        nSatProof     = p->nSatProof;
        nSatCallsSat  = p->nSatCallsSat;
        nRecycles     = p->nRecycles;
        nSatFailsReal = p->nSatFailsReal;
        nUniques      = p->nUniques;

        p->nVarsMax  = ABC_MAX( p->nVarsMax,  p->pMSat->nSatVars );
        p->nCallsMax = ABC_MAX( p->nCallsMax, p->pMSat->nSolverCalls );
        Ssw_SatStop( p->pMSat );
        p->pMSat = NULL;
        Ssw_ManCleanup( p );
        if ( !RetValue ) 
            break;
    } 
    p->pPars->nIters = nIter + 1;
p->timeTotal = clock() - clkTotal;
    pAigNew = Aig_ManDupRepr( p->pAig, 0 );
    Aig_ManSeqCleanup( pAigNew );
//Ssw_ClassesPrint( p->ppClasses, 1 );
    // get the final stats
    p->nLitsEnd  = Ssw_ClassesLitNum( p->ppClasses );
    p->nNodesEnd = Aig_ManNodeNum(pAigNew);
    p->nRegsEnd  = Aig_ManRegNum(pAigNew);
    return pAigNew;
}

/**Function*************************************************************

  Synopsis    [Performs computation of signal correspondence with constraints.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Ssw_SignalCorrespondence( Aig_Man_t * pAig, Ssw_Pars_t * pPars )
{
    Ssw_Pars_t Pars;
    Aig_Man_t * pAigNew;
    Ssw_Man_t * p;
    assert( Aig_ManRegNum(pAig) > 0 );
    // reset random numbers
    Aig_ManRandom( 1 );
    // if parameters are not given, create them
    if ( pPars == NULL )
        Ssw_ManSetDefaultParams( pPars = &Pars );
    // consider the case of empty AIG
    if ( Aig_ManNodeNum(pAig) == 0 )
    {
        pPars->nIters = 0;
        // Ntl_ManFinalize() needs the following to satisfy an assertion
        Aig_ManReprStart( pAig,Aig_ManObjNumMax(pAig) );
        return Aig_ManDupOrdered(pAig);
    }
    // check and update parameters
    if ( pPars->fUniqueness )
    {
        pPars->nFramesAddSim = 0;
        if ( pPars->nFramesK != 2 )
            printf( "Setting K = 2 for uniqueness constraints to work.\n" );
        pPars->nFramesK = 2;
    }
    if ( pPars->fLatchCorrOpt )
    {
        pPars->fLatchCorr = 1;
        pPars->nFramesAddSim = 0;
        if ( (pAig->vClockDoms && Vec_VecSize(pAig->vClockDoms) > 0) )
           return Ssw_SignalCorrespondencePart( pAig, pPars );
    }
    else
    {
        assert( pPars->nFramesK > 0 );
        // perform partitioning
        if ( (pPars->nPartSize > 0 && pPars->nPartSize < Aig_ManRegNum(pAig))
             || (pAig->vClockDoms && Vec_VecSize(pAig->vClockDoms) > 0)  )
            return Ssw_SignalCorrespondencePart( pAig, pPars );
    }
    // start the induction manager
    p = Ssw_ManCreate( pAig, pPars );
    // compute candidate equivalence classes
//    p->pPars->nConstrs = 1;
    if ( p->pPars->nConstrs == 0 )
    {
        // perform one round of seq simulation and generate candidate equivalence classes
        p->ppClasses = Ssw_ClassesPrepare( pAig, pPars->nFramesK, pPars->fLatchCorr, pPars->nMaxLevs, pPars->fVerbose );
//        p->ppClasses = Ssw_ClassesPrepareTargets( pAig );
        if ( pPars->fLatchCorrOpt )
            p->pSml = Ssw_SmlStart( pAig, 0, 2, 1 );
        else if ( pPars->fDynamic )
            p->pSml = Ssw_SmlStart( pAig, 0, p->nFrames + p->pPars->nFramesAddSim, 1 );
        else
            p->pSml = Ssw_SmlStart( pAig, 0, 1 + p->pPars->nFramesAddSim, 1 );
        Ssw_ClassesSetData( p->ppClasses, p->pSml, Ssw_SmlObjHashWord, Ssw_SmlObjIsConstWord, Ssw_SmlObjsAreEqualWord );
    }
    else
    {
        // create trivial equivalence classes with all nodes being candidates for constant 1
        p->ppClasses = Ssw_ClassesPrepareSimple( pAig, pPars->fLatchCorr, pPars->nMaxLevs );
        Ssw_ClassesSetData( p->ppClasses, NULL, NULL, Ssw_SmlObjIsConstBit, Ssw_SmlObjsAreEqualBit );
    }
    if ( p->pPars->fLocalSim )
        p->pVisited = ABC_CALLOC( int, Ssw_SmlNumFrames( p->pSml ) * Aig_ManObjNumMax(p->pAig) );
    // perform refinement of classes
    pAigNew = Ssw_SignalCorrespondenceRefine( p );    
    if ( pPars->fUniqueness )
        printf( "Uniqueness constraints = %3d. Prevented counter-examples = %3d.\n", 
            p->nUniquesAdded, p->nUniquesUseful );
    // cleanup
    Ssw_ManStop( p );
    return pAigNew;
}

/**Function*************************************************************

  Synopsis    [Performs computation of latch correspondence.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Ssw_LatchCorrespondence( Aig_Man_t * pAig, Ssw_Pars_t * pPars )
{
    Ssw_Pars_t Pars;
    if ( pPars == NULL )
        Ssw_ManSetDefaultParamsLcorr( pPars = &Pars );
    return Ssw_SignalCorrespondence( pAig, pPars );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


