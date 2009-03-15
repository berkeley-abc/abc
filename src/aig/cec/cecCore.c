/**CFile****************************************************************

  FileName    [cecCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinatinoal equivalence checking.]

  Synopsis    [Core procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cecCore.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cecInt.h"

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
void Cec_ManSatSetDefaultParams( Cec_ParSat_t * p )
{
    memset( p, 0, sizeof(Cec_ParSat_t) );
    p->nBTLimit       =      10;  // conflict limit at a node
    p->nSatVarMax     =    2000;  // the max number of SAT variables
    p->nCallsRecycle  =     200;  // calls to perform before recycling SAT solver
    p->fPolarFlip     =       1;  // flops polarity of variables
    p->fCheckMiter    =       0;  // the circuit is the miter
    p->fFirstStop     =       0;  // stop on the first sat output
    p->fVerbose       =       0;  // verbose stats
}  

/**Function************  *************************************************

  Synopsis    [This procedure sets default parameters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManSimSetDefaultParams( Cec_ParSim_t * p )
{
    memset( p, 0, sizeof(Cec_ParSim_t) );
    p->nWords         =      15;  // the number of simulation words
    p->nRounds        =      15;  // the number of simulation rounds
    p->TimeLimit      =       0;  // the runtime limit in seconds
    p->fCheckMiter    =       0;  // the circuit is the miter
    p->fFirstStop     =       0;  // stop on the first sat output
    p->fDualOut       =       0;  // miter with separate outputs
    p->fSeqSimulate   =       0;  // performs sequential simulation
    p->fVeryVerbose   =       0;  // verbose stats
    p->fVerbose       =       0;  // verbose stats
} 

/**Function************  *************************************************

  Synopsis    [This procedure sets default parameters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManSmfSetDefaultParams( Cec_ParSmf_t * p )
{
    memset( p, 0, sizeof(Cec_ParSmf_t) );
    p->nWords         =      31;  // the number of simulation words
    p->nRounds        =       1;  // the number of simulation rounds
    p->nFrames        =       2;  // the number of time frames
    p->nBTLimit       =     100;  // conflict limit at a node
    p->TimeLimit      =       0;  // the runtime limit in seconds
    p->fDualOut       =       0;  // miter with separate outputs
    p->fCheckMiter    =       0;  // the circuit is the miter
    p->fFirstStop     =       0;  // stop on the first sat output
    p->fVerbose       =       0;  // verbose stats
} 

/**Function************  *************************************************

  Synopsis    [This procedure sets default parameters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManFraSetDefaultParams( Cec_ParFra_t * p )
{
    memset( p, 0, sizeof(Cec_ParFra_t) );
    p->nWords         =      15;  // the number of simulation words
    p->nRounds        =      15;  // the number of simulation rounds
    p->TimeLimit      =       0;  // the runtime limit in seconds
    p->nItersMax      =      10;  // the maximum number of iterations of SAT sweeping
    p->nBTLimit       =     100;  // conflict limit at a node
    p->nLevelMax      =       0;  // restriction on the level of nodes to be swept
    p->nDepthMax      =       1;  // the depth in terms of steps of speculative reduction
    p->fRewriting     =       0;  // enables AIG rewriting
    p->fCheckMiter    =       0;  // the circuit is the miter
    p->fFirstStop     =       0;  // stop on the first sat output
    p->fDualOut       =       0;  // miter with separate outputs
    p->fColorDiff     =       0;  // miter with separate outputs
    p->fVeryVerbose   =       0;  // verbose stats
    p->fVerbose       =       0;  // verbose stats
} 

/**Function*************************************************************

  Synopsis    [This procedure sets default parameters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManCecSetDefaultParams( Cec_ParCec_t * p )
{
    memset( p, 0, sizeof(Cec_ParCec_t) );
    p->nBTLimit       =    1000;  // conflict limit at a node
    p->TimeLimit      =       0;  // the runtime limit in seconds
    p->fFirstStop     =       0;  // stop on the first sat output
    p->fUseSmartCnf   =       0;  // use smart CNF computation
    p->fRewriting     =       0;  // enables AIG rewriting
    p->fVeryVerbose   =       0;  // verbose stats
    p->fVerbose       =       0;  // verbose stats
}  

/**Function*************************************************************

  Synopsis    [Core procedure for SAT sweeping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Cec_ManSatSolving( Gia_Man_t * pAig, Cec_ParSat_t * pPars )
{
    Gia_Man_t * pNew;
    Cec_ManPat_t * pPat;
    pPat = Cec_ManPatStart();
    Cec_ManSatSolve( pPat, pAig, pPars );
    pNew = Gia_ManDupDfsSkip( pAig );
    Cec_ManPatStop( pPat );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Core procedure for simulation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManSimulation( Gia_Man_t * pAig, Cec_ParSim_t * pPars )
{
    Cec_ManSim_t * pSim;
    int RetValue, clkTotal = clock();
    if ( pPars->fSeqSimulate )
        printf( "Performing sequential simulation of %d frames with %d words.\n", 
            pPars->nWords, pPars->nRounds );
    Aig_ManRandom( 1 );
    pSim = Cec_ManSimStart( pAig, pPars );
    if ( pAig->pReprs == NULL )
        RetValue = Cec_ManSimClassesPrepare( pSim );
    Cec_ManSimClassesRefine( pSim );
    if ( pPars->fCheckMiter )
        printf( "The number of failed outputs of the miter = %6d. (Words = %4d. Rounds = %4d.)\n", 
            pSim->iOut, pSim->nOuts, pPars->nWords, pPars->nRounds );
    if ( pPars->fVerbose )
        ABC_PRT( "Time", clock() - clkTotal );
    Cec_ManSimStop( pSim );
}

/**Function*************************************************************

  Synopsis    [Core procedure for SAT sweeping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Cec_ManSatSweeping( Gia_Man_t * pAig, Cec_ParFra_t * pPars )
{
    int fOutputResult = 0;
    Cec_ParSat_t ParsSat, * pParsSat = &ParsSat;
    Cec_ParSim_t ParsSim, * pParsSim = &ParsSim;
    Gia_Man_t * pIni, * pSrm, * pTemp;
    Cec_ManFra_t * p;
    Cec_ManSim_t * pSim;
    Cec_ManPat_t * pPat;
    int i, fTimeOut = 0, nMatches = 0, clk, clk2;
    double clkTotal = clock();

    // duplicate AIG and transfer equivalence classes
    Aig_ManRandom( 1 );
    pIni = Gia_ManDup(pAig);
    pIni->pReprs = pAig->pReprs; pAig->pReprs = NULL;
    pIni->pNexts = pAig->pNexts; pAig->pNexts = NULL;

    // prepare the managers
    // SAT sweeping
    p = Cec_ManFraStart( pIni, pPars );
    if ( pPars->fDualOut )
        pPars->fColorDiff = 1;
    // simulation
    Cec_ManSimSetDefaultParams( pParsSim );
    pParsSim->nWords      = pPars->nWords;
    pParsSim->nRounds     = pPars->nRounds;
    pParsSim->fCheckMiter = pPars->fCheckMiter;
    pParsSim->fFirstStop  = pPars->fFirstStop;
    pParsSim->fDualOut = pPars->fDualOut;
    pParsSim->fVerbose    = pPars->fVerbose;
    pSim = Cec_ManSimStart( p->pAig, pParsSim );
    // SAT solving
    Cec_ManSatSetDefaultParams( pParsSat );
    pParsSat->nBTLimit = pPars->nBTLimit;
    pParsSat->fVerbose = pPars->fVeryVerbose;
    // simulation patterns
    pPat = Cec_ManPatStart();
    pPat->fVerbose = pPars->fVeryVerbose;

    // start equivalence classes
clk = clock();
    if ( p->pAig->pReprs == NULL )
    {
        if ( Cec_ManSimClassesPrepare(pSim) || Cec_ManSimClassesRefine(pSim) )
        {
            Gia_ManStop( p->pAig );
            p->pAig = NULL;
            goto finalize;
        }
    }
p->timeSim += clock() - clk;
    // perform solving
    for ( i = 1; i <= pPars->nItersMax; i++ )
    {
        clk2 = clock();
        nMatches = 0;
        if ( pPars->fDualOut )
        {
            nMatches = Gia_ManEquivSetColors( p->pAig, pPars->fVeryVerbose );
//            p->pAig->pIso = Cec_ManDetectIsomorphism( p->pAig );
//            Gia_ManEquivTransform( p->pAig, 1 );
        }
        pSrm = Cec_ManFraSpecReduction( p ); 

//        Gia_WriteAiger( pSrm, "gia_srm.aig", 0, 0 );

        if ( pPars->fVeryVerbose )
            Gia_ManPrintStats( pSrm );
        if ( Gia_ManCoNum(pSrm) == 0 )
        {
            Gia_ManStop( pSrm );
            if ( p->pPars->fVerbose )
                printf( "Considered all available candidate equivalences.\n" );
            if ( pPars->fDualOut && Gia_ManAndNum(p->pAig) > 0 )
            {
                if ( pPars->fColorDiff )
                {
                    if ( p->pPars->fVerbose )
                        printf( "Switching into reduced mode.\n" );
                    pPars->fColorDiff = 0;
                }
                else
                {
                    if ( p->pPars->fVerbose )
                        printf( "Switching into normal mode.\n" );
                    pPars->fDualOut = 0;
                }
                continue;
            }
            break;
        }
clk = clock();
        Cec_ManSatSolve( pPat, pSrm, pParsSat ); 
p->timeSat += clock() - clk;
        if ( Cec_ManFraClassesUpdate( p, pSim, pPat, pSrm ) )
        {
            Gia_ManStop( pSrm );
            Gia_ManStop( p->pAig );
            p->pAig = NULL;
            goto finalize;
        }
        Gia_ManStop( pSrm );

        // update the manager
        pSim->pAig = p->pAig = Gia_ManEquivReduceAndRemap( pTemp = p->pAig, 0, pParsSim->fDualOut );
        Gia_ManStop( pTemp );
        if ( p->pAig == NULL )
            break;
        if ( p->pPars->fVerbose )
        {
            printf( "%3d : P =%7d. D =%7d. F =%6d. M = %7d. And =%8d. ", 
                i, p->nAllProved, p->nAllDisproved, p->nAllFailed, nMatches, Gia_ManAndNum(p->pAig) );
            ABC_PRT( "Time", clock() - clk2 );
        }
        if ( Gia_ManAndNum(p->pAig) == 0 )
        {
            if ( p->pPars->fVerbose )
                printf( "Network after reduction is empty.\n" );
            break;
        }
        // check resource limits
        if ( p->pPars->TimeLimit && ((double)clock() - clkTotal)/CLOCKS_PER_SEC >= p->pPars->TimeLimit )
        {
            fTimeOut = 1;
            break;
        }
//        if ( p->nAllFailed && !p->nAllProved && !p->nAllDisproved )
        if ( p->nAllFailed > p->nAllProved + p->nAllDisproved )
        {
            if ( pParsSat->nBTLimit >= 10000 )
                break;
            pParsSat->nBTLimit *= 10;
            if ( p->pPars->fVerbose )
            {
                if ( p->pPars->fVerbose )
                    printf( "Increasing conflict limit to %d.\n", pParsSat->nBTLimit );
                if ( fOutputResult )
                {
                    Gia_WriteAiger( p->pAig, "gia_cec_temp.aig", 0, 0 );
                    printf("The result is written into file \"%s\".\n", "gia_cec_temp.aig" );
                }
            }
        }
        if ( pPars->fDualOut && pPars->fColorDiff && Gia_ManAndNum(p->pAig) < 100000 )
        {
            if ( p->pPars->fVerbose )
                printf( "Switching into reduced mode.\n" );
            pPars->fColorDiff = 0;
        }
        if ( pPars->fDualOut && Gia_ManAndNum(p->pAig) < 20000 )
        {
            if ( p->pPars->fVerbose )
                printf( "Switching into normal mode.\n" );
            pPars->fColorDiff = 0;
            pPars->fDualOut = 0;
        }
    }
finalize:
    if ( p->pPars->fVerbose )
    {
        ABC_PRTP( "Sim ", p->timeSim, clock() - (int)clkTotal );
        ABC_PRTP( "Sat ", p->timeSat-pPat->timeTotalSave, clock() - (int)clkTotal );
        ABC_PRTP( "Pat ", p->timePat+pPat->timeTotalSave, clock() - (int)clkTotal );
        ABC_PRT( "Time", clock() - clkTotal );
    }

    pTemp = p->pAig; p->pAig = NULL;
    if ( pTemp == NULL && pSim->iOut >= 0 )
        printf( "Disproved at least one output of the miter (zero-based number %d).\n", pSim->iOut );
    else if ( pSim->pCexes )
        printf( "Disproved %d outputs of the miter.\n", pSim->nOuts );
    if ( fTimeOut )
        printf( "Timed out after %d seconds.\n", (int)((double)clock() - clkTotal)/CLOCKS_PER_SEC );

    pAig->pCexComb = pSim->pCexComb; pSim->pCexComb = NULL;
    Cec_ManSimStop( pSim );
    Cec_ManPatStop( pPat );
    Cec_ManFraStop( p );
    return pTemp;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


