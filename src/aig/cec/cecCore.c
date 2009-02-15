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
    p->nCallsRecycle  =     100;  // calls to perform before recycling SAT solver
    p->fPolarFlip     =       1;  // flops polarity of variables
    p->fFirstStop     =       0;  // stop on the first sat output
    p->fVerbose       =       1;  // verbose stats
}  
  
/**Function************  *************************************************

  Synopsis    [This procedure sets default parameters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManCswSetDefaultParams( Cec_ParCsw_t * p )
{
    memset( p, 0, sizeof(Cec_ParCsw_t) );
    p->nWords         =      20;  // the number of simulation words
    p->nRounds        =      20;  // the number of simulation rounds
    p->nItersMax      =      20;  // the maximum number of iterations of SAT sweeping
    p->nBTLimit       =   10000;  // conflict limit at a node
    p->nSatVarMax     =    2000;  // the max number of SAT variables
    p->nCallsRecycle  =     100;  // calls to perform before recycling SAT solver
    p->nLevelMax      =       0;  // restriction on the level of nodes to be swept
    p->nDepthMax      =       1;  // the depth in terms of steps of speculative reduction
    p->fRewriting     =       0;  // enables AIG rewriting
    p->fFirstStop     =       0;  // stop on the first sat output
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
    p->nIters         =       1;  // iterations of SAT solving/sweeping
    p->nBTLimitBeg    =       2;  // starting backtrack limit
    p->nBTlimitMulti  =       8;  // multiple of backtrack limiter
    p->fUseSmartCnf   =       0;  // use smart CNF computation
    p->fRewriting     =       0;  // enables AIG rewriting
    p->fSatSweeping   =       0;  // enables SAT sweeping
    p->fFirstStop     =       0;  // stop on the first sat output
    p->fVerbose       =       1;  // verbose stats
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

  Synopsis    [Core procedure for SAT sweeping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Cec_ManSatSweeping( Gia_Man_t * pAig, Cec_ParCsw_t * pPars )
{
    Cec_ParSat_t ParsSat, * pParsSat = &ParsSat;
    Gia_Man_t * pNew;
    Cec_ManCsw_t * p;
    Cec_ManPat_t * pPat;
    int i, RetValue, clk, clk2, clkTotal = clock();
    Aig_ManRandom( 1 );
    Gia_ManSetPhase( pAig );
    Gia_ManCleanMark0( pAig );
    Gia_ManCleanMark1( pAig );
    p = Cec_ManCswStart( pAig, pPars );
clk = clock();
    RetValue = Cec_ManCswClassesPrepare( p );
p->timeSim += clock() - clk;
    Cec_ManSatSetDefaultParams( pParsSat );
    pParsSat->nBTLimit = pPars->nBTLimit;
    pParsSat->fVerbose = pPars->fVeryVerbose;
    pPat = Cec_ManPatStart();
    pPat->fVerbose = pPars->fVeryVerbose;
    for ( i = 1; i <= pPars->nItersMax; i++ )
    {
        clk2 = clock();
        pNew = Cec_ManCswSpecReduction( p ); 
        if ( pPars->fVeryVerbose )
        {
            Gia_ManPrintStats( p->pAig );
            Gia_ManPrintStats( pNew );
        }
        if ( Gia_ManCoNum(pNew) == 0 )
        {
            Gia_ManStop( pNew );
            break;
        }
clk = clock();
        Cec_ManSatSolve( pPat, pNew, pParsSat ); 
p->timeSat += clock() - clk;
clk = clock();
        Cec_ManCswClassesUpdate( p, pPat, pNew );
p->timeSim += clock() - clk;
        Gia_ManStop( pNew );
        pNew = Cec_ManCswDupWithClasses( p );
        Gia_WriteAiger( pNew, "gia_temp_new.aig", 0, 1 );
        if ( p->pPars->fVerbose )
        {
            printf( "%3d : P =%7d. D =%7d. F =%6d. Lit =%8d. And =%8d. ", 
                i, p->nAllProved, p->nAllDisproved, p->nAllFailed,  
                Cec_ManCswCountLitsAll(p), Gia_ManAndNum(pNew) );
            ABC_PRT( "Time", clock() - clk2 );
        }
        if ( p->pPars->fVeryVerbose )
        {
            ABC_PRTP( "Sim ", p->timeSim, clock() - clkTotal );
            ABC_PRTP( "Sat ", p->timeSat, clock() - clkTotal );
            ABC_PRT( "Time", clock() - clkTotal );
            printf( "****** Intermedate result %3d ******\n", i );
            Gia_ManPrintStats( p->pAig );
            Gia_ManPrintStats( pNew );
            printf("The result is written into file \"%s\".\n", "gia_temp.aig" );
            printf( "************************************\n" );
        }
        if ( Gia_ManAndNum(pNew) == 0 )
        {
            Gia_ManStop( pNew );
            break;
        }
        Gia_ManStop( pNew );
    }
    Gia_ManCleanMark0( pAig );
    Gia_ManCleanMark1( pAig );

    // verify the result
    if ( p->pPars->fVerbose )
    {
        printf( "Verifying the result:\n" );
        pNew = Cec_ManCswSpecReductionProved( p );
        pParsSat->nBTLimit = 1000000;
        pParsSat->fVerbose = 1;
        Cec_ManSatSolve( NULL, pNew, pParsSat ); 
        Gia_ManStop( pNew );
    }

    // create the resulting miter
    pAig->pReprs = Cec_ManCswDeriveReprs( p );
    pNew = Gia_ManDupDfsClasses( pAig );
    Cec_ManCswStop( p );
    Cec_ManPatStop( pPat );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


