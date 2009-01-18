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
    p->nBTLimit       =   100;  // conflict limit at a node
    p->nSatVarMax     =  2000;  // the max number of SAT variables
    p->nCallsRecycle  =    10;  // calls to perform before recycling SAT solver
    p->fFirstStop     =     0;  // stop on the first sat output
    p->fPolarFlip     =     0;  // uses polarity adjustment
    p->fVerbose       =     0;  // verbose stats
}

/**Function*************************************************************

  Synopsis    [This procedure sets default parameters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManCswSetDefaultParams( Cec_ParCsw_t * p )
{
    memset( p, 0, sizeof(Cec_ParCsw_t) );
    p->nWords         =    15;  // the number of simulation words
    p->nRounds        =    10;  // the number of simulation rounds
    p->nBTlimit       =    10;  // conflict limit at a node
    p->fRewriting     =     0;  // enables AIG rewriting
    p->fVerbose       =     1;  // verbose stats
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
    p->nIters         =     5;  // iterations of SAT solving/sweeping
    p->nBTLimitBeg    =     2;  // starting backtrack limit
    p->nBTlimitMulti  =     8;  // multiple of backtrack limiter
    p->fUseSmartCnf   =     0;  // use smart CNF computation
    p->fRewriting     =     0;  // enables AIG rewriting
    p->fSatSweeping   =     0;  // enables SAT sweeping
    p->fFirstStop     =     0;  // stop on the first sat output
    p->fVerbose       =     1;  // verbose stats
}


/**Function*************************************************************

  Synopsis    [Performs equivalence checking.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_Sweep( Aig_Man_t * pAig, int nBTLimit )
{
    Cec_MtrStatus_t Status;
    Cec_ParCsw_t ParsCsw, * pParsCsw = &ParsCsw;
    Cec_ParSat_t ParsSat, * pParsSat = &ParsSat;
    Caig_Man_t * pCaig;
    Aig_Man_t * pSRAig;
    int clk;

    Cec_ManCswSetDefaultParams( pParsCsw );
    pParsCsw->nBTlimit = nBTLimit;
    pCaig = Caig_ManClassesPrepare( pAig, pParsCsw->nWords, pParsCsw->nRounds );

    pSRAig = Caig_ManSpecReduce( pCaig );
    Aig_ManPrintStats( pSRAig );

    Cec_ManSatSetDefaultParams( pParsSat );
    pParsSat->fFirstStop = 0;
    pParsSat->nBTLimit = pParsCsw->nBTlimit;
clk = clock();
    Status = Cec_SatSolveOutputs( pSRAig, pParsSat );
    Cec_MiterStatusPrint( Status, "SRM   ", clock() - clk );

    Aig_ManStop( pSRAig );

    Caig_ManDelete( pCaig );

    return 1;
}

/**Function*************************************************************

  Synopsis    [Performs equivalence checking.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_Solve( Aig_Man_t * pAig0, Aig_Man_t * pAig1, Cec_ParCec_t * pPars )
{
    Cec_ParSat_t ParsSat, * pParsSat = &ParsSat;
    Cec_MtrStatus_t Status;
    Aig_Man_t * pMiter;
    int i, clk = clock();
    if ( pPars->fVerbose )
    {
        Status = Cec_MiterStatusTrivial( pAig0 );
        Status.nNodes += pAig1? Aig_ManNodeNum( pAig1 ) : 0;
        Cec_MiterStatusPrint( Status, "Init  ", 0 );
    }
    // create combinational miter
    if ( pAig1 == NULL )
    {
        Status = Cec_MiterStatus( pAig0 );
        if ( Status.nSat > 0 && pPars->fFirstStop )
        {
            if ( pPars->fVerbose )
            printf( "Output %d is trivially SAT.\n", Status.iOut );
            return 0;
        }
        if ( Status.nUndec == 0 )
        {
            if ( pPars->fVerbose )
            printf( "The miter has no undecided outputs.\n" );
            return 1;
        }
        pMiter = Cec_Duplicate( pAig0 );
    }
    else
    {
        pMiter = Cec_DeriveMiter( pAig0, pAig1 );
        Status = Cec_MiterStatus( pMiter );
        if ( Status.nSat > 0 && pPars->fFirstStop )
        {
            if ( pPars->fVerbose )
            printf( "Output %d is trivially SAT.\n", Status.iOut );
            Aig_ManStop( pMiter );
            return 0;
        }
        if ( Status.nUndec == 0 )
        {
            if ( pPars->fVerbose )
            printf( "The problem is solved by structrual hashing.\n" );
            Aig_ManStop( pMiter );
            return 1;
        }
    }
    if ( pPars->fVerbose )
        Cec_MiterStatusPrint( Status, "Strash", clock() - clk );
    // start parameter structures
    Cec_ManSatSetDefaultParams( pParsSat );
    pParsSat->fFirstStop = pPars->fFirstStop;
    pParsSat->nBTLimit = pPars->nBTLimitBeg;
    for ( i = 0; i < pPars->nIters; i++ )
    {
        // try SAT solving
        clk = clock();
        pParsSat->nBTLimit *= pPars->nBTlimitMulti;
        Status = Cec_SatSolveOutputs( pMiter, pParsSat );
        if ( pPars->fVerbose )
            Cec_MiterStatusPrint( Status, "SAT   ", clock() - clk );
        if ( Status.nSat && pParsSat->fFirstStop )
            break;
        if ( Status.nUndec == 0 )
            break;

        // try rewriting

        // try SAT sweeping
        Cec_Sweep( pMiter, 10 );
        i = i;
    }
    Aig_ManStop( pMiter );
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


