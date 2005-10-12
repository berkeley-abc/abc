/**CFile****************************************************************

  FileName    [abcFpgaSeq.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Mapping for FPGAs using sequential cuts.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcFpgaSeq.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abcs.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

Abc_Ntk_t * Abc_NtkMapSeq( Abc_Ntk_t * pNtk, int fVerbose ) { return 0; }

extern Cut_Man_t *     Abc_NtkSeqCuts( Abc_Ntk_t * pNtk, Cut_Params_t * pParams );
extern void            Abc_NtkFpgaSeqRetimeDelayLags( Seq_FpgaMan_t * p );

static Seq_FpgaMan_t * Abc_NtkFpgaSeqStart( Abc_Ntk_t * pNtk, int fVerbose );
static void            Abc_NtkFpgaSeqStop( Seq_FpgaMan_t * p );

static Abc_Ntk_t *     Abc_NtkFpgaSeqConstruct( Seq_FpgaMan_t * p );
static void            Abc_NtkFpgaSeqRetime( Seq_FpgaMan_t * p, Abc_Ntk_t * pNtkNew );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Retimes AIG for optimal delay.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkFpgaSeq( Abc_Ntk_t * pNtk, int fVerbose )
{
    Abc_Ntk_t * pNtkNew;
    Seq_FpgaMan_t * p;
    Cut_Params_t Params, * pParams = &Params;
    int clk;

    assert( Abc_NtkIsSeq( pNtk ) );

    // get the sequential FPGA manager
    p = Abc_NtkFpgaSeqStart( pNtk, fVerbose );

    // create the cuts
    memset( pParams, 0, sizeof(Cut_Params_t) );
    pParams->nVarsMax  = 5;     // the max cut size ("k" of the k-feasible cuts)
    pParams->nKeepMax  = 1000;  // the max number of cuts kept at a node
    pParams->fTruth    = 0;     // compute truth tables
    pParams->fFilter   = 1;     // filter dominated cuts
    pParams->fSeq      = 1;     // compute sequential cuts
    pParams->fVerbose  = 0;     // the verbosiness flag

clk = clock();
    p->pMan = Abc_NtkSeqCuts( pNtk, pParams );
p->timeCuts += clock() - clk;

    // find best arrival times (p->vArrivals) and free the cuts
    // select mapping (p->vMapping) and remember best cuts (p->vMapCuts) 
clk = clock();
    Abc_NtkFpgaSeqRetimeDelayLags( p );
p->timeDelay += clock() - clk;

return NULL;

    // construct the network
clk = clock();
    pNtkNew = Abc_NtkFpgaSeqConstruct( p );
p->timeNtk += clock() - clk;

    // retime the network
clk = clock();
    Abc_NtkFpgaSeqRetime( p, pNtkNew );
p->timeRet += clock() - clk;

    // remove temporaries
    Abc_NtkFpgaSeqStop( p );

    // check the resulting network
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkFpgaSeq(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Starts sequential FPGA mapper.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Seq_FpgaMan_t * Abc_NtkFpgaSeqStart( Abc_Ntk_t * pNtk, int fVerbose )
{
    Seq_FpgaMan_t * p;
    // create the FPGA mapping manager
    p = ALLOC( Seq_FpgaMan_t, 1 );
    memset( p, 0, sizeof(Seq_FpgaMan_t) );
    p->pNtk      = pNtk;
    p->pMan      = NULL;
    p->vArrivals = Vec_IntAlloc( 0 );
    p->vBestCuts = Vec_PtrAlloc( 0 );
    p->vMapping  = Vec_PtrAlloc( 0 );
    p->vMapCuts  = Vec_PtrAlloc( 0 );
    p->vLagsMap  = Vec_StrStart( Abc_NtkObjNumMax(pNtk) );
    p->fVerbose  = fVerbose;
    return p;
}

/**Function*************************************************************

  Synopsis    [Stops sequential FPGA mapper.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkFpgaSeqStop( Seq_FpgaMan_t * p )
{
    if ( p->fVerbose )
    {
        printf( "Sequential FPGA mapping stats:\n" );
//        printf( "Total allocated   = %8d.\n", p->nCutsAlloc );
//        printf( "Cuts per node     = %8.1f\n", ((float)(p->nCutsCur-p->nCutsTriv))/p->nNodes );
        PRT( "Cuts   ", p->timeCuts );
        PRT( "Arrival", p->timeDelay );
        PRT( "Network", p->timeNtk );
        PRT( "Retime ", p->timeRet );
    }
    Vec_IntFree( p->vArrivals );
    Vec_PtrFree( p->vBestCuts );
    Vec_PtrFree( p->vMapping );
    Vec_VecFree( (Vec_Vec_t *)p->vMapCuts );
    Vec_StrFree( p->vLagsMap );
    free( p );
}


/**Function*************************************************************

  Synopsis    [Construct the final network after mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkFpgaSeqConstruct( Seq_FpgaMan_t * p )
{
    Abc_Ntk_t * pNtk = NULL;
    return pNtk;
}

/**Function*************************************************************

  Synopsis    [Retimes the final network after mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkFpgaSeqRetime( Seq_FpgaMan_t * p, Abc_Ntk_t * pNtkNew )
{
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


