/**CFile****************************************************************

  FileName    [fraSec.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New FRAIG package.]

  Synopsis    [Performs SEC based on seq sweeping.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 30, 2007.]

  Revision    [$Id: fraSec.c,v 1.00 2007/06/30 00:00:00 alanmi Exp $]

***********************************************************************/

#include "fra.h"
#include "ioa.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_FraigSec( Aig_Man_t * p, int nFramesMax, int fRetimeFirst, int fFraiging, int fVerbose, int fVeryVerbose )
{
    Fra_Ssw_t Pars, * pPars = &Pars;
    Fra_Sml_t * pSml;
    Aig_Man_t * pNew, * pTemp;
    int nFrames, RetValue, nIter, clk, clkTotal = clock();
    int fLatchCorr = 0;
    // prepare parameters
    memset( pPars, 0, sizeof(Fra_Ssw_t) );
    pPars->fLatchCorr  = fLatchCorr;
    pPars->fVerbose = fVeryVerbose;

    pNew = Aig_ManDup( p, 1 );
    if ( fVerbose )
    {
        printf( "Original miter:       Latches = %5d. Nodes = %6d.\n", 
            Aig_ManRegNum(pNew), Aig_ManNodeNum(pNew) );
    }
//Aig_ManDumpBlif( pNew, "after.blif" );

    // perform sequential cleanup
clk = clock();
    if ( pNew->nRegs )
    pNew = Aig_ManReduceLaches( pNew, 0 );
    if ( pNew->nRegs )
    pNew = Aig_ManConstReduce( pNew, 0 );
    if ( fVerbose )
    {
        printf( "Sequential cleanup:   Latches = %5d. Nodes = %6d. ", 
            Aig_ManRegNum(pNew), Aig_ManNodeNum(pNew) );
PRT( "Time", clock() - clk );
    }

    // perform forward retiming
    if ( fRetimeFirst && pNew->nRegs )
    {
clk = clock();
    pNew = Rtm_ManRetime( pTemp = pNew, 1, 1000, 0 );
    Aig_ManStop( pTemp );
    if ( fVerbose )
    {
        printf( "Forward retiming:     Latches = %5d. Nodes = %6d. ", 
            Aig_ManRegNum(pNew), Aig_ManNodeNum(pNew) );
PRT( "Time", clock() - clk );
    }
    }
    
    // run latch correspondence
clk = clock();
    if ( pNew->nRegs )
    {
    pNew = Aig_ManDup( pTemp = pNew, 1 );
    Aig_ManStop( pTemp );
    pNew = Fra_FraigLatchCorrespondence( pTemp = pNew, 0, 100000, 1, fVeryVerbose, &nIter );
    p->pSeqModel = pTemp->pSeqModel; pTemp->pSeqModel = NULL;
    Aig_ManStop( pTemp );
    if ( pNew == NULL )
    {
        RetValue = 0;
        printf( "Networks are NOT EQUIVALENT after simulation.   " );
PRT( "Time", clock() - clkTotal );
        return RetValue;
    }

    if ( fVerbose )
    {
        printf( "Latch-corr (I=%3d):   Latches = %5d. Nodes = %6d. ", 
            nIter, Aig_ManRegNum(pNew), Aig_ManNodeNum(pNew) );
PRT( "Time", clock() - clk );
    }
    }

    // perform fraiging
    if ( fFraiging )
    {
clk = clock();
    pNew = Fra_FraigEquivence( pTemp = pNew, 100, 0 );
    Aig_ManStop( pTemp );
    if ( fVerbose )
    {
        printf( "Fraiging:             Latches = %5d. Nodes = %6d. ", 
            Aig_ManRegNum(pNew), Aig_ManNodeNum(pNew) );
PRT( "Time", clock() - clk );
    }
    }

    // perform seq sweeping while increasing the number of frames
    RetValue = Fra_FraigMiterStatus( pNew );
    if ( RetValue == -1 )
    for ( nFrames = 1; nFrames <= nFramesMax; nFrames *= 2 )
    {
clk = clock();
        pPars->nFramesK = nFrames;
        pNew = Fra_FraigInduction( pTemp = pNew, pPars );
        Aig_ManStop( pTemp );
        RetValue = Fra_FraigMiterStatus( pNew );
        if ( fVerbose )
        { 
            printf( "K-step (K=%2d,I=%3d):  Latches = %5d. Nodes = %6d. ", 
                nFrames, pPars->nIters, Aig_ManRegNum(pNew), Aig_ManNodeNum(pNew) );
PRT( "Time", clock() - clk );
        }
        if ( RetValue != -1 )
            break;

        // perform rewriting
clk = clock();
        pNew = Aig_ManDup( pTemp = pNew, 1 );
        Aig_ManStop( pTemp );
        pNew = Dar_ManRewriteDefault( pTemp = pNew );
        Aig_ManStop( pTemp );
        if ( fVerbose )
        {
            printf( "Rewriting:            Latches = %5d. Nodes = %6d. ", 
                Aig_ManRegNum(pNew), Aig_ManNodeNum(pNew) );
PRT( "Time", clock() - clk );
        } 

        // perform retiming
        if ( fRetimeFirst && pNew->nRegs )
//        if ( pNew->nRegs )
        {
clk = clock();
        pNew = Rtm_ManRetime( pTemp = pNew, 1, 1000, 0 );
        Aig_ManStop( pTemp );
        pNew = Aig_ManDup( pTemp = pNew, 1 );
        Aig_ManStop( pTemp );
        if ( fVerbose )
        {
            printf( "Forward retiming:     Latches = %5d. Nodes = %6d. ", 
                Aig_ManRegNum(pNew), Aig_ManNodeNum(pNew) );
PRT( "Time", clock() - clk );
        }
        }

        if ( pNew->nRegs )
            pNew = Aig_ManConstReduce( pNew, 0 );

        // perform sequential simulation
        if ( pNew->nRegs )
        {
clk = clock();
        pSml = Fra_SmlSimulateSeq( pNew, 0, 128 * nFrames, 1 + 16/(1+Aig_ManNodeNum(pNew)/1000) ); 
        if ( fVerbose )
        {
            printf( "Seq simulation  :     Latches = %5d. Nodes = %6d. ", 
                Aig_ManRegNum(pNew), Aig_ManNodeNum(pNew) );
PRT( "Time", clock() - clk );
        }
        if ( pSml->fNonConstOut )
        {
            p->pSeqModel = Fra_SmlGetCounterExample( pSml );
            Fra_SmlStop( pSml );
            Aig_ManStop( pNew );
            RetValue = 0;
            printf( "Networks are NOT EQUIVALENT after simulation.   " );
PRT( "Time", clock() - clkTotal );
            return RetValue;
        }
        Fra_SmlStop( pSml );
        }
    }

    // get the miter status
    RetValue = Fra_FraigMiterStatus( pNew );

    // report the miter
    if ( RetValue == 1 )
    {
        printf( "Networks are equivalent.   " );
PRT( "Time", clock() - clkTotal );
    }
    else if ( RetValue == 0 )
    {
        printf( "Networks are NOT EQUIVALENT.   " );
PRT( "Time", clock() - clkTotal );
    }
    else
    {
        static int Counter = 1;
        char pFileName[1000];
        printf( "Networks are UNDECIDED.   " );
PRT( "Time", clock() - clkTotal );
        sprintf( pFileName, "sm%03d.aig", Counter++ );
        Ioa_WriteAiger( pNew, pFileName, 0, 0 );
        printf( "The unsolved reduced miter is written into file \"%s\".\n", pFileName );
    }
    Aig_ManStop( pNew );
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


