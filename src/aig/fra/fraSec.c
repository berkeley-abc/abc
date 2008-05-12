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
int Fra_FraigSec( Aig_Man_t * p, int nFramesMax, int fPhaseAbstract, int fRetimeFirst, int fRetimeRegs, int fFraiging, int fVerbose, int fVeryVerbose, int TimeLimit )
{
    Fra_Ssw_t Pars, * pPars = &Pars;
    Fra_Sml_t * pSml;
    Aig_Man_t * pNew, * pTemp;
    int nFrames, RetValue, nIter, clk, clkTotal = clock();
    int fLatchCorr = 0;
    float TimeLeft = 0.0;

    // try the miter before solving
    pNew = Aig_ManDup( p );
    RetValue = Fra_FraigMiterStatus( pNew );
    if ( RetValue >= 0 )
        goto finish;

    // prepare parameters
    memset( pPars, 0, sizeof(Fra_Ssw_t) );
    pPars->fLatchCorr  = fLatchCorr;
    pPars->fVerbose = fVeryVerbose;
    if ( fVerbose )
    {
        printf( "Original miter:       Latches = %5d. Nodes = %6d.\n", 
            Aig_ManRegNum(pNew), Aig_ManNodeNum(pNew) );
    }
//Aig_ManDumpBlif( pNew, "after.blif", NULL, NULL );

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
    RetValue = Fra_FraigMiterStatus( pNew );
    if ( RetValue >= 0 )
        goto finish;

    // perform phase abstraction
clk = clock();
    if ( fPhaseAbstract )
    {
        extern Aig_Man_t * Saig_ManPhaseAbstractAuto( Aig_Man_t * p, int fVerbose );
        pNew->nTruePis = Aig_ManPiNum(pNew) - Aig_ManRegNum(pNew); 
        pNew->nTruePos = Aig_ManPoNum(pNew) - Aig_ManRegNum(pNew); 
        pNew = Saig_ManPhaseAbstractAuto( pTemp = pNew, 0 );
        Aig_ManStop( pTemp );
        if ( fVerbose )
        {
            printf( "Phase abstraction:    Latches = %5d. Nodes = %6d. ", 
                Aig_ManRegNum(pNew), Aig_ManNodeNum(pNew) );
PRT( "Time", clock() - clk );
        }
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
    pNew = Aig_ManDupOrdered( pTemp = pNew );
//    pNew = Aig_ManDupDfs( pTemp = pNew );
    Aig_ManStop( pTemp );
    if ( TimeLimit )
    {
        TimeLeft = (float)TimeLimit - ((float)(clock()-clkTotal)/(float)(CLOCKS_PER_SEC));
        TimeLeft = AIG_MAX( TimeLeft, 0.0 );
        if ( TimeLeft == 0.0 )
        {
            printf( "Runtime limit exceeded.\n" );
            RetValue = -1;
            goto finish;
        }
    }
    pNew = Fra_FraigLatchCorrespondence( pTemp = pNew, 0, 100000, 1, fVeryVerbose, &nIter, TimeLeft );
    if ( pNew == NULL )
    {
        pNew = pTemp;
        RetValue = -1;
        goto finish;
    }
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

    if ( TimeLimit )
    {
        TimeLeft = (float)TimeLimit - ((float)(clock()-clkTotal)/(float)(CLOCKS_PER_SEC));
        TimeLeft = AIG_MAX( TimeLeft, 0.0 );
        if ( TimeLeft == 0.0 )
        {
            printf( "Runtime limit exceeded.\n" );
            RetValue = -1;
            goto finish;
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

    if ( pNew->nRegs == 0 )
        RetValue = Fra_FraigCec( &pNew, 0 );

    RetValue = Fra_FraigMiterStatus( pNew );
    if ( RetValue >= 0 )
        goto finish;

    if ( TimeLimit )
    {
        TimeLeft = (float)TimeLimit - ((float)(clock()-clkTotal)/(float)(CLOCKS_PER_SEC));
        TimeLeft = AIG_MAX( TimeLeft, 0.0 );
        if ( TimeLeft == 0.0 )
        {
            printf( "Runtime limit exceeded.\n" );
            RetValue = -1;
            goto finish;
        }
    }

    // perform min-area retiming
    if ( fRetimeRegs && pNew->nRegs )
    {
    extern Aig_Man_t * Saig_ManRetimeMinArea( Aig_Man_t * p, int nMaxIters, int fForwardOnly, int fBackwardOnly, int fInitial, int fVerbose );
clk = clock();
    pNew->nTruePis = Aig_ManPiNum(pNew) - Aig_ManRegNum(pNew); 
    pNew->nTruePos = Aig_ManPoNum(pNew) - Aig_ManRegNum(pNew); 
//        pNew = Rtm_ManRetime( pTemp = pNew, 1, 1000, 0 );
    pNew = Saig_ManRetimeMinArea( pTemp = pNew, 1000, 0, 0, 1, 0 );
    Aig_ManStop( pTemp );
    pNew = Aig_ManDupOrdered( pTemp = pNew );
    Aig_ManStop( pTemp );
    if ( fVerbose )
    {
    printf( "Min-reg retiming:     Latches = %5d. Nodes = %6d. ", 
        Aig_ManRegNum(pNew), Aig_ManNodeNum(pNew) );
PRT( "Time", clock() - clk );
    }
    }

    // perform seq sweeping while increasing the number of frames
    RetValue = Fra_FraigMiterStatus( pNew );
    if ( RetValue == -1 )
    for ( nFrames = 1; nFrames <= nFramesMax; nFrames *= 2 )
    {
        if ( TimeLimit )
        {
            TimeLeft = (float)TimeLimit - ((float)(clock()-clkTotal)/(float)(CLOCKS_PER_SEC));
            TimeLeft = AIG_MAX( TimeLeft, 0.0 );
            if ( TimeLeft == 0.0 )
            {
                printf( "Runtime limit exceeded.\n" );
                RetValue = -1;
                goto finish;
            }
        }

clk = clock();
        pPars->nFramesK = nFrames;
        pPars->TimeLimit = TimeLeft;
        pNew = Fra_FraigInduction( pTemp = pNew, pPars );
        if ( pNew == NULL )
        {
            pNew = pTemp;
            RetValue = -1;
            goto finish;
        }
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

        // perform retiming
//        if ( fRetimeFirst && pNew->nRegs )
        if ( pNew->nRegs )
        {
        extern Aig_Man_t * Saig_ManRetimeMinArea( Aig_Man_t * p, int nMaxIters, int fForwardOnly, int fBackwardOnly, int fInitial, int fVerbose );
clk = clock();
        pNew->nTruePis = Aig_ManPiNum(pNew) - Aig_ManRegNum(pNew); 
        pNew->nTruePos = Aig_ManPoNum(pNew) - Aig_ManRegNum(pNew); 
//        pNew = Rtm_ManRetime( pTemp = pNew, 1, 1000, 0 );
        pNew = Saig_ManRetimeMinArea( pTemp = pNew, 1000, 0, 0, 1, 0 );
        Aig_ManStop( pTemp );
        pNew = Aig_ManDupOrdered( pTemp = pNew );
        Aig_ManStop( pTemp );
        if ( fVerbose )
        {
            printf( "Min-reg retiming:     Latches = %5d. Nodes = %6d. ", 
                Aig_ManRegNum(pNew), Aig_ManNodeNum(pNew) );
PRT( "Time", clock() - clk );
        }
        }

        if ( pNew->nRegs )
            pNew = Aig_ManConstReduce( pNew, 0 );

        // perform rewriting
clk = clock();
        pNew = Aig_ManDupOrdered( pTemp = pNew );
        Aig_ManStop( pTemp );
//        pNew = Dar_ManRewriteDefault( pTemp = pNew );
        pNew = Dar_ManCompress2( pTemp = pNew, 1, 0, 1, 0 ); 
        Aig_ManStop( pTemp );
        if ( fVerbose )
        {
            printf( "Rewriting:            Latches = %5d. Nodes = %6d. ", 
                Aig_ManRegNum(pNew), Aig_ManNodeNum(pNew) );
PRT( "Time", clock() - clk );
        } 

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

    // try interplation
clk = clock();
    if ( RetValue == -1 && Aig_ManRegNum(pNew) > 0 )
    {
        extern int Saig_Interpolate( Aig_Man_t * pAig, int nConfLimit, int fRewrite, int fTransLoop, int fVerbose, int * pDepth );
        int Depth;
        pNew->nTruePis = Aig_ManPiNum(pNew) - Aig_ManRegNum(pNew); 
        pNew->nTruePos = Aig_ManPoNum(pNew) - Aig_ManRegNum(pNew); 
        RetValue = Saig_Interpolate( pNew, 10000, 0, 1, 0, &Depth );
        if ( fVerbose )
        {
        if ( RetValue == 1 )
            printf( "Property proved using interpolation.  " );
        else if ( RetValue == 0 )
            printf( "Property DISPROVED with cex at depth %d using interpolation.  ", Depth );
        else if ( RetValue == -1 )
            printf( "Property UNDECIDED after interpolation.  " );
        else
            assert( 0 ); 
PRT( "Time", clock() - clk );
        }
    }

    // try reachability analysis
    if ( RetValue == -1 && Aig_ManRegNum(pNew) < 200 && Aig_ManRegNum(pNew) > 0 )
    {
        extern int Aig_ManVerifyUsingBdds( Aig_Man_t * p, int nBddMax, int nIterMax, int fPartition, int fReorder, int fVerbose );
        pNew->nTruePis = Aig_ManPiNum(pNew) - Aig_ManRegNum(pNew); 
        pNew->nTruePos = Aig_ManPoNum(pNew) - Aig_ManRegNum(pNew); 
        RetValue = Aig_ManVerifyUsingBdds( pNew, 100000, 1000, 1, 1, 0 );
    }

finish:
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


