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
#include "int.h"

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
void Fra_SecSetDefaultParams( Fra_Sec_t * p )
{
    memset( p, 0, sizeof(Fra_Sec_t) );
    p->fTryComb          =   1;  // try CEC call as a preprocessing step
    p->fTryBmc           =   1;  // try BMC call as a preprocessing step 
    p->nFramesMax        =   4;  // the max number of frames used for induction
    p->fPhaseAbstract    =   1;  // enables phase abstraction
    p->fRetimeFirst      =   1;  // enables most-forward retiming at the beginning
    p->fRetimeRegs       =   1;  // enables min-register retiming at the beginning
    p->fFraiging         =   1;  // enables fraiging at the beginning
    p->fInterpolation    =   1;  // enables interpolation
    p->fReachability     =   1;  // enables BDD based reachability
    p->fStopOnFirstFail  =   1;  // enables stopping after first output of a miter has failed to prove
    p->fSilent           =   0;  // disables all output
    p->fVerbose          =   0;  // enables verbose reporting of statistics
    p->fVeryVerbose      =   0;  // enables very verbose reporting  
    p->TimeLimit         =   0;  // enables the timeout
    // internal parameters
    p->fReportSolution   =   0;  // enables specialized format for reporting solution
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_FraigSec( Aig_Man_t * p, Fra_Sec_t * pParSec )
{
    Fra_Ssw_t Pars, * pPars = &Pars;
    Fra_Sml_t * pSml;
    Aig_Man_t * pNew, * pTemp;
    int nFrames, RetValue, nIter, clk, clkTotal = clock();
    int TimeOut = 0;
    int fLatchCorr = 0;
    float TimeLeft = 0.0;

    // try the miter before solving
    pNew = Aig_ManDupSimple( p );
    RetValue = Fra_FraigMiterStatus( pNew );
    if ( RetValue >= 0 )
        goto finish;

    // prepare parameters
    memset( pPars, 0, sizeof(Fra_Ssw_t) );
    pPars->fLatchCorr  = fLatchCorr;
    pPars->fVerbose = pParSec->fVeryVerbose;
    if ( pParSec->fVerbose )
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
    if ( pParSec->fVerbose )
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
    if ( pParSec->fPhaseAbstract )
    {
        extern Aig_Man_t * Saig_ManPhaseAbstractAuto( Aig_Man_t * p, int fVerbose );
        pNew->nTruePis = Aig_ManPiNum(pNew) - Aig_ManRegNum(pNew); 
        pNew->nTruePos = Aig_ManPoNum(pNew) - Aig_ManRegNum(pNew); 
        pNew = Saig_ManPhaseAbstractAuto( pTemp = pNew, 0 );
        Aig_ManStop( pTemp );
        if ( pParSec->fVerbose )
        {
            printf( "Phase abstraction:    Latches = %5d. Nodes = %6d. ", 
                Aig_ManRegNum(pNew), Aig_ManNodeNum(pNew) );
PRT( "Time", clock() - clk );
        }
    }

    // perform forward retiming
    if ( pParSec->fRetimeFirst && pNew->nRegs )
    {
clk = clock();
    pNew = Rtm_ManRetime( pTemp = pNew, 1, 1000, 0 );
    Aig_ManStop( pTemp );
    if ( pParSec->fVerbose )
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
    if ( RetValue == -1 && pParSec->TimeLimit )
    {
        TimeLeft = (float)pParSec->TimeLimit - ((float)(clock()-clkTotal)/(float)(CLOCKS_PER_SEC));
        TimeLeft = AIG_MAX( TimeLeft, 0.0 );
        if ( TimeLeft == 0.0 )
        {
            if ( !pParSec->fSilent )
                printf( "Runtime limit exceeded.\n" );
            RetValue = -1;
            TimeOut = 1;
            goto finish;
        }
    }
    pNew = Fra_FraigLatchCorrespondence( pTemp = pNew, 0, 1000, 1, pParSec->fVeryVerbose, &nIter, TimeLeft );
    p->pSeqModel = pTemp->pSeqModel; pTemp->pSeqModel = NULL;
    if ( pNew == NULL )
    {
        if ( p->pSeqModel )
        {
            RetValue = 0;
            if ( !pParSec->fSilent )
            {
                printf( "Networks are NOT EQUIVALENT after simulation.   " );
PRT( "Time", clock() - clkTotal );
            }
            if ( pParSec->fReportSolution && !pParSec->fRecursive )
            {
            printf( "SOLUTION: FAIL       " );
PRT( "Time", clock() - clkTotal );
            }
            return RetValue;
        }
        pNew = pTemp;
        RetValue = -1;
        TimeOut = 1;
        goto finish;
    }
    Aig_ManStop( pTemp );

    if ( pParSec->fVerbose )
    {
        printf( "Latch-corr (I=%3d):   Latches = %5d. Nodes = %6d. ", 
            nIter, Aig_ManRegNum(pNew), Aig_ManNodeNum(pNew) );
PRT( "Time", clock() - clk );
    }
    }

    if ( RetValue == -1 && pParSec->TimeLimit )
    {
        TimeLeft = (float)pParSec->TimeLimit - ((float)(clock()-clkTotal)/(float)(CLOCKS_PER_SEC));
        TimeLeft = AIG_MAX( TimeLeft, 0.0 );
        if ( TimeLeft == 0.0 )
        {
            if ( !pParSec->fSilent )
                printf( "Runtime limit exceeded.\n" );
            RetValue = -1;
            TimeOut = 1;
            goto finish;
        }
    }

    // perform fraiging
    if ( pParSec->fFraiging )
    {
clk = clock();
    pNew = Fra_FraigEquivence( pTemp = pNew, 100, 0 );
    Aig_ManStop( pTemp );
    if ( pParSec->fVerbose )
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

    if ( RetValue == -1 && pParSec->TimeLimit )
    {
        TimeLeft = (float)pParSec->TimeLimit - ((float)(clock()-clkTotal)/(float)(CLOCKS_PER_SEC));
        TimeLeft = AIG_MAX( TimeLeft, 0.0 );
        if ( TimeLeft == 0.0 )
        {
            if ( !pParSec->fSilent )
                printf( "Runtime limit exceeded.\n" );
            RetValue = -1;
            TimeOut = 1;
            goto finish;
        }
    }

    // perform min-area retiming
    if ( pParSec->fRetimeRegs && pNew->nRegs )
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
    if ( pParSec->fVerbose )
    {
    printf( "Min-reg retiming:     Latches = %5d. Nodes = %6d. ", 
        Aig_ManRegNum(pNew), Aig_ManNodeNum(pNew) );
PRT( "Time", clock() - clk );
    }
    }

    // perform seq sweeping while increasing the number of frames
    RetValue = Fra_FraigMiterStatus( pNew );
    if ( RetValue == -1 )
    for ( nFrames = 1; nFrames <= pParSec->nFramesMax; nFrames *= 2 )
    {
        if ( RetValue == -1 && pParSec->TimeLimit )
        {
            TimeLeft = (float)pParSec->TimeLimit - ((float)(clock()-clkTotal)/(float)(CLOCKS_PER_SEC));
            TimeLeft = AIG_MAX( TimeLeft, 0.0 );
            if ( TimeLeft == 0.0 )
            {
                if ( !pParSec->fSilent )
                    printf( "Runtime limit exceeded.\n" );
                RetValue = -1;
                TimeOut = 1;
                goto finish;
            }
        }

clk = clock();
        pPars->nFramesK = nFrames;
        pPars->TimeLimit = TimeLeft;
        pPars->fSilent = pParSec->fSilent;
        pNew = Fra_FraigInduction( pTemp = pNew, pPars );
        if ( pNew == NULL )
        {
            pNew = pTemp;
            RetValue = -1;
            TimeOut = 1;
            goto finish;
        }
        Aig_ManStop( pTemp );
        RetValue = Fra_FraigMiterStatus( pNew );
        if ( pParSec->fVerbose )
        { 
            printf( "K-step (K=%2d,I=%3d):  Latches = %5d. Nodes = %6d. ", 
                nFrames, pPars->nIters, Aig_ManRegNum(pNew), Aig_ManNodeNum(pNew) );
PRT( "Time", clock() - clk );
        }
        if ( RetValue != -1 )
            break;

        // perform retiming
//        if ( pParSec->fRetimeFirst && pNew->nRegs )
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
        if ( pParSec->fVerbose )
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
        if ( pParSec->fVerbose )
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
        if ( pParSec->fVerbose )
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
            if ( !pParSec->fSilent )
            {
                printf( "Networks are NOT EQUIVALENT after simulation.   " );
PRT( "Time", clock() - clkTotal );
            }
            if ( pParSec->fReportSolution && !pParSec->fRecursive )
            {
            printf( "SOLUTION: FAIL       " );
PRT( "Time", clock() - clkTotal );
            }
            return RetValue;
        }
        Fra_SmlStop( pSml );
        }
    }

    // get the miter status
    RetValue = Fra_FraigMiterStatus( pNew );

    // try interplation
clk = clock();
    if ( pParSec->fInterpolation && RetValue == -1 && Aig_ManRegNum(pNew) > 0 && Aig_ManPoNum(pNew)-Aig_ManRegNum(pNew) == 1 )
    {
        Inter_ManParams_t Pars, * pPars = &Pars;
        int Depth;
        pNew->nTruePis = Aig_ManPiNum(pNew) - Aig_ManRegNum(pNew); 
        pNew->nTruePos = Aig_ManPoNum(pNew) - Aig_ManRegNum(pNew); 

        Inter_ManSetDefaultParams( pPars );
        pPars->fVerbose = pParSec->fVeryVerbose;
        RetValue = Inter_ManPerformInterpolation( pNew, pPars, &Depth );

        if ( pParSec->fVerbose )
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
    if ( pParSec->fReachability && RetValue == -1 && Aig_ManRegNum(pNew) > 0 && Aig_ManRegNum(pNew) < 150 )
    {
        extern int Aig_ManVerifyUsingBdds( Aig_Man_t * p, int nBddMax, int nIterMax, int fPartition, int fReorder, int fVerbose, int fSilent );
        pNew->nTruePis = Aig_ManPiNum(pNew) - Aig_ManRegNum(pNew); 
        pNew->nTruePos = Aig_ManPoNum(pNew) - Aig_ManRegNum(pNew); 
        RetValue = Aig_ManVerifyUsingBdds( pNew, 100000, 1000, 1, 1, 0, pParSec->fSilent );
    }

    // try one-output at a time
    if ( RetValue == -1 && Aig_ManPoNum(pNew)-Aig_ManRegNum(pNew) > 1 )
    {
        Aig_Man_t * pNew2;
        int i, TimeLimit2, RetValue2, fOneUnsolved = 0, iCount, Counter = 0;
        // count unsolved outputs
        for ( i = 0; i < Aig_ManPoNum(pNew)-Aig_ManRegNum(pNew); i++ )
            if ( !Aig_ObjIsConst1( Aig_ObjFanin0(Aig_ManPo(pNew,i)) ) )
                Counter++;
        if ( !pParSec->fSilent )
            printf( "*** The miter has %d outputs (out of %d total) unsolved in the multi-output form.\n", 
                Counter, Aig_ManPoNum(pNew)-Aig_ManRegNum(pNew) );
        iCount = 0;
        for ( i = 0; i < Aig_ManPoNum(pNew)-Aig_ManRegNum(pNew); i++ )
        {
            int TimeLimitCopy = 0;
            // get the remaining time for this output
            if ( pParSec->TimeLimit )
            {
                TimeLeft = (float)pParSec->TimeLimit - ((float)(clock()-clkTotal)/(float)(CLOCKS_PER_SEC));
                TimeLeft = AIG_MAX( TimeLeft, 0.0 );
                if ( TimeLeft == 0.0 )
                {
                    if ( !pParSec->fSilent )
                        printf( "Runtime limit exceeded.\n" );
                    TimeOut = 1;
                    goto finish;
                }
                TimeLimit2 = 1 + (int)TimeLeft;
            }
            else
                TimeLimit2 = 0;
            if ( Aig_ObjIsConst1( Aig_ObjFanin0(Aig_ManPo(pNew,i)) ) )
                continue;
            iCount++;
            if ( !pParSec->fSilent )
                printf( "*** Running output %d of the miter (number %d out of %d unsolved).\n", i, iCount, Counter );
            pNew2 = Aig_ManDupOneOutput( pNew, i, 1 );
            
            TimeLimitCopy = pParSec->TimeLimit;
            pParSec->TimeLimit = TimeLimit2;
            pParSec->fRecursive = 1;
            RetValue2 = Fra_FraigSec( pNew2, pParSec );
            pParSec->fRecursive = 0;
            pParSec->TimeLimit = TimeLimitCopy;

            Aig_ManStop( pNew2 );
            if ( RetValue2 == 0 )
                goto finish;
            if ( RetValue2 == -1 )
            {
                fOneUnsolved = 1;
                if ( pParSec->fStopOnFirstFail )
                    break;
            }
        }
        if ( fOneUnsolved )
            RetValue = -1;
        else
            RetValue = 1;
        if ( !pParSec->fSilent )
            printf( "*** Finished running separate outputs of the miter.\n" );
    }

finish:
    // report the miter
    if ( RetValue == 1 )
    {
        if ( !pParSec->fSilent )
        {
            printf( "Networks are equivalent.   " );
PRT( "Time", clock() - clkTotal );
        }
        if ( pParSec->fReportSolution && !pParSec->fRecursive )
        {
        printf( "SOLUTION: PASS       " );
PRT( "Time", clock() - clkTotal );
        }
    }
    else if ( RetValue == 0 )
    {
        if ( !pParSec->fSilent )
        {
            printf( "Networks are NOT EQUIVALENT.   " );
PRT( "Time", clock() - clkTotal );
        }
        if ( pParSec->fReportSolution && !pParSec->fRecursive )
        {
        printf( "SOLUTION: FAIL       " );
PRT( "Time", clock() - clkTotal );
        }
    }
    else 
    {
        if ( !pParSec->fSilent )
        {
            printf( "Networks are UNDECIDED.   " );
PRT( "Time", clock() - clkTotal );
        }
        if ( pParSec->fReportSolution && !pParSec->fRecursive )
        {
        printf( "SOLUTION: UNDECIDED  " );
PRT( "Time", clock() - clkTotal );
        }
        if ( !TimeOut && !pParSec->fSilent )
        {
            static int Counter = 1;
            char pFileName[1000];
            sprintf( pFileName, "sm%03d.aig", Counter++ );
            Ioa_WriteAiger( pNew, pFileName, 0, 0 );
            printf( "The unsolved reduced miter is written into file \"%s\".\n", pFileName );
        }
    }
    if ( pNew )
        Aig_ManStop( pNew );
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


