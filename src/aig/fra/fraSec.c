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
int Fra_FraigSec2( Aig_Man_t * p, int nFramesFix, int fVerbose, int fVeryVerbose )
{
    Aig_Man_t * pNew;
    int nFrames, RetValue, nIter, clk, clkTotal = clock();
    int fLatchCorr = 0;
    if ( nFramesFix )
    {
        nFrames = nFramesFix;
        // perform seq sweeping for one frame number
        pNew = Fra_FraigInduction( p, 0, nFrames, 0, 0, 0, fLatchCorr, 0, fVeryVerbose, &nIter );
    }
    else
    {
        // perform seq sweeping while increasing the number of frames
        for ( nFrames = 1; ; nFrames++ )
        {
clk = clock();
            pNew = Fra_FraigInduction( p, 0, nFrames, 0, 0, 0, fLatchCorr, 0, fVeryVerbose, &nIter );
            RetValue = Fra_FraigMiterStatus( pNew );
            if ( fVerbose )
            {
                printf( "FRAMES %3d : Iters = %3d. ", nFrames, nIter );
                if ( RetValue == 1 )
                    printf( "UNSAT     " );
                else
                    printf( "UNDECIDED " );
PRT( "Time", clock() - clk );
            }
            if ( RetValue != -1 )
                break;
            Aig_ManStop( pNew );
        }
    }

    // get the miter status
    RetValue = Fra_FraigMiterStatus( pNew );
    Aig_ManStop( pNew );

    // report the miter
    if ( RetValue == 1 )
        printf( "Networks are equivalent after seq sweeping with K=%d frames (%d iters). ", nFrames, nIter );
    else if ( RetValue == 0 )
        printf( "Networks are NOT EQUIVALENT. " );
    else
        printf( "Networks are UNDECIDED after seq sweeping with K=%d frames (%d iters). ", nFrames, nIter );
PRT( "Time", clock() - clkTotal );
    return RetValue;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_FraigSec( Aig_Man_t * p, int nFramesFix, int fRetimeFirst, int fVerbose, int fVeryVerbose )
{
    Aig_Man_t * pNew, * pTemp;
    int nFrames, RetValue, nIter, clk, clkTotal = clock();
    int fLatchCorr = 0;

    pNew = Aig_ManDup( p, 1 );
    if ( fVerbose )
    {
        printf( "Original miter:       Latches = %5d. Nodes = %6d.\n", 
            Aig_ManRegNum(pNew), Aig_ManNodeNum(pNew) );
    }
//Aig_ManDumpBlif( pNew, "after.blif" );

    // perform sequential cleanup
clk = clock();
    pNew = Aig_ManReduceLaches( pNew, 0 );
    pNew = Aig_ManConstReduce( pNew, 0 );
    if ( fVerbose )
    {
        printf( "Sequential cleanup:   Latches = %5d. Nodes = %6d. ", 
            Aig_ManRegNum(pNew), Aig_ManNodeNum(pNew) );
PRT( "Time", clock() - clk );
    }

    // perform forward retiming
    if ( fRetimeFirst )
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
    pNew = Aig_ManDup( pTemp = pNew, 1 );
    Aig_ManStop( pTemp );
    pNew = Fra_FraigLatchCorrespondence( pTemp = pNew, 0, 100000, fVeryVerbose, &nIter );
    Aig_ManStop( pTemp );
    if ( fVerbose )
    {
        printf( "Latch-corr (I=%3d):   Latches = %5d. Nodes = %6d. ", 
            nIter, Aig_ManRegNum(pNew), Aig_ManNodeNum(pNew) );
PRT( "Time", clock() - clk );
    }

    // perform fraiging
clk = clock();
    pNew = Fra_FraigEquivence( pTemp = pNew, 1000 );
    Aig_ManStop( pTemp );
    if ( fVerbose )
    {
        printf( "Fraiging:             Latches = %5d. Nodes = %6d. ", 
            Aig_ManRegNum(pNew), Aig_ManNodeNum(pNew) );
PRT( "Time", clock() - clk );
    }

    // perform seq sweeping while increasing the number of frames
    RetValue = Fra_FraigMiterStatus( pNew );
    if ( RetValue == -1 )
    for ( nFrames = 1; ; nFrames *= 2 )
    {
clk = clock();
        pNew = Fra_FraigInduction( pTemp = pNew, 0, nFrames, 0, 0, 0, fLatchCorr, 0, fVeryVerbose, &nIter );
        Aig_ManStop( pTemp );
        RetValue = Fra_FraigMiterStatus( pNew );
        if ( fVerbose )
        { 
            printf( "K-step (K=%2d,I=%3d):  Latches = %5d. Nodes = %6d. ", 
                nFrames, nIter, Aig_ManRegNum(pNew), Aig_ManNodeNum(pNew) );
PRT( "Time", clock() - clk );
        }
        if ( RetValue != -1 )
            break;
        // perform rewriting
clk = clock();
        pNew = Aig_ManDup( pTemp = pNew, 1 );
        Aig_ManStop( pTemp );
        pNew = Dar_ManRewriteDefault( pTemp = pNew );
        if ( fVerbose )
        {
            printf( "Rewriting:            Latches = %5d. Nodes = %6d. ", 
                Aig_ManRegNum(pNew), Aig_ManNodeNum(pNew) );
PRT( "Time", clock() - clk );
        }
        // perform retiming
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
    // get the miter status
    RetValue = Fra_FraigMiterStatus( pNew );
    Aig_ManStop( pNew );

    // report the miter
    if ( RetValue == 1 )
        printf( "Networks are equivalent.   " );
    else if ( RetValue == 0 )
        printf( "Networks are NOT EQUIVALENT.   " );
    else
        printf( "Networks are UNDECIDED.   " );
PRT( "Time", clock() - clkTotal );
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


