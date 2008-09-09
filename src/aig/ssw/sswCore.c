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
    p->nPartSize      =     0;  // size of the partition
    p->nOverSize      =     0;  // size of the overlap between partitions
    p->nFramesK       =     1;  // the induction depth
    p->nConstrs       =     0;  // treat the last nConstrs POs as seq constraints
    p->nBTLimit       =  1000;  // conflict limit at a node
    p->fPolarFlip     =     0;  // uses polarity adjustment
    p->fLatchCorr     =     0;  // performs register correspondence
    p->fVerbose       =     0;  // verbose stats
    p->nIters         =     0;  // the number of iterations performed
}

/**Function*************************************************************

  Synopsis    [Performs computation of signal correspondence with constraints.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Ssw_SignalCorrespondence( Aig_Man_t * pAig, Ssw_Pars_t * pPars )
{
    Aig_Man_t * pAigNew;
    Ssw_Man_t * p;
    int RetValue, nIter, clk, clkTotal = clock();
    // reset random numbers
    Aig_ManRandom( 1 );
    // start the choicing manager
    p = Ssw_ManCreate( pAig, pPars );
    // compute candidate equivalence classes
    if ( p->pPars->nConstrs == 0 )
    {
        p->ppClasses = Ssw_ClassesPrepare( pAig, pPars->fLatchCorr, pPars->nMaxLevs );
        p->pSml = Ssw_SmlStart( pAig, 0, p->nFrames + 2, 2 );
        Ssw_ClassesSetData( p->ppClasses, p->pSml, Ssw_SmlNodeHash, Ssw_SmlNodeIsConst, Ssw_SmlNodesAreEqual );
    }
    else
    {
        assert( 0 );
        p->ppClasses = Ssw_ClassesPrepareSimple( pAig, pPars->fLatchCorr, pPars->nMaxLevs );
    }
//    Ssw_ClassesSetData( p->ppClasses, NULL, NULL, Ssw_NodeIsConstCex, Ssw_NodesAreEqualCex );

    // get the starting stats
    p->nLitsBeg  = Ssw_ClassesLitNum( p->ppClasses );
    p->nNodesBeg = Aig_ManNodeNum(pAig);
    p->nRegsBeg  = Aig_ManRegNum(pAig);
    // refine classes using BMC
    if ( pPars->fVerbose )
    {
        printf( "Before BMC: " );
        Ssw_ClassesPrint( p->ppClasses, 0 );
    }
    Ssw_ManSweepBmc( p );
    Ssw_ManCleanup( p );
    if ( pPars->fVerbose )
    {
        printf( "After  BMC: " );
        Ssw_ClassesPrint( p->ppClasses, 0 );
    }
    // refine classes using induction
    for ( nIter = 0; ; nIter++ )
    {
clk = clock();
        RetValue = Ssw_ManSweep( p );
        if ( pPars->fVerbose )
        {
            printf( "%3d : Const = %6d. Cl = %6d.  L = %6d. LR = %6d.  NR = %6d. ", 
                nIter, Ssw_ClassesCand1Num(p->ppClasses), Ssw_ClassesClassNum(p->ppClasses), 
                p->nConstrTotal, p->nConstrReduced, Aig_ManNodeNum(p->pFrames) );
            PRT( "T", clock() - clk );
        } 
        Ssw_ManCleanup( p );
        if ( !RetValue )
            break;
    } 
    p->pPars->nIters = nIter + 1;
p->timeTotal = clock() - clkTotal;
    pAigNew = Aig_ManDupRepr( pAig, 0 );
    Aig_ManSeqCleanup( pAigNew );
    // get the final stats
    p->nLitsEnd  = Ssw_ClassesLitNum( p->ppClasses );
    p->nNodesEnd = Aig_ManNodeNum(pAigNew);
    p->nRegsEnd  = Aig_ManRegNum(pAigNew);
    // cleanup
    Ssw_ManStop( p );
    return pAigNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


