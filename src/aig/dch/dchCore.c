/**CFile****************************************************************

  FileName    [dchCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Choice computation for tech-mapping.]

  Synopsis    [The core procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 29, 2008.]

  Revision    [$Id: dchCore.c,v 1.00 2008/07/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "dchInt.h"

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
void Dch_ManSetDefaultParams( Dch_Pars_t * p )
{
    memset( p, 0, sizeof(Dch_Pars_t) );
    p->nWords         =     8;  // the number of simulation words
    p->nBTLimit       =  1000;  // conflict limit at a node
    p->nSatVarMax     =  5000;  // the max number of SAT variables
    p->fSynthesis     =     1;  // derives three snapshots
    p->fPolarFlip     =     1;  // uses polarity adjustment
    p->fSimulateTfo   =     1;  // simulate TFO
    p->fVerbose       =     0;  // verbose stats
    p->nNodesAhead    =  1000;  // the lookahead in terms of nodes
    p->nCallsRecycle  =   100;  // calls to perform before recycling SAT solver
}

/**Function*************************************************************

  Synopsis    [Performs computation of AIGs with choices.]

  Description [Takes several AIGs and performs choicing.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Dch_ComputeChoices( Vec_Ptr_t * vAigs, Dch_Pars_t * pPars )
{
    Dch_Man_t * p;
    Aig_Man_t * pResult;
    int clk, clkTotal = clock();
    assert( Vec_PtrSize(vAigs) > 0 );
    // reset random numbers
    Aig_ManRandom(1);
    // start the choicing manager
    p = Dch_ManCreate( vAigs, pPars );
    // compute candidate equivalence classes
clk = clock(); 
    p->ppClasses = Dch_CreateCandEquivClasses( p->pAigTotal, pPars->nWords, pPars->fVerbose );
p->timeSimInit = clock() - clk;
//    Dch_ClassesPrint( p->ppClasses, 0 );
    p->nLits = Dch_ClassesLitNum( p->ppClasses );
    // perform SAT sweeping
    Dch_ManSweep( p );
    // count the number of representatives
    p->nReprs = Dch_DeriveChoiceCountReprs( p->pAigTotal );
    // create choices
clk = clock();
    pResult = Dch_DeriveChoiceAig( p->pAigTotal );
p->timeChoice = clock() - clk;
//    Aig_ManCleanup( p->pAigTotal );
//    pResult = Aig_ManDupSimpleDfs( p->pAigTotal );
    // count the number of equivalences and choices
    p->nEquivs = Dch_DeriveChoiceCountEquivs( pResult );
    p->nChoices = Aig_ManCountChoices( pResult );
p->timeTotal = clock() - clkTotal;
    Dch_ManStop( p );
    return pResult;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


