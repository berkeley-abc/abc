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
    p->nWords     =     4;    // the number of simulation words
    p->nBTLimit   =  1000;    // conflict limit at a node
    p->nSatVarMax =  5000;    // the max number of SAT variables
    p->fVerbose   =     1;    // verbose stats
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
    int i;

    assert( Vec_PtrSize(vAigs) > 0 );

    printf( "AIGs considered for choicing:\n" );
    Vec_PtrForEachEntry( vAigs, pResult, i )
    {
        Aig_ManPrintStats( pResult );
    }

    // start the choicing manager
    p = Dch_ManCreate( vAigs, pPars );
    // compute candidate equivalence classes
    p->ppClasses = Dch_CreateCandEquivClasses( p->pAigTotal, pPars->nWords, pPars->fVerbose );

    



    // create choices
//    pResult = Dch_DeriveChoiceAig( p->pAigTotal );
    Aig_ManCleanup( p->pAigTotal );
    pResult = Aig_ManDupSimpleDfs( p->pAigTotal );

    Dch_ManStop( p );
    return pResult;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


