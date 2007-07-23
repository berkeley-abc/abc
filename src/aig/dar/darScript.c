/**CFile****************************************************************

  FileName    [darScript.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting.]

  Synopsis    [Rewriting scripts.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: darScript.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "darInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Reproduces script "compress2".]

  Description []
               
  SideEffects [This procedure does not tighten level during restructuring.]

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Dar_ManCompress2_old( Aig_Man_t * pAig, int fVerbose )
//alias compress2   "b -l; rw -l; rf -l; b -l; rw -l; rwz -l; b -l; rfz -l; rwz -l; b -l"
{
    Aig_Man_t * pTemp;
    int fBalance = 0;

    Dar_RwrPar_t ParsRwr, * pParsRwr = &ParsRwr;
    Dar_RefPar_t ParsRef, * pParsRef = &ParsRef;

    Dar_ManDefaultRwrParams( pParsRwr );
    Dar_ManDefaultRefParams( pParsRef );

    pParsRwr->fVerbose = fVerbose;
    pParsRef->fVerbose = fVerbose;

    // balance
    pAig = Dar_ManBalance( pTemp = pAig, fBalance );
    Aig_ManStop( pTemp );
    
    // rewrite
    Dar_ManRewrite( pAig, pParsRwr );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );
    
    // refactor
    Dar_ManRefactor( pAig, pParsRef );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );

    // balance
    pAig = Dar_ManBalance( pTemp = pAig, fBalance );
    Aig_ManStop( pTemp );
    
    // rewrite
    Dar_ManRewrite( pAig, pParsRwr );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );

    pParsRwr->fUseZeros = 1;
    pParsRef->fUseZeros = 1;
    
    // rewrite
    Dar_ManRewrite( pAig, pParsRwr );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );

    // balance
    pAig = Dar_ManBalance( pTemp = pAig, fBalance );
    Aig_ManStop( pTemp );
    
    // refactor
    Dar_ManRefactor( pAig, pParsRef );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );
    
    // rewrite
    Dar_ManRewrite( pAig, pParsRwr );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );

    // balance
    pAig = Dar_ManBalance( pTemp = pAig, fBalance );
    Aig_ManStop( pTemp );
    return pAig;
}

/**Function*************************************************************

  Synopsis    [Reproduces script "compress2".]

  Description []
               
  SideEffects [This procedure does not tighten level during restructuring.]

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Dar_ManCompress2_no_z( Aig_Man_t * pAig, int fVerbose )
//alias compress2   "b -l; rw -l; rf -l; b -l; rw -l; rwz -l; b -l; rfz -l; rwz -l; b -l"
{
    Aig_Man_t * pTemp;
    int fBalance = 0;

    Dar_RwrPar_t ParsRwr, * pParsRwr = &ParsRwr;
    Dar_RefPar_t ParsRef, * pParsRef = &ParsRef;

    Dar_ManDefaultRwrParams( pParsRwr );
    Dar_ManDefaultRefParams( pParsRef );

    pParsRwr->fVerbose = fVerbose;
    pParsRef->fVerbose = fVerbose;
    
    // rewrite
    Dar_ManRewrite( pAig, pParsRwr );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );
    
    // refactor
    Dar_ManRefactor( pAig, pParsRef );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );

    // balance
    pAig = Dar_ManBalance( pTemp = pAig, fBalance );
    Aig_ManStop( pTemp );
    
    // rewrite
    Dar_ManRewrite( pAig, pParsRwr );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );
    
    // refactor
    Dar_ManRefactor( pAig, pParsRef );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );

    // balance
    pAig = Dar_ManBalance( pTemp = pAig, fBalance );
    Aig_ManStop( pTemp );
    
    // rewrite
    Dar_ManRewrite( pAig, pParsRwr );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );
    
    // refactor
    Dar_ManRefactor( pAig, pParsRef );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );
    return pAig;
}

/**Function*************************************************************

  Synopsis    [Reproduces script "compress2".]

  Description []
               
  SideEffects [This procedure does not tighten level during restructuring.]

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Dar_ManCompress2( Aig_Man_t * pAig, int fVerbose )
//alias compress2   "b -l; rw -l; rf -l; b -l; rw -l; rwz -l; b -l; rfz -l; rwz -l; b -l"
{
    Aig_Man_t * pTemp;
    int fBalance = 0;

    Dar_RwrPar_t ParsRwr, * pParsRwr = &ParsRwr;
    Dar_RefPar_t ParsRef, * pParsRef = &ParsRef;

    Dar_ManDefaultRwrParams( pParsRwr );
    Dar_ManDefaultRefParams( pParsRef );

    pParsRwr->fVerbose = fVerbose;
    pParsRef->fVerbose = fVerbose;
    
    // rewrite
    Dar_ManRewrite( pAig, pParsRwr );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );
    
    // refactor
    Dar_ManRefactor( pAig, pParsRef );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );
/*
    // balance
    pAig = Dar_ManBalance( pTemp = pAig, fBalance );
    Aig_ManStop( pTemp );
*/    
    // rewrite
    Dar_ManRewrite( pAig, pParsRwr );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );

    pParsRwr->fUseZeros = 1;
    pParsRef->fUseZeros = 1;
    
    // rewrite
    Dar_ManRewrite( pAig, pParsRwr );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );

    // balance
    pAig = Dar_ManBalance( pTemp = pAig, fBalance );
    Aig_ManStop( pTemp );
    
    // refactor
    Dar_ManRefactor( pAig, pParsRef );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );
    
    // rewrite
    Dar_ManRewrite( pAig, pParsRwr );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );
    return pAig;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


