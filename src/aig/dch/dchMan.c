/**CFile****************************************************************

  FileName    [dchMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Computation of equivalence classes using simulation.]

  Synopsis    [Calls to the SAT solver.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 29, 2008.]

  Revision    [$Id: dchMan.c,v 1.00 2008/07/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "dchInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates the interpolation manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dch_Man_t * Dch_ManCreate( Vec_Ptr_t * vAigs, Dch_Pars_t * pPars )
{
    Dch_Man_t * p;
    // create interpolation manager
    p = ALLOC( Dch_Man_t, 1 );
    memset( p, 0, sizeof(Dch_Man_t) );
    p->pPars      = pPars;
    // AIGs
    p->vAigs      = vAigs;
    p->pAigTotal  = Dch_DeriveTotalAig( vAigs );
    // equivalence classes
    Aig_ManReprStart( p->pAigTotal, Aig_ManObjNumMax(p->pAigTotal) );
    // SAT solving
    p->ppSatVars  = CALLOC( Vec_Int_t *, Aig_ManObjNumMax(p->pAigTotal) );
    p->vUsedNodes = Vec_PtrAlloc( 1000 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Frees the interpolation manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dch_ManStop( Dch_Man_t * p )
{
    if ( p->pPars->fVerbose )
    {
/*
        p->timeOther = p->timeTotal-p->timeRwr-p->timeCnf-p->timeSat-p->timeInt-p->timeEqu;
        printf( "Runtime statistics:\n" );
        PRTP( "Rewriting  ", p->timeRwr,   p->timeTotal );
        PRTP( "CNF mapping", p->timeCnf,   p->timeTotal );
        PRTP( "SAT solving", p->timeSat,   p->timeTotal );
        PRTP( "Interpol   ", p->timeInt,   p->timeTotal );
        PRTP( "Containment", p->timeEqu,   p->timeTotal );
        PRTP( "Other      ", p->timeOther, p->timeTotal );
        PRTP( "TOTAL      ", p->timeTotal, p->timeTotal );
*/
    }
    if ( p->pAigTotal )
        Aig_ManStop( p->pAigTotal );
    if ( p->pAigFraig )
        Aig_ManStop( p->pAigFraig );
    FREE( p->ppClasses );
    FREE( p->ppSatVars );
    Vec_PtrFree( p->vUsedNodes );
    free( p );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


