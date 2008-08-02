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

  Synopsis    [Creates the manager.]

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
    p->vAigs      = vAigs;
    p->pAigTotal  = Dch_DeriveTotalAig( vAigs );
    // SAT solving
    p->nSatVars   = 1;
    p->pSatVars   = CALLOC( int, Aig_ManObjNumMax(p->pAigTotal) );
    p->vUsedNodes = Vec_PtrAlloc( 1000 );
    p->vFanins    = Vec_PtrAlloc( 100 );
    p->vRoots     = Vec_PtrAlloc( 1000 );
    // equivalences proved
    p->pReprsProved = CALLOC( Aig_Obj_t *, Aig_ManObjNumMax(p->pAigTotal) );
    return p;
}

/**Function*************************************************************

  Synopsis    [Prints stats of the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dch_ManPrintStats( Dch_Man_t * p )
{
//    Aig_Man_t * pAig;
    int i;
    for ( i = 0; i < 85; i++ )
        printf( " " );
    printf( "\r" );
//    printf( "Choicing will be performed with %d AIGs:\n", Vec_PtrSize(p->vAigs) );
//    Vec_PtrForEachEntry( p->vAigs, pAig, i )
//        Aig_ManPrintStats( pAig );
    printf( "Parameters: Sim words = %d. Conf limit = %d. SAT var max = %d.\n", 
        p->pPars->nWords, p->pPars->nBTLimit, p->pPars->nSatVarMax );
    printf( "AIG nodes : Total = %6d. Dangling = %6d. Main = %6d. (%6.2f %%)\n", 
        Aig_ManNodeNum(p->pAigTotal), 
        Aig_ManNodeNum(p->pAigTotal)-Aig_ManNodeNum(Vec_PtrEntry(p->vAigs,0)),
        Aig_ManNodeNum(Vec_PtrEntry(p->vAigs,0)),
        100.0 * Aig_ManNodeNum(Vec_PtrEntry(p->vAigs,0))/Aig_ManNodeNum(p->pAigTotal) );
    printf( "SAT solver: Vars = %d. Max cone = %d. Recycles = %d.\n", 
        p->nSatVars, p->nConeMax, p->nRecycles );
    printf( "SAT calls : All = %6d. Unsat = %6d. Sat = %6d. Fail = %6d.\n", 
        p->nSatCalls, p->nSatCalls-p->nSatCallsSat-p->nSatFailsReal, 
        p->nSatCallsSat, p->nSatFailsReal );
    printf( "Choices   : Lits = %6d. Reprs = %5d. Equivs = %5d. Choices = %5d.\n", 
        p->nLits, p->nReprs, p->nEquivs, p->nChoices );
    printf( "Runtime statistics:\n" );
    p->timeOther = p->timeTotal-p->timeSimInit-p->timeSimSat-p->timeSat-p->timeChoice;
    PRTP( "Sim init   ", p->timeSimInit,  p->timeTotal );
    PRTP( "Sim SAT    ", p->timeSimSat,   p->timeTotal );
    PRTP( "SAT solving", p->timeSat,      p->timeTotal );
    PRTP( "  sat      ", p->timeSatSat,   p->timeTotal );
    PRTP( "  unsat    ", p->timeSatUnsat, p->timeTotal );
    PRTP( "  undecided", p->timeSatUndec, p->timeTotal );
    PRTP( "Choice     ", p->timeChoice,   p->timeTotal );
    PRTP( "Other      ", p->timeOther,    p->timeTotal );
    PRTP( "TOTAL      ", p->timeTotal,    p->timeTotal );
    PRT( "Synthesis  ", p->pPars->timeSynth );
}

/**Function*************************************************************

  Synopsis    [Frees the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dch_ManStop( Dch_Man_t * p )
{
    if ( p->pPars->fVerbose )
        Dch_ManPrintStats( p );
    if ( p->pAigTotal )
        Aig_ManStop( p->pAigTotal );
    if ( p->pAigFraig )
        Aig_ManStop( p->pAigFraig );
    if ( p->ppClasses )
        Dch_ClassesStop( p->ppClasses );
    if ( p->pSat )
        sat_solver_delete( p->pSat );
    Vec_PtrFree( p->vUsedNodes );
    Vec_PtrFree( p->vFanins );
    Vec_PtrFree( p->vRoots );
    FREE( p->pReprsProved );
    FREE( p->pSatVars );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Recycles the SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dch_ManSatSolverRecycle( Dch_Man_t * p )
{
    int Lit;
    if ( p->pSat )
    {
        sat_solver_delete( p->pSat );
        memset( p->pSatVars, 0, sizeof(int) * Aig_ManObjNumMax(p->pAigTotal) );
    }
    p->pSat = sat_solver_new();
    sat_solver_setnvars( p->pSat, 1000 );
    // var 0 is reserved for const1 node - add the clause
    Lit = toLit( 0 );
    sat_solver_addclause( p->pSat, &Lit, &Lit + 1 );
    p->nSatVars = 1;
    p->nRecycles++;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


