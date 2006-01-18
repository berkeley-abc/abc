/**CFile****************************************************************

  FileName    [fraigEngine.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: fraigEngine.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Starts the simulation engine for the first time.]

  Description [Tries several random patterns and their distance-1 
  minterms hoping to get simulation started.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_EngineSimulateFirst( Aig_Man_t * p )
{
    Aig_Pattern_t * pPat;
    int i;
    assert( Vec_PtrSize(p->vPats) == 0 );
    for ( i = 0; i < p->nPatsMax; i++ )
    {
        pPat = Aig_PatternAlloc( Aig_ManPiNum(p) );
        Aig_PatternRandom( pPat );
        Vec_PtrPush( p->vPats, pPat );
        if ( !Aig_EngineSimulate( p ) )
            return;
    }
}

/**Function*************************************************************

  Synopsis    [Implements intelligent simulation engine.]

  Description [Assumes that the good simulation patterns have been 
  assigned (p->vPats). Simulates until all of them are gone. Returns 1 
  if some classes are left. Returns 0 if there is no more classes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_EngineSimulate( Aig_Man_t * p )
{
    Aig_Pattern_t * pPat;
    if ( Vec_VecSize(p->vClasses) == 0 )
        return 0;
    assert( Vec_PtrSize(p->vPats) > 0 );
    // process patterns
    while ( Vec_PtrSize(p->vPats) > 0 && Vec_VecSize(p->vClasses) > 0 )
    {
        // get the pattern and create new siminfo
        pPat = Vec_PtrPop(p->vPats);
        // create the new siminfo
        Aig_SimInfoFromPattern( p->pInfoPi, pPat );
        // free the patter
        Aig_PatternFree( pPat );

        // simulate this info
        Aig_ManSimulateInfo( p, p->pInfoPi, p->pInfoTemp );
        // split the classes and collect the new patterns
        Aig_ManUpdateClasses( p, p->pInfoTemp, p->vClasses );
    }
    return Vec_VecSize(p->vClasses) > 0;
}

/**Function*************************************************************

  Synopsis    [Simulates all nodes using random simulation for the first time.]

  Description [Assigns the original simulation info and the storage for the
  future simulation info.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_EngineSimulateRandomFirst( Aig_Man_t * p )
{
    Aig_SimInfo_t * pInfoPi, * pInfoAll;
    assert( !p->pInfo && !p->pInfoTemp );
    // create random PI info
    pInfoPi = Aig_SimInfoAlloc( p->vPis->nSize, Aig_BitWordNum(p->pParam->nPatsRand), 0 );
    Aig_SimInfoRandom( pInfoPi );
    // allocate sim info for all nodes
    pInfoAll = Aig_SimInfoAlloc( p->vNodes->nSize, pInfoPi->nWords, 1 );
    // simulate though the circuit
    Aig_ManSimulateInfo( p, pInfoPi, pInfoAll );
    // detect classes
    p->vClasses = Aig_ManDeriveClassesFirst( p, pInfoAll );
    Aig_SimInfoFree( pInfoAll );
    // save simulation info
    p->pInfo     = pInfoPi;
    p->pInfoPi   = Aig_SimInfoAlloc( p->vPis->nSize,   Aig_BitWordNum(p->vPis->nSize),  0 );
    p->pInfoTemp = Aig_SimInfoAlloc( p->vNodes->nSize, Aig_BitWordNum(p->vPis->nSize),  1 );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


