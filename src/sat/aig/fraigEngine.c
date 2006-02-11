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
    pInfoPi = Aig_SimInfoAlloc( Aig_ManPiNum(p), p->pParam->nPatsRand, 0 );
    Aig_SimInfoRandom( pInfoPi );
    // allocate sim info for all nodes
    pInfoAll = Aig_SimInfoAlloc( Aig_ManNodeNum(p), p->pParam->nPatsRand, 1 );
    // simulate though the circuit
    Aig_ManSimulateInfo( p, pInfoPi, pInfoAll );
    // detect classes
    p->vClasses = Aig_ManDeriveClassesFirst( p, pInfoAll );
    Aig_SimInfoFree( pInfoAll );
    // save simulation info
    p->pInfo     = pInfoPi;
    p->pInfoPi   = Aig_SimInfoAlloc( Aig_ManPiNum(p),   Aig_ManPiNum(p)+1,  0 );
    p->pInfoTemp = Aig_SimInfoAlloc( Aig_ManNodeNum(p), Aig_ManPiNum(p)+1,  1 );
    p->pPatMask  = Aig_PatternAlloc( Aig_ManPiNum(p)+1 );
}

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
    int i, Counter;

    // simulate the pattern of all zeros
    pPat = Aig_PatternAlloc( Aig_ManPiNum(p) ); 
    Aig_PatternClean( pPat );
    Vec_PtrPush( p->vPats, pPat );
    if ( !Aig_EngineSimulate( p ) )
        return;

    // simulate the pattern of all ones
    pPat = Aig_PatternAlloc( Aig_ManPiNum(p) ); 
    Aig_PatternFill( pPat );
    Vec_PtrPush( p->vPats, pPat );
    if ( !Aig_EngineSimulate( p ) )
        return;

    // simulate random until the number of new patterns is reasonable
    do {
        // generate random PI siminfo
        Aig_SimInfoRandom( p->pInfoPi );
        // simulate this info
        Aig_ManSimulateInfo( p, p->pInfoPi, p->pInfoTemp );
        // split the classes and collect the new patterns
        if ( Aig_ManUpdateClasses( p, p->pInfoTemp, p->vClasses, p->pPatMask ) )
            Aig_ManCollectPatterns( p, p->pInfoTemp, p->pPatMask, NULL );
        if ( Vec_VecSize(p->vClasses) == 0 )
            return;
        // count the number of useful patterns
        Counter = Aig_PatternCount(p->pPatMask);
    }
    while ( Counter > p->nPatsMax/2 );

    // perform targetted simulation
    for ( i = 0; i < 3; i++ )
    {
        assert( Vec_PtrSize(p->vPats) == 0 );
        // generate random PI siminfo
        Aig_SimInfoRandom( p->pInfoPi );
        // simulate this info
        Aig_ManSimulateInfo( p, p->pInfoPi, p->pInfoTemp );
        // split the classes and collect the new patterns
        if ( Aig_ManUpdateClasses( p, p->pInfoTemp, p->vClasses, p->pPatMask ) )
            Aig_ManCollectPatterns( p, p->pInfoTemp, p->pPatMask, p->vPats );
        if ( Vec_VecSize(p->vClasses) == 0 )
            return;
        // simulate the remaining patters
        if ( Vec_PtrSize(p->vPats) > 0 )
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
        assert( pPat->nBits == Aig_ManPiNum(p) );
        // create the new siminfo
        Aig_SimInfoFromPattern( p->pInfoPi, pPat );
        // free the pattern
        Aig_PatternFree( pPat );

        // simulate this info
        Aig_ManSimulateInfo( p, p->pInfoPi, p->pInfoTemp );
        // split the classes and collect the new patterns
        if ( Aig_ManUpdateClasses( p, p->pInfoTemp, p->vClasses, p->pPatMask ) )
            Aig_ManCollectPatterns( p, p->pInfoTemp, p->pPatMask, p->vPats );
    }
    return Vec_VecSize(p->vClasses) > 0;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


