/**CFile****************************************************************

  FileName    [aigMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: aigMan.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Sets the default parameters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManSetDefaultParams( Aig_Param_t * pParam )
{
    memset( pParam, 0, sizeof(Aig_Param_t) );
    pParam->nPatsRand = 1024;  // the number of random patterns
    pParam->nBTLimit  =   99;  // backtrack limit at the intermediate nodes
    pParam->nSeconds  =    1;  // the timeout for the final miter in seconds
}

/**Function*************************************************************

  Synopsis    [Starts the AIG manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManStart( Aig_Param_t * pParam )
{
    Aig_Man_t * p;
    // set the random seed for simulation
    srand( 0xDEADCAFE );
    // start the manager
    p = ALLOC( Aig_Man_t, 1 );
    memset( p, 0, sizeof(Aig_Man_t) );
    p->pParam     = &p->Param;
    p->nTravIds   = 1;
    p->nPatsMax   = 20;
    // set the defaults
    *p->pParam    = *pParam;
    // start memory managers
    p->mmNodes    = Aig_MemFixedStart( sizeof(Aig_Node_t) );
    // allocate node arrays
    p->vPis       = Vec_PtrAlloc( 1000 );    // the array of primary inputs
    p->vPos       = Vec_PtrAlloc( 1000 );    // the array of primary outputs
    p->vNodes     = Vec_PtrAlloc( 1000 );    // the array of internal nodes
    // start the table
    p->pTable     = Aig_TableCreate( 1000 );
    // create the constant node
    p->pConst1    = Aig_NodeCreateConst( p );
    // initialize other variables
    p->vFanouts   = Vec_PtrAlloc( 10 ); 
    p->vToReplace = Vec_PtrAlloc( 10 ); 
    return p;
}

/**Function*************************************************************

  Synopsis    [Returns the number of dangling nodes removed.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ManCleanup( Aig_Man_t * pMan )
{
    Aig_Node_t * pAnd;
    int i, nNodesOld;
    nNodesOld = Aig_ManAndNum(pMan);
    Aig_ManForEachAnd( pMan, pAnd, i )
        if ( pAnd->nRefs == 0 )
            Aig_NodeDeleteAnd_rec( pMan, pAnd );
    return nNodesOld - Aig_ManAndNum(pMan);
}

/**Function*************************************************************

  Synopsis    [Stops the AIG manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManStop( Aig_Man_t * p )
{
    // SAT solver
    if ( p->pSat )       solver_delete( p->pSat );
    if ( p->vVar2Sat )   Vec_IntFree( p->vVar2Sat );
    if ( p->vSat2Var )   Vec_IntFree( p->vSat2Var );
    if ( p->vPiSatNums ) Vec_IntFree( p->vPiSatNums );
    // fanouts
    if ( p->vFanPivots ) Vec_PtrFree( p->vFanPivots );
    if ( p->vFanFans0 )  Vec_PtrFree( p->vFanFans0 );
    if ( p->vFanFans1 )  Vec_PtrFree( p->vFanFans1 );
    if ( p->vClasses  )  Vec_VecFree( p->vClasses );
    // nodes
    Aig_MemFixedStop( p->mmNodes, 0 );
    Vec_PtrFree( p->vNodes );
    Vec_PtrFree( p->vPis );
    Vec_PtrFree( p->vPos );
    // temporary
    Vec_PtrFree( p->vFanouts );
    Vec_PtrFree( p->vToReplace );
    Aig_TableFree( p->pTable );
    free( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


