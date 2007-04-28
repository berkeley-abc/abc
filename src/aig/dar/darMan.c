/**CFile****************************************************************

  FileName    [darMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting.]

  Synopsis    [AIG manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: darMan.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "dar.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Starts the AIG manager.]

  Description [The argument of this procedure is a soft limit on the
  the number of nodes, or 0 if the limit is unknown.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Man_t * Dar_ManStart( int nNodesMax )
{
    Dar_Man_t * p;
    int i;
    if ( nNodesMax <= 0 )
        nNodesMax = 10007;
    // start the manager
    p = ALLOC( Dar_Man_t, 1 );
    memset( p, 0, sizeof(Dar_Man_t) );
    // perform initializations
    p->nTravIds = 1;
    p->fCatchExor = 0;
    // allocate arrays for nodes
    p->vPis = Vec_PtrAlloc( 100 );
    p->vPos = Vec_PtrAlloc( 100 );
    // prepare the internal memory manager
    p->pMemObjs = Dar_MmFixedStart( sizeof(Dar_Obj_t), nNodesMax );
    p->pMemCuts = Dar_MmFlexStart();
    // prepare storage for cuts
    p->nBaseCuts = DAR_CUT_BASE;
    for ( i = 0; i < p->nBaseCuts; i++ )
        p->pBaseCuts[i] = p->BaseCuts + i;
    // create the constant node
    p->pConst1 = Dar_ManFetchMemory( p );
    p->pConst1->Type = DAR_AIG_CONST1;
    p->pConst1->fPhase = 1;
    p->nCreated = 1;
    // start the table
    p->nTableSize = nNodesMax;
    p->pTable = ALLOC( Dar_Obj_t *, p->nTableSize );
    memset( p->pTable, 0, sizeof(Dar_Obj_t *) * p->nTableSize );
    // other data
    p->vLeavesBest = Vec_PtrAlloc( 4 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Stops the AIG manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ManStop( Dar_Man_t * p )
{
    Dar_Obj_t * pObj;
    int i;
    // make sure the nodes have clean marks
    Dar_ManForEachObj( p, pObj, i )
        assert( !pObj->fMarkA && !pObj->fMarkB );
    // print time
    if ( p->time1 ) { PRT( "time1", p->time1 ); }
    if ( p->time2 ) { PRT( "time2", p->time2 ); }
//    Dar_TableProfile( p );
    Dar_MmFixedStop( p->pMemObjs, 0 );
    Dar_MmFlexStop( p->pMemCuts, 0 );
    if ( p->vPis )      Vec_PtrFree( p->vPis );
    if ( p->vPos )      Vec_PtrFree( p->vPos );
    if ( p->vObjs )     Vec_PtrFree( p->vObjs );
    if ( p->vRequired ) Vec_IntFree( p->vRequired );
    if ( p->vLeavesBest ) Vec_PtrFree( p->vLeavesBest );
    free( p->pTable );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Returns the number of dangling nodes removed.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_ManCleanup( Dar_Man_t * p )
{
    Vec_Ptr_t * vObjs;
    Dar_Obj_t * pNode;
    int i, nNodesOld;
    nNodesOld = Dar_ManNodeNum(p);
    // collect roots of dangling nodes
    vObjs = Vec_PtrAlloc( 100 );
    Dar_ManForEachObj( p, pNode, i )
        if ( Dar_ObjIsNode(pNode) && Dar_ObjRefs(pNode) == 0 )
            Vec_PtrPush( vObjs, pNode );
    // recursively remove dangling nodes
    Vec_PtrForEachEntry( vObjs, pNode, i )
        Dar_ObjDelete_rec( p, pNode, 1 );
    Vec_PtrFree( vObjs );
    return nNodesOld - Dar_ManNodeNum(p);
}

/**Function*************************************************************

  Synopsis    [Stops the AIG manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ManPrintStats( Dar_Man_t * p )
{
    printf( "PI/PO = %d/%d. ", Dar_ManPiNum(p), Dar_ManPoNum(p) );
    printf( "A = %7d. ",       Dar_ManAndNum(p) );
    printf( "X = %5d. ",       Dar_ManExorNum(p) );
    printf( "Cre = %7d. ",     p->nCreated );
    printf( "Del = %7d. ",     p->nDeleted );
    printf( "Lev = %3d. ",     Dar_ManCountLevels(p) );
    printf( "\n" );
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


