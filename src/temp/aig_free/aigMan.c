/**CFile****************************************************************

  FileName    [aigMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Minimalistic And-Inverter Graph package.]

  Synopsis    [AIG manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: aig_.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Starts the AIG manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManStart()
{
    Aig_Man_t * p;
    // start the manager
    p = ALLOC( Aig_Man_t, 1 );
    memset( p, 0, sizeof(Aig_Man_t) );
    // perform initializations
    p->nTravIds = 1;
    p->fRefCount = 1;
    p->fCatchExor = 0;
    // allocate arrays for nodes
    p->vPis = Vec_PtrAlloc( 100 );
    p->vPos = Vec_PtrAlloc( 100 );
    // prepare the internal memory manager
    Aig_ManStartMemory( p );
    // create the constant node
    p->pConst1 = Aig_ManFetchMemory( p );
    p->pConst1->Type = AIG_CONST1;
    p->pConst1->fPhase = 1;
    p->nCreated = 1;
    // start the table
    p->nTableSize = 10007;
    p->pTable = ALLOC( Aig_Obj_t *, p->nTableSize );
    memset( p->pTable, 0, sizeof(Aig_Obj_t *) * p->nTableSize );
    return p;
}

/**Function*************************************************************

  Synopsis    [Stops the AIG manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManStop( Aig_Man_t * p )
{
    Aig_Obj_t * pObj;
    int i;
    // make sure the nodes have clean marks
    pObj = Aig_ManConst1(p);
    assert( !pObj->fMarkA && !pObj->fMarkB );
    Aig_ManForEachPi( p, pObj, i )
        assert( !pObj->fMarkA && !pObj->fMarkB );
    Aig_ManForEachPo( p, pObj, i )
        assert( !pObj->fMarkA && !pObj->fMarkB );
    Aig_ManForEachNode( p, pObj, i )
        assert( !pObj->fMarkA && !pObj->fMarkB );
    // print time
    if ( p->time1 ) { PRT( "time1", p->time1 ); }
    if ( p->time2 ) { PRT( "time2", p->time2 ); }
//    Aig_TableProfile( p );
    if ( p->vChunks )   Aig_ManStopMemory( p );
    if ( p->vPis )      Vec_PtrFree( p->vPis );
    if ( p->vPos )      Vec_PtrFree( p->vPos );
    free( p->pTable );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Returns the number of dangling nodes removed.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ManCleanup( Aig_Man_t * p )
{
    Vec_Ptr_t * vNodes;
    Aig_Obj_t * pNode;
    int i, nNodesOld;
    assert( p->fRefCount );
    nNodesOld = Aig_ManNodeNum(p);
    // collect roots of dangling nodes
    vNodes = Vec_PtrAlloc( 100 );
    Aig_ManForEachNode( p, pNode, i )
        if ( Aig_ObjRefs(pNode) == 0 )
            Vec_PtrPush( vNodes, pNode );
    // recursively remove dangling nodes
    Vec_PtrForEachEntry( vNodes, pNode, i )
        Aig_ObjDelete_rec( p, pNode );
    Vec_PtrFree( vNodes );
    return nNodesOld - Aig_ManNodeNum(p);
}

/**Function*************************************************************

  Synopsis    [Stops the AIG manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManPrintStats( Aig_Man_t * p )
{
    printf( "PI/PO = %d/%d. ", Aig_ManPiNum(p), Aig_ManPoNum(p) );
    printf( "A = %7d. ",       Aig_ManAndNum(p) );
    printf( "X = %5d. ",       Aig_ManExorNum(p) );
    printf( "Cre = %7d. ",     p->nCreated );
    printf( "Del = %7d. ",     p->nDeleted );
    printf( "Lev = %3d. ",     Aig_ManCountLevels(p) );
    printf( "\n" );
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


