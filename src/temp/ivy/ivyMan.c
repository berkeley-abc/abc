/**CFile****************************************************************

  FileName    [ivyMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    [AIG manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: ivy_.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ivy.h"

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
Ivy_Man_t * Ivy_ManStart( int nPis, int nPos, int nNodesMax )
{
    Ivy_Man_t * p;
    Ivy_Obj_t * pObj;
    int i, nTotalSize;
    // start the manager
    p = ALLOC( Ivy_Man_t, 1 );
    memset( p, 0, sizeof(Ivy_Man_t) );
    p->nTravIds = 1;
    p->fCatchExor = 1;
    // AIG nodes
    p->nObjsAlloc = 1 + nPis + nPos + nNodesMax;
//    p->nObjsAlloc += (p->nObjsAlloc & 1); // make it even
    nTotalSize = p->nObjsAlloc + IVY_SANDBOX_SIZE + 1;
    p->pObjs = ALLOC( Ivy_Obj_t, nTotalSize );
    memset( p->pObjs, 0, sizeof(Ivy_Obj_t) * nTotalSize );
    // temporary storage for deleted entries
    p->vFree  = Vec_IntAlloc( 100 );
    // set the node IDs
    for ( i = 0, pObj = p->pObjs; i < nTotalSize; i++, pObj++ )
        pObj->Id = i - IVY_SANDBOX_SIZE - 1;
    // remember the manager in the first entry
    *((Ivy_Man_t **)p->pObjs) = p; 
    p->pObjs += IVY_SANDBOX_SIZE + 1;
    // create the constant node
    p->nCreated = 1;
    p->ObjIdNext = 1;
    Ivy_ManConst1(p)->fPhase = 1;
    // create PIs
    pObj = Ivy_ManGhost(p);
    pObj->Type = IVY_PI;
    p->vPis = Vec_IntAlloc( 100 );
    for ( i = 0; i < nPis; i++ )
        Ivy_ObjCreate( pObj );
    // create POs
    pObj->Type = IVY_PO;
    p->vPos = Vec_IntAlloc( 100 );
    for ( i = 0; i < nPos; i++ )
        Ivy_ObjCreate( pObj );
    // start the table
    p->nTableSize = p->nObjsAlloc*5/2+13;
    p->pTable = ALLOC( int, p->nTableSize );
    memset( p->pTable, 0, sizeof(int) * p->nTableSize );
    // allocate undo storage
    p->nUndosAlloc = 100;
    p->pUndos = ALLOC( Ivy_Obj_t, p->nUndosAlloc );
    memset( p->pUndos, 0, sizeof(Ivy_Obj_t) * p->nUndosAlloc );
    return p;
}

/**Function*************************************************************

  Synopsis    [Stops the AIG manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManStop( Ivy_Man_t * p )
{
    if ( p->fExtended )
    {
        Ivy_Obj_t * pObj;
        int i;
        Ivy_ManForEachObj( p, pObj, i )
            if ( Ivy_ObjGetFanins(pObj) )
                Vec_IntFree( Ivy_ObjGetFanins(pObj) );
    }
    if ( p->vFree )   Vec_IntFree( p->vFree );
    if ( p->vTruths ) Vec_IntFree( p->vTruths );
    if ( p->vPis )    Vec_IntFree( p->vPis );
    if ( p->vPos )    Vec_IntFree( p->vPos );
    FREE( p->pMemory );
    free( p->pObjs - IVY_SANDBOX_SIZE - 1 );
    free( p->pTable );
    free( p->pUndos );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Returns the number of dangling nodes removed.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManGrow( Ivy_Man_t * p )
{
    int i;
    assert( p->ObjIdNext == p->nObjsAlloc );
    if ( p->ObjIdNext != p->nObjsAlloc )
        return;
//    printf( "Ivy_ObjCreate(): Reallocing the node array.\n" );
    p->nObjsAlloc = 2 * p->nObjsAlloc;
    p->pObjs = REALLOC( Ivy_Obj_t, p->pObjs - IVY_SANDBOX_SIZE - 1, p->nObjsAlloc + IVY_SANDBOX_SIZE + 1 ) + IVY_SANDBOX_SIZE + 1;
    memset( p->pObjs + p->ObjIdNext, 0, sizeof(Ivy_Obj_t) * p->nObjsAlloc / 2 );
    for ( i = p->nObjsAlloc / 2; i < p->nObjsAlloc; i++ )
        Ivy_ManObj( p, i )->Id = i;
}

/**Function*************************************************************

  Synopsis    [Returns the number of dangling nodes removed.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_ManCleanup( Ivy_Man_t * p )
{
    Ivy_Obj_t * pNode;
    int i, nNodesOld;
    nNodesOld = Ivy_ManNodeNum(p);
    Ivy_ManForEachNode( p, pNode, i )
        if ( Ivy_ObjRefs(pNode) == 0 )
            Ivy_ObjDelete_rec( pNode, 1 );
    return nNodesOld - Ivy_ManNodeNum(p);
}

/**Function*************************************************************

  Synopsis    [Stops the AIG manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManPrintStats( Ivy_Man_t * p )
{
    printf( "PI/PO = %d/%d ", Ivy_ManPiNum(p), Ivy_ManPoNum(p) );
    if ( p->fExtended )
    {
    printf( "Am = %d. ",    Ivy_ManAndMultiNum(p) );
    printf( "Xm = %d. ",    Ivy_ManExorMultiNum(p) );
    printf( "Lut = %d. ",   Ivy_ManLutNum(p) );
    }
    else
    {
    printf( "A = %d. ",     Ivy_ManAndNum(p) );
    printf( "X = %d. ",     Ivy_ManExorNum(p) );
    printf( "B = %4d. ",     Ivy_ManBufNum(p) );
    }
//    printf( "MaxID = %d. ", p->ObjIdNext-1 );
//    printf( "All = %d. ",   p->nObjsAlloc );
    printf( "Cre = %d. ",   p->nCreated );
    printf( "Del = %d. ",   p->nDeleted );
    printf( "Lev = %d. ",   Ivy_ManReadLevels(p) );
    printf( "\n" );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


