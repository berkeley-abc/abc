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
    p->vObjs = Vec_PtrAlloc( 1000 );
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
    p->nObjs[DAR_AIG_CONST1]++;
    // start the table
    p->nTableSize = nNodesMax;
    p->pTable = ALLOC( Dar_Obj_t *, p->nTableSize );
    memset( p->pTable, 0, sizeof(Dar_Obj_t *) * p->nTableSize );
    // other data
    p->vLeavesBest = Vec_PtrAlloc( 4 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Man_t * Dar_ManStartFrom( Dar_Man_t * p )
{
    Dar_Man_t * pNew;
    Dar_Obj_t * pObj;
    int i;
    // create the new manager
    pNew = Dar_ManStart( Dar_ManObjIdMax(p) + 1 );
    // create the PIs
    Dar_ManConst1(p)->pData = Dar_ManConst1(pNew);
    Dar_ManForEachPi( p, pObj, i )
        pObj->pData = Dar_ObjCreatePi(pNew);
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Man_t * Dar_ManDup( Dar_Man_t * p )
{
    Dar_Man_t * pNew;
    Dar_Obj_t * pObj;
    int i;
    // create the new manager
    pNew = Dar_ManStart( Dar_ManObjIdMax(p) + 1 );
    // create the PIs
    Dar_ManConst1(p)->pData = Dar_ManConst1(pNew);
    Dar_ManForEachPi( p, pObj, i )
        pObj->pData = Dar_ObjCreatePi(pNew);
    // duplicate internal nodes
    Dar_ManForEachObj( p, pObj, i )
        if ( Dar_ObjIsBuf(pObj) )
            pObj->pData = Dar_ObjChild0Copy(pObj);
        else if ( Dar_ObjIsNode(pObj) )
            pObj->pData = Dar_And( pNew, Dar_ObjChild0Copy(pObj), Dar_ObjChild1Copy(pObj) );
    // add the POs
    Dar_ManForEachPo( p, pObj, i )
        Dar_ObjCreatePo( pNew, Dar_ObjChild0Copy(pObj) );
    // check the resulting network
    if ( !Dar_ManCheck(pNew) )
        printf( "Dar_ManDup(): The check has failed.\n" );
    return pNew;
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
    if ( p->vPis )        Vec_PtrFree( p->vPis );
    if ( p->vPos )        Vec_PtrFree( p->vPos );
    if ( p->vObjs )       Vec_PtrFree( p->vObjs );
    if ( p->vRequired )   Vec_IntFree( p->vRequired );
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
    printf( "PI/PO/Lat = %5d/%5d/%5d   ", Dar_ManPiNum(p), Dar_ManPoNum(p), Dar_ManLatchNum(p) );
    printf( "A = %6d. ",    Dar_ManAndNum(p) );
    if ( Dar_ManExorNum(p) )
        printf( "X = %5d. ",    Dar_ManExorNum(p) );
    if ( Dar_ManBufNum(p) )
        printf( "B = %3d. ",    Dar_ManBufNum(p) );
    printf( "Cre = %6d. ",  p->nCreated );
    printf( "Del = %6d. ",  p->nDeleted );
//    printf( "Lev = %3d. ",  Dar_ManCountLevels(p) );
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    [Stops the AIG manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ManPrintRuntime( Dar_Man_t * p )
{
    int i, Gain;
    printf( "Good cuts = %d. Bad cuts = %d.  Cut mem = %d Mb\n", 
        p->nCutsGood, p->nCutsBad, p->nCutMemUsed );
    PRT( "Cuts  ", p->timeCuts );
    PRT( "Eval  ", p->timeEval );
    PRT( "Other ", p->timeOther );
    PRT( "TOTAL ", p->timeTotal );
    Gain = p->nNodesInit - Dar_ManNodeNum(p);
    for ( i = 0; i < 222; i++ )
    {
        if ( p->ClassGains[i] == 0 && p->ClassTimes[i] == 0 )
            continue;
        printf( "%3d : ", i );
        printf( "G = %6d (%5.2f %%)  ", p->ClassGains[i], Gain? 100.0*p->ClassGains[i]/Gain : 0.0 );
        printf( "S = %8d (%5.2f %%)  ", p->ClassSubgs[i], p->nTotalSubgs? 100.0*p->ClassSubgs[i]/p->nTotalSubgs : 0.0 );
        printf( "R = %7d  ", p->ClassGains[i]? p->ClassSubgs[i]/p->ClassGains[i] : 9999999 );
        PRTP( "T", p->ClassTimes[i], p->timeEval );
    }
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


