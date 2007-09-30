/**CFile****************************************************************

  FileName    [aigMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [AIG package.]

  Synopsis    [AIG manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: aigMan.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

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

  Description [The argument of this procedure is a soft limit on the
  the number of nodes, or 0 if the limit is unknown.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManStart( int nNodesMax )
{
    Aig_Man_t * p;
    if ( nNodesMax <= 0 )
        nNodesMax = 10007;
    // start the manager
    p = ALLOC( Aig_Man_t, 1 );
    memset( p, 0, sizeof(Aig_Man_t) );
    // perform initializations
    p->nTravIds = 1;
    p->fCatchExor = 0;
    // allocate arrays for nodes
    p->vPis  = Vec_PtrAlloc( 100 );
    p->vPos  = Vec_PtrAlloc( 100 );
    p->vObjs = Vec_PtrAlloc( 1000 );
    p->vBufs = Vec_PtrAlloc( 100 );
    // prepare the internal memory manager
    p->pMemObjs = Aig_MmFixedStart( sizeof(Aig_Obj_t), nNodesMax );
    // create the constant node
    p->pConst1 = Aig_ManFetchMemory( p );
    p->pConst1->Type = AIG_OBJ_CONST1;
    p->pConst1->fPhase = 1;
    p->nObjs[AIG_OBJ_CONST1]++;
    // start the table
    p->nTableSize = Aig_PrimeCudd( nNodesMax );
    p->pTable = ALLOC( Aig_Obj_t *, p->nTableSize );
    memset( p->pTable, 0, sizeof(Aig_Obj_t *) * p->nTableSize );
    return p;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManStartFrom( Aig_Man_t * p )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i;
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    // create the PIs
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachPi( p, pObj, i )
        pObj->pData = Aig_ObjCreatePi(pNew);
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager recursively.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_ManDup_rec( Aig_Man_t * pNew, Aig_Man_t * p, Aig_Obj_t * pObj )
{
    if ( pObj->pData )
        return pObj->pData;
    Aig_ManDup_rec( pNew, p, Aig_ObjFanin0(pObj) );
    if ( Aig_ObjIsBuf(pObj) )
        return pObj->pData = Aig_ObjChild0Copy(pObj);
    Aig_ManDup_rec( pNew, p, Aig_ObjFanin1(pObj) );
    return pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDup( Aig_Man_t * p, int fOrdered )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i;
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    pNew->nRegs = p->nRegs;
    pNew->nAsserts = p->nAsserts;
    if ( p->vFlopNums )
        pNew->vFlopNums = Vec_IntDup( p->vFlopNums );
    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachPi( p, pObj, i )
        pObj->pData = Aig_ObjCreatePi(pNew);
    // duplicate internal nodes
    if ( fOrdered )
    {
        Aig_ManForEachObj( p, pObj, i )
            if ( Aig_ObjIsBuf(pObj) )
                pObj->pData = Aig_ObjChild0Copy(pObj);
            else if ( Aig_ObjIsNode(pObj) )
                pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    }
    else
    {
        Aig_ManForEachObj( p, pObj, i )
            if ( !Aig_ObjIsPo(pObj) )
            {
                Aig_ManDup_rec( pNew, p, pObj );        
                assert( pObj->Level == ((Aig_Obj_t*)pObj->pData)->Level );
            }
    }
    // add the POs
    Aig_ManForEachPo( p, pObj, i )
        Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    assert( Aig_ManBufNum(p) != 0 || Aig_ManNodeNum(p) == Aig_ManNodeNum(pNew) );
    // check the resulting network
    if ( !Aig_ManCheck(pNew) )
        printf( "Aig_ManDup(): The check has failed.\n" );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Extracts the miter composed of XOR of the two nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManExtractMiter( Aig_Man_t * p, Aig_Obj_t * pNode1, Aig_Obj_t * pNode2 )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i;
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachPi( p, pObj, i )
        pObj->pData = Aig_ObjCreatePi(pNew);
    // dump the nodes
    Aig_ManDup_rec( pNew, p, pNode1 );   
    Aig_ManDup_rec( pNew, p, pNode2 );   
    // construct the EXOR
    pObj = Aig_Exor( pNew, pNode1->pData, pNode2->pData ); 
    pObj = Aig_NotCond( pObj, Aig_Regular(pObj)->fPhase ^ Aig_IsComplement(pObj) );
    // add the PO
    Aig_ObjCreatePo( pNew, pObj );
    // check the resulting network
    if ( !Aig_ManCheck(pNew) )
        printf( "Aig_ManDup(): The check has failed.\n" );
    return pNew;
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
    if ( p->vMapped )
        Vec_PtrFree( p->vMapped );
    // print time
    if ( p->time1 ) { PRT( "time1", p->time1 ); }
    if ( p->time2 ) { PRT( "time2", p->time2 ); }
    // delete timing
    if ( p->pManTime )
        Aig_TManStop( p->pManTime );
    // delete fanout
    if ( p->pFanData ) 
        Aig_ManFanoutStop( p );
    // make sure the nodes have clean marks
    Aig_ManForEachObj( p, pObj, i )
        assert( !pObj->fMarkA && !pObj->fMarkB );
//    Aig_TableProfile( p );
    Aig_MmFixedStop( p->pMemObjs, 0 );
    if ( p->vPis )     Vec_PtrFree( p->vPis );
    if ( p->vPos )     Vec_PtrFree( p->vPos );
    if ( p->vObjs )    Vec_PtrFree( p->vObjs );
    if ( p->vBufs )    Vec_PtrFree( p->vBufs );
    if ( p->vLevelR )  Vec_IntFree( p->vLevelR );
    if ( p->vLevels )  Vec_VecFree( p->vLevels );
    if ( p->vFlopNums) Vec_IntFree( p->vFlopNums );
    FREE( p->pName );
    FREE( p->pObjCopies );
    FREE( p->pReprs );
    FREE( p->pEquivs );
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
    Vec_Ptr_t * vObjs;
    Aig_Obj_t * pNode;
    int i, nNodesOld;
    nNodesOld = Aig_ManNodeNum(p);
    // collect roots of dangling nodes
    vObjs = Vec_PtrAlloc( 100 );
    Aig_ManForEachObj( p, pNode, i )
        if ( Aig_ObjIsNode(pNode) && Aig_ObjRefs(pNode) == 0 )
            Vec_PtrPush( vObjs, pNode );
    // recursively remove dangling nodes
    Vec_PtrForEachEntry( vObjs, pNode, i )
        Aig_ObjDelete_rec( p, pNode, 1 );
    Vec_PtrFree( vObjs );
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
    printf( "PI/PO/Lat = %5d/%5d/%5d   ", Aig_ManPiNum(p), Aig_ManPoNum(p), Aig_ManLatchNum(p) );
    printf( "A = %7d. ",    Aig_ManAndNum(p) );
    if ( Aig_ManExorNum(p) )
        printf( "X = %5d. ",    Aig_ManExorNum(p) );
//    if ( Aig_ManBufNum(p) )
        printf( "B = %5d. ",    Aig_ManBufNum(p) );
//    printf( "Cre = %6d. ",  p->nCreated );
//    printf( "Del = %6d. ",  p->nDeleted );
//    printf( "Lev = %3d. ",  Aig_ManCountLevels(p) );
    printf( "Max = %7d. ",  Aig_ManObjNumMax(p) );
    printf( "Lev = %3d. ",  Aig_ManLevels(p) );
    if ( Aig_ManRegNum(p) )
        printf( "Lat = %5d. ", Aig_ManRegNum(p) );
    printf( "\n" );
    fflush( stdout );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


