/**CFile****************************************************************

  FileName    [aigScl.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [AIG package.]

  Synopsis    [Sequential cleanup.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: aigScl.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Remaps the manager.]

  Description [Map in the array specifies for each CI nodes the node that
  should be used after remapping.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManRemap( Aig_Man_t * p, Vec_Ptr_t * vMap )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pObjMapped;
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
    // implement the mapping
    Aig_ManForEachPi( p, pObj, i )
    {
        pObjMapped = Vec_PtrEntry( vMap, i );
        pObj->pData = Aig_NotCond( Aig_Regular(pObjMapped)->pData, Aig_IsComplement(pObjMapped) );
    }
    // duplicate internal nodes
    Aig_ManForEachObj( p, pObj, i )
        if ( Aig_ObjIsBuf(pObj) )
            pObj->pData = Aig_ObjChild0Copy(pObj);
        else if ( Aig_ObjIsNode(pObj) )
            pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    // add the POs
    Aig_ManForEachPo( p, pObj, i )
        Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    assert( Aig_ManNodeNum(p) >= Aig_ManNodeNum(pNew) );
    // check the resulting network
    if ( !Aig_ManCheck(pNew) )
        printf( "Aig_ManDup(): The check has failed.\n" );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Returns the number of dangling nodes removed.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManSeqCleanup_rec( Aig_Man_t * p, Aig_Obj_t * pObj, Vec_Ptr_t * vNodes )
{
    if ( Aig_ObjIsTravIdCurrent(p, pObj) )
        return;
    Aig_ObjSetTravIdCurrent(p, pObj);
    // collect latch input corresponding to unmarked PI (latch output)
    if ( Aig_ObjIsPi(pObj) )
    {
        Vec_PtrPush( vNodes, pObj->pNext );
        return;
    }
    if ( Aig_ObjIsPo(pObj) )
    {
        Aig_ManSeqCleanup_rec( p, Aig_ObjFanin0(pObj), vNodes );
        return;
    }
    assert( Aig_ObjIsNode(pObj) );
    Aig_ManSeqCleanup_rec( p, Aig_ObjFanin0(pObj), vNodes );
    Aig_ManSeqCleanup_rec( p, Aig_ObjFanin1(pObj), vNodes );
}

/**Function*************************************************************

  Synopsis    [Returns the number of dangling nodes removed.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ManSeqCleanup( Aig_Man_t * p )
{
    Vec_Ptr_t * vNodes, * vCis, * vCos;
    Aig_Obj_t * pObj, * pObjLi, * pObjLo;
    int i, nTruePis, nTruePos;
    assert( Aig_ManBufNum(p) == 0 );

    // mark the PIs
    Aig_ManIncrementTravId( p );
    Aig_ObjSetTravIdCurrent( p, Aig_ManConst1(p) );
    Aig_ManForEachPiSeq( p, pObj, i )
        Aig_ObjSetTravIdCurrent( p, pObj );

    // prepare to collect nodes reachable from POs
    vNodes = Vec_PtrAlloc( 100 );
    Aig_ManForEachPoSeq( p, pObj, i )
        Vec_PtrPush( vNodes, pObj );

    // remember latch inputs in latch outputs
    Aig_ManForEachLiLoSeq( p, pObjLi, pObjLo, i )
        pObjLo->pNext = pObjLi;
    // mark the nodes reachable from these nodes
    Vec_PtrForEachEntry( vNodes, pObj, i )
        Aig_ManSeqCleanup_rec( p, pObj, vNodes );
    assert( Vec_PtrSize(vNodes) <= Aig_ManPoNum(p) );
    // clean latch output pointers
    Aig_ManForEachLiLoSeq( p, pObjLi, pObjLo, i )
        pObjLo->pNext = NULL;

    // if some latches are removed, update PIs/POs
    if ( Vec_PtrSize(vNodes) < Aig_ManPoNum(p) )
    {
        if ( p->vFlopNums )
        {
            int nTruePos = Aig_ManPoNum(p)-Aig_ManRegNum(p);
            // remember numbers of flops in the flops
            Aig_ManForEachLiSeq( p, pObj, i )
                pObj->pNext = (Aig_Obj_t *)(long)Vec_IntEntry( p->vFlopNums, i - nTruePos );
            // reset the flop numbers
            Vec_PtrForEachEntryStart( vNodes, pObj, i, nTruePos )
                Vec_IntWriteEntry( p->vFlopNums, i - nTruePos, (int)(long)pObj->pNext );
            Vec_IntShrink( p->vFlopNums, Vec_PtrSize(vNodes) - nTruePos );
            // clean the next pointer
            Aig_ManForEachLiSeq( p, pObj, i )
                pObj->pNext = NULL;
        }
        // collect new CIs/COs
        vCis = Vec_PtrAlloc( Aig_ManPiNum(p) );
        Aig_ManForEachPi( p, pObj, i )
            if ( Aig_ObjIsTravIdCurrent(p, pObj) )
                Vec_PtrPush( vCis, pObj );
            else
            {
                Vec_PtrWriteEntry( p->vObjs, pObj->Id, NULL );
//                Aig_ManRecycleMemory( p, pObj );
            }
        vCos = Vec_PtrAlloc( Aig_ManPoNum(p) );
        Aig_ManForEachPo( p, pObj, i )
            if ( Aig_ObjIsTravIdCurrent(p, pObj) )
                Vec_PtrPush( vCos, pObj );
            else
            {
                Aig_ObjDisconnect( p, pObj );
                Vec_PtrWriteEntry( p->vObjs, pObj->Id, NULL );
//                Aig_ManRecycleMemory( p, pObj );
            }
        // remember the number of true PIs/POs
        nTruePis = Aig_ManPiNum(p) - Aig_ManRegNum(p);
        nTruePos = Aig_ManPoNum(p) - Aig_ManRegNum(p);
        // set the new number of registers
        p->nRegs -= Aig_ManPoNum(p) - Vec_PtrSize(vNodes);
        // create new PIs/POs
        assert( Vec_PtrSize(vCis) == nTruePis + p->nRegs );
        assert( Vec_PtrSize(vCos) == nTruePos + p->nRegs );
        Vec_PtrFree( p->vPis );    p->vPis = vCis;
        Vec_PtrFree( p->vPos );    p->vPos = vCos;
        p->nObjs[AIG_OBJ_PI] = Vec_PtrSize( p->vPis );
        p->nObjs[AIG_OBJ_PO] = Vec_PtrSize( p->vPos );
                
    }
    Vec_PtrFree( vNodes );
    // remove dangling nodes
    return Aig_ManCleanup( p );
}

/**Function*************************************************************

  Synopsis    [Returns the number of dangling nodes removed.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ManCountMergeRegs( Aig_Man_t * p )
{
    Aig_Obj_t * pObj, * pFanin;
    int i, Counter = 0, Const0 = 0, Const1 = 0;
    Aig_ManIncrementTravId( p );
    Aig_ManForEachLiSeq( p, pObj, i )
    {
        pFanin = Aig_ObjFanin0(pObj);
        if ( Aig_ObjIsConst1(pFanin) )
        {
            if ( Aig_ObjFaninC0(pObj) )
                Const0++;
            else
                Const1++;
        }
        if ( Aig_ObjIsTravIdCurrent(p, pFanin) )
            continue;
        Aig_ObjSetTravIdCurrent(p, pFanin);
        Counter++;
    }
    printf( "Regs = %d. Fanins = %d. Const0 = %d. Const1 = %d.\n", 
        Aig_ManRegNum(p), Counter, Const0, Const1 );
    return 0;
}


/**Function*************************************************************

  Synopsis    [Checks how many latches can be reduced.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ManReduceLachesCount( Aig_Man_t * p )
{
    Aig_Obj_t * pObj, * pFanin;
    int i, Counter = 0, Diffs = 0;
    assert( Aig_ManRegNum(p) > 0 );
    Aig_ManForEachObj( p, pObj, i )
        assert( !pObj->fMarkA && !pObj->fMarkB );
    Aig_ManForEachLiSeq( p, pObj, i )
    {
        pFanin = Aig_ObjFanin0(pObj);
        if ( Aig_ObjFaninC0(pObj) )
        {
            if ( pFanin->fMarkB )
                Counter++;
            else
                pFanin->fMarkB = 1;
        }
        else
        {
            if ( pFanin->fMarkA )
                Counter++;
            else
                pFanin->fMarkA = 1;
        }
    }
    // count fanins that have both attributes
    Aig_ManForEachLiSeq( p, pObj, i )
    {
        pFanin = Aig_ObjFanin0(pObj);
        Diffs += pFanin->fMarkA && pFanin->fMarkB;
        pFanin->fMarkA = pFanin->fMarkB = 0;
    }
//    printf( "Diffs = %d.\n", Diffs );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Reduces the latches.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Aig_ManReduceLachesOnce( Aig_Man_t * p )
{
    Vec_Ptr_t * vMap;
    Aig_Obj_t * pObj, * pObjLi, * pObjLo, * pFanin;
    int * pMapping, i;
    // start mapping by adding the true PIs
    vMap = Vec_PtrAlloc( Aig_ManPiNum(p) );
    Aig_ManForEachPiSeq( p, pObj, i )
        Vec_PtrPush( vMap, pObj );
    // create mapping of fanin nodes into the corresponding latch outputs
    pMapping = ALLOC( int, 2 * Aig_ManObjNumMax(p) );
    Aig_ManForEachLiLoSeq( p, pObjLi, pObjLo, i )
    {
        pFanin = Aig_ObjFanin0(pObjLi);
        if ( Aig_ObjFaninC0(pObjLi) )
        {
            if ( pFanin->fMarkB )
            {
                Vec_PtrPush( vMap, Aig_ManLo(p, pMapping[2*pFanin->Id + 1]) );
            }
            else
            {
                pFanin->fMarkB = 1;
                pMapping[2*pFanin->Id + 1] = i;
                Vec_PtrPush( vMap, pObjLo );
            }
        }
        else
        {
            if ( pFanin->fMarkA )
            {
                Vec_PtrPush( vMap, Aig_ManLo(p, pMapping[2*pFanin->Id]) );
            }
            else
            {
                pFanin->fMarkA = 1;
                pMapping[2*pFanin->Id] = i;
                Vec_PtrPush( vMap, pObjLo );
            }
        }
    }
    free( pMapping );
    Aig_ManForEachLiSeq( p, pObj, i )
    {
        pFanin = Aig_ObjFanin0(pObj);
        pFanin->fMarkA = pFanin->fMarkB = 0;
    }
    return vMap;
}

/**Function*************************************************************

  Synopsis    [Reduces the latches.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManReduceLaches( Aig_Man_t * p, int fVerbose )
{
    Aig_Man_t * pTemp;
    Vec_Ptr_t * vMap;
    int nSaved, nCur;
    for ( nSaved = 0; (nCur = Aig_ManReduceLachesCount(p)); nSaved += nCur )
    {
        if ( fVerbose )
        {
        printf( "Saved = %5d.   ", nCur );
        printf( "RBeg = %5d. NBeg = %6d.   ", Aig_ManRegNum(p), Aig_ManNodeNum(p) );
        }
        vMap = Aig_ManReduceLachesOnce( p );
        p = Aig_ManRemap( pTemp = p, vMap );
        Aig_ManStop( pTemp );
        Vec_PtrFree( vMap );
        Aig_ManSeqCleanup( p );
        if ( fVerbose )
        {
        printf( "REnd = %5d. NEnd = %6d.   ", Aig_ManRegNum(p), Aig_ManNodeNum(p) );
        printf( "\n" );
        }
        if ( p->nRegs == 0 )
            break;
    }
    return p;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


