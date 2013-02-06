/**CFile****************************************************************

  FileName    [giaTim.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Procedures with hierarchy/timing manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaTim.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "misc/tim/tim.h"
#include "proof/cec/cec.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Duplicates AIG in the DFS order while putting CIs first.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDupNormalize( Gia_Man_t * p )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i;
    Gia_ManFillValue( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);
    Gia_ManForEachAnd( p, pObj, i )
        pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachCo( p, pObj, i )
        pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    assert( Gia_ManIsNormalized(pNew) );
    Gia_ManDupRemapEquiv( pNew, p );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates AIG according to the timing manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDupUnnomalize( Gia_Man_t * p )
{
    Tim_Man_t * pTime = (Tim_Man_t *)p->pManTime;
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i, k, curCi, curCo, curNo, nodeLim;
//Gia_ManPrint( p );
    assert( pTime != NULL );
    assert( Gia_ManIsNormalized(p) );
    Gia_ManFillValue( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManConst0(p)->Value = 0;
    if ( p->pSibls )
        pNew->pSibls = ABC_CALLOC( int, Gia_ManObjNum(p) );
    // copy primary inputs
    for ( k = 0; k < Tim_ManPiNum(pTime); k++ )
        Gia_ManPi(p, k)->Value = Gia_ManAppendCi(pNew);
    curCi = Tim_ManPiNum(pTime);
    curCo = 0;
    curNo = Gia_ManPiNum(p)+1;
    for ( i = 0; i < Tim_ManBoxNum(pTime); i++ )
    {
        // find the latest node feeding into inputs of this box
        nodeLim = -1;
        for ( k = 0; k < Tim_ManBoxInputNum(pTime, i); k++ )
        {
            pObj = Gia_ManPo( p, curCo + k );
            nodeLim = Abc_MaxInt( nodeLim, Gia_ObjFaninId0p(p, pObj)+1 );
        }
        // copy nodes up to the given node
        for ( k = curNo; k < nodeLim; k++ )
        {
            pObj = Gia_ManObj( p, k );
            assert( Gia_ObjIsAnd(pObj) );
            pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        }
        curNo = Abc_MaxInt( curNo, nodeLim );
        // copy COs
        for ( k = 0; k < Tim_ManBoxInputNum(pTime, i); k++ )
        {
            pObj = Gia_ManPo( p, curCo + k );
            pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
        }
        curCo += Tim_ManBoxInputNum(pTime, i);
        // copy CIs
        for ( k = 0; k < Tim_ManBoxOutputNum(pTime, i); k++ )
        {
            pObj = Gia_ManPi( p, curCi + k );
            pObj->Value = Gia_ManAppendCi(pNew);
        }
        curCi += Tim_ManBoxOutputNum(pTime, i);
    }
    // copy remaining nodes
    nodeLim = Gia_ManObjNum(p) - Gia_ManPoNum(p);
    for ( k = curNo; k < nodeLim; k++ )
    {
        pObj = Gia_ManObj( p, k );
        assert( Gia_ObjIsAnd(pObj) );
        pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    }
    curNo = Abc_MaxInt( curNo, nodeLim );
    curNo += Gia_ManPoNum(p);
    // copy primary outputs
    for ( k = 0; k < Tim_ManPoNum(pTime); k++ )
    {
        pObj = Gia_ManPo( p, curCo + k );
        pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    }
    curCo += Tim_ManPoNum(pTime);
    assert( curCi == Gia_ManPiNum(p) );
    assert( curCo == Gia_ManPoNum(p) );
    assert( curNo == Gia_ManObjNum(p) );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    Gia_ManDupRemapEquiv( pNew, p );
//Gia_ManPrint( pNew );
    // pass the timing manager
    pNew->pManTime = pTime;  p->pManTime = NULL;
    return pNew;
}


/**Function*************************************************************

  Synopsis    [Find the ordering of AIG objects.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManDupFindOrderWithHie_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vNodes )
{
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return;
    Gia_ObjSetTravIdCurrent(p, pObj);
    assert( Gia_ObjIsAnd(pObj) );
    if ( Gia_ObjSibl(p, Gia_ObjId(p, pObj)) )
        Gia_ManDupFindOrderWithHie_rec( p, Gia_ObjSiblObj(p, Gia_ObjId(p, pObj)), vNodes );
    Gia_ManDupFindOrderWithHie_rec( p, Gia_ObjFanin0(pObj), vNodes );
    Gia_ManDupFindOrderWithHie_rec( p, Gia_ObjFanin1(pObj), vNodes );
    Vec_IntPush( vNodes, Gia_ObjId(p, pObj) );
}
Vec_Int_t * Gia_ManDupFindOrderWithHie( Gia_Man_t * p )
{
    Tim_Man_t * pTime = (Tim_Man_t *)p->pManTime;
    Vec_Int_t * vNodes;
    Gia_Obj_t * pObj;
    int i, k, curCi, curCo;
    assert( p->pManTime != NULL );
    assert( Gia_ManIsNormalized( p ) );
    // start trav IDs
    Gia_ManIncrementTravId( p );
    // start the array
    vNodes = Vec_IntAlloc( Gia_ManObjNum(p) );
    // include constant
    Vec_IntPush( vNodes, 0 );
    Gia_ObjSetTravIdCurrent( p, Gia_ManConst0(p) );
    // include primary inputs
    for ( i = 0; i < Tim_ManPiNum(pTime); i++ )
    {
        pObj = Gia_ManPi( p, i );
        Vec_IntPush( vNodes, Gia_ObjId(p, pObj) );
        Gia_ObjSetTravIdCurrent( p, pObj );
        assert( Gia_ObjId(p, pObj) == i+1 );
//printf( "%d ", Gia_ObjId(p, pObj) );
    }
    // for each box, include box nodes
    curCi = Tim_ManPiNum(pTime);
    curCo = 0;
    for ( i = 0; i < Tim_ManBoxNum(pTime); i++ )
    {
//printf( "Box %d:\n", i );
        // add internal nodes
        for ( k = 0; k < Tim_ManBoxInputNum(pTime, i); k++ )
        {
            pObj = Gia_ManPo( p, curCo + k );
//Gia_ObjPrint( p, pObj );
//printf( "Fanin " );
//Gia_ObjPrint( p, Gia_ObjFanin0(pObj) );
            Gia_ManDupFindOrderWithHie_rec( p, Gia_ObjFanin0(pObj), vNodes );
        }
        // add POs corresponding to box inputs
        for ( k = 0; k < Tim_ManBoxInputNum(pTime, i); k++ )
        {
            pObj = Gia_ManPo( p, curCo + k );
            Vec_IntPush( vNodes, Gia_ObjId(p, pObj) );
        }
        curCo += Tim_ManBoxInputNum(pTime, i);
        // add PIs corresponding to box outputs
        for ( k = 0; k < Tim_ManBoxOutputNum(pTime, i); k++ )
        {
            pObj = Gia_ManPi( p, curCi + k );
//Gia_ObjPrint( p, pObj );
            Vec_IntPush( vNodes, Gia_ObjId(p, pObj) );
            Gia_ObjSetTravIdCurrent( p, pObj );
        }
        curCi += Tim_ManBoxOutputNum(pTime, i);
    }
    // add remaining nodes
    for ( i = Tim_ManCoNum(pTime) - Tim_ManPoNum(pTime); i < Tim_ManCoNum(pTime); i++ )
    {
        pObj = Gia_ManPo( p, i );
        Gia_ManDupFindOrderWithHie_rec( p, Gia_ObjFanin0(pObj), vNodes );
    }
    // add POs
    for ( i = Tim_ManCoNum(pTime) - Tim_ManPoNum(pTime); i < Tim_ManCoNum(pTime); i++ )
    {
        pObj = Gia_ManPo( p, i );
        Vec_IntPush( vNodes, Gia_ObjId(p, pObj) );
    }
    curCo += Tim_ManPoNum(pTime);
    // verify counts
    assert( curCi == Gia_ManPiNum(p) );
    assert( curCo == Gia_ManPoNum(p) );
    assert( Vec_IntSize(vNodes) == Gia_ManObjNum(p) );
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Duplicates AIG according to the timing manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDupWithHierarchy( Gia_Man_t * p, Vec_Int_t ** pvNodes )
{
    Vec_Int_t * vNodes;
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i;
    Gia_ManFillValue( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    if ( p->pSibls )
        pNew->pSibls = ABC_CALLOC( int, Gia_ManObjNum(p) );
    vNodes = Gia_ManDupFindOrderWithHie( p );
    Gia_ManForEachObjVec( vNodes, p, pObj, i )
    {
        if ( Gia_ObjIsAnd(pObj) )
        {
            pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
            if ( Gia_ObjSibl(p, Gia_ObjId(p, pObj)) )
                pNew->pSibls[Abc_Lit2Var(pObj->Value)] = Abc_Lit2Var(Gia_ObjSiblObj(p, Gia_ObjId(p, pObj))->Value);        
        }
        else if ( Gia_ObjIsCi(pObj) )
            pObj->Value = Gia_ManAppendCi( pNew );
        else if ( Gia_ObjIsCo(pObj) )
            pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
        else if ( Gia_ObjIsConst0(pObj) )
            pObj->Value = 0;
        else assert( 0 );
    }
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    if ( pvNodes )
        *pvNodes = vNodes;
    else
        Vec_IntFree( vNodes );
    return pNew;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManDupWithBoxes_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Gia_Man_t * pNew )
{
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return;
    Gia_ObjSetTravIdCurrent(p, pObj);
    assert( Gia_ObjIsAnd(pObj) );
    if ( Gia_ObjSibl(p, Gia_ObjId(p, pObj)) )
        Gia_ManDupWithBoxes_rec( p, Gia_ObjSiblObj(p, Gia_ObjId(p, pObj)), pNew );
    Gia_ManDupWithBoxes_rec( p, Gia_ObjFanin0(pObj), pNew );
    Gia_ManDupWithBoxes_rec( p, Gia_ObjFanin1(pObj), pNew );
//    assert( !~pObj->Value );
    pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    if ( Gia_ObjSibl(p, Gia_ObjId(p, pObj)) )
        pNew->pSibls[Abc_Lit2Var(pObj->Value)] = Abc_Lit2Var(Gia_ObjSiblObj(p, Gia_ObjId(p, pObj))->Value);        
}
Gia_Man_t * Gia_ManDupWithBoxes( Gia_Man_t * p, Gia_Man_t * pBoxes )
{
    Tim_Man_t * pTime = (Tim_Man_t *)p->pManTime;
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj, * pObjBox;
    int i, k, curCi, curCo;
    assert( Gia_ManRegNum(p) == 0 );
    assert( Gia_ManPiNum(p) == Tim_ManPiNum(pTime) + Gia_ManPoNum(pBoxes) );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    if ( p->pSibls )
        pNew->pSibls = ABC_CALLOC( int, Gia_ManObjNum(p) );
    Gia_ManHashAlloc( pNew );
    // copy const and real PIs
    Gia_ManFillValue( p );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManIncrementTravId( p );
    Gia_ObjSetTravIdCurrent( p, Gia_ManConst0(p) );
    for ( i = 0; i < Tim_ManPiNum(pTime); i++ )
    {
        pObj = Gia_ManPi( p, i );
        pObj->Value = Gia_ManAppendCi(pNew);
        Gia_ObjSetTravIdCurrent( p, pObj );
    }
    // create logic for each box
    curCi = Tim_ManPiNum(pTime);
    curCo = 0;
    for ( i = 0; i < Tim_ManBoxNum(pTime); i++ )
    {
        // clean boxes
        Gia_ManIncrementTravId( pBoxes );
        Gia_ObjSetTravIdCurrent( pBoxes, Gia_ManConst0(pBoxes) );
        Gia_ManConst0(pBoxes)->Value = 0;
        // add internal nodes
        for ( k = 0; k < Tim_ManBoxInputNum(pTime, i); k++ )
        {
            // build logic
            pObj = Gia_ManPo( p, curCo + k );
            Gia_ManDupWithBoxes_rec( p, Gia_ObjFanin0(pObj), pNew );
            // transfer to the PI
            pObjBox = Gia_ManPi( pBoxes, k );
            pObjBox->Value = Gia_ObjFanin0Copy(pObj);
            Gia_ObjSetTravIdCurrent( pBoxes, pObjBox );
        }
        curCo += Tim_ManBoxInputNum(pTime, i);
        // add internal nodes
        for ( k = 0; k < Tim_ManBoxOutputNum(pTime, i); k++ )
        {
            // build logic
            pObjBox = Gia_ManPo( pBoxes, curCi - Tim_ManPiNum(pTime) + k );
            Gia_ManDupWithBoxes_rec( pBoxes, Gia_ObjFanin0(pObjBox), pNew );
            // transfer to the PI
            pObj = Gia_ManPi( p, curCi + k );
            pObj->Value = Gia_ObjFanin0Copy(pObjBox);
            Gia_ObjSetTravIdCurrent( p, pObj );
        }
        curCi += Tim_ManBoxOutputNum(pTime, i);
    }
    // add remaining nodes
    for ( i = Tim_ManCoNum(pTime) - Tim_ManPoNum(pTime); i < Tim_ManCoNum(pTime); i++ )
    {
        pObj = Gia_ManPo( p, i );
        Gia_ManDupWithBoxes_rec( p, Gia_ObjFanin0(pObj), pNew );
        pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    }
    curCo += Tim_ManPoNum(pTime);
    // verify counts
    assert( curCi == Gia_ManPiNum(p) );
    assert( curCo == Gia_ManPoNum(p) );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    Gia_ManHashStop( pNew );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    assert( Tim_ManPoNum(pTime) == Gia_ManPoNum(pNew) );
    assert( Tim_ManPiNum(pTime) == Gia_ManPiNum(pNew) );
    return pNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManLevelWithBoxes_rec( Gia_Man_t * p, Gia_Obj_t * pObj )
{
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return;
    Gia_ObjSetTravIdCurrent(p, pObj);
    assert( Gia_ObjIsAnd(pObj) );
    if ( Gia_ObjSibl(p, Gia_ObjId(p, pObj)) )
        Gia_ManLevelWithBoxes_rec( p, Gia_ObjSiblObj(p, Gia_ObjId(p, pObj)) );
    Gia_ManLevelWithBoxes_rec( p, Gia_ObjFanin0(pObj) );
    Gia_ManLevelWithBoxes_rec( p, Gia_ObjFanin1(pObj) );
    Gia_ObjSetAndLevel( p, pObj );
}
int Gia_ManLevelWithBoxes( Gia_Man_t * p )
{
    Tim_Man_t * pTime = (Tim_Man_t *)p->pManTime;
    Gia_Obj_t * pObj;
    int i, k, curCi, curCo, LevelMax;
    assert( Gia_ManRegNum(p) == 0 );
    // copy const and real PIs
    Gia_ManCleanLevels( p, Gia_ManObjNum(p) );
    Gia_ObjSetLevel( p, Gia_ManConst0(p), 0 );
    Gia_ManIncrementTravId( p );
    Gia_ObjSetTravIdCurrent( p, Gia_ManConst0(p) );
    for ( i = 0; i < Tim_ManPiNum(pTime); i++ )
    {
        pObj = Gia_ManPi( p, i );
//        Gia_ObjSetLevel( p, pObj, Tim_ManGetCiArrival(pTime, i) );
        Gia_ObjSetLevel( p, pObj, 0 );
        Gia_ObjSetTravIdCurrent( p, pObj );
    }
    // create logic for each box
    curCi = Tim_ManPiNum(pTime);
    curCo = 0;
    for ( i = 0; i < Tim_ManBoxNum(pTime); i++ )
    {
        LevelMax = 0;
        for ( k = 0; k < Tim_ManBoxInputNum(pTime, i); k++ )
        {
            pObj = Gia_ManPo( p, curCo + k );
            Gia_ManLevelWithBoxes_rec( p, Gia_ObjFanin0(pObj) );
            Gia_ObjSetCoLevel( p, pObj );
            LevelMax = Abc_MaxInt( LevelMax, Gia_ObjLevel(p, pObj) );
        }
        curCo += Tim_ManBoxInputNum(pTime, i);
        LevelMax++;
        for ( k = 0; k < Tim_ManBoxOutputNum(pTime, i); k++ )
        {
            pObj = Gia_ManPi( p, curCi + k );
            Gia_ObjSetLevel( p, pObj, LevelMax );
            Gia_ObjSetTravIdCurrent( p, pObj );
        }
        curCi += Tim_ManBoxOutputNum(pTime, i);
    }
    // add remaining nodes
    p->nLevels = 0;
    for ( i = Tim_ManCoNum(pTime) - Tim_ManPoNum(pTime); i < Tim_ManCoNum(pTime); i++ )
    {
        pObj = Gia_ManPo( p, i );
        Gia_ManLevelWithBoxes_rec( p, Gia_ObjFanin0(pObj) );
        Gia_ObjSetCoLevel( p, pObj );
        p->nLevels = Abc_MaxInt( p->nLevels, Gia_ObjLevel(p, pObj) );
    }
    curCo += Tim_ManPoNum(pTime);
    // verify counts
    assert( curCi == Gia_ManPiNum(p) );
    assert( curCo == Gia_ManPoNum(p) );
//    printf( "Max level is %d.\n", p->nLevels );
    return p->nLevels;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManVerifyWithBoxes( Gia_Man_t * pGia, void * pParsInit )
{
    int fVerbose =  1;
    int Status   = -1;
    Gia_Man_t * pSpec, * pGia0, * pGia1, * pMiter;
    if ( pGia->pSpec == NULL )
    {
        printf( "Spec file is not given. Use standard flow.\n" );
        return Status;
    }
    if ( pGia->pManTime == NULL )
    {
        printf( "Design has no tim manager. Use standard flow.\n" );
        return Status;
    }
    if ( pGia->pAigExtra == NULL )
    {
        printf( "Design has no box logic. Use standard flow.\n" );
        return Status;
    }
    // read original AIG
    pSpec = Gia_AigerRead( pGia->pSpec, 0, 0 );
    if ( pSpec->pManTime == NULL )
    {
        printf( "Spec has no tim manager. Use standard flow.\n" );
        return Status;
    }
    if ( pSpec->pAigExtra == NULL )
    {
        printf( "Spec has no box logic. Use standard flow.\n" );
        return Status;
    }
    pGia0 = Gia_ManDupWithBoxes( pSpec, pSpec->pAigExtra );
    pGia1 = Gia_ManDupWithBoxes( pGia,  pGia->pAigExtra  );
    // compute the miter
    pMiter = Gia_ManMiter( pGia0, pGia1, 1, 0, fVerbose );
    if ( pMiter )
    {
        Cec_ParCec_t ParsCec, * pPars = &ParsCec;
        Cec_ManCecSetDefaultParams( pPars );
        pPars->fVerbose = fVerbose;
        if ( pParsInit )
            memcpy( pPars, pParsInit, sizeof(Cec_ParCec_t) );
        Status = Cec_ManVerify( pMiter, pPars );
        Gia_ManStop( pMiter );
        if ( pPars->iOutFail >= 0 )
            Abc_Print( 1, "Verification failed for at least one output (%d).\n", pPars->iOutFail );
    }
    Gia_ManStop( pGia0 );
    Gia_ManStop( pGia1 );
    Gia_ManStop( pSpec );
    return Status;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

