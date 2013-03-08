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

  Synopsis    [Find the ordering of AIG objects.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManOrderWithBoxes_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vNodes )
{
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return 0;
    Gia_ObjSetTravIdCurrent(p, pObj);
    if ( Gia_ObjIsCi(pObj) )
    {
        p->iData2 = Gia_ObjCioId(pObj);
        return 1;
    }
    assert( Gia_ObjIsAnd(pObj) );
    if ( Gia_ObjSibl(p, Gia_ObjId(p, pObj)) )
        if ( Gia_ManOrderWithBoxes_rec( p, Gia_ObjSiblObj(p, Gia_ObjId(p, pObj)), vNodes ) )
            return 1;
    if ( Gia_ManOrderWithBoxes_rec( p, Gia_ObjFanin0(pObj), vNodes ) )
        return 1;
    if ( Gia_ManOrderWithBoxes_rec( p, Gia_ObjFanin1(pObj), vNodes ) )
        return 1;
    Vec_IntPush( vNodes, Gia_ObjId(p, pObj) );
    return 0;
}
Vec_Int_t * Gia_ManOrderWithBoxes( Gia_Man_t * p )
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
    }
    // for each box, include box nodes
    curCi = Tim_ManPiNum(pTime);
    curCo = 0;
    for ( i = 0; i < Tim_ManBoxNum(pTime); i++ )
    {
        // add internal nodes
        for ( k = 0; k < Tim_ManBoxInputNum(pTime, i); k++ )
        {
            pObj = Gia_ManPo( p, curCo + k );
            if ( Gia_ManOrderWithBoxes_rec( p, Gia_ObjFanin0(pObj), vNodes ) )
            {
                int iCiNum  = p->iData2;
                int iBoxNum = Tim_ManBoxFindFromCiNum( p->pManTime, iCiNum );
                printf( "Boxes are not in a topological order. The command has to terminate.\n" );
                printf( "The following information may help debugging (numbers are 0-based):\n" );
                printf( "Input %d of BoxA %d (1stCI = %d; 1stCO = %d) has TFI with CI %d,\n", 
                    k, i, Tim_ManBoxOutputFirst(p->pManTime, i), Tim_ManBoxInputFirst(p->pManTime, i), iCiNum );
                printf( "which corresponds to output %d of BoxB %d (1stCI = %d; 1stCO = %d).\n", 
                    iCiNum - Tim_ManBoxOutputFirst(p->pManTime, iBoxNum), iBoxNum, 
                    Tim_ManBoxOutputFirst(p->pManTime, iBoxNum), Tim_ManBoxInputFirst(p->pManTime, iBoxNum) );
                printf( "In a correct topological order, BoxB should preceed BoxA.\n" );
                Vec_IntFree( vNodes );
                p->iData2 = 0;
                return NULL;
            }
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
            Vec_IntPush( vNodes, Gia_ObjId(p, pObj) );
            Gia_ObjSetTravIdCurrent( p, pObj );
        }
        curCi += Tim_ManBoxOutputNum(pTime, i);
    }
    // add remaining nodes
    for ( i = Tim_ManCoNum(pTime) - Tim_ManPoNum(pTime); i < Tim_ManCoNum(pTime); i++ )
    {
        pObj = Gia_ManPo( p, i );
        Gia_ManOrderWithBoxes_rec( p, Gia_ObjFanin0(pObj), vNodes );
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
Gia_Man_t * Gia_ManDupUnnormalize( Gia_Man_t * p )
{
    Vec_Int_t * vNodes;
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i;
    vNodes = Gia_ManOrderWithBoxes( p );
    if ( vNodes == NULL )
        return NULL;
    Gia_ManFillValue( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    if ( p->pSibls )
        pNew->pSibls = ABC_CALLOC( int, Gia_ManObjNum(p) );
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
    Vec_IntFree( vNodes );
    return pNew;
}


/**Function*************************************************************

  Synopsis    [Remaps the AIG from the old manager into the new manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCleanupRemap( Gia_Man_t * p, Gia_Man_t * pGia )
{
    Gia_Obj_t * pObj, * pObjGia;
    int i, iPrev;
    Gia_ManForEachObj1( p, pObj, i )
    {
        iPrev = Gia_ObjValue(pObj);
        if ( iPrev == ~0 )
            continue;
        pObjGia = Gia_ManObj( pGia, Abc_Lit2Var(iPrev) );
        if ( pObjGia->Value == ~0 )
            Gia_ObjSetValue( pObj, pObjGia->Value ); 
        else
            Gia_ObjSetValue( pObj, Abc_LitNotCond(pObjGia->Value, Abc_LitIsCompl(iPrev)) );
    }
}

/**Function*************************************************************

  Synopsis    [Computes AIG with boxes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManDupCollapse_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Gia_Man_t * pNew )
{
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return;
    Gia_ObjSetTravIdCurrent(p, pObj);
    assert( Gia_ObjIsAnd(pObj) );
    if ( Gia_ObjSibl(p, Gia_ObjId(p, pObj)) )
        Gia_ManDupCollapse_rec( p, Gia_ObjSiblObj(p, Gia_ObjId(p, pObj)), pNew );
    Gia_ManDupCollapse_rec( p, Gia_ObjFanin0(pObj), pNew );
    Gia_ManDupCollapse_rec( p, Gia_ObjFanin1(pObj), pNew );
//    assert( !~pObj->Value );
    pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    if ( Gia_ObjSibl(p, Gia_ObjId(p, pObj)) )
        pNew->pSibls[Abc_Lit2Var(pObj->Value)] = Abc_Lit2Var(Gia_ObjSiblObj(p, Gia_ObjId(p, pObj))->Value);        
}
Gia_Man_t * Gia_ManDupCollapse( Gia_Man_t * p, Gia_Man_t * pBoxes, Vec_Int_t * vBoxPres )
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
        if ( Tim_ManBoxIsBlack(pTime, i) )
        {
            int fSkip = (vBoxPres != NULL && !Vec_IntEntry(vBoxPres, i));
            for ( k = 0; k < Tim_ManBoxInputNum(pTime, i); k++ )
            {
                pObj = Gia_ManPo( p, curCo + k );
                Gia_ManDupCollapse_rec( p, Gia_ObjFanin0(pObj), pNew );
                pObj->Value = fSkip ? -1 : Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
            }
            for ( k = 0; k < Tim_ManBoxOutputNum(pTime, i); k++ )
            {
                pObj = Gia_ManPi( p, curCi + k );
                pObj->Value = fSkip ? 0 : Gia_ManAppendCi(pNew);
                Gia_ObjSetTravIdCurrent( p, pObj );
            }
        }
        else
        {
            for ( k = 0; k < Tim_ManBoxInputNum(pTime, i); k++ )
            {
                // build logic
                pObj = Gia_ManPo( p, curCo + k );
                Gia_ManDupCollapse_rec( p, Gia_ObjFanin0(pObj), pNew );
                // transfer to the PI
                pObjBox = Gia_ManPi( pBoxes, k );
                pObjBox->Value = Gia_ObjFanin0Copy(pObj);
                Gia_ObjSetTravIdCurrent( pBoxes, pObjBox );
            }
            for ( k = 0; k < Tim_ManBoxOutputNum(pTime, i); k++ )
            {
                // build logic
                pObjBox = Gia_ManPo( pBoxes, curCi - Tim_ManPiNum(pTime) + k );
                Gia_ManDupCollapse_rec( pBoxes, Gia_ObjFanin0(pObjBox), pNew );
                // transfer to the PI
                pObj = Gia_ManPi( p, curCi + k );
                pObj->Value = Gia_ObjFanin0Copy(pObjBox);
                Gia_ObjSetTravIdCurrent( p, pObj );
            }
        }
        curCo += Tim_ManBoxInputNum(pTime, i);
        curCi += Tim_ManBoxOutputNum(pTime, i);
    }
    // add remaining nodes
    for ( i = Tim_ManCoNum(pTime) - Tim_ManPoNum(pTime); i < Tim_ManCoNum(pTime); i++ )
    {
        pObj = Gia_ManPo( p, i );
        Gia_ManDupCollapse_rec( p, Gia_ObjFanin0(pObj), pNew );
        pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    }
    curCo += Tim_ManPoNum(pTime);
    // verify counts
    assert( curCi == Gia_ManPiNum(p) );
    assert( curCo == Gia_ManPoNum(p) );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    Gia_ManHashStop( pNew );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManCleanupRemap( p, pTemp );
    Gia_ManStop( pTemp );
    assert( Tim_ManPoNum(pTime) == Gia_ManPoNum(pNew) );
    assert( Tim_ManPiNum(pTime) == Gia_ManPiNum(pNew) );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Computes level with boxes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManLevelWithBoxes_rec( Gia_Man_t * p, Gia_Obj_t * pObj )
{
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return 0;
    Gia_ObjSetTravIdCurrent(p, pObj);
    if ( Gia_ObjIsCi(pObj) )
        return 1;
    assert( Gia_ObjIsAnd(pObj) );
    if ( Gia_ObjSibl(p, Gia_ObjId(p, pObj)) )
        Gia_ManLevelWithBoxes_rec( p, Gia_ObjSiblObj(p, Gia_ObjId(p, pObj)) );
    if ( Gia_ManLevelWithBoxes_rec( p, Gia_ObjFanin0(pObj) ) )
        return 1;
    if ( Gia_ManLevelWithBoxes_rec( p, Gia_ObjFanin1(pObj) ) )
        return 1;
    Gia_ObjSetAndLevel( p, pObj );
    return 0;
}
int Gia_ManLevelWithBoxes( Gia_Man_t * p )
{
    int nAnd2Delay = p->nAnd2Delay ? p->nAnd2Delay : 1;
    Tim_Man_t * pTime = (Tim_Man_t *)p->pManTime;
    Gia_Obj_t * pObj, * pObjIn;
    int i, k, j, curCi, curCo, LevelMax;
    assert( Gia_ManRegNum(p) == 0 );
    // copy const and real PIs
    Gia_ManCleanLevels( p, Gia_ManObjNum(p) );
    Gia_ObjSetLevel( p, Gia_ManConst0(p), 0 );
    Gia_ManIncrementTravId( p );
    Gia_ObjSetTravIdCurrent( p, Gia_ManConst0(p) );
    for ( i = 0; i < Tim_ManPiNum(pTime); i++ )
    {
        pObj = Gia_ManPi( p, i );
        Gia_ObjSetLevel( p, pObj, Tim_ManGetCiArrival(pTime, i) / nAnd2Delay );
        Gia_ObjSetTravIdCurrent( p, pObj );
    }
    // create logic for each box
    curCi = Tim_ManPiNum(pTime);
    curCo = 0;
    for ( i = 0; i < Tim_ManBoxNum(pTime); i++ )
    {
        int nBoxInputs  = Tim_ManBoxInputNum( pTime, i );
        int nBoxOutputs = Tim_ManBoxOutputNum( pTime, i );
        float * pDelayTable = Tim_ManBoxDelayTable( pTime, i );
        // compute level for TFI of box inputs
        for ( k = 0; k < nBoxInputs; k++ )
        {
            pObj = Gia_ManPo( p, curCo + k );
            if ( Gia_ManLevelWithBoxes_rec( p, Gia_ObjFanin0(pObj) ) )
            {
                printf( "Boxes are not in a topological order. Switching to level computation without boxes.\n" );
                return Gia_ManLevelNum( p );
            }
            // set box input level
            Gia_ObjSetCoLevel( p, pObj );
        }
        // compute level for box outputs
        for ( k = 0; k < nBoxOutputs; k++ )
        {
            pObj = Gia_ManPi( p, curCi + k );
            Gia_ObjSetTravIdCurrent( p, pObj );
            // evaluate delay of this output
            LevelMax = 0;
            assert( nBoxInputs == (int)pDelayTable[1] );
            for ( j = 0; j < nBoxInputs && (pObjIn = Gia_ManPo(p, curCo + j)); j++ )
                if ( (int)pDelayTable[3+k*nBoxInputs+j] != -ABC_INFINITY )
                    LevelMax = Abc_MaxInt( LevelMax, Gia_ObjLevel(p, pObjIn) + ((int)pDelayTable[3+k*nBoxInputs+j] / nAnd2Delay) );
            // set box output level
            Gia_ObjSetLevel( p, pObj, LevelMax );
        }
        curCo += nBoxInputs;
        curCi += nBoxOutputs;
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

  Synopsis    [Verify XAIG against its spec.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManVerifyWithBoxes( Gia_Man_t * pGia, void * pParsInit )
{
    int fVerbose =  1;
    int Status   = -1;
    Gia_Man_t * pSpec, * pGia0, * pGia1, * pMiter;
    Vec_Int_t * vBoxPres = NULL;
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
    // if timing managers have different number of black boxes,
    // it is possible that some of the boxes are swept away
    if ( Tim_ManBlackBoxNum( (Tim_Man_t *)pSpec->pManTime ) > 0 )
    {
        // specification cannot have fewer boxes than implementation
        if ( Tim_ManBoxNum( (Tim_Man_t *)pSpec->pManTime ) < Tim_ManBoxNum( (Tim_Man_t *)pGia->pManTime ) )
        {
            printf( "Spec has more boxes than the design. Cannot proceed.\n" );
            return Status;
        }
        // to align the boxes, find what boxes of pSpec are dropped in pGia
        if ( Tim_ManBoxNum( (Tim_Man_t *)pSpec->pManTime ) != Tim_ManBoxNum( (Tim_Man_t *)pGia->pManTime ) )
        {
            vBoxPres = Tim_ManAlignTwo( (Tim_Man_t *)pSpec->pManTime, (Tim_Man_t *)pGia->pManTime );
            if ( vBoxPres == NULL )
            {
                printf( "Boxes of spec and design cannot be aligned. Cannot proceed.\n" );
                return Status;
            }
        }
    }
    // collapse two designs
    pGia0 = Gia_ManDupCollapse( pSpec, pSpec->pAigExtra, vBoxPres );
    pGia1 = Gia_ManDupCollapse( pGia,  pGia->pAigExtra,  NULL  );
    Vec_IntFreeP( &vBoxPres );
    // compute the miter
    pMiter = Gia_ManMiter( pGia0, pGia1, 0, 1, 0, fVerbose );
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

/**Function*************************************************************

  Synopsis    [Update hierarchy/timing manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void * Gia_ManUpdateTimMan( Gia_Man_t * p, Vec_Int_t * vBoxPres )
{
    assert( p->pManTime != NULL );
    assert( Tim_ManBoxNum(p->pManTime) == Vec_IntSize(vBoxPres) );
    return Tim_ManTrim( p->pManTime, vBoxPres );
}

/**Function*************************************************************

  Synopsis    [Update AIG of the holes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManUpdateExtraAig( void * pTime, Gia_Man_t * p, Vec_Int_t * vBoxPres )
{
    Gia_Man_t * pNew = NULL;
    Tim_Man_t * pManTime = (Tim_Man_t *)pTime;
    Vec_Int_t * vOutPres = Vec_IntAlloc( 100 );
    int i, k, curPo = 0;
    assert( Vec_IntSize(vBoxPres) == Tim_ManBoxNum(pManTime) );
    assert( Gia_ManPoNum(p) == Tim_ManCiNum(pManTime) - Tim_ManPiNum(pManTime) );
    for ( i = 0; i < Tim_ManBoxNum(pManTime); i++ )
    {
        for ( k = 0; k < Tim_ManBoxOutputNum(pManTime, i); k++ )
            Vec_IntPush( vOutPres, Vec_IntEntry(vBoxPres, i) );
        curPo += Tim_ManBoxOutputNum(pManTime, i);
    }
    assert( curPo == Gia_ManPoNum(p) );
//    if ( Vec_IntSize(vOutPres) > 0 )
        pNew = Gia_ManDupOutputVec( p, vOutPres );
    Vec_IntFree( vOutPres );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

