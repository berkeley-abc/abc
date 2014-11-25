/**CFile****************************************************************

  FileName    [giaSweep.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Sweeping of GIA manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaSweep.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "giaAig.h"
#include "proof/dch/dch.h"
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

  Synopsis    [Mark GIA nodes that feed into POs.]

  Description [Returns the array of classes of remaining registers.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManMarkSeqGiaWithBoxes_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vRoots )
{
    Tim_Man_t * pManTime = (Tim_Man_t *)p->pManTime;
    int i, iBox, nBoxIns, nBoxOuts, iShift, nRealCis;
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return;
    Gia_ObjSetTravIdCurrent(p, pObj);
    if ( Gia_ObjIsAnd(pObj) )
    {
        Gia_ManMarkSeqGiaWithBoxes_rec( p, Gia_ObjFanin0(pObj), vRoots );
        Gia_ManMarkSeqGiaWithBoxes_rec( p, Gia_ObjFanin1(pObj), vRoots );
        return;
    }
    assert( Gia_ObjIsCi(pObj) );
    nRealCis = Tim_ManPiNum(pManTime);
    if ( Gia_ObjCioId(pObj) < nRealCis )
    {
        int nRegs = Gia_ManRegBoxNum(p);
        int iFlop = Gia_ObjCioId(pObj) - (nRealCis - nRegs);
        assert( iFlop >= 0 && iFlop < nRegs );
        pObj = Gia_ManCo( p, Gia_ManPoNum(p) - nRegs + iFlop );
        Vec_IntPush( vRoots, Gia_ObjId(p, pObj) );
        return;
    }
    // get the box
    iBox = Tim_ManBoxForCi( pManTime, Gia_ObjCioId(pObj) );
    nBoxIns = Tim_ManBoxInputNum(pManTime, iBox);
    nBoxOuts = Tim_ManBoxOutputNum(pManTime, iBox);
    // mark all outputs
    iShift = Tim_ManBoxOutputFirst(pManTime, iBox);
    for ( i = 0; i < nBoxOuts; i++ )
        Gia_ObjSetTravIdCurrent(p, Gia_ManCi(p, iShift + i));
    // traverse from inputs
    iShift = Tim_ManBoxInputFirst(pManTime, iBox);
    for ( i = 0; i < nBoxIns; i++ )
        Gia_ObjSetTravIdCurrent(p, Gia_ManCo(p, iShift + i));
    for ( i = 0; i < nBoxIns; i++ )
        Gia_ManMarkSeqGiaWithBoxes_rec( p, Gia_ObjFanin0(Gia_ManCo(p, iShift + i)), vRoots );
}
void Gia_ManMarkSeqGiaWithBoxes( Gia_Man_t * p, int fSeq )
{
    // CI order: real PIs + flop outputs + box outputs
    // CO order: box inputs + real POs + flop inputs
    Tim_Man_t * pManTime = (Tim_Man_t *)p->pManTime;
    Vec_Int_t * vRoots;
    Gia_Obj_t * pObj;
    int nRealCis = Tim_ManPiNum(pManTime);
    int nRealCos = Tim_ManPoNum(pManTime);
    int i, nRegs = fSeq ? Gia_ManRegBoxNum(p) : 0;
    assert( Gia_ManRegNum(p) == 0 );
    assert( Gia_ManBoxNum(p) > 0 );
    // mark the terminals
    Gia_ManIncrementTravId( p );
    Gia_ObjSetTravIdCurrent( p, Gia_ManConst0(p) );
    for ( i = 0; i < nRealCis - nRegs; i++ )
        Gia_ObjSetTravIdCurrent( p, Gia_ManPi(p, i) );
    // collect flops reachable from the POs
    vRoots = Vec_IntAlloc( Gia_ManRegBoxNum(p) );
    for ( i = Gia_ManPoNum(p) - nRealCos; i < Gia_ManPoNum(p) - nRegs; i++ )
    {
        Gia_ObjSetTravIdCurrent( p, Gia_ManPo(p, i) );
        Gia_ManMarkSeqGiaWithBoxes_rec( p, Gia_ObjFanin0(Gia_ManPo(p, i)), vRoots );
    }
    // collect flops reachable from roots
    if ( fSeq )
    {
        Gia_ManForEachObjVec( vRoots, p, pObj, i )
        {
            assert( Gia_ObjIsCo(pObj) );
            Gia_ObjSetTravIdCurrent( p, pObj );
            Gia_ManMarkSeqGiaWithBoxes_rec( p, Gia_ObjFanin0(pObj), vRoots );
        }
        //printf( "Explored %d flops\n", Vec_IntSize(vRoots) );
    }
    Vec_IntFree( vRoots );
}
Gia_Man_t * Gia_ManDupWithBoxes( Gia_Man_t * p, int fSeq )
{
    Tim_Man_t * pManTime = (Tim_Man_t *)p->pManTime;
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    Vec_Int_t * vBoxesLeft;
    int curCi, curCo, nBoxIns, nBoxOuts;
    int i, k, iShift, nMarked;
    int CiLeft = 0, CoLeft = 0;
    assert( Gia_ManBoxNum(p) > 0 );
    assert( Gia_ManRegBoxNum(p) > 0 );
    // mark useful boxes
    Gia_ManMarkSeqGiaWithBoxes( p, fSeq );
    // duplicate marked entries
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachObj1( p, pObj, i )
    {
        if ( !Gia_ObjIsTravIdCurrent(p, pObj) )
            continue;
        if ( Gia_ObjIsCi(pObj) )
            pObj->Value = Gia_ManAppendCi(pNew);
        else if ( Gia_ObjIsAnd(pObj) )
            pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        else if ( Gia_ObjIsCo(pObj) )
            pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
        else assert( 0 );
    }
    assert( !Gia_ManHasDangling(pNew) );
    // collect remaining flops
    if ( fSeq )
    {
        pNew->vRegClasses = Vec_IntAlloc( Gia_ManRegBoxNum(p) );
        iShift = Gia_ManPoNum(p) - Gia_ManRegBoxNum(p);
        for ( i = 0; i < Gia_ManRegBoxNum(p); i++ )
            if ( Gia_ObjIsTravIdCurrent(p, Gia_ManCo(p, iShift + i)) )
                Vec_IntPush( pNew->vRegClasses, Vec_IntEntry(p->vRegClasses, i) );
    }
    else if ( p->vRegClasses )
        pNew->vRegClasses = Vec_IntDup( p->vRegClasses );
    // collect remaining boxes
    vBoxesLeft = Vec_IntAlloc( Gia_ManBoxNum(p) );
    curCi = Tim_ManPiNum(pManTime);
    curCo = 0;
    for ( i = 0; i < Gia_ManBoxNum(p); i++ )
    {
        nBoxIns = Tim_ManBoxInputNum(pManTime, i);
        nBoxOuts = Tim_ManBoxOutputNum(pManTime, i);
        nMarked = 0;
        for ( k = 0; k < nBoxIns; k++ )
            nMarked += Gia_ObjIsTravIdCurrent( p, Gia_ManCo(p, curCo + k) );
        for ( k = 0; k < nBoxOuts; k++ )
            nMarked += Gia_ObjIsTravIdCurrent( p, Gia_ManCi(p, curCi + k) );
        curCo += nBoxIns;
        curCi += nBoxOuts;
        // check presence
        assert( nMarked == 0 || nMarked == nBoxIns + nBoxOuts );
        if ( nMarked )
        {
            Vec_IntPush( vBoxesLeft, i );

            CoLeft += nBoxIns;
            CiLeft += nBoxOuts;
        }
    }
    curCo += Tim_ManPoNum(pManTime);
    assert( curCi == Gia_ManCiNum(p) );
    assert( curCo == Gia_ManCoNum(p) );
    // update timing manager
    pNew->pManTime = Gia_ManUpdateTimMan2( p, vBoxesLeft, Vec_IntSize(p->vRegClasses) - Vec_IntSize(pNew->vRegClasses) );
    // update extra STG
    assert( p->pAigExtra != NULL );
    assert( pNew->pAigExtra == NULL );
    pNew->pAigExtra = Gia_ManUpdateExtraAig2( p->pManTime, p->pAigExtra, vBoxesLeft );
    {
        int a = Gia_ManCiNum(pNew);
        int b = Tim_ManPiNum(pNew->pManTime);
        int c = Gia_ManCoNum(pNew->pAigExtra);
        int d = b + c;
    assert( Gia_ManCiNum(pNew) == Tim_ManPiNum(pNew->pManTime) + Gia_ManCoNum(pNew->pAigExtra) );
    }
    Vec_IntFree( vBoxesLeft );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Mark GIA nodes that feed into POs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManFraigCheckCis( Gia_Man_t * p, Gia_Obj_t * pObj )
{
    for ( assert( Gia_ObjIsCi(pObj) ); Gia_ObjIsCi(pObj); pObj-- )
        if ( Gia_ObjIsTravIdCurrent(p, pObj) )
            return 1;
    return 0;
}
Gia_Obj_t * Gia_ManFraigMarkCis( Gia_Man_t * p, Gia_Obj_t * pObj, int fMark )
{
    for ( assert( Gia_ObjIsCi(pObj) ); Gia_ObjIsCi(pObj); pObj-- )
        if ( fMark )
            Gia_ObjSetTravIdCurrent( p, pObj );
    return pObj;
}
Gia_Obj_t * Gia_ManFraigMarkCos( Gia_Man_t * p, Gia_Obj_t * pObj, int fMark )
{
    for ( assert( Gia_ObjIsCo(pObj) ); Gia_ObjIsCo(pObj); pObj-- )
        if ( fMark )
        {
            Gia_ObjSetTravIdCurrent( p, pObj );
            Gia_ObjSetTravIdCurrent( p, Gia_ObjFanin0(pObj) );
        }
    return pObj;
}
Gia_Obj_t * Gia_ManFraigMarkAnd( Gia_Man_t * p, Gia_Obj_t * pObj )
{
    for ( assert( Gia_ObjIsAnd(pObj) ); Gia_ObjIsAnd(pObj); pObj-- )
        if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        {
            Gia_ObjSetTravIdCurrent( p, Gia_ObjFanin0(pObj) );
            Gia_ObjSetTravIdCurrent( p, Gia_ObjFanin1(pObj) );
        }
    return pObj;
}
Gia_Man_t * Gia_ManFraigCreateGia( Gia_Man_t * p )
{
    Vec_Int_t * vBoxPres;
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i, fLabelPos;
    assert( p->pManTime != NULL );
    // start marks
    Gia_ManIncrementTravId( p );
    Gia_ObjSetTravIdCurrent( p, Gia_ManConst0(p) );
    vBoxPres = Vec_IntAlloc( 1000 );
    // mark primary outputs
    fLabelPos = 1;
    pObj = Gia_ManObj( p, Gia_ManObjNum(p) - 1 );
    assert( Gia_ObjIsCo(pObj) );
    while ( Gia_ObjIsCo(pObj) )
    {
        pObj = Gia_ManFraigMarkCos( p, pObj, fLabelPos );
        if ( Gia_ObjIsAnd(pObj) )
            pObj = Gia_ManFraigMarkAnd( p, pObj );
        assert( Gia_ObjIsCi(pObj) );
        fLabelPos = Gia_ManFraigCheckCis(p, pObj);
        pObj = Gia_ManFraigMarkCis( p, pObj, fLabelPos );
        Vec_IntPush( vBoxPres, fLabelPos );
    }
    Vec_IntPop( vBoxPres );
    Vec_IntReverseOrder( vBoxPres );
    assert( Gia_ObjIsConst0(pObj) );
    // mark primary inputs
    Gia_ManForEachObj1( p, pObj, i )
        if ( Gia_ObjIsCi(pObj) )
            Gia_ObjSetTravIdCurrent( p, pObj );
        else
            break;
    // duplicate marked entries
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachObj1( p, pObj, i )
    {
        if ( !Gia_ObjIsTravIdCurrent(p, pObj) )
            continue;
        if ( Gia_ObjIsCi(pObj) )
            pObj->Value = Gia_ManAppendCi(pNew);
        else if ( Gia_ObjIsAnd(pObj) )
            pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        else if ( Gia_ObjIsCo(pObj) )
            pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
        else assert( 0 );
    }
    // update timing manager
    pNew->pManTime = Gia_ManUpdateTimMan( p, vBoxPres );
    // update extra STG
    assert( p->pAigExtra != NULL );
    assert( pNew->pAigExtra == NULL );
    pNew->pAigExtra = Gia_ManUpdateExtraAig( p->pManTime, p->pAigExtra, vBoxPres );
    Vec_IntFree( vBoxPres );
//    assert( Gia_ManPiNum(pNew) == Tim_ManCiNum(pNew->pManTime) );
//    assert( Gia_ManPoNum(pNew) == Tim_ManCoNum(pNew->pManTime) );
//    assert( Gia_ManPiNum(pNew) == Tim_ManPiNum(pNew->pManTime) + Gia_ManPoNum(pNew->pAigExtra) );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ObjFanin0CopyRepr( Gia_Man_t * p, Gia_Obj_t * pObj, int * pReprs )
{
    int fanId = Gia_ObjFaninId0p( p, pObj );
    if ( pReprs[fanId] == -1 )
        return Gia_ObjFanin0Copy( pObj );
    assert( Abc_Lit2Var(pReprs[fanId]) < Gia_ObjId(p, pObj) );
    return Abc_LitNotCond( Gia_ObjValue(Gia_ManObj(p, Abc_Lit2Var(pReprs[fanId]))), Gia_ObjFaninC0(pObj) ^ Abc_LitIsCompl(pReprs[fanId]) );
}
int Gia_ObjFanin1CopyRepr( Gia_Man_t * p, Gia_Obj_t * pObj, int * pReprs )
{
    int fanId = Gia_ObjFaninId1p( p, pObj );
    if ( pReprs[fanId] == -1 )
        return Gia_ObjFanin1Copy( pObj );
    assert( Abc_Lit2Var(pReprs[fanId]) < Gia_ObjId(p, pObj) );
    return Abc_LitNotCond( Gia_ObjValue(Gia_ManObj(p, Abc_Lit2Var(pReprs[fanId]))), Gia_ObjFaninC1(pObj) ^ Abc_LitIsCompl(pReprs[fanId]) );
}
Gia_Man_t * Gia_ManFraigReduceGia( Gia_Man_t * p, int * pReprs )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i;
    assert( pReprs != NULL );
    assert( Gia_ManRegNum(p) == 0 );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManFillValue( p );
    Gia_ManHashAlloc( pNew );
    Gia_ManForEachObj( p, pObj, i )
    {
        if ( Gia_ObjIsAnd(pObj) )
            pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0CopyRepr(p, pObj, pReprs), Gia_ObjFanin1CopyRepr(p, pObj, pReprs) );
        else if ( Gia_ObjIsCi(pObj) )
            pObj->Value = Gia_ManAppendCi( pNew );
        else if ( Gia_ObjIsCo(pObj) )
            pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0CopyRepr(p, pObj, pReprs) );
        else if ( Gia_ObjIsConst0(pObj) )
            pObj->Value = 0;
        else assert( 0 );
    }
    Gia_ManHashStop( pNew );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Computes representatives in terms of the original objects.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int * Gia_ManFraigSelectReprs( Gia_Man_t * p, Gia_Man_t * pClp, int fVerbose )
{
    Gia_Obj_t * pObj;
    Tim_Man_t * pManTime = (Tim_Man_t *)p->pManTime;
    int * pReprs   = ABC_FALLOC( int, Gia_ManObjNum(p) );
    int * pClp2Gia = ABC_FALLOC( int, Gia_ManObjNum(pClp) );
    int i, nBoxes, iLast, iBox, iLitClp, iLitClp2, iReprClp, fCompl;
    int nConsts = 0, nReprs = 0, Count1 = 0, Count2 = 0;
    assert( pManTime != NULL );
    // count the number of equivalent objects
    Gia_ManForEachObj1( pClp, pObj, i )
    {
        if ( Gia_ObjIsCo(pObj) )
            continue;
        if ( i == Gia_ObjReprSelf(pClp, i) )
            continue;
        if ( Gia_ObjReprSelf(pClp, i) == 0 )
            nConsts++;
        else
            nReprs++;
    }
    if ( fVerbose )
        printf( "Computed %d const objects and %d other objects.\n", nConsts, nReprs );
    nConsts = nReprs = 0;

    // mark flop input boxes
    Gia_ManCleanMark0( p );
    for ( i = Gia_ManPoNum(p) - Gia_ManRegBoxNum(p); i < Gia_ManPoNum(p); i++ )
    {
        pObj = Gia_ObjFanin0( Gia_ManPo(p, i) );
        assert( Gia_ObjIsCi(pObj) );
        pObj->fMark0 = 1;
        Count1++;
    }
    // mark connects between last box inputs and first box outputs
    nBoxes =  Tim_ManBoxNum( pManTime );
    for ( i = 0; i < nBoxes; i++ )
    {
        iLast = Tim_ManBoxInputLast( pManTime, i );
        pObj = Gia_ObjFanin0( Gia_ManCo(p, iLast) );
        if ( !Gia_ObjIsCi(pObj) )
            continue;
        iBox = Tim_ManBoxForCi( pManTime, Gia_ObjCioId(pObj) );
        if ( iBox == -1 ) 
            continue;
        assert( Gia_ObjIsCi(pObj) );
        if ( Gia_ObjCioId(pObj) == Tim_ManBoxOutputLast(pManTime, iBox) )
            pObj->fMark0 = 1, Count2++;
    }
    if ( fVerbose )
        printf( "Fixed %d flop inputs and %d box/box connections (out of %d boxes).\n", 
            Count1, Count2, nBoxes - Gia_ManRegBoxNum(p) );

    // compute representatives
    pClp2Gia[0] = 0;
    Gia_ManSetPhase( pClp );
    Gia_ManForEachObj1( p, pObj, i )
    {
        if ( Gia_ObjIsCo(pObj) )
            continue;
        if ( Gia_ObjIsCi(pObj) && pObj->fMark0 ) // skip CI pointed by CO
            continue;
        assert( Gia_ObjIsCi(pObj) || Gia_ObjIsAnd(pObj) );
        iLitClp = Gia_ObjValue(pObj);
        if ( iLitClp == -1 )
            continue;
        iReprClp = Gia_ObjReprSelf( pClp, Abc_Lit2Var(iLitClp) );
        if ( pClp2Gia[iReprClp] == -1 )
            pClp2Gia[iReprClp] = i;
        else
        { 
            iLitClp2 = Gia_ObjValue( Gia_ManObj(p, pClp2Gia[iReprClp]) );
            assert( Gia_ObjReprSelf(pClp, Abc_Lit2Var(iLitClp)) == Gia_ObjReprSelf(pClp, Abc_Lit2Var(iLitClp2)) );
            fCompl  = Abc_LitIsCompl(iLitClp) ^ Abc_LitIsCompl(iLitClp2);
            fCompl ^= Gia_ManObj(pClp, Abc_Lit2Var(iLitClp))->fPhase;
            fCompl ^= Gia_ManObj(pClp, Abc_Lit2Var(iLitClp2))->fPhase;
            pReprs[i] = Abc_Var2Lit( pClp2Gia[iReprClp], fCompl );
            assert( Abc_Lit2Var(pReprs[i]) < i );
            if ( pClp2Gia[iReprClp] == 0 )
                nConsts++;
            else
                nReprs++;
        }
    }
    ABC_FREE( pClp2Gia );
    Gia_ManForEachCi( p, pObj, i )
        pObj->fMark0 = 0;
    if ( fVerbose )
        printf( "Found %d const objects and %d other objects.\n", nConsts, nReprs );
    return pReprs;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManFraigSweepPerform( Gia_Man_t * p, void * pPars )
{
    Aig_Man_t * pNew;
    pNew = Gia_ManToAigSimple( p );
    assert( Gia_ManObjNum(p) == Aig_ManObjNum(pNew) );
    Dch_ComputeEquivalences( pNew, (Dch_Pars_t *)pPars );
    Gia_ManReprFromAigRepr( pNew, p );
    Aig_ManStop( pNew );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManFraigSweepSimple( Gia_Man_t * p, void * pPars )
{
    Gia_Man_t * pNew;
    assert( p->pManTime == NULL || Gia_ManBoxNum(p) == 0 );
    Gia_ManFraigSweepPerform( p, pPars );
    pNew = Gia_ManEquivReduce( p, 1, 0, 0, 0 );
    if ( pNew == NULL )
        pNew = Gia_ManDup(p);
    Gia_ManTransferTiming( pNew, p );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Reduces root model with scorr.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManSweepWithBoxes( Gia_Man_t * p, void * pParsC, void * pParsS, int fConst, int fEquiv, int fVerbose )
{ 
    Gia_Man_t * pClp, * pNew, * pTemp;
    int * pReprs;
    assert( Gia_ManRegNum(p) == 0 );
    assert( p->pAigExtra != NULL );
    // order AIG objects
    pNew = Gia_ManDupUnnormalize( p );
    if ( pNew == NULL )
        return NULL;
    // find global equivalences
    Gia_ManTransferTiming( pNew, p );
    pClp = Gia_ManDupCollapse( pNew, pNew->pAigExtra, NULL, pParsC ? 0 : 1 );
    // compute equivalences
    if ( pParsC )
        Gia_ManFraigSweepPerform( pClp, pParsC );
    else if ( pParsS )
        Cec_ManLSCorrespondenceClasses( pClp, (Cec_ParCor_t *)pParsS );
    else 
        Gia_ManSeqCleanupClasses( pClp, fConst, fEquiv, fVerbose );
    // transfer equivalences
    pReprs = Gia_ManFraigSelectReprs( pNew, pClp, fVerbose );
    Gia_ManStop( pClp );
    // reduce AIG
    Gia_ManTransferTiming( p, pNew );
    pNew = Gia_ManFraigReduceGia( pTemp = pNew, pReprs );
    Gia_ManTransferTiming( pNew, p );
    Gia_ManStop( pTemp );
    ABC_FREE( pReprs );
    // derive new AIG
    pNew = Gia_ManDupWithBoxes( pTemp = pNew, pParsC ? 0 : 1 );
    Gia_ManStop( pTemp );
    // normalize the result
    pNew = Gia_ManDupNormalize( pTemp = pNew );
    Gia_ManTransferTiming( pNew, pTemp );
    Gia_ManStop( pTemp );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

