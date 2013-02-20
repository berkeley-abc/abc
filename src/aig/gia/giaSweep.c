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

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

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
            Gia_ObjSetTravIdCurrent( p, pObj );
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
    Vec_IntFree( vBoxPres );
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
    int faninId = Gia_ObjFaninId0p( p, pObj );
    if ( pReprs[faninId] == -1 )
        return Gia_ObjFanin0Copy( pObj );
    assert( Abc_Lit2Var(pReprs[faninId]) < Gia_ObjId(p, pObj) );
    return Abc_LitNotCond( Gia_ObjValue(Gia_ManObj(p, Abc_Lit2Var(pReprs[faninId]))), Abc_LitIsCompl(pReprs[faninId]) );
}
int Gia_ObjFanin1CopyRepr( Gia_Man_t * p, Gia_Obj_t * pObj, int * pReprs )
{
    int faninId = Gia_ObjFaninId1p( p, pObj );
    if ( pReprs[faninId] == -1 )
        return Gia_ObjFanin1Copy( pObj );
    assert( Abc_Lit2Var(pReprs[faninId]) < Gia_ObjId(p, pObj) );
    return Abc_LitNotCond( Gia_ObjValue(Gia_ManObj(p, Abc_Lit2Var(pReprs[faninId]))), Abc_LitIsCompl(pReprs[faninId]) );
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
            pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0CopyRepr(p, pObj, pReprs), Gia_ObjFanin1CopyRepr(p, pObj, pReprs) );
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

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManFraigReduceGia2( Gia_Man_t * p, int * pReprs )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i;
    assert( p->pSibls == NULL );
    assert( Gia_ManRegNum(p) == 0 );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManHashAlloc( pNew );
    // copy const and real PIs
    Gia_ManFillValue( p );
    Gia_ManForEachObj( p, pObj, i )
    {
        if ( Gia_ObjIsAnd(pObj) )
        {
            assert( pReprs[i] == -1 || Abc_Lit2Var(pReprs[i]) < i );
            if ( pReprs[i] == -1 )
                pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
            else
                pObj->Value = Abc_LitNotCond( Gia_ObjValue(Gia_ManObj(p, Abc_Lit2Var(pReprs[i]))), Abc_LitIsCompl(pReprs[i]) );
        }
        else if ( Gia_ObjIsCi(pObj) )
            pObj->Value = Gia_ManAppendCi( pNew );
        else if ( Gia_ObjIsCo(pObj) )
            pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
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
int * Gia_ManFraigSelectReprs( Gia_Man_t * p, Gia_Man_t * pGia, int fVerbose )
{
    Gia_Obj_t * pObj;
    int * pReprs   = ABC_FALLOC( int, Gia_ManObjNum(p) );
    int * pGia2Abc = ABC_FALLOC( int, Gia_ManObjNum(pGia) );
    int i, iLitGia, iLitGia2, iReprGia, fCompl;
    int nConsts = 0, nReprs = 0;
    pGia2Abc[0] = 0;
    Gia_ManSetPhase( pGia );
    Gia_ManForEachObj1( p, pObj, i )
    {
        if ( Gia_ObjIsCo(pObj) )
            continue;
        assert( Gia_ObjIsCi(pObj) || Gia_ObjIsAnd(pObj) );
        iLitGia = Gia_ObjValue(pObj);
        if ( iLitGia == -1 )
            continue;
        iReprGia = Gia_ObjReprSelf( pGia, Abc_Lit2Var(iLitGia) );
        if ( pGia2Abc[iReprGia] == -1 )
            pGia2Abc[iReprGia] = i;
        else
        { 
//            iLitGia2 = Abc2_ObjCopyId( p, pGia2Abc[iReprGia] );
            iLitGia2 = Gia_ObjValue( Gia_ManObj(p, pGia2Abc[iReprGia]) );
            assert( Gia_ObjReprSelf(pGia, Abc_Lit2Var(iLitGia)) == Gia_ObjReprSelf(pGia, Abc_Lit2Var(iLitGia2)) );
            fCompl  = Abc_LitIsCompl(iLitGia) ^ Abc_LitIsCompl(iLitGia2);
            fCompl ^= Gia_ManObj(pGia, Abc_Lit2Var(iLitGia))->fPhase;
            fCompl ^= Gia_ManObj(pGia, Abc_Lit2Var(iLitGia2))->fPhase;
            pReprs[i] = Abc_Var2Lit( pGia2Abc[iReprGia], fCompl );
            if ( pGia2Abc[iReprGia] == 0 )
                nConsts++;
            else
                nReprs++;
        }
    }
    ABC_FREE( pGia2Abc );
    if ( fVerbose )
        printf( "Found %d const reprs and %d other reprs.\n", nConsts, nReprs );
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

  Synopsis    [Reduces root model with scorr.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManFraigSweep( Gia_Man_t * p, void * pPars )
{ 
    Gia_Man_t * pGia, * pNew, * pTemp;
    int * pReprs;
    assert( Gia_ManRegNum(p) == 0 );
    if ( p->pManTime == NULL )
    {
        Gia_ManFraigSweepPerform( p, pPars );
        pNew = Gia_ManEquivReduce( p, 1, 0, 0 );
        if ( pNew == NULL )
            return Gia_ManDup(p);
        return pNew;
    }
    if ( p->pAigExtra == NULL )
    {
        printf( "Timing manager is given but there is no GIA of boxes.\n" );
        return NULL;
    }
    // ordering AIG objects
    pNew = Gia_ManDupWithHierarchy( p, NULL );
    if ( pNew == NULL )
        return NULL;
    // find global equivalences
    pGia = Gia_ManDupWithBoxes( p, p->pAigExtra );
    Gia_ManFraigSweepPerform( pGia, pPars );
    // transfer equivalences
    pReprs = Gia_ManFraigSelectReprs( pNew, pGia, ((Dch_Pars_t *)pPars)->fVerbose );
    Gia_ManStop( pGia );
    // reduce AIG
    pNew = Gia_ManFraigReduceGia( pTemp = pNew, pReprs );
    Gia_ManStop( pTemp );
    ABC_FREE( pReprs );
    // order reduced AIG
    pNew->pManTime = p->pManTime;
    pNew = Gia_ManDupWithHierarchy( pTemp = pNew, NULL );
    pTemp->pManTime = NULL;
    Gia_ManStop( pTemp );
    // derive new AIG
    assert( pTemp->pManTime == NULL );
    pNew = Gia_ManFraigCreateGia( pTemp = pNew );
    assert( pNew->pManTime != NULL );
    Gia_ManStop( pTemp );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

