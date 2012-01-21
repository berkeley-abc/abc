/**CFile****************************************************************

  FileName    [saigSimExt.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [Extending simulation trace to contain ternary values.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: saigSimExt.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "saig.h"
#include "src/proof/ssw/ssw.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline int Saig_ManSimInfoNot( int Value )
{
    if ( Value == SAIG_ZER )
        return SAIG_ONE;
    if ( Value == SAIG_ONE )
        return SAIG_ZER;
    return SAIG_UND;
}

static inline int Saig_ManSimInfoAnd( int Value0, int Value1 )
{
    if ( Value0 == SAIG_ZER || Value1 == SAIG_ZER )
        return SAIG_ZER;
    if ( Value0 == SAIG_ONE && Value1 == SAIG_ONE )
        return SAIG_ONE;
    return SAIG_UND;
}

static inline int Saig_ManSimInfoGet( Vec_Ptr_t * vSimInfo, Aig_Obj_t * pObj, int iFrame )
{
    unsigned * pInfo = (unsigned *)Vec_PtrEntry( vSimInfo, Aig_ObjId(pObj) );
    return 3 & (pInfo[iFrame >> 4] >> ((iFrame & 15) << 1));
}

static inline void Saig_ManSimInfoSet( Vec_Ptr_t * vSimInfo, Aig_Obj_t * pObj, int iFrame, int Value )
{
    unsigned * pInfo = (unsigned *)Vec_PtrEntry( vSimInfo, Aig_ObjId(pObj) );
    assert( Value >= SAIG_ZER && Value <= SAIG_UND );
    Value ^= Saig_ManSimInfoGet( vSimInfo, pObj, iFrame );
    pInfo[iFrame >> 4] ^= (Value << ((iFrame & 15) << 1));
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs ternary simulation for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_ManExtendOneEval( Vec_Ptr_t * vSimInfo, Aig_Obj_t * pObj, int iFrame )
{
    int Value0, Value1, Value;
    Value0 = Saig_ManSimInfoGet( vSimInfo, Aig_ObjFanin0(pObj), iFrame );
    if ( Aig_ObjFaninC0(pObj) )
        Value0 = Saig_ManSimInfoNot( Value0 );
    if ( Aig_ObjIsPo(pObj) )
    {
        Saig_ManSimInfoSet( vSimInfo, pObj, iFrame, Value0 );
        return Value0;
    }
    assert( Aig_ObjIsNode(pObj) );
    Value1 = Saig_ManSimInfoGet( vSimInfo, Aig_ObjFanin1(pObj), iFrame );
    if ( Aig_ObjFaninC1(pObj) )
        Value1 = Saig_ManSimInfoNot( Value1 );
    Value = Saig_ManSimInfoAnd( Value0, Value1 );
    Saig_ManSimInfoSet( vSimInfo, pObj, iFrame, Value );
    return Value;
}

/**Function*************************************************************

  Synopsis    [Performs ternary simulation for one design.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_ManSimDataInit( Aig_Man_t * p, Abc_Cex_t * pCex, Vec_Ptr_t * vSimInfo, Vec_Int_t * vRes )
{
    Aig_Obj_t * pObj, * pObjLi, * pObjLo;
    int i, f, Entry, iBit = 0;
    Saig_ManForEachLo( p, pObj, i )
        Saig_ManSimInfoSet( vSimInfo, pObj, 0, Abc_InfoHasBit(pCex->pData, iBit++)?SAIG_ONE:SAIG_ZER );
    for ( f = 0; f <= pCex->iFrame; f++ )
    {
        Saig_ManSimInfoSet( vSimInfo, Aig_ManConst1(p), f, SAIG_ONE );
        Saig_ManForEachPi( p, pObj, i )
            Saig_ManSimInfoSet( vSimInfo, pObj, f, Abc_InfoHasBit(pCex->pData, iBit++)?SAIG_ONE:SAIG_ZER );
        if ( vRes )
        Vec_IntForEachEntry( vRes, Entry, i )
            Saig_ManSimInfoSet( vSimInfo, Aig_ManPi(p, Entry), f, SAIG_UND );
        Aig_ManForEachNode( p, pObj, i )
            Saig_ManExtendOneEval( vSimInfo, pObj, f );
        Aig_ManForEachPo( p, pObj, i )
            Saig_ManExtendOneEval( vSimInfo, pObj, f );
        if ( f == pCex->iFrame )
            break;
        Saig_ManForEachLiLo( p, pObjLi, pObjLo, i )
            Saig_ManSimInfoSet( vSimInfo, pObjLo, f+1, Saig_ManSimInfoGet(vSimInfo, pObjLi, f) );
    }
    // make sure the output of the property failed
    pObj = Aig_ManPo( p, pCex->iPo );
    return Saig_ManSimInfoGet( vSimInfo, pObj, pCex->iFrame );
}

/**Function*************************************************************

  Synopsis    [Tries to assign ternary value to one of the primary inputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_ManExtendOne( Aig_Man_t * p, Abc_Cex_t * pCex, Vec_Ptr_t * vSimInfo, 
    int iPi, int iFrame, Vec_Int_t * vUndo, Vec_Int_t * vVis, Vec_Int_t * vVis2 )
{
    Aig_Obj_t * pFanout, * pObj = Aig_ManPi(p, iPi);
    int i, k, f, iFanout, Value, Value2, Entry;
    // save original value
    Value = Saig_ManSimInfoGet( vSimInfo, pObj, iFrame );
    assert( Value == SAIG_ZER || Value == SAIG_ONE );
    Vec_IntPush( vUndo, Aig_ObjId(pObj) );
    Vec_IntPush( vUndo, iFrame );
    Vec_IntPush( vUndo, Value );
    // update original value
    Saig_ManSimInfoSet( vSimInfo, pObj, iFrame, SAIG_UND );
    // traverse
    Vec_IntClear( vVis );
    Vec_IntPush( vVis, Aig_ObjId(pObj) );
    for ( f = iFrame; f <= pCex->iFrame; f++ )
    {
        Vec_IntClear( vVis2 );
        Vec_IntForEachEntry( vVis, Entry, i )
        {
            pObj = Aig_ManObj( p, Entry );
            Aig_ObjForEachFanout( p, pObj, pFanout, iFanout, k )
            {
                assert( Aig_ObjId(pObj) < Aig_ObjId(pFanout) );
                Value = Saig_ManSimInfoGet( vSimInfo, pFanout, f );
                if ( Value == SAIG_UND )
                    continue;
                Value2 = Saig_ManExtendOneEval( vSimInfo, pFanout, f );
                if ( Value2 == Value )
                    continue;
                assert( Value2 == SAIG_UND );
//                assert( Vec_IntFind(vVis, Aig_ObjId(pFanout)) == -1 );
                if ( Aig_ObjIsNode(pFanout) )
                    Vec_IntPushOrder( vVis, Aig_ObjId(pFanout) );
                else if ( Saig_ObjIsLi(p, pFanout) )
                    Vec_IntPush( vVis2, Aig_ObjId(pFanout) );
                Vec_IntPush( vUndo, Aig_ObjId(pFanout) );
                Vec_IntPush( vUndo, f );
                Vec_IntPush( vUndo, Value );
            }
        }
        if ( Vec_IntSize(vVis2) == 0 )
            break;
        if ( f == pCex->iFrame )
            break;
        // transfer
        Vec_IntClear( vVis );
        Vec_IntForEachEntry( vVis2, Entry, i )
        {
            pObj = Aig_ManObj( p, Entry );
            assert( Saig_ObjIsLi(p, pObj) );
            pFanout = Saig_ObjLiToLo( p, pObj );
            Vec_IntPushOrder( vVis, Aig_ObjId(pFanout) );
            Value = Saig_ManSimInfoGet( vSimInfo, pObj, f );
            Saig_ManSimInfoSet( vSimInfo, pFanout, f+1, Value );
        }
    }
    // check the output
    pObj = Aig_ManPo( p, pCex->iPo );
    Value = Saig_ManSimInfoGet( vSimInfo, pObj, pCex->iFrame );
    assert( Value == SAIG_ONE || Value == SAIG_UND );
    return (int)(Value == SAIG_ONE);
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManExtendUndo( Aig_Man_t * p, Vec_Ptr_t * vSimInfo, Vec_Int_t * vUndo )
{
    Aig_Obj_t * pObj;
    int i, iFrame, Value;
    for ( i = 0; i < Vec_IntSize(vUndo); i += 3 )
    {
        pObj = Aig_ManObj( p, Vec_IntEntry(vUndo, i) );
        iFrame = Vec_IntEntry(vUndo, i+1);
        Value  = Vec_IntEntry(vUndo, i+2);
        assert( Saig_ManSimInfoGet(vSimInfo, pObj, iFrame) == SAIG_UND );
        Saig_ManSimInfoSet( vSimInfo, pObj, iFrame, Value );
    }
}

/**Function*************************************************************

  Synopsis    [Returns the array of PIs for flops that should not be absracted.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Saig_ManExtendCounterExample0( Aig_Man_t * p, int iFirstFlopPi, Abc_Cex_t * pCex, Vec_Ptr_t * vSimInfo, int fVerbose )
{
    Vec_Int_t * vRes, * vResInv, * vUndo, * vVis, * vVis2;
    int i, f, Value;
//    assert( Aig_ManRegNum(p) > 0 );
    assert( (unsigned *)Vec_PtrEntry(vSimInfo,1) - (unsigned *)Vec_PtrEntry(vSimInfo,0) >= Abc_BitWordNum(2*(pCex->iFrame+1)) );
    // start simulation data
    Value = Saig_ManSimDataInit( p, pCex, vSimInfo, NULL );
    assert( Value == SAIG_ONE );
    // select the result
    vRes = Vec_IntAlloc( 1000 );
    vResInv = Vec_IntAlloc( 1000 );
    vVis = Vec_IntAlloc( 1000 );
    vVis2 = Vec_IntAlloc( 1000 );
    vUndo = Vec_IntAlloc( 1000 );
    for ( i = iFirstFlopPi; i < Saig_ManPiNum(p); i++ )
    {
        Vec_IntClear( vUndo );
        for ( f = pCex->iFrame; f >= 0; f-- )
            if ( !Saig_ManExtendOne( p, pCex, vSimInfo, i, f, vUndo, vVis, vVis2 ) )
            {
                Saig_ManExtendUndo( p, vSimInfo, vUndo );
                break;
            }
        if ( f >= 0 )
            Vec_IntPush( vRes, i );
        else
            Vec_IntPush( vResInv, i );
    }
    Vec_IntFree( vVis );
    Vec_IntFree( vVis2 );
    Vec_IntFree( vUndo );
    // resimulate to make sure it is valid
    Value = Saig_ManSimDataInit( p, pCex, vSimInfo, vResInv );
    assert( Value == SAIG_ONE );
    Vec_IntFree( vResInv );
    return vRes;
}

/**Function*************************************************************

  Synopsis    [Returns the array of PIs for flops that should not be absracted.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Saig_ManExtendCounterExample1( Aig_Man_t * p, int iFirstFlopPi, Abc_Cex_t * pCex, Vec_Ptr_t * vSimInfo, int fVerbose )
{
    Vec_Int_t * vRes, * vResInv, * vUndo, * vVis, * vVis2;
    int i, f, Value;
//    assert( Aig_ManRegNum(p) > 0 );
    assert( (unsigned *)Vec_PtrEntry(vSimInfo,1) - (unsigned *)Vec_PtrEntry(vSimInfo,0) >= Abc_BitWordNum(2*(pCex->iFrame+1)) );
    // start simulation data
    Value = Saig_ManSimDataInit( p, pCex, vSimInfo, NULL );
    assert( Value == SAIG_ONE );
    // select the result
    vRes = Vec_IntAlloc( 1000 );
    vResInv = Vec_IntAlloc( 1000 );
    vVis = Vec_IntAlloc( 1000 );
    vVis2 = Vec_IntAlloc( 1000 );
    vUndo = Vec_IntAlloc( 1000 );
    for ( i = Saig_ManPiNum(p) - 1; i >= iFirstFlopPi; i-- )
    {
        Vec_IntClear( vUndo );
        for ( f = pCex->iFrame; f >= 0; f-- )
            if ( !Saig_ManExtendOne( p, pCex, vSimInfo, i, f, vUndo, vVis, vVis2 ) )
            {
                Saig_ManExtendUndo( p, vSimInfo, vUndo );
                break;
            }
        if ( f >= 0 )
            Vec_IntPush( vRes, i );
        else
            Vec_IntPush( vResInv, i );
    }
    Vec_IntFree( vVis );
    Vec_IntFree( vVis2 );
    Vec_IntFree( vUndo );
    // resimulate to make sure it is valid
    Value = Saig_ManSimDataInit( p, pCex, vSimInfo, vResInv );
    assert( Value == SAIG_ONE );
    Vec_IntFree( vResInv );
    return vRes;
}

/**Function*************************************************************

  Synopsis    [Returns the array of PIs for flops that should not be absracted.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Saig_ManExtendCounterExample2( Aig_Man_t * p, int iFirstFlopPi, Abc_Cex_t * pCex, Vec_Ptr_t * vSimInfo, int fVerbose )
{
    Vec_Int_t * vRes, * vResInv, * vUndo, * vVis, * vVis2;
    int i, f, Value;
//    assert( Aig_ManRegNum(p) > 0 );
    assert( (unsigned *)Vec_PtrEntry(vSimInfo,1) - (unsigned *)Vec_PtrEntry(vSimInfo,0) >= Abc_BitWordNum(2*(pCex->iFrame+1)) );
    // start simulation data
    Value = Saig_ManSimDataInit( p, pCex, vSimInfo, NULL );
    assert( Value == SAIG_ONE );
    // select the result
    vRes = Vec_IntAlloc( 1000 );
    vResInv = Vec_IntAlloc( 1000 );
    vVis = Vec_IntAlloc( 1000 );
    vVis2 = Vec_IntAlloc( 1000 );
    vUndo = Vec_IntAlloc( 1000 );
    for ( i = iFirstFlopPi; i < Saig_ManPiNum(p); i++ )
    {
        if ( i % 2 == 0 )
            continue;
        Vec_IntClear( vUndo );
        for ( f = pCex->iFrame; f >= 0; f-- )
            if ( !Saig_ManExtendOne( p, pCex, vSimInfo, i, f, vUndo, vVis, vVis2 ) )
            {
                Saig_ManExtendUndo( p, vSimInfo, vUndo );
                break;
            }
        if ( f >= 0 )
            Vec_IntPush( vRes, i );
        else
            Vec_IntPush( vResInv, i );
    }
    for ( i = iFirstFlopPi; i < Saig_ManPiNum(p); i++ )
    {
        if ( i % 2 == 1 )
            continue;
        Vec_IntClear( vUndo );
        for ( f = pCex->iFrame; f >= 0; f-- )
            if ( !Saig_ManExtendOne( p, pCex, vSimInfo, i, f, vUndo, vVis, vVis2 ) )
            {
                Saig_ManExtendUndo( p, vSimInfo, vUndo );
                break;
            }
        if ( f >= 0 )
            Vec_IntPush( vRes, i );
        else
            Vec_IntPush( vResInv, i );
    }
    Vec_IntFree( vVis );
    Vec_IntFree( vVis2 );
    Vec_IntFree( vUndo );
    // resimulate to make sure it is valid
    Value = Saig_ManSimDataInit( p, pCex, vSimInfo, vResInv );
    assert( Value == SAIG_ONE );
    Vec_IntFree( vResInv );
    return vRes;
}

/**Function*************************************************************

  Synopsis    [Returns the array of PIs for flops that should not be absracted.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Saig_ManExtendCounterExample3( Aig_Man_t * p, int iFirstFlopPi, Abc_Cex_t * pCex, Vec_Ptr_t * vSimInfo, int fVerbose )
{
    Vec_Int_t * vRes, * vResInv, * vUndo, * vVis, * vVis2;
    int i, f, Value;
//    assert( Aig_ManRegNum(p) > 0 );
    assert( (unsigned *)Vec_PtrEntry(vSimInfo,1) - (unsigned *)Vec_PtrEntry(vSimInfo,0) >= Abc_BitWordNum(2*(pCex->iFrame+1)) );
    // start simulation data
    Value = Saig_ManSimDataInit( p, pCex, vSimInfo, NULL );
    assert( Value == SAIG_ONE );
    // select the result
    vRes = Vec_IntAlloc( 1000 );
    vResInv = Vec_IntAlloc( 1000 );
    vVis = Vec_IntAlloc( 1000 );
    vVis2 = Vec_IntAlloc( 1000 );
    vUndo = Vec_IntAlloc( 1000 );
    for ( i = Saig_ManPiNum(p) - 1; i >= iFirstFlopPi; i-- )
    {
        if ( i % 2 == 0 )
            continue;
        Vec_IntClear( vUndo );
        for ( f = pCex->iFrame; f >= 0; f-- )
            if ( !Saig_ManExtendOne( p, pCex, vSimInfo, i, f, vUndo, vVis, vVis2 ) )
            {
                Saig_ManExtendUndo( p, vSimInfo, vUndo );
                break;
            }
        if ( f >= 0 )
            Vec_IntPush( vRes, i );
        else
            Vec_IntPush( vResInv, i );
    }
    for ( i = Saig_ManPiNum(p) - 1; i >= iFirstFlopPi; i-- )
    {
        if ( i % 2 == 1 )
            continue;
        Vec_IntClear( vUndo );
        for ( f = pCex->iFrame; f >= 0; f-- )
            if ( !Saig_ManExtendOne( p, pCex, vSimInfo, i, f, vUndo, vVis, vVis2 ) )
            {
                Saig_ManExtendUndo( p, vSimInfo, vUndo );
                break;
            }
        if ( f >= 0 )
            Vec_IntPush( vRes, i );
        else
            Vec_IntPush( vResInv, i );
    }
    Vec_IntFree( vVis );
    Vec_IntFree( vVis2 );
    Vec_IntFree( vUndo );
    // resimulate to make sure it is valid
    Value = Saig_ManSimDataInit( p, pCex, vSimInfo, vResInv );
    assert( Value == SAIG_ONE );
    Vec_IntFree( vResInv );
    return vRes;
}

/**Function*************************************************************

  Synopsis    [Returns the array of PIs for flops that should not be absracted.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Saig_ManExtendCounterExample( Aig_Man_t * p, int iFirstFlopPi, Abc_Cex_t * pCex, Vec_Ptr_t * vSimInfo, int fVerbose )
{
    Vec_Int_t * vRes0 = Saig_ManExtendCounterExample0( p, iFirstFlopPi, pCex, vSimInfo, fVerbose );
    Vec_Int_t * vRes1 = Saig_ManExtendCounterExample1( p, iFirstFlopPi, pCex, vSimInfo, fVerbose );
    Vec_Int_t * vRes2 = Saig_ManExtendCounterExample2( p, iFirstFlopPi, pCex, vSimInfo, fVerbose );
    Vec_Int_t * vRes3 = Saig_ManExtendCounterExample3( p, iFirstFlopPi, pCex, vSimInfo, fVerbose );
    Vec_Int_t * vRes  = vRes0;
//    if ( fVerbose ) 
        printf( "Removable flops: Order0 =%3d. Order1 =%3d. Order2 =%3d. Order3 =%3d.\n",
            Vec_IntSize(vRes0), Vec_IntSize(vRes1), Vec_IntSize(vRes2), Vec_IntSize(vRes3) );
    if ( Vec_IntSize(vRes1) <  Vec_IntSize(vRes) )
        vRes = vRes1;
    if ( Vec_IntSize(vRes2) <  Vec_IntSize(vRes) )
        vRes = vRes2;
    if ( Vec_IntSize(vRes3) <  Vec_IntSize(vRes) )
        vRes = vRes3;
    vRes = Vec_IntDup( vRes );
    Vec_IntFree( vRes0 );
    Vec_IntFree( vRes1 );
    Vec_IntFree( vRes2 );
    Vec_IntFree( vRes3 );
    return vRes;
}

/**Function*************************************************************

  Synopsis    [Returns the array of PIs for flops that should not be absracted.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Saig_ManExtendCounterExampleTest( Aig_Man_t * p, int iFirstFlopPi, Abc_Cex_t * pCex, int fTryFour, int fVerbose )
{
    Vec_Int_t * vRes;
    Vec_Ptr_t * vSimInfo;
    int clk;
    if ( Saig_ManPiNum(p) != pCex->nPis )
    {
        printf( "Saig_ManExtendCounterExampleTest(): The PI count of AIG (%d) does not match that of cex (%d).\n", 
            Aig_ManPiNum(p), pCex->nPis );
        return NULL;
    }
    Aig_ManFanoutStart( p );
    vSimInfo = Vec_PtrAllocSimInfo( Aig_ManObjNumMax(p), Abc_BitWordNum(2*(pCex->iFrame+1)) );
    Vec_PtrCleanSimInfo( vSimInfo, 0, Abc_BitWordNum(2*(pCex->iFrame+1)) );

clk = clock();
    if ( fTryFour )
        vRes = Saig_ManExtendCounterExample( p, iFirstFlopPi, pCex, vSimInfo, fVerbose );
    else
        vRes = Saig_ManExtendCounterExample0( p, iFirstFlopPi, pCex, vSimInfo, fVerbose );
    if ( fVerbose )
    {
        printf( "Total new PIs = %3d. Non-removable PIs = %3d.  ", Saig_ManPiNum(p)-iFirstFlopPi, Vec_IntSize(vRes) );
ABC_PRT( "Time", clock() - clk );
    }
    Vec_PtrFree( vSimInfo );
    Aig_ManFanoutStop( p );
    return vRes;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

