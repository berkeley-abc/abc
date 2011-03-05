/**CFile****************************************************************

  FileName    [saigSimExt2.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [Extending simulation trace to contain ternary values.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: saigSimExt2.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "saig.h"
#include "ssw.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define SAIG_ZER_NEW 0   // 0 not visited
#define SAIG_ONE_NEW 1   // 1 not visited
#define SAIG_ZER_OLD 2   // 0 visited
#define SAIG_ONE_OLD 3   // 1 visited

static inline int Saig_ManSimInfo2IsOld( int Value )
{
    return Value == SAIG_ZER_OLD || Value == SAIG_ONE_OLD;
}

static inline int Saig_ManSimInfo2SetOld( int Value )
{
    if ( Value == SAIG_ZER_NEW )
        return SAIG_ZER_OLD;
    if ( Value == SAIG_ONE_NEW )
        return SAIG_ONE_OLD;
    assert( 0 );
    return 0;
}

static inline int Saig_ManSimInfo2Not( int Value )
{
    if ( Value == SAIG_ZER_NEW )
        return SAIG_ONE_NEW;
    if ( Value == SAIG_ONE_NEW )
        return SAIG_ZER_NEW;
    assert( 0 );
    return 0;
}

static inline int Saig_ManSimInfo2And( int Value0, int Value1 )
{
    if ( Value0 == SAIG_ZER_NEW || Value1 == SAIG_ZER_NEW )
        return SAIG_ZER_NEW;
    if ( Value0 == SAIG_ONE_NEW && Value1 == SAIG_ONE_NEW )
        return SAIG_ONE_NEW;
    assert( 0 );
    return 0;
}

static inline int Saig_ManSimInfo2Get( Vec_Ptr_t * vSimInfo, Aig_Obj_t * pObj, int iFrame )
{
    unsigned * pInfo = (unsigned *)Vec_PtrEntry( vSimInfo, Aig_ObjId(pObj) );
    return 3 & (pInfo[iFrame >> 4] >> ((iFrame & 15) << 1));
}

static inline void Saig_ManSimInfo2Set( Vec_Ptr_t * vSimInfo, Aig_Obj_t * pObj, int iFrame, int Value )
{
    unsigned * pInfo = (unsigned *)Vec_PtrEntry( vSimInfo, Aig_ObjId(pObj) );
    Value ^= Saig_ManSimInfo2Get( vSimInfo, pObj, iFrame );
    pInfo[iFrame >> 4] ^= (Value << ((iFrame & 15) << 1));
}

// performs ternary simulation
extern int Saig_ManSimDataInit( Aig_Man_t * p, Abc_Cex_t * pCex, Vec_Ptr_t * vSimInfo, Vec_Int_t * vRes );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs ternary simulation for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_ManExtendOneEval2( Vec_Ptr_t * vSimInfo, Aig_Obj_t * pObj, int iFrame )
{
    int Value0, Value1, Value;
    Value0 = Saig_ManSimInfo2Get( vSimInfo, Aig_ObjFanin0(pObj), iFrame );
    if ( Aig_ObjFaninC0(pObj) )
        Value0 = Saig_ManSimInfo2Not( Value0 );
    if ( Aig_ObjIsPo(pObj) )
    {
        Saig_ManSimInfo2Set( vSimInfo, pObj, iFrame, Value0 );
        return Value0;
    }
    assert( Aig_ObjIsNode(pObj) );
    Value1 = Saig_ManSimInfo2Get( vSimInfo, Aig_ObjFanin1(pObj), iFrame );
    if ( Aig_ObjFaninC1(pObj) )
        Value1 = Saig_ManSimInfo2Not( Value1 );
    Value = Saig_ManSimInfo2And( Value0, Value1 );
    Saig_ManSimInfo2Set( vSimInfo, pObj, iFrame, Value );
    return Value;
}

/**Function*************************************************************

  Synopsis    [Performs sensitization analysis for one design.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_ManSimDataInit2( Aig_Man_t * p, Abc_Cex_t * pCex, Vec_Ptr_t * vSimInfo )
{
    Aig_Obj_t * pObj, * pObjLi, * pObjLo;
    int i, f, iBit = 0;
    Saig_ManForEachLo( p, pObj, i )
        Saig_ManSimInfo2Set( vSimInfo, pObj, 0, Aig_InfoHasBit(pCex->pData, iBit++)?SAIG_ONE_NEW:SAIG_ZER_NEW );
    for ( f = 0; f <= pCex->iFrame; f++ )
    {
        Saig_ManSimInfo2Set( vSimInfo, Aig_ManConst1(p), f, SAIG_ONE_NEW );
        Saig_ManForEachPi( p, pObj, i )
            Saig_ManSimInfo2Set( vSimInfo, pObj, f, Aig_InfoHasBit(pCex->pData, iBit++)?SAIG_ONE_NEW:SAIG_ZER_NEW );
        Aig_ManForEachNode( p, pObj, i )
            Saig_ManExtendOneEval2( vSimInfo, pObj, f );
        Aig_ManForEachPo( p, pObj, i )
            Saig_ManExtendOneEval2( vSimInfo, pObj, f );
        if ( f == pCex->iFrame )
            break;
        Saig_ManForEachLiLo( p, pObjLi, pObjLo, i )
            Saig_ManSimInfo2Set( vSimInfo, pObjLo, f+1, Saig_ManSimInfo2Get(vSimInfo, pObjLi, f) );
    }
    // make sure the output of the property failed
    pObj = Aig_ManPo( p, pCex->iPo );
    return Saig_ManSimInfo2Get( vSimInfo, pObj, pCex->iFrame );
}

/**Function*************************************************************

  Synopsis    [Performs recursive sensetization analysis.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManExplorePaths_rec( Aig_Man_t * p, Aig_Obj_t * pObj, int f, Vec_Ptr_t * vSimInfo )
{
    int Value = Saig_ManSimInfo2Get( vSimInfo, pObj, f );
    if ( Saig_ManSimInfo2IsOld( Value ) )
        return;
    Saig_ManSimInfo2Set( vSimInfo, pObj, f, Saig_ManSimInfo2SetOld(Value) );
    if ( (Aig_ObjIsPi(pObj) && f == 0) || Saig_ObjIsPi(p, pObj) || Aig_ObjIsConst1(pObj) )
        return;
    if ( Saig_ObjIsLo( p, pObj ) )
    {
        assert( f > 0 );
        Saig_ManExplorePaths_rec( p, Saig_ObjLoToLi(p, pObj), f-1, vSimInfo );
        return;
    }
    if ( Aig_ObjIsPo(pObj) )
    {
        Saig_ManExplorePaths_rec( p, Aig_ObjFanin0(pObj), f, vSimInfo );
        return;
    }
    assert( Aig_ObjIsNode(pObj) );
    if ( Value == SAIG_ZER_OLD )
        Saig_ManExplorePaths_rec( p, Aig_ObjFanin0(pObj), f, vSimInfo );
    else
    {
        Saig_ManExplorePaths_rec( p, Aig_ObjFanin0(pObj), f, vSimInfo );
        Saig_ManExplorePaths_rec( p, Aig_ObjFanin1(pObj), f, vSimInfo );
    }
}

/**Function*************************************************************

  Synopsis    [Returns the array of PIs for flops that should not be absracted.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Saig_ManProcessCex( Aig_Man_t * p, int iFirstFlopPi, Abc_Cex_t * pCex, Vec_Ptr_t * vSimInfo, int fVerbose )
{
    Vec_Int_t * vRes, * vResInv;
    int i, f, Value;
//    assert( Aig_ManRegNum(p) > 0 );
    assert( (unsigned *)Vec_PtrEntry(vSimInfo,1) - (unsigned *)Vec_PtrEntry(vSimInfo,0) >= Aig_BitWordNum(2*(pCex->iFrame+1)) );
    // start simulation data
    Value = Saig_ManSimDataInit2( p, pCex, vSimInfo );
    assert( Value == SAIG_ONE_NEW );
    // recursively compute justification
    Saig_ManExplorePaths_rec( p, Aig_ManPo(p, pCex->iPo), pCex->iFrame, vSimInfo );
    // select the result
    vRes = Vec_IntAlloc( 1000 );
    vResInv = Vec_IntAlloc( 1000 );
    for ( i = iFirstFlopPi; i < Saig_ManPiNum(p); i++ )
    {
        for ( f = pCex->iFrame; f >= 0; f-- )
        {
            Value = Saig_ManSimInfo2Get( vSimInfo, Aig_ManPi(p, i), f );
            if ( Saig_ManSimInfo2IsOld( Value ) )
                break;
        }
        if ( f >= 0 )
            Vec_IntPush( vRes, i );
        else
            Vec_IntPush( vResInv, i );
    }
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
Vec_Int_t * Saig_ManExtendCounterExampleTest2( Aig_Man_t * p, int iFirstFlopPi, Abc_Cex_t * pCex, int fVerbose )
{
    Vec_Int_t * vRes;
    Vec_Ptr_t * vSimInfo;
    int clk;
    if ( Saig_ManPiNum(p) != pCex->nPis )
    {
        printf( "Saig_ManExtendCounterExampleTest2(): The PI count of AIG (%d) does not match that of cex (%d).\n", 
            Aig_ManPiNum(p), pCex->nPis );
        return NULL;
    }
    Aig_ManFanoutStart( p );
    vSimInfo = Vec_PtrAllocSimInfo( Aig_ManObjNumMax(p), Aig_BitWordNum(2*(pCex->iFrame+1)) );
    Vec_PtrCleanSimInfo( vSimInfo, 0, Aig_BitWordNum(2*(pCex->iFrame+1)) );

clk = clock();
    vRes = Saig_ManProcessCex( p, iFirstFlopPi, pCex, vSimInfo, fVerbose );
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

