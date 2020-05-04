/**CFile****************************************************************

  FileName    [giaResub.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Resubstitution.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaResub.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "misc/vec/vecWec.h"
#include "misc/vec/vecQue.h"
#include "misc/vec/vecHsh.h"
#include "misc/util/utilTruth.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computes MFFCs of all qualifying nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ObjCheckMffc_rec( Gia_Man_t * p,Gia_Obj_t * pObj, int Limit, Vec_Int_t * vNodes )
{
    int iFanin;
    if ( Gia_ObjIsCi(pObj) )
        return 1;
    assert( Gia_ObjIsAnd(pObj) );
    iFanin = Gia_ObjFaninId0p(p, pObj);
    Vec_IntPush( vNodes, iFanin );
    if ( !Gia_ObjRefDecId(p, iFanin) && (Vec_IntSize(vNodes) > Limit || !Gia_ObjCheckMffc_rec(p, Gia_ObjFanin0(pObj), Limit, vNodes)) )
        return 0;
    iFanin = Gia_ObjFaninId1p(p, pObj);
    Vec_IntPush( vNodes, iFanin );
    if ( !Gia_ObjRefDecId(p, iFanin) && (Vec_IntSize(vNodes) > Limit || !Gia_ObjCheckMffc_rec(p, Gia_ObjFanin1(pObj), Limit, vNodes)) )
        return 0;
    if ( !Gia_ObjIsMux(p, pObj) )
        return 1;
    iFanin = Gia_ObjFaninId2p(p, pObj);
    Vec_IntPush( vNodes, iFanin );
    if ( !Gia_ObjRefDecId(p, iFanin) && (Vec_IntSize(vNodes) > Limit || !Gia_ObjCheckMffc_rec(p, Gia_ObjFanin2(p, pObj), Limit, vNodes)) )
        return 0;
    return 1;
}
static inline int Gia_ObjCheckMffc( Gia_Man_t * p, Gia_Obj_t * pRoot, int Limit, Vec_Int_t * vNodes, Vec_Int_t * vLeaves, Vec_Int_t * vInners )
{
    int RetValue, iObj, i;
    Vec_IntClear( vNodes );
    RetValue = Gia_ObjCheckMffc_rec( p, pRoot, Limit, vNodes );
    if ( RetValue )
    {
        Vec_IntClear( vLeaves );
        Vec_IntClear( vInners );
        Vec_IntSort( vNodes, 0 );
        Vec_IntForEachEntry( vNodes, iObj, i )
            if ( Gia_ObjRefNumId(p, iObj) > 0 || Gia_ObjIsCi(Gia_ManObj(p, iObj)) )
            {
                if ( !Vec_IntSize(vLeaves) || Vec_IntEntryLast(vLeaves) != iObj )
                    Vec_IntPush( vLeaves, iObj );
            }
            else
            {
                if ( !Vec_IntSize(vInners) || Vec_IntEntryLast(vInners) != iObj )
                    Vec_IntPush( vInners, iObj );
            }
        Vec_IntPush( vInners, Gia_ObjId(p, pRoot) );
    }
    Vec_IntForEachEntry( vNodes, iObj, i )
        Gia_ObjRefIncId( p, iObj );
    return RetValue;
}
Vec_Wec_t * Gia_ManComputeMffcs( Gia_Man_t * p, int LimitMin, int LimitMax, int SuppMax, int RatioBest )
{
    Gia_Obj_t * pObj;
    Vec_Wec_t * vMffcs;
    Vec_Int_t * vNodes, * vLeaves, * vInners, * vMffc;
    int i, iPivot;
    assert( p->pMuxes );
    vNodes  = Vec_IntAlloc( 2 * LimitMax );
    vLeaves = Vec_IntAlloc( 2 * LimitMax );
    vInners = Vec_IntAlloc( 2 * LimitMax );
    vMffcs  = Vec_WecAlloc( 1000 );
    Gia_ManCreateRefs( p );
    Gia_ManForEachAnd( p, pObj, i )
    {
        if ( !Gia_ObjRefNum(p, pObj) )
            continue;
        if ( !Gia_ObjCheckMffc(p, pObj, LimitMax, vNodes, vLeaves, vInners) )
            continue;
        if ( Vec_IntSize(vInners) < LimitMin )
            continue;
        if ( Vec_IntSize(vLeaves) > SuppMax )
            continue;
        // improve cut
        // collect cut
        vMffc = Vec_WecPushLevel( vMffcs );
        Vec_IntGrow( vMffc, Vec_IntSize(vLeaves) + Vec_IntSize(vInners) + 20 );
        Vec_IntPush( vMffc, i );
        Vec_IntPush( vMffc, Vec_IntSize(vLeaves) );
        Vec_IntPush( vMffc, Vec_IntSize(vInners) );
        Vec_IntAppend( vMffc, vLeaves );
//        Vec_IntAppend( vMffc, vInners );
        // add last entry equal to the ratio
        Vec_IntPush( vMffc, 1000 * Vec_IntSize(vInners) / Vec_IntSize(vLeaves) );
    }
    Vec_IntFree( vNodes );
    Vec_IntFree( vLeaves );
    Vec_IntFree( vInners );
    // sort MFFCs by their inner/leaf ratio
    Vec_WecSortByLastInt( vMffcs, 1 );
    Vec_WecForEachLevel( vMffcs, vMffc, i )
        Vec_IntPop( vMffc );
    // remove those whose ratio is not good
    iPivot = RatioBest * Vec_WecSize(vMffcs) / 100;
    Vec_WecForEachLevelStart( vMffcs, vMffc, i, iPivot )
        Vec_IntErase( vMffc );
    assert( iPivot <= Vec_WecSize(vMffcs) );
    Vec_WecShrink( vMffcs, iPivot );
    return vMffcs;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManPrintDivStats( Gia_Man_t * p, Vec_Wec_t * vMffcs, Vec_Wec_t * vPivots ) 
{
    int fVerbose = 0;
    Vec_Int_t * vMffc;
    int i, nDivs, nDivsAll = 0, nDivs0 = 0;
    Vec_WecForEachLevel( vMffcs, vMffc, i )
    {
        nDivs = Vec_IntSize(vMffc) - 3 - Vec_IntEntry(vMffc, 1) - Vec_IntEntry(vMffc, 2);
        nDivs0 += (nDivs == 0);
        nDivsAll += nDivs;
        if ( !fVerbose )
            continue;
        printf( "%6d : ",      Vec_IntEntry(vMffc, 0) );
        printf( "Leaf =%3d  ", Vec_IntEntry(vMffc, 1) );
        printf( "Mffc =%4d  ", Vec_IntEntry(vMffc, 2) );
        printf( "Divs =%4d  ", nDivs );
        printf( "\n" );
    }
    printf( "Collected %d (%.1f %%) MFFCs and %d (%.1f %%) have no divisors (div ave for others is %.2f).\n", 
        Vec_WecSize(vMffcs), 100.0 * Vec_WecSize(vMffcs) / Gia_ManAndNum(p), 
        nDivs0, 100.0 * nDivs0 / Gia_ManAndNum(p), 
        1.0*nDivsAll/Abc_MaxInt(1, Vec_WecSize(vMffcs) - nDivs0) );
    printf( "Using %.2f MB for MFFCs and %.2f MB for pivots.   ", 
        Vec_WecMemory(vMffcs)/(1<<20), Vec_WecMemory(vPivots)/(1<<20) );
}

/**Function*************************************************************

  Synopsis    [Compute divisors and Boolean functions for the nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManAddDivisors( Gia_Man_t * p, Vec_Wec_t * vMffcs )
{
    Vec_Wec_t * vPivots;
    Vec_Int_t * vMffc, * vPivot, * vPivot0, * vPivot1;
    Vec_Int_t * vCommon, * vCommon2, * vMap;
    Gia_Obj_t * pObj;
    int i, k, iObj, iPivot, iMffc;
//abctime clkStart = Abc_Clock();
    // initialize pivots (mapping of nodes into MFFCs whose leaves they are)
    vMap = Vec_IntStartFull( Gia_ManObjNum(p) );
    vPivots = Vec_WecStart( Gia_ManObjNum(p) );
    Vec_WecForEachLevel( vMffcs, vMffc, i )
    {
        assert( Vec_IntSize(vMffc) == 3 + Vec_IntEntry(vMffc, 1) );
        iPivot = Vec_IntEntry( vMffc, 0 );
        Vec_IntWriteEntry( vMap, iPivot, i );
        // iterate through the MFFC leaves
        Vec_IntForEachEntryStart( vMffc, iObj, k, 3 )
        {
            vPivot = Vec_WecEntry( vPivots, iObj );
            if ( Vec_IntSize(vPivot) == 0 )
                Vec_IntGrow(vPivot, 4);
            Vec_IntPush( vPivot, iPivot );            
        }
    }
    Vec_WecForEachLevel( vPivots, vPivot, i )
        Vec_IntSort( vPivot, 0 );
    // create pivots for internal nodes while growing MFFCs
    vCommon = Vec_IntAlloc( 100 );
    vCommon2 = Vec_IntAlloc( 100 );
    Gia_ManForEachAnd( p, pObj, i )
    {
        // find commont pivots
        // the slow down happens because some PIs have very large sets of pivots
        vPivot0 = Vec_WecEntry( vPivots, Gia_ObjFaninId0(pObj, i) );
        vPivot1 = Vec_WecEntry( vPivots, Gia_ObjFaninId1(pObj, i) );
        Vec_IntTwoFindCommon( vPivot0, vPivot1, vCommon );
        if ( Gia_ObjIsMuxId(p, i) )
        {
            vPivot = Vec_WecEntry( vPivots, Gia_ObjFaninId2(p, i) );
            Vec_IntTwoFindCommon( vPivot, vCommon, vCommon2 );
            ABC_SWAP( Vec_Int_t *, vCommon, vCommon2 );
        }
        if ( Vec_IntSize(vCommon) == 0 )
            continue;
        // add new pivots (this trick increased memory used in vPivots)
        vPivot = Vec_WecEntry( vPivots, i );
        Vec_IntTwoMerge2( vPivot, vCommon, vCommon2 );
        ABC_SWAP( Vec_Int_t, *vPivot, *vCommon2 );
        // grow MFFCs
        Vec_IntForEachEntry( vCommon, iObj, k )
        {
            iMffc = Vec_IntEntry( vMap, iObj );
            assert( iMffc != -1 );
            vMffc = Vec_WecEntry( vMffcs, iMffc );
            Vec_IntPush( vMffc, i );
        }
    }
//Abc_PrintTime( 1, "Time", Abc_Clock() - clkStart );
    Vec_IntFree( vCommon );
    Vec_IntFree( vCommon2 );
    Vec_IntFree( vMap );
    Gia_ManPrintDivStats( p, vMffcs, vPivots );
    Vec_WecFree( vPivots );
    // returns the modified array of MFFCs
}
void Gia_ManResubTest( Gia_Man_t * p )
{
    Vec_Wec_t * vMffcs;
    Gia_Man_t * pNew = Gia_ManDupMuxes( p, 2 );
abctime clkStart = Abc_Clock();
    vMffcs = Gia_ManComputeMffcs( pNew, 4, 100, 8, 100 );
    Gia_ManAddDivisors( pNew, vMffcs );
    Vec_WecFree( vMffcs );
Abc_PrintTime( 1, "Time", Abc_Clock() - clkStart );
    Gia_ManStop( pNew );
}





/**Function*************************************************************

  Synopsis    [Resubstitution data-structure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
typedef struct Gia_ResbMan_t_ Gia_ResbMan_t;
struct Gia_ResbMan_t_
{
    int         nWords;
    Vec_Ptr_t * vDivs;
    Vec_Int_t * vGates;
    Vec_Int_t * vUnateLits[2];
    Vec_Int_t * vNotUnateVars[2];
    Vec_Int_t * vUnatePairs[2];
    Vec_Int_t * vBinateVars;
    Vec_Int_t * vUnateLitsW[2];
    Vec_Int_t * vUnatePairsW[2];
    word *      pDivA;
    word *      pDivB;
};
Gia_ResbMan_t * Gia_ResbAlloc( Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vGates )
{
    Gia_ResbMan_t * p   = ABC_CALLOC( Gia_ResbMan_t, 1 );
    p->nWords           = nWords;
    p->vDivs            = vDivs;
    p->vGates           = vGates;
    p->vUnateLits[0]    = Vec_IntAlloc( 100 );
    p->vUnateLits[1]    = Vec_IntAlloc( 100 );
    p->vNotUnateVars[0] = Vec_IntAlloc( 100 );
    p->vNotUnateVars[1] = Vec_IntAlloc( 100 );
    p->vUnatePairs[0]   = Vec_IntAlloc( 100 );
    p->vUnatePairs[1]   = Vec_IntAlloc( 100 );
    p->vUnateLitsW[0]   = Vec_IntAlloc( 100 );
    p->vUnateLitsW[1]   = Vec_IntAlloc( 100 );
    p->vUnatePairsW[0]  = Vec_IntAlloc( 100 );
    p->vUnatePairsW[1]  = Vec_IntAlloc( 100 );
    p->vBinateVars      = Vec_IntAlloc( 100 );
    p->pDivA            = ABC_CALLOC( word, nWords );
    p->pDivB            = ABC_CALLOC( word, nWords );
    return p;
}
void Gia_ResbReset( Gia_ResbMan_t * p )
{
    Vec_IntClear( p->vUnateLits[0]    );
    Vec_IntClear( p->vUnateLits[1]    );
    Vec_IntClear( p->vNotUnateVars[0] );
    Vec_IntClear( p->vNotUnateVars[1] );
    Vec_IntClear( p->vUnatePairs[0]   );
    Vec_IntClear( p->vUnatePairs[1]   );
    Vec_IntClear( p->vUnateLitsW[0]   );
    Vec_IntClear( p->vUnateLitsW[1]   );
    Vec_IntClear( p->vUnatePairsW[0]  );
    Vec_IntClear( p->vUnatePairsW[1]  );
    Vec_IntClear( p->vBinateVars      );
}
void Gia_ResbFree( Gia_ResbMan_t * p )
{
    Vec_IntFree( p->vUnateLits[0]    );
    Vec_IntFree( p->vUnateLits[1]    );
    Vec_IntFree( p->vNotUnateVars[0] );
    Vec_IntFree( p->vNotUnateVars[1] );
    Vec_IntFree( p->vUnatePairs[0]   );
    Vec_IntFree( p->vUnatePairs[1]   );
    Vec_IntFree( p->vUnateLitsW[0]   );
    Vec_IntFree( p->vUnateLitsW[1]   );
    Vec_IntFree( p->vUnatePairsW[0]  );
    Vec_IntFree( p->vUnatePairsW[1]  );
    Vec_IntFree( p->vBinateVars      );
    ABC_FREE( p->pDivA );
    ABC_FREE( p->pDivB );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Verify resubstitution.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManResubVerify( Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vGates, int iTopLit )
{
    int i, iLit0, iLit1, RetValue, nDivs = Vec_PtrSize(vDivs);
    word * pOffSet = (word *)Vec_PtrEntry( vDivs, 0 );
    word * pOnSet  = (word *)Vec_PtrEntry( vDivs, 1 );
    word * pDivRes; 
    Vec_Wrd_t * vSims = NULL;
    if ( iTopLit <= -1 )
        return -1;
    if ( iTopLit == 0 )
        return Abc_TtIsConst0( pOnSet, nWords );
    if ( iTopLit == 1 )
        return Abc_TtIsConst0( pOffSet, nWords );
    if ( Abc_Lit2Var(iTopLit) < nDivs )
    {
        assert( Vec_IntSize(vGates) == 0 );
        pDivRes = (word *)Vec_PtrEntry( vDivs, Abc_Lit2Var(iTopLit) );
    }
    else
    {
        assert( Vec_IntSize(vGates) > 0 );
        assert( Vec_IntSize(vGates) % 2 == 0 );
        assert( Abc_Lit2Var(iTopLit)-nDivs == Vec_IntSize(vGates)/2-1 );
        vSims = Vec_WrdStart( nWords * Vec_IntSize(vGates)/2 );
        Vec_IntForEachEntryDouble( vGates, iLit0, iLit1, i )
        {
            int iVar0 = Abc_Lit2Var(iLit0);
            int iVar1 = Abc_Lit2Var(iLit1);
            word * pDiv0 = iVar0 < nDivs ? (word *)Vec_PtrEntry(vDivs, iVar0) : Vec_WrdEntryP(vSims, nWords*(nDivs - iVar0));
            word * pDiv1 = iVar1 < nDivs ? (word *)Vec_PtrEntry(vDivs, iVar1) : Vec_WrdEntryP(vSims, nWords*(nDivs - iVar1));
            word * pDiv  = Vec_WrdEntryP(vSims, nWords*i/2);
            if ( iVar0 < iVar1 )
                Abc_TtAndCompl( pDiv, pDiv0, Abc_LitIsCompl(iLit0), pDiv1, Abc_LitIsCompl(iLit1), nWords );
            else if ( iVar0 > iVar1 )
            {
                assert( !Abc_LitIsCompl(iLit0) );
                assert( !Abc_LitIsCompl(iLit1) );
                Abc_TtXor( pDiv, pDiv0, pDiv1, nWords, 0 );
            }
            else assert( 0 );
        }
        pDivRes = Vec_WrdEntryP( vSims, nWords*(Vec_IntSize(vGates)/2-1) );
    }
    if ( Abc_LitIsCompl(iTopLit) )
        RetValue = !Abc_TtIntersectOne(pOnSet,  0, pDivRes, 0, nWords) && !Abc_TtIntersectOne(pOffSet, 0, pDivRes, 1, nWords);
    else
        RetValue = !Abc_TtIntersectOne(pOffSet, 0, pDivRes, 0, nWords) && !Abc_TtIntersectOne(pOnSet,  0, pDivRes, 1, nWords);
    Vec_WrdFreeP( &vSims );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Construct AIG manager from gates.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManGetVar( Gia_Man_t * pNew, Vec_Int_t * vUsed, int iVar )
{
    if ( Vec_IntEntry(vUsed, iVar) == -1 )
        Vec_IntWriteEntry( vUsed, iVar, Gia_ManAppendCi(pNew) );
    return Vec_IntEntry(vUsed, iVar);
}
Gia_Man_t * Gia_ManConstructFromGates( int nVars, Vec_Int_t * vGates, int iTopLit )
{
    int i, iLit0, iLit1, iLitRes;
    Gia_Man_t * pNew = Gia_ManStart( 100 );
    pNew->pName = Abc_UtilStrsav( "resub" );
    assert( iTopLit >= 0 );
    if ( iTopLit == 0 || iTopLit == 1 )
        iLitRes = 0;
    else if ( Abc_Lit2Var(iTopLit) < nVars )
    {
        assert( Vec_IntSize(vGates) == 0 );
        iLitRes = Gia_ManAppendCi(pNew);
    }
    else
    {
        Vec_Int_t * vUsed = Vec_IntStartFull( nVars );
        Vec_Int_t * vCopy = Vec_IntAlloc( Vec_IntSize(vGates)/2 );
        assert( Vec_IntSize(vGates) > 0 );
        assert( Vec_IntSize(vGates) % 2 == 0 );
        assert( Abc_Lit2Var(iTopLit)-nVars == Vec_IntSize(vGates)/2-1 );
        Vec_IntForEachEntryDouble( vGates, iLit0, iLit1, i )
        {
            int iVar0 = Abc_Lit2Var(iLit0);
            int iVar1 = Abc_Lit2Var(iLit1);
            int iRes0 = iVar0 < nVars ? Gia_ManGetVar(pNew, vUsed, iVar0) : Vec_IntEntry(vCopy, nVars - iVar0);
            int iRes1 = iVar1 < nVars ? Gia_ManGetVar(pNew, vUsed, iVar1) : Vec_IntEntry(vCopy, nVars - iVar1);
            if ( iVar0 < iVar1 )
                iLitRes = Gia_ManAppendAnd( pNew, Abc_LitNotCond(iRes0, Abc_LitIsCompl(iLit0)), Abc_LitNotCond(iRes1, Abc_LitIsCompl(iLit1)) );
            else if ( iVar0 > iVar1 )
            {
                assert( !Abc_LitIsCompl(iLit0) );
                assert( !Abc_LitIsCompl(iLit1) );
                iLitRes = Gia_ManAppendXor( pNew, Abc_LitNotCond(iRes0, Abc_LitIsCompl(iLit0)), Abc_LitNotCond(iRes1, Abc_LitIsCompl(iLit1)) );
            }
            else assert( 0 );
            Vec_IntPush( vCopy, iLitRes );
        }
        assert( Vec_IntSize(vCopy) == Vec_IntSize(vGates)/2 );
        iLitRes = Vec_IntEntry( vCopy, Vec_IntSize(vGates)/2-1 );
        Vec_IntFree( vUsed );
        Vec_IntFree( vCopy );
    }
    Gia_ManAppendCo( pNew, Abc_LitNotCond(iLitRes, Abc_LitIsCompl(iTopLit)) );
    return pNew;
}


/**Function*************************************************************

  Synopsis    [Perform resubstitution.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Gia_ManFindFirstCommonLit( Vec_Int_t * vArr1, Vec_Int_t * vArr2 )
{
    int * pBeg1 = vArr1->pArray;
    int * pBeg2 = vArr2->pArray;
    int * pEnd1 = vArr1->pArray + vArr1->nSize;
    int * pEnd2 = vArr2->pArray + vArr2->nSize;
    int * pStart1 = vArr1->pArray;
    int * pStart2 = vArr2->pArray;
    int nRemoved = 0;
    while ( pBeg1 < pEnd1 && pBeg2 < pEnd2 )
    {
        if ( Abc_Lit2Var(*pBeg1) == Abc_Lit2Var(*pBeg2) )
        { 
            if ( *pBeg1 != *pBeg2 ) 
                return *pBeg1; 
            else
                pBeg1++, pBeg2++;
            nRemoved++;
        }
        else if ( *pBeg1 < *pBeg2 )
            *pStart1++ = *pBeg1++;
        else 
            *pStart2++ = *pBeg2++;
    }
    while ( pBeg1 < pEnd1 )
        *pStart1++ = *pBeg1++;
    while ( pBeg2 < pEnd2 )
        *pStart2++ = *pBeg2++;
    Vec_IntShrink( vArr1, pStart1 - vArr1->pArray );
    Vec_IntShrink( vArr2, pStart2 - vArr2->pArray );
    printf( "Removed %d duplicated entries.  Array1 = %d.  Array2 = %d.\n", nRemoved, Vec_IntSize(vArr1), Vec_IntSize(vArr2) );
    return -1;
}

void Gia_ManFindOneUnateInt( word * pOffSet, word * pOnSet, Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnateLits, Vec_Int_t * vNotUnateVars )
{
    word * pDiv; int i;
    Vec_IntClear( vUnateLits );
    Vec_IntClear( vNotUnateVars );
    Vec_PtrForEachEntryStart( word *, vDivs, pDiv, i, 2 )
        if ( !Abc_TtIntersectOne( pOffSet, 0, pDiv, 0, nWords ) )
            Vec_IntPush( vUnateLits, Abc_Var2Lit(i, 0) );
        else if ( !Abc_TtIntersectOne( pOffSet, 0, pDiv, 1, nWords ) )
            Vec_IntPush( vUnateLits, Abc_Var2Lit(i, 1) );
        else
            Vec_IntPush( vNotUnateVars, i );
}
int Gia_ManFindOneUnate( Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnateLits[2], Vec_Int_t * vNotUnateVars[2] )
{
    word * pOffSet = (word *)Vec_PtrEntry( vDivs, 0 );
    word * pOnSet  = (word *)Vec_PtrEntry( vDivs, 1 );
    int n;
    for ( n = 0; n < 2; n++ )
    {
        Vec_IntClear( vUnateLits[n] );
        Vec_IntClear( vNotUnateVars[n] );
        Gia_ManFindOneUnateInt( pOffSet, pOnSet, vDivs, nWords, vUnateLits[n], vNotUnateVars[n] );
        ABC_SWAP( word *, pOffSet, pOnSet );
        printf( "Found %d %d-unate divs.\n", Vec_IntSize(vUnateLits[n]), n );
    }
    return Gia_ManFindFirstCommonLit( vUnateLits[0], vUnateLits[1] );
}

static inline int Gia_ManDivCover( word * pOffSet, word * pOnSet, word * pDivA, int ComplA, word * pDivB, int ComplB, int nWords )
{
    assert( !Abc_TtIntersectOne(pOffSet, 0, pDivA, ComplA, nWords) );
    assert( !Abc_TtIntersectOne(pOffSet, 0, pDivB, ComplB, nWords) );
    return !Abc_TtIntersectTwo( pOnSet, 0, pDivA, !ComplA, pDivB, !ComplB, nWords );
}
int Gia_ManFindTwoUnateInt( word * pOffSet, word * pOnSet, Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnateLits )
{
    int i, k, iDiv0, iDiv1;
    Vec_IntForEachEntry( vUnateLits, iDiv1, i )
    Vec_IntForEachEntryStop( vUnateLits, iDiv0, k, i )
    {
        word * pDiv0 = (word *)Vec_PtrEntry(vDivs, Abc_Lit2Var(iDiv0));
        word * pDiv1 = (word *)Vec_PtrEntry(vDivs, Abc_Lit2Var(iDiv1));
        if ( Gia_ManDivCover(pOffSet, pOnSet, pDiv0, Abc_LitIsCompl(iDiv0), pDiv1, Abc_LitIsCompl(iDiv1), nWords) )
            return Abc_Var2Lit((Abc_LitNot(iDiv0) << 16) | Abc_LitNot(iDiv1), 0);
    }
    return -1;
}
int Gia_ManFindTwoUnate( Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnateLits[2] )
{
    word * pOffSet = (word *)Vec_PtrEntry( vDivs, 0 );
    word * pOnSet  = (word *)Vec_PtrEntry( vDivs, 1 );
    int n, iLit;
    for ( n = 0; n < 2; n++ )
    {
        printf( "Trying %d pairs of %d-unate divs.\n", Vec_IntSize(vUnateLits[n])*(Vec_IntSize(vUnateLits[n])-1)/2, n );
        iLit = Gia_ManFindTwoUnateInt( pOffSet, pOnSet, vDivs, nWords, vUnateLits[n] );
        if ( iLit >= 0 )
            return Abc_LitNotCond(iLit, !n);
        ABC_SWAP( word *, pOffSet, pOnSet );
    }
    return -1;
}

void Gia_ManFindXorInt( word * pOffSet, word * pOnSet, Vec_Int_t * vBinate, Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnateLits )
{
    int i, k, iDiv0, iDiv1;
    Vec_IntClear( vUnateLits );
    Vec_IntForEachEntry( vBinate, iDiv1, i )
    Vec_IntForEachEntryStop( vBinate, iDiv0, k, i )
    {
        word * pDiv0 = (word *)Vec_PtrEntry(vDivs, iDiv0);
        word * pDiv1 = (word *)Vec_PtrEntry(vDivs, iDiv1);
        if ( !Abc_TtIntersectXor( pOffSet, 0, pDiv0, pDiv1, 0, nWords ) )
            Vec_IntPush( vUnateLits, Abc_Var2Lit((Abc_Var2Lit(iDiv1, 0) << 16) | Abc_Var2Lit(iDiv0, 0), 0) );
        else if ( !Abc_TtIntersectXor( pOffSet, 0, pDiv0, pDiv1, 1, nWords ) )
            Vec_IntPush( vUnateLits, Abc_Var2Lit((Abc_Var2Lit(iDiv1, 0) << 16) | Abc_Var2Lit(iDiv0, 0), 1) );
    }
}
int Gia_ManFindXor( Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vBinateVars, Vec_Int_t * vUnateLits[2] )
{
    word * pOffSet = (word *)Vec_PtrEntry( vDivs, 0 );
    word * pOnSet  = (word *)Vec_PtrEntry( vDivs, 1 );
    int n;
    for ( n = 0; n < 2; n++ )
    {
        Vec_IntClear( vUnateLits[n] );
        Gia_ManFindXorInt( pOffSet, pOnSet, vBinateVars, vDivs, nWords, vUnateLits[n] );
        ABC_SWAP( word *, pOffSet, pOnSet );
        printf( "Found %d %d-unate XOR divs.\n", Vec_IntSize(vUnateLits[n]), n );
    }
    return Gia_ManFindFirstCommonLit( vUnateLits[0], vUnateLits[1] );
}

void Gia_ManFindUnatePairsInt( word * pOffSet, word * pOnSet, Vec_Int_t * vBinate, Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnateLits )
{
    int n, i, k, iDiv0, iDiv1;
    Vec_IntClear( vUnateLits );
    Vec_IntForEachEntry( vBinate, iDiv1, i )
    Vec_IntForEachEntryStop( vBinate, iDiv0, k, i )
    {
        word * pDiv0 = (word *)Vec_PtrEntry(vDivs, iDiv0);
        word * pDiv1 = (word *)Vec_PtrEntry(vDivs, iDiv1);
        for ( n = 0; n < 4; n++ )
        {
            int iLit0 = Abc_Var2Lit( iDiv0, n&1 );
            int iLit1 = Abc_Var2Lit( iDiv1, n>>1 );
            if ( !Abc_TtIntersectTwo( pOffSet, 0, pDiv0, n&1, pDiv1, n>>1, nWords ) )
                Vec_IntPush( vUnateLits, Abc_Var2Lit((iLit0 << 16) | iLit1, 0) );
        }
    }
}
void Gia_ManFindUnatePairs( Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vBinateVars, Vec_Int_t * vUnateLits[2] )
{
    word * pOffSet = (word *)Vec_PtrEntry( vDivs, 0 );
    word * pOnSet  = (word *)Vec_PtrEntry( vDivs, 1 );
    int n, RetValue;
    for ( n = 0; n < 2; n++ )
    {
        int nBefore = Vec_IntSize(vUnateLits[n]);
        Gia_ManFindUnatePairsInt( pOffSet, pOnSet, vBinateVars, vDivs, nWords, vUnateLits[n] );
        ABC_SWAP( word *, pOffSet, pOnSet );
        printf( "Found %d %d-unate pair divs.\n", Vec_IntSize(vUnateLits[n])-nBefore, n );
    }
    RetValue = Gia_ManFindFirstCommonLit( vUnateLits[0], vUnateLits[1] );
    assert( RetValue == -1 );
}

int Gia_ManFindAndGateInt( word * pOffSet, word * pOnSet, Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnateLits, Vec_Int_t * vUnatePairs, word * pDivTemp )
{
    int i, k, iDiv0, iDiv1;
    Vec_IntForEachEntry( vUnateLits, iDiv0, i )
    Vec_IntForEachEntry( vUnatePairs, iDiv1, k )
    {
        int fCompl = Abc_LitIsCompl(iDiv1);
        int iDiv10 = Abc_Lit2Var(iDiv1) >> 16;
        int iDiv11 = Abc_Lit2Var(iDiv1) & 0xFFF;
        word * pDiv0  = (word *)Vec_PtrEntry(vDivs, Abc_Lit2Var(iDiv0));
        word * pDiv10 = (word *)Vec_PtrEntry(vDivs, Abc_Lit2Var(iDiv10));
        word * pDiv11 = (word *)Vec_PtrEntry(vDivs, Abc_Lit2Var(iDiv11));
        Abc_TtAndCompl( pDivTemp, pDiv10, Abc_LitIsCompl(iDiv10), pDiv11, Abc_LitIsCompl(iDiv11), nWords );
        if ( Gia_ManDivCover(pOnSet, pOffSet, pDiv0, Abc_LitIsCompl(iDiv0), pDivTemp, fCompl, nWords) )
            return Abc_Var2Lit((Abc_LitNot(iDiv0) << 16) | Abc_Var2Lit(k, 1), 0);
    }
    return -1;
}
int Gia_ManFindAndGate( Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnateLits[2], Vec_Int_t * vUnatePairs[2], word * pDivTemp )
{
    word * pOffSet = (word *)Vec_PtrEntry( vDivs, 0 );
    word * pOnSet  = (word *)Vec_PtrEntry( vDivs, 1 );
    int n, iLit;
    for ( n = 0; n < 2; n++ )
    {
        iLit = Gia_ManFindAndGateInt( pOffSet, pOnSet, vDivs, nWords, vUnateLits[n], vUnatePairs[n], pDivTemp );
        if ( iLit > 0 )
            return Abc_LitNotCond( iLit, !n );
        ABC_SWAP( word *, pOffSet, pOnSet );
    }
    return -1;
}

int Gia_ManFindGateGateInt( word * pOffSet, word * pOnSet, Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnatePairs, word * pDivTempA, word * pDivTempB )
{
    int i, k, iDiv0, iDiv1;
    Vec_IntForEachEntry( vUnatePairs, iDiv0, i )
    {
        int fCompA = Abc_LitIsCompl(iDiv0);
        int iDiv00 = Abc_Lit2Var(iDiv0 >> 16);
        int iDiv01 = Abc_Lit2Var(iDiv0 & 0xFFF);
        word * pDiv00 = (word *)Vec_PtrEntry(vDivs, Abc_Lit2Var(iDiv00));
        word * pDiv01 = (word *)Vec_PtrEntry(vDivs, Abc_Lit2Var(iDiv01));
        Abc_TtAndCompl( pDivTempA, pDiv00, Abc_LitIsCompl(iDiv00), pDiv01, Abc_LitIsCompl(iDiv01), nWords );
        Vec_IntForEachEntryStop( vUnatePairs, iDiv1, k, i )
        {
            int fCompB = Abc_LitIsCompl(iDiv1);
            int iDiv10 = Abc_Lit2Var(iDiv1 >> 16);
            int iDiv11 = Abc_Lit2Var(iDiv1 & 0xFFF);
            word * pDiv10 = (word *)Vec_PtrEntry(vDivs, Abc_Lit2Var(iDiv10));
            word * pDiv11 = (word *)Vec_PtrEntry(vDivs, Abc_Lit2Var(iDiv11));
            Abc_TtAndCompl( pDivTempB, pDiv10, Abc_LitIsCompl(iDiv10), pDiv11, Abc_LitIsCompl(iDiv11), nWords );
            if ( Gia_ManDivCover(pOnSet, pOffSet, pDivTempA, fCompA, pDivTempB, fCompB, nWords) )
                return Abc_Var2Lit((iDiv1 << 16) | iDiv0, 0);
        }
    }
    return -1;
}
int Gia_ManFindGateGate( Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnatePairs[2], word * pDivTempA, word * pDivTempB )
{
    word * pOffSet = (word *)Vec_PtrEntry( vDivs, 0 );
    word * pOnSet  = (word *)Vec_PtrEntry( vDivs, 1 );
    int n, iLit;
    for ( n = 0; n < 2; n++ )
    {
        iLit = Gia_ManFindGateGateInt( pOffSet, pOnSet, vDivs, nWords, vUnatePairs[n], pDivTempA, pDivTempB );
        ABC_SWAP( word *, pOffSet, pOnSet );
        if ( iLit > 0 )
            return iLit;
    }
    return -1;
}

void Gia_ManComputeLitWeightsInt( word * pOffSet, word * pOnSet, Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnateLits, Vec_Int_t * vUnateLitsW )
{
    int i, iLit;
    Vec_IntClear( vUnateLitsW );
    Vec_IntForEachEntry( vUnateLits, iLit, i )
    {
        word * pDiv = (word *)Vec_PtrEntry( vDivs, Abc_Lit2Var(iLit) );
        assert( !Abc_TtIntersectOne( pOffSet, 0, pDiv, Abc_LitIsCompl(iLit), nWords ) );
        Vec_IntPush( vUnateLitsW, Abc_TtCountOnesVecMask(pDiv, pOnSet, nWords, Abc_LitIsCompl(iLit)) );
    }
}
void Gia_ManComputeLitWeights( Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnateLits[2], Vec_Int_t * vUnateLitsW[2] )
{
    word * pOffSet = (word *)Vec_PtrEntry( vDivs, 0 );
    word * pOnSet  = (word *)Vec_PtrEntry( vDivs, 1 );
    int n;
    for ( n = 0; n < 2; n++ )
    {
        Vec_IntClear( vUnateLitsW[n] );
        Gia_ManComputeLitWeightsInt( pOffSet, pOnSet, vDivs, nWords, vUnateLits[n], vUnateLitsW[n] );
        ABC_SWAP( word *, pOffSet, pOnSet );
    }
    for ( n = 0; n < 2; n++ )
    {
        int i, * pPerm = Abc_MergeSortCost( Vec_IntArray(vUnateLitsW[n]), Vec_IntSize(vUnateLitsW[n]) );
        Abc_ReverseOrder( pPerm, Vec_IntSize(vUnateLitsW[n]) );
        printf( "Top 10 %d-unate:\n", n );
        for ( i = 0; i < 10 && i < Vec_IntSize(vUnateLits[n]); i++ )
        {
            printf( "%5d : ", i );
            printf( "Obj = %5d  ",  Vec_IntEntry(vUnateLits[n], pPerm[i]) );
            printf( "Cost = %5d\n", Vec_IntEntry(vUnateLitsW[n], pPerm[i]) );
        }
        ABC_FREE( pPerm );
    }
}

void Gia_ManComputePairWeightsInt( word * pOffSet, word * pOnSet, Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnatePairs, Vec_Int_t * vUnatePairsW )
{
    int i, iPair;
    Vec_IntClear( vUnatePairsW );
    Vec_IntForEachEntry( vUnatePairs, iPair, i )
    {
        int fCompl = Abc_LitIsCompl(iPair);
        int Pair = Abc_Lit2Var(iPair);
        int iLit0 = Pair >> 16;
        int iLit1 = Pair & 0xFFFF;
        word * pDiv0 = (word *)Vec_PtrEntry( vDivs, Abc_Lit2Var(iLit0) );
        word * pDiv1 = (word *)Vec_PtrEntry( vDivs, Abc_Lit2Var(iLit1) );
        if ( iLit0 < iLit1 )
        {
            assert( !fCompl );
            assert( !Abc_TtIntersectTwo( pOffSet, 0, pDiv0, Abc_LitIsCompl(iLit0), pDiv1, Abc_LitIsCompl(iLit1), nWords ) );
            Vec_IntPush( vUnatePairsW, Abc_TtCountOnesVecMask2(pDiv0, pDiv1, Abc_LitIsCompl(iLit0), Abc_LitIsCompl(iLit1), pOnSet, nWords) );
        }
        else
        {
            assert( !Abc_LitIsCompl(iLit0) );
            assert( !Abc_LitIsCompl(iLit1) );
            assert( !Abc_TtIntersectXor( pOffSet, 0, pDiv0, pDiv1, 0, nWords ) );
            Vec_IntPush( vUnatePairsW, Abc_TtCountOnesVecXorMask(pDiv0, pDiv1, fCompl, pOnSet, nWords) );
        }
    }
}
void Gia_ManComputePairWeights( Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnatePairs[2], Vec_Int_t * vUnatePairsW[2] )
{
    word * pOffSet = (word *)Vec_PtrEntry( vDivs, 0 );
    word * pOnSet  = (word *)Vec_PtrEntry( vDivs, 1 );
    int n;
    for ( n = 0; n < 2; n++ )
    {
        Gia_ManComputePairWeightsInt( pOffSet, pOnSet, vDivs, nWords, vUnatePairs[n], vUnatePairsW[n] );
        ABC_SWAP( word *, pOffSet, pOnSet );
    }
    for ( n = 0; n < 2; n++ )
    {
        int i, * pPerm = Abc_MergeSortCost( Vec_IntArray(vUnatePairsW[n]), Vec_IntSize(vUnatePairsW[n]) );
        Abc_ReverseOrder( pPerm, Vec_IntSize(vUnatePairsW[n]) );
        printf( "Top 10 %d-unate:\n", n );
        for ( i = 0; i < 10 && i < Vec_IntSize(vUnatePairs[n]); i++ )
        {
            printf( "%5d : ", i );
            printf( "Obj = %5d  ",  Vec_IntEntry(vUnatePairs[n], pPerm[i]) );
            printf( "Cost = %5d\n", Vec_IntEntry(vUnatePairsW[n], pPerm[i]) );
        }
        ABC_FREE( pPerm );
    }
}


/**Function*************************************************************

  Synopsis    [Perform resubstitution.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManResubInt2( Vec_Ptr_t * vDivs, int nWords, int NodeLimit, int ChoiceType, Vec_Int_t * vGates )
{
    return 0;
}
int Gia_ManResubInt( Gia_ResbMan_t * p )
{
    int nDivs = Vec_PtrSize(p->vDivs);
    int iResLit = Gia_ManFindOneUnate( p->vDivs, p->nWords, p->vUnateLits, p->vNotUnateVars );
    if ( iResLit >= 0 ) // buffer
    {
        printf( "Creating %s (%d).\n", Abc_LitIsCompl(iResLit) ? "inverter" : "buffer", Abc_Lit2Var(iResLit) );
        return iResLit;
    }
    iResLit = Gia_ManFindTwoUnate( p->vDivs, p->nWords, p->vUnateLits );
    if ( iResLit >= 0 ) // and
    {
        int fCompl = Abc_LitIsCompl(iResLit);
        int iDiv0 = Abc_Lit2Var(iResLit) >> 16;
        int iDiv1 = Abc_Lit2Var(iResLit) & 0xFFFF;
        Vec_IntPushTwo( p->vGates, iDiv0, iDiv1 );
        printf( "Creating one AND-gate.\n" );
        return Abc_Var2Lit( nDivs + Vec_IntSize(p->vGates)/2-1, fCompl );
    }
    Vec_IntTwoFindCommon( p->vNotUnateVars[0], p->vNotUnateVars[1], p->vBinateVars );
    if ( Vec_IntSize(p->vBinateVars) > 1000 )
    {
        printf( "Reducing binate divs from %d to 1000.\n", Vec_IntSize(p->vBinateVars) );
        Vec_IntShrink( p->vBinateVars, 1000 );
    }
    iResLit = Gia_ManFindXor( p->vDivs, p->nWords, p->vBinateVars, p->vUnatePairs );
    if ( iResLit >= 0 ) // xor
    {
        int fCompl = Abc_LitIsCompl(iResLit);
        int iDiv0 = Abc_Lit2Var(iResLit) >> 16;
        int iDiv1 = Abc_Lit2Var(iResLit) & 0xFFFF;
        assert( !Abc_LitIsCompl(iDiv0) );
        assert( !Abc_LitIsCompl(iDiv1) );
        Vec_IntPushTwo( p->vGates, iDiv0, iDiv1 ); // xor
        printf( "Creating one XOR-gate.\n" );
        return Abc_Var2Lit( nDivs + Vec_IntSize(p->vGates)/2-1, fCompl );
    }
    Gia_ManFindUnatePairs( p->vDivs, p->nWords, p->vBinateVars, p->vUnatePairs );
/*
    iResLit = Gia_ManFindAndGate( p->vDivs, p->nWords, p->vUnateLits, p->vUnatePairs, p->pDivA );
    if ( iResLit >= 0 ) // and-gate
    {
        int New = nDivs + Vec_IntSize(p->vGates)/2;
        int fCompl = Abc_LitIsCompl(iResLit);
        int iDiv0 = Abc_Lit2Var(iResLit) >> 16;
        int iDiv1 = Abc_Lit2Var(iResLit) & 0xFFFF;
        Vec_IntPushTwo( p->vGates, Abc_LitNot(iDiv1), Abc_LitNot(iDiv0) );
        Vec_IntPushTwo( p->vGates, Abc_LitNot(iDiv0), New );
        printf( "Creating one two gates.\n" );
        return Abc_Var2Lit( nDivs + Vec_IntSize(p->vGates)/2-1, 1 );
    }
    iResLit = Gia_ManFindGateGate( p->vDivs, p->nWords, p->vUnatePairs, p->pDivA, p->pDivB );
    if ( iResLit >= 0 ) // and-(gate,gate)
    {
        printf( "Creating one three gates.\n" );
        return -1;
    }
*/
    Gia_ManComputeLitWeights( p->vDivs, p->nWords, p->vUnateLits, p->vUnateLitsW );
    Gia_ManComputePairWeights( p->vDivs, p->nWords, p->vUnatePairs, p->vUnatePairsW );
    return -1;
}

/**Function*************************************************************

  Synopsis    [Top level.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCheckResub( Vec_Ptr_t * vDivs, int nWords )
{
    int i, Set[10] = { 2, 189, 2127, 2125, 177, 178 };
    word * pOffSet = (word *)Vec_PtrEntry( vDivs, 0 );
    word * pOnSet  = (word *)Vec_PtrEntry( vDivs, 1 );
    Vec_Int_t * vValue = Vec_IntStartFull( 1 << 6 );
    printf( "Verifying resub:\n" );
    for ( i = 0; i < 64*nWords; i++ )
    {
        int v, Mint = 0, Value = Abc_TtGetBit(pOnSet, i);
        if ( !Abc_TtGetBit(pOffSet, i) && !Value )
            continue;
        for ( v = 0; v < 6; v++ )
            if ( Abc_TtGetBit((word *)Vec_PtrEntry(vDivs, Set[v]), i) )
                Mint |= 1 << v;
        if ( Vec_IntEntry(vValue, Mint) == -1 )
            Vec_IntWriteEntry(vValue, Mint, Value);
        else if ( Vec_IntEntry(vValue, Mint) != Value )
            printf( "Mismatch in pattern %d\n", i );
    }
    printf( "Finished verifying resub.\n" );
    Vec_IntFree( vValue );
}
Vec_Ptr_t * Gia_ManDeriveDivs( Vec_Wrd_t * vSims, int nWords )
{
    int i, nDivs = Vec_WrdSize(vSims)/nWords;
    Vec_Ptr_t * vDivs = Vec_PtrAlloc( nDivs );
    for ( i = 0; i < nDivs; i++ )
        Vec_PtrPush( vDivs, Vec_WrdEntryP(vSims, nWords*i) );
    return vDivs;
}
Gia_Man_t * Gia_ManResub2( Gia_Man_t * pGia, int nNodes, int nSupp, int nDivs, int fVerbose, int fVeryVerbose )
{
    return NULL;
}
Gia_Man_t * Gia_ManResub1( char * pFileName, int nNodes, int nSupp, int nDivs, int fVerbose, int fVeryVerbose )
{
    int iTopLit, nWords = 0;
    Gia_Man_t * pMan   = NULL;
    Vec_Wrd_t * vSims  = Gia_ManSimPatRead( pFileName, &nWords );
    Vec_Ptr_t * vDivs  = vSims ? Gia_ManDeriveDivs( vSims, nWords ) : NULL;
    Vec_Int_t * vGates = vDivs ? Vec_IntAlloc( 100 ) : NULL;
    Gia_ResbMan_t * p  = vDivs ? Gia_ResbAlloc( vDivs, nWords, vGates ) : NULL;
    if ( p == NULL )
        return NULL;
    assert( Vec_PtrSize(vDivs) < (1<<15) );
    printf( "OFF = %5d (%6.2f %%)  ", Abc_TtCountOnesVec((word *)Vec_PtrEntry(vDivs, 0), nWords), 100.0*Abc_TtCountOnesVec((word *)Vec_PtrEntry(vDivs, 0), nWords)/(64*nWords) );
    printf( "ON = %5d (%6.2f %%)\n",  Abc_TtCountOnesVec((word *)Vec_PtrEntry(vDivs, 1), nWords), 100.0*Abc_TtCountOnesVec((word *)Vec_PtrEntry(vDivs, 1), nWords)/(64*nWords) );
    if ( Vec_PtrSize(vDivs) > 4000 )
    {
        printf( "Reducing all divs from %d to 4000.\n", Vec_PtrSize(vDivs) );
        Vec_PtrShrink( vDivs, 4000 );
    }
    Gia_ResbReset( p );
//    Gia_ManCheckResub( vDivs, nWords );
    iTopLit = Gia_ManResubInt( p );
    if ( iTopLit >= 0 )
    {
        printf( "Verification %s.\n", Gia_ManResubVerify( vDivs, nWords, vGates, iTopLit ) ? "succeeded" : "FAILED" );
        pMan = Gia_ManConstructFromGates( Vec_PtrSize(vDivs), vGates, iTopLit );
    }
    else
        printf( "Decomposition did not succeed.\n" );
    Gia_ResbFree( p );
    Vec_IntFree( vGates );
    Vec_PtrFree( vDivs );
    Vec_WrdFree( vSims );
    return pMan;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

