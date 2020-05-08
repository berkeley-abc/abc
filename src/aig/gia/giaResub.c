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
    int         nLimit;
    int         fDebug;
    int         fVerbose;
    Vec_Ptr_t * vDivs;
    Vec_Int_t * vGates;
    Vec_Int_t * vUnateLits[2];
    Vec_Int_t * vNotUnateVars[2];
    Vec_Int_t * vUnatePairs[2];
    Vec_Int_t * vBinateVars;
    Vec_Int_t * vUnateLitsW[2];
    Vec_Int_t * vUnatePairsW[2];
    word *      pSets[2];
    word *      pDivA;
    word *      pDivB;
    Vec_Wrd_t * vSims;
};
Gia_ResbMan_t * Gia_ResbAlloc( int nWords )
{
    Gia_ResbMan_t * p   = ABC_CALLOC( Gia_ResbMan_t, 1 );
    p->nWords           = nWords;
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
    p->vGates           = Vec_IntAlloc( 100 );
    p->vDivs            = Vec_PtrAlloc( 100 );
    p->pSets[0]         = ABC_CALLOC( word, nWords );
    p->pSets[1]         = ABC_CALLOC( word, nWords );
    p->pDivA            = ABC_CALLOC( word, nWords );
    p->pDivB            = ABC_CALLOC( word, nWords );
    p->vSims            = Vec_WrdAlloc( 100 );
    return p;
}
void Gia_ResbInit( Gia_ResbMan_t * p, Vec_Ptr_t * vDivs, int nWords, int nLimit, int fDebug, int fVerbose )
{
    assert( p->nWords == nWords );
    p->nLimit   = nLimit;
    p->fDebug   = fDebug;
    p->fVerbose = fVerbose;
    Abc_TtCopy( p->pSets[0], (word *)Vec_PtrEntry(vDivs, 0), nWords, 0 );
    Abc_TtCopy( p->pSets[1], (word *)Vec_PtrEntry(vDivs, 1), nWords, 0 );
    Vec_PtrClear( p->vDivs );
    Vec_PtrAppend( p->vDivs, vDivs );
    Vec_IntClear( p->vGates );
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
    Vec_IntFree( p->vGates           );
    Vec_WrdFree( p->vSims            );
    Vec_PtrFree( p->vDivs            );
    ABC_FREE( p->pSets[0] );
    ABC_FREE( p->pSets[1] );
    ABC_FREE( p->pDivA );
    ABC_FREE( p->pDivB );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Print resubstitution.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManResubPrintNode( Vec_Int_t * vRes, int nVars, int Node, int fCompl )
{
    extern void Gia_ManResubPrintLit( Vec_Int_t * vRes, int nVars, int iLit );
    int iLit0 = Vec_IntEntry( vRes, 2*Node + 0 );
    int iLit1 = Vec_IntEntry( vRes, 2*Node + 1 );
    assert( iLit0 != iLit1 );
    if ( iLit0 > iLit1 && Abc_LitIsCompl(fCompl) ) // xor
    {
        printf( "~" );
        fCompl = 0;
    }
    printf( "(" );
    Gia_ManResubPrintLit( vRes, nVars, Abc_LitNotCond(iLit0, fCompl) );
    printf( " %c ", iLit0 > iLit1 ? '^' : (fCompl ? '|' : '&') );
    Gia_ManResubPrintLit( vRes, nVars, Abc_LitNotCond(iLit1, fCompl) );
    printf( ")" );
}
void Gia_ManResubPrintLit( Vec_Int_t * vRes, int nVars, int iLit )
{
    if ( Abc_Lit2Var(iLit) < nVars )
    {
        if ( nVars < 26 )
            printf( "%s%c", Abc_LitIsCompl(iLit) ? "~":"", 'a' + Abc_Lit2Var(iLit)-2 );
        else
            printf( "%si%d", Abc_LitIsCompl(iLit) ? "~":"", Abc_Lit2Var(iLit)-2 );
    }
    else
        Gia_ManResubPrintNode( vRes, nVars, Abc_Lit2Var(iLit) - nVars, Abc_LitIsCompl(iLit) );
}
int Gia_ManResubPrint( Vec_Int_t * vRes, int nVars )
{
    int iTopLit;
    if ( Vec_IntSize(vRes) == 0 )
        return printf( "none" );
    assert( Vec_IntSize(vRes) % 2 == 1 );
    iTopLit = Vec_IntEntryLast(vRes);
    if ( iTopLit == 0 )
        return printf( "const0" );
    if ( iTopLit == 1 )
        return printf( "const1" );
    Gia_ManResubPrintLit( vRes, nVars, iTopLit );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Verify resubstitution.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManResubVerify( Gia_ResbMan_t * p )
{
    int nVars = Vec_PtrSize(p->vDivs);
    int iTopLit, RetValue;
    word * pDivRes; 
    if ( Vec_IntSize(p->vGates) == 0 )
        return -1;
    iTopLit = Vec_IntEntryLast(p->vGates);
    assert( iTopLit >= 0 );
    if ( iTopLit == 0 )
        return Abc_TtIsConst0( p->pSets[1], p->nWords );
    if ( iTopLit == 1 )
        return Abc_TtIsConst0( p->pSets[0], p->nWords );
    if ( Abc_Lit2Var(iTopLit) < nVars )
    {
        assert( Vec_IntSize(p->vGates) == 1 );
        pDivRes = (word *)Vec_PtrEntry( p->vDivs, Abc_Lit2Var(iTopLit) );
    }
    else
    {
        int i, iLit0, iLit1;
        assert( Vec_IntSize(p->vGates) > 1 );
        assert( Vec_IntSize(p->vGates) % 2 == 1 );
        assert( Abc_Lit2Var(iTopLit)-nVars == Vec_IntSize(p->vGates)/2-1 );
        Vec_WrdFill( p->vSims, p->nWords * Vec_IntSize(p->vGates)/2, 0 );
        Vec_IntForEachEntryDouble( p->vGates, iLit0, iLit1, i )
        {
            int iVar0 = Abc_Lit2Var(iLit0);
            int iVar1 = Abc_Lit2Var(iLit1);
            word * pDiv0 = iVar0 < nVars ? (word *)Vec_PtrEntry(p->vDivs, iVar0) : Vec_WrdEntryP(p->vSims, p->nWords*(iVar0 - nVars));
            word * pDiv1 = iVar1 < nVars ? (word *)Vec_PtrEntry(p->vDivs, iVar1) : Vec_WrdEntryP(p->vSims, p->nWords*(iVar1 - nVars));
            word * pDiv  = Vec_WrdEntryP(p->vSims, p->nWords*i/2);
            if ( iVar0 < iVar1 )
                Abc_TtAndCompl( pDiv, pDiv0, Abc_LitIsCompl(iLit0), pDiv1, Abc_LitIsCompl(iLit1), p->nWords );
            else if ( iVar0 > iVar1 )
            {
                assert( !Abc_LitIsCompl(iLit0) );
                assert( !Abc_LitIsCompl(iLit1) );
                Abc_TtXor( pDiv, pDiv0, pDiv1, p->nWords, 0 );
            }
            else assert( 0 );
        }
        pDivRes = Vec_WrdEntryP( p->vSims, p->nWords*(Vec_IntSize(p->vGates)/2-1) );
    }
    if ( Abc_LitIsCompl(iTopLit) )
        RetValue = !Abc_TtIntersectOne(p->pSets[1], 0, pDivRes, 0, p->nWords) && !Abc_TtIntersectOne(p->pSets[0], 0, pDivRes, 1, p->nWords);
    else
        RetValue = !Abc_TtIntersectOne(p->pSets[0], 0, pDivRes, 0, p->nWords) && !Abc_TtIntersectOne(p->pSets[1], 0, pDivRes, 1, p->nWords);
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
Gia_Man_t * Gia_ManConstructFromGates( Vec_Int_t * vGates, int nVars )
{
    int i, iLit0, iLit1, iTopLit, iLitRes;
    Gia_Man_t * pNew;
    if ( Vec_IntSize(vGates) == 0 )
        return NULL;
    assert( Vec_IntSize(vGates) % 2 == 1 );
    pNew = Gia_ManStart( 100 );
    pNew->pName = Abc_UtilStrsav( "resub" );
    iTopLit = Vec_IntEntryLast( vGates );
    if ( iTopLit == 0 || iTopLit == 1 )
        iLitRes = 0;
    else if ( Abc_Lit2Var(iTopLit) < nVars )
    {
        assert( Vec_IntSize(vGates) == 1 );
        iLitRes = Gia_ManAppendCi(pNew);
    }
    else
    {
        Vec_Int_t * vUsed = Vec_IntStartFull( nVars );
        Vec_Int_t * vCopy = Vec_IntAlloc( Vec_IntSize(vGates)/2 );
        assert( Vec_IntSize(vGates) > 1 );
        assert( Vec_IntSize(vGates) % 2 == 1 );
        assert( Abc_Lit2Var(iTopLit)-nVars == Vec_IntSize(vGates)/2-1 );
        Vec_IntForEachEntryDouble( vGates, iLit0, iLit1, i )
        {
            int iVar0 = Abc_Lit2Var(iLit0);
            int iVar1 = Abc_Lit2Var(iLit1);
            int iRes0 = iVar0 < nVars ? Gia_ManGetVar(pNew, vUsed, iVar0) : Vec_IntEntry(vCopy, iVar0 - nVars);
            int iRes1 = iVar1 < nVars ? Gia_ManGetVar(pNew, vUsed, iVar1) : Vec_IntEntry(vCopy, iVar1 - nVars);
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
static inline int Gia_ManFindFirstCommonLit( Vec_Int_t * vArr1, Vec_Int_t * vArr2, int fVerbose )
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
    if ( fVerbose ) printf( "Removed %d duplicated entries.  Array1 = %d.  Array2 = %d.\n", nRemoved, Vec_IntSize(vArr1), Vec_IntSize(vArr2) );
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
int Gia_ManFindOneUnate( word * pSets[2], Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnateLits[2], Vec_Int_t * vNotUnateVars[2], int fVerbose )
{
    int n;
    for ( n = 0; n < 2; n++ )
    {
        Gia_ManFindOneUnateInt( pSets[n], pSets[!n], vDivs, nWords, vUnateLits[n], vNotUnateVars[n] );
        if ( fVerbose ) printf( "Found %d %d-unate divs.\n", Vec_IntSize(vUnateLits[n]), n );
    }
    return Gia_ManFindFirstCommonLit( vUnateLits[0], vUnateLits[1], fVerbose );
}

static inline int Gia_ManDivCover( word * pOffSet, word * pOnSet, word * pDivA, int ComplA, word * pDivB, int ComplB, int nWords )
{
    //assert( !Abc_TtIntersectOne(pOffSet, 0, pDivA, ComplA, nWords) );
    //assert( !Abc_TtIntersectOne(pOffSet, 0, pDivB, ComplB, nWords) );
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
        if ( Gia_ManDivCover(pOffSet, pOnSet, pDiv1, Abc_LitIsCompl(iDiv1), pDiv0, Abc_LitIsCompl(iDiv0), nWords) )
            return Abc_Var2Lit((Abc_LitNot(iDiv1) << 15) | Abc_LitNot(iDiv0), 1);
    }
    return -1;
}
int Gia_ManFindTwoUnate( word * pSets[2], Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnateLits[2], int fVerbose )
{
    int n, iLit;
    for ( n = 0; n < 2; n++ )
    {
        int nPairs = Vec_IntSize(vUnateLits[n])*(Vec_IntSize(vUnateLits[n])-1)/2;
        if ( fVerbose ) printf( "Trying %d pairs of %d-unate divs.\n", nPairs, n );
        iLit = Gia_ManFindTwoUnateInt( pSets[n], pSets[!n], vDivs, nWords, vUnateLits[n] );
        if ( iLit >= 0 )
            return Abc_LitNotCond(iLit, n);
    }
    return -1;
}

void Gia_ManFindXorInt( word * pOffSet, word * pOnSet, Vec_Int_t * vBinate, Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnatePairs )
{
    int i, k, iDiv0, iDiv1;
    Vec_IntForEachEntry( vBinate, iDiv1, i )
    Vec_IntForEachEntryStop( vBinate, iDiv0, k, i )
    {
        word * pDiv0 = (word *)Vec_PtrEntry(vDivs, iDiv0);
        word * pDiv1 = (word *)Vec_PtrEntry(vDivs, iDiv1);
        if ( !Abc_TtIntersectXor( pOffSet, 0, pDiv0, pDiv1, 0, nWords ) )
            Vec_IntPush( vUnatePairs, Abc_Var2Lit((Abc_Var2Lit(iDiv0, 0) << 15) | Abc_Var2Lit(iDiv1, 0), 0) );
        else if ( !Abc_TtIntersectXor( pOffSet, 0, pDiv0, pDiv1, 1, nWords ) )
            Vec_IntPush( vUnatePairs, Abc_Var2Lit((Abc_Var2Lit(iDiv0, 0) << 15) | Abc_Var2Lit(iDiv1, 0), 1) );
    }
}
int Gia_ManFindXor( word * pSets[2], Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vBinateVars, Vec_Int_t * vUnatePairs[2], int fVerbose )
{
    int n;
    for ( n = 0; n < 2; n++ )
    {
        Vec_IntClear( vUnatePairs[n] );
        Gia_ManFindXorInt( pSets[n], pSets[!n], vBinateVars, vDivs, nWords, vUnatePairs[n] );
        if ( fVerbose ) printf( "Found %d %d-unate XOR divs.\n", Vec_IntSize(vUnatePairs[n]), n );
    }
    return Gia_ManFindFirstCommonLit( vUnatePairs[0], vUnatePairs[1], fVerbose );
}

void Gia_ManFindUnatePairsInt( word * pOffSet, word * pOnSet, Vec_Int_t * vBinate, Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnatePairs )
{
    int n, i, k, iDiv0, iDiv1;
    Vec_IntForEachEntry( vBinate, iDiv1, i )
    Vec_IntForEachEntryStop( vBinate, iDiv0, k, i )
    {
        word * pDiv0 = (word *)Vec_PtrEntry(vDivs, iDiv0);
        word * pDiv1 = (word *)Vec_PtrEntry(vDivs, iDiv1);
        for ( n = 0; n < 4; n++ )
        {
            int iLit0 = Abc_Var2Lit( iDiv0, n&1 );
            int iLit1 = Abc_Var2Lit( iDiv1, n>>1 );
            if ( !Abc_TtIntersectTwo( pOffSet, 0, pDiv1, n>>1, pDiv0, n&1, nWords ) )
                Vec_IntPush( vUnatePairs, Abc_Var2Lit((iLit1 << 15) | iLit0, 0) );
        }
    }
}
void Gia_ManFindUnatePairs( word * pSets[2], Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vBinateVars, Vec_Int_t * vUnatePairs[2], int fVerbose )
{
    int n, RetValue;
    for ( n = 0; n < 2; n++ )
    {
        int nBefore = Vec_IntSize(vUnatePairs[n]);
        Gia_ManFindUnatePairsInt( pSets[n], pSets[!n], vBinateVars, vDivs, nWords, vUnatePairs[n] );
        if ( fVerbose ) printf( "Found %d %d-unate pair divs.\n", Vec_IntSize(vUnatePairs[n])-nBefore, n );
    }
    RetValue = Gia_ManFindFirstCommonLit( vUnatePairs[0], vUnatePairs[1], fVerbose );
    assert( RetValue == -1 );
}

void Gia_ManDeriveDivPair( int iDiv, Vec_Ptr_t * vDivs, int nWords, word * pRes )
{
    int fComp = Abc_LitIsCompl(iDiv);
    int iDiv0 = Abc_Lit2Var(iDiv) & 0x7FFF;
    int iDiv1 = Abc_Lit2Var(iDiv) >> 15;
    word * pDiv0 = (word *)Vec_PtrEntry(vDivs, Abc_Lit2Var(iDiv0));
    word * pDiv1 = (word *)Vec_PtrEntry(vDivs, Abc_Lit2Var(iDiv1));
    if ( iDiv0 < iDiv1 )
    {
        assert( !fComp );
        Abc_TtAndCompl( pRes, pDiv0, Abc_LitIsCompl(iDiv0), pDiv1, Abc_LitIsCompl(iDiv1), nWords );
    }
    else 
    {
        assert( !Abc_LitIsCompl(iDiv0) );
        assert( !Abc_LitIsCompl(iDiv1) );
        Abc_TtXor( pRes, pDiv0, pDiv1, nWords, 0 );
    }
}
int Gia_ManFindDivGateInt( word * pOffSet, word * pOnSet, Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnateLits, Vec_Int_t * vUnatePairs, word * pDivTemp )
{
    int i, k, iDiv0, iDiv1;
    int Limit1 = Abc_MinInt( Vec_IntSize(vUnateLits), 1000 );
    int Limit2 = Abc_MinInt( Vec_IntSize(vUnatePairs), 1000 );
    Vec_IntForEachEntryStop( vUnateLits, iDiv0, i, Limit1 )
    Vec_IntForEachEntryStop( vUnatePairs, iDiv1, k, Limit2 )
    {
        word * pDiv0 = (word *)Vec_PtrEntry(vDivs, Abc_Lit2Var(iDiv0));
        int fComp1   = Abc_LitIsCompl(iDiv1);
        Gia_ManDeriveDivPair( iDiv1, vDivs, nWords, pDivTemp );
        if ( Gia_ManDivCover(pOffSet, pOnSet, pDiv0, Abc_LitIsCompl(iDiv0), pDivTemp, fComp1, nWords) )
            return Abc_Var2Lit((Abc_Var2Lit(k, 1) << 15) | Abc_LitNot(iDiv0), 1);
    }
    return -1;
}
int Gia_ManFindDivGate( word * pSets[2], Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnateLits[2], Vec_Int_t * vUnatePairs[2], word * pDivTemp )
{
    int n, iLit;
    for ( n = 0; n < 2; n++ )
    {
        iLit = Gia_ManFindDivGateInt( pSets[n], pSets[!n], vDivs, nWords, vUnateLits[n], vUnatePairs[n], pDivTemp );
        if ( iLit >= 0 )
            return Abc_LitNotCond( iLit, n );
    }
    return -1;
}

int Gia_ManFindGateGateInt( word * pOffSet, word * pOnSet, Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnatePairs, word * pDivTempA, word * pDivTempB )
{
    int i, k, iDiv0, iDiv1;
    int Limit2 = Abc_MinInt( Vec_IntSize(vUnatePairs), 1000 );
    Vec_IntForEachEntryStop( vUnatePairs, iDiv1, i, Limit2 )
    {
        int fCompB = Abc_LitIsCompl(iDiv1);
        Gia_ManDeriveDivPair( iDiv1, vDivs, nWords, pDivTempB );
        Vec_IntForEachEntryStop( vUnatePairs, iDiv0, k, i )
        {
            int fCompA = Abc_LitIsCompl(iDiv0);
            Gia_ManDeriveDivPair( iDiv0, vDivs, nWords, pDivTempA );
            if ( Gia_ManDivCover(pOffSet, pOnSet, pDivTempA, fCompA, pDivTempB, fCompB, nWords) )
                return Abc_Var2Lit((Abc_Var2Lit(i, 1) << 15) | Abc_Var2Lit(k, 1), 1);
        }
    }
    return -1;
}
int Gia_ManFindGateGate( word * pSets[2], Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnatePairs[2], word * pDivTempA, word * pDivTempB )
{
    int n, iLit;
    for ( n = 0; n < 2; n++ )
    {
        iLit = Gia_ManFindGateGateInt( pSets[n], pSets[!n], vDivs, nWords, vUnatePairs[n], pDivTempA, pDivTempB );
        if ( iLit >= 0 )
            return Abc_LitNotCond( iLit, n );
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
        //assert( !Abc_TtIntersectOne( pOffSet, 0, pDiv, Abc_LitIsCompl(iLit), nWords ) );
        Vec_IntPush( vUnateLitsW, -Abc_TtCountOnesVecMask(pDiv, pOnSet, nWords, Abc_LitIsCompl(iLit)) );
    }
}
void Gia_ManComputeLitWeights( word * pSets[2], Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnateLits[2], Vec_Int_t * vUnateLitsW[2], int TopW[2], int fVerbose )
{
    int n, TopNum = 5;
    TopW[0] = TopW[1] = 0;
    for ( n = 0; n < 2; n++ )
        Gia_ManComputeLitWeightsInt( pSets[n], pSets[!n], vDivs, nWords, vUnateLits[n], vUnateLitsW[n] );
    for ( n = 0; n < 2; n++ )
        if ( Vec_IntSize(vUnateLitsW[n]) )
        {
            int i, * pPerm = Abc_MergeSortCost( Vec_IntArray(vUnateLitsW[n]), Vec_IntSize(vUnateLitsW[n]) );
            TopW[n] = -Vec_IntEntry(vUnateLitsW[n], pPerm[0]);
            if ( fVerbose ) 
            {
                printf( "Top %d %d-unate divs:\n", TopNum, n );
                for ( i = 0; i < TopNum && i < Vec_IntSize(vUnateLits[n]); i++ )
                {
                    printf( "%5d : ", i );
                    printf( "Lit = %5d  ",  Vec_IntEntry(vUnateLits[n], pPerm[i]) );
                    printf( "Cost = %5d\n", -Vec_IntEntry(vUnateLitsW[n], pPerm[i]) );
                }
            }
            for ( i = 0; i < Vec_IntSize(vUnateLits[n]); i++ )
                pPerm[i] = Vec_IntEntry(vUnateLits[n], pPerm[i]);
            for ( i = 0; i < Vec_IntSize(vUnateLits[n]); i++ )
                vUnateLits[n]->pArray[i] = pPerm[i];
            ABC_FREE( pPerm );
        }
}

void Gia_ManComputePairWeightsInt( word * pOffSet, word * pOnSet, Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnatePairs, Vec_Int_t * vUnatePairsW )
{
    int i, iPair;
    Vec_IntClear( vUnatePairsW );
    Vec_IntForEachEntry( vUnatePairs, iPair, i )
    {
        int fComp = Abc_LitIsCompl(iPair);
        int iLit0 = Abc_Lit2Var(iPair) & 0x7FFF;
        int iLit1 = Abc_Lit2Var(iPair) >> 15;
        word * pDiv0 = (word *)Vec_PtrEntry( vDivs, Abc_Lit2Var(iLit0) );
        word * pDiv1 = (word *)Vec_PtrEntry( vDivs, Abc_Lit2Var(iLit1) );
        if ( iLit0 < iLit1 )
        {
            assert( !fComp );
            //assert( !Abc_TtIntersectTwo( pOffSet, 0, pDiv0, Abc_LitIsCompl(iLit0), pDiv1, Abc_LitIsCompl(iLit1), nWords ) );
            Vec_IntPush( vUnatePairsW, -Abc_TtCountOnesVecMask2(pDiv0, pDiv1, Abc_LitIsCompl(iLit0), Abc_LitIsCompl(iLit1), pOnSet, nWords) );
        }
        else
        {
            assert( !Abc_LitIsCompl(iLit0) );
            assert( !Abc_LitIsCompl(iLit1) );
            //assert( !Abc_TtIntersectXor( pOffSet, 0, pDiv0, pDiv1, fComp, nWords ) );
            Vec_IntPush( vUnatePairsW, -Abc_TtCountOnesVecXorMask(pDiv0, pDiv1, fComp, pOnSet, nWords) );
        }
    }
}
void Gia_ManComputePairWeights( word * pSets[2], Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnatePairs[2], Vec_Int_t * vUnatePairsW[2], int TopW[2], int fVerbose )
{
    int n, TopNum = 5;
    TopW[0] = TopW[1] = 0;
    for ( n = 0; n < 2; n++ )
        Gia_ManComputePairWeightsInt( pSets[n], pSets[!n], vDivs, nWords, vUnatePairs[n], vUnatePairsW[n] );
    for ( n = 0; n < 2; n++ )
        if ( Vec_IntSize(vUnatePairsW[n]) )
        {
            int i, * pPerm = Abc_MergeSortCost( Vec_IntArray(vUnatePairsW[n]), Vec_IntSize(vUnatePairsW[n]) );
            TopW[n] = -Vec_IntEntry(vUnatePairsW[n], pPerm[0]);
            if ( fVerbose ) 
            {
                printf( "Top %d %d-unate pairs:\n", TopNum, n );
                for ( i = 0; i < TopNum && i < Vec_IntSize(vUnatePairs[n]); i++ )
                {
                    int Pair = Vec_IntEntry(vUnatePairs[n], pPerm[i]);
                    int Div0 = Abc_Lit2Var(Pair) & 0x7FFF;
                    int Div1 = Abc_Lit2Var(Pair) >> 15;
                    printf( "%5d : ", i );
                    printf( "Compl = %5d  ", Abc_LitIsCompl(Pair) );
                    printf( "Type = %s  ",   Div0 < Div1 ? "and" : "xor" );
                    printf( "Div0 = %5d  ",  Div0 );
                    printf( "Div1 = %5d  ",  Div1 );
                    printf( "Cost = %5d\n",  -Vec_IntEntry(vUnatePairsW[n], pPerm[i]) );
                }
            }
            for ( i = 0; i < Vec_IntSize(vUnatePairs[n]); i++ )
                pPerm[i] = Vec_IntEntry(vUnatePairs[n], pPerm[i]);
            for ( i = 0; i < Vec_IntSize(vUnatePairs[n]); i++ )
                vUnatePairs[n]->pArray[i] = pPerm[i];
            ABC_FREE( pPerm );
        }
}


/**Function*************************************************************

  Synopsis    [Perform resubstitution.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManResubPerform_rec( Gia_ResbMan_t * p, int nLimit )
{
    int TopOneW[2] = {0}, TopTwoW[2] = {0}, Max1, Max2, iResLit, nVars = Vec_PtrSize(p->vDivs);
    if ( p->fVerbose )
    {
        printf( "\nCalling decomposition for ISF: " ); 
        printf( "OFF = %5d (%6.2f %%)  ", Abc_TtCountOnesVec(p->pSets[0], p->nWords), 100.0*Abc_TtCountOnesVec(p->pSets[0], p->nWords)/(64*p->nWords) );
        printf( "ON = %5d (%6.2f %%)\n",  Abc_TtCountOnesVec(p->pSets[1], p->nWords), 100.0*Abc_TtCountOnesVec(p->pSets[1], p->nWords)/(64*p->nWords) );
    }
    if ( Abc_TtIsConst0( p->pSets[1], p->nWords ) )
        return 0;
    if ( Abc_TtIsConst0( p->pSets[0], p->nWords ) )
        return 1;
    iResLit = Gia_ManFindOneUnate( p->pSets, p->vDivs, p->nWords, p->vUnateLits, p->vNotUnateVars, p->fVerbose );
    if ( iResLit >= 0 ) // buffer
        return iResLit;
    if ( nLimit == 0 )
        return -1;
    iResLit = Gia_ManFindTwoUnate( p->pSets, p->vDivs, p->nWords, p->vUnateLits, p->fVerbose );
    if ( iResLit >= 0 ) // and
    {
        int iNode = nVars + Vec_IntSize(p->vGates)/2;
        int fComp = Abc_LitIsCompl(iResLit);
        int iDiv0 = Abc_Lit2Var(iResLit) & 0x7FFF;
        int iDiv1 = Abc_Lit2Var(iResLit) >> 15;
        assert( iDiv0 < iDiv1 );
        Vec_IntPushTwo( p->vGates, iDiv0, iDiv1 );
        return Abc_Var2Lit( iNode, fComp );
    }
    Vec_IntTwoFindCommon( p->vNotUnateVars[0], p->vNotUnateVars[1], p->vBinateVars );
    if ( Vec_IntSize(p->vBinateVars) > 1000 )
    {
        printf( "Reducing binate divs from %d to 1000.\n", Vec_IntSize(p->vBinateVars) );
        Vec_IntShrink( p->vBinateVars, 1000 );
    }
    iResLit = Gia_ManFindXor( p->pSets, p->vDivs, p->nWords, p->vBinateVars, p->vUnatePairs, p->fVerbose );
    if ( iResLit >= 0 ) // xor
    {
        int iNode = nVars + Vec_IntSize(p->vGates)/2;
        int fComp = Abc_LitIsCompl(iResLit);
        int iDiv0 = Abc_Lit2Var(iResLit) & 0x7FFF;
        int iDiv1 = Abc_Lit2Var(iResLit) >> 15;
        assert( !Abc_LitIsCompl(iDiv0) );
        assert( !Abc_LitIsCompl(iDiv1) );
        assert( iDiv0 > iDiv1 );
        Vec_IntPushTwo( p->vGates, iDiv0, iDiv1 );
        return Abc_Var2Lit( iNode, fComp );
    }
    if ( nLimit == 1 )
        return -1;
    Gia_ManFindUnatePairs( p->pSets, p->vDivs, p->nWords, p->vBinateVars, p->vUnatePairs, p->fVerbose );
    iResLit = Gia_ManFindDivGate( p->pSets, p->vDivs, p->nWords, p->vUnateLits, p->vUnatePairs, p->pDivA );
    if ( iResLit >= 0 ) // and(div,pair)
    {
        int iNode  = nVars + Vec_IntSize(p->vGates)/2;

        int fComp  = Abc_LitIsCompl(iResLit);
        int iDiv0  = Abc_Lit2Var(iResLit) & 0x7FFF; // div
        int iDiv1  = Abc_Lit2Var(iResLit) >> 15;    // pair

        int Div1   = Vec_IntEntry( p->vUnatePairs[!fComp], Abc_Lit2Var(iDiv1) );
        int fComp1 = Abc_LitIsCompl(Div1) ^ Abc_LitIsCompl(iDiv1);
        int iDiv10 = Abc_Lit2Var(Div1) & 0x7FFF;
        int iDiv11 = Abc_Lit2Var(Div1) >> 15;   

        Vec_IntPushTwo( p->vGates, iDiv10, iDiv11 );
        Vec_IntPushTwo( p->vGates, iDiv0, Abc_Var2Lit(iNode, fComp1) );
        return Abc_Var2Lit( iNode+1, fComp );
    }
    if ( nLimit == 2 )
        return -1;
    iResLit = Gia_ManFindGateGate( p->pSets, p->vDivs, p->nWords, p->vUnatePairs, p->pDivA, p->pDivB );
    if ( iResLit >= 0 ) // and(pair,pair)
    {
        int iNode  = nVars + Vec_IntSize(p->vGates)/2;

        int fComp  = Abc_LitIsCompl(iResLit);
        int iDiv0  = Abc_Lit2Var(iResLit) & 0x7FFF; // pair
        int iDiv1  = Abc_Lit2Var(iResLit) >> 15;    // pair

        int Div0   = Vec_IntEntry( p->vUnatePairs[!fComp], Abc_Lit2Var(iDiv0) );
        int fComp0 = Abc_LitIsCompl(Div0) ^ Abc_LitIsCompl(iDiv0);
        int iDiv00 = Abc_Lit2Var(Div0) & 0x7FFF;
        int iDiv01 = Abc_Lit2Var(Div0) >> 15;   
        
        int Div1   = Vec_IntEntry( p->vUnatePairs[!fComp], Abc_Lit2Var(iDiv1) );
        int fComp1 = Abc_LitIsCompl(Div1) ^ Abc_LitIsCompl(iDiv1);
        int iDiv10 = Abc_Lit2Var(Div1) & 0x7FFF;
        int iDiv11 = Abc_Lit2Var(Div1) >> 15;   
        
        Vec_IntPushTwo( p->vGates, iDiv00, iDiv01 );
        Vec_IntPushTwo( p->vGates, iDiv10, iDiv11 );
        Vec_IntPushTwo( p->vGates, Abc_Var2Lit(iNode, fComp0), Abc_Var2Lit(iNode+1, fComp1) );
        return Abc_Var2Lit( iNode+2, fComp );
    }
    if ( nLimit == 3 )
        return -1;
    if ( Vec_IntSize(p->vUnateLits[0]) + Vec_IntSize(p->vUnateLits[1]) + Vec_IntSize(p->vUnatePairs[0]) + Vec_IntSize(p->vUnatePairs[1]) == 0 )
        return -1;
    Gia_ManComputeLitWeights( p->pSets, p->vDivs, p->nWords, p->vUnateLits, p->vUnateLitsW, TopOneW, p->fVerbose );
    Gia_ManComputePairWeights( p->pSets, p->vDivs, p->nWords, p->vUnatePairs, p->vUnatePairsW, TopTwoW, p->fVerbose );
    Max1 = Abc_MaxInt(TopOneW[0], TopOneW[1]);
    Max2 = Abc_MaxInt(TopTwoW[0], TopTwoW[1]);
    if ( Abc_MaxInt(Max1, Max2) == 0 )
        return -1;
    if ( Max1 > Max2/2 )
    {
        if ( Max1 == TopOneW[0] || Max1 == TopOneW[1] )
        {
            int fUseOr  = Max1 == TopOneW[0];
            int iDiv    = Vec_IntEntry( p->vUnateLits[!fUseOr], 0 );
            int fComp   = Abc_LitIsCompl(iDiv);
            word * pDiv = (word *)Vec_PtrEntry( p->vDivs, Abc_Lit2Var(iDiv) );
            Abc_TtAndSharp( p->pSets[fUseOr], p->pSets[fUseOr], pDiv, p->nWords, !fComp );
            iResLit = Gia_ManResubPerform_rec( p, nLimit-1 );
            if ( iResLit >= 0 ) 
            {
                int iNode = nVars + Vec_IntSize(p->vGates)/2;
                Vec_IntPushTwo( p->vGates, Abc_LitNot(iDiv), Abc_LitNotCond(iResLit, fUseOr) );
                return Abc_Var2Lit( iNode, fUseOr );
            }
        }
        if ( Max2 == 0 )
            return -1;
        if ( Max2 == TopTwoW[0] || Max2 == TopTwoW[1] )
        {
            int fUseOr  = Max2 == TopTwoW[0];
            int iDiv    = Vec_IntEntry( p->vUnatePairs[!fUseOr], 0 );
            int fComp   = Abc_LitIsCompl(iDiv);
            Gia_ManDeriveDivPair( iDiv, p->vDivs, p->nWords, p->pDivA );
            Abc_TtAndSharp( p->pSets[fUseOr], p->pSets[fUseOr], p->pDivA, p->nWords, !fComp );
            iResLit = Gia_ManResubPerform_rec( p, nLimit-2 );
            if ( iResLit >= 0 ) 
            {
                int iNode = nVars + Vec_IntSize(p->vGates)/2;
                int iDiv0 = Abc_Lit2Var(iDiv) & 0x7FFF;   
                int iDiv1 = Abc_Lit2Var(iDiv) >> 15;      
                Vec_IntPushTwo( p->vGates, iDiv0, iDiv1 );
                Vec_IntPushTwo( p->vGates, Abc_LitNotCond(iResLit, fUseOr), Abc_Var2Lit(iNode, !fComp) );
                return Abc_Var2Lit( iNode+1, fUseOr );
            }
        }
    }
    else
    {
        if ( Max2 == TopTwoW[0] || Max2 == TopTwoW[1] )
        {
            int fUseOr  = Max2 == TopTwoW[0];
            int iDiv    = Vec_IntEntry( p->vUnatePairs[!fUseOr], 0 );
            int fComp   = Abc_LitIsCompl(iDiv);
            Gia_ManDeriveDivPair( iDiv, p->vDivs, p->nWords, p->pDivA );
            Abc_TtAndSharp( p->pSets[fUseOr], p->pSets[fUseOr], p->pDivA, p->nWords, !fComp );
            iResLit = Gia_ManResubPerform_rec( p, nLimit-2 );
            if ( iResLit >= 0 ) 
            {
                int iNode = nVars + Vec_IntSize(p->vGates)/2;
                int iDiv0 = Abc_Lit2Var(iDiv) & 0x7FFF;   
                int iDiv1 = Abc_Lit2Var(iDiv) >> 15;      
                Vec_IntPushTwo( p->vGates, iDiv0, iDiv1 );
                Vec_IntPushTwo( p->vGates, Abc_LitNotCond(iResLit, fUseOr), Abc_Var2Lit(iNode, !fComp) );
                return Abc_Var2Lit( iNode+1, fUseOr );
            }
        }
        if ( Max1 == 0 )
            return -1;
        if ( Max1 == TopOneW[0] || Max1 == TopOneW[1] )
        {
            int fUseOr  = Max1 == TopOneW[0];
            int iDiv    = Vec_IntEntry( p->vUnateLits[!fUseOr], 0 );
            int fComp   = Abc_LitIsCompl(iDiv);
            word * pDiv = (word *)Vec_PtrEntry( p->vDivs, Abc_Lit2Var(iDiv) );
            Abc_TtAndSharp( p->pSets[fUseOr], p->pSets[fUseOr], pDiv, p->nWords, !fComp );
            iResLit = Gia_ManResubPerform_rec( p, nLimit-1 );
            if ( iResLit >= 0 ) 
            {
                int iNode = nVars + Vec_IntSize(p->vGates)/2;
                Vec_IntPushTwo( p->vGates, Abc_LitNot(iDiv), Abc_LitNotCond(iResLit, fUseOr) );
                return Abc_Var2Lit( iNode, fUseOr );
            }
        }
    }
    return -1;
}
void Gia_ManResubPerform( Gia_ResbMan_t * p, Vec_Ptr_t * vDivs, int nWords, int nLimit, int fDebug, int fVerbose )
{
    int Res;
    Gia_ResbInit( p, vDivs, nWords, nLimit, fDebug, fVerbose );
    Res = Gia_ManResubPerform_rec( p, nLimit );
    if ( Res >= 0 )
        Vec_IntPush( p->vGates, Res );
}

/**Function*************************************************************

  Synopsis    [Top level.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_ResbMan_t * s_pResbMan = NULL;

void Abc_ResubPrepareManager( int nWords )
{
    if ( s_pResbMan != NULL )
        Gia_ResbFree( s_pResbMan );
    if ( nWords > 0 )
        s_pResbMan = Gia_ResbAlloc( nWords );
}

int Abc_ResubComputeFunction( void ** ppDivs, int nDivs, int nWords, int nLimit, int fDebug, int fVerbose, int ** ppArray )
{
    Vec_Ptr_t Divs = { nDivs, nDivs, ppDivs };
    assert( s_pResbMan != NULL ); // first call Abc_ResubPrepareManager()
    Gia_ManResubPerform( s_pResbMan, &Divs, nWords, nLimit, fDebug, 0 );
    if ( fVerbose )
    {
        Gia_ManResubPrint( s_pResbMan->vGates, nDivs );
        printf( "\n" );
    }
    if ( fDebug )
    {
        if ( !Gia_ManResubVerify(s_pResbMan) )
        {
            Gia_ManResubPrint( s_pResbMan->vGates, nDivs );
            printf( "Verification FAILED.\n" );
        }
        //else
        //    printf( "Verification succeeded.\n" );
    }
    *ppArray = Vec_IntArray(s_pResbMan->vGates);
    assert( Vec_IntSize(s_pResbMan->vGates)/2 <= nLimit );
    return Vec_IntSize(s_pResbMan->vGates);
}

void Abc_ResubDumpProblem( char * pFileName, void ** ppDivs, int nDivs, int nWords )
{
    Vec_Wrd_t * vSims = Vec_WrdAlloc( nDivs * nWords );
    word ** pDivs = (word **)ppDivs;
    int d, w;
    for ( d = 0; d < nDivs;  d++ )
    for ( w = 0; w < nWords; w++ )
        Vec_WrdPush( vSims, pDivs[d][w] );
    Gia_ManSimPatWrite( pFileName, vSims, nWords );
    Vec_WrdFree( vSims );
}

/**Function*************************************************************

  Synopsis    [Top level.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

extern void Extra_PrintHex( FILE * pFile, unsigned * pTruth, int nVars );
extern void Dau_DsdPrintFromTruth2( word * pTruth, int nVarsInit );

void Gia_ManResubTest3()
{
    int nVars = 3;
    int fVerbose = 1;
    word Divs[6] = { 0, 0, 
        ABC_CONST(0xAAAAAAAAAAAAAAAA),
        ABC_CONST(0xCCCCCCCCCCCCCCCC),
        ABC_CONST(0xF0F0F0F0F0F0F0F0),
        ABC_CONST(0xFF00FF00FF00FF00) 
    };
    Vec_Ptr_t * vDivs = Vec_PtrAlloc( 6 );
    Vec_Int_t * vRes = Vec_IntAlloc( 100 );
    int i, k, ArraySize, * pArray; 
    for ( i = 0; i < 6; i++ )
        Vec_PtrPush( vDivs, Divs+i );
    Abc_ResubPrepareManager( 1 );
    for ( i = 0; i < (1<<(1<<nVars)); i++ )
    {
        word Truth = Abc_Tt6Stretch( i, nVars );
        Divs[0] = ~Truth;
        Divs[1] =  Truth;
        printf( "%3d : ", i );
        Extra_PrintHex( stdout, (unsigned*)&Truth, nVars );
        printf( " " );
        Dau_DsdPrintFromTruth2( &Truth, nVars );
        printf( "           " );

        //Abc_ResubDumpProblem( "temp.resub", (void **)Vec_PtrArray(vDivs), Vec_PtrSize(vDivs), 1 );
        ArraySize = Abc_ResubComputeFunction( (void **)Vec_PtrArray(vDivs), Vec_PtrSize(vDivs), 1, 4, 1, fVerbose, &pArray );
        if ( !fVerbose )
            printf( "\n" );

        Vec_IntClear( vRes );
        for ( k = 0; k < ArraySize; k++ )
            Vec_IntPush( vRes, pArray[k] );

        if ( i == 1000 )
            break;
    }
    Abc_ResubPrepareManager( 0 );
    Vec_IntFree( vRes );
    Vec_PtrFree( vDivs );
}
void Gia_ManResubTest3_()
{
    Gia_ResbMan_t * p = Gia_ResbAlloc( 1 );
    word Divs[6] = { 0, 0, 
        ABC_CONST(0xAAAAAAAAAAAAAAAA),
        ABC_CONST(0xCCCCCCCCCCCCCCCC),
        ABC_CONST(0xF0F0F0F0F0F0F0F0),
        ABC_CONST(0xFF00FF00FF00FF00) 
    };
    Vec_Ptr_t * vDivs = Vec_PtrAlloc( 6 );
    Vec_Int_t * vRes = Vec_IntAlloc( 100 );
    int i; 
    for ( i = 0; i < 6; i++ )
        Vec_PtrPush( vDivs, Divs+i );

    {
        word Truth = (Divs[2] | Divs[3]) & (Divs[4] & Divs[5]);
//        word Truth = (~Divs[2] | Divs[3]) | ~Divs[4];
        Divs[0] = ~Truth;
        Divs[1] =  Truth;
        Extra_PrintHex( stdout, (unsigned*)&Truth, 6 );
        printf( " " );
        Dau_DsdPrintFromTruth2( &Truth, 6 );
        printf( "       " );
        Gia_ManResubPerform( p, vDivs, 1, 100, 1, 0 );
    }
    Gia_ResbFree( p );
    Vec_IntFree( vRes );
    Vec_PtrFree( vDivs );
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
    int nWords = 0;
    Gia_Man_t * pMan   = NULL;
    Vec_Wrd_t * vSims  = Gia_ManSimPatRead( pFileName, &nWords );
    Vec_Ptr_t * vDivs  = vSims ? Gia_ManDeriveDivs( vSims, nWords ) : NULL;
    Gia_ResbMan_t * p = Gia_ResbAlloc( nWords );
//    Gia_ManCheckResub( vDivs, nWords );
    if ( Vec_PtrSize(vDivs) >= (1<<14) )
    {
        printf( "Reducing all divs from %d to %d.\n", Vec_PtrSize(vDivs), (1<<14)-1 );
        Vec_PtrShrink( vDivs, (1<<14)-1 );
    }
    assert( Vec_PtrSize(vDivs) < (1<<14) );
    Gia_ManResubPerform( p, vDivs, nWords, 100, 1, 1 );
    if ( Vec_IntSize(p->vGates) )
        pMan = Gia_ManConstructFromGates( p->vGates, Vec_PtrSize(vDivs) );
    else
        printf( "Decomposition did not succeed.\n" );
    Gia_ResbFree( p );
    Vec_PtrFree( vDivs );
    Vec_WrdFree( vSims );
    return pMan;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

