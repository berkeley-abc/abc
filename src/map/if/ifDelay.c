/**CFile****************************************************************

  FileName    [ifDelay.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [Delay balancing for cut functions.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: ifDelay.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "if.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define IF_MAX_CUBES 70

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////
 
/**Function*************************************************************

  Synopsis    [Computes the SOP delay using balanced AND decomposition.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int If_CutMaxCubeSize( Vec_Int_t * vCover, int nVars )
{
    int i, k, Entry, Literal, Count, CountMax = 0;
    Vec_IntForEachEntry( vCover, Entry, i )
    {
        Count = 0;
        for ( k = 0; k < nVars; k++ )
        {
            Literal = (3 & (Entry >> (k << 1)));
            if ( Literal == 1 || Literal == 2 )
                Count++;
        }
        CountMax = Abc_MaxInt( CountMax, Count );
    }
    return CountMax;
}
int If_CutDelaySop( If_Man_t * p, If_Cut_t * pCut )
{
    // delay is calculated using 1+log2(NumFanins)
    static double GateDelays[20] = { 1.00, 1.00, 2.00, 2.58, 3.00, 3.32, 3.58, 3.81, 4.00, 4.17, 4.32, 4.46, 4.58, 4.70, 4.81, 4.91, 5.00, 5.09, 5.17, 5.25 };
    Vec_Int_t * vCover;
    If_Obj_t * pLeaf;
    int i, nLitMax, Delay, DelayMax;
    // mark cut as a user cut
    pCut->fUser = 1;
    if ( pCut->nLeaves == 0 )
        return 0;
    if ( pCut->nLeaves == 1 )
        return (int)If_ObjCutBest(If_CutLeaf(p, pCut, 0))->Delay;
    vCover = Vec_WecEntry( p->vTtIsops[pCut->nLeaves], Abc_Lit2Var(If_CutTruthLit(pCut)) );
    if ( Vec_IntSize(vCover) == 0 )
        return -1;
    // mark the output as complemented
//    vAnds = If_CutDelaySopAnds( p, pCut, p->vCover, RetValue ^ pCut->fCompl );
    if ( Vec_IntSize(p->vCover) > p->pPars->nGateSize )
        return ABC_INFINITY;
    // set the area cost
    assert( If_CutLeaveNum(pCut) >= 0 && If_CutLeaveNum(pCut) <= 16 );
    // compute the gate delay
    nLitMax = If_CutMaxCubeSize( p->vCover, If_CutLeaveNum(pCut) );
    if ( Vec_IntSize(p->vCover) < 2 )
    {
        pCut->Cost = Vec_IntSize(p->vCover);
        Delay = (int)(GateDelays[If_CutLeaveNum(pCut)] + 0.5);
        DelayMax = 0;
        If_CutForEachLeaf( p, pCut, pLeaf, i )
            DelayMax = Abc_MaxInt( DelayMax, If_ObjCutBest(pLeaf)->Delay + (pCut->pPerm[i] = (char)Delay) );
    }
    else
    {
        pCut->Cost = Vec_IntSize(p->vCover) + 1;
        Delay = (int)(GateDelays[If_CutLeaveNum(pCut)] + GateDelays[nLitMax] + 0.5);
        DelayMax = 0;
        If_CutForEachLeaf( p, pCut, pLeaf, i )
            DelayMax = Abc_MaxInt( DelayMax, If_ObjCutBest(pLeaf)->Delay + (pCut->pPerm[i] = (char)Delay) );
    }
    return DelayMax;
}


/**Function*************************************************************

  Synopsis    [Naive implementation of log-counter.]

  Description [Incrementally computes [log2(SUMi(2^di)).]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int If_LogCounter64Eval( word Count )
{
    int n = ((Count & (Count - 1)) > 0) ? -1 : 0;
    assert( Count > 0 );
    if ( (Count & ABC_CONST(0xFFFFFFFF00000000)) == 0 ) { n += 32; Count <<= 32; }
    if ( (Count & ABC_CONST(0xFFFF000000000000)) == 0 ) { n += 16; Count <<= 16; }
    if ( (Count & ABC_CONST(0xFF00000000000000)) == 0 ) { n +=  8; Count <<=  8; }
    if ( (Count & ABC_CONST(0xF000000000000000)) == 0 ) { n +=  4; Count <<=  4; }
    if ( (Count & ABC_CONST(0xC000000000000000)) == 0 ) { n +=  2; Count <<=  2; }
    if ( (Count & ABC_CONST(0x8000000000000000)) == 0 ) { n++; }
    return 63 - n;
}
static word If_LogCounter64Add( word Count, int Num )
{
    assert( Num < 48 );
    return Count + (((word)1) << Num);
}

/**Function*************************************************************

  Synopsis    [Implementation of log-counter.]

  Description [Incrementally computes [log2(SUMi(2^di)).
  Supposed to work correctly up to 16 entries.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int If_LogCounter32Eval( unsigned Count, int Start )
{
    int n = (Abc_LitIsCompl(Start) || (Count & (Count - 1)) > 0) ? -1 : 0;
    assert( Count > 0 );
    if ( (Count & 0xFFFF0000) == 0 ) { n += 16; Count <<= 16; }
    if ( (Count & 0xFF000000) == 0 ) { n +=  8; Count <<=  8; }
    if ( (Count & 0xF0000000) == 0 ) { n +=  4; Count <<=  4; }
    if ( (Count & 0xC0000000) == 0 ) { n +=  2; Count <<=  2; }
    if ( (Count & 0x80000000) == 0 ) { n++; }
    return Abc_Lit2Var(Start) + 31 - n;
}
static unsigned If_LogCounter32Add( unsigned Count, int * pStart, int Num )
{
    int Start = Abc_Lit2Var(*pStart);
    if ( Num < Start )
    {
        *pStart |= 1;
        return Count;
    }
    if ( Num > Start + 16 )
    {
        int Shift = Num - (Start + 16);
        if ( !Abc_LitIsCompl(*pStart) && (Shift >= 32 ? Count : Count & ~(~0 << Shift)) > 0 )
            *pStart |= 1;
        Count >>= Shift;
        Start += Shift;
        *pStart = Abc_Var2Lit( Start, Abc_LitIsCompl(*pStart) );
        assert( Num <= Start + 16 );
    }
    return Count + (1 << (Num-Start));
}

/**Function*************************************************************

  Synopsis    [Testing of the counter]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_LogCounterTest2()
{
    word Count64 = 0;

    unsigned Count = 0; 
    int Start = 0;

    int Result, Result64;

    Count = If_LogCounter32Add( Count, &Start, 39 );
    Count = If_LogCounter32Add( Count, &Start, 35 );
    Count = If_LogCounter32Add( Count, &Start, 35 );
    Count = If_LogCounter32Add( Count, &Start, 36 );
    Count = If_LogCounter32Add( Count, &Start, 37 );
    Count = If_LogCounter32Add( Count, &Start, 38 );
    Count = If_LogCounter32Add( Count, &Start, 40 );
    Count = If_LogCounter32Add( Count, &Start, 1 );
    Count = If_LogCounter32Add( Count, &Start, 41 );
    Count = If_LogCounter32Add( Count, &Start, 42 );

    Count64 = If_LogCounter64Add( Count64, 1 );
    Count64 = If_LogCounter64Add( Count64, 35 );
    Count64 = If_LogCounter64Add( Count64, 35 );
    Count64 = If_LogCounter64Add( Count64, 36 );
    Count64 = If_LogCounter64Add( Count64, 37 );
    Count64 = If_LogCounter64Add( Count64, 38 );
    Count64 = If_LogCounter64Add( Count64, 39 );
    Count64 = If_LogCounter64Add( Count64, 40 );
    Count64 = If_LogCounter64Add( Count64, 41 );
    Count64 = If_LogCounter64Add( Count64, 42 );

    Result = If_LogCounter32Eval( Count, Start );
    Result64 = If_LogCounter64Eval( Count64 );

    printf( "%d  %d\n", Result, Result64 );
}

/**Function*************************************************************

  Synopsis    [Adds the number to the numbers stored.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int If_LogCounterAdd( int * pTimes, int * pnTimes, int Num, int fXor )
{
    int nTimes = *pnTimes;
    pTimes[nTimes++] = Num;
    if ( nTimes > 1 )
    {
        int i, k;
        for ( k = nTimes-1; k > 0; k-- )
        {
            if ( pTimes[k] < pTimes[k-1] )
                break;
            if ( pTimes[k] > pTimes[k-1] )
            { 
                ABC_SWAP( int, pTimes[k], pTimes[k-1] ); 
                continue; 
            }
            pTimes[k-1] += 1 + fXor;
            for ( nTimes--, i = k; i < nTimes; i++ )
                pTimes[i] = pTimes[i+1];
        }
    }
    assert( nTimes > 0 );
    *pnTimes = nTimes;
    return pTimes[0] + (nTimes > 1 ? 1 + fXor : 0);
}

/**Function*************************************************************

  Synopsis    [Testing of the counter]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_LogCounterTest()
{
    int pArray[10] = { 1, 2, 4, 5, 6, 3, 1 };
    int i, nSize = 4;

    word Count64 = 0;
    int Result, Result64;

    int pTimes[100];
    int nTimes = 0;

    for ( i = 0; i < nSize; i++ )
        Count64 = If_LogCounter64Add( Count64, pArray[i] );
    Result64 = If_LogCounter64Eval( Count64 );

    for ( i = 0; i < nSize; i++ )
        Result = If_LogCounterAdd( pTimes, &nTimes, pArray[i], 0 );

    printf( "%d  %d\n", Result64, Result );
}

/**Function*************************************************************

  Synopsis    [Inserts the entry while sorting them by delay.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
word If_AigVerifyArray( Vec_Int_t * vAig, int nLeaves, int fCompl )
{
    assert( Vec_IntSize(vAig) > 0 );
    assert( Vec_IntEntryLast(vAig) < 2 );
    if ( Vec_IntSize(vAig) == 1 ) // const
        return Vec_IntEntry(vAig, 0) ? ~((word)0) : 0;
    if ( Vec_IntSize(vAig) == 2 ) // variable
    {
        assert( Vec_IntEntry(vAig, 0) == 0 );
        return Vec_IntEntry(vAig, 1) ? ~s_Truths6[0] : s_Truths6[0];
    }
    else
    {
        word Truth0 = 0, Truth1 = 0, TruthR;
        int i, iVar0, iVar1, iLit0, iLit1;
        assert( Vec_IntSize(vAig) & 1 );
        Vec_IntForEachEntryDouble( vAig, iLit0, iLit1, i )
        {
            iVar0 = Abc_Lit2Var( iLit0 );
            iVar1 = Abc_Lit2Var( iLit1 );
            Truth0 = iVar0 < nLeaves ? s_Truths6[iVar0] : Vec_WrdEntry( (Vec_Wrd_t *)vAig, iVar0 - nLeaves );
            Truth1 = iVar1 < nLeaves ? s_Truths6[iVar1] : Vec_WrdEntry( (Vec_Wrd_t *)vAig, iVar1 - nLeaves );
            if ( Abc_LitIsCompl(iLit0) )
                Truth0 = ~Truth0;
            if ( Abc_LitIsCompl(iLit1) )
                Truth1 = ~Truth1;
            assert( (i & 1) == 0 );
            Vec_WrdWriteEntry( (Vec_Wrd_t *)vAig, Abc_Lit2Var(i), Truth0 & Truth1 );  // overwriting entries
        }
        assert( i == Vec_IntSize(vAig) - 1 );
        TruthR = Truth0 & Truth1;
        if ( Vec_IntEntry(vAig, i) ^ fCompl )
            TruthR = ~TruthR;
        Vec_IntClear( vAig ); // useless
        return TruthR;
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int If_LogCreateAnd( Vec_Int_t * vAig, int iLit0, int iLit1, int nSuppAll )
{
    int iObjId = Vec_IntSize(vAig)/2 + nSuppAll;
    Vec_IntPush( vAig, iLit0 );
    Vec_IntPush( vAig, iLit1 );
    return Abc_Var2Lit( iObjId, 0 );
}
static inline int If_LogCreateMux( Vec_Int_t * vAig, int iLitC, int iLit1, int iLit0, int nSuppAll )
{
    int iFanLit0 = If_LogCreateAnd( vAig, iLitC, iLit1, nSuppAll );
    int iFanLit1 = If_LogCreateAnd( vAig, Abc_LitNot(iLitC), iLit0, nSuppAll );
    int iResLit  = If_LogCreateAnd( vAig, Abc_LitNot(iFanLit0), Abc_LitNot(iFanLit1), nSuppAll );
    return Abc_LitNot(iResLit);
}
static inline int If_LogCreateXor( Vec_Int_t * vAig, int iLit0, int iLit1, int nSuppAll )
{
    return If_LogCreateMux( vAig, iLit0, Abc_LitNot(iLit1), iLit1, nSuppAll );
}
static inline int If_LogCreateAndXor( Vec_Int_t * vAig, int iLit0, int iLit1, int nSuppAll, int fXor )
{
    return fXor ? If_LogCreateXor(vAig, iLit0, iLit1, nSuppAll) : If_LogCreateAnd(vAig, iLit0, iLit1, nSuppAll);
}
static inline int If_LogCreateAndXorMulti( Vec_Int_t * vAig, int * pFaninLits, int nFanins, int nSuppAll, int fXor )
{
    int i;
    assert( nFanins > 0 );
    for ( i = nFanins - 1; i > 0; i-- )
        pFaninLits[i-1] = If_LogCreateAndXor( vAig, pFaninLits[i], pFaninLits[i-1], nSuppAll, fXor );
    return pFaninLits[0];
}
static inline int If_LogCounterAddAig( int * pTimes, int * pnTimes, int * pFaninLits, int Num, int iLit, Vec_Int_t * vAig, int nSuppAll, int fXor )
{
    int nTimes = *pnTimes;
    if ( vAig )
        pFaninLits[nTimes] = iLit;
    pTimes[nTimes++] = Num;
    if ( nTimes > 1 )
    {
        int i, k;
        for ( k = nTimes-1; k > 0; k-- )
        {
            if ( pTimes[k] < pTimes[k-1] )
                break;
            if ( pTimes[k] > pTimes[k-1] )
            { 
                ABC_SWAP( int, pTimes[k], pTimes[k-1] ); 
                if ( vAig )
                    ABC_SWAP( int, pFaninLits[k], pFaninLits[k-1] ); 
                continue; 
            }
            pTimes[k-1] += 1 + fXor;
            if ( vAig )
                pFaninLits[k-1] = If_LogCreateAndXor( vAig, pFaninLits[k], pFaninLits[k-1], nSuppAll, fXor );
            for ( nTimes--, i = k; i < nTimes; i++ )
            {
                pTimes[i] = pTimes[i+1];
                if ( vAig )
                    pFaninLits[i] = pFaninLits[i+1];
            }
        }
    }
    assert( nTimes > 0 );
    *pnTimes = nTimes;
    return pTimes[0] + (nTimes > 1 ? 1 + fXor : 0);
}


/**Function*************************************************************

  Synopsis    [Compute delay/area profile of the structure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int  If_CutPinDelayGet( word D, int v )           { assert(v >= 0 && v < IF_MAX_FUNC_LUTSIZE); return (int)((D >> (v << 2)) & 0xF);                             }
static inline void If_CutPinDelaySet( word * pD, int v, int d ) { assert(v >= 0 && v < IF_MAX_FUNC_LUTSIZE); assert(d >= 0 && d < IF_MAX_FUNC_LUTSIZE); *pD |= ((word)d << (v << 2)); }
static inline word If_CutPinDelayInit( int v )                  { assert(v >= 0 && v < IF_MAX_FUNC_LUTSIZE); return (word)1 << (v << 2);                                      }
static inline word If_CutPinDelayMax( word D1, word D2, int nVars, int AddOn )
{
    int v, Max;
    word D = 0;
    for ( v = 0; v < nVars; v++ )
        if ( (Max = Abc_MaxInt(If_CutPinDelayGet(D1, v), If_CutPinDelayGet(D2, v))) )
            If_CutPinDelaySet( &D, v, Abc_MinInt(Max + AddOn, 15) );
    return D;
}
static inline word If_CutPinDelayDecrement( word D1, int nVars )
{
    int v;
    word D = 0;
    for ( v = 0; v < nVars; v++ )
        if ( If_CutPinDelayGet(D1, v) )
            If_CutPinDelaySet( &D, v, If_CutPinDelayGet(D1, v) - 1 );
    return D;
}
static inline int If_CutPinDelayEqual( word D1, word D2, int nVars ) // returns 1 if D1 has the same delays than D2
{
    int v;
    for ( v = 0; v < nVars; v++ )
        if ( If_CutPinDelayGet(D1, v) != If_CutPinDelayGet(D2, v) )
            return 0;
    return 1;
}
static inline int If_CutPinDelayDom( word D1, word D2, int nVars ) // returns 1 if D1 has the same or smaller delays than D2
{
    int v;
    for ( v = 0; v < nVars; v++ )
        if ( If_CutPinDelayGet(D1, v) > If_CutPinDelayGet(D2, v) )
            return 0;
    return 1;
}
static inline void If_CutPinDelayTranslate( word D, int nVars, char * pPerm ) // fills up the array
{
    int v, Delay;
    for ( v = 0; v < nVars; v++ )
    {
        Delay = If_CutPinDelayGet(D, v);
        assert( Delay > 1 );
        pPerm[v] = Delay - 1;
    }
}
static inline void If_CutPinDelayPrint( word D, int nVars )
{
    int v;
    printf( "Delay profile = {" );
    for ( v = 0; v < nVars; v++ )
        printf( " %d", If_CutPinDelayGet(D, v) );
    printf( " }\n" );
}
static inline int If_LogCounterPinDelays( int * pTimes, int * pnTimes, word * pPinDels, int Num, word PinDel, int nSuppAll, int fXor )
{
    int nTimes = *pnTimes;
    pPinDels[nTimes] = PinDel;
    pTimes[nTimes++] = Num;
    if ( nTimes > 1 )
    {
        int i, k;
        for ( k = nTimes-1; k > 0; k-- )
        {
            if ( pTimes[k] < pTimes[k-1] )
                break;
            if ( pTimes[k] > pTimes[k-1] )
            { 
                ABC_SWAP( int, pTimes[k], pTimes[k-1] ); 
                ABC_SWAP( word, pPinDels[k], pPinDels[k-1] ); 
                continue; 
            }
            pTimes[k-1] += 1 + fXor;
            pPinDels[k-1] = If_CutPinDelayMax( pPinDels[k], pPinDels[k-1], nSuppAll, 1 + fXor );
            for ( nTimes--, i = k; i < nTimes; i++ )
            {
                pTimes[i] = pTimes[i+1];
                pPinDels[i] = pPinDels[i+1];
            }
        }
    }
    assert( nTimes > 0 );
    *pnTimes = nTimes;
    return pTimes[0] + (nTimes > 1 ? 1 + fXor : 0);
}
static inline word If_LogPinDelaysMulti( word * pPinDels, int nFanins, int nSuppAll, int fXor )
{
    int i;
    assert( nFanins > 0 );
    for ( i = nFanins - 1; i > 0; i-- )
        pPinDels[i-1] = If_CutPinDelayMax( pPinDels[i], pPinDels[i-1], nSuppAll, 1 + fXor );
    return pPinDels[0];
}
int If_CutSopBalancePinDelaysInt( Vec_Int_t * vCover, int * pTimes, int nSuppAll, char * pPerm )
{
    word pPinDelsAnd[IF_MAX_FUNC_LUTSIZE], pPinDelsOr[IF_MAX_CUBES];
    int nCounterAnd, pCounterAnd[IF_MAX_FUNC_LUTSIZE];
    int nCounterOr,  pCounterOr[IF_MAX_CUBES];
    int i, k, Entry, Literal, Delay = 0;
    word ResAnd, ResOr;
    if ( Vec_IntSize(vCover) > IF_MAX_CUBES )
        return -1;
    nCounterOr = 0;
    Vec_IntForEachEntry( vCover, Entry, i )
    { 
        nCounterAnd = 0;
        for ( k = 0; k < nSuppAll; k++ )
        {
            Literal = 3 & (Entry >> (k << 1));
            if ( Literal == 1 || Literal == 2 ) // neg or pos literal
                Delay = If_LogCounterPinDelays( pCounterAnd, &nCounterAnd, pPinDelsAnd, pTimes[k], If_CutPinDelayInit(k), nSuppAll, 0 );
            else if ( Literal != 0 ) 
                assert( 0 );
        }
        assert( nCounterAnd > 0 );
        ResAnd = If_LogPinDelaysMulti( pPinDelsAnd, nCounterAnd, nSuppAll, 0 );
        Delay = If_LogCounterPinDelays( pCounterOr, &nCounterOr, pPinDelsOr, Delay, ResAnd, nSuppAll, 0 );
    }
    assert( nCounterOr > 0 );
    ResOr = If_LogPinDelaysMulti( pPinDelsOr, nCounterOr, nSuppAll, 0 );
    If_CutPinDelayTranslate( ResOr, nSuppAll, pPerm );
    return Delay;
}
int If_CutSopBalancePinDelays( If_Man_t * p, If_Cut_t * pCut, char * pPerm )
{
    if ( pCut->nLeaves == 0 ) // const
        return 0;
    if ( pCut->nLeaves == 1 ) // variable
    {
        pPerm[0] = 0;
        return (int)If_ObjCutBest(If_CutLeaf(p, pCut, 0))->Delay;
    }
    else
    {
        Vec_Int_t * vCover;
        int i, pTimes[IF_MAX_FUNC_LUTSIZE];
        vCover = Vec_WecEntry( p->vTtIsops[pCut->nLeaves], Abc_Lit2Var(If_CutTruthLit(pCut)) );
        if ( Vec_IntSize(vCover) == 0 )
            return -1;
        for ( i = 0; i < If_CutLeaveNum(pCut); i++ )
            pTimes[i] = (int)If_ObjCutBest(If_CutLeaf(p, pCut, i))->Delay; 
        return If_CutSopBalancePinDelaysInt( vCover, pTimes, If_CutLeaveNum(pCut), pPerm );
    }
}

/**Function*************************************************************

  Synopsis    [Evaluate delay using SOP balancing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CutSopBalanceEvalIntInt( Vec_Int_t * vCover, int * pTimes, Vec_Int_t * vAig, int * piRes, int nSuppAll, int * pArea )
{
    int nCounterAnd, pCounterAnd[IF_MAX_FUNC_LUTSIZE], pFaninLitsAnd[IF_MAX_FUNC_LUTSIZE];
    int nCounterOr,  pCounterOr[IF_MAX_CUBES],  pFaninLitsOr[IF_MAX_CUBES];
    int i, k, Entry, Literal, nLits, Delay = 0, iRes = 0;
    if ( Vec_IntSize(vCover) > IF_MAX_CUBES )
        return -1;
    nCounterOr = 0;
    Vec_IntForEachEntry( vCover, Entry, i )
    { 
        nCounterAnd = nLits = 0;
        for ( k = 0; k < nSuppAll; k++ )
        {
            Literal = 3 & (Entry >> (k << 1));
            if ( Literal == 1 ) // neg literal
                nLits++, Delay = If_LogCounterAddAig( pCounterAnd, &nCounterAnd, pFaninLitsAnd, pTimes[k], Abc_Var2Lit(k, 1), vAig, nSuppAll, 0 );
            else if ( Literal == 2 ) // pos literal
                nLits++, Delay = If_LogCounterAddAig( pCounterAnd, &nCounterAnd, pFaninLitsAnd, pTimes[k], Abc_Var2Lit(k, 0), vAig, nSuppAll, 0 );
            else if ( Literal != 0 ) 
                assert( 0 );
        }
        assert( nCounterAnd > 0 );
        assert( nLits > 0 );
        if ( vAig )
            iRes = If_LogCreateAndXorMulti( vAig, pFaninLitsAnd, nCounterAnd, nSuppAll, 0 );
        else
            *pArea += nLits == 1 ? 0 : nLits - 1;
        Delay = If_LogCounterAddAig( pCounterOr, &nCounterOr, pFaninLitsOr, Delay, Abc_LitNot(iRes), vAig, nSuppAll, 0 );
    }
    assert( nCounterOr > 0 );
    if ( vAig )
        *piRes = Abc_LitNot( If_LogCreateAndXorMulti( vAig, pFaninLitsOr, nCounterOr, nSuppAll, 0 ) );
    else       
        *pArea += Vec_IntSize(vCover) == 1 ? 0 : Vec_IntSize(vCover) - 1;
    return Delay;
}
int If_CutSopBalanceEvalInt( Vec_Int_t * vCover, int nLeaves, int * pTimes, Vec_Int_t * vAig, int fCompl, int * pArea ) 
{
    int iRes = 0, Res;
    if ( Vec_IntSize(vCover) == 0 )
        return -1;
    Res = If_CutSopBalanceEvalIntInt( vCover, pTimes, vAig, &iRes, nLeaves, pArea );
    if ( Res == -1 )
        return -1;
    assert( vAig == NULL || Abc_Lit2Var(iRes) == nLeaves + Abc_Lit2Var(Vec_IntSize(vAig)) - 1 );
    if ( vAig )
        Vec_IntPush( vAig, Abc_LitIsCompl(iRes) ^ fCompl );
    assert( vAig == NULL || (Vec_IntSize(vAig) & 1) );
    return Res;
}
int If_CutSopBalanceEval( If_Man_t * p, If_Cut_t * pCut, Vec_Int_t * vAig )
{
    pCut->fUser = 1;
    if ( vAig )
        Vec_IntClear( vAig );
    if ( pCut->nLeaves == 0 ) // const
    {
        assert( Abc_Lit2Var(If_CutTruthLit(pCut)) == 0 );
        if ( vAig )
            Vec_IntPush( vAig, Abc_LitIsCompl(If_CutTruthLit(pCut)) );
        return 0;
    }
    if ( pCut->nLeaves == 1 ) // variable
    {
        assert( Abc_Lit2Var(If_CutTruthLit(pCut)) == 1 );
        if ( vAig )
            Vec_IntPush( vAig, 0 );
        if ( vAig )
            Vec_IntPush( vAig, Abc_LitIsCompl(If_CutTruthLit(pCut)) );
        return (int)If_ObjCutBest(If_CutLeaf(p, pCut, 0))->Delay;
    }
    else
    {
        Vec_Int_t * vCover = Vec_WecEntry( p->vTtIsops[pCut->nLeaves], Abc_Lit2Var(If_CutTruthLit(pCut)) );
        int fCompl = Abc_LitIsCompl(If_CutTruthLit(pCut)) ^ ((vCover->nCap >> 16) & 1); // hack to remember complemented attribute
        int Delay, Area = 0;
        int i, pTimes[IF_MAX_FUNC_LUTSIZE];
        for ( i = 0; i < If_CutLeaveNum(pCut); i++ )
            pTimes[i] = (int)If_ObjCutBest(If_CutLeaf(p, pCut, i))->Delay; 
        Delay = If_CutSopBalanceEvalInt( vCover, If_CutLeaveNum(pCut), pTimes, vAig, fCompl, &Area );
        pCut->Cost = Area;
        return Delay;
    }
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

