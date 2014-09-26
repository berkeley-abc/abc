/**CFile****************************************************************

  FileName    [wlcBlast.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Verilog parser.]

  Synopsis    [Bit-blasting.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 22, 2014.]

  Revision    [$Id: wlcBlast.c,v 1.00 2014/09/12 00:00:00 alanmi Exp $]

***********************************************************************/

#include "wlc.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Helper functions.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Wlc_NtkPrepareBits( Wlc_Ntk_t * p )
{
    Wlc_Obj_t * pObj;
    int i, nBits = 0;
    Wlc_NtkCleanCopy( p );
    Wlc_NtkForEachObj( p, pObj, i )
    {
        Wlc_ObjSetCopy( p, i, nBits );
        nBits += Wlc_ObjRange(pObj);
    }
    return nBits;
}
int * Wlc_VecCopy( Vec_Int_t * vOut, int * pArray, int nSize )
{
    int i; Vec_IntClear( vOut );
    for( i = 0; i < nSize; i++) 
        Vec_IntPush( vOut, pArray[i] );
    return Vec_IntArray( vOut );
}
int * Wlc_VecLoadFanins( Vec_Int_t * vOut, int * pFanins, int nFanins, int nTotal, int fSigned )
{
    int Fill = fSigned ? pFanins[nFanins-1] : 0;
    int i; Vec_IntClear( vOut );
    assert( nFanins <= nTotal );
    for( i = 0; i < nTotal; i++) 
        Vec_IntPush( vOut, i < nFanins ? pFanins[i] : Fill );
    return Vec_IntArray( vOut );
}
int Wlc_BlastGetConst( int * pNum, int nNum )
{
    int i, Res = 0;
    for ( i = 0; i < nNum; i++ )
        if ( pNum[i] == 1 )
            Res |= (1 << i);
        else if ( pNum[i] != 0 )
            return -1;
    return Res;
}
int Wlc_NtkMuxTree_rec( Gia_Man_t * pNew, int * pCtrl, int nCtrl, Vec_Int_t * vData, int Shift )
{
    int iLit0, iLit1;
    if ( nCtrl == 0 )
        return Vec_IntEntry( vData, Shift );
    iLit0 = Wlc_NtkMuxTree_rec( pNew, pCtrl, nCtrl-1, vData, Shift );
    iLit1 = Wlc_NtkMuxTree_rec( pNew, pCtrl, nCtrl-1, vData, Shift + (1<<(nCtrl-1)) );
    return Gia_ManHashMux( pNew, pCtrl[nCtrl-1], iLit1, iLit0 );
}

/**Function*************************************************************

  Synopsis    [Bit blasting for specific operations.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Wlc_BlastShiftRight( Gia_Man_t * pNew, int * pNum, int nNum, int * pShift, int nShift, int fSticky, Vec_Int_t * vRes )
{
    int * pRes = Wlc_VecCopy( vRes, pNum, nNum );
    int Fill = fSticky ? pNum[nNum-1] : 0;
    int i, j, fShort = 0;
    assert( nShift <= 32 );
    for( i = 0; i < nShift; i++ ) 
        for( j = 0; j < nNum - fSticky; j++ ) 
        {
            if( fShort || j + (1<<i) >= nNum ) 
            {
                pRes[j] = Gia_ManHashMux( pNew, pShift[i], Fill, pRes[j] );
                if ( (1<<i) > nNum ) 
                    fShort = 1;
            } 
            else 
                pRes[j] = Gia_ManHashMux( pNew, pShift[i], pRes[j+(1<<i)], pRes[j] );
        }
}
void Wlc_BlastShiftLeft( Gia_Man_t * pNew, int * pNum, int nNum, int * pShift, int nShift, int fSticky, Vec_Int_t * vRes )
{
    int * pRes = Wlc_VecCopy( vRes, pNum, nNum );
    int Fill = fSticky ? pNum[0] : 0;
    int i, j, fShort = 0;
    assert( nShift <= 32 );
    for( i = 0; i < nShift; i++ ) 
        for( j = nNum-1; j >= fSticky; j-- ) 
        {
            if( fShort || (1<<i) > j ) 
            {
                pRes[j] = Gia_ManHashMux( pNew, pShift[i], Fill, pRes[j] );
                if ( (1<<i) > nNum ) 
                    fShort = 1;
            } 
            else 
                pRes[j] = Gia_ManHashMux( pNew, pShift[i], pRes[j-(1<<i)], pRes[j] );
        }
}
void Wlc_BlastRotateRight( Gia_Man_t * pNew, int * pNum, int nNum, int * pShift, int nShift, Vec_Int_t * vRes )
{
    int * pRes = Wlc_VecCopy( vRes, pNum, nNum );
    int i, j, * pTemp = ABC_ALLOC( int, nNum );
    assert( nShift <= 32 );
    for( i = 0; i < nShift; i++, pRes = Wlc_VecCopy(vRes, pTemp, nNum) ) 
        for( j = 0; j < nNum; j++ ) 
            pTemp[j] = Gia_ManHashMux( pNew, pShift[i], pRes[(j+(1<<i))%nNum], pRes[j] );
    ABC_FREE( pTemp );
}
void Wlc_BlastRotateLeft( Gia_Man_t * pNew, int * pNum, int nNum, int * pShift, int nShift, Vec_Int_t * vRes )
{
    int * pRes = Wlc_VecCopy( vRes, pNum, nNum );
    int i, j, * pTemp = ABC_ALLOC( int, nNum );
    assert( nShift <= 32 );
    for( i = 0; i < nShift; i++, pRes = Wlc_VecCopy(vRes, pTemp, nNum) ) 
        for( j = 0; j < nNum; j++ ) 
        {
            int move = (j >= (1<<i)) ? (j-(1<<i))%nNum : (nNum - (((1<<i)-j)%nNum)) % nNum;
            pTemp[j] = Gia_ManHashMux( pNew, pShift[i], pRes[move], pRes[j] );
//            pTemp[j] = Gia_ManHashMux( pNew, pShift[i], pRes[((unsigned)(nNum-(1<<i)+j))%nNum], pRes[j] );
        }
    ABC_FREE( pTemp );
}
int Wlc_BlastReduction( Gia_Man_t * pNew, int * pFans, int nFans, int Type )
{
    if ( Type == WLC_OBJ_REDUCT_AND )
    {
        int k, iLit = 1;
        for ( k = 0; k < nFans; k++ )
            iLit = Gia_ManHashAnd( pNew, iLit, pFans[k] );
        return iLit;
    }
    if ( Type == WLC_OBJ_REDUCT_OR )
    {
        int k, iLit = 0;
        for ( k = 0; k < nFans; k++ )
            iLit = Gia_ManHashOr( pNew, iLit, pFans[k] );
        return iLit;
    }
    if ( Type == WLC_OBJ_REDUCT_XOR )
    {
        int k, iLit = 0;
        for ( k = 0; k < nFans; k++ )
            iLit = Gia_ManHashXor( pNew, iLit, pFans[k] );
        return iLit;
    }
    assert( 0 );
    return -1;
}
int Wlc_BlastLess( Gia_Man_t * pNew, int * pArg0, int * pArg1, int nBits )
{
    int k, iTerm, iEqu = 1, iLit = 0;
    for ( k = nBits - 1; k >= 0; k-- )
    {
        iTerm = Gia_ManHashAnd( pNew, Abc_LitNot(pArg0[k]), pArg1[k] );
        iTerm = Gia_ManHashAnd( pNew, iTerm, iEqu );
        if ( iTerm == 1 )
            return 1;
        iLit  = Gia_ManHashOr( pNew, iLit, iTerm ); 
        iEqu  = Abc_LitNot( Gia_ManHashXor( pNew, pArg0[k], pArg1[k] ) );
    }
    return iLit;
}
void Wlc_BlastAdder( Gia_Man_t * pNew, int * pAdd0, int * pAdd1, int nBits ) // result is in pAdd0
{
    int iCarry = 0, iTerm1, iTerm2, iTerm3, iSum, b;
    for ( b = 0; b < nBits; b++ )
    {
        iSum   = Gia_ManHashXor( pNew, iCarry, Gia_ManHashXor(pNew, pAdd0[b], pAdd1[b]) );
        iTerm1 = Gia_ManHashAnd( pNew, pAdd0[b], pAdd1[b] );
        iTerm2 = Gia_ManHashAnd( pNew, pAdd0[b], iCarry );
        iTerm3 = Gia_ManHashAnd( pNew, pAdd1[b], iCarry );
        iCarry = Gia_ManHashOr( pNew, iTerm1, Gia_ManHashOr(pNew, iTerm2, iTerm3) );
        pAdd0[b] = iSum;
    }
}
void Wlc_BlastSubtract( Gia_Man_t * pNew, int * pAdd0, int * pAdd1, int nBits ) // result is in pAdd0
{
    int borrow = 0, top_bit, b;
    for ( b = 0; b < nBits; b++ )
    {
        top_bit  = Gia_ManHashMux(pNew, borrow, Abc_LitNot(pAdd0[b]),  pAdd0[b]);
        borrow   = Gia_ManHashMux(pNew, pAdd0[b], Gia_ManHashAnd(pNew, borrow, pAdd1[b]), Gia_ManHashOr(pNew, borrow, pAdd1[b]));
        pAdd0[b] = Gia_ManHashXor(pNew, top_bit, pAdd1[b]);
    }
}

void Wlc_BlastMultiplier( Gia_Man_t * pNew, int * pArg0, int * pArg1, int nBits, Vec_Int_t * vTemp, Vec_Int_t * vRes )
{
    int i, j;
    Vec_IntFill( vRes, nBits, 0 );
    for ( i = 0; i < nBits; i++ )
    {
        Vec_IntFill( vTemp, i, 0 );
        for ( j = 0; Vec_IntSize(vTemp) < nBits; j++ )
            Vec_IntPush( vTemp, Gia_ManHashAnd(pNew, pArg0[j], pArg1[i]) );
        assert( Vec_IntSize(vTemp) == nBits );
        Wlc_BlastAdder( pNew, Vec_IntArray(vRes), Vec_IntArray(vTemp), nBits );
    }
}
void Wlc_BlastDivider( Gia_Man_t * pNew, int * pNum, int nNum, int * pDiv, int nDiv, int fQuo, Vec_Int_t * vRes )
{
    int * pRes  = Wlc_VecCopy( vRes, pNum, nNum );
    int * pQuo  = ABC_ALLOC( int, nNum );
    int * pTemp = ABC_ALLOC( int, nNum );
    int i, j, known, borrow, y_bit, top_bit;
    assert( nNum == nDiv );
    for ( j = nNum - 1; j >= 0; j-- ) 
    {
        known = 0;
        for ( i = nNum - 1; i > nNum - 1 - j; i-- ) 
        {
            known = Gia_ManHashOr( pNew, known, pDiv[i] );
            if( known == 1 ) 
                break;
        }
        pQuo[j] = known;
        for ( i = nNum - 1; i >= 0; i-- ) 
        {
            if ( known == 1 ) 
                break;
            y_bit = (i >= j) ? pDiv[i-j] : 0;
            pQuo[j] = Gia_ManHashMux( pNew, known, pQuo[j], Gia_ManHashAnd( pNew, y_bit, Abc_LitNot(pRes[i]) ) );
            known = Gia_ManHashOr( pNew, known, Gia_ManHashXor(pNew, y_bit, pRes[i]));
        }
        pQuo[j] = Abc_LitNot(pQuo[j]);
        if ( pQuo[j] == 0 )
            continue;
        borrow = 0;
        for ( i = 0; i < nNum; i++ ) 
        {
            top_bit  = Gia_ManHashMux( pNew, borrow, Abc_LitNot(pRes[i]), pRes[i] );
            y_bit    = (i >= j) ? pDiv[i-j] : 0;
            borrow   = Gia_ManHashMux( pNew, pRes[i], Gia_ManHashAnd(pNew, borrow, y_bit), Gia_ManHashOr(pNew, borrow, y_bit) );
            pTemp[i] = Gia_ManHashXor( pNew, top_bit, y_bit );
        }
        if ( pQuo[j] == 1 ) 
            Wlc_VecCopy( vRes, pTemp, nNum );
        else 
            for( i = 0; i < nNum; i++ ) 
                pRes[i] = Gia_ManHashMux( pNew, pQuo[j], pTemp[i], pRes[i] );
    }
    ABC_FREE( pTemp );
    if ( fQuo )
        Wlc_VecCopy( vRes, pQuo, nNum );
    ABC_FREE( pQuo );
}
void Wlc_BlastMinus( Gia_Man_t * pNew, int * pNum, int nNum, Vec_Int_t * vRes )
{
    int i, * pRes, invert = 0;
    Vec_IntFill( vRes, nNum, 0 );
    pRes = Vec_IntArray( vRes );
    for ( i = 0; i < nNum; i++ )
    {
        pRes[i] = Gia_ManHashMux( pNew, invert, Abc_LitNot(pRes[i]), pRes[i] );
        invert = Gia_ManHashOr( pNew, invert, pNum[i] );    
    }
}
void Wlc_BlastTable( Gia_Man_t * pNew, word * pTable, int * pFans, int nFans, int nOuts, Vec_Int_t * vRes )
{
    extern int Kit_TruthToGia( Gia_Man_t * pMan, unsigned * pTruth, int nVars, Vec_Int_t * vMemory, Vec_Int_t * vLeaves, int fHash );
    Vec_Int_t * vMemory = Vec_IntAlloc( 0 );
    Vec_Int_t vLeaves = { nFans, nFans, pFans };
    word * pTruth = ABC_ALLOC( word, Abc_TtWordNum(nFans) );
    int o, i, m, iLit, nMints = (1 << nFans);
    Vec_IntClear( vRes );
    for ( o = 0; o < nOuts; o++ )
    {
        // derive truth table
        memset( pTruth, 0, sizeof(word) * Abc_TtWordNum(nFans) );
        for ( m = 0; m < nMints; m++ )
            for ( i = 0; i < nFans; i++ )
                if ( Abc_TtGetBit( pTable, m * nFans + i ) )
                    Abc_TtSetBit( pTruth, m );
        // implement truth table
        if ( nFans < 6 )
            pTruth[0] = Abc_Tt6Stretch( pTruth[0], nFans );
        iLit = Kit_TruthToGia( pNew, (unsigned *)pTruth, nFans, vMemory, &vLeaves, 1 );
        Vec_IntPush( vRes, iLit );
    }
    Vec_IntFree( vMemory );
    ABC_FREE( pTruth );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Wlc_NtkBitBlast( Wlc_Ntk_t * p )
{
    Gia_Man_t * pTemp, * pNew;
    Wlc_Obj_t * pObj, * pPrev = NULL;
    Vec_Int_t * vBits, * vTemp0, * vTemp1, * vTemp2, * vRes;
    int nBits = Wlc_NtkPrepareBits( p );
    int nRange, nRange0, nRange1, nRange2;
    int i, k, b, iFanin, iLit, * pFans0, * pFans1, * pFans2;
    vBits  = Vec_IntAlloc( nBits );
    vTemp0 = Vec_IntAlloc( 1000 );
    vTemp1 = Vec_IntAlloc( 1000 );
    vTemp2 = Vec_IntAlloc( 1000 );
    vRes   = Vec_IntAlloc( 1000 );
    // create AIG manager
    pNew = Gia_ManStart( 5 * Wlc_NtkObjNum(p) + 1000 );
    pNew->pName = Abc_UtilStrsav( p->pName );
    Gia_ManHashAlloc( pNew );
    // clean AND-gate counters
    memset( p->nAnds, 0, sizeof(int) * WLC_OBJ_NUMBER );
    // create primary inputs
    Wlc_NtkForEachObj( p, pObj, i )
    {
        int nAndPrev = Gia_ManObjNum(pNew);
//        char * pName = Wlc_ObjName(p, i);
        nRange  = Wlc_ObjRange( pObj );
        nRange0 = Wlc_ObjFaninNum(pObj) > 0 ? Wlc_ObjRange( Wlc_ObjFanin0(p, pObj) ) : -1;
        nRange1 = Wlc_ObjFaninNum(pObj) > 1 ? Wlc_ObjRange( Wlc_ObjFanin1(p, pObj) ) : -1;
        nRange2 = Wlc_ObjFaninNum(pObj) > 2 ? Wlc_ObjRange( Wlc_ObjFanin2(p, pObj) ) : -1;
        pFans0  = Wlc_ObjFaninNum(pObj) > 0 ? Vec_IntEntryP( vBits, Wlc_ObjCopy(p, Wlc_ObjFaninId0(pObj)) ) : NULL;
        pFans1  = Wlc_ObjFaninNum(pObj) > 1 ? Vec_IntEntryP( vBits, Wlc_ObjCopy(p, Wlc_ObjFaninId1(pObj)) ) : NULL;
        pFans2  = Wlc_ObjFaninNum(pObj) > 2 ? Vec_IntEntryP( vBits, Wlc_ObjCopy(p, Wlc_ObjFaninId2(pObj)) ) : NULL;
        Vec_IntClear( vRes );
        if ( pObj->Type == WLC_OBJ_PI )
        {
            for ( k = 0; k < nRange; k++ )
                Vec_IntPush( vRes, Gia_ManAppendCi(pNew) );
        }
        else if ( pObj->Type == WLC_OBJ_PO || pObj->Type == WLC_OBJ_BUF )
        {
            if ( pObj->Type == WLC_OBJ_BUF && pObj->Signed && !Wlc_ObjFanin0(p, pObj)->Signed ) // unsign->sign
            {
                int nRangeMax = Abc_MaxInt( nRange0, nRange );
                int * pArg0 = Wlc_VecLoadFanins( vTemp0, pFans0, nRange0, nRangeMax, 0 );
                Wlc_BlastMinus( pNew, pArg0, nRange, vRes );
            }
            else
            {
    //            assert( nRange <= nRange0 );
                for ( k = 0; k < nRange; k++ )
                    Vec_IntPush( vRes, k < nRange0 ? pFans0[k] : 0 );
            }
        }
        else if ( pObj->Type == WLC_OBJ_CONST )
        {
            word * pTruth = (word *)Wlc_ObjFanins(pObj);
            for ( k = 0; k < nRange; k++ )
                Vec_IntPush( vRes, Abc_TtGetBit(pTruth, k) );
        }
        else if ( pObj->Type == WLC_OBJ_MUX )
        {
            assert( 1 + (1 << nRange0) == Wlc_ObjFaninNum(pObj) );
            for ( b = 0; b < nRange; b++ )
            {
                Vec_IntClear( vTemp0 );
                Wlc_ObjForEachFanin( pObj, iFanin, k )
                {
                    if ( !k ) continue;
                    assert( nRange == Wlc_ObjRange(Wlc_NtkObj(p, iFanin)) );
                    pFans1 = Vec_IntEntryP( vBits, Wlc_ObjCopy(p, iFanin) );
                    Vec_IntPush( vTemp0, pFans1[b] );
                }
                Vec_IntPush( vRes, Wlc_NtkMuxTree_rec(pNew, pFans0, nRange0, vTemp0, 0) );
            }
        }
        else if ( pObj->Type == WLC_OBJ_SHIFT_R || pObj->Type == WLC_OBJ_SHIFT_RA )
        {
            assert( nRange0 >= nRange );
            Wlc_BlastShiftRight( pNew, pFans0, nRange0, pFans1, nRange1, pObj->Type == WLC_OBJ_SHIFT_RA, vRes );
            if ( nRange0 > nRange )
                Vec_IntShrink( vRes, nRange );
        }
        else if ( pObj->Type == WLC_OBJ_SHIFT_L || pObj->Type == WLC_OBJ_SHIFT_LA )
        {
            int * pArg0 = Wlc_VecLoadFanins( vTemp0, pFans0, nRange0, nRange, Wlc_ObjFanin0(p, pObj)->Signed );
            assert( nRange0 <= nRange );
            Wlc_BlastShiftLeft( pNew, pArg0, nRange, pFans1, nRange1, pObj->Type == WLC_OBJ_SHIFT_LA, vRes );
        }
        else if ( pObj->Type == WLC_OBJ_ROTATE_R )
        {
            assert( nRange0 == nRange );
            Wlc_BlastRotateRight( pNew, pFans0, nRange0, pFans1, nRange1, vRes );
        }
        else if ( pObj->Type == WLC_OBJ_ROTATE_L )
        {
            assert( nRange0 == nRange );
            Wlc_BlastRotateLeft( pNew, pFans0, nRange0, pFans1, nRange1, vRes );
        }
        else if ( pObj->Type == WLC_OBJ_BIT_NOT )
        {
            assert( nRange == nRange0 );
            for ( k = 0; k < nRange; k++ )
                Vec_IntPush( vRes, Abc_LitNot(pFans0[k]) );
        }
        else if ( pObj->Type == WLC_OBJ_BIT_AND )
        {
            assert( nRange0 == nRange && nRange1 == nRange );
            for ( k = 0; k < nRange; k++ )
                Vec_IntPush( vRes, Gia_ManHashAnd(pNew, pFans0[k], pFans1[k]) );
        }
        else if ( pObj->Type == WLC_OBJ_BIT_OR )
        {
            assert( nRange0 == nRange && nRange1 == nRange );
            for ( k = 0; k < nRange; k++ )
                Vec_IntPush( vRes, Gia_ManHashOr(pNew, pFans0[k], pFans1[k]) );
        }
        else if ( pObj->Type == WLC_OBJ_BIT_XOR )
        {
            assert( nRange0 == nRange && nRange1 == nRange );
            for ( k = 0; k < nRange; k++ )
                Vec_IntPush( vRes, Gia_ManHashXor(pNew, pFans0[k], pFans1[k]) );
        }
        else if ( pObj->Type == WLC_OBJ_BIT_SELECT )
        {
            int End = Wlc_ObjRangeEnd(pObj);
            int Beg = Wlc_ObjRangeBeg(pObj);
            assert( nRange == End - Beg + 1 );
            for ( k = Beg; k <= End; k++ )
                Vec_IntPush( vRes, pFans0[k] );
        }
        else if ( pObj->Type == WLC_OBJ_BIT_CONCAT )
        {
            int iFanin, nTotal = 0;
            Wlc_ObjForEachFanin( pObj, iFanin, k )
                nTotal += Wlc_ObjRange( Wlc_NtkObj(p, iFanin) );
            assert( nRange == nTotal );
            Wlc_ObjForEachFaninReverse( pObj, iFanin, k )
            {
                nRange0 = Wlc_ObjRange( Wlc_NtkObj(p, iFanin) );
                pFans0 = Vec_IntEntryP( vBits, Wlc_ObjCopy(p, iFanin) );
                for ( b = 0; b < nRange0; b++ )
                    Vec_IntPush( vRes, pFans0[b] );
            }
        }
        else if ( pObj->Type == WLC_OBJ_BIT_ZEROPAD || pObj->Type == WLC_OBJ_BIT_SIGNEXT )
        {
            int Pad = pObj->Type == WLC_OBJ_BIT_ZEROPAD ? 0 : pFans0[nRange0-1];
            assert( nRange0 < nRange );
            for ( k = 0; k < nRange0; k++ )
                Vec_IntPush( vRes, pFans0[k] );
            for (      ; k < nRange; k++ )
                Vec_IntPush( vRes, Pad );
        }
        else if ( pObj->Type == WLC_OBJ_LOGIC_NOT )
        {
            iLit = Wlc_BlastReduction( pNew, pFans0, nRange, WLC_OBJ_REDUCT_OR );
            assert( nRange == 1 );
            Vec_IntFill( vRes, 1, Abc_LitNot(iLit) );
        }
        else if ( pObj->Type == WLC_OBJ_LOGIC_AND )
        {
            int iLit0 = Wlc_BlastReduction( pNew, pFans0, nRange, WLC_OBJ_REDUCT_OR );
            int iLit1 = Wlc_BlastReduction( pNew, pFans0, nRange, WLC_OBJ_REDUCT_OR );
            assert( nRange == 1 );
            Vec_IntFill( vRes, 1, Gia_ManHashAnd(pNew, iLit0, iLit1) );
        }
        else if ( pObj->Type == WLC_OBJ_LOGIC_OR )
        {
            int iLit0 = Wlc_BlastReduction( pNew, pFans0, nRange, WLC_OBJ_REDUCT_OR );
            int iLit1 = Wlc_BlastReduction( pNew, pFans0, nRange, WLC_OBJ_REDUCT_OR );
            assert( nRange == 1 );
            Vec_IntFill( vRes, 1, Gia_ManHashOr(pNew, iLit0, iLit1) );
        }
        else if ( pObj->Type == WLC_OBJ_COMP_EQU || pObj->Type == WLC_OBJ_COMP_NOTEQU )
        {
            int iLit = 0;
            assert( nRange == 1 && nRange0 == nRange1 );
            for ( k = 0; k < nRange0; k++ )
                iLit = Gia_ManHashOr( pNew, iLit, Gia_ManHashXor(pNew, pFans0[k], pFans1[k]) ); 
            Vec_IntFill( vRes, 1, Abc_LitNotCond(iLit, pObj->Type == WLC_OBJ_COMP_EQU) );
        }
        else if ( pObj->Type == WLC_OBJ_COMP_LESS || pObj->Type == WLC_OBJ_COMP_MOREEQU ||
                  pObj->Type == WLC_OBJ_COMP_MORE || pObj->Type == WLC_OBJ_COMP_LESSEQU )
        {
            int nRangeMax = Abc_MaxInt( nRange0, nRange1 );
            int * pArg0 = Wlc_VecLoadFanins( vRes,   pFans0, nRange0, nRangeMax, Wlc_ObjFanin0(p, pObj)->Signed );
            int * pArg1 = Wlc_VecLoadFanins( vTemp1, pFans1, nRange1, nRangeMax, Wlc_ObjFanin1(p, pObj)->Signed );
            int fSwap  = (pObj->Type == WLC_OBJ_COMP_MORE    || pObj->Type == WLC_OBJ_COMP_LESSEQU);
            int fCompl = (pObj->Type == WLC_OBJ_COMP_MOREEQU || pObj->Type == WLC_OBJ_COMP_LESSEQU);
            assert( nRange == 1 );
            if ( fSwap ) ABC_SWAP( int *, pFans0, pFans1 );
            iLit = Wlc_BlastLess( pNew, pArg0, pArg1, nRangeMax );
            iLit = Abc_LitNotCond( iLit, fCompl );
            Vec_IntFill( vRes, 1, iLit );
        }
        else if ( pObj->Type == WLC_OBJ_REDUCT_AND || pObj->Type == WLC_OBJ_REDUCT_OR || pObj->Type == WLC_OBJ_REDUCT_XOR )
            Vec_IntPush( vRes, Wlc_BlastReduction( pNew, pFans0, nRange, pObj->Type ) );
        else if ( pObj->Type == WLC_OBJ_ARI_ADD || pObj->Type == WLC_OBJ_ARI_SUB ) 
        {
            int * pArg0 = Wlc_VecLoadFanins( vRes,   pFans0, nRange0, nRange, Wlc_ObjFanin0(p, pObj)->Signed );
            int * pArg1 = Wlc_VecLoadFanins( vTemp1, pFans1, nRange1, nRange, Wlc_ObjFanin1(p, pObj)->Signed );
            if ( pObj->Type == WLC_OBJ_ARI_ADD )
                Wlc_BlastAdder( pNew, pArg0, pArg1, nRange ); // result is in pFan0 (vRes)
            else 
                Wlc_BlastSubtract( pNew, pArg0, pArg1, nRange ); // result is in pFan0 (vRes)
        }
        else if ( pObj->Type == WLC_OBJ_ARI_MULTI )
        {
            int * pArg0 = Wlc_VecLoadFanins( vTemp0, pFans0, nRange0, nRange, Wlc_ObjFanin0(p, pObj)->Signed );
            int * pArg1 = Wlc_VecLoadFanins( vTemp1, pFans1, nRange1, nRange, Wlc_ObjFanin1(p, pObj)->Signed );
            assert( nRange0 <= nRange && nRange1 <= nRange );
            Wlc_BlastMultiplier( pNew, pArg0, pArg1, nRange, vTemp2, vRes );
        }
        else if ( pObj->Type == WLC_OBJ_ARI_DIVIDE || pObj->Type == WLC_OBJ_ARI_MODULUS )
        {
            int nRangeMax = Abc_MaxInt( nRange, Abc_MaxInt(nRange0, nRange1) );
            int * pArg0 = Wlc_VecLoadFanins( vTemp0, pFans0, nRange0, nRangeMax, Wlc_ObjFanin0(p, pObj)->Signed );
            int * pArg1 = Wlc_VecLoadFanins( vTemp1, pFans1, nRange1, nRangeMax, Wlc_ObjFanin1(p, pObj)->Signed );
            Wlc_BlastDivider( pNew, pArg0, nRangeMax, pArg1, nRangeMax, pObj->Type == WLC_OBJ_ARI_DIVIDE, vRes );
            Vec_IntShrink( vRes, nRange );
        }
        else if ( pObj->Type == WLC_OBJ_ARI_MINUS )
        {
            int * pArg0 = Wlc_VecLoadFanins( vTemp0, pFans0, nRange0, nRange, Wlc_ObjFanin0(p, pObj)->Signed );
            assert( nRange0 <= nRange );
            Wlc_BlastMinus( pNew, pArg0, nRange, vRes );
        }
        else if ( pObj->Type == WLC_OBJ_TABLE )
            Wlc_BlastTable( pNew, Wlc_ObjTable(p, pObj), pFans0, nRange0, nRange, vRes );
        else assert( 0 );
        assert( Vec_IntSize(vBits) == Wlc_ObjCopy(p, i) );
        Vec_IntAppend( vBits, vRes );
        pPrev = pObj;
        if ( pObj->Type != WLC_OBJ_PI && pObj->Type != WLC_OBJ_PO )
            p->nAnds[pObj->Type] += Gia_ManObjNum(pNew) - nAndPrev;
    }
    p->nAnds[0] = Gia_ManAndNum(pNew);
    assert( nBits == Vec_IntSize(vBits) );
    Vec_IntFree( vTemp0 );
    Vec_IntFree( vTemp1 );
    Vec_IntFree( vTemp2 );
    Vec_IntFree( vRes );
    // create POs
    Wlc_NtkForEachPo( p, pObj, i )
    {
        nRange = Wlc_ObjRange( pObj );
        nRange0 = Wlc_ObjFaninNum(pObj) > 0 ? Wlc_ObjRange( Wlc_ObjFanin0(p, pObj) ) : -1;
        assert( nRange == nRange0 );
        pFans0 = Vec_IntEntryP( vBits, Wlc_ObjCopy(p, Wlc_ObjId(p, pObj)) );
        for ( k = 0; k < nRange; k++ )
            Gia_ManAppendCo( pNew, pFans0[k] );
    }
    Vec_IntFree( vBits );
    Vec_IntErase( &p->vCopies );
    // finalize and cleanup
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

