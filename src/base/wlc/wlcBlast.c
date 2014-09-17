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

  Synopsis    []

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
int Wlc_NtkComputeReduction( Gia_Man_t * pNew, int * pFans, int nFans, int Type )
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
int Wlc_NtkMuxTree_rec( Gia_Man_t * pNew, int * pCtrl, int nCtrl, Vec_Int_t * vData, int Shift )
{
    int iLit0, iLit1;
    if ( nCtrl == 0 )
        return Vec_IntEntry( vData, Shift );
    iLit0 = Wlc_NtkMuxTree_rec( pNew, pCtrl, nCtrl-1, vData, Shift );
    iLit1 = Wlc_NtkMuxTree_rec( pNew, pCtrl, nCtrl-1, vData, Shift + (1<<(nCtrl-1)) );
    return Gia_ManHashMux( pNew, pCtrl[nCtrl-1], iLit1, iLit0 );
}
void Wlc_NtkAdderChain( Gia_Man_t * pNew, int * pAdd0, int * pAdd1, int nBits )
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
Gia_Man_t * Wlc_NtkBitBlast( Wlc_Ntk_t * p )
{
    Gia_Man_t * pTemp, * pNew;
    Wlc_Obj_t * pObj;
    Vec_Int_t * vBits, * vTemp0, * vTemp1, * vTemp2, * vTemp3;
    int nBits = Wlc_NtkPrepareBits( p );
    int nRange, nRange0, nRange1, nRange2;
    int i, k, b, iLit, * pFans0, * pFans1, * pFans2;
    vBits  = Vec_IntAlloc( nBits );
    vTemp0 = Vec_IntAlloc( 1000 );
    vTemp1 = Vec_IntAlloc( 1000 );
    vTemp2 = Vec_IntAlloc( 1000 );
    vTemp3 = Vec_IntAlloc( 1000 );
    // craete AIG manager
    pNew = Gia_ManStart( 5 * Wlc_NtkObjNum(p) + 1000 );
    pNew->pName = Abc_UtilStrsav( p->pName );
    Gia_ManHashAlloc( pNew );
    // create primary inputs
    Wlc_NtkForEachObj( p, pObj, i )
    {
//        char * pName = Wlc_ObjName(p, i);
        nRange  = Wlc_ObjRange( pObj );
        nRange0 = Wlc_ObjFaninNum(pObj) > 0 ? Wlc_ObjRange( Wlc_ObjFanin0(p, pObj) ) : -1;
        nRange1 = Wlc_ObjFaninNum(pObj) > 1 ? Wlc_ObjRange( Wlc_ObjFanin1(p, pObj) ) : -1;
        nRange2 = Wlc_ObjFaninNum(pObj) > 2 ? Wlc_ObjRange( Wlc_ObjFanin2(p, pObj) ) : -1;
        pFans0 = Wlc_ObjFaninNum(pObj) > 0 ? Vec_IntEntryP( vBits, Wlc_ObjCopy(p, Wlc_ObjFaninId0(pObj)) ) : NULL;
        pFans1 = Wlc_ObjFaninNum(pObj) > 1 ? Vec_IntEntryP( vBits, Wlc_ObjCopy(p, Wlc_ObjFaninId1(pObj)) ) : NULL;
        pFans2 = Wlc_ObjFaninNum(pObj) > 2 ? Vec_IntEntryP( vBits, Wlc_ObjCopy(p, Wlc_ObjFaninId2(pObj)) ) : NULL;
        if ( pObj->Type == WLC_OBJ_PI )
        {
            for ( k = 0; k < nRange; k++ )
                Vec_IntPush( vBits, Gia_ManAppendCi(pNew) );
        }
        else if ( pObj->Type == WLC_OBJ_PO || pObj->Type == WLC_OBJ_BUF )
        {
//            assert( nRange <= nRange0 );
            for ( k = 0; k < nRange; k++ )
                Vec_IntPush( vBits, k < nRange0 ? pFans0[k] : 0 );
        }
        else if ( pObj->Type == WLC_OBJ_CONST )
        {
            word * pTruth = (word *)Wlc_ObjFanins(pObj);
            for ( k = 0; k < nRange; k++ )
                Vec_IntPush( vBits, Abc_TtGetBit(pTruth, k) );
        }
        else if ( pObj->Type == WLC_OBJ_MUX )
        {
            assert( nRange0 == 1 );
            assert( nRange1 == nRange );
            assert( nRange2 == nRange );
            for ( k = 0; k < nRange; k++ )
                Vec_IntPush( vBits, Gia_ManHashMux(pNew, pFans0[0], pFans1[k], pFans2[k]) );
        }
        else if ( pObj->Type == WLC_OBJ_SHIFT_R || pObj->Type == WLC_OBJ_SHIFT_RA )
        {
            // prepare data
            int Fill = pObj->Type == WLC_OBJ_SHIFT_R ? 0 : pFans0[nRange0-1];
            int nTotal = nRange + (1 << nRange1);
            Vec_IntClear( vTemp0 );
            for ( k = 0; k < nRange0; k++ )
                Vec_IntPush( vTemp0, pFans0[k] );
            for ( k = 0; k < nTotal; k++ )
                Vec_IntPush( vTemp0, Fill );
            // derive the result
            for ( k = 0; k < nRange; k++ )
                Vec_IntPush( vBits, Wlc_NtkMuxTree_rec(pNew, pFans1, nRange1, vTemp0, k) );
        }
        else if ( pObj->Type == WLC_OBJ_SHIFT_L || pObj->Type == WLC_OBJ_SHIFT_LA )
        {
            // prepare data
            int Fill = pObj->Type == WLC_OBJ_SHIFT_L ? 0 : pFans0[0];
            int nTotal = nRange + (1 << nRange1);
            Vec_IntClear( vTemp0 );
            for ( k = 0; k < nRange0; k++ )
                Vec_IntPush( vTemp0, pFans0[k] );
            for ( k = 0; k < nTotal; k++ )
                Vec_IntPush( vTemp0, Fill );
            // derive the result
            for ( k = 0; k < nRange; k++ )
                Vec_IntPush( vBits, Wlc_NtkMuxTree_rec(pNew, pFans1, nRange1, vTemp0, k) );
        }
        else if ( pObj->Type == WLC_OBJ_BIT_NOT )
        {
            assert( nRange == nRange0 );
            for ( k = 0; k < nRange; k++ )
                Vec_IntPush( vBits, Abc_LitNot(pFans0[k]) );
        }
        else if ( pObj->Type == WLC_OBJ_BIT_AND )
        {
            assert( nRange0 == nRange && nRange1 == nRange );
            for ( k = 0; k < nRange; k++ )
                Vec_IntPush( vBits, Gia_ManHashAnd(pNew, pFans0[k], pFans1[k]) );
        }
        else if ( pObj->Type == WLC_OBJ_BIT_OR )
        {
            assert( nRange0 == nRange && nRange1 == nRange );
            for ( k = 0; k < nRange; k++ )
                Vec_IntPush( vBits, Gia_ManHashOr(pNew, pFans0[k], pFans1[k]) );
        }
        else if ( pObj->Type == WLC_OBJ_BIT_XOR )
        {
            assert( nRange0 == nRange && nRange1 == nRange );
            for ( k = 0; k < nRange; k++ )
                Vec_IntPush( vBits, Gia_ManHashXor(pNew, pFans0[k], pFans1[k]) );
        }
        else if ( pObj->Type == WLC_OBJ_BIT_SELECT )
        {
            int End = Wlc_ObjRangeEnd(pObj);
            int Beg = Wlc_ObjRangeBeg(pObj);
            assert( nRange == End - Beg + 1 );
            for ( k = Beg; k <= End; k++ )
                Vec_IntPush( vBits, pFans0[k] );
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
                    Vec_IntPush( vBits, pFans0[b] );
            }
        }
        else if ( pObj->Type == WLC_OBJ_BIT_ZEROPAD || pObj->Type == WLC_OBJ_BIT_SIGNEXT )
        {
            int Pad = pObj->Type == WLC_OBJ_BIT_ZEROPAD ? 0 : pFans0[nRange0-1];
            assert( nRange0 < nRange );
            for ( k = 0; k < nRange0; k++ )
                Vec_IntPush( vBits, pFans0[k] );
            for (      ; k < nRange; k++ )
                Vec_IntPush( vBits, Pad );
        }
        else if ( pObj->Type == WLC_OBJ_LOGIC_NOT )
        {
            iLit = Wlc_NtkComputeReduction( pNew, pFans0, nRange, WLC_OBJ_REDUCT_OR );
            assert( nRange == 1 );
            Vec_IntPush( vBits, Abc_LitNot(iLit) );
        }
        else if ( pObj->Type == WLC_OBJ_LOGIC_AND )
        {
            int iLit0 = Wlc_NtkComputeReduction( pNew, pFans0, nRange, WLC_OBJ_REDUCT_OR );
            int iLit1 = Wlc_NtkComputeReduction( pNew, pFans0, nRange, WLC_OBJ_REDUCT_OR );
            assert( nRange == 1 );
            Vec_IntPush( vBits, Gia_ManHashAnd(pNew, iLit0, iLit1) );
        }
        else if ( pObj->Type == WLC_OBJ_LOGIC_OR )
        {
            int iLit0 = Wlc_NtkComputeReduction( pNew, pFans0, nRange, WLC_OBJ_REDUCT_OR );
            int iLit1 = Wlc_NtkComputeReduction( pNew, pFans0, nRange, WLC_OBJ_REDUCT_OR );
            assert( nRange == 1 );
            Vec_IntPush( vBits, Gia_ManHashOr(pNew, iLit0, iLit1) );
        }
        else if ( pObj->Type == WLC_OBJ_COMP_EQU || pObj->Type == WLC_OBJ_COMP_NOT )
        {
            int iLit = 0;
            assert( nRange == 1 );
            assert( nRange0 == nRange1 );
            for ( k = 0; k < nRange0; k++ )
                iLit = Gia_ManHashOr( pNew, iLit, Gia_ManHashXor(pNew, pFans0[k], pFans1[k]) ); 
            Vec_IntPush( vBits, Abc_LitNotCond(iLit, pObj->Type == WLC_OBJ_COMP_EQU) );
        }
        else if ( pObj->Type == WLC_OBJ_COMP_LESS || pObj->Type == WLC_OBJ_COMP_MOREEQU ||
                  pObj->Type == WLC_OBJ_COMP_MORE || pObj->Type == WLC_OBJ_COMP_LESSEQU )
        {
            int iTerm, iEqu = 1, iLit = 0;
            assert( nRange == 1 );
            assert( nRange0 == nRange1 );
            if ( pObj->Type == WLC_OBJ_COMP_MORE || pObj->Type == WLC_OBJ_COMP_LESSEQU )
                ABC_SWAP( int *, pFans0, pFans1 );
            for ( k = nRange0 - 1; k >= 0; k-- )
            {
                iTerm = Gia_ManHashAnd( pNew, Abc_LitNot(pFans0[k]), pFans1[k] );
                iTerm = Gia_ManHashAnd( pNew, iTerm, iEqu );
                iLit  = Gia_ManHashOr( pNew, iLit, iTerm ); 
                iEqu  = Abc_LitNot( Gia_ManHashXor( pNew, pFans0[k], pFans1[k] ) );
            }
            Vec_IntPush( vBits, Abc_LitNotCond(iLit, pObj->Type == WLC_OBJ_COMP_MOREEQU) );
        }
        else if ( pObj->Type == WLC_OBJ_REDUCT_AND || pObj->Type == WLC_OBJ_REDUCT_OR || pObj->Type == WLC_OBJ_REDUCT_XOR )
            Vec_IntPush( vBits, Wlc_NtkComputeReduction( pNew, pFans0, nRange, pObj->Type ) );
        else if ( pObj->Type == WLC_OBJ_ARI_ADD )
        {
            int Pad0 = Wlc_ObjFanin0(p, pObj)->Signed ? pFans0[nRange0-1] : 0;
            int Pad1 = Wlc_ObjFanin1(p, pObj)->Signed ? pFans1[nRange1-1] : 0;
            assert( nRange0 <= nRange && nRange1 <= nRange );
            Vec_IntClear( vTemp0 );
            for ( k = 0; k < nRange; k++ )
                Vec_IntPush( vTemp0, k < nRange0 ? pFans0[k] : Pad0 );
            Vec_IntClear( vTemp1 );
            for ( k = 0; k < nRange; k++ )
                Vec_IntPush( vTemp1, k < nRange1 ? pFans1[k] : Pad1 );
            Wlc_NtkAdderChain( pNew, Vec_IntArray(vTemp0), Vec_IntArray(vTemp1), nRange );
            Vec_IntAppend( vBits, vTemp0 );
        }
        else if ( pObj->Type == WLC_OBJ_ARI_MULTI )
        {
            int Pad0 = Wlc_ObjFanin0(p, pObj)->Signed ? pFans0[nRange0-1] : 0;
            int Pad1 = Wlc_ObjFanin1(p, pObj)->Signed ? pFans1[nRange1-1] : 0;
            assert( nRange0 <= nRange && nRange1 <= nRange );
            Vec_IntClear( vTemp0 );
            for ( k = 0; k < nRange; k++ )
                Vec_IntPush( vTemp0, k < nRange0 ? pFans0[k] : Pad0 );
            Vec_IntClear( vTemp1 );
            for ( k = 0; k < nRange; k++ )
                Vec_IntPush( vTemp1, k < nRange1 ? pFans1[k] : Pad1 );
            // iterate
            Vec_IntFill( vTemp3, nRange, 0 );
            for ( k = 0; k < nRange; k++ )
            {
                Vec_IntFill( vTemp2, k, 0 );
                Vec_IntForEachEntry( vTemp0, iLit, b )
                {
                    Vec_IntPush( vTemp2, Gia_ManHashAnd(pNew, iLit, Vec_IntEntry(vTemp1, k)) );
                    if ( Vec_IntSize(vTemp2) == nRange )
                        break;
                }
                assert( Vec_IntSize(vTemp2) == nRange );
                Wlc_NtkAdderChain( pNew, Vec_IntArray(vTemp3), Vec_IntArray(vTemp2), nRange );
            }
            assert( Vec_IntSize(vTemp3) == nRange );
            Vec_IntAppend( vBits, vTemp3 );
        }
        else if ( pObj->Type == WLC_OBJ_TABLE )
        {
            assert( pObj->Type != WLC_OBJ_TABLE );
            for ( k = 0; k < nRange; k++ )
                Vec_IntPush( vBits, 0 );
        }
        else assert( 0 );
    }
    assert( nBits == Vec_IntSize(vBits) );
    Vec_IntFree( vTemp0 );
    Vec_IntFree( vTemp1 );
    Vec_IntFree( vTemp2 );
    Vec_IntFree( vTemp3 );
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

