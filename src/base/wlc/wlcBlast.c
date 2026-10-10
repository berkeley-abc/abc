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
#include "misc/tim/tim.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "base/cmd/cmd.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Counts constant bits.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Wlc_NtkCountConstBits( int * pArray, int nSize )
{
    int i, Counter = 0;
    for ( i = 0; i < nSize; i++ )
        Counter += (pArray[i] == 0 || pArray[i] == 1);
    return Counter;
}

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
int Wlc_NtkMuxTree2_nb( Gia_Man_t * pNew, int * pCtrl, int nCtrl, Vec_Int_t * vData, Vec_Int_t * vAnds )
{
    int iLitOr = 0, iLitAnd, m;
    assert( Vec_IntSize(vData) == (1 << nCtrl) );
    assert( Vec_IntSize(vAnds) == (1 << nCtrl) );
    for ( m = 0; m < (1 << nCtrl); m++ )
    {
        iLitAnd = Gia_ManHashAnd( pNew, Vec_IntEntry(vAnds, m), Vec_IntEntry(vData, m) );
        iLitOr  = Gia_ManHashOr( pNew, iLitOr, iLitAnd );
    }
    return iLitOr;
}
int Wlc_NtkMuxTree2( Gia_Man_t * pNew, int * pCtrl, int nCtrl, Vec_Int_t * vData, Vec_Int_t * vAnds, Vec_Int_t * vTemp )
{
    int m, iLit;
    assert( !nCtrl || Vec_IntSize(vData) == (1 << nCtrl) );
    assert( !nCtrl || Vec_IntSize(vAnds) == (1 << nCtrl) );
    Vec_IntClear( vTemp );
    Vec_IntForEachEntry( vAnds, iLit, m )
        Vec_IntPush( vTemp, Abc_LitNot( Gia_ManHashAnd(pNew, iLit, Vec_IntEntry(vData, m)) ) );
    return Abc_LitNot( Gia_ManHashAndMulti(pNew, vTemp) );
}
int Wlc_NtkMuxTree3( Gia_Man_t * p, Vec_Int_t * vData, char * pNums, Vec_Int_t ** pvDecs )
{
    int i, iStart = 0, nSize = Vec_IntSize(vData);
    for ( i = (int)strlen(pNums)-1; i >= 0; i-- )
    {
        int k, b, nBits = (int)(pNums[i] - '0');
        Vec_Int_t * vDec = pvDecs[i];
        for ( k = 0; k < nSize; k++ )
            Vec_IntWriteEntry( vData, k, Gia_ManHashAnd(p, Vec_IntEntry(vData, k), Vec_IntEntry(vDec, k%Vec_IntSize(vDec))) );
        for ( b = 0; b < nBits; b++, nSize /= 2 )
            for ( k = 0; k < nSize/2; k++ )
                Vec_IntWriteEntry( vData, k, Gia_ManHashOr(p, Vec_IntEntry(vData, 2*k), Vec_IntEntry(vData, 2*k+1)) );
        iStart += nBits;
    }
    assert( nSize == 1 );
    return Vec_IntEntry(vData, 0);
}
Vec_Int_t ** Wlc_NtkMuxTree3DecsDerive( Gia_Man_t * p, int * pIns, int nIns, char * pNums )
{
    extern Vec_Int_t * Wlc_BlastDecoder2_rec( Gia_Man_t * p, int * pLits, int nLits );
    Vec_Int_t ** pvDecs = ABC_ALLOC( Vec_Int_t *, strlen(pNums) ); int i, iStart = 0;
    for ( i = (int)strlen(pNums)-1; i >= 0; i-- ) {
        pvDecs[i] = Wlc_BlastDecoder2_rec( p, pIns + iStart, (int)(pNums[i] - '0') );
        iStart += (int)(pNums[i] - '0');
    }
    assert( iStart == nIns );
    return pvDecs;
}
void Wlc_NtkMuxTree3DecsFree( Vec_Int_t ** pvDecs, char * pNums )
{
    int i;
    for ( i = (int)strlen(pNums)-1; i >= 0; i-- )
        Vec_IntFree( pvDecs[i] );
    ABC_FREE( pvDecs );
}
char * Wlc_NtkMuxTreeString( int nIns )
{
    if ( nIns == 1 )    return (char*)"1";    
    if ( nIns == 2 )    return (char*)"11";
    if ( nIns == 3 )    return (char*)"111";
    if ( nIns == 4 )    return (char*)"112";
    if ( nIns == 5 )    return (char*)"1112";
    if ( nIns == 6 )    return (char*)"1113";
    if ( nIns == 7 )    return (char*)"1114";
    if ( nIns == 8 )    return (char*)"1124";
    if ( nIns == 9 )    return (char*)"11124";
    if ( nIns == 10 )   return (char*)"11125";
    if ( nIns == 11 )   return (char*)"11126";
    if ( nIns == 12 )   return (char*)"11136";
    if ( nIns == 13 )   return (char*)"11137";
    if ( nIns == 14 )   return (char*)"11147";
    if ( nIns == 15 )   return (char*)"11148";
    if ( nIns == 16 )   return (char*)"11248";
    return NULL;
}
void Wlc_NtkPrintNameArray( Vec_Ptr_t * vNames )
{
    int i; char * pTemp;
    Vec_PtrForEachEntry( char *, vNames, pTemp, i )
        printf( "%2d : %s\n", i, pTemp );
}

/**Function*************************************************************

  Synopsis    [Bit blasting for specific operations.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Wlc_BlastShiftRightInt( Gia_Man_t * pNew, int * pNum, int nNum, int * pShift, int nShift, int fSticky, Vec_Int_t * vRes )
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
void Wlc_BlastShiftRight( Gia_Man_t * pNew, int * pNum, int nNum, int * pShift, int nShift, int fSticky, Vec_Int_t * vRes )
{
    int nShiftMax = Abc_Base2Log(nNum);
    int * pShiftNew = ABC_ALLOC( int, nShift );
    memcpy( pShiftNew, pShift, sizeof(int)*nShift );
    if ( nShiftMax < nShift && nShift > 30 )
    {
        int i, iRes = pShiftNew[nShiftMax];
        for ( i = nShiftMax + 1; i < nShift; i++ )
            iRes = Gia_ManHashOr( pNew, iRes, pShiftNew[i] );
        pShiftNew[nShiftMax++] = iRes;
    }
    else 
        nShiftMax = nShift;
    Wlc_BlastShiftRightInt( pNew, pNum, nNum, pShiftNew, nShiftMax, fSticky, vRes );
    ABC_FREE( pShiftNew );
}
void Wlc_BlastShiftLeftInt( Gia_Man_t * pNew, int * pNum, int nNum, int * pShift, int nShift, int fSticky, Vec_Int_t * vRes )
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
void Wlc_BlastShiftLeft( Gia_Man_t * pNew, int * pNum, int nNum, int * pShift, int nShift, int fSticky, Vec_Int_t * vRes )
{
    int nShiftMax = Abc_Base2Log(nNum);
    int * pShiftNew = ABC_ALLOC( int, nShift );
    memcpy( pShiftNew, pShift, sizeof(int)*nShift );
    if ( nShiftMax < nShift )
    {
        int i, iRes = pShiftNew[nShiftMax];
        for ( i = nShiftMax + 1; i < nShift; i++ )
            iRes = Gia_ManHashOr( pNew, iRes, pShiftNew[i] );
        pShiftNew[nShiftMax++] = iRes;
    }
    else 
        nShiftMax = nShift;
    Wlc_BlastShiftLeftInt( pNew, pNum, nNum, pShiftNew, nShiftMax, fSticky, vRes );
    ABC_FREE( pShiftNew );
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
    if ( Type == WLC_OBJ_REDUCT_AND || Type == WLC_OBJ_REDUCT_NAND )
    {
        int k, iLit = 1;
        for ( k = 0; k < nFans; k++ )
            iLit = Gia_ManHashAnd( pNew, iLit, pFans[k] );
        return Abc_LitNotCond( iLit, Type == WLC_OBJ_REDUCT_NAND );
    }
    if ( Type == WLC_OBJ_REDUCT_OR || Type == WLC_OBJ_REDUCT_NOR )
    {
        int k, iLit = 0;
        for ( k = 0; k < nFans; k++ )
            iLit = Gia_ManHashOr( pNew, iLit, pFans[k] );
        return Abc_LitNotCond( iLit, Type == WLC_OBJ_REDUCT_NOR );
    }
    if ( Type == WLC_OBJ_REDUCT_XOR || Type == WLC_OBJ_REDUCT_NXOR )
    {
        int k, iLit = 0;
        for ( k = 0; k < nFans; k++ )
            iLit = Gia_ManHashXor( pNew, iLit, pFans[k] );
        return Abc_LitNotCond( iLit, Type == WLC_OBJ_REDUCT_NXOR );
    }
    assert( 0 );
    return -1;
}
int Wlc_BlastLess2( Gia_Man_t * pNew, int * pArg0, int * pArg1, int nBits )
{
    int k, iKnown = 0, iRes = 0;
    for ( k = nBits - 1; k >= 0; k-- )
    {
        iRes   = Gia_ManHashMux( pNew, iKnown, iRes, Gia_ManHashAnd(pNew, Abc_LitNot(pArg0[k]), pArg1[k]) );
        iKnown = Gia_ManHashOr( pNew, iKnown, Gia_ManHashXor(pNew, pArg0[k], pArg1[k]) );
        if ( iKnown == 1 )
            break;
    }
    return iRes;
}
void Wlc_BlastLess_rec( Gia_Man_t * pNew, int * pArg0, int * pArg1, int nBits, int * pYes, int * pNo )
{
    if ( nBits > 1 )
    {
        int Yes = Gia_ManHashAnd( pNew, Abc_LitNot(pArg0[nBits-1]), pArg1[nBits-1] ), YesR;
        int No  = Gia_ManHashAnd( pNew, Abc_LitNot(pArg1[nBits-1]), pArg0[nBits-1] ), NoR;
        if ( Yes == 1 || No == 1 )
        {
            *pYes = Yes;
            *pNo  = No;
            return;
        }
        Wlc_BlastLess_rec( pNew, pArg0, pArg1, nBits-1, &YesR, &NoR );
        *pYes = Gia_ManHashOr( pNew, Yes, Gia_ManHashAnd(pNew, Abc_LitNot(No),  YesR) );
        *pNo  = Gia_ManHashOr( pNew, No,  Gia_ManHashAnd(pNew, Abc_LitNot(Yes), NoR ) );
        return;
    }
    assert( nBits == 1 );
    *pYes = Gia_ManHashAnd( pNew, Abc_LitNot(pArg0[0]), pArg1[0] );
    *pNo  = Gia_ManHashAnd( pNew, Abc_LitNot(pArg1[0]), pArg0[0] );
}
int Wlc_BlastLess( Gia_Man_t * pNew, int * pArg0, int * pArg1, int nBits )
{
    int Yes, No;
    if ( nBits == 0 )
        return 0;
    Wlc_BlastLess_rec( pNew, pArg0, pArg1, nBits, &Yes, &No );
    return Yes;
}
int Wlc_BlastLessSigned( Gia_Man_t * pNew, int * pArg0, int * pArg1, int nBits )
{
    int iDiffSign = Gia_ManHashXor( pNew, pArg0[nBits-1], pArg1[nBits-1] );
    return Gia_ManHashMux( pNew, iDiffSign, pArg0[nBits-1], Wlc_BlastLess(pNew, pArg0, pArg1, nBits-1) );
}
int Wlc_BlastLess3( Gia_Man_t * p, int * pArg1, int * pArg0, int nBits )
{
    int i, iLit = 1;
    for ( i = 0; i < nBits; i++ ) {
        int iLitA0  = pArg0[i];
        int iLitA1  = i == nBits-1 ? 0 : pArg0[i+1];
        int iLitB0  = pArg1[i];
        int iLitB1  = i == nBits-1 ? 0 : pArg1[i+1];
        int iOrLit0;
        if ( i == 0 )
            iOrLit0 = Gia_ManHashOr(p, Abc_LitNotCond(iLitA0, !(i&1)), Abc_LitNotCond(iLitB0, i&1));
        else
            iOrLit0 = Gia_ManHashAnd(p, Abc_LitNotCond(iLitA0, !(i&1)), Abc_LitNotCond(iLitB0, i&1));
        int iOrLit1 = Gia_ManHashAnd(p, Abc_LitNotCond(iLitA1, !(i&1)), Abc_LitNotCond(iLitB1, i&1));
        int iOrLit  = Gia_ManHashOr(p, iOrLit0, iOrLit1 );
        iLit = Gia_ManHashOr(p, Abc_LitNot(iLit), iOrLit );
    }
    return Abc_LitNotCond(iLit, nBits&1);
}
int Wlc_BlastLessSigned3( Gia_Man_t * pNew, int * pArg0, int * pArg1, int nBits )
{
    int iDiffSign = Gia_ManHashXor( pNew, pArg0[nBits-1], pArg1[nBits-1] );
    return Gia_ManHashMux( pNew, iDiffSign, pArg0[nBits-1], Wlc_BlastLess3(pNew, pArg0, pArg1, nBits-1) );
}
void Wlc_BlastFullAdder( Gia_Man_t * pNew, int a, int b, int c, int * pc, int * ps )
{
    int fUseXor = 0;
    int fCompl = (a == 1 || b == 1 || c == 1);
    // propagate complement through the FA - helps generate less redundant logic
    if ( fCompl )
        a = Abc_LitNot(a), b = Abc_LitNot(b), c = Abc_LitNot(c); 
    if ( fUseXor )
    {
        int Xor  = Gia_ManHashXor(pNew, a, b);
        int And1 = Gia_ManHashAnd(pNew, a, b);
        int And2 = Gia_ManHashAnd(pNew, c, Xor);
        *ps      = Gia_ManHashXor(pNew, c, Xor);
        *pc      = Gia_ManHashOr (pNew, And1, And2);
    }
    else
    {
        int And1 = Gia_ManHashAnd(pNew, a, b);
        int And1_= Gia_ManHashAnd(pNew, Abc_LitNot(a), Abc_LitNot(b));
        int Xor  = Gia_ManHashAnd(pNew, Abc_LitNot(And1), Abc_LitNot(And1_));
        int And2 = Gia_ManHashAnd(pNew, c, Xor);
        int And2_= Gia_ManHashAnd(pNew, Abc_LitNot(c), Abc_LitNot(Xor));
        *ps      = Gia_ManHashAnd(pNew, Abc_LitNot(And2), Abc_LitNot(And2_));
        *pc      = Gia_ManHashOr (pNew, And1, And2);
    }
    if ( fCompl )
        *ps = Abc_LitNot(*ps), *pc = Abc_LitNot(*pc); 
}
int Wlc_BlastAdder( Gia_Man_t * pNew, int * pAdd0, int * pAdd1, int nBits, int Carry ) // result is in pAdd0
{
    int b;
    for ( b = 0; b < nBits; b++ )
        Wlc_BlastFullAdder( pNew, pAdd0[b], pAdd1[b], Carry, &Carry, &pAdd0[b] );
    return Carry;
}
void Wlc_BlastSubtract( Gia_Man_t * pNew, int * pAdd0, int * pAdd1, int nBits, int Carry ) // result is in pAdd0
{
    int b;
    for ( b = 0; b < nBits; b++ )
        Wlc_BlastFullAdder( pNew, pAdd0[b], Abc_LitNot(pAdd1[b]), Carry, &Carry, &pAdd0[b] );
}

void Wlc_BlastAdderCLA_one( Gia_Man_t * pNew, int * pGen, int * pPro, int * pCar, int * pGen1, int * pPro1, int * pCar1 )
{
    int Temp = Gia_ManHashAnd( pNew, pGen[0], pPro[1] );
    *pPro1   = Gia_ManHashAnd( pNew, pPro[0], pPro[1] );
    *pGen1   = Gia_ManHashOr( pNew, Gia_ManHashOr(pNew, pGen[1], Temp), Gia_ManHashAnd(pNew, *pPro1, pCar[0]) );
    *pCar1   = Gia_ManHashOr( pNew, pGen[0], Gia_ManHashAnd(pNew, pPro[0], pCar[0]) );
}
void Wlc_BlastAdderCLA_rec( Gia_Man_t * pNew, int * pGen, int * pPro, int * pCar, int nBits, int * pGen1, int * pPro1 )
{
    if ( nBits == 2 )
        Wlc_BlastAdderCLA_one( pNew, pGen, pPro, pCar, pGen1, pPro1, pCar+1 ); // returns *pGen1, *pPro1, pCar[1]
    else
    {
        int pGen2[2], pPro2[2];
        assert( nBits % 2 == 0 );
        // call recursively
        Wlc_BlastAdderCLA_rec( pNew, pGen,         pPro,         pCar,         nBits/2, pGen2,   pPro2   );
        pCar[nBits/2] = *pGen2;
        Wlc_BlastAdderCLA_rec( pNew, pGen+nBits/2, pPro+nBits/2, pCar+nBits/2, nBits/2, pGen2+1, pPro2+1 );
        // create structure
        Wlc_BlastAdderCLA_one( pNew, pGen2, pPro2, pCar, pGen1, pPro1, pCar+nBits/2 ); // returns *pGen1, *pPro1, pCar[nBits/2]
    }
}
void Wlc_BlastAdderCLA_int( Gia_Man_t * pNew, int * pAdd0, int * pAdd1, int nBits, int CarryIn ) // result is in pAdd0
{
    int * pGen = ABC_CALLOC( int, nBits );
    int * pPro = ABC_CALLOC( int, nBits );
    int * pCar = ABC_CALLOC( int, nBits+1 );
    int b, Gen, Pro;
    if ( nBits == 1 )
    {
        int Carry = CarryIn;
        Wlc_BlastFullAdder( pNew, pAdd0[0], pAdd1[0], Carry, &Carry, &pAdd0[0] );
        return;
    }
    assert( nBits >= 2 );
    pCar[0] = CarryIn;
    for ( b = 0; b < nBits; b++ )
    {
        pGen[b] = Gia_ManHashAnd(pNew, pAdd0[b], pAdd1[b]);
        pPro[b] = Gia_ManHashXor(pNew, pAdd0[b], pAdd1[b]);
    }
    Wlc_BlastAdderCLA_rec( pNew, pGen, pPro, pCar, nBits, &Gen, &Pro );
    for ( b = 0; b < nBits; b++ )
        pAdd0[b] = Gia_ManHashXor(pNew, pPro[b], pCar[b]);
    ABC_FREE(pGen);
    ABC_FREE(pPro);
    ABC_FREE(pCar);
}
void Wlc_BlastAdderCLA( Gia_Man_t * pNew, int * pAdd0, int * pAdd1, int nBits, int fSign, int CarryIn ) // result is in pAdd0
{
    int i, Log2 = Abc_Base2Log(nBits);
    int * pAdd0n = ABC_CALLOC( int, 1<<Log2 );
    int * pAdd1n = ABC_CALLOC( int, 1<<Log2 );
    for ( i = 0; i < nBits; i++ )
    {
        pAdd0n[i] = pAdd0[i];
        pAdd1n[i] = pAdd1[i];
    }
    for ( ; i < (1<<Log2); i++ )
    {
        pAdd0n[i] = fSign ? pAdd0[nBits-1] : 0;
        pAdd1n[i] = fSign ? pAdd1[nBits-1] : 0;
    }
    Wlc_BlastAdderCLA_int( pNew, pAdd0n, pAdd1n, 1<<Log2, CarryIn );
    for ( i = 0; i < nBits; i++ )
        pAdd0[i] = pAdd0n[i];
    ABC_FREE(pAdd0n);
    ABC_FREE(pAdd1n);
}

void Wlc_BlastAdderFast_int( Gia_Man_t * pNew, int * pAdd0, int * pAdd1, int Log2, int CarryIn ) // result is in pAdd0
{
    int i, b, Gen, Pro, nBits = 1 << Log2;
    int * pGen = ABC_CALLOC( int, nBits+1 );
    int * pPro = ABC_CALLOC( int, nBits+1 );
    int * pPro2= ABC_CALLOC( int, nBits+1 );
    if ( nBits == 1 )
    {
        int Carry = CarryIn;
        Wlc_BlastFullAdder( pNew, pAdd0[0], pAdd1[0], Carry, &Carry, &pAdd0[0] );
        ABC_FREE(pGen);
        ABC_FREE(pPro);
        ABC_FREE(pPro2);
        return;
    }
    assert( nBits >= 2 );
    pGen[0] = CarryIn;
    pPro[0] = 0;
    pPro2[0]= 0;
    for ( b = 1; b <= nBits; b++ )
    {
        pGen[b] = Gia_ManHashAnd(pNew, pAdd0[b-1], pAdd1[b-1]);
        pPro[b] = Gia_ManHashXor(pNew, pAdd0[b-1], pAdd1[b-1]);
        pPro2[b]= pPro[b];
    }
    
    // Han-Carlson adder from http://www.aoki.ecei.tohoku.ac.jp/arith/mg/algorithm.html
    for ( b = 1; b <= nBits; b += 2 )
    {
        Gen = Gia_ManHashOr( pNew, pGen[b], Gia_ManHashAnd(pNew, pPro[b], pGen[b-1]) );
        Pro = Gia_ManHashAnd(pNew, pPro[b], pPro[b-1]);
        pPro[b] = Pro;
        pGen[b] = Gen;
    }
    for ( i = 1; i < Log2-1; i++ )
    {
        for ( b = 1 + 2*i; b <= nBits; b += 2 )
        {
            Gen = Gia_ManHashOr( pNew, pGen[b], Gia_ManHashAnd(pNew, pPro[b], pGen[b-i*2]) );
            Pro = Gia_ManHashAnd(pNew, pPro[b], pPro[b-i*2]);
            pPro[b] = Pro;
            pGen[b] = Gen;
        }
    }
    for ( b = nBits/2 + 1; b <= nBits; b += 2 )
    {
        Gen = Gia_ManHashOr( pNew, pGen[b], Gia_ManHashAnd(pNew, pPro[b], pGen[b-nBits/2]) );
        Pro = Gia_ManHashAnd(pNew, pPro[b], pPro[b-nBits/2]);
        pPro[b] = Pro;
        pGen[b] = Gen;
    }
    for ( b = 2; b <= nBits; b += 2 )
    {
        Gen = Gia_ManHashOr( pNew, pGen[b], Gia_ManHashAnd(pNew, pPro[b], pGen[b-1]) );
        Pro = Gia_ManHashAnd(pNew, pPro[b], pPro[b-1]);
        pPro[b] = Pro;
        pGen[b] = Gen;
    }
    
    for ( b = 0; b < nBits; b++ )
        pAdd0[b] = Gia_ManHashXor(pNew, pPro2[b+1], pGen[b]);
    pAdd0[nBits] = pGen[nBits];

    ABC_FREE(pGen);
    ABC_FREE(pPro);
    ABC_FREE(pPro2);
}
void Wlc_BlastAdderFast( Gia_Man_t * pNew, int * pAdd0, int * pAdd1, int nBits, int fSign, int CarryIn ) // result is in pAdd0
{
    int i, Log2 = Abc_Base2Log(nBits);
    int * pAdd0n = ABC_CALLOC( int, (1<<Log2)+1 );
    int * pAdd1n = ABC_CALLOC( int, (1<<Log2)+1 );
    for ( i = 0; i < nBits; i++ )
    {
        pAdd0n[i] = pAdd0[i];
        pAdd1n[i] = pAdd1[i];
    }
    for ( ; i < (1<<Log2); i++ )
    {
        pAdd0n[i] = fSign ? pAdd0[nBits-1] : 0;
        pAdd1n[i] = fSign ? pAdd1[nBits-1] : 0;
    }
    Wlc_BlastAdderFast_int( pNew, pAdd0n, pAdd1n, Log2, CarryIn );
    for ( i = 0; i <= nBits; i++ )
        pAdd0[i] = pAdd0n[i];
    ABC_FREE(pAdd0n);
    ABC_FREE(pAdd1n);
}

void Wlc_BlastMinus( Gia_Man_t * pNew, int * pNum, int nNum, Vec_Int_t * vRes )
{
    int * pRes  = Wlc_VecCopy( vRes, pNum, nNum );
    int i, invert = 0;
    for ( i = 0; i < nNum; i++ )
    {
        pRes[i] = Gia_ManHashMux( pNew, invert, Abc_LitNot(pRes[i]), pRes[i] );
        invert = Gia_ManHashOr( pNew, invert, pNum[i] );    
    }
}
void Wlc_BlastMultiplier2( Gia_Man_t * pNew, int * pArg0, int * pArg1, int nBits, Vec_Int_t * vTemp, Vec_Int_t * vRes )
{
    int i, j;
    Vec_IntFill( vRes, nBits, 0 );
    for ( i = 0; i < nBits; i++ )
    {
        Vec_IntFill( vTemp, i, 0 );
        for ( j = 0; Vec_IntSize(vTemp) < nBits; j++ )
            Vec_IntPush( vTemp, Gia_ManHashAnd(pNew, pArg0[j], pArg1[i]) );
        assert( Vec_IntSize(vTemp) == nBits );
        Wlc_BlastAdder( pNew, Vec_IntArray(vRes), Vec_IntArray(vTemp), nBits, 0 );
    }
}
void Wlc_BlastFullAdderCtrl( Gia_Man_t * pNew, int a, int ac, int b, int c, int * pc, int * ps, int fNeg )
{
    int And  = Abc_LitNotCond( Gia_ManHashAnd(pNew, a, ac), fNeg );
    Wlc_BlastFullAdder( pNew, And, b, c, pc, ps );
}
void Wlc_BlastFullAdderSubtr( Gia_Man_t * pNew, int a, int b, int c, int * pc, int * ps, int fSub )
{
    Wlc_BlastFullAdder( pNew, Gia_ManHashXor(pNew, a, fSub), b, c, pc, ps );
}
void Wlc_BlastMultiplier( Gia_Man_t * pNew, int * pArgA, int * pArgB, int nArgA, int nArgB, Vec_Int_t * vTemp, Vec_Int_t * vRes, int fSigned )
{
    int * pRes, * pArgC, * pArgS, a, b, Carry = fSigned;
    assert( nArgA > 0 && nArgB > 0 );
    assert( fSigned == 0 || fSigned == 1 );
    // prepare result
    Vec_IntFill( vRes, nArgA + nArgB, 0 );
    //Vec_IntFill( vRes, nArgA + nArgB + 1, 0 );
    pRes = Vec_IntArray( vRes );
    // prepare intermediate storage
    Vec_IntFill( vTemp, 2 * nArgA, 0 );
    pArgC = Vec_IntArray( vTemp );
    pArgS = pArgC + nArgA;
    // create matrix
    for ( b = 0; b < nArgB; b++ )
        for ( a = 0; a < nArgA; a++ )
            Wlc_BlastFullAdderCtrl( pNew, pArgA[a], pArgB[b], pArgS[a], pArgC[a], 
                &pArgC[a], a ? &pArgS[a-1] : &pRes[b], fSigned && ((a+1 == nArgA) ^ (b+1 == nArgB)) );
    // final addition
    pArgS[nArgA-1] = fSigned;
    for ( a = 0; a < nArgA; a++ )
        Wlc_BlastFullAdderCtrl( pNew, 1, pArgC[a], pArgS[a], Carry, &Carry, &pRes[nArgB+a], 0 );
    //Vec_IntWriteEntry( vRes, nArgA + nArgB, Carry );
}
void Wlc_BlastMultiplierC( Gia_Man_t * pNew, int * pArgA, int * pArgB, int nArgA, int nArgB, Vec_Int_t * vTemp, Vec_Int_t * vRes, int fSigned )
{
    int * pRes, * pArgC, * pArgS, a, b, Carry = !fSigned; // change
    assert( nArgA > 0 && nArgB > 0 );
    assert( fSigned == 0 || fSigned == 1 );
    Vec_IntFill( vRes, nArgA + nArgB, 0 );
    pRes = Vec_IntArray( vRes );
    Vec_IntFill( vTemp, 2 * nArgA, 1 ); // change
    pArgC = Vec_IntArray( vTemp );
    pArgS = pArgC + nArgA;
    for ( b = 0; b < nArgB; b++ )
        for ( a = 0; a < nArgA; a++ )
            Wlc_BlastFullAdderCtrl( pNew, pArgA[a], pArgB[b], pArgS[a], pArgC[a], 
                &pArgC[a], a ? &pArgS[a-1] : &pRes[b], !(fSigned && ((a+1 == nArgA) ^ (b+1 == nArgB))) ); // change
    pArgS[nArgA-1] = !fSigned; // change
    for ( a = 0; a < nArgA; a++ )
        Wlc_BlastFullAdderCtrl( pNew, 1, pArgC[a], pArgS[a], Carry, &Carry, &pRes[nArgB+a], 0 );
    for ( b = 0; b < nArgA + nArgB; b++ ) // change
        pRes[b] = Abc_LitNot(pRes[b]);
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
// non-restoring divider
void Wlc_BlastDividerNR( Gia_Man_t * pNew, int * pNum, int nNum, int * pDiv, int nDiv, int fQuo, Vec_Int_t * vRes )
{
    int i, * pRes  = Vec_IntArray(vRes);
    int k, * pQuo  = ABC_ALLOC( int, nNum );
    assert( nNum > 0 && nDiv > 0 );
    assert( Vec_IntSize(vRes) < nNum + nDiv );
    for ( i = 0; i < nNum + nDiv; i++ )
        pRes[i] = i < nNum ? pNum[i] : 0;
    for ( i = nNum-1; i >= 0; i-- )
    {
        int Cntrl = i == nNum-1 ? 1 : pQuo[i+1];
        int Carry = Cntrl;
        for ( k = 0; k <= nDiv; k++ )
            Wlc_BlastFullAdderSubtr( pNew, k < nDiv ? pDiv[k] : 0, pRes[i+k], Carry, &Carry, &pRes[i+k], Cntrl );
        pQuo[i] = Abc_LitNot(pRes[i+nDiv]);
    }
    if ( fQuo )
        Wlc_VecCopy( vRes, pQuo, nNum );
    else
    {
        int Carry = 0, Temp;
        for ( k = 0; k < nDiv; k++ )
        {
            Wlc_BlastFullAdder( pNew, pDiv[k], pRes[k], Carry, &Carry, &Temp );
            pRes[k] = Gia_ManHashMux( pNew, pQuo[0], pRes[k], Temp );
        }
        Vec_IntShrink( vRes, nDiv );
    }
    ABC_FREE( pQuo );
}
void Wlc_BlastDividerTop( Gia_Man_t * pNew, int * pNum, int nNum, int * pDiv, int nDiv, int fQuo, Vec_Int_t * vRes, int fNonRest )
{
    if ( fNonRest )
        Wlc_BlastDividerNR( pNew, pNum, nNum, pDiv, nDiv, fQuo, vRes );
    else
        Wlc_BlastDivider( pNew, pNum, nNum, pDiv, nDiv, fQuo, vRes );
}
void Wlc_BlastDividerSigned( Gia_Man_t * pNew, int * pNum, int nNum, int * pDiv, int nDiv, int fQuo, Vec_Int_t * vRes, int fNonRest )
{
    Vec_Int_t * vNum   = Vec_IntAlloc( nNum );
    Vec_Int_t * vDiv   = Vec_IntAlloc( nDiv );
    Vec_Int_t * vRes00 = Vec_IntAlloc( nNum + nDiv );
    Vec_Int_t * vRes01 = Vec_IntAlloc( nNum + nDiv );
    Vec_Int_t * vRes10 = Vec_IntAlloc( nNum + nDiv );
    Vec_Int_t * vRes11 = Vec_IntAlloc( nNum + nDiv );
    Vec_Int_t * vRes2  = Vec_IntAlloc( nNum );
    int k, iDiffSign   = Gia_ManHashXor( pNew, pNum[nNum-1], pDiv[nDiv-1] );
    Wlc_BlastMinus( pNew, pNum, nNum, vNum );
    Wlc_BlastMinus( pNew, pDiv, nDiv, vDiv );
    Wlc_BlastDividerTop( pNew,               pNum, nNum,               pDiv, nDiv, fQuo, vRes00, fNonRest );
    Wlc_BlastDividerTop( pNew,               pNum, nNum, Vec_IntArray(vDiv), nDiv, fQuo, vRes01, fNonRest );
    Wlc_BlastDividerTop( pNew, Vec_IntArray(vNum), nNum,               pDiv, nDiv, fQuo, vRes10, fNonRest );
    Wlc_BlastDividerTop( pNew, Vec_IntArray(vNum), nNum, Vec_IntArray(vDiv), nDiv, fQuo, vRes11, fNonRest );
    Vec_IntClear( vRes );
    for ( k = 0; k < nNum; k++ )
    {
        int Data0 =  Gia_ManHashMux( pNew, pDiv[nDiv-1], Vec_IntEntry(vRes01,k), Vec_IntEntry(vRes00,k) );
        int Data1 =  Gia_ManHashMux( pNew, pDiv[nDiv-1], Vec_IntEntry(vRes11,k), Vec_IntEntry(vRes10,k) );
        Vec_IntPush( vRes, Gia_ManHashMux(pNew, pNum[nNum-1], Data1, Data0) );
    }
    Wlc_BlastMinus( pNew, Vec_IntArray(vRes), nNum, vRes2 );
    for ( k = 0; k < nNum; k++ )
        Vec_IntWriteEntry( vRes, k, Gia_ManHashMux(pNew, fQuo ? iDiffSign : pNum[nNum-1], Vec_IntEntry(vRes2,k), Vec_IntEntry(vRes,k)) );
    Vec_IntFree( vNum );
    Vec_IntFree( vDiv );
    Vec_IntFree( vRes00 );
    Vec_IntFree( vRes01 );
    Vec_IntFree( vRes10 );
    Vec_IntFree( vRes11 );
    Vec_IntFree( vRes2 );
    assert( Vec_IntSize(vRes) == nNum );
}
void Wlc_BlastZeroCondition( Gia_Man_t * pNew, int * pDiv, int nDiv, Vec_Int_t * vRes )
{
    int i, Entry, iLit = Wlc_BlastReduction( pNew, pDiv, nDiv, WLC_OBJ_REDUCT_OR );
    Vec_IntForEachEntry( vRes, Entry, i )
        Vec_IntWriteEntry( vRes, i, Gia_ManHashAnd(pNew, iLit, Entry) );
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
void Wlc_BlastLut( Gia_Man_t * pNew, word Truth, int * pFans, int nFans, int nOuts, Vec_Int_t * vRes )
{
    extern int Kit_TruthToGia( Gia_Man_t * pMan, unsigned * pTruth, int nVars, Vec_Int_t * vMemory, Vec_Int_t * vLeaves, int fHash );
    Vec_Int_t * vMemory = Vec_IntAlloc( 0 );
    Vec_Int_t vLeaves = { nFans, nFans, pFans };
    int iLit;
    Vec_IntClear( vRes );
    assert( nOuts == 1 );
    if ( nFans < 6 )
        Truth = Abc_Tt6Stretch( Truth, nFans );
    iLit = Kit_TruthToGia( pNew, (unsigned *)&Truth, nFans, vMemory, &vLeaves, 1 );
    Vec_IntPush( vRes, iLit );
    Vec_IntFree( vMemory );
}
void Wlc_BlastPower( Gia_Man_t * pNew, int * pNum, int nNum, int * pExp, int nExp, Vec_Int_t * vTemp, Vec_Int_t * vRes )
{
    Vec_Int_t * vDegrees = Vec_IntAlloc( 2*nNum );
    Vec_Int_t * vResTemp = Vec_IntAlloc( 2*nNum );
    int i, * pDegrees = NULL, * pRes = Vec_IntArray(vRes);
    int k, * pResTemp = Vec_IntArray(vResTemp);
    Vec_IntFill( vRes, nNum, 0 );
    Vec_IntWriteEntry( vRes, 0, 1 );
    for ( i = 0; i < nExp; i++ )
    {
        if ( i == 0 )
            pDegrees = Wlc_VecCopy( vDegrees, pNum, nNum );
        else
        {
            Wlc_BlastMultiplier2( pNew, pDegrees, pDegrees, nNum, vTemp, vResTemp );
            pDegrees = Wlc_VecCopy( vDegrees, pResTemp, nNum );
        }
        Wlc_BlastMultiplier2( pNew, pRes, pDegrees, nNum, vTemp, vResTemp );
        for ( k = 0; k < nNum; k++ )
            pRes[k] = Gia_ManHashMux( pNew, pExp[i], pResTemp[k], pRes[k] );
    }
    Vec_IntFree( vResTemp );
    Vec_IntFree( vDegrees );
}
void Wlc_BlastSqrt( Gia_Man_t * pNew, int * pNum, int nNum, Vec_Int_t * vTmp, Vec_Int_t * vRes )
{
    int * pRes, * pSum, * pSumP;
    int i, k, Carry = -1;
    assert( nNum % 2 == 0 );
    Vec_IntFill( vRes, nNum/2, 0 );
    Vec_IntFill( vTmp, 2*nNum, 0 );
    pRes = Vec_IntArray( vRes );
    pSum = Vec_IntArray( vTmp );
    pSumP = pSum + nNum;
    for ( i = 0; i < nNum/2; i++ )
    {
        pSumP[0] = pNum[nNum-2*i-2];
        pSumP[1] = pNum[nNum-2*i-1];
        for ( k = 0; k < i+1; k++ )
            pSumP[k+2] = pSum[k];
        for ( k = 0; k < i + 3; k++ )
        {
            if ( k >= 2 && k < i + 2 ) // middle ones
                Wlc_BlastFullAdder( pNew, pSumP[k], Abc_LitNot(pRes[i-k+1]), Carry, &Carry, &pSum[k] );
            else
                Wlc_BlastFullAdder( pNew, pSumP[k], Abc_LitNot(k ? Carry:1), 1,     &Carry, &pSum[k] );
            if ( k == 0 || k > i )
                Carry = Abc_LitNot(Carry);
        }
        pRes[i] = Abc_LitNot(Carry);
        for ( k = 0; k < i + 3; k++ )
            pSum[k] = Gia_ManHashMux( pNew, pRes[i], pSum[k], pSumP[k] );
    }
    Vec_IntReverseOrder( vRes );
}
void Wlc_BlastSqrtNR( Gia_Man_t * pNew, int * pNum, int nNum, Vec_Int_t * vTmp, Vec_Int_t * vRes )
{
    int * pSqr, * pRem, * pIn1;
    int i, k, Carry = 1;
    assert( nNum % 2 == 0 );
    Vec_IntFill( vRes, nNum/2, 0 );
    Vec_IntFill( vTmp, 2*nNum, 0 );
    pSqr = Vec_IntArray( vRes );
    pRem = Vec_IntArray( vTmp );
    pIn1 = pRem + nNum;
    for ( i = 0; i < nNum/2; i++ )
    {
        int SqrPrev = Carry;
        assert( pIn1[0] == 0 );
        for ( k = 1; k < i; k++ )
            pIn1[k] = 0;
        for ( k = i; k < 2*i; k++ )
            pIn1[k] = pSqr[k-i];
        pIn1[k++] = Abc_LitNot(Carry);
        pIn1[k++] = 1;
        assert( k == 2*i+2 );
        pRem[2*i+0] = pNum[nNum-2*i-1];
        pRem[2*i+1] = pNum[nNum-2*i-2];
        for ( k = 2*i+1; k >= 0; k-- )
            Wlc_BlastFullAdder( pNew, Gia_ManHashXor(pNew, SqrPrev, pIn1[k]), pRem[k], Carry, &Carry, &pRem[k] );
        pSqr[i] = Carry;
    }
    Vec_IntReverseOrder( vRes );
}
void Wlc_IntInsert( Vec_Int_t * vProd, Vec_Int_t * vLevel, int Node, int Level )
{
    int i;
    for ( i = Vec_IntSize(vLevel) - 1; i >= 0; i-- )
        if ( Vec_IntEntry(vLevel, i) >= Level )
            break;
    Vec_IntInsert( vProd,  i + 1, Node  );
    Vec_IntInsert( vLevel, i + 1, Level );
}
void Wlc_BlastPrintMatrix( Gia_Man_t * p, Vec_Wec_t * vProds, int fVerbose )
{
    Vec_Int_t * vSupp = Vec_IntAlloc( 100 );
    Vec_Wrd_t * vTemp = Vec_WrdStart( Gia_ManObjNum(p) );
    Vec_Int_t * vLevel;  word Truth;
    int i, k, iLit; 
    Vec_WecForEachLevel( vProds, vLevel, i )
        Vec_IntForEachEntry( vLevel, iLit, k )
            if ( Gia_ObjIsAnd(Gia_ManObj(p, Abc_Lit2Var(iLit))) )
                Vec_IntPushUnique( vSupp, Abc_Lit2Var(iLit) );
    printf( "Booth partial products: %d pps, %d unique, %d nodes.\n", 
        Vec_WecSizeSize(vProds), Vec_IntSize(vSupp), Gia_ManAndNum(p) );
    Vec_IntPrint( vSupp );

    if ( fVerbose )
    Vec_WecForEachLevel( vProds, vLevel, i )
        Vec_IntForEachEntry( vLevel, iLit, k )
        {
            printf( "Obj = %4d : ", Abc_Lit2Var(iLit) );
            printf( "Compl = %d  ", Abc_LitIsCompl(iLit) );
            printf( "Rank = %2d  ", i );
            Truth = Gia_ObjComputeTruth6Cis( p, iLit, vSupp, vTemp );
            Extra_PrintHex( stdout, (unsigned*)&Truth, Vec_IntSize(vSupp) );
            if ( Vec_IntSize(vSupp) == 4 ) printf( "    " );
            if ( Vec_IntSize(vSupp) == 3 ) printf( "      " );
            if ( Vec_IntSize(vSupp) <= 2 ) printf( "       " );
            printf( "  " );
            Vec_IntPrint( vSupp );
            if ( k == Vec_IntSize(vLevel)-1 )
                printf( "\n" );
        }
    Vec_IntFree( vSupp );
    Vec_WrdFree( vTemp );
}
// the final adder is driven by the arrival profile if pTim is given, otherwise it is carry-look-ahead (fCla) or ripple-carry;
// if nBitsRes is positive, only the nBitsRes least significant columns are added and returned
void Wlc_BlastReduceMatrix( Gia_Man_t * pNew, Vec_Wec_t * vProds, Vec_Wec_t * vLevels, Vec_Int_t * vRes, int fSigned, int fCla, Wlc_BlastTim_t * pTim, int nBitsRes )
{
    Vec_Int_t * vLevel, * vProd;
    int i, NodeS, NodeC, LevelS, LevelC, Node1, Node2, Node3, Level1, Level2, Level3, nBits;
    int nSize = Vec_WecSize(vProds), nFAs = Vec_WecSize(vProds), nHAs = 0;
    assert( nSize == Vec_WecSize(vLevels) );
    for ( i = 0; i < nSize; i++ )
    {
        while ( 1 )
        {
            vProd  = Vec_WecEntry( vProds, i );
            if ( Vec_IntSize(vProd) < 3 )
                break;

            Node1  = Vec_IntPop( vProd );
            Node2  = Vec_IntPop( vProd );
            Node3  = Vec_IntPop( vProd );

            vLevel = Vec_WecEntry( vLevels, i );

            Level1 = Vec_IntPop( vLevel );
            Level2 = Vec_IntPop( vLevel );
            Level3 = Vec_IntPop( vLevel );

            int nInputs = (Node1 > 1) + (Node2 > 1) + (Node3 > 1);
            if ( nInputs == 3 )
                nFAs++;
            else if ( nInputs == 2 )
                nHAs++;            

            Wlc_BlastFullAdder( pNew, Node1, Node2, Node3, &NodeC, &NodeS );
            LevelS = Abc_MaxInt( Abc_MaxInt(Level1, Level2), Level3 ) + 2;
            LevelC = LevelS - 1;

            Wlc_IntInsert( vProd, vLevel, NodeS, LevelS );

            vProd  = Vec_WecEntry( vProds, i+1 );
            vLevel = Vec_WecEntry( vLevels, i+1 );

            Wlc_IntInsert( vProd, vLevel, NodeC, LevelC );
        }
    }

    // make all ranks have two products
    for ( i = 0; i < nSize; i++ )
    {
        vProd  = Vec_WecEntry( vProds, i );
        while ( Vec_IntSize(vProd) < 2 )
            Vec_IntPush( vProd, 0 ), nFAs--, nHAs++;
        assert( Vec_IntSize(vProd) == 2 );
    }
//    Vec_WecPrint( vProds, 0 );

    vLevel = Vec_WecEntry( vLevels, 0 );
    Vec_IntClear( vRes );
    Vec_IntClear( vLevel );
    for ( i = 0; i < nSize; i++ )
    {
        vProd  = Vec_WecEntry( vProds, i );
        Vec_IntPush( vRes,   Vec_IntEntry(vProd, 0) );
        Vec_IntPush( vLevel, Vec_IntEntry(vProd, 1) );
    }
    Vec_IntPush( vRes,   0 );
    Vec_IntPush( vLevel, 0 );

    nBits = nBitsRes > 0 ? Abc_MinInt( nBitsRes, Vec_IntSize(vRes) ) : Vec_IntSize(vRes);
    if ( pTim )
        Wlc_BlastAdderProfile( pNew, pTim, Vec_IntArray(vRes), Vec_IntArray(vLevel), nBits, 1, 1 );
    else if ( fCla )
        Wlc_BlastAdderCLA( pNew, Vec_IntArray(vRes), Vec_IntArray(vLevel), nBits, fSigned, 0 );
    else
        Wlc_BlastAdder( pNew, Vec_IntArray(vRes), Vec_IntArray(vLevel), nBits, 0 );
    Vec_IntShrink( vRes, nBits );
    //printf( "Created %d-bit %d-input AT with %d FAs and %d HAs.\n", Vec_WecSize(vProds), Vec_WecSizeSize(vProds), nFAs, nHAs );
}

int Wlc_BlastAddLevel( Gia_Man_t * pNew, int Start )
{
    int i;
    if ( Start == 0 )
        Gia_ManCleanLevels( pNew, 5 * Gia_ManObjNum(pNew) );
    for ( i = Start; i < Gia_ManObjNum(pNew); i++ )
    {
        Gia_Obj_t * pObj = Gia_ManObj( pNew, i );
        if ( Gia_ObjIsAnd(pObj) )
            Gia_ObjSetAndLevel( pNew, pObj );
    }
    return Gia_ManObjNum(pNew);
}
void Wlc_IntInsert2( Gia_Man_t * pNew, Vec_Int_t * vProd, int iLit )
{
    int i, Entry, Level = Gia_ObjLevelId(pNew, Abc_Lit2Var(iLit));
    Vec_IntForEachEntryReverse( vProd, Entry, i )
        if ( Gia_ObjLevelId(pNew, Abc_Lit2Var(Entry)) >= Level )
            break;
    Vec_IntInsert( vProd, i + 1, iLit );
//    Vec_IntForEachEntry( vProd, Entry, i )
//        printf( "Obj=%d(%d) ", Abc_Lit2Var(Entry), Gia_ObjLevelId(pNew, Abc_Lit2Var(Entry)) );
//    printf( "\n" );
}
void Wlc_IntSortCostReverse( Gia_Man_t * pNew, int * pArray, int nSize )
{
    int i, j, best_i;
    for ( i = 0; i < nSize-1; i++ )
    {
        best_i = i;
        for ( j = i+1; j < nSize; j++ )
            if ( Gia_ObjLevelId(pNew, Abc_Lit2Var(pArray[j])) > Gia_ObjLevelId(pNew, Abc_Lit2Var(pArray[best_i])) )
                best_i = j;
        ABC_SWAP( int, pArray[i], pArray[best_i] );
    }
}
void Wlc_BlastReduceMatrix2( Gia_Man_t * pNew, Vec_Wec_t * vProds, Vec_Int_t * vRes, int fSigned, int fCla )
{
    Vec_Int_t * vProd, * vTemp;
    int i, NodeS, NodeC, Node1, Node2, Node3;
    int Start = Wlc_BlastAddLevel( pNew, 0 );
    int nSize = Vec_WecSize(vProds);
    Vec_WecForEachLevel( vProds, vProd, i )
        Wlc_IntSortCostReverse( pNew, Vec_IntArray(vProd), Vec_IntSize(vProd) );
    for ( i = 0; i < nSize; i++ )
    {
        while ( 1 )
        {
            vProd = Vec_WecEntry( vProds, i );
            if ( Vec_IntSize(vProd) < 3 )
                break;

            Node1  = Vec_IntPop( vProd );
            Node2  = Vec_IntPop( vProd );
            Node3  = Vec_IntPop( vProd );

            assert( Gia_ObjLevelId(pNew, Abc_Lit2Var(Node3)) >= Gia_ObjLevelId(pNew, Abc_Lit2Var(Node2)) );
            assert( Gia_ObjLevelId(pNew, Abc_Lit2Var(Node2)) >= Gia_ObjLevelId(pNew, Abc_Lit2Var(Node1)) );

            Wlc_BlastFullAdder( pNew, Node1, Node2, Node3, &NodeC, &NodeS );
            Start = Wlc_BlastAddLevel( pNew, Start );

            Wlc_IntInsert2( pNew, vProd, NodeS );

            vProd  = Vec_WecEntry( vProds, i+1 );
            Wlc_IntInsert2( pNew, vProd, NodeC );
        }
    }

    // make all ranks have two products
    for ( i = 0; i < nSize; i++ )
    {
        vProd  = Vec_WecEntry( vProds, i );
        while ( Vec_IntSize(vProd) < 2 )
            Vec_IntPush( vProd, 0 );
        assert( Vec_IntSize(vProd) == 2 );
    }
//    Vec_WecPrint( vProds, 0 );

    Vec_IntClear( vRes );
    vTemp = Vec_IntAlloc( 100 );
    for ( i = 0; i < nSize; i++ )
    {
        vProd  = Vec_WecEntry( vProds, i );
        Vec_IntPush( vRes,  Vec_IntEntry(vProd, 0) );
        Vec_IntPush( vTemp, Vec_IntEntry(vProd, 1) );
    }
    Vec_IntPush( vRes,  0 );
    Vec_IntPush( vTemp, 0 );

    if ( fCla )
        Wlc_BlastAdderCLA( pNew, Vec_IntArray(vRes), Vec_IntArray(vTemp), Vec_IntSize(vRes), fSigned, 0 );
    else
        Wlc_BlastAdder( pNew, Vec_IntArray(vRes), Vec_IntArray(vTemp), Vec_IntSize(vRes), 0 );
    Vec_IntFree( vTemp );
}

void Wlc_BlastMultiplier3( Gia_Man_t * pNew, int * pArgA, int * pArgB, int nArgA, int nArgB, Vec_Int_t * vRes, int fSigned, int fCla, Vec_Wec_t ** pvProds, int fVerbose )
{
    Vec_Wec_t * vProds  = Vec_WecStart( nArgA + nArgB );
    Vec_Wec_t * vLevels = Vec_WecStart( nArgA + nArgB );
    int i, k;
    for ( i = 0; i < nArgA; i++ )
        for ( k = 0; k < nArgB; k++ )
        {
            int fCompl = fSigned && ((i == nArgA-1) ^ (k == nArgB-1));
            Vec_WecPush( vProds,  i+k, Abc_LitNotCond(Gia_ManHashAnd(pNew, pArgA[i], pArgB[k]), fCompl) );
            Vec_WecPush( vLevels, i+k, 0 );
        }
    if ( fSigned )
    {
        Vec_WecPush( vProds,  nArgB-1, 1 );
        Vec_WecPush( vLevels, nArgB-1, 0 );

        Vec_WecPush( vProds,  nArgA-1, 1 );
        Vec_WecPush( vLevels, nArgA-1, 0 );

        Vec_WecPush( vProds,  nArgA+nArgB-1, 1 );
        Vec_WecPush( vLevels, nArgA+nArgB-1, 0 );
    }
    if ( fVerbose )
        Vec_WecPrint( vProds, 0 );
    if ( pvProds )
        *pvProds = Vec_WecDup(vProds);
    else
        Wlc_BlastReduceMatrix( pNew, vProds, vLevels, vRes, fSigned, fCla, NULL, 0 );
//    Wlc_BlastReduceMatrix2( pNew, vProds, vRes, fSigned, fCla );

    Vec_WecFree( vProds );
    Vec_WecFree( vLevels );
}
void Wlc_BlastSquare( Gia_Man_t * pNew, int * pNum, int nNum, Vec_Int_t * vTmp, Vec_Int_t * vRes )
{
    Vec_Wec_t * vProds  = Vec_WecStart( 2*nNum );
    Vec_Wec_t * vLevels = Vec_WecStart( 2*nNum );
    int i, k;
    for ( i = 0; i < nNum; i++ )
        for ( k = 0; k < nNum; k++ )
        {
            if ( i == k )
            {
                Vec_WecPush( vProds,  i+k, pNum[i] );
                Vec_WecPush( vLevels, i+k, 0 );
            }
            else if ( i < k )
            {
                Vec_WecPush( vProds,  i+k+1, Gia_ManHashAnd(pNew, pNum[i], pNum[k]) );
                Vec_WecPush( vLevels, i+k+1, 0 );
            }
        }

    Wlc_BlastReduceMatrix( pNew, vProds, vLevels, vRes, 0, 0, NULL, 0 );

    Vec_WecFree( vProds );
    Vec_WecFree( vLevels );
}
void Wlc_BlastDecoder( Gia_Man_t * pNew, int * pNum, int nNum, Vec_Int_t * vTmp, Vec_Int_t * vRes )
{
    int i, k, nMints = 1 << nNum;
    Vec_IntClear( vRes );
    for ( i = 0; i < nMints; i++ )
    {
        int iMint = 1;
        for ( k = 0; k < nNum; k++ )
            iMint = Gia_ManHashAnd( pNew, iMint, Abc_LitNotCond(pNum[k], !((i >> k) & 1)) );
        Vec_IntPush( vRes, iMint );
    }
}
Vec_Int_t * Wlc_BlastDecoder2_rec( Gia_Man_t * p, int * pLits, int nLits )
{
    if ( nLits == 1 )
    {
        Vec_Int_t * vRes = Vec_IntAlloc( 2 );
        Vec_IntPush( vRes, Abc_LitNot(pLits[0]) );
        Vec_IntPush( vRes, pLits[0] );
        return vRes;
    }
    assert( nLits > 1 );
    int nPart1 = nLits / 2;
    int nPart2 = nLits - nPart1;
    Vec_Int_t * vRes1 = Wlc_BlastDecoder2_rec( p, pLits, nPart1 );
    Vec_Int_t * vRes2 = Wlc_BlastDecoder2_rec( p, pLits+nPart1, nPart2 );
    Vec_Int_t * vRes = Vec_IntAlloc( Vec_IntSize(vRes1) * Vec_IntSize(vRes2) );
    int i, k, Lit1, Lit2;
    Vec_IntForEachEntry( vRes2, Lit2, k )
    Vec_IntForEachEntry( vRes1, Lit1, i )
        Vec_IntPush( vRes, Gia_ManHashAnd(p, Lit1, Lit2) );
    Vec_IntFree( vRes1 );
    Vec_IntFree( vRes2 );
    return vRes;   
}
Vec_Int_t * Wlc_BlastDecoder2( Gia_Man_t * pNew, int * pNum, int nNum, Vec_Int_t * vTmp, Vec_Int_t * vRes )
{
    Vec_Int_t * vRes2 = Wlc_BlastDecoder2_rec( pNew, pNum, nNum );
    Vec_IntClear( vRes );
    Vec_IntAppend( vRes, vRes2 );
    Vec_IntFree( vRes2 );
    return vRes;
}
void Wlc_DumpMatrix( Gia_Man_t * pNew, Vec_Wec_t * vProds )
{
    char * pFileName = "booth_pps.aig";
    Vec_Int_t * vLevel; int i, k, Entry;
    Vec_WecForEachLevel( vProds, vLevel, i )
        Vec_IntForEachEntry( vLevel, Entry, k )
            Gia_ManAppendCo(pNew, Entry);
    Gia_AigerWrite( pNew, pFileName, 0, 0, 0 );
    printf( "Finished dumping Booth PPs into \"%s\".\n", pFileName );
    exit(1);
}
void Wlc_BlastBooth( Gia_Man_t * pNew, int * pArgA, int * pArgB, int nArgA, int nArgB, Vec_Int_t * vRes, int fSigned, int fFastAdder, Vec_Wec_t ** pvProds, int fVerbose )
{
    Vec_Wec_t * vProds  = Vec_WecStart( nArgA + nArgB + 3 );
    Vec_Wec_t * vLevels = Vec_WecStart( nArgA + nArgB + 3 );
    Wlc_BlastTim_t * pTim = NULL; // timing memo for the arrival-driven final adder
    int FillA = fSigned ? pArgA[nArgA-1] : 0;
    int FillB = fSigned ? pArgB[nArgB-1] : 0;
    int i, k, Sign;
    if ( fFastAdder && pvProds == NULL )
    {
        pTim = Wlc_BlastTimStart();
        Wlc_BlastTimNewGen( pTim, pNew );
        Wlc_BlastTimSetInputs( pTim, pArgA, nArgA );
        Wlc_BlastTimSetInputs( pTim, pArgB, nArgB );
    }

    // extend argument B
    Vec_Int_t * vArgB = Vec_IntAlloc( nArgB + 2 );
    Vec_IntPush( vArgB, 0 );
    for ( i = 0; i < nArgB; i++ )
        Vec_IntPush( vArgB, pArgB[i] );
    if ( !fSigned )
        Vec_IntPushTwo( vArgB, FillB, FillB );
    if ( Vec_IntSize(vArgB) % 2 == 0 )
        Vec_IntPush( vArgB, FillB );
    assert( Vec_IntSize(vArgB) % 2 == 1 );

    // iterate through bit-pairs of B
    for ( k = 0; k+2 < Vec_IntSize(vArgB); k+=2 )
    {
        int pp    = -1;
        int Q2jM1 = Vec_IntEntry(vArgB, k);   // q(2*j-1)
        int Q2j   = Vec_IntEntry(vArgB, k+1); // q(2*j+0)
        int Q2jP1 = Vec_IntEntry(vArgB, k+2); // q(2*j+1)
        int Neg   = Q2jP1;
        int One   = Gia_ManHashXor( pNew, Q2j, Q2jM1 );
        int Two   = Gia_ManHashMux( pNew, Neg, Gia_ManHashAnd(pNew, Abc_LitNot(Q2j), Abc_LitNot(Q2jM1)), Gia_ManHashAnd(pNew, Q2j, Q2jM1) );
        for ( i = 0; i <= nArgA; i++ )
        {
            int This = i == nArgA ? FillA : pArgA[i];
            int Prev = i ? pArgA[i-1] : 0;
            int Part = Gia_ManHashOr( pNew, Gia_ManHashAnd(pNew, One, This), Gia_ManHashAnd(pNew, Two, Prev) );
            pp = Gia_ManHashXor( pNew, Part, Neg );
            if ( fVerbose ) printf( "%4d = PP(%5d %5d  %5d %5d %5d)\n", pp, Prev, This, Q2jM1, Q2j, Q2jP1 );
            if ( pp == 0 || (fSigned && i == nArgA) )
                continue;
            if ( pp )
            {
                Vec_WecPush( vProds,  k+i, pp );
                Vec_WecPush( vLevels, k+i, 0 );
            }
        }
        if ( fSigned ) i--;
        // perform sign extension
        Sign = fSigned ? pp : Neg;
        if ( k == 0 )
        {
            Vec_WecPush( vProds,  k+i, Sign );
            Vec_WecPush( vLevels, k+i, 0 );

            Vec_WecPush( vProds,  k+i+1, Sign );
            Vec_WecPush( vLevels, k+i+1, 0 );

            if ( Sign != 1 )
            {
            Vec_WecPush( vProds,  k+i+2, Abc_LitNot(Sign) );
            Vec_WecPush( vLevels, k+i+2, 0 );
            }
        }
        else 
        {
            if ( Sign != 1 )
            {
            Vec_WecPush( vProds,  k+i, Abc_LitNot(Sign) );
            Vec_WecPush( vLevels, k+i, 0 );
            }

            Vec_WecPush( vProds,  k+i+1, 1 );
            Vec_WecPush( vLevels, k+i+1, 0 );
        }
        // add neg to the first column
        if ( Neg == 0 )
            continue;
        Vec_WecPush( vProds,  k, Neg );
        Vec_WecPush( vLevels, k, 0 );
    }
    //Vec_WecShrink( vProds,  nArgA + nArgB );
    //Vec_WecShrink( vLevels, nArgA + nArgB );   
    if ( fVerbose )
        Vec_WecPrint( vProds, 0 );
    if ( fVerbose ) 
        printf( "Total PPs = %d.\n", Vec_WecSizeSize(vProds) );
    //Wlc_DumpMatrix( pNew, vProds );
    //Wlc_BlastPrintMatrix( pNew, vProds, 1 );
    //printf( "Cutoff ID for partial products = %d.\n", Gia_ManObjNum(pNew) );
    if ( pvProds )
        *pvProds = Vec_WecDup(vProds);
    else
    {
        // the columns above the product width hold the leftovers of the sign-extension trick
        Wlc_BlastReduceMatrix( pNew, vProds, vLevels, vRes, fSigned, 0, pTim, nArgA + nArgB );
    }
    //    Wlc_BlastReduceMatrix2( pNew, vProds, vRes, fSigned, fCla );
    if ( pTim )
        Wlc_BlastTimStop( pTim );
    Vec_WecFree( vProds );
    Vec_WecFree( vLevels );
    Vec_IntFree( vArgB );
}

/**Function*************************************************************

  Synopsis    [Arrival-driven multipliers following Yeh and Jen (IEEE TC, July 2000).]

  Description [Overview of the code below: the timing memo (Wlc_BlastTim_t),
  the final adder (Wlc_BlastAdderProfile), the column reduction
  (Wlc_BlastYjReduce), and the Booth (Wlc_BlastBoothYJ) and Wallace
  (Wlc_BlastWallace) generators. The Booth multiplier implements the three
  parts of the paper. (1) Modified Booth
  encoding in which the multiplicand bits are XORed with the negation signal
  before the one/two selection, so that the negation does not add a serial
  XOR after the selection; the zero digit produces an all-zero row without
  a correction bit. (2) Partial-product array in which the LSB of every row
  and its negation carry are folded into two precomputed signals (eqs. (2)
  and (3) of the paper), removing one entry from each even column.
  (3) TDM-style column reduction (three earliest signals of a column enter
  one full adder, the slowest on the carry-in) driven by the actual AIG
  levels of the signals, followed by a final adder. With fFastAdder, the
  block structure of the final adder follows the arrival profile of the two
  reduced rows; this adder is an adaptation of the paper's MLCSMA to the AIG
  cost model rather than a transcription of it (Wlc_BlastAdderProfile lists
  the differences). Without fFastAdder, the final adder is ripple-carry.
  Parts (3) and the final adder are shared with the Wallace-tree multiplier
  (Wlc_BlastWallace), which reduces plain AND partial products instead of
  Booth-encoded ones; the reduction is in Wlc_BlastYjReduce.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
// Timing memo of the arrival-driven multiplier. Objects created by the current
// multiplier (ID >= iBase) are memoized in a dense array indexed by ID - iBase;
// the few older objects it touches (its operands, which are preset to level 0,
// and nodes returned by structural hashing) go into a small hash table. Both
// cost only what the multiplier visits. An array covering the whole AIG for
// every multiplier made designs with many multipliers quadratic.
Wlc_BlastTim_t * Wlc_BlastTimStart( void )
{
    Wlc_BlastTim_t * p = ABC_CALLOC( Wlc_BlastTim_t, 1 );
    p->vLev = Vec_IntAlloc( 1000 );
    p->vOld = Vec_IntAlloc( 0 );
    return p;
}
void Wlc_BlastTimStop( Wlc_BlastTim_t * p )
{
    Vec_IntFree( p->vLev );
    Vec_IntFree( p->vOld );
    ABC_FREE( p );
}
// forgets all memoized levels; objects created from now on are the new ones
void Wlc_BlastTimNewGen( Wlc_BlastTim_t * p, Gia_Man_t * pGia )
{
    p->iBase = Gia_ManObjNum( pGia );
    p->nOld  = 0;
    Vec_IntClear( p->vLev );
    Vec_IntFill( p->vOld, Vec_IntSize(p->vOld), -1 );
}
static inline int Wlc_BlastTimHash( int iObj, int nSlots )
{
    return (int)(((unsigned)iObj * 2654435761u) & (unsigned)(nSlots - 1));
}
// open-addressing hash of (object ID -> level); empty slots have key -1
static inline int Wlc_BlastTimOldLookup( Wlc_BlastTim_t * p, int iObj )
{
    int nSlots = Vec_IntSize(p->vOld) / 2, s;
    if ( nSlots == 0 )
        return -1;
    for ( s = Wlc_BlastTimHash(iObj, nSlots); Vec_IntEntry(p->vOld, 2*s) != -1; s = (s + 1) & (nSlots - 1) )
        if ( Vec_IntEntry(p->vOld, 2*s) == iObj )
            return Vec_IntEntry( p->vOld, 2*s+1 );
    return -1;
}
static void Wlc_BlastTimOldInsert( Wlc_BlastTim_t * p, int iObj, int Level )
{
    int nSlots = Vec_IntSize(p->vOld) / 2, s;
    if ( 2 * (p->nOld + 1) > nSlots )
    {
        // grow and rehash
        Vec_Int_t * vOld = p->vOld;
        int i, nNew = Abc_MaxInt( 64, 4 * nSlots );
        p->vOld = Vec_IntStartFull( 2 * nNew );
        p->nOld = 0;
        for ( i = 0; i < Vec_IntSize(vOld); i += 2 )
            if ( Vec_IntEntry(vOld, i) != -1 )
                Wlc_BlastTimOldInsert( p, Vec_IntEntry(vOld, i), Vec_IntEntry(vOld, i+1) );
        Vec_IntFree( vOld );
        nSlots = nNew;
    }
    for ( s = Wlc_BlastTimHash(iObj, nSlots); Vec_IntEntry(p->vOld, 2*s) != -1; s = (s + 1) & (nSlots - 1) )
        if ( Vec_IntEntry(p->vOld, 2*s) == iObj )
        {
            Vec_IntWriteEntry( p->vOld, 2*s+1, Level );
            return;
        }
    Vec_IntWriteEntry( p->vOld, 2*s,   iObj );
    Vec_IntWriteEntry( p->vOld, 2*s+1, Level );
    p->nOld++;
}
static inline void Wlc_BlastTimSet( Wlc_BlastTim_t * p, int iObj, int Level )
{
    if ( iObj < p->iBase )
        Wlc_BlastTimOldInsert( p, iObj, Level );
    else
    {
        Vec_IntFillExtra( p->vLev, iObj - p->iBase + 1, -1 );
        Vec_IntWriteEntry( p->vLev, iObj - p->iBase, Level );
    }
}
// the operands of the arithmetic unit arrive at time 0
void Wlc_BlastTimSetInputs( Wlc_BlastTim_t * p, int * pLits, int nLits )
{
    int i;
    for ( i = 0; i < nLits; i++ )
        Wlc_BlastTimSet( p, Abc_Lit2Var(pLits[i]), 0 );
}
// returns -1 if the level of the object is not memoized
static inline int Wlc_BlastTimGet( Wlc_BlastTim_t * p, int iObj )
{
    if ( iObj < p->iBase )
        return Wlc_BlastTimOldLookup( p, iObj );
    if ( iObj - p->iBase >= Vec_IntSize(p->vLev) )
        return -1;
    return Vec_IntEntry( p->vLev, iObj - p->iBase );
}
// returns the AIG level of a literal, computed relative to the nodes preset
// to level 0 (the operands of the multiplier);
// other non-AND objects have level 0
int Wlc_BlastYjLevel( Gia_Man_t * p, Wlc_BlastTim_t * pTim, int iLit )
{
    int iObj  = Abc_Lit2Var( iLit );
    int Level = Wlc_BlastTimGet( pTim, iObj );
    Gia_Obj_t * pObj;
    if ( Level >= 0 )
        return Level;
    pObj = Gia_ManObj( p, iObj );
    if ( Gia_ObjIsAnd(pObj) )
        Level = 1 + Abc_MaxInt( Wlc_BlastYjLevel(p, pTim, Gia_ObjFaninLit0(pObj, iObj)),
                                Wlc_BlastYjLevel(p, pTim, Gia_ObjFaninLit1(pObj, iObj)) );
    else
        Level = 0;
    Wlc_BlastTimSet( pTim, iObj, Level );
    return Level;
}
static inline int Wlc_BlastYjTime( Gia_Man_t * p, Wlc_BlastTim_t * pTim, int iLitG, int iLitP )
{
    return Abc_MaxInt( Wlc_BlastYjLevel(p, pTim, iLitG), Wlc_BlastYjLevel(p, pTim, iLitP) );
}
// adds a literal to a column of the partial-product matrix, keeping the column sorted by arrival time
static inline void Wlc_BlastYjPush( Gia_Man_t * p, Wlc_BlastTim_t * pTim, Vec_Wec_t * vProds, Vec_Wec_t * vLevels, int Col, int iLit )
{
    if ( iLit == 0 || Col >= Vec_WecSize(vProds) )
        return;
    Wlc_IntInsert( Vec_WecEntry(vProds, Col), Vec_WecEntry(vLevels, Col), iLit, Wlc_BlastYjLevel(p, pTim, iLit) );
}
// combines generate/propagate of a higher bit range with those of the adjacent lower bit range
static inline void Wlc_BlastYjMerge( Gia_Man_t * p, int Ghi, int Phi, int Glo, int Plo, int * pG, int * pP )
{
    *pG = Gia_ManHashOr( p, Ghi, Gia_ManHashAnd(p, Phi, Glo) );
    *pP = Gia_ManHashAnd( p, Phi, Plo );
}

/**Function*************************************************************

  Synopsis    [Final adder driven by the arrival profile of its inputs.]

  Description [Processes the bits from LSB to MSB. A stack of prefix levels
  is maintained. Level 0 holds the real carries. When the running prefix of
  the top level arrives later than the next input bit by more than Slack
  levels, a new level is opened for that bit and grows on its own (serially
  while its inputs keep up, recursively otherwise). A level is closed into
  the level below when it has caught up with it, or when closing it cannot
  delay anything because the level below is itself waiting for an even
  later level. Closing merges every prefix of the level with the prefix
  of the level below (conditional carries). When a level closes into
  level 0 and the incoming carry is the critical signal, the sums are
  produced by selecting between precomputed conditional sums (conditional
  sum), which costs one mux instead of a carry merge and an XOR.
  The result is returned in pAdd0. Levels are measured by Wlc_BlastYjLevel.
  This is an adaptation of the MLCSMA of Yeh and Jen to the AIG cost model,
  not the algorithm itself. The differences are: (a) blocks are represented
  by generate/propagate prefixes merged with the usual rules G | P & G' and
  P & P' instead of the paper's conditional-carry cells; (b) a new level
  starts with a single bit instead of a two-bit conditional-carry adder;
  (c) the decisions to open and close levels use the AIG arrival times and
  the Slack rule above instead of the paper's cell-delay rules; (d) the
  conditional sums may be used wherever a level closes into the real
  carries, not only in the most significant block.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Wlc_BlastAdderProfile( Gia_Man_t * pNew, Wlc_BlastTim_t * pTim, int * pAdd0, int * pAdd1, int nBits, int Slack, int fCondSum )
{
    Vec_Wec_t * vGs = Vec_WecAlloc( 16 ), * vPs = Vec_WecAlloc( 16 );
    Vec_Int_t * vStart = Vec_IntAlloc( 16 ), * vG, * vP;
    int * pG = ABC_ALLOC( int, nBits );
    int * pP = ABC_ALLOC( int, nBits );
    int * pC = ABC_ALLOC( int, nBits + 1 );
    int * pS = ABC_ALLOC( int, nBits );
    int b, k, n, Tb, Tacc, iTop;
    for ( b = 0; b < nBits; b++ )
    {
        pG[b] = Gia_ManHashAnd( pNew, pAdd0[b], pAdd1[b] );
        pP[b] = Gia_ManHashXor( pNew, pAdd0[b], pAdd1[b] );
        pC[b] = pS[b] = -1;
    }
    pC[0] = 0; pC[nBits] = -1;
    // level 0: the entries are the carries into bits 1, 2, ...
    Vec_IntPush( vStart, 0 );
    vG = Vec_WecPushLevel( vGs ); Vec_IntClear( vG );
    vP = Vec_WecPushLevel( vPs ); Vec_IntClear( vP );
    for ( b = 0; b < nBits; b++ )
    {
        iTop = Vec_IntSize(vStart) - 1;
        vG   = Vec_WecEntry( vGs, iTop );
        vP   = Vec_WecEntry( vPs, iTop );
        Tb   = Wlc_BlastYjLevel( pNew, pTim, pP[b] );
        Tacc = Vec_IntSize(vG) ? Wlc_BlastYjTime( pNew, pTim, Vec_IntEntryLast(vG), Vec_IntEntryLast(vP) ) : 0;
        if ( Tacc > Tb + Slack )
        {
            // the running prefix is late: open a new level starting with this bit
            Vec_IntPush( vStart, b );
            vG = Vec_WecPushLevel( vGs ); Vec_IntClear( vG ); Vec_IntPush( vG, pG[b] );
            vP = Vec_WecPushLevel( vPs ); Vec_IntClear( vP ); Vec_IntPush( vP, pP[b] );
        }
        else if ( iTop == 0 )
        {
            // ripple into the real carry
            int c = Vec_IntSize(vG) ? Vec_IntEntryLast(vG) : 0;
            pC[b+1] = Gia_ManHashOr( pNew, pG[b], Gia_ManHashAnd(pNew, pP[b], c) );
            Vec_IntPush( vG, pC[b+1] );
            Vec_IntPush( vP, 0 );
        }
        else
        {
            // ripple into the relative prefix of the top level
            int G, P;
            Wlc_BlastYjMerge( pNew, pG[b], pP[b], Vec_IntEntryLast(vG), Vec_IntEntryLast(vP), &G, &P );
            Vec_IntPush( vG, G );
            Vec_IntPush( vP, P );
        }
        // close the levels that are ready
        while ( (n = Vec_IntSize(vStart)) > 1 )
        {
            Vec_Int_t * vGh = Vec_WecEntry( vGs, n-1 ), * vPh = Vec_WecEntry( vPs, n-1 );
            Vec_Int_t * vGl = Vec_WecEntry( vGs, n-2 ), * vPl = Vec_WecEntry( vPs, n-2 );
            int Start  = Vec_IntEntry( vStart, n-1 );
            int Thi    = Wlc_BlastYjTime( pNew, pTim, Vec_IntEntryLast(vGh), Vec_IntEntryLast(vPh) );
            int Tlo    = Vec_IntSize(vGl) ? Wlc_BlastYjTime( pNew, pTim, Vec_IntEntryLast(vGl), Vec_IntEntryLast(vPl) ) : 0;
            int fClose = (b == nBits - 1) || (Thi >= Tlo);
            if ( !fClose && n > 2 )
            {
                Vec_Int_t * vGll = Vec_WecEntry( vGs, n-3 ), * vPll = Vec_WecEntry( vPs, n-3 );
                int Tll = Vec_IntSize(vGll) ? Wlc_BlastYjTime( pNew, pTim, Vec_IntEntryLast(vGll), Vec_IntEntryLast(vPll) ) : 0;
                fClose  = Abc_MaxInt(Thi, Tlo) + 2 <= Tll;
            }
            if ( !fClose )
                break;
            if ( n == 2 )
            {
                // closing into level 0: the entries become real carries
                int c  = Vec_IntSize(vGl) ? Vec_IntEntryLast(vGl) : 0;
                int Tc = Wlc_BlastYjLevel( pNew, pTim, c );
                for ( k = 0; k < Vec_IntSize(vGh); k++ )
                {
                    int Gk = Vec_IntEntry(vGh, k), Pk = Vec_IntEntry(vPh, k), j = Start + k + 1; // j is the bit receiving the carry
                    int TG = Wlc_BlastYjLevel( pNew, pTim, Gk ), TP = Wlc_BlastYjLevel( pNew, pTim, Pk );
                    int Carry = -1, fMux = 0;
                    if ( j < nBits )
                    {
                        int Tp     = Wlc_BlastYjLevel( pNew, pTim, pP[j] );
                        int TCarry = Abc_MaxInt( Abc_MaxInt(TP, Tc) + 1, TG ) + 1;
                        int TSum   = Abc_MaxInt( TCarry, Tp ) + 2;
                        int TSum0  = Abc_MaxInt( Tp, TG ) + 2;
                        int TSum1  = Abc_MaxInt( Tp, Abc_MaxInt(TG, TP) + 1 ) + 2;
                        int TMux   = Abc_MaxInt( Tc, Abc_MaxInt(TSum0, TSum1) ) + 2;
                        fMux = fCondSum && TMux < TSum;
                        if ( fMux )
                        {
                            int Sum0 = Gia_ManHashXor( pNew, pP[j], Gk );
                            int Sum1 = Gia_ManHashXor( pNew, pP[j], Gia_ManHashOr(pNew, Gk, Pk) );
                            pS[j] = Gia_ManHashMux( pNew, c, Sum1, Sum0 );
                        }
                    }
                    if ( !fMux || k == Vec_IntSize(vGh) - 1 )
                        Carry = Gia_ManHashOr( pNew, Gk, Gia_ManHashAnd(pNew, Pk, c) );
                    pC[j] = Carry;
                    Vec_IntPush( vGl, Carry == -1 ? 0 : Carry );
                    Vec_IntPush( vPl, 0 );
                }
            }
            else
            {
                int Glo = Vec_IntEntryLast(vGl), Plo = Vec_IntEntryLast(vPl);
                for ( k = 0; k < Vec_IntSize(vGh); k++ )
                {
                    int G, P;
                    Wlc_BlastYjMerge( pNew, Vec_IntEntry(vGh, k), Vec_IntEntry(vPh, k), Glo, Plo, &G, &P );
                    Vec_IntPush( vGl, G );
                    Vec_IntPush( vPl, P );
                }
            }
            Vec_WecShrink( vGs, n-1 );
            Vec_WecShrink( vPs, n-1 );
            Vec_IntShrink( vStart, n-1 );
        }
    }
    assert( Vec_IntSize(vStart) == 1 );
    for ( b = 0; b < nBits; b++ )
    {
        if ( pS[b] == -1 )
        {
            assert( pC[b] != -1 );
            pS[b] = Gia_ManHashXor( pNew, pP[b], pC[b] );
        }
        pAdd0[b] = pS[b];
    }
    Vec_WecFree( vGs );
    Vec_WecFree( vPs );
    Vec_IntFree( vStart );
    ABC_FREE( pG );
    ABC_FREE( pP );
    ABC_FREE( pC );
    ABC_FREE( pS );
}

// A column that is down to three signals is finished by a half adder on the
// two earliest ones when the third arrives at least this many AIG levels after
// them. Without this, the latest signal is swallowed by the last full adder
// of the column, which delays it by two levels, and when the next column is
// in the same situation this repeats: for the plain partial-product matrix,
// whose columns grow by one row each, the reduced rows of a 64-bit multiplier
// arrive 131 levels late in the middle instead of 37. The threshold is not
// zero because the profile adder is faster for columns holding one signal
// and a constant (no generate) than for two real signals; sweeping it over
// 16..64-bit Booth and Wallace multipliers found 5..6 best overall.
#define WLC_YJ_HA_SLACK 6

/**Function*************************************************************

  Synopsis    [Reduces a partial-product matrix and adds the two remaining rows.]

  Description [Each column is compressed by full adders over its three
  earliest-arriving signals (the slowest on the carry-in) until two remain;
  a column left with three signals is finished by a half adder on the two
  earliest, which keeps its latest signal out of the carry chain. The
  carries enter the next column with their arrival times. The
  final addition is driven by the arrival profile when fFastAdder is set and
  is ripple-carry otherwise. The columns of vProds/vLevels are kept sorted by
  decreasing arrival time, as filled by Wlc_BlastYjPush. The product is
  returned in vRes with one bit per column.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Wlc_BlastYjReduce( Gia_Man_t * pNew, Wlc_BlastTim_t * pTim, Vec_Wec_t * vProds, Vec_Wec_t * vLevels, Vec_Int_t * vRes, int fFastAdder, int fVerbose )
{
    int nCols = Vec_WecSize(vProds);
    int * pRow0 = ABC_CALLOC( int, nCols );
    int * pRow1 = ABC_CALLOC( int, nCols );
    Vec_Int_t * vProd, * vLevel;
    int i, Node1, Node2, Node3, NodeS, NodeC, nFAs = 0, nHAs = 0;
    assert( nCols == Vec_WecSize(vLevels) );
    if ( fVerbose )
        Vec_WecPrint( vProds, 0 );

    // reduce the columns: the three earliest signals enter one full adder, the slowest on the carry-in;
    // a column with three signals left, the latest of which is much later than the other two, gets a half
    // adder on the two earliest, so that its latest signal goes to the final adder directly instead of
    // rippling through the last full adders of the following columns (see the comment at WLC_YJ_HA_SLACK)
    for ( i = 0; i < nCols; i++ )
    {
        vProd  = Vec_WecEntry( vProds,  i );
        vLevel = Vec_WecEntry( vLevels, i );
        while ( Vec_IntSize(vProd) >= 3 )
        {
            Node1 = Vec_IntPop( vProd );  Vec_IntPop( vLevel );
            Node2 = Vec_IntPop( vProd );  Vec_IntPop( vLevel );
            if ( Vec_IntSize(vProd) == 1 && fFastAdder && Vec_IntEntry(vLevel, 0) - Wlc_BlastYjLevel(pNew, pTim, Node2) >= WLC_YJ_HA_SLACK )
            {
                NodeS = Gia_ManHashXor( pNew, Node1, Node2 );
                NodeC = Gia_ManHashAnd( pNew, Node1, Node2 );
                nHAs += (Node1 > 1) + (Node2 > 1) == 2;
            }
            else
            {
                Node3 = Vec_IntPop( vProd );  Vec_IntPop( vLevel );
                Wlc_BlastFullAdder( pNew, Node1, Node2, Node3, &NodeC, &NodeS );
                nFAs += (Node1 > 1) + (Node2 > 1) + (Node3 > 1) == 3;
                nHAs += (Node1 > 1) + (Node2 > 1) + (Node3 > 1) == 2;
            }
            Wlc_IntInsert( vProd, vLevel, NodeS, Wlc_BlastYjLevel(pNew, pTim, NodeS) );
            if ( i + 1 < nCols )
                Wlc_IntInsert( Vec_WecEntry(vProds, i+1), Vec_WecEntry(vLevels, i+1), NodeC, Wlc_BlastYjLevel(pNew, pTim, NodeC) );
        }
        pRow0[i] = Vec_IntSize(vProd) > 0 ? Vec_IntEntry(vProd, 0) : 0;
        pRow1[i] = Vec_IntSize(vProd) > 1 ? Vec_IntEntry(vProd, 1) : 0;
    }
    if ( fVerbose )
    {
        printf( "%d FAs, %d HAs. Arrival profile of the reduced rows:\n", nFAs, nHAs );
        for ( i = 0; i < nCols; i++ )
            printf( "%d ", Abc_MaxInt(Wlc_BlastYjLevel(pNew, pTim, pRow0[i]), Wlc_BlastYjLevel(pNew, pTim, pRow1[i])) );
        printf( "\n" );
    }

    // final addition: driven by the arrival profile, or ripple-carry
    if ( fFastAdder )
        Wlc_BlastAdderProfile( pNew, pTim, pRow0, pRow1, nCols, 1, 1 );
    else
        Wlc_BlastAdder( pNew, pRow0, pRow1, nCols, 0 );
    if ( fVerbose )
    {
        printf( "Arrival profile of the product:\n" );
        for ( i = 0; i < nCols; i++ )
            printf( "%d ", Wlc_BlastYjLevel(pNew, pTim, pRow0[i]) );
        printf( "\n" );
    }
    Vec_IntClear( vRes );
    for ( i = 0; i < nCols; i++ )
        Vec_IntPush( vRes, pRow0[i] );
    ABC_FREE( pRow0 );
    ABC_FREE( pRow1 );
}

/**Function*************************************************************

  Synopsis    [Generates the Yeh-Jen Booth multiplier.]

  Description [The product has nArgA + nArgB bits (sign-extended by the
  caller if a wider result is needed).]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Wlc_BlastBoothYJ( Gia_Man_t * pNew, Wlc_BlastTim_t * pTim, int * pArgA, int * pArgB, int nArgA, int nArgB, Vec_Int_t * vRes, int fSigned, int fFastAdder, int fVerbose )
{
    int nCols = nArgA + nArgB;
    Vec_Wec_t * vProds  = Vec_WecStart( nCols );
    Vec_Wec_t * vLevels = Vec_WecStart( nCols );
    Wlc_BlastTim_t * pTimLocal = pTim ? NULL : Wlc_BlastTimStart();
    Vec_Int_t * vArgB   = Vec_IntAlloc( nArgB + 4 );
    Vec_Int_t * vArgN   = Vec_IntAlloc( nArgA + 2 );
    int FillA = fSigned ? pArgA[nArgA-1] : 0;
    int FillB = fSigned ? pArgB[nArgB-1] : 0;
    int i, k, Sign;
    assert( nArgA > 0 && nArgB > 0 );
    if ( pTim == NULL )
        pTim = pTimLocal;
    Wlc_BlastTimNewGen( pTim, pNew );

    // the operands arrive at time 0
    Wlc_BlastTimSetInputs( pTim, pArgA, nArgA );
    Wlc_BlastTimSetInputs( pTim, pArgB, nArgB );

    // extend argument B
    Vec_IntPush( vArgB, 0 );
    for ( i = 0; i < nArgB; i++ )
        Vec_IntPush( vArgB, pArgB[i] );
    if ( !fSigned )
        Vec_IntPushTwo( vArgB, FillB, FillB );
    if ( Vec_IntSize(vArgB) % 2 == 0 )
        Vec_IntPush( vArgB, FillB );
    assert( Vec_IntSize(vArgB) % 2 == 1 );

    // iterate through bit-pairs of B
    for ( k = 0; k+2 < Vec_IntSize(vArgB); k += 2 )
    {
        int pp    = 0;
        int Q2jM1 = Vec_IntEntry(vArgB, k);   // q(2*j-1)
        int Q2j   = Vec_IntEntry(vArgB, k+1); // q(2*j+0)
        int Q2jP1 = Vec_IntEntry(vArgB, k+2); // q(2*j+1)
        int Neg   = Q2jP1;                                                                                  // the digit is -2, -1 or -0
        int One   = Gia_ManHashXor( pNew, Q2j, Q2jM1 );                                                     // the digit is +1 or -1
        int Two   = Gia_ManHashAnd( pNew, Gia_ManHashXor(pNew, Q2jP1, Q2j), Abc_LitNot(One) );              // the digit is +2 or -2
        int NegC  = Gia_ManHashAnd( pNew, Neg, Abc_LitNot(Gia_ManHashAnd(pNew, Q2j, Q2jM1)) );              // the digit is -2 or -1
        // the row LSB with the negation carry folded in (eq. 2), and the carry into the next column (eq. 3)
        int Lsb   = Gia_ManHashAnd( pNew, One, pArgA[0] );
        int Cin   = Gia_ManHashOr( pNew, Gia_ManHashAnd(pNew, Neg, Gia_ManHashAnd(pNew, Abc_LitNot(Q2j), Abc_LitNot(Q2jM1))),
                                         Gia_ManHashAnd(pNew, One, Gia_ManHashAnd(pNew, Neg, Abc_LitNot(pArgA[0]))) );
        // multiplicand bits XORed with the negation signal, in parallel with the encoder (bit -1 is Neg)
        Vec_IntClear( vArgN );
        Vec_IntPush( vArgN, Neg );
        for ( i = 0; i <= nArgA; i++ )
            Vec_IntPush( vArgN, Gia_ManHashXor(pNew, i == nArgA ? FillA : pArgA[i], Neg) );
        for ( i = 0; i <= nArgA; i++ )
        {
            pp = Gia_ManHashOr( pNew, Gia_ManHashAnd(pNew, One, Vec_IntEntry(vArgN, i+1)), Gia_ManHashAnd(pNew, Two, Vec_IntEntry(vArgN, i)) );
            if ( fVerbose ) printf( "%4d = PP(%5d %5d  %5d %5d %5d)\n", pp, i ? pArgA[i-1] : 0, i == nArgA ? FillA : pArgA[i], Q2jM1, Q2j, Q2jP1 );
            if ( i == 0 || (fSigned && i == nArgA) )
                continue;
            Wlc_BlastYjPush( pNew, pTim, vProds, vLevels, k+i, pp );
        }
        Wlc_BlastYjPush( pNew, pTim, vProds, vLevels, k,   Lsb );
        Wlc_BlastYjPush( pNew, pTim, vProds, vLevels, k+1, Cin );
        if ( fSigned ) i--;
        // perform sign extension
        Sign = fSigned ? pp : NegC;
        if ( k == 0 )
        {
            Wlc_BlastYjPush( pNew, pTim, vProds, vLevels, k+i,   Sign );
            Wlc_BlastYjPush( pNew, pTim, vProds, vLevels, k+i+1, Sign );
            Wlc_BlastYjPush( pNew, pTim, vProds, vLevels, k+i+2, Abc_LitNot(Sign) );
        }
        else
        {
            Wlc_BlastYjPush( pNew, pTim, vProds, vLevels, k+i,   Abc_LitNot(Sign) );
            Wlc_BlastYjPush( pNew, pTim, vProds, vLevels, k+i+1, 1 );
        }
    }
    if ( fVerbose )
        printf( "Yeh-Jen Booth %d x %d (%s):\n", nArgA, nArgB, fSigned ? "signed" : "unsigned" );
    Wlc_BlastYjReduce( pNew, pTim, vProds, vLevels, vRes, fFastAdder, fVerbose );

    Vec_WecFree( vProds );
    Vec_WecFree( vLevels );
    if ( pTimLocal )
        Wlc_BlastTimStop( pTimLocal );
    Vec_IntFree( vArgB );
    Vec_IntFree( vArgN );
}

/**Function*************************************************************

  Synopsis    [Generates the Wallace-tree multiplier with arrival-driven reduction.]

  Description [The partial products are plain AND gates, in Baugh-Wooley form
  for signed operands. They are compressed and added the same way as in the
  Yeh-Jen Booth multiplier. The product has nArgA + nArgB bits.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Wlc_BlastWallace( Gia_Man_t * pNew, Wlc_BlastTim_t * pTim, int * pArgA, int * pArgB, int nArgA, int nArgB, Vec_Int_t * vRes, int fSigned, int fFastAdder, int fVerbose )
{
    int nCols = nArgA + nArgB;
    Vec_Wec_t * vProds  = Vec_WecStart( nCols );
    Vec_Wec_t * vLevels = Vec_WecStart( nCols );
    Wlc_BlastTim_t * pTimLocal = pTim ? NULL : Wlc_BlastTimStart();
    int i, k;
    assert( nArgA > 0 && nArgB > 0 );
    if ( pTim == NULL )
        pTim = pTimLocal;
    Wlc_BlastTimNewGen( pTim, pNew );

    // the operands arrive at time 0
    Wlc_BlastTimSetInputs( pTim, pArgA, nArgA );
    Wlc_BlastTimSetInputs( pTim, pArgB, nArgB );

    // partial products; in the signed case, the ones involving exactly one sign bit are complemented
    for ( i = 0; i < nArgA; i++ )
        for ( k = 0; k < nArgB; k++ )
        {
            int fCompl = fSigned && ((i == nArgA-1) ^ (k == nArgB-1));
            Wlc_BlastYjPush( pNew, pTim, vProds, vLevels, i+k, Abc_LitNotCond(Gia_ManHashAnd(pNew, pArgA[i], pArgB[k]), fCompl) );
        }
    // the Baugh-Wooley correction 2^(nArgA-1) + 2^(nArgB-1) + 2^(nArgA+nArgB-1) compensates for the complemented products
    if ( fSigned )
    {
        Wlc_BlastYjPush( pNew, pTim, vProds, vLevels, nArgA-1, 1 );
        Wlc_BlastYjPush( pNew, pTim, vProds, vLevels, nArgB-1, 1 );
        Wlc_BlastYjPush( pNew, pTim, vProds, vLevels, nCols-1, 1 );
    }
    if ( fVerbose )
        printf( "Wallace %d x %d (%s):\n", nArgA, nArgB, fSigned ? "signed" : "unsigned" );
    Wlc_BlastYjReduce( pNew, pTim, vProds, vLevels, vRes, fFastAdder, fVerbose );

    Vec_WecFree( vProds );
    Vec_WecFree( vLevels );
    if ( pTimLocal )
        Wlc_BlastTimStop( pTimLocal );
}

void Wlc_NtkDumpMulties( Wlc_Ntk_t * p, Gia_Man_t * pNew )
{
    Wlc_Obj_t * pObj; int i;
    Gia_ManCreateRefs( pNew );
    Wlc_NtkForEachObj( p, pObj, i ) {
        if ( pObj->Type != WLC_OBJ_ARI_MULTI )
            continue;
        int fSigned  = Wlc_ObjIsSignedFanin01(p, pObj);
        int nRange   = Wlc_ObjRange( pObj );
        int nRange0  = Wlc_ObjRange( Wlc_ObjFanin0(p, pObj) );
        int nRange1  = Wlc_ObjRange( Wlc_ObjFanin1(p, pObj) );
        int * pFans  = Vec_IntEntryP( &p->vBits, Wlc_ObjCopy(p, i) );
        int * pFans0 = Vec_IntEntryP( &p->vBits, Wlc_ObjCopy(p, Wlc_ObjFaninId0(pObj)) );
        int * pFans1 = Vec_IntEntryP( &p->vBits, Wlc_ObjCopy(p, Wlc_ObjFaninId1(pObj)) );

        printf( "\n%d\n", fSigned );
        printf( "%2d :", nRange0 );
        for ( int k = 0; k < nRange0; k++ )
            if ( pFans0[k] == -1 )
                printf( " -" );
            else
                printf( " %c%d(%d)", Abc_LitIsCompl(pFans0[k])?'-':'+', Abc_Lit2Var(pFans0[k]), Gia_ObjRefNumId(pNew, Abc_Lit2Var(pFans0[k])) );
        printf( "\n" );

        printf( "%2d :", nRange1 );
        for ( int k = 0; k < nRange1; k++ )
            if ( pFans1[k] == -1 )
                printf( " -" );
            else
                printf( " %c%d(%d)", Abc_LitIsCompl(pFans1[k])?'-':'+', Abc_Lit2Var(pFans1[k]), Gia_ObjRefNumId(pNew, Abc_Lit2Var(pFans1[k])) );
        printf( "\n" );

        printf( "%2d :", nRange );
        for ( int k = 0; k < nRange; k++ )
            if ( pFans[k] == -1 )
                printf( " -" );
            else
                printf( " %c%d(%d)", Abc_LitIsCompl(pFans[k])?'-':'+', Abc_Lit2Var(pFans[k]), Gia_ObjRefNumId(pNew, Abc_Lit2Var(pFans[k])) );
        printf( "\n" );
    }
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Wlc_NtkBitBlast( Wlc_Ntk_t * p, Wlc_BstPar_t * pParIn )
{
    int fVerbose = 0;
    int fUseOldMultiplierBlasting = 0;
    int fSkipBitRange = 0;
    Tim_Man_t * pManTime = NULL;
    If_LibBox_t * pBoxLib = NULL;
    Vec_Ptr_t * vTables = NULL;
    Vec_Int_t * vFf2Ci = Vec_IntAlloc( 100 );
    Vec_Int_t * vRegClasses = NULL;
    Gia_Man_t * pTemp, * pNew, * pExtra = NULL;
    Wlc_Obj_t * pObj, * pObj2;
    Vec_Int_t * vBits = &p->vBits, * vTemp0, * vTemp1, * vTemp2, * vRes, * vAddOutputs = NULL, * vAddObjs = NULL;
    Wlc_BlastTim_t * pTim = NULL; // timing memo shared by the Yeh-Jen multipliers
    int nBits = Wlc_NtkPrepareBits( p );
    int nRange, nRange0, nRange1, nRange2, nRange3;
    int i, k, b, iFanin, iLit, nAndPrev, * pFans0, * pFans1, * pFans2, * pFans3;
    int nFFins = 0, nFFouts = 0, curPi = 0, curPo = 0, nFf2Regs = 0;
    int nBitCis = 0, nBitCos = 0, fAdded = 0;
    Wlc_BstPar_t Par, * pPar = &Par;
    Wlc_BstParDefault( pPar );
    pPar = pParIn ? pParIn : pPar;
    Vec_IntClear( vBits );
    Vec_IntGrow( vBits, nBits );
    vTemp0 = Vec_IntAlloc( 1000 );
    vTemp1 = Vec_IntAlloc( 1000 );
    vTemp2 = Vec_IntAlloc( 1000 );
    vRes   = Vec_IntAlloc( 1000 );
    // clean AND-gate counters
    memset( p->nAnds, 0, sizeof(int) * WLC_OBJ_NUMBER );
    // create AIG manager
    pNew = Gia_ManStart( 5 * Wlc_NtkObjNum(p) + 1000 );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    pNew->fGiaSimple = pPar->fGiaSimple;
    if ( !pPar->fGiaSimple )
        Gia_ManHashAlloc( pNew );
    if ( pPar->fAddOutputs )
        vAddOutputs = Vec_IntAlloc( 100 );
    if ( pPar->fAddOutputs )
        vAddObjs = Vec_IntAlloc( 100 );
    // prepare for AIG with boxes
    if ( pPar->vBoxIds )
    {
        int nNewCis = 0, nNewCos = 0;
        assert( Vec_IntSize(&p->vFfs2) == 0 );
        Wlc_NtkForEachObj( p, pObj, i )
            pObj->Mark = 0;
        // count bit-width of regular CIs/COs
        Wlc_NtkForEachCi( p, pObj, i )
            nBitCis += Wlc_ObjRange( pObj );
        Wlc_NtkForEachCo( p, pObj, i )
            nBitCos += Wlc_ObjRange( pObj );
        // count bit-width of additional CIs/COs due to selected multipliers
        assert( Vec_IntSize(pPar->vBoxIds) > 0 );
        Wlc_NtkForEachObjVec( pPar->vBoxIds, p, pObj, i )
        {
            // currently works only for multipliers
            assert( pObj->Type == WLC_OBJ_ARI_MULTI || pObj->Type == WLC_OBJ_ARI_ADD );
            nNewCis += Wlc_ObjRange( pObj );
            nNewCos += Wlc_ObjRange( Wlc_ObjFanin0(p, pObj) );
            nNewCos += Wlc_ObjRange( Wlc_ObjFanin1(p, pObj) );
            if ( Wlc_ObjFaninNum(pObj) > 2 )
            nNewCos += Wlc_ObjRange( Wlc_ObjFanin2(p, pObj) );
            pObj->Mark = 1;
        }
        // create hierarchy manager
        pManTime = Tim_ManStart( nBitCis + nNewCis, nBitCos + nNewCos );
        curPi = nBitCis;
        curPo = 0;
        // create AIG manager for logic of the boxes
        pExtra = Gia_ManStart( Wlc_NtkObjNum(p) );
        Gia_ManHashAlloc( pExtra );
        assert( !pPar->fGiaSimple );
        // create box library
        pBoxLib = If_LibBoxStart();
    }
    if ( Vec_IntSize(&p->vFfs2) > 0 )
    {
        Vec_Int_t * vSignature;
        int nNewCis = 0, nNewCos = 0;
        assert( pPar->vBoxIds == 0 );
        // count bit-width of regular CIs/COs
        Wlc_NtkForEachCi( p, pObj, i )
            nBitCis += Wlc_ObjRange( pObj );
        Wlc_NtkForEachCo( p, pObj, i )
            nBitCos += Wlc_ObjRange( pObj );
        // count bit-width of additional CIs/COs due to selected multipliers
        Wlc_NtkForEachFf2( p, pObj, i )
        {
            // currently works only for multipliers
            assert( pObj->Type == WLC_OBJ_FF );
            assert( Wlc_ObjRange(pObj) == Wlc_ObjRange(Wlc_ObjFanin0(p, pObj)) );
            nNewCis += Wlc_ObjRange(pObj);
            nNewCos += 2*Wlc_ObjRange(pObj) + 3;
            nFf2Regs+= Wlc_ObjRange(pObj);
        }
        // create hierarchy manager
        pManTime = Tim_ManStart( nBitCis + nNewCis + nFf2Regs, nBitCos + nNewCos + nFf2Regs );
        curPi = nBitCis + nFf2Regs;
        curPo = 0;
        // create AIG manager for logic of the boxes
        pExtra = Gia_ManStart( Wlc_NtkObjNum(p) );
        Gia_ManHashAlloc( pExtra );
        assert( !pPar->fGiaSimple );
        // create register classes
        vRegClasses = Vec_IntAlloc(0);
        vSignature = Vec_IntAlloc( 100 );
        Vec_IntPushTwo( vSignature, -1, -1 );
        Wlc_NtkForEachFf2( p, pObj, i )
        {
            int iClk0,  iClk  = Wlc_ObjFaninId( pObj, 1 );
            int iAsyn0, iAsyn = Wlc_ObjFaninId( pObj, 5 );
            nRange = Wlc_ObjRange(pObj);
            Vec_IntForEachEntryDouble( vSignature, iClk0, iAsyn0, k )
                if ( iClk == iClk0 && iAsyn == iAsyn0 )
                {
                    for ( b = 0; b < nRange; b++ )
                        Vec_IntPush( vRegClasses, k/2 );
                    break;
                }
            if ( k < Vec_IntSize(vSignature) )
                continue;
            for ( b = 0; b < nRange; b++ )
                Vec_IntPush( vRegClasses, k/2 );
            Vec_IntPushTwo( vSignature, iClk, iAsyn );
        }
        assert( Vec_IntSize(vRegClasses) == nFf2Regs );
        Vec_IntFree( vSignature );
        // create box library
        pBoxLib = If_LibBoxStart();
    }
    //printf( "Init state: %s\n", p->pInits );

    // blast in the topological order
    Wlc_NtkForEachObj( p, pObj, i )
    {
        //char * pName1 = Wlc_ObjName(p, i);
        //char * pName2 = Wlc_ObjFaninNum(pObj) ? Wlc_ObjName(p, Wlc_ObjFaninId0(pObj)) : NULL;

        nAndPrev = Gia_ManAndNum(pNew);
        nRange  = Wlc_ObjRange( pObj );
        nRange0 = Wlc_ObjFaninNum(pObj) > 0 ? Wlc_ObjRange( Wlc_ObjFanin0(p, pObj) ) : -1;
        nRange1 = Wlc_ObjFaninNum(pObj) > 1 ? Wlc_ObjRange( Wlc_ObjFanin1(p, pObj) ) : -1;
        nRange2 = Wlc_ObjFaninNum(pObj) > 2 ? Wlc_ObjRange( Wlc_ObjFanin2(p, pObj) ) : -1;
        nRange3 = Wlc_ObjFaninNum(pObj) > 3 ? Wlc_ObjRange( Wlc_ObjFanin(p, pObj, 3) ) : -1;
        pFans0  = pObj->Type != WLC_OBJ_FF && Wlc_ObjFaninNum(pObj) > 0 ? Vec_IntEntryP( vBits, Wlc_ObjCopy(p, Wlc_ObjFaninId0(pObj)) ) : NULL;
        pFans1  = pObj->Type != WLC_OBJ_FF && Wlc_ObjFaninNum(pObj) > 1 ? Vec_IntEntryP( vBits, Wlc_ObjCopy(p, Wlc_ObjFaninId1(pObj)) ) : NULL;
        pFans2  = pObj->Type != WLC_OBJ_FF && Wlc_ObjFaninNum(pObj) > 2 ? Vec_IntEntryP( vBits, Wlc_ObjCopy(p, Wlc_ObjFaninId2(pObj)) ) : NULL;
        pFans3  = pObj->Type != WLC_OBJ_FF && Wlc_ObjFaninNum(pObj) > 3 ? Vec_IntEntryP( vBits, Wlc_ObjCopy(p, Wlc_ObjFaninId(pObj,3)) ) : NULL;
        Vec_IntClear( vRes );
        assert( nRange > 0 );
        if ( pPar->vBoxIds && pObj->Mark )
        {
            If_Box_t * pBox;
            char Buffer[100];
            float * pTable;
            int CarryIn = 0;

            pObj->Mark = 0;
            assert( pObj->Type == WLC_OBJ_ARI_MULTI || pObj->Type == WLC_OBJ_ARI_ADD || pObj->Type == WLC_OBJ_ARI_SUB );

            // account for carry-in
            if ( Wlc_ObjFaninNum(pObj) == 3 )
                assert( nRange2 == 1 );
            else
                nRange2 = 0;

            // create new box
            if ( vTables == NULL ) {
                Tim_ManSetDelayTables( pManTime, (vTables = Vec_PtrAlloc(100)) );
                Vec_PtrPush( vTables, NULL );
            }
            Tim_ManCreateBox( pManTime, curPo, nRange0 + nRange1 + nRange2, curPi, nRange, Vec_PtrSize(vTables), 0 );
            Tim_ManBoxSetCopy( pManTime, Tim_ManBoxNum(pManTime)-1, Tim_ManBoxNum(pManTime)-1 );
            curPi += nRange;
            curPo += nRange0 + nRange1 + nRange2;

            // create delay table
            pTable = ABC_ALLOC( float, 3 + nRange * (nRange0 + nRange1 + nRange2) );
            pTable[0] = Vec_PtrSize(vTables);
            pTable[1] = nRange0 + nRange1 + nRange2;
            pTable[2] = nRange;
            for ( k = 0; k < nRange * (nRange0 + nRange1 + nRange2); k++ )
                pTable[3 + k] = 1.0;
            Vec_PtrPush( vTables, pTable );

            // create combinational outputs in the normal manager
            for ( k = 0; k < nRange0; k++ )
                Gia_ManAppendCo( pNew, pFans0[k] );
            for ( k = 0; k < nRange1; k++ )
                Gia_ManAppendCo( pNew, pFans1[k] );
            for ( k = 0; k < nRange2; k++ )
                Gia_ManAppendCo( pNew, pFans2[0] );

            // make sure there is enough primary inputs in the manager
            for ( k = Gia_ManPiNum(pExtra); k < nRange0 + nRange1 + nRange2; k++ )
                Gia_ManAppendCi( pExtra );
            // create combinational inputs
            Vec_IntClear( vTemp0 );
            for ( k = 0; k < nRange0; k++ )
                Vec_IntPush( vTemp0, Gia_Obj2Lit(pExtra, Gia_ManPi(pExtra, k)) );
            Vec_IntClear( vTemp1 );
            for ( k = 0; k < nRange1; k++ )
                Vec_IntPush( vTemp1, Gia_Obj2Lit(pExtra, Gia_ManPi(pExtra, nRange0+k)) );
            if ( nRange2 == 1 )
                CarryIn = Gia_Obj2Lit(pExtra, Gia_ManPi(pExtra, nRange0+nRange1));

            // get new fanin arrays
            pFans0 = Vec_IntArray( vTemp0 );
            pFans1 = Vec_IntArray( vTemp1 );

            // bit-blast in the external manager
            if ( pObj->Type == WLC_OBJ_ARI_ADD || pObj->Type == WLC_OBJ_ARI_SUB ) 
            {
                int nRangeMax = Abc_MaxInt( nRange, Abc_MaxInt(nRange0, nRange1) );
                int * pArg0 = Wlc_VecLoadFanins( vRes,   pFans0, nRange0, nRangeMax, Wlc_ObjIsSignedFanin01(p, pObj) );
                int * pArg1 = Wlc_VecLoadFanins( vTemp1, pFans1, nRange1, nRangeMax, Wlc_ObjIsSignedFanin01(p, pObj) );
                if ( pObj->Type == WLC_OBJ_ARI_ADD )
                    Wlc_BlastAdder( pExtra, pArg0, pArg1, nRange, CarryIn ); // result is in pFan0 (vRes)
                else 
                    Wlc_BlastSubtract( pExtra, pArg0, pArg1, nRange, 1 ); // result is in pFan0 (vRes)
                Vec_IntShrink( vRes, nRange );
            }
            else if ( fUseOldMultiplierBlasting )
            {                
                int nRangeMax = Abc_MaxInt( nRange, Abc_MaxInt(nRange0, nRange1) );
                int * pArg0 = Wlc_VecLoadFanins( vTemp0, pFans0, nRange0, nRangeMax, Wlc_ObjIsSignedFanin01(p, pObj) );
                int * pArg1 = Wlc_VecLoadFanins( vTemp1, pFans1, nRange1, nRangeMax, Wlc_ObjIsSignedFanin01(p, pObj) );
                Wlc_BlastMultiplier2( pExtra, pArg0, pArg1, nRange, vTemp2, vRes );
                Vec_IntShrink( vRes, nRange );
            }
            else
            {
                int fSigned = Wlc_ObjIsSignedFanin01(p, pObj);
                int nRangeMax = Abc_MaxInt(nRange0, nRange1);
                int * pArg0 = Wlc_VecLoadFanins( vTemp0, pFans0, nRange0, nRangeMax, fSigned );
                int * pArg1 = Wlc_VecLoadFanins( vTemp1, pFans1, nRange1, nRangeMax, fSigned );
                Wlc_BlastMultiplier( pExtra, pArg0, pArg1, nRangeMax, nRangeMax, vTemp2, vRes, fSigned );
                if ( nRange > nRangeMax + nRangeMax )
                    Vec_IntFillExtra( vRes, nRange, fSigned ? Vec_IntEntryLast(vRes) : 0 );
                else
                    Vec_IntShrink( vRes, nRange );
                assert( Vec_IntSize(vRes) == nRange );
            }
            // create outputs in the external manager
            for ( k = 0; k < nRange; k++ )
                Gia_ManAppendCo( pExtra, Vec_IntEntry(vRes, k) );

            // create combinational inputs in the normal manager
            Vec_IntClear( vRes );
            for ( k = 0; k < nRange; k++ )
                Vec_IntPush( vRes, Gia_ManAppendCi(pNew) );

            // add box to the library
            sprintf( Buffer, "%s%03d", pObj->Type == WLC_OBJ_ARI_ADD ? "add":"mul", 1+If_LibBoxNum(pBoxLib) );
            pBox = If_BoxStart( Abc_UtilStrsav(Buffer), 1+If_LibBoxNum(pBoxLib), nRange0 + nRange1 + nRange2, nRange, 0, 0, 0 ); 
            If_LibBoxAdd( pBoxLib, pBox );
            for ( k = 0; k < pBox->nPis * pBox->nPos; k++ )
                pBox->pDelays[k] = 1;
        }
        else if ( Wlc_ObjIsCi(pObj) || pObj->Type == WLC_OBJ_FF ) // assuming that FFs are ordered immediately after PIs
        {
            if ( pObj->Type == WLC_OBJ_FF )
                Vec_IntPush( vFf2Ci, Gia_ManCiNum(pNew) );
            if ( Wlc_ObjRangeIsReversed(pObj) )
            {
                for ( k = 0; k < nRange; k++ )
                    Vec_IntPush( vRes, -1 );
                for ( k = 0; k < nRange; k++ )
                    Vec_IntWriteEntry( vRes, Vec_IntSize(vRes)-1-k, Gia_ManAppendCi(pNew) );
            }
            else
            {
                for ( k = 0; k < nRange; k++ )
                    Vec_IntPush( vRes, Gia_ManAppendCi(pNew) );
            }
            if ( pObj->Type == WLC_OBJ_FO )
                nFFouts += Vec_IntSize(vRes);
            if ( pObj->Type == WLC_OBJ_FF )
            {
                // complement flop output whose init state is 1
            }
        }
        else if ( pObj->Type == WLC_OBJ_BUF )
        {
            int nRangeMax = Abc_MaxInt( nRange0, nRange );
            int * pArg0 = Wlc_VecLoadFanins( vTemp0, pFans0, nRange0, nRangeMax, Wlc_ObjIsSignedFanin0(p, pObj) );
            for ( k = 0; k < nRange; k++ )
                Vec_IntPush( vRes, pArg0[k] );
        }
        else if ( pObj->Type == WLC_OBJ_CONST )
        {
            word * pTruth = (word *)Wlc_ObjFanins(pObj);
            for ( k = 0; k < nRange; k++ )
                Vec_IntPush( vRes, Abc_TtGetBit(pTruth, k) );
        }
        else if ( pObj->Type == WLC_OBJ_MUX )
        {
            // It is strange and disturbing that Verilog standard treats these statements differently:
            // Statement 1:   
            //     assign o = i ? b : a;
            // Statement 2:
            //     always @( i or a or b )
            //       begin
            //         case ( i )
            //           0 : o = a ;
            //           1 : o = b ;
            //         endcase
            //       end
            // If a is signed and b is unsigned,  Statement 1 does not sign-extend a, while Statement 2 does.
            // The signedness of o does not matter.
            //
            // Below we (somewhat arbitrarily) distinguish these two by assuming that 
            // Statement 1 has three fanins, while Statement 2 has more than three fanins.
            //
            int fSigned = 1;
            assert( nRange0 >= 1 && Wlc_ObjFaninNum(pObj) >= 3 );
            assert( 1 + (1 << nRange0) == Wlc_ObjFaninNum(pObj) );
            Wlc_ObjForEachFanin( pObj, iFanin, k )
                if ( k > 0 )
                    fSigned &= Wlc_NtkObj(p, iFanin)->Signed;
            if ( pPar->fBlastNew && nRange0 <= 16 )
            {
                char * pNums = Wlc_NtkMuxTreeString( nRange0 );
                Vec_Int_t ** pvDecs = Wlc_NtkMuxTree3DecsDerive( pNew, pFans0, nRange0, pNums );
                for ( b = 0; b < nRange; b++ )
                {
                    Vec_IntClear( vTemp0 );
                    Wlc_ObjForEachFanin( pObj, iFanin, k ) {
                        if ( k > 0 )
                        {
                            nRange1 = Wlc_ObjRange( Wlc_NtkObj(p, iFanin) );
                            pFans1  = Vec_IntEntryP( vBits, Wlc_ObjCopy(p, iFanin) );
                            if ( Wlc_ObjFaninNum(pObj) == 3 ) // Statement 1
                                Vec_IntPush( vTemp0, b < nRange1 ? pFans1[b] : (fSigned? pFans1[nRange1-1] : 0) );
                            else // Statement 2
                                Vec_IntPush( vTemp0, b < nRange1 ? pFans1[b] : (Wlc_NtkObj(p, iFanin)->Signed? pFans1[nRange1-1] : 0) );
                        }
                    }
                    assert( (1 << nRange0) == Vec_IntSize(vTemp0) );
                    Vec_IntPush( vRes, Wlc_NtkMuxTree3(pNew, vTemp0, pNums, pvDecs) );
                }
                Wlc_NtkMuxTree3DecsFree( pvDecs, pNums );
            }
            else
            {
                Vec_IntClear( vTemp1 );
                if ( pPar->fDecMuxes )
                {
                    for ( k = 0; k < (1 << nRange0); k++ )
                    {
                        int iLitAnd = 1;
                        for ( b = 0; b < nRange0; b++ )
                            iLitAnd = Gia_ManHashAnd( pNew, iLitAnd, Abc_LitNotCond(pFans0[b], ((k >> b) & 1) == 0) );
                        Vec_IntPush( vTemp1, iLitAnd );
                    }
                }
                for ( b = 0; b < nRange; b++ )
                {
                    Vec_IntClear( vTemp0 );
                    Wlc_ObjForEachFanin( pObj, iFanin, k )
                        if ( k > 0 )
                        {
                            nRange1 = Wlc_ObjRange( Wlc_NtkObj(p, iFanin) );
                            pFans1  = Vec_IntEntryP( vBits, Wlc_ObjCopy(p, iFanin) );
                            if ( Wlc_ObjFaninNum(pObj) == 3 ) // Statement 1
                                Vec_IntPush( vTemp0, b < nRange1 ? pFans1[b] : (fSigned? pFans1[nRange1-1] : 0) );
                            else // Statement 2
                                Vec_IntPush( vTemp0, b < nRange1 ? pFans1[b] : (Wlc_NtkObj(p, iFanin)->Signed? pFans1[nRange1-1] : 0) );
                        }
                    if ( pPar->fDecMuxes )
                        Vec_IntPush( vRes, Wlc_NtkMuxTree2(pNew, pFans0, nRange0, vTemp0, vTemp1, vTemp2) );
                    else
                        Vec_IntPush( vRes, Wlc_NtkMuxTree_rec(pNew, pFans0, nRange0, vTemp0, 0) );
                }
            }
        }
        else if ( pObj->Type == WLC_OBJ_SEL )
        {
            assert( nRange0 == Wlc_ObjFaninNum(pObj)-1 );
            Vec_IntClear( vTemp1 );
            for ( k = 0; k < nRange0; k++ )
                Vec_IntPush( vTemp1, pFans0[k] );
            for ( b = 0; b < nRange; b++ )
            {
                Vec_IntClear( vTemp0 );
                Wlc_ObjForEachFanin( pObj, iFanin, k )
                    if ( k > 0 )
                    {
                        Wlc_Obj_t * pFanin = Wlc_NtkObj(p, iFanin);
                        (void)pFanin;
                        assert( nRange == Wlc_ObjRange(pFanin) );
                        pFans1 = Vec_IntEntryP( vBits, Wlc_ObjCopy(p, iFanin) );
                        Vec_IntPush( vTemp0, pFans1[b] );
                    }
                Vec_IntPush( vRes, Wlc_NtkMuxTree2(pNew, NULL, 0, vTemp0, vTemp1, vTemp2) );
            }
        }
        else if ( pObj->Type == WLC_OBJ_SHIFT_R || pObj->Type == WLC_OBJ_SHIFT_RA ||
                  pObj->Type == WLC_OBJ_SHIFT_L || pObj->Type == WLC_OBJ_SHIFT_LA )
        {
            int nRangeMax = Abc_MaxInt( nRange, nRange0 );
            int * pArg0 = Wlc_VecLoadFanins( vTemp0, pFans0, nRange0, nRangeMax, Wlc_ObjIsSignedFanin0(p, pObj) );
            if ( pObj->Type == WLC_OBJ_SHIFT_R || pObj->Type == WLC_OBJ_SHIFT_RA )
                Wlc_BlastShiftRight( pNew, pArg0, nRangeMax, pFans1, nRange1, Wlc_ObjIsSignedFanin0(p, pObj) && pObj->Type == WLC_OBJ_SHIFT_RA, vRes );
            else
                Wlc_BlastShiftLeft( pNew, pArg0, nRangeMax, pFans1, nRange1, 0, vRes );
            Vec_IntShrink( vRes, nRange );
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
            int nRangeMax = Abc_MaxInt( nRange, nRange0 );
            int * pArg0 = Wlc_VecLoadFanins( vTemp0, pFans0, nRange0, nRangeMax, Wlc_ObjIsSignedFanin0(p, pObj) );
            for ( k = 0; k < nRange; k++ )
                Vec_IntPush( vRes, Abc_LitNot(pArg0[k]) );
        }
        else if ( pObj->Type == WLC_OBJ_BIT_AND || pObj->Type == WLC_OBJ_BIT_NAND )
        {
            int nRangeMax = Abc_MaxInt( nRange, Abc_MaxInt(nRange0, nRange1) );
            int * pArg0 = Wlc_VecLoadFanins( vTemp0, pFans0, nRange0, nRangeMax, Wlc_ObjIsSignedFanin01(p, pObj) );
            int * pArg1 = Wlc_VecLoadFanins( vTemp1, pFans1, nRange1, nRangeMax, Wlc_ObjIsSignedFanin01(p, pObj) );
            for ( k = 0; k < nRange; k++ )
                Vec_IntPush( vRes, Abc_LitNotCond(Gia_ManHashAnd(pNew, pArg0[k], pArg1[k]), pObj->Type == WLC_OBJ_BIT_NAND) );
        }
        else if ( pObj->Type == WLC_OBJ_BIT_OR || pObj->Type == WLC_OBJ_BIT_NOR )
        {
            int nRangeMax = Abc_MaxInt( nRange, Abc_MaxInt(nRange0, nRange1) );
            int * pArg0 = Wlc_VecLoadFanins( vTemp0, pFans0, nRange0, nRangeMax, Wlc_ObjIsSignedFanin01(p, pObj) );
            int * pArg1 = Wlc_VecLoadFanins( vTemp1, pFans1, nRange1, nRangeMax, Wlc_ObjIsSignedFanin01(p, pObj) );
            for ( k = 0; k < nRange; k++ )
                Vec_IntPush( vRes, Abc_LitNotCond(Gia_ManHashOr(pNew, pArg0[k], pArg1[k]), pObj->Type == WLC_OBJ_BIT_NOR) );
        }
        else if ( pObj->Type == WLC_OBJ_BIT_XOR || pObj->Type == WLC_OBJ_BIT_NXOR )
        {
            int nRangeMax = Abc_MaxInt( nRange, Abc_MaxInt(nRange0, nRange1) );
            int * pArg0 = Wlc_VecLoadFanins( vTemp0, pFans0, nRange0, nRangeMax, Wlc_ObjIsSignedFanin01(p, pObj) );
            int * pArg1 = Wlc_VecLoadFanins( vTemp1, pFans1, nRange1, nRangeMax, Wlc_ObjIsSignedFanin01(p, pObj) );
            for ( k = 0; k < nRange; k++ )
                Vec_IntPush( vRes, Abc_LitNotCond(Gia_ManHashXor(pNew, pArg0[k], pArg1[k]), pObj->Type == WLC_OBJ_BIT_NXOR) );
        }
        else if ( pObj->Type == WLC_OBJ_BIT_SELECT )
        {
            Wlc_Obj_t * pFanin = Wlc_ObjFanin0(p, pObj);
            int End = Wlc_ObjRangeEnd(pObj);
            int Beg = Wlc_ObjRangeBeg(pObj);
            int Low  = Abc_MinInt( End, Beg );
            (void)Low;
            int High = Abc_MaxInt( End, Beg );
            (void)High;
            assert( nRange == High - Low + 1 );
            if ( pFanin->End >= pFanin->Beg )
            {
                assert( pFanin->Beg <= Low && High <= pFanin->End );
                for ( k = 0; k < nRange; k++ )
                {
                    int Label = End >= Beg ? Beg + k : Beg - k;
                    Vec_IntPush( vRes, pFans0[Label - pFanin->Beg] );
                }
            }
            else
            {
                assert( pFanin->End <= Low && High <= pFanin->Beg );
                for ( k = 0; k < nRange; k++ )
                {
                    int Label = End >= Beg ? Beg + k : Beg - k;
                    Vec_IntPush( vRes, pFans0[pFanin->Beg - Label] );
                }
            }
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
            assert( nRange0 <= nRange );
            for ( k = 0; k < nRange0; k++ )
                Vec_IntPush( vRes, pFans0[k] );
            for (      ; k < nRange; k++ )
                Vec_IntPush( vRes, Pad );
        }
        else if ( pObj->Type == WLC_OBJ_LOGIC_NOT )
        {
            iLit = Wlc_BlastReduction( pNew, pFans0, nRange0, WLC_OBJ_REDUCT_OR );
            Vec_IntFill( vRes, 1, Abc_LitNot(iLit) );
            for ( k = 1; k < nRange; k++ )
                Vec_IntPush( vRes, 0 );
        }
        else if ( pObj->Type == WLC_OBJ_LOGIC_IMPL )
        {
            int iLit0 = Wlc_BlastReduction( pNew, pFans0, nRange0, WLC_OBJ_REDUCT_OR );
            int iLit1 = Wlc_BlastReduction( pNew, pFans1, nRange1, WLC_OBJ_REDUCT_OR );
            Vec_IntFill( vRes, 1, Gia_ManHashOr(pNew, Abc_LitNot(iLit0), iLit1) );
            for ( k = 1; k < nRange; k++ )
                Vec_IntPush( vRes, 0 );
        }
        else if ( pObj->Type == WLC_OBJ_LOGIC_AND )
        {
            int iLit0 = Wlc_BlastReduction( pNew, pFans0, nRange0, WLC_OBJ_REDUCT_OR );
            int iLit1 = Wlc_BlastReduction( pNew, pFans1, nRange1, WLC_OBJ_REDUCT_OR );
            Vec_IntFill( vRes, 1, Gia_ManHashAnd(pNew, iLit0, iLit1) );
            for ( k = 1; k < nRange; k++ )
                Vec_IntPush( vRes, 0 );
        }
        else if ( pObj->Type == WLC_OBJ_LOGIC_OR )
        {
            int iLit0 = Wlc_BlastReduction( pNew, pFans0, nRange0, WLC_OBJ_REDUCT_OR );
            int iLit1 = Wlc_BlastReduction( pNew, pFans1, nRange1, WLC_OBJ_REDUCT_OR );
            Vec_IntFill( vRes, 1, Gia_ManHashOr(pNew, iLit0, iLit1) );
            for ( k = 1; k < nRange; k++ )
                Vec_IntPush( vRes, 0 );
        }
        else if ( pObj->Type == WLC_OBJ_LOGIC_XOR )
        {
            int iLit0 = Wlc_BlastReduction( pNew, pFans0, nRange0, WLC_OBJ_REDUCT_OR );
            int iLit1 = Wlc_BlastReduction( pNew, pFans1, nRange1, WLC_OBJ_REDUCT_OR );
            Vec_IntFill( vRes, 1, Gia_ManHashXor(pNew, iLit0, iLit1) );
            for ( k = 1; k < nRange; k++ )
                Vec_IntPush( vRes, 0 );
        }
        else if ( pObj->Type == WLC_OBJ_COMP_NOTEQU && Wlc_ObjFaninNum(pObj) > 2 )
        {
            // find the max range
            int a, b, iRes = 1, nRangeMax = Abc_MaxInt( nRange0, nRange1 );
            for ( k = 2; k < Wlc_ObjFaninNum(pObj); k++ )
                nRangeMax = Abc_MaxInt( nRangeMax, Wlc_ObjRange( Wlc_NtkObj(p, Wlc_ObjFaninId(pObj, k)) ) );
            // create pairwise distinct
            for ( a = 0; a < Wlc_ObjFaninNum(pObj); a++ )
            for ( b = a+1; b < Wlc_ObjFaninNum(pObj); b++ )
            {
                int nRange0 = Wlc_ObjRange( Wlc_NtkObj(p, Wlc_ObjFaninId(pObj, a)) );
                int nRange1 = Wlc_ObjRange( Wlc_NtkObj(p, Wlc_ObjFaninId(pObj, b)) );
                int * pFans0 = Vec_IntEntryP( vBits, Wlc_ObjCopy(p, Wlc_ObjFaninId(pObj, a)) );
                int * pFans1 = Vec_IntEntryP( vBits, Wlc_ObjCopy(p, Wlc_ObjFaninId(pObj, b)) );
                int * pArg0 = Wlc_VecLoadFanins( vTemp0, pFans0, nRange0, nRangeMax, 0 );
                int * pArg1 = Wlc_VecLoadFanins( vTemp1, pFans1, nRange1, nRangeMax, 0 );
                int iLit = 0;
                for ( k = 0; k < nRangeMax; k++ )
                    iLit = Gia_ManHashOr( pNew, iLit, Gia_ManHashXor(pNew, pArg0[k], pArg1[k]) ); 
                iRes = Gia_ManHashAnd( pNew, iRes, iLit ); 
            }
            Vec_IntFill( vRes, 1, iRes );
            for ( k = 1; k < nRange; k++ )
                Vec_IntPush( vRes, 0 );
        }
        else if ( pObj->Type == WLC_OBJ_COMP_EQU || pObj->Type == WLC_OBJ_COMP_NOTEQU )
        {
            int iLit = 0, nRangeMax = Abc_MaxInt( nRange0, nRange1 );
            int * pArg0 = Wlc_VecLoadFanins( vTemp0, pFans0, nRange0, nRangeMax, Wlc_ObjIsSignedFanin01(p, pObj) );
            int * pArg1 = Wlc_VecLoadFanins( vTemp1, pFans1, nRange1, nRangeMax, Wlc_ObjIsSignedFanin01(p, pObj) );
            for ( k = 0; k < nRangeMax; k++ )
                iLit = Gia_ManHashOr( pNew, iLit, Gia_ManHashXor(pNew, pArg0[k], pArg1[k]) ); 
            Vec_IntFill( vRes, 1, Abc_LitNotCond(iLit, pObj->Type == WLC_OBJ_COMP_EQU) );
            for ( k = 1; k < nRange; k++ )
                Vec_IntPush( vRes, 0 );
        }
        else if ( pObj->Type == WLC_OBJ_COMP_LESS || pObj->Type == WLC_OBJ_COMP_MOREEQU ||
                  pObj->Type == WLC_OBJ_COMP_MORE || pObj->Type == WLC_OBJ_COMP_LESSEQU )
        {
            int nRangeMax = Abc_MaxInt( nRange0, nRange1 );
            int fSigned = Wlc_ObjIsSignedFanin01(p, pObj);
            int * pArg0 = Wlc_VecLoadFanins( vTemp0, pFans0, nRange0, nRangeMax, fSigned );
            int * pArg1 = Wlc_VecLoadFanins( vTemp1, pFans1, nRange1, nRangeMax, fSigned );
            int fSwap  = (pObj->Type == WLC_OBJ_COMP_MORE    || pObj->Type == WLC_OBJ_COMP_LESSEQU);
            int fCompl = (pObj->Type == WLC_OBJ_COMP_MOREEQU || pObj->Type == WLC_OBJ_COMP_LESSEQU);
            if ( fSwap ) ABC_SWAP( int *, pArg0, pArg1 );
            if ( fSigned )
                iLit = pPar->fBlastNew ? Wlc_BlastLessSigned3( pNew, pArg0, pArg1, nRangeMax ) :  Wlc_BlastLessSigned( pNew, pArg0, pArg1, nRangeMax );
            else
                iLit = pPar->fBlastNew ? Wlc_BlastLess3( pNew, pArg0, pArg1, nRangeMax ) : Wlc_BlastLess( pNew, pArg0, pArg1, nRangeMax );
            iLit = Abc_LitNotCond( iLit, fCompl );
            Vec_IntFill( vRes, 1, iLit );
            for ( k = 1; k < nRange; k++ )
                Vec_IntPush( vRes, 0 );
        }
        else if ( pObj->Type == WLC_OBJ_REDUCT_AND  || pObj->Type == WLC_OBJ_REDUCT_OR  || pObj->Type == WLC_OBJ_REDUCT_XOR ||
                  pObj->Type == WLC_OBJ_REDUCT_NAND || pObj->Type == WLC_OBJ_REDUCT_NOR || pObj->Type == WLC_OBJ_REDUCT_NXOR )
        {
            Vec_IntPush( vRes, Wlc_BlastReduction( pNew, pFans0, nRange0, pObj->Type ) );
            for ( k = 1; k < nRange; k++ )
                Vec_IntPush( vRes, 0 );
        }
        else if ( pObj->Type == WLC_OBJ_ARI_ADD || pObj->Type == WLC_OBJ_ARI_SUB ) 
        {
            int nRangeMax = Abc_MaxInt( nRange, Abc_MaxInt(nRange0, nRange1) );
            int * pArg0 = Wlc_VecLoadFanins( vRes,   pFans0, nRange0, nRangeMax, Wlc_ObjIsSignedFanin01(p, pObj) );
            int * pArg1 = Wlc_VecLoadFanins( vTemp1, pFans1, nRange1, nRangeMax, Wlc_ObjIsSignedFanin01(p, pObj) );
            int CarryIn = Wlc_ObjFaninNum(pObj) == 3 ? pFans2[0] : 0;
            if ( pObj->Type == WLC_OBJ_ARI_ADD )
            {
                if ( pPar->fCla )
                    Wlc_BlastAdderCLA( pNew, pArg0, pArg1, nRangeMax, Wlc_ObjIsSignedFanin01(p, pObj), CarryIn ); // result is in pFan0 (vRes)
                    //Wlc_BlastAdderFast( pNew, pArg0, pArg1, nRangeMax, Wlc_ObjIsSignedFanin01(p, pObj), CarryIn ); // result is in pFan0 (vRes)
                else
                    Wlc_BlastAdder( pNew, pArg0, pArg1, nRangeMax, CarryIn ); // result is in pFan0 (vRes)
            }
            else 
                Wlc_BlastSubtract( pNew, pArg0, pArg1, nRange, 1 ); // result is in pFan0 (vRes)
            Vec_IntShrink( vRes, nRange );
        }
        else if ( pObj->Type == WLC_OBJ_ARI_ADDSUB ) 
        {
            int nRangeMax = Abc_MaxInt( nRange, Abc_MaxInt(nRange2, nRange3) );
            int * pArg0 = Wlc_VecLoadFanins( vTemp0, pFans2, nRange2, nRangeMax, Wlc_ObjIsSignedFanin01(p, pObj) );
            int * pArg1 = Wlc_VecLoadFanins( vTemp1, pFans2, nRange2, nRangeMax, Wlc_ObjIsSignedFanin01(p, pObj) );
            int * pArg2 = Wlc_VecLoadFanins( vTemp2, pFans3, nRange3, nRangeMax, Wlc_ObjIsSignedFanin01(p, pObj) );
            int ModeIn   = pFans0[0];
            int CarryIn  = pFans1[0]; int j;
            Wlc_BlastAdder   ( pNew, pArg0, pArg2, nRangeMax, CarryIn ); // result is in pArg0 (vTemp0)
            Wlc_BlastSubtract( pNew, pArg1, pArg2, nRangeMax, Abc_LitNot(CarryIn) ); // result is in pArg1 (vTemp1)
            Vec_IntClear( vRes );
            for ( j = 0; j < nRange; j++ )
                Vec_IntPush( vRes, Gia_ManHashMux(pNew, ModeIn, pArg0[j], pArg1[j]) ); 
        }
        else if ( pObj->Type == WLC_OBJ_ARI_MULTI )
        {
            if ( fUseOldMultiplierBlasting )
            {
                int nRangeMax = Abc_MaxInt( nRange, Abc_MaxInt(nRange0, nRange1) );
                int * pArg0 = Wlc_VecLoadFanins( vTemp0, pFans0, nRange0, nRangeMax, Wlc_ObjIsSignedFanin01(p, pObj) );
                int * pArg1 = Wlc_VecLoadFanins( vTemp1, pFans1, nRange1, nRangeMax, Wlc_ObjIsSignedFanin01(p, pObj) );
                Wlc_BlastMultiplier2( pNew, pArg0, pArg1, nRange, vTemp2, vRes );
                Vec_IntShrink( vRes, nRange );
            }
            else
            {
                int fSigned = Wlc_ObjIsSignedFanin01(p, pObj);
                int nRangeMax = Abc_MaxInt(nRange0, nRange1);
                int * pArg0 = Wlc_VecLoadFanins( vTemp0, pFans0, nRange0, nRangeMax, fSigned );
                int * pArg1 = Wlc_VecLoadFanins( vTemp1, pFans1, nRange1, nRangeMax, fSigned );
                if ( Wlc_NtkCountConstBits(pArg0, nRangeMax) < Wlc_NtkCountConstBits(pArg1, nRangeMax) ) {
                    ABC_SWAP( int *, pArg0, pArg1 );
                    ABC_SWAP( int, nRange0, nRange1 );
                }
                if ( pPar->fBooth )
                {
                    if ( pTim == NULL )
                        pTim = Wlc_BlastTimStart();
                    Wlc_BlastBoothYJ( pNew, pTim, pArg0, pArg1, nRange0, nRange1, vRes, fSigned, pPar->fCla, pParIn->fVerbose );
                }
                else if ( pPar->fBoothOld )
                    Wlc_BlastBooth( pNew, pArg0, pArg1, nRange0, nRange1, vRes, fSigned, pPar->fCla, NULL, pParIn->fVerbose );
                else if ( pPar->fWallace )
                {
                    if ( pTim == NULL )
                        pTim = Wlc_BlastTimStart();
                    Wlc_BlastWallace( pNew, pTim, pArg0, pArg1, nRange0, nRange1, vRes, fSigned, pPar->fCla, pParIn->fVerbose );
                }
                else if ( pPar->fCla )
                    Wlc_BlastMultiplier3( pNew, pArg0, pArg1, nRange0, nRange1, vRes, Wlc_ObjIsSignedFanin01(p, pObj), pPar->fCla, NULL, pParIn->fVerbose );
                else
                    Wlc_BlastMultiplier( pNew, pArg0, pArg1, nRangeMax, nRangeMax, vTemp2, vRes, fSigned );
                    //Wlc_BlastMultiplierC( pNew, pArg0, pArg1, nRangeMax, nRangeMax, vTemp2, vRes, fSigned );
                if ( nRange > Vec_IntSize(vRes) )
                    Vec_IntFillExtra( vRes, nRange, fSigned ? Vec_IntEntryLast(vRes) : 0 );
                else
                    Vec_IntShrink( vRes, nRange );
                assert( Vec_IntSize(vRes) == nRange );
            }
        }
        else if ( pObj->Type == WLC_OBJ_ARI_DIVIDE || pObj->Type == WLC_OBJ_ARI_REM || pObj->Type == WLC_OBJ_ARI_MODULUS )
        {
            int nRangeMax = Abc_MaxInt( nRange, Abc_MaxInt(nRange0, nRange1) );
            int fSigned = Wlc_ObjIsSignedFanin01(p, pObj);
            int * pArg0 = Wlc_VecLoadFanins( vTemp0, pFans0, nRange0, nRangeMax, fSigned );
            int * pArg1 = Wlc_VecLoadFanins( vTemp1, pFans1, nRange1, nRangeMax, fSigned );
            if ( fSigned )
                Wlc_BlastDividerSigned( pNew, pArg0, nRangeMax, pArg1, nRangeMax, pObj->Type == WLC_OBJ_ARI_DIVIDE, vRes, pPar->fNonRest );
            else
                Wlc_BlastDividerTop( pNew, pArg0, nRangeMax, pArg1, nRangeMax, pObj->Type == WLC_OBJ_ARI_DIVIDE, vRes, pPar->fNonRest );
            Vec_IntShrink( vRes, nRange );
            if ( !pPar->fDivBy0 )
                Wlc_BlastZeroCondition( pNew, pFans1, nRange1, vRes );
        }
        else if ( pObj->Type == WLC_OBJ_ARI_MINUS )
        {
            int nRangeMax = Abc_MaxInt( nRange0, nRange );
            int * pArg0 = Wlc_VecLoadFanins( vTemp0, pFans0, nRange0, nRangeMax, Wlc_ObjIsSignedFanin0(p, pObj) );
            Wlc_BlastMinus( pNew, pArg0, nRangeMax, vRes );
            Vec_IntShrink( vRes, nRange );
        }
        else if ( pObj->Type == WLC_OBJ_ARI_POWER )
        {
            int nRangeMax = Abc_MaxInt(nRange0, nRange);
            int * pArg0 = Wlc_VecLoadFanins( vTemp0, pFans0, nRange0, nRangeMax, Wlc_ObjIsSignedFanin0(p, pObj) );
            int * pArg1 = Wlc_VecLoadFanins( vTemp1, pFans1, nRange1, nRange1, Wlc_ObjIsSignedFanin1(p, pObj) );
            Wlc_BlastPower( pNew, pArg0, nRangeMax, pArg1, nRange1, vTemp2, vRes );
            Vec_IntShrink( vRes, nRange );
        }
        else if ( pObj->Type == WLC_OBJ_ARI_SQRT )
        {
            int * pArg0 = Wlc_VecLoadFanins( vTemp0, pFans0, nRange0, nRange0 + (nRange0 & 1), 0 );
            nRange0 += (nRange0 & 1);
            if ( pPar->fNonRest )
                Wlc_BlastSqrtNR( pNew, pArg0, nRange0, vTemp2, vRes );
            else
                Wlc_BlastSqrt( pNew, pArg0, nRange0, vTemp2, vRes );
            if ( nRange > Vec_IntSize(vRes) )
                Vec_IntFillExtra( vRes, nRange, 0 );
            else
                Vec_IntShrink( vRes, nRange );
        }
        else if ( pObj->Type == WLC_OBJ_ARI_SQUARE )
        {
            int * pArg0 = Wlc_VecLoadFanins( vTemp0, pFans0, nRange0, nRange0, 0 );
            Wlc_BlastSquare( pNew, pArg0, nRange0, vTemp2, vRes );
            if ( nRange > Vec_IntSize(vRes) )
                Vec_IntFillExtra( vRes, nRange, 0 );
            else
                Vec_IntShrink( vRes, nRange );
        }
        else if ( pObj->Type == WLC_OBJ_DEC )
        {
            int * pArg0 = Wlc_VecLoadFanins( vTemp0, pFans0, nRange0, nRange0, 0 );
            if ( pPar->fBlastNew )
                Wlc_BlastDecoder2( pNew, pArg0, nRange0, vTemp2, vRes );
            else
                Wlc_BlastDecoder( pNew, pArg0, nRange0, vTemp2, vRes );
            if ( nRange > Vec_IntSize(vRes) )
                Vec_IntFillExtra( vRes, nRange, 0 );
            else
                Vec_IntShrink( vRes, nRange );
        }
        else if ( pObj->Type == WLC_OBJ_TABLE )
            Wlc_BlastTable( pNew, Wlc_ObjTable(p, pObj), pFans0, nRange0, nRange, vRes );
        else if ( pObj->Type == WLC_OBJ_LUT && p->vLutTruths )
            Wlc_BlastLut( pNew, Vec_WrdEntry(p->vLutTruths, Wlc_ObjId(p, pObj)), pFans0, nRange0, nRange, vRes );
        else assert( 0 );
        assert( Vec_IntSize(vBits) == Wlc_ObjCopy(p, i) );
        Vec_IntAppend( vBits, vRes );
        if ( vAddOutputs && !Wlc_ObjIsCo(pObj) && 
            (
             (pObj->Type >= WLC_OBJ_MUX      && pObj->Type <= WLC_OBJ_ROTATE_L)     || 
             (pObj->Type >= WLC_OBJ_COMP_EQU && pObj->Type <= WLC_OBJ_COMP_MOREEQU) || 
             (pObj->Type >= WLC_OBJ_ARI_ADD  && pObj->Type <= WLC_OBJ_ARI_SQUARE)
            )
           )
        {
            Vec_IntAppend( vAddOutputs, vRes );
            Vec_IntPush( vAddObjs, Wlc_ObjId(p, pObj) );
        }
        p->nAnds[pObj->Type] += Gia_ManAndNum(pNew) - nAndPrev;
    }
    p->nAnds[0] = Gia_ManAndNum(pNew);
    assert( nBits == Vec_IntSize(vBits) );
    Vec_IntFree( vTemp0 );
    Vec_IntFree( vTemp1 );
    Vec_IntFree( vTemp2 );
    Vec_IntFree( vRes );
    if ( pTim )
        Wlc_BlastTimStop( pTim );
    // create flop boxes
    Wlc_NtkForEachFf2( p, pObj, i )
    {
        If_Box_t * pBox;
        char Buffer[100];
        float * pTable;
        Vec_Int_t * vTemp0 = Vec_IntAlloc( 100 );
        Vec_Int_t * vTemp1 = Vec_IntAlloc( 100 );
        int iLit, nRange = Wlc_ObjRange(pObj);
        int * pFans0, * pFans1, * pFans2, * pFans3;
        int iReset, iSet, iEnable;
        int nRangeIn = 2*nRange + 3; // D, reset, set, enable, Q
        int iSre = Wlc_ObjFaninId(pObj, 6);

        assert( pObj->Type == WLC_OBJ_FF );

        // create new box
        if ( vTables == NULL ) {
            Tim_ManSetDelayTables( pManTime, (vTables = Vec_PtrAlloc(100)) );
            Vec_PtrPush( vTables, NULL );
        }
        Tim_ManCreateBox( pManTime, curPo, nRangeIn, curPi, nRange, Vec_PtrSize(vTables), 0 );
        curPi += nRange;
        curPo += nRangeIn;

        // create delay table
        pTable = ABC_ALLOC( float, 3 + nRange * nRangeIn );
        pTable[0] = Vec_PtrSize(vTables);
        pTable[1] = nRangeIn;
        pTable[2] = nRange;
        for ( k = 0; k < nRange * nRangeIn; k++ )
            pTable[3 + k] = 1.0;
        Vec_PtrPush( vTables, pTable );

        // create combinational outputs in the normal manager
        pFans0  = Wlc_ObjFaninNum(pObj) > 0 ? Vec_IntEntryP( vBits, Wlc_ObjCopy(p, Wlc_ObjFaninId0(pObj)) ) : NULL;
        pFans1  = Wlc_ObjFaninNum(pObj) > 2 ? Vec_IntEntryP( vBits, Wlc_ObjCopy(p, Wlc_ObjFaninId(pObj,2)) ) : NULL; // reset
        pFans2  = Wlc_ObjFaninNum(pObj) > 3 ? Vec_IntEntryP( vBits, Wlc_ObjCopy(p, Wlc_ObjFaninId(pObj,3)) ) : NULL; // set
        pFans3  = Wlc_ObjFaninNum(pObj) > 4 ? Vec_IntEntryP( vBits, Wlc_ObjCopy(p, Wlc_ObjFaninId(pObj,4)) ) : NULL; // enable
        for ( k = 0; k < nRange; k++ )
            Gia_ManAppendCo( pNew, pFans0[k] );
        Gia_ManAppendCo( pNew, pFans1[0] );
        Gia_ManAppendCo( pNew, pFans2[0] );
        Gia_ManAppendCo( pNew, pFans3[0] );
        for ( k = 0; k < nRange; k++ )
            Gia_ManAppendCo( pNew, Gia_Obj2Lit(pNew, Gia_ManCi(pNew, Vec_IntEntry(vFf2Ci, i)+k)) );

        // make sure there is enough primary inputs in the manager
        for ( k = Gia_ManPiNum(pExtra); k < nRangeIn; k++ )
            Gia_ManAppendCi( pExtra );
        // create combinational inputs
        for ( k = 0; k < nRange; k++ )
            Vec_IntPush( vTemp0, Gia_Obj2Lit(pExtra, Gia_ManPi(pExtra, k)) );
        iReset  = Gia_Obj2Lit(pExtra, Gia_ManPi(pExtra, nRange+0));
        iSet    = Gia_Obj2Lit(pExtra, Gia_ManPi(pExtra, nRange+1));
        iEnable = Gia_Obj2Lit(pExtra, Gia_ManPi(pExtra, nRange+2));
        for ( k = 0; k < nRange; k++ )
            Vec_IntPush( vTemp1, Gia_Obj2Lit(pExtra, Gia_ManPi(pExtra, nRangeIn-nRange+k)) );

        // bit-blast in the external manager
        for ( k = 0; k < nRange; k++ )
        {
            // enable
            //iLitFlop = Gia_LitNotCond( Gia_ObjCopy(pObj), Gia_FlopIsOne(pObj) );
            //iLit = Gia_ManHashMux( Gia_ObjGia(pObj), Gia_FlopEnableCopy(pObj), iLit, iLitFlop );
            iLit = Gia_ManHashMux( pExtra, iEnable, Vec_IntEntry(vTemp0, k), Vec_IntEntry(vTemp1, k) );
            if ( iSre )
            {
                // reset
                //iLit = Gia_ManHashAnd( Gia_ObjGia(pObj), iLit, Gia_LitNot(Gia_FlopResetCopy(pObj)) );
                iLit = Gia_ManHashAnd( pExtra, iLit, Abc_LitNot(iReset) );
                // set
                //iLit = Gia_ManHashOr( Gia_ObjGia(pObj), iLit, Gia_FlopSetCopy(pObj) );
                iLit = Gia_ManHashOr( pExtra, iLit, iSet );
            }
            else
            {
                // set
                //iLit = Gia_ManHashOr( Gia_ObjGia(pObj), iLit, Gia_FlopSetCopy(pObj) );
                iLit = Gia_ManHashOr( pExtra, iLit, iSet );
                // reset
                //iLit = Gia_ManHashAnd( Gia_ObjGia(pObj), iLit, Gia_LitNot(Gia_FlopResetCopy(pObj)) );
                iLit = Gia_ManHashAnd( pExtra, iLit, Abc_LitNot(iReset) );
            }
            // create outputs in the external manager
            Gia_ManAppendCo( pExtra, iLit );
        }

        // add box to the library
        sprintf( Buffer, "%s%03d", "ff_comb", 1+If_LibBoxNum(pBoxLib) );
        pBox = If_BoxStart( Abc_UtilStrsav(Buffer), 1+If_LibBoxNum(pBoxLib), nRangeIn, nRange, 0, 0, 0 ); 
        If_LibBoxAdd( pBoxLib, pBox );
        for ( k = 0; k < pBox->nPis * pBox->nPos; k++ )
            pBox->pDelays[k] = 1;
        Vec_IntFree( vTemp0 );
        Vec_IntFree( vTemp1 );
    }
    Vec_IntFree( vFf2Ci );
    // create COs
    if ( pPar->fCreateMiter || pPar->fCreateWordMiter )
    {
        int nPairs = 0, nBits = 0;
        Vec_Int_t * vOuts = Vec_IntAlloc( 100 );
        assert( Wlc_NtkPoNum(p) % 2 == 0 );
        Wlc_NtkForEachCo( p, pObj, i )
        {
            if ( pObj->fIsFi )
            {
                nRange = Wlc_ObjRange( pObj );
                pFans0 = Vec_IntEntryP( vBits, Wlc_ObjCopy(p, Wlc_ObjId(p, pObj)) );
                if ( Wlc_ObjRangeIsReversed(pObj) )
                {
                    for ( k = 0; k < nRange; k++ )
                        Gia_ManAppendCo( pNew, pFans0[nRange-1-k] );
                }
                else
                {
                    for ( k = 0; k < nRange; k++ )
                        Gia_ManAppendCo( pNew, pFans0[k] );
                }
                nFFins += nRange;
                continue;
            }
            pObj2   = Wlc_NtkCo( p, ++i );
            nRange1 = Wlc_ObjRange( pObj );
            nRange2 = Wlc_ObjRange( pObj2 );
            assert( nRange1 == nRange2 );
            pFans1  = Vec_IntEntryP( vBits, Wlc_ObjCopy(p, Wlc_ObjId(p, pObj)) );
            pFans2  = Vec_IntEntryP( vBits, Wlc_ObjCopy(p, Wlc_ObjId(p, pObj2)) );
            if ( pPar->fCreateWordMiter )
            {
                Vec_IntClear( vOuts );
                if ( Wlc_ObjRangeIsReversed(pObj) )
                {
                    for ( k = 0; k < nRange1; k++ )
                        Vec_IntPushTwo( vOuts, pFans1[nRange1-1-k], pFans2[nRange2-1-k] );
                }
                else
                {
                    for ( k = 0; k < nRange1; k++ )
                        Vec_IntPushTwo( vOuts, pFans1[k], pFans2[k] );
                }
                Gia_ManAppendCo( pNew, Gia_ManHashDualMiter(pNew, vOuts) );
            }
            else
            {
                if ( Wlc_ObjRangeIsReversed(pObj) )
                {
                    for ( k = 0; k < nRange1; k++ )
                    {
                        Gia_ManAppendCo( pNew, pFans1[nRange1-1-k] );
                        Gia_ManAppendCo( pNew, pFans2[nRange2-1-k] );
                    }
                }
                else
                {
                    for ( k = 0; k < nRange1; k++ )
                    {
                        Gia_ManAppendCo( pNew, pFans1[k] );
                        Gia_ManAppendCo( pNew, pFans2[k] );
                    }
                }
            }
            nPairs++;
            nBits += nRange1;
        }
        Vec_IntFree( vOuts );
        if ( pPar->fCreateWordMiter )
            printf( "Derived an ordinary miter with %d bit-level outputs, one for each pair of word-level outputs.\n", nPairs );
        else
            printf( "Derived a dual-output miter with %d pairs of bits belonging to %d pairs of word-level outputs.\n", nBits, nPairs );
    }
    else
    {
        Wlc_NtkForEachCo( p, pObj, i )
        {
            // skip all outputs except the given ones
            if ( pPar->iOutput >= 0 && (i < pPar->iOutput || i >= pPar->iOutput + pPar->nOutputRange) )
                continue;
            // create additional PO literals
            if ( vAddOutputs && pObj->fIsFi )
            {
                Vec_IntForEachEntry( vAddOutputs, iLit, k )
                    Gia_ManAppendCo( pNew, iLit );
                printf( "Created %d additional POs for %d interesting internal word-level variables.\n", Vec_IntSize(vAddOutputs), Vec_IntSize(vAddObjs) );
                Vec_IntFreeP( &vAddOutputs );
            }
            nRange = Wlc_ObjRange( pObj );
            pFans0 = Vec_IntEntryP( vBits, Wlc_ObjCopy(p, Wlc_ObjId(p, pObj)) );
            if ( fVerbose )
                printf( "%s(%d) ", Wlc_ObjName(p, Wlc_ObjId(p, pObj)), Gia_ManCoNum(pNew) );
            if ( Wlc_ObjRangeIsReversed(pObj) )
            {
                for ( k = 0; k < nRange; k++ )
                    Gia_ManAppendCo( pNew, pFans0[nRange-1-k] );
            }
            else
            {
                for ( k = 0; k < nRange; k++ )
                    Gia_ManAppendCo( pNew, pFans0[k] );
            }
            if ( pObj->fIsFi )
                nFFins += nRange;
        }
        if ( fVerbose )
            printf( "\n" );
    }
    //Vec_IntErase( vBits );
    //Vec_IntErase( &p->vCopies );
    // set the number of registers
    if ( Vec_IntSize(&p->vFfs2) > 0 )
    {
        assert( nFFins == 0 && nFFouts == 0 );
        // complement flop inputs whose init state is 1
        for ( i = 0; i < nFf2Regs; i++ )
            Gia_ManAppendCo( pNew, Gia_ManAppendCi(pNew) );
        Gia_ManSetRegNum( pNew, nFf2Regs );
    }
    else
    {
        assert( nFFins == nFFouts );
        Gia_ManSetRegNum( pNew, nFFins );
    }
    // finalize AIG
    if ( !pPar->fGiaSimple && !pPar->fNoCleanup )
    {
        pNew = Gia_ManCleanup( pTemp = pNew );
        Gia_ManDupRemapLiterals( vBits, pTemp );
        //printf( "Cutoff ID %d became %d.\n", 75, Abc_Lit2Var(Gia_ManObj(pTemp, 73)->Value) );
        Gia_ManStop( pTemp );
    }
    // transform AIG with init state
    if ( p->pInits )
    {
        if ( (int)strlen(p->pInits) != Gia_ManRegNum(pNew) )
        {
            printf( "The number of init values (%d) does not match the number of flops (%d).\n", (int)strlen(p->pInits), Gia_ManRegNum(pNew) );
            printf( "It is assumed that the AIG has constant 0 initial state.\n" );
        }
        else
        {
            pNew = Gia_ManDupZeroUndc( pTemp = pNew, p->pInits, pPar->fSaveFfNames ? 1+Gia_ManRegNum(pNew) : 0, pPar->fGiaSimple, pPar->fVerbose );
            Gia_ManDupRemapLiterals( vBits, pTemp );
            Gia_ManStop( pTemp );
        }
    }
    // finalize AIG with boxes
    if ( Vec_IntSize(&p->vFfs2) > 0 )
    {
        curPo += nBitCos + nFf2Regs;
        assert( curPi == Tim_ManCiNum(pManTime) );
        assert( curPo == Tim_ManCoNum(pManTime) );
        // finalize the extra AIG
        pExtra = Gia_ManCleanup( pTemp = pExtra );
        Gia_ManStop( pTemp );
        assert( Gia_ManPoNum(pExtra) == Gia_ManCiNum(pNew) - nBitCis - nFf2Regs );
        // attach
        pNew->pAigExtra = pExtra;
        pNew->pManTime = pManTime;
        // normalize AIG
        pNew = Gia_ManDupNormalize( pTemp = pNew, 0 );
        Gia_ManTransferTiming( pNew, pTemp );
        Gia_ManStop( pTemp );
        //Tim_ManPrint( pManTime );
    }
    if ( pPar->vBoxIds )
    {
        curPo += nBitCos;
        assert( curPi == Tim_ManCiNum(pManTime) );
        assert( curPo == Tim_ManCoNum(pManTime) );
        // finalize the extra AIG
        pExtra = Gia_ManCleanup( pTemp = pExtra );
        Gia_ManStop( pTemp );
        assert( Gia_ManPoNum(pExtra) == Gia_ManCiNum(pNew) - nBitCis - nFf2Regs );
        // attach
        pNew->pAigExtra = pExtra;
        pNew->pManTime = pManTime;
        // normalize AIG
        pNew = Gia_ManDupNormalize( pTemp = pNew, 0 );
        Gia_ManTransferTiming( pNew, pTemp );
        Gia_ManStop( pTemp );
        //Tim_ManPrint( pManTime );
    }
    // create input names
    pNew->vNamesIn = Vec_PtrAlloc( Gia_ManCiNum(pNew) );
    Wlc_NtkForEachCi( p, pObj, i )
    if ( Wlc_ObjIsPi(pObj) )
    {
        char * pName = Wlc_ObjName(p, Wlc_ObjId(p, pObj));
        nRange = Wlc_ObjRange( pObj );
        if ( fSkipBitRange && nRange == 1 )
            Vec_PtrPush( pNew->vNamesIn, Abc_UtilStrsav(pName) );
        else
            for ( k = 0; k < nRange; k++ )
            {
                char Buffer[1000];
                sprintf( Buffer, "%s[%d]", pName, pObj->Beg < pObj->End ? pObj->Beg+k : pObj->Beg-k );
                Vec_PtrPush( pNew->vNamesIn, Abc_UtilStrsav(Buffer) );
                //printf( "Writing %s\n", Buffer );
            }
    }
    if ( p->pInits )
    {
        int Length = strlen(p->pInits);
        for ( i = 0; i < Length; i++ )
        if ( p->pInits[i] == 'x' || p->pInits[i] == 'X' )
        {
            char Buffer[100];
            sprintf( Buffer, "_%s_abc_%d_", "init", i );
            Vec_PtrPush( pNew->vNamesIn, Abc_UtilStrsav(Buffer) );
            fAdded = 1;
        }
        if ( pPar->fSaveFfNames )
            for ( i = 0; i < 1+Length; i++ )
                Vec_PtrPush( pNew->vNamesIn, NULL );
    }
    Wlc_NtkForEachCi( p, pObj, i )
    if ( !Wlc_ObjIsPi(pObj) )
    {
        char * pName = Wlc_ObjName(p, Wlc_ObjId(p, pObj));
        nRange = Wlc_ObjRange( pObj );
        if ( fSkipBitRange && nRange == 1 )
            Vec_PtrPush( pNew->vNamesIn, Abc_UtilStrsav(pName) );
        else
            for ( k = 0; k < nRange; k++ )
            {
                char Buffer[1000];
                sprintf( Buffer, "%s[%d]", pName, pObj->Beg < pObj->End ? pObj->Beg+k : pObj->Beg-k );
                Vec_PtrPush( pNew->vNamesIn, Abc_UtilStrsav(Buffer) );
            }
    }
    Wlc_NtkForEachFf2( p, pObj, i )
    {
        char * pName = Wlc_ObjName(p, Wlc_ObjId(p, pObj));
        nRange = Wlc_ObjRange( pObj );
        if ( fSkipBitRange && nRange == 1 )
        {
            char Buffer[1000];
            sprintf( Buffer, "%s_fo", pName );
            Vec_PtrPush( pNew->vNamesIn, Abc_UtilStrsav(Buffer) );
        }
        else
            for ( k = 0; k < nRange; k++ )
            {
                char Buffer[1000];
                sprintf( Buffer, "%s_fo[%d]", pName, pObj->Beg < pObj->End ? pObj->Beg+k : pObj->Beg-k );
                Vec_PtrPush( pNew->vNamesIn, Abc_UtilStrsav(Buffer) );
            }
    }
    Wlc_NtkForEachFf2( p, pObj, i )
    {
        char * pName = Wlc_ObjName(p, Wlc_ObjId(p, pObj));
        nRange = Wlc_ObjRange( pObj );
        if ( fSkipBitRange && nRange == 1 )
            Vec_PtrPush( pNew->vNamesIn, Abc_UtilStrsav(pName) );
        else
            for ( k = 0; k < nRange; k++ )
            {
                char Buffer[1000];
                sprintf( Buffer, "%s[%d]", pName, pObj->Beg < pObj->End ? pObj->Beg+k : pObj->Beg-k );
                Vec_PtrPush( pNew->vNamesIn, Abc_UtilStrsav(Buffer) );
            }
    }
    if ( p->pInits && pPar->fSaveFfNames )
    {
        char * pName;
        int Length    = (int)strlen(p->pInits);
        int NameStart = Vec_PtrSize(pNew->vNamesIn)-Length;
        int NullStart = Vec_PtrSize(pNew->vNamesIn)-2*Length;
        int SepStart  = Vec_PtrSize(pNew->vNamesIn)-2*Length-1;
        assert( Vec_PtrEntry(pNew->vNamesIn, SepStart) == NULL );
        Vec_PtrWriteEntry( pNew->vNamesIn, SepStart, Abc_UtilStrsav("_abc_190121_abc_") );
        for ( i = 0; i < Length; i++ )
        {
            char Buffer[100];
            sprintf( Buffer, "%c%s", p->pInits[i], (char *)Vec_PtrEntry(pNew->vNamesIn, NameStart+i) );
            assert( Vec_PtrEntry(pNew->vNamesIn, NullStart+i) == NULL );
            Vec_PtrWriteEntry( pNew->vNamesIn, NullStart+i, Abc_UtilStrsav(Buffer) );
        }
        Vec_PtrForEachEntry( char *, pNew->vNamesIn, pName, i )
            assert( pName != NULL );
    }
    if ( p->pInits && fAdded )
        Vec_PtrPush( pNew->vNamesIn, Abc_UtilStrsav("abc_reset_flop") );
    if ( pPar->vBoxIds )
    {
        Wlc_NtkForEachObjVec( pPar->vBoxIds, p, pObj, i )
        {
            char * pName = Wlc_ObjName(p, Wlc_ObjId(p, pObj));
            nRange = Wlc_ObjRange( pObj );
            assert( nRange > 1 );
            for ( k = 0; k < nRange; k++ )
            {
                char Buffer[1000];
                sprintf( Buffer, "%s[%d]", pName, pObj->Beg < pObj->End ? pObj->Beg+k : pObj->Beg-k );
                Vec_PtrPush( pNew->vNamesIn, Abc_UtilStrsav(Buffer) );
            }
        }
    }
    assert( Vec_PtrSize(pNew->vNamesIn) == Gia_ManCiNum(pNew) );
    // create output names
    pNew->vNamesOut = Vec_PtrAlloc( Gia_ManCoNum(pNew) );
    Wlc_NtkForEachFf2( p, pObj, i )
    {
        int iFanin;
        Wlc_ObjForEachFanin( pObj, iFanin, b )
        {
            char * pName = Wlc_ObjName(p, iFanin);
            nRange = Wlc_ObjRange( Wlc_NtkObj(p, iFanin) );
            if ( fSkipBitRange && nRange == 1 )
                Vec_PtrPush( pNew->vNamesOut, Abc_UtilStrsav(pName) );
            else
                for ( k = 0; k < nRange; k++ )
                {
                    char Buffer[1000];
                    Wlc_Obj_t * pFanin = Wlc_NtkObj(p, iFanin);
                    sprintf( Buffer, "%s[%d]", pName, pFanin->Beg < pFanin->End ? pFanin->Beg+k : pFanin->Beg-k );
                    Vec_PtrPush( pNew->vNamesOut, Abc_UtilStrsav(Buffer) );
                }
            if ( b == 3 )
                break;
        }
        {
            char * pName = Wlc_ObjName(p, Wlc_ObjId(p, pObj));
            nRange = Wlc_ObjRange( pObj );
            if ( fSkipBitRange && nRange == 1 )
            {
                char Buffer[1000];
                sprintf( Buffer, "%s_in", pName );
                Vec_PtrPush( pNew->vNamesOut, Abc_UtilStrsav(Buffer) );
            }
            else
                for ( k = 0; k < nRange; k++ )
                {
                    char Buffer[1000];
                    sprintf( Buffer, "%s_in[%d]", pName, pObj->Beg < pObj->End ? pObj->Beg+k : pObj->Beg-k );
                    Vec_PtrPush( pNew->vNamesOut, Abc_UtilStrsav(Buffer) );
                }
        }
    }
    if ( pPar->vBoxIds )
    {
        Wlc_NtkForEachObjVec( pPar->vBoxIds, p, pObj, i )
        {
            int iFanin, f;
            Wlc_ObjForEachFanin( pObj, iFanin, f )
            {
                char * pName = Wlc_ObjName(p, iFanin);
                nRange = Wlc_ObjRange( Wlc_NtkObj(p, iFanin) );
                assert( nRange >= 1 );
                for ( k = 0; k < nRange; k++ )
                {
                    char Buffer[1000];
                    Wlc_Obj_t * pFanin = Wlc_NtkObj(p, iFanin);
                    sprintf( Buffer, "%s[%d]", pName, pFanin->Beg < pFanin->End ? pFanin->Beg+k : pFanin->Beg-k );
                    Vec_PtrPush( pNew->vNamesOut, Abc_UtilStrsav(Buffer) );
                }
            }
        }
    }
    // add real primary outputs
    Wlc_NtkForEachCo( p, pObj, i )
    if ( Wlc_ObjIsPo(pObj) )
    {
        char * pName = Wlc_ObjName(p, Wlc_ObjId(p, pObj));
        nRange = Wlc_ObjRange( pObj );
        if ( pPar->fCreateWordMiter )
        {
            Wlc_Obj_t * pObj2 = Wlc_NtkCo( p, ++i );
            char * pName2 = Wlc_ObjName(p, Wlc_ObjId(p, pObj2));
            char Buffer[1000];
            sprintf( Buffer, "%s_xor_%s", pName, pName2 );
            Vec_PtrPush( pNew->vNamesOut, Abc_UtilStrsav(Buffer) );
            //printf( "Adding output %s\n", Buffer );
        }
        else if ( pPar->fCreateMiter && nRange > 1 )
        {
            Wlc_Obj_t * pObj2 = Wlc_NtkCo( p, ++i );
            char * pName2 = Wlc_ObjName(p, Wlc_ObjId(p, pObj2));
            int nRange1 = Wlc_ObjRange( pObj );
            (void)nRange1;
            assert( nRange == nRange1 );
            for ( k = 0; k < nRange; k++ )
            {
                char Buffer[1000];
                sprintf( Buffer, "%s[%d]", pName, pObj->Beg < pObj->End ? pObj->Beg+k : pObj->Beg-k );
                Vec_PtrPush( pNew->vNamesOut, Abc_UtilStrsav(Buffer) );
                sprintf( Buffer, "%s[%d]", pName2, pObj->Beg < pObj->End ? pObj->Beg+k : pObj->Beg-k );
                Vec_PtrPush( pNew->vNamesOut, Abc_UtilStrsav(Buffer) );
            }
        }
        else 
        {
            if ( fSkipBitRange && nRange == 1 )
                Vec_PtrPush( pNew->vNamesOut, Abc_UtilStrsav(pName) );
            else
                for ( k = 0; k < nRange; k++ )
                {
                    char Buffer[1000];
                    sprintf( Buffer, "%s[%d]", pName, pObj->Beg < pObj->End ? pObj->Beg+k : pObj->Beg-k );
                    Vec_PtrPush( pNew->vNamesOut, Abc_UtilStrsav(Buffer) );
                }
        }
    }
    if ( vAddObjs )
    {
        // add internal primary outputs
        Wlc_NtkForEachObjVec( vAddObjs, p, pObj, i )
        {
            char * pName = Wlc_ObjName(p, Wlc_ObjId(p, pObj));
            nRange = Wlc_ObjRange( pObj );
            if ( fSkipBitRange && nRange == 1 )
                Vec_PtrPush( pNew->vNamesOut, Abc_UtilStrsav(pName) );
            else
                for ( k = 0; k < nRange; k++ )
                {
                    char Buffer[1000];
                    sprintf( Buffer, "%s[%d]", pName, pObj->Beg < pObj->End ? pObj->Beg+k : pObj->Beg-k );
                    Vec_PtrPush( pNew->vNamesOut, Abc_UtilStrsav(Buffer) );
                }
        }
        Vec_IntFreeP( &vAddObjs );
    }
    // add flop outputs
    if ( fAdded )
        Vec_PtrPush( pNew->vNamesOut, Abc_UtilStrsav("abc_reset_flop_in") );
    Wlc_NtkForEachCo( p, pObj, i )
    if ( !Wlc_ObjIsPo(pObj) )
    {
        char * pName = Wlc_ObjName(p, Wlc_ObjId(p, pObj));
        nRange = Wlc_ObjRange( pObj );
        if ( fSkipBitRange && nRange == 1 )
        {
            char Buffer[1000];
            sprintf( Buffer, "%s_fi", pName );
            Vec_PtrPush( pNew->vNamesOut, Abc_UtilStrsav(Buffer) );
        }
        else
            for ( k = 0; k < nRange; k++ )
            {
                char Buffer[1000];
                sprintf( Buffer, "%s_fi[%d]", pName, pObj->Beg < pObj->End ? pObj->Beg+k : pObj->Beg-k );
                Vec_PtrPush( pNew->vNamesOut, Abc_UtilStrsav(Buffer) );
            }
    }
    Wlc_NtkForEachFf2( p, pObj, i )
    {
        char * pName = Wlc_ObjName(p, Wlc_ObjId(p, pObj));
        nRange = Wlc_ObjRange( pObj );
        if ( fSkipBitRange && nRange == 1 )
        {
            char Buffer[1000];
            sprintf( Buffer, "%s_fi", pName );
            Vec_PtrPush( pNew->vNamesOut, Abc_UtilStrsav(Buffer) );
        }
        else
            for ( k = 0; k < nRange; k++ )
            {
                char Buffer[1000];
                sprintf( Buffer, "%s_fi[%d]", pName, pObj->Beg < pObj->End ? pObj->Beg+k : pObj->Beg-k );
                Vec_PtrPush( pNew->vNamesOut, Abc_UtilStrsav(Buffer) );
            }
    }
    assert( Vec_PtrSize(pNew->vNamesOut) == Gia_ManCoNum(pNew) );

    // replace the current library
    if ( pBoxLib )
    {
        If_LibBoxFree( (If_LibBox_t *)Abc_FrameReadLibBox() );
        Abc_FrameSetLibBox( pBoxLib );
    }

    // dump the miter parts
    if ( 0 )
    {
        char pFileName0[1000], pFileName1[1000];
        char * pNameGeneric = Extra_FileNameGeneric( p->pSpec );
        Vec_Int_t * vOrder = Vec_IntStartNatural( Gia_ManPoNum(pNew) );
        Gia_Man_t * pGia0 = Gia_ManDupCones( pNew, Vec_IntArray(vOrder),                         Vec_IntSize(vOrder)/2, 0 );
        Gia_Man_t * pGia1 = Gia_ManDupCones( pNew, Vec_IntArray(vOrder) + Vec_IntSize(vOrder)/2, Vec_IntSize(vOrder)/2, 0 );
        assert( Gia_ManPoNum(pNew) % 2 == 0 );
        sprintf( pFileName0, "%s_lhs_.aig", pNameGeneric );
        sprintf( pFileName1, "%s_rhs_.aig", pNameGeneric );
        Gia_AigerWrite( pGia0, pFileName0, 0, 0, 0 );
        Gia_AigerWrite( pGia1, pFileName1, 0, 0, 0 );
        Gia_ManStop( pGia0 );
        Gia_ManStop( pGia1 );
        Vec_IntFree( vOrder );
        ABC_FREE( pNameGeneric );
        printf( "Dumped two parts of the miter into files \"%s\" and \"%s\".\n", pFileName0, pFileName1 );
    }
    //Wlc_NtkPrintNameArray( pNew->vNamesIn );
    //Wlc_NtkPrintNameArray( pNew->vNamesOut );
    if ( pPar->vBoxIds )
    {
        Vec_PtrFreeFree( pNew->vNamesIn );   pNew->vNamesIn  = NULL;
        Vec_PtrFreeFree( pNew->vNamesOut );  pNew->vNamesOut = NULL;
    }
    pNew->vRegClasses = vRegClasses;
    // save initial box info
//    if ( pNew->pManTime ) {
//        Abc_Frame_t * pAbc = Abc_FrameGetGlobalFrame();
//        pAbc->vMiniLutObjs = Gia_ManDeriveBoxMapping( pNew );        
//    }
    //Wlc_NtkDumpMulties( p, pNew );
    return pNew;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float * Extra_FileReadFloat( FILE * pFile, int * pnFileSize )
{
    float * pBuffer;
    int RetValue, nFileSize;
    fseek( pFile, 0, SEEK_END );  
    nFileSize = *pnFileSize = ftell( pFile );  
    rewind( pFile ); 
    assert( nFileSize%4 == 0 );
    pBuffer = ABC_CALLOC( float, nFileSize/4 );
    RetValue = fread( pBuffer, nFileSize, 1, pFile );
    return pBuffer;
}
float * Extra_FileReadFloatContents( char * pFileName, int * pnFileSize )
{
    FILE * pFile;
    float * pBuffer;
    pFile = fopen( pFileName, "rb" );
    pBuffer = pFile ? Extra_FileReadFloat( pFile, pnFileSize ) : NULL;
    if ( pFile )  fclose( pFile );
    return pBuffer;
}
static inline int Extra_FixedFound( int Value, int Fixed )
{
    Value  += 1 << (Fixed-1);
    Value >>= Fixed;
    return Value;
}
static inline int Extra_ConvertFloat8( float Value )
{
    return Extra_FixedFound( (int)(Value * (1 << 16)), 8 );
}
Gia_Man_t * Wlc_BlastArray( char * pFileName )
{
    int nFileSize = 0;
    float * pBuffer = Extra_FileReadFloatContents( pFileName, &nFileSize );
    int i, v, Value, nInputs = nFileSize/4 - 1;
    Vec_Int_t * vArg0 = Vec_IntAlloc( 100 );
    Vec_Int_t * vArg1 = Vec_IntAlloc( 100 );
    Vec_Int_t * vTemp = Vec_IntAlloc( 100 );
    Vec_Int_t * vRes  = Vec_IntAlloc( 100 );
    Vec_Int_t * vSum  = Vec_IntAlloc( 100 );
    Gia_Man_t * pTemp, * pNew = Gia_ManStart( 10000 );
    pNew->pName = Abc_UtilStrsav( "blast" );
    Gia_ManHashAlloc( pNew );
    for ( i = 0; i < 8*nInputs; i++ )
        Gia_ManAppendCi(pNew);

    Value = (Extra_ConvertFloat8(pBuffer[0]) << 8) | (1 << 7);
    for ( v = 0; v < 20; v++ )
        Vec_IntPush( vSum, (Value >> v) & 1 );
    
    for ( i = 0; i < nInputs; i++ )
    {
        Value = Extra_ConvertFloat8( pBuffer[1+i] );

        Vec_IntClear( vArg0 );
        for ( v = 0; v < 8; v++ )
            Vec_IntPush( vArg0, Gia_ManCiLit(pNew, 8*i+v) );

        Vec_IntClear( vArg1 );
        for ( v = 0; v < 12; v++ )
            Vec_IntPush( vArg1, (Value >> v) & 1 );

        Wlc_BlastMultiplier( pNew, Vec_IntArray(vArg0), Vec_IntArray(vArg1), 8, 12, vTemp, vRes, 1 );
        Wlc_BlastAdder( pNew, Vec_IntArray(vSum), Vec_IntArray(vRes), 20, 0 );
    }
    ABC_FREE( pBuffer );
    for ( v = 8; v < 16; v++ )
        Gia_ManAppendCo( pNew, Vec_IntEntry(vSum, v) );
    Vec_IntFree( vArg0 );
    Vec_IntFree( vArg1 );
    Vec_IntFree( vTemp );
    Vec_IntFree( vRes );
    Vec_IntFree( vSum );

    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Wlc_ComputePerm( Wlc_Ntk_t * pNtk, int nPis )
{
    Vec_Int_t * vPerm  = Vec_IntAlloc( 100 );
    Vec_Int_t * vSizes = Vec_IntAlloc( 100 );
    Vec_Int_t * vOffs  = Vec_IntAlloc( 100 );
    Wlc_Obj_t * pObj; 
    int i, k, First, Size, nBitCis = 0, fChange = 1;
    Wlc_NtkForEachPi( pNtk, pObj, i )
    {
        Vec_IntPush( vOffs, nBitCis );
        Vec_IntPush( vSizes, Wlc_ObjRange(pObj) );
        nBitCis += Wlc_ObjRange(pObj);
    }
    for ( k = 0; fChange; k++ )
    {
        fChange = 0;
        Vec_IntForEachEntryTwo( vOffs, vSizes, First, Size, i )
            if ( k < Size )
            {
                Vec_IntPush( vPerm, First+k );
                fChange = 1;
            }
    }
    assert( Vec_IntSize(vPerm) == nBitCis );
    Vec_IntFree( vOffs );
    Vec_IntFree( vSizes );
    Vec_IntReverseOrder( vPerm );
    for ( i = Vec_IntSize(vPerm); i < nPis; i++ )
        Vec_IntPush( vPerm, i );
    //Vec_IntPrint( vPerm );
    return vPerm;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Wlc_TransferPioNames( Wlc_Ntk_t * p, Gia_Man_t * pNew )
{
    int fSkipBitRange = 0;
    Wlc_Obj_t * pObj; int i, k;
    Vec_PtrFreeP( &pNew->vNamesIn );
    Vec_PtrFreeP( &pNew->vNamesOut );
    pNew->vNamesIn = Vec_PtrAlloc( Gia_ManPiNum(pNew) );
    pNew->vNamesOut = Vec_PtrAlloc( Gia_ManPoNum(pNew) );
    // create input names
    Wlc_NtkForEachCi( p, pObj, i )
    if ( Wlc_ObjIsPi(pObj) )
    {
        char * pName = Wlc_ObjName(p, Wlc_ObjId(p, pObj));
        int nRange = Wlc_ObjRange( pObj );
        if ( fSkipBitRange && nRange == 1 )
            Vec_PtrPush( pNew->vNamesIn, Abc_UtilStrsav(pName) );
        else
            for ( k = 0; k < nRange; k++ )
            {
                char Buffer[1000];
                sprintf( Buffer, "%s[%d]", pName, pObj->Beg < pObj->End ? pObj->Beg+k : pObj->Beg-k );
                Vec_PtrPush( pNew->vNamesIn, Abc_UtilStrsav(Buffer) );
                //printf( "Writing %s\n", Buffer );
            }
    }    
    // add real primary outputs
    Wlc_NtkForEachCo( p, pObj, i )
    if ( Wlc_ObjIsPo(pObj) )
    {
        char * pName = Wlc_ObjName(p, Wlc_ObjId(p, pObj));
        int nRange = Wlc_ObjRange( pObj );
        if ( fSkipBitRange && nRange == 1 )
            Vec_PtrPush( pNew->vNamesOut, Abc_UtilStrsav(pName) );
        else
            for ( k = 0; k < nRange; k++ )
            {
                char Buffer[1000];
                sprintf( Buffer, "%s[%d]", pName, pObj->Beg < pObj->End ? pObj->Beg+k : pObj->Beg-k );
                Vec_PtrPush( pNew->vNamesOut, Abc_UtilStrsav(Buffer) );
            }
    }
    if ( Vec_PtrSize(pNew->vNamesIn) != Gia_ManPiNum(pNew) ) 
        printf( "The number of input bits (%d) does not match the number of primary inputs (%d) in the current AIG.\n", Vec_PtrSize(pNew->vNamesIn), Gia_ManPiNum(pNew) );
    if ( Vec_PtrSize(pNew->vNamesOut) != Gia_ManPoNum(pNew) ) 
        printf( "The number of output bits (%d) does not match the number of primary inputs (%d) in the current AIG.\n", Vec_PtrSize(pNew->vNamesOut), Gia_ManPoNum(pNew) );
    if ( Vec_PtrSize(pNew->vNamesIn) != Gia_ManPiNum(pNew) || Vec_PtrSize(pNew->vNamesOut) != Gia_ManPoNum(pNew) ) 
    {
        Vec_PtrFreeP( &pNew->vNamesIn );
        Vec_PtrFreeP( &pNew->vNamesOut );
    }
    else
        printf( "Successfully transferred the primary input/output names from the word-level design to the current AIG.\n" );
}
    
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Wlc_MultBlastFileGen( int a, int b, int s )
{
    FILE * pFile = fopen( "_test13_.v", "wb" );
    fprintf( pFile, "module test ( a, b, z );\n" );
    fprintf( pFile, "input %s [%d:0] a;\n", s ? "signed":"", a-1 );
    fprintf( pFile, "input %s [%d:0] b;\n", s ? "signed":"", b-1 );
    fprintf( pFile, "output %s [%d:0] z;\n", s ? "signed":"", a+b-1 );
    fprintf( pFile, "assign z = a * b;\n" );
    fprintf( pFile, "endmodule\n" );    
    fclose( pFile );
}
void Wlc_MultBlastTest()
{
    char * Command = "%read _test13_.v; %blast; &ps; &w 1.aig;  %read _test13_.v; %blast -b; &ps; &w 2.aig; cec -n 1.aig 2.aig";
    int a, b, s, Iters = 0;
    for ( a = 1; a < 8; a++ )
    for ( b = 1; b < 8; b++ )
    for ( s = 0; s < 2; s++ )
    {
        Wlc_MultBlastFileGen( a, b, s );
        if ( Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), Command ) )
        {
            fprintf( stdout, "Cannot execute command \"%s\".\n", Command );
            return;
        }
        Iters++;
    }
    printf( "Finished %d iterations.\n", Iters );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
