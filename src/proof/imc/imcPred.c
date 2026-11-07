/**CFile****************************************************************

  FileName    [imcPred.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Interpolation-based model checking.]

  Synopsis    [Definitional extensions of the interpolation interface.]

  Author      [ABC contributors]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 23, 2026.]

  Revision    [$Id: imcPred.c,v 1.00 2026/10/23 00:00:00 alanmi Exp $]

***********************************************************************/

#include "imcInt.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Recognizes an XOR or equivalence of two register outputs.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_PredXorRegisters( Gia_Man_t * p, Gia_Obj_t * pObj, int * pReg0, int * pReg1 )
{
    Gia_Obj_t * p0, * p1;
    int a, b, c, d;
    if ( !Gia_ObjFaninC0(pObj) || !Gia_ObjFaninC1(pObj) )
        return 0;
    p0 = Gia_ObjFanin0( pObj );
    p1 = Gia_ObjFanin1( pObj );
    if ( !Gia_ObjIsAnd(p0) || !Gia_ObjIsAnd(p1) )
        return 0;
    a = Gia_ObjFaninLit0p( p, p0 );
    b = Gia_ObjFaninLit1p( p, p0 );
    c = Gia_ObjFaninLit0p( p, p1 );
    d = Gia_ObjFaninLit1p( p, p1 );
    if ( !((a == (c ^ 1) && b == (d ^ 1)) || (a == (d ^ 1) && b == (c ^ 1))) )
        return 0;
    p0 = Gia_ManObj( p, Abc_Lit2Var(a) );
    p1 = Gia_ManObj( p, Abc_Lit2Var(b) );
    if ( !Gia_ObjIsRo(p, p0) || !Gia_ObjIsRo(p, p1) )
        return 0;
    a = Gia_ObjCioId(p0) - Gia_ManPiNum(p);
    b = Gia_ObjCioId(p1) - Gia_ManPiNum(p);
    *pReg0 = Abc_MinInt( a, b );
    *pReg1 = Abc_MaxInt( a, b );
    return a != b;
}

/**Function*************************************************************

  Synopsis    [Classifies the circuit structure used to select predicate templates.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_PredClass( Gia_Man_t * pGia )
{
    Vec_Int_t * vStack = Vec_IntAlloc( 64 );
    Vec_Str_t * vSeen = Vec_StrStart( Gia_ManObjNum(pGia) );
    Gia_Obj_t * pObj;
    int Lit, Seen, Mask, nPairs = 0, fRecord = 0;
    Vec_IntPush( vStack, Gia_ObjFaninLit0p(pGia, Gia_ManPo(pGia, 0)) );
    while ( Vec_IntSize(vStack) )
    {
        Gia_Obj_t * p0, * p1;
        Lit = Vec_IntPop( vStack );
        pObj = Gia_ManObj( pGia, Abc_Lit2Var(Lit) );
        Seen = Vec_StrEntry( vSeen, Abc_Lit2Var(Lit) );
        Mask = 1 << Abc_LitIsCompl(Lit);
        if ( Seen & Mask )
            continue;
        Vec_StrWriteEntry( vSeen, Abc_Lit2Var(Lit), Seen | Mask );
        if ( Gia_ObjRecognizeExor(pObj, &p0, &p1) &&
             Gia_ObjIsRo(pGia, Gia_Regular(p0)) && Gia_ObjIsRo(pGia, Gia_Regular(p1)) )
        {
            nPairs += Seen == 0;
            continue;
        }
        if ( Abc_LitIsCompl(Lit) )
            continue;
        if ( Gia_ObjIsRo(pGia, pObj) )
        {
            Gia_Obj_t * pRi = Gia_ObjRoToRi( pGia, pObj );
            Gia_Obj_t * pDriver = Gia_ObjFanin0( pRi );
            if ( Gia_ObjFaninC0(pRi) && Gia_ObjIsAnd(pDriver) &&
                 ((Gia_ObjFanin0(pDriver) == pObj && Gia_ObjFaninC0(pDriver)) ||
                  (Gia_ObjFanin1(pDriver) == pObj && Gia_ObjFaninC1(pDriver))) )
                fRecord = 1;
        }
        else if ( Gia_ObjIsAnd(pObj) )
        {
            Vec_IntPush( vStack, Gia_ObjFaninLit0p(pGia, pObj) );
            Vec_IntPush( vStack, Gia_ObjFaninLit1p(pGia, pObj) );
        }
    }
    Vec_IntFree( vStack );
    Vec_StrFree( vSeen );
    if ( fRecord && nPairs >= 4 )
        return 1;
    // A full register-word comparison can benefit from linear templates
    // even when the property does not compare a saved and a live state.
    if ( Gia_ManRegNum(pGia) > 512 )
        return 0;
    nPairs = 0;
    Gia_ManForEachAnd( pGia, pObj, Lit )
    {
        Gia_Obj_t * p0, * p1;
        if ( Gia_ObjRecognizeExor(pObj, &p0, &p1) &&
             Gia_ObjIsRo(pGia, Gia_Regular(p0)) && Gia_ObjIsRo(pGia, Gia_Regular(p1)) )
            nPairs++;
    }
    return nPairs >= 16 ? 2 : 0;
}


// Cofactor registers with constant-one successors for predicate discovery.
// This graph is never used as the transition relation or as a proof.
/**Function*************************************************************

  Synopsis    [Cofactors constant-one successors when classifying the circuit.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Imc_PredAfterInit( Gia_Man_t * pGia )
{
    Gia_Man_t * pNew, * pResult;
    Vec_Int_t * vMap;
    Gia_Obj_t * pObj;
    int i, Count = 0;
    Gia_ManForEachRi( pGia, pObj, i )
        Count += Gia_ObjFaninLit0p(pGia, pObj) == 1;
    if ( !Count )
        return NULL;
    vMap = Vec_IntStart( Gia_ManObjNum(pGia) );
    pNew = Gia_ManStart( Gia_ManObjNum(pGia) );
    Gia_ManHashStart( pNew );
    Gia_ManForEachCi( pGia, pObj, i )
        Vec_IntWriteEntry( vMap, Gia_ObjId(pGia, pObj), Gia_ManAppendCi(pNew) );
    Gia_ManForEachRo( pGia, pObj, i )
        if ( Gia_ObjFaninLit0p(pGia, Gia_ManRi(pGia, i)) == 1 )
            Vec_IntWriteEntry( vMap, Gia_ObjId(pGia, pObj), 1 );
    Gia_ManForEachAnd( pGia, pObj, i )
        Vec_IntWriteEntry( vMap, i, Gia_ManHashAnd(pNew,
            Vec_IntEntry(vMap, Gia_ObjFaninId0p(pGia, pObj)) ^ Gia_ObjFaninC0(pObj),
            Vec_IntEntry(vMap, Gia_ObjFaninId1p(pGia, pObj)) ^ Gia_ObjFaninC1(pObj)) );
    Gia_ManForEachCo( pGia, pObj, i )
        Gia_ManAppendCo( pNew, Vec_IntEntry(vMap, Gia_ObjFaninId0p(pGia, pObj)) ^ Gia_ObjFaninC0(pObj) );
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(pGia) );
    pResult = Gia_ManCleanup( pNew );
    Gia_ManStop( pNew );
    Vec_IntFree( vMap );
    return pResult;
}

/**Function*************************************************************

  Synopsis    [Classifies the original circuit and its first-step cofactor.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Imc_ManPredicateClass( Gia_Man_t * pGia, int * pfAfterInit )
{
    int Result = Imc_PredClass( pGia );
    Gia_Man_t * pNew;
    if ( pfAfterInit )
        *pfAfterInit = 0;
    if ( Result || Gia_ManRegNum(pGia) > 512 )
        return Result;
    pNew = Imc_PredAfterInit( pGia );
    if ( pNew )
    {
        Result = Imc_PredClass( pNew );
        if ( pfAfterInit )
            *pfAfterInit = Result != 0;
        Gia_ManStop( pNew );
    }
    return Result;
}

/**Function*************************************************************

  Synopsis    [Records a distinct register word within the word limit.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Imc_PredAddWord( Vec_Int_t * vWords, int Base, int Width )
{
    int i;
    for ( i = 0; i < Vec_IntSize(vWords); i += 2 )
        if ( Vec_IntEntry(vWords, i) == Base && Vec_IntEntry(vWords, i + 1) == Width )
            return;
    if ( Vec_IntSize(vWords) >= 16 )
        return;
    Vec_IntPush( vWords, Base );
    Vec_IntPush( vWords, Width );
}

// Zero/ones tests expose words that are absent from register comparisons.
// Keep maximal nonoverlapping intervals before considering narrower ones.
/**Function*************************************************************

  Synopsis    [Finds register words in all-zero and all-one comparisons.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Imc_PredConstantWords( Gia_Man_t * pGia, Vec_Int_t * vWords, abctime TimeStop )
{
    Vec_Int_t * vBase = Vec_IntStartFull( Gia_ManObjNum(pGia) );
    Vec_Int_t * vSize = Vec_IntStart( Gia_ManObjNum(pGia) );
    Vec_Int_t * vPol = Vec_IntStart( Gia_ManObjNum(pGia) );
    Gia_Obj_t * pObj;
    int i, j, a, b, Size0, Size1, Base0, Base1, Pol0, Pol1, Width;
    Gia_ManForEachRo( pGia, pObj, i )
    {
        Vec_IntWriteEntry( vBase, Gia_ObjId(pGia, pObj), i );
        Vec_IntWriteEntry( vSize, Gia_ObjId(pGia, pObj), 1 );
    }
    Gia_ManForEachAnd( pGia, pObj, i )
    {
        if ( (i & 1023) == 0 && TimeStop && Abc_Clock() >= TimeStop )
            goto finish;
        a = Gia_ObjFaninId0p(pGia, pObj); b = Gia_ObjFaninId1p(pGia, pObj);
        Size0 = Vec_IntEntry(vSize, a); Size1 = Vec_IntEntry(vSize, b);
        if ( !Size0 || !Size1 || Size0 + Size1 > 64 ||
             (Size0 > 1 && Gia_ObjFaninC0(pObj)) || (Size1 > 1 && Gia_ObjFaninC1(pObj)) )
            continue;
        Base0 = Vec_IntEntry(vBase, a); Base1 = Vec_IntEntry(vBase, b);
        Pol0 = Vec_IntEntry(vPol, a) ^ Gia_ObjFaninC0(pObj);
        Pol1 = Vec_IntEntry(vPol, b) ^ Gia_ObjFaninC1(pObj);
        if ( Pol0 != Pol1 || (Base0 + Size0 != Base1 && Base1 + Size1 != Base0) )
            continue;
        Vec_IntWriteEntry( vBase, i, Abc_MinInt(Base0, Base1) );
        Vec_IntWriteEntry( vSize, i, Size0 + Size1 );
        Vec_IntWriteEntry( vPol, i, Pol0 );
    }
    for ( Width = 32; Width >= 4; Width /= 2 )
        Gia_ManForEachAnd( pGia, pObj, i )
        {
            if ( (i & 1023) == 0 && TimeStop && Abc_Clock() >= TimeStop )
                goto finish;
            if ( Vec_IntEntry(vSize, i) != Width )
                continue;
            Base0 = Vec_IntEntry(vBase, i);
            for ( j = 0; j < Vec_IntSize(vWords); j += 2 )
                if ( Base0 < Vec_IntEntry(vWords, j) + Vec_IntEntry(vWords, j + 1) &&
                     Vec_IntEntry(vWords, j) < Base0 + Width )
                    break;
            if ( j == Vec_IntSize(vWords) )
                Imc_PredAddWord( vWords, Base0, Width );
        }
finish:
    Vec_IntFree( vBase );
    Vec_IntFree( vSize );
    Vec_IntFree( vPol );
}

/**Function*************************************************************

  Synopsis    [Builds a modular word-addition equality predicate.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_PredSum( Gia_Man_t * p, int Base0, int Base1, int Base2, int Width, int fReverse )
{
    int i, a, b, c, Xor, Sum, Carry = 0, Equal = 1;
    for ( i = 0; i < Width; i++ )
    {
        int Bit = fReverse ? Width - 1 - i : i;
        a = Gia_Obj2Lit( p, Gia_ManCi(p, Base0 + Bit) );
        b = Gia_Obj2Lit( p, Gia_ManCi(p, Base1 + Bit) );
        c = Gia_Obj2Lit( p, Gia_ManCi(p, Base2 + Bit) );
        Xor = Gia_ManHashXor( p, a, b );
        Sum = Gia_ManHashXor( p, Xor, Carry );
        Carry = Gia_ManHashOr( p, Gia_ManHashAnd(p, a, b), Gia_ManHashAnd(p, Xor, Carry) );
        Equal = Gia_ManHashAnd( p, Equal, Gia_ManHashXor(p, Sum, c) ^ 1 );
    }
    return Equal;
}

/**Function*************************************************************

  Synopsis    [Adds word-addition predicates within the output and time limits.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Imc_PredLinear( Gia_Man_t * p, Vec_Int_t * vWords, Vec_Int_t * vOutputs, abctime TimeStop )
{
    int i, j, k, Order, Width;
    for ( i = 0; i < Vec_IntSize(vWords); i += 2 )
        for ( j = i + 2; j < Vec_IntSize(vWords); j += 2 )
            for ( k = 0; k < Vec_IntSize(vWords); k += 2 )
            {
                if ( Vec_IntSize(vOutputs) >= IMC_PRED_MAX - 42 || (TimeStop && Abc_Clock() >= TimeStop) )
                    return;
                Width = Vec_IntEntry( vWords, i + 1 );
                if ( k == i || k == j || Width < 4 ||
                     Width != Vec_IntEntry(vWords, j + 1) || Width != Vec_IntEntry(vWords, k + 1) )
                    continue;
                for ( Order = 0; Order < 2; Order++ )
                    Vec_IntPushUnique( vOutputs, Imc_PredSum(p, Vec_IntEntry(vWords, i),
                        Vec_IntEntry(vWords, j), Vec_IntEntry(vWords, k), Width, Order) );
            }
}

/**Function*************************************************************

  Synopsis    [Builds a signed or unsigned less-than predicate in either bit order.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_PredLess( Gia_Man_t * p, int Base0, int Base1, int Width, int fSigned, int fReverse )
{
    int i, a, b, Equal, Less = 0;
    for ( i = 0; i < Width; i++ )
    {
        int Bit = fReverse ? Width - 1 - i : i;
        a = Gia_Obj2Lit( p, Gia_ManCi(p, Base0 + Bit) );
        b = Gia_Obj2Lit( p, Gia_ManCi(p, Base1 + Bit) );
        if ( fSigned && i == Width - 1 )
            a ^= 1, b ^= 1;
        Equal = Gia_ManHashXor( p, a, b ) ^ 1;
        Less = Gia_ManHashOr( p, Gia_ManHashAnd(p, a ^ 1, b), Gia_ManHashAnd(p, Equal, Less) );
    }
    return Less;
}

/**Function*************************************************************

  Synopsis    [Builds the predicate excluding signed subtraction overflow.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_PredDifferenceSafe( Gia_Man_t * p, int Base0, int Base1, int Width, int fReverse )
{
    int i, a = 0, b = 0, Difference = 0, Borrow = 0;
    for ( i = 0; i < Width; i++ )
    {
        int Bit = fReverse ? Width - 1 - i : i;
        a = Gia_Obj2Lit( p, Gia_ManCi(p, Base0 + Bit) );
        b = Gia_Obj2Lit( p, Gia_ManCi(p, Base1 + Bit) );
        Difference = Gia_ManHashXor( p, Gia_ManHashXor(p, a, b), Borrow );
        Borrow = Gia_ManHashOr( p, Gia_ManHashAnd(p, a ^ 1, b),
            Gia_ManHashAnd(p, Gia_ManHashOr(p, a ^ 1, b), Borrow) );
    }
    return Gia_ManHashAnd( p, Gia_ManHashXor(p, a, b), Gia_ManHashXor(p, a, Difference) ) ^ 1;
}

/**Function*************************************************************

  Synopsis    [Adds predicates comparing extrema of register-word pairs.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Imc_PredExtrema( Gia_Man_t * p, Vec_Int_t * vWords, Vec_Int_t * vOutputs, abctime TimeStop )
{
    int i, j, k, l, Mode, a, b, c, d, Width, nAdded = 0;
    for ( i = 0; i < Vec_IntSize(vWords) && nAdded < 64; i += 2 )
        for ( j = i + 2; j < Vec_IntSize(vWords) && nAdded < 64; j += 2 )
            for ( k = 0; k < Vec_IntSize(vWords) && nAdded < 64; k += 2 )
                for ( l = k + 2; l < Vec_IntSize(vWords) && nAdded < 64; l += 2 )
                {
                    if ( Vec_IntSize(vOutputs) >= IMC_PRED_MAX - 42 || (TimeStop && Abc_Clock() >= TimeStop) )
                        return;
                    if ( i == k || i == l || j == k || j == l )
                        continue;
                    Width = Vec_IntEntry( vWords, i + 1 );
                    if ( Width != Vec_IntEntry(vWords, j + 1) || Width != Vec_IntEntry(vWords, k + 1) || Width != Vec_IntEntry(vWords, l + 1) )
                        continue;
                    a = Vec_IntEntry( vWords, i ); b = Vec_IntEntry( vWords, j );
                    c = Vec_IntEntry( vWords, k ); d = Vec_IntEntry( vWords, l );
                    for ( Mode = 0; Mode < 4; Mode++ )
                    {
                        int ab = Imc_PredLess( p, a, b, Width, Mode & 1, Mode >> 1 );
                        int cd = Imc_PredLess( p, c, d, Width, Mode & 1, Mode >> 1 );
                        int ac = Imc_PredLess( p, a, c, Width, Mode & 1, Mode >> 1 );
                        int ad = Imc_PredLess( p, a, d, Width, Mode & 1, Mode >> 1 );
                        int bc = Imc_PredLess( p, b, c, Width, Mode & 1, Mode >> 1 );
                        int bd = Imc_PredLess( p, b, d, Width, Mode & 1, Mode >> 1 );
                        Vec_IntPushUnique( vOutputs, Gia_ManHashMux(p, ab, Gia_ManHashAnd(p, ac, ad), Gia_ManHashAnd(p, bc, bd)) );
                        Vec_IntPushUnique( vOutputs, Gia_ManHashMux(p, cd, Gia_ManHashAnd(p, ad, bd), Gia_ManHashAnd(p, ac, bc)) );
                        nAdded += 2;
                    }
                }
}

// Adjacent register pairs compared by XOR/XNOR often form words. Order
// predicates are only candidate Boolean functions: their interpretation
// as words is not an assumption used to prove the property.
/**Function*************************************************************

  Synopsis    [Counts registers in one register's next-state support.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_PredStateSupport( Gia_Man_t * pGia, int Reg, abctime TimeStop )
{
    Vec_Int_t * vStack = Vec_IntAlloc( 64 );
    Gia_Obj_t * pObj;
    int Id, Count = 0;
    Gia_ManIncrementTravId( pGia );
    Vec_IntPush( vStack, Gia_ObjFaninId0p(pGia, Gia_ManRi(pGia, Reg)) );
    while ( Vec_IntSize(vStack) && (!TimeStop || Abc_Clock() < TimeStop) )
    {
        Id = Vec_IntPop( vStack );
        pObj = Gia_ManObj( pGia, Id );
        if ( Gia_ObjIsTravIdCurrent(pGia, pObj) )
            continue;
        Gia_ObjSetTravIdCurrent( pGia, pObj );
        if ( Gia_ObjIsRo(pGia, pObj) )
            Count++;
        else if ( Gia_ObjIsAnd(pObj) )
        {
            Vec_IntPush( vStack, Gia_ObjFaninId0p(pGia, pObj) );
            Vec_IntPush( vStack, Gia_ObjFaninId1p(pGia, pObj) );
        }
    }
    Vec_IntFree( vStack );
    return Count;
}

/**Function*************************************************************

  Synopsis    [Chooses whether a short control field precedes the data words.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_PredShortPrefix( Gia_Man_t * pGia, Vec_Int_t * vWords, Vec_Int_t * vRefs, int Base, int Diff, int Run, abctime TimeStop )
{
    int i, Offset, Head = 0, Tail = 0, Remainder = Run % 32;
    if ( Run <= 32 || Remainder == 0 )
        return 0;
    // Reuse boundaries already identified by another word comparison.
    for ( i = 0; i < Vec_IntSize(vWords); i += 2 )
        if ( Vec_IntEntry(vWords, i + 1) == 32 )
        {
            Offset = Vec_IntEntry( vWords, i );
            if ( Offset == Base || Offset == Base + Diff )
                return 0;
            if ( Offset == Base + Remainder || Offset == Base + Diff + Remainder )
                return 1;
        }
    // A short control field normally has a smaller state support than
    // the high bits of a word updated by arithmetic. Input support is
    // deliberately ignored: control guards can inspect wide inputs.
    for ( i = 0; i < Remainder; i++ )
    {
        Head += Imc_PredStateSupport( pGia, Base + i, TimeStop );
        Head += Imc_PredStateSupport( pGia, Base + Diff + i, TimeStop );
        Tail += Imc_PredStateSupport( pGia, Base + Run - Remainder + i, TimeStop );
        Tail += Imc_PredStateSupport( pGia, Base + Diff + Run - Remainder + i, TimeStop );
    }
    if ( Head != Tail )
        return Head < Tail;
    Head = Tail = 0;
    // Control bits usually have more structural uses than data bits.
    // This chooses a candidate grouping only, never a proof assumption.
    for ( i = 0; i < Remainder; i++ )
    {
        Head += Vec_IntEntry( vRefs, Gia_ObjId(pGia, Gia_ManRo(pGia, Base + i)) );
        Head += Vec_IntEntry( vRefs, Gia_ObjId(pGia, Gia_ManRo(pGia, Base + Diff + i)) );
        Tail += Vec_IntEntry( vRefs, Gia_ObjId(pGia, Gia_ManRo(pGia, Base + Run - Remainder + i)) );
        Tail += Vec_IntEntry( vRefs, Gia_ObjId(pGia, Gia_ManRo(pGia, Base + Diff + Run - Remainder + i)) );
    }
    return Head >= Tail;
}

/**Function*************************************************************

  Synopsis    [Checks whether a register belongs to a discovered data word.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_PredDataRegister( Vec_Int_t * vWords, int Reg )
{
    int i;
    for ( i = 0; i < Vec_IntSize(vWords); i += 2 )
        if ( Vec_IntEntry(vWords, i + 1) >= 4 && Reg >= Vec_IntEntry(vWords, i) && Reg < Vec_IntEntry(vWords, i) + Vec_IntEntry(vWords, i + 1) )
            return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Builds base and full control guards from the property cone.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Imc_PredGuards( Gia_Man_t * pGia, Gia_Man_t * pNew, Vec_Int_t * vWords, Vec_Int_t * vOutputs, Vec_Int_t * vLevel, int fLinear, abctime TimeStop )
{
    Vec_Int_t * vStack = Vec_IntAlloc( 64 );
    Vec_Str_t * vSeen = Vec_StrStart( Gia_ManObjNum(pGia) );
    Gia_Obj_t * pObj;
    int Lit, a, b, Base = 1, Full = 1;
    // Extract state-only conjuncts even when other conjuncts read inputs.
    {
        Lit = Gia_ObjFaninLit0p( pGia, Gia_ManPo(pGia, 0) );
        pObj = Gia_ManObj( pGia, Abc_Lit2Var(Lit) );
        // A delayed input-dependent property has a single output register.
        // Inspect its defining conjunction to recover state-only guards.
        if ( !Abc_LitIsCompl(Lit) && Gia_ObjIsRo(pGia, pObj) &&
             !Gia_ObjFaninC0(Gia_ObjRoToRi(pGia, pObj)) &&
             Gia_ObjIsAnd(Gia_ObjFanin0(Gia_ObjRoToRi(pGia, pObj))) )
            Lit = Gia_ObjFaninLit0p( pGia, Gia_ObjRoToRi(pGia, pObj) );
        Vec_IntPush( vStack, Lit );
    }
    while ( Vec_IntSize(vStack) && (!TimeStop || Abc_Clock() < TimeStop) )
    {
        Lit = Vec_IntPop( vStack );
        pObj = Gia_ManObj( pGia, Abc_Lit2Var(Lit) );
        if ( Gia_ObjIsAnd(pObj) && Imc_PredXorRegisters(pGia, pObj, &a, &b) )
        {
            if ( !Imc_PredDataRegister(vWords, a) || !Imc_PredDataRegister(vWords, b) )
                Full = Gia_ManHashAnd( pNew, Full, pObj->Value ^ Abc_LitIsCompl(Lit) );
            continue;
        }
        if ( !Abc_LitIsCompl(Lit) && Gia_ObjIsAnd(pObj) )
        {
            if ( Vec_StrEntry(vSeen, Abc_Lit2Var(Lit)) )
                continue;
            Vec_StrWriteEntry( vSeen, Abc_Lit2Var(Lit), 1 );
            Vec_IntPush( vStack, Gia_ObjFaninLit0p(pGia, pObj) );
            Vec_IntPush( vStack, Gia_ObjFaninLit1p(pGia, pObj) );
            continue;
        }
        if ( Vec_IntEntry(vLevel, Abc_Lit2Var(Lit)) < 0 )
            continue;
        Full = Gia_ManHashAnd( pNew, Full, pObj->Value ^ Abc_LitIsCompl(Lit) );
        if ( fLinear )
        {
            // Ordinary safety properties need guards in every control
            // location. Retain only sticky validity monitors in Base.
            if ( Gia_ObjIsRo(pGia, pObj) )
            {
                Gia_Obj_t * pDriver = Gia_ObjFanin0( Gia_ObjRoToRi(pGia, pObj) );
                if ( Gia_ObjIsAnd(pDriver) &&
                     (Gia_ObjFanin0(pDriver) == pObj || Gia_ObjFanin1(pDriver) == pObj) )
                    Base = Gia_ManHashAnd( pNew, Base, pObj->Value ^ Abc_LitIsCompl(Lit) );
            }
            continue;
        }
        if ( Gia_ObjIsRo(pGia, pObj) && !Abc_LitIsCompl(Lit) )
        {
            Gia_Obj_t * pRi = Gia_ObjRoToRi( pGia, pObj );
            Gia_Obj_t * pDriver = Gia_ObjFanin0( pRi );
            if ( Gia_ObjFaninC0(pRi) && Gia_ObjIsAnd(pDriver) &&
                 ((Gia_ObjFanin0(pDriver) == pObj && Gia_ObjFaninC0(pDriver)) ||
                  (Gia_ObjFanin1(pDriver) == pObj && Gia_ObjFaninC1(pDriver))) )
                continue;
        }
        Base = Gia_ManHashAnd( pNew, Base, pObj->Value ^ Abc_LitIsCompl(Lit) );
    }
    // The last two outputs are always the broad validity guard and the
    // property guard with data-word equalities removed, in this order.
    Vec_IntPush( vOutputs, Base );
    Vec_IntPush( vOutputs, Full );
    Vec_IntFree( vStack );
    Vec_StrFree( vSeen );
}

/**Function*************************************************************

  Synopsis    [Adds individual guard-bit predicates to the output set.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Imc_PredGuardBits( Gia_Man_t * p, Gia_Man_t * pGia, Vec_Int_t * vOutputs, int fLinear )
{
    Vec_Int_t * vStack = Vec_IntAlloc( 32 ), * vBits = Vec_IntAlloc( 16 );
    Gia_Obj_t * pObj;
    int i, k, Lit, Root, Id, Base = Vec_IntEntry(vOutputs, Vec_IntSize(vOutputs) - 2);
    int Full = Vec_IntEntry(vOutputs, Vec_IntSize(vOutputs) - 1);
    Gia_ManIncrementTravId( p );
    Vec_IntPush( vStack, Abc_Lit2Var(Full) );
    while ( Vec_IntSize(vStack) )
    {
        Id = Vec_IntPop( vStack );
        pObj = Gia_ManObj( p, Id );
        if ( Gia_ObjIsTravIdCurrent(p, pObj) )
            continue;
        Gia_ObjSetTravIdCurrent( p, pObj );
        if ( Gia_ObjIsCi(pObj) )
        {
            Vec_IntPush( vBits, Abc_Var2Lit(Id, 0) );
            if ( Vec_IntSize(vBits) > 16 )
                goto finish;
        }
        else if ( Gia_ObjIsAnd(pObj) )
        {
            Vec_IntPush( vStack, Gia_ObjFaninId0p(p, pObj) );
            Vec_IntPush( vStack, Gia_ObjFaninId1p(p, pObj) );
        }
    }
    // Expose control bits used by the weakened property guard. Internal
    // short XORs can be arithmetic subexpressions and need not be exposed.
    Vec_IntShrink( vOutputs, Vec_IntSize(vOutputs) - 2 );
    Vec_IntForEachEntry( vBits, Lit, i )
        Vec_IntPushUnique( vOutputs, Lit );
    if ( fLinear )
    {
        for ( i = k = 0; i < Vec_IntSize(vBits); i++ )
        {
            Gia_Obj_t * pRo, * pDriver;
            Lit = Vec_IntEntry( vBits, i );
            pRo = Gia_ManRo( pGia, Gia_ObjCioId(Gia_ManObj(p, Abc_Lit2Var(Lit))) );
            pDriver = Gia_ObjFanin0( Gia_ObjRoToRi(pGia, pRo) );
            if ( pDriver == pRo || Gia_ObjIsConst0(pDriver) ||
                 (Gia_ObjIsAnd(pDriver) && (Gia_ObjFanin0(pDriver) == pRo || Gia_ObjFanin1(pDriver) == pRo)) )
                continue;
            Vec_IntWriteEntry( vBits, k++, Lit );
        }
        Vec_IntShrink( vBits, k );
        if ( k >= 2 && k <= 4 )
            for ( i = 0; i < (1 << k); i++ )
            {
                int Bit;
                Root = 1;
                for ( Bit = 0; Bit < k; Bit++ )
                    Root = Gia_ManHashAnd( p, Root, Vec_IntEntry(vBits, Bit) ^ ((i >> Bit) & 1) );
                Vec_IntPushUnique( vOutputs, Root );
            }
    }
    while ( Vec_IntSize(vBits) )
        Vec_IntPushUnique( vOutputs, Vec_IntPop(vBits) );
    Vec_IntPush( vOutputs, Base );
    Vec_IntPush( vOutputs, Full );
finish:
    Vec_IntFree( vStack );
    Vec_IntFree( vBits );
}

/**Function*************************************************************

  Synopsis    [Adds word-order predicates from the discovered register groups.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Imc_PredWordOrders( Gia_Man_t * pGia, Gia_Man_t * pNew, Vec_Int_t * vOutputs, Vec_Int_t * vRefs, Vec_Int_t * vLevel, int iPredClass, abctime TimeStop )
{
    Vec_Wrd_t * vPairs = Vec_WrdAlloc( 128 );
    Vec_Int_t * vWords = Vec_IntAlloc( 16 );
    Gia_Obj_t * pObj;
    word Pair;
    int i, j, k, a, b, Width, Run, Base, Diff, Bit, Equal, fShortPrefix;
    int fLinear = iPredClass == 2;
    Gia_ManForEachAnd( pGia, pObj, i )
    {
        if ( (i & 1023) == 0 && TimeStop && Abc_Clock() >= TimeStop )
            goto finish;
        if ( Imc_PredXorRegisters(pGia, pObj, &a, &b) )
            Vec_WrdPush( vPairs, ((word)(unsigned)(b - a) << 32) | (unsigned)a );
    }
    Vec_WrdUniqify( vPairs );
    for ( i = 0; i < Vec_WrdSize(vPairs) && Vec_IntSize(vOutputs) < IMC_PRED_MAX - 34; i += Run )
    {
        if ( TimeStop && Abc_Clock() >= TimeStop )
            goto finish;
        Pair = Vec_WrdEntry( vPairs, i );
        Base = (int)(unsigned)Pair;
        Diff = (int)(Pair >> 32);
        for ( Run = 1; i + Run < Vec_WrdSize(vPairs) && Vec_WrdEntry(vPairs, i + Run) == Pair + Run; Run++ ) {}
        if ( Run < 4 )
        {
            Equal = 1;
            for ( Bit = 0; Bit < Run; Bit++ )
            {
                Equal = Gia_ManHashAnd( pNew, Equal, Gia_ManHashXor(pNew,
                    Gia_Obj2Lit(pNew, Gia_ManCi(pNew, Base + Bit)),
                    Gia_Obj2Lit(pNew, Gia_ManCi(pNew, Base + Diff + Bit))) ^ 1 );
            }
            Vec_IntPushUnique( vOutputs, Equal );
            continue;
        }
        fShortPrefix = Imc_PredShortPrefix( pGia, vWords, vRefs, Base, Diff, Run, TimeStop );
        for ( k = 0; k < Run && Vec_IntSize(vOutputs) < IMC_PRED_MAX - 34; k += Width )
        {
            Width = k == 0 && fShortPrefix ? Run % 32 : Abc_MinInt(32, Run - k);
            Imc_PredAddWord( vWords, Base + k, Width );
            Imc_PredAddWord( vWords, Base + Diff + k, Width );
            Equal = 1;
            for ( Bit = 0; Bit < Width; Bit++ )
                Equal = Gia_ManHashAnd( pNew, Equal, Gia_ManHashXor(pNew,
                    Gia_Obj2Lit(pNew, Gia_ManCi(pNew, Base + k + Bit)),
                    Gia_Obj2Lit(pNew, Gia_ManCi(pNew, Base + Diff + k + Bit))) ^ 1 );
            Vec_IntPushUnique( vOutputs, Equal );
        }
    }
    if ( fLinear )
        Imc_PredConstantWords( pGia, vWords, TimeStop );
    for ( i = 0; i < Vec_IntSize(vWords) && Vec_IntSize(vOutputs) < IMC_PRED_MAX - 42; i += 2 )
    {
        int Zero = 1, Ones = 1;
        if ( TimeStop && Abc_Clock() >= TimeStop )
            goto finish;
        Base = Vec_IntEntry( vWords, i );
        Width = Vec_IntEntry( vWords, i + 1 );
        for ( Bit = 0; Bit < Width; Bit++ )
        {
            a = Gia_Obj2Lit( pNew, Gia_ManCi(pNew, Base + Bit) );
            Zero = Gia_ManHashAnd( pNew, Zero, a ^ 1 );
            Ones = Gia_ManHashAnd( pNew, Ones, a );
            if ( Bit < 3 || Bit + 3 >= Width )
                Vec_IntPushUnique( vOutputs, a );
        }
        Vec_IntPushUnique( vOutputs, Zero );
        Vec_IntPushUnique( vOutputs, Ones );
        for ( j = 0; j < Vec_IntSize(vWords); j += 2 )
        {
            if ( TimeStop && Abc_Clock() >= TimeStop )
                goto finish;
            if ( Vec_IntSize(vOutputs) > IMC_PRED_MAX - 38 )
                break;
            if ( i != j && Vec_IntEntry(vWords, i + 1) == Vec_IntEntry(vWords, j + 1) )
                for ( k = 0; k < 4; k++ )
                    Vec_IntPushUnique( vOutputs, Imc_PredLess(pNew, Vec_IntEntry(vWords, i),
                        Vec_IntEntry(vWords, j), Vec_IntEntry(vWords, i + 1), k & 1, k >> 1) );
        }
    }
    for ( i = 0; i < Vec_IntSize(vWords) && Vec_IntSize(vOutputs) < IMC_PRED_MAX - 42; i += 2 )
        for ( j = i + 2; j < Vec_IntSize(vWords); j += 2 )
        {
            if ( TimeStop && Abc_Clock() >= TimeStop )
                goto finish;
            if ( Vec_IntSize(vOutputs) > IMC_PRED_MAX - 36 )
                break;
            if ( Vec_IntEntry(vWords, i + 1) == Vec_IntEntry(vWords, j + 1) )
                for ( k = 0; k < 2; k++ )
                    Vec_IntPushUnique( vOutputs, Gia_ManHashAnd(pNew,
                        Imc_PredDifferenceSafe(pNew, Vec_IntEntry(vWords, i), Vec_IntEntry(vWords, j), Vec_IntEntry(vWords, i + 1), k),
                        Imc_PredDifferenceSafe(pNew, Vec_IntEntry(vWords, j), Vec_IntEntry(vWords, i), Vec_IntEntry(vWords, i + 1), k)) );
        }
    Imc_PredExtrema( pNew, vWords, vOutputs, TimeStop );
    if ( fLinear )
        Imc_PredLinear( pNew, vWords, vOutputs, TimeStop );
    if ( TimeStop && Abc_Clock() >= TimeStop )
        goto finish;
    Imc_PredGuards( pGia, pNew, vWords, vOutputs, vLevel, fLinear, TimeStop );
    if ( TimeStop && Abc_Clock() >= TimeStop )
        goto finish;
    Imc_PredGuardBits( pNew, pGia, vOutputs, fLinear );
finish:
    Vec_IntFree( vWords );
    Vec_WrdFree( vPairs );
}

/**Function*************************************************************

  Synopsis    [Collects reused state predicates and state/input boundaries.]

  Description [Definitions use only register outputs. Their identical
  copies in both SAT partitions let a proof refer to compound predicates
  as shared atoms. Substitution later removes these additional variables.]

  SideEffects [Uses temporary values in the input AIG.]

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Imc_PredFind( Gia_Man_t * pGia, abctime TimeStop, int fCoarse, int iPredClass )
{
    Vec_Int_t * vLevel = Vec_IntStartFull( Gia_ManObjNum(pGia) );
    Vec_Int_t * vRefs = Vec_IntStart( Gia_ManObjNum(pGia) );
    Vec_Int_t * vSelected = Vec_IntAlloc( 128 );
    Vec_Int_t * vOutputs = Vec_IntAlloc( 256 );
    Vec_Int_t * vStack = Vec_IntAlloc( 64 );
    Vec_Str_t * vBorder = Vec_StrStart( Gia_ManObjNum(pGia) );
    Vec_Str_t * vSeen = Vec_StrStart( Gia_ManObjNum(pGia) );
    Gia_Man_t * pNew = NULL, * pResult = NULL;
    Gia_Obj_t * pObj;
    int i, Id, Id0, Id1, Level0, Level1;
    Vec_IntWriteEntry( vLevel, 0, 0 );
    Gia_ManForEachRo( pGia, pObj, i )
        Vec_IntWriteEntry( vLevel, Gia_ObjId(pGia, pObj), 0 );
    Gia_ManForEachAnd( pGia, pObj, i )
    {
        if ( (i & 1023) == 0 && TimeStop && Abc_Clock() >= TimeStop )
            goto finish;
        Id0 = Gia_ObjFaninId0p( pGia, pObj );
        Id1 = Gia_ObjFaninId1p( pGia, pObj );
        Level0 = Vec_IntEntry( vLevel, Id0 );
        Level1 = Vec_IntEntry( vLevel, Id1 );
        Vec_IntAddToEntry( vRefs, Id0, 1 );
        Vec_IntAddToEntry( vRefs, Id1, 1 );
        if ( Level0 >= 0 && Level1 >= 0 )
            Vec_IntWriteEntry( vLevel, i, Abc_MaxInt(Level0, Level1) + 1 );
        else
        {
            if ( Level0 >= 0 ) Vec_StrWriteEntry( vBorder, Id0, 1 );
            if ( Level1 >= 0 ) Vec_StrWriteEntry( vBorder, Id1, 1 );
        }
    }
    Gia_ManForEachCo( pGia, pObj, i )
        Vec_StrWriteEntry( vBorder, Gia_ObjFaninId0p(pGia, pObj), 1 );
    // Preserve state literals that guard the property and direct sticky
    // monitor feedback, without exposing every bit of data registers.
    Vec_IntPush( vStack, Gia_ObjFaninLit0p(pGia, Gia_ManPo(pGia, 0)) );
    while ( Vec_IntSize(vStack) )
    {
        int Lit = Vec_IntPop( vStack );
        pObj = Gia_ManObj( pGia, Abc_Lit2Var(Lit) );
        if ( Gia_ObjIsRo(pGia, pObj) && Vec_IntSize(vSelected) < 64 )
            Vec_IntPushUnique( vSelected, Gia_ObjId(pGia, pObj) );
        else if ( !Abc_LitIsCompl(Lit) && Gia_ObjIsAnd(pObj) && !Vec_StrEntry(vSeen, Abc_Lit2Var(Lit)) )
        {
            Vec_StrWriteEntry( vSeen, Abc_Lit2Var(Lit), 1 );
            Vec_IntPush( vStack, Gia_ObjFaninLit0p(pGia, pObj) );
            Vec_IntPush( vStack, Gia_ObjFaninLit1p(pGia, pObj) );
        }
    }
    Gia_ManForEachRo( pGia, pObj, i )
    {
        Gia_Obj_t * pDriver = Gia_ObjFanin0( Gia_ManRi(pGia, i) );
        if ( Vec_IntSize(vSelected) < 64 && (pDriver == pObj || Gia_ObjIsConst0(pDriver) ||
             (Gia_ObjIsAnd(pDriver) && (Gia_ObjFanin0(pDriver) == pObj || Gia_ObjFanin1(pDriver) == pObj))) )
            Vec_IntPushUnique( vSelected, Gia_ObjId(pGia, pObj) );
    }
    if ( fCoarse )
    {
        if ( iPredClass == 2 )
        {
            Gia_ManForEachAnd( pGia, pObj, i )
                if ( Vec_IntEntry(vRefs, i) >= 3 && Vec_IntEntry(vLevel, i) >= 1 && Vec_IntEntry(vLevel, i) <= 4 &&
                     !Gia_ObjRecognizeExor(pObj, NULL, NULL) && Vec_IntSize(vSelected) < 96 )
                    Vec_IntPushUnique( vSelected, i );
        }
        Gia_ManForEachAnd( pGia, pObj, i )
            if ( Vec_StrEntry(vBorder, i) && Vec_IntEntry(vLevel, i) >= 1 && Vec_IntEntry(vLevel, i) <= 4 &&
                 !Gia_ObjRecognizeExor(pObj, NULL, NULL) && Vec_IntSize(vSelected) < 128 )
                Vec_IntPushUnique( vSelected, i );
        Gia_ManForEachAnd( pGia, pObj, i )
            if ( Gia_ObjIsMuxType(pObj) && !Gia_ObjRecognizeExor(pObj, NULL, NULL) )
            {
                Gia_Obj_t * pThen, * pElse;
                Gia_Obj_t * pControl = Gia_ObjRecognizeMux( pObj, &pThen, &pElse );
                Id = Gia_ObjId( pGia, pControl );
                if ( Vec_IntEntry(vLevel, Id) >= 0 && Vec_IntEntry(vRefs, Id) >= 4 && Vec_IntSize(vSelected) < 128 )
                    Vec_IntPushUnique( vSelected, Id );
            }
        Id = Gia_ObjFaninId0p( pGia, Gia_ManPo(pGia, 0) );
        if ( Vec_IntEntry(vLevel, Id) >= 0 )
            Vec_IntPushUnique( vSelected, Id );
    }
    else
        for ( i = Gia_ManObjNum(pGia) - 1; i > 0 && Vec_IntSize(vSelected) < 128; i-- )
            if ( Vec_IntEntry(vLevel, i) >= 4 && (Vec_StrEntry(vBorder, i) || Vec_IntEntry(vRefs, i) > 1) )
                Vec_IntPush( vSelected, i );
    if ( Vec_IntSize(vSelected) == 0 || (TimeStop && Abc_Clock() >= TimeStop) )
        goto finish;
    pNew = Gia_ManStart( Gia_ManObjNum(pGia) );
    Gia_ManHashStart( pNew );
    Gia_ManConst0(pGia)->Value = 0;
    Gia_ManForEachRo( pGia, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachAnd( pGia, pObj, i )
        if ( Vec_IntEntry(vLevel, i) >= 0 )
            pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Vec_IntForEachEntry( vSelected, Id, i )
        Vec_IntPushUnique( vOutputs, Gia_ManObj(pGia, Id)->Value );
    Imc_PredWordOrders( pGia, pNew, vOutputs, vRefs, vLevel, iPredClass, TimeStop );
    if ( TimeStop && Abc_Clock() >= TimeStop )
        goto finish;
    if ( Vec_IntSize(vOutputs) > IMC_PRED_MAX )
    {
        int Base = Vec_IntEntry(vOutputs, Vec_IntSize(vOutputs) - 2);
        int Full = Vec_IntEntry(vOutputs, Vec_IntSize(vOutputs) - 1);
        Vec_IntShrink( vOutputs, IMC_PRED_MAX - 2 );
        Vec_IntPush( vOutputs, Base );
        Vec_IntPush( vOutputs, Full );
    }
    Vec_IntForEachEntry( vOutputs, Id, i )
        Gia_ManAppendCo( pNew, Id );
    Gia_ManHashStop( pNew );
    pResult = Gia_ManCleanup( pNew );
    Gia_ManCreateRefs( pResult );
finish:
    Gia_ManStopP( &pNew );
    Vec_IntFree( vLevel );
    Vec_IntFree( vRefs );
    Vec_IntFree( vSelected );
    Vec_IntFree( vOutputs );
    Vec_IntFree( vStack );
    Vec_StrFree( vBorder );
    Vec_StrFree( vSeen );
    return pResult;
}

/**Function*************************************************************

  Synopsis    [Discovers bounded predicates with optional first-step cofactoring.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Imc_ManFindPredicates( Gia_Man_t * pGia, abctime TimeStop, int fCoarse, int iPredClass, int fAfterInit )
{
    Gia_Man_t * pNew, * pResult;
    if ( TimeStop && Abc_Clock() >= TimeStop )
        return NULL;
    // The original circuit's class is computed once by the entry point.
    // Cofactor only when this was needed to recognize the original class.
    // Otherwise it can remove useful initialization guards and word pairs.
    pNew = fAfterInit ? Imc_PredAfterInit(pGia) : NULL;
    pResult = Imc_PredFind( pNew ? pNew : pGia, TimeStop, fCoarse, iPredClass );
    Gia_ManStopP( &pNew );
    return pResult;
}

/**Function*************************************************************

  Synopsis    [Substitutes concrete register formulas for predicate inputs.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Imc_ManExpandPredicates( Gia_Man_t * pImage, Gia_Man_t * pPred )
{
    Gia_Man_t * pNew = Gia_ManStart( Gia_ManObjNum(pImage) + Gia_ManObjNum(pPred) ), * pResult;
    Gia_Obj_t * pObj;
    int i;
    int nStateInputs = Gia_ManCiNum(pImage) - Gia_ManCoNum(pPred);
    assert( nStateInputs == 0 || nStateInputs == Gia_ManCiNum(pPred) );
    Gia_ManHashStart( pNew );
    Gia_ManConst0(pPred)->Value = 0;
    Gia_ManForEachCi( pPred, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachAnd( pPred, pObj, i )
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManConst0(pImage)->Value = 0;
    Gia_ManForEachCi( pImage, pObj, i )
        pObj->Value = i < nStateInputs ? Gia_ManCi(pPred, i)->Value : Gia_ObjFanin0Copy(Gia_ManCo(pPred, i - nStateInputs));
    Gia_ManForEachAnd( pImage, pObj, i )
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(Gia_ManPo(pImage, 0)) );
    Gia_ManHashStop( pNew );
    pResult = Gia_ManCleanup( pNew );
    Gia_ManStop( pNew );
    return pResult;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
