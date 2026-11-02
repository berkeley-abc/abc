/*
 * Small auxiliary signatures for the existing ODC constructor.
 *
 * These samples evaluate the old combinational graph with free PIs and ROs.
 * They are NOT reset-reachable CEX and confer NO proof privileges. Requiring
 * their target values strengthens construction constraints and can exclude
 * valid sequential/ODC recipes. Original care observations are retained; all
 * generated recipes still require the unchanged boundary proof and commit.
 *
 * One context belongs to one immutable discovery snapshot. Random simulation
 * is shared across roots; SAT cubes evaluate only the root/pool union TFI.
 */
#include <limits.h>

enum { CEC_TRAN_GUIDE_SAT_QUERIES = 64, CEC_TRAN_GUIDE_SAT_CONFLICTS = 100 };

typedef struct Cec_TranSigGuide_t_ Cec_TranSigGuide_t;
struct Cec_TranSigGuide_t_
{
    Gia_Man_t * pGia;
    Gia_Man_t * pSatGia;
    Cbs_Man_t * pSat;
    Cec_TranSim_t * pExtra;
    Cec_TranSim_t * pJoined;
    Vec_Int_t * vStack;
    int * pSatLits;
    int * pSeen;
    word * pValues;
    int Mode, nCapacity, Stamp;
    long long nRoots, nLow, nAliases, nChanged, nSplit, nConflicts;
    long long nRowsBefore, nRowsAfter;
    long long nSatCalls, nSatYes, nSatNo, nSatUnknown;
    abctime TimePrep, TimeGuide, TimeSat;
};

static word Cec_TranSigGuideRandom( word * pState )
{
    // Independent stream: enabling guidance does not perturb reachable sims.
    *pState += ABC_CONST(0x9e3779b97f4a7c15);
    return Cec_TranResidualMix( *pState );
}

static Cec_TranSigGuide_t * Cec_TranSigGuideStart( Gia_Man_t * pGia, int Mode )
{
    Cec_TranSigGuide_t * p;
    Gia_Obj_t * pObj;
    word State = ABC_CONST(0xf375791ab);
    int i, iObj;
    abctime clk = Abc_Clock();
    if ( !Mode )
        return NULL;
    assert( Mode >= 1 && Mode <= 3 );
    p = ABC_CALLOC( Cec_TranSigGuide_t, 1 );
    p->pGia = pGia;
    p->Mode = Mode;
    p->pExtra = Cec_TranSimStartRootBatch( pGia, 1, 1 );
    p->pSeen = ABC_CALLOC( int, Gia_ManObjNum(pGia) );
    p->pValues = ABC_CALLOC( word, Gia_ManObjNum(pGia) );
    p->vStack = Vec_IntAlloc( 64 );
    Gia_ManForEachCi( pGia, pObj, i )
        Cec_TranSimObj(p->pExtra, Gia_ObjId(pGia, pObj))[0] =
            Cec_TranSigGuideRandom( &State );
    Gia_ManForEachObj1( pGia, pObj, iObj )
    {
        word a, b;
        if ( Gia_ObjIsCi(pObj) )
            continue;
        a = Cec_TranSimLit( p->pExtra, Gia_ObjFaninLit0p(pGia, pObj), 0 );
        if ( Gia_ObjIsCo(pObj) || Gia_ObjIsBuf(pObj) )
            Cec_TranSimObj(p->pExtra, iObj)[0] = a;
        else
        {
            b = Cec_TranSimLit( p->pExtra, Gia_ObjFaninLit1p(pGia, pObj), 0 );
            Cec_TranSimObj(p->pExtra, iObj)[0] = Gia_ObjIsXor(pObj) ? a ^ b : a & b;
        }
    }
    p->TimePrep = Abc_Clock() - clk;
    return p;
}

// Build a private plain AIG without using the source objects' Value fields.
// Standard AIGs keep the same IDs/order as the experimental SAT snapshot;
// buffers and native XORs are mapped explicitly, with unchanged CI ordering.
static void Cec_TranSigGuideStartSat( Cec_TranSigGuide_t * p )
{
    Gia_Obj_t * pObj;
    int i, a, b;
    p->pSatGia = Gia_ManStart( Gia_ManObjNum(p->pGia) );
    p->pSatLits = ABC_CALLOC( int, Gia_ManObjNum(p->pGia) );
    Gia_ManForEachObj1( p->pGia, pObj, i )
    {
        if ( Gia_ObjIsCi(pObj) )
        {
            p->pSatLits[i] = Gia_ManAppendCi( p->pSatGia );
            continue;
        }
        a = Abc_LitNotCond( p->pSatLits[Gia_ObjFaninId0p(p->pGia, pObj)],
            Gia_ObjFaninC0(pObj) );
        if ( Gia_ObjIsCo(pObj) )
            p->pSatLits[i] = Gia_ManAppendCo( p->pSatGia, a );
        else if ( Gia_ObjIsBuf(pObj) )
            p->pSatLits[i] = a;
        else
        {
            b = Abc_LitNotCond( p->pSatLits[Gia_ObjFaninId1p(p->pGia, pObj)],
                Gia_ObjFaninC1(pObj) );
            p->pSatLits[i] = Gia_ObjIsXor(pObj) ?
                Gia_ManAppendXor2(p->pSatGia, a, b) : Gia_ManAppendAnd2(p->pSatGia, a, b);
        }
    }
    Gia_ManSetRegNum( p->pSatGia, Gia_ManRegNum(p->pGia) );
    assert( Gia_ManCiNum(p->pSatGia) == Gia_ManCiNum(p->pGia) );
    p->pSat = Cbs_ManAlloc( p->pSatGia );
    Cbs_ManSetConflictNum( p->pSat, CEC_TRAN_GUIDE_SAT_CONFLICTS );
}

// Iterative postorder avoids recursion proportional to the original TFI depth.
// CI values are fixed once per cube; shared cone nodes are evaluated once.
static word Cec_TranSigGuideValue( Cec_TranSigGuide_t * p, int iRoot )
{
    Gia_Obj_t * pObj;
    int iObj, iFan0, iFan1;
    word a, b;
    assert( Vec_IntSize(p->vStack) == 0 );
    Vec_IntPush( p->vStack, iRoot );
    while ( Vec_IntSize(p->vStack) )
    {
        iObj = Vec_IntEntryLast( p->vStack );
        if ( p->pSeen[iObj] == p->Stamp )
        {
            Vec_IntPop( p->vStack );
            continue;
        }
        pObj = Gia_ManObj( p->pGia, iObj );
        assert( iObj && !Gia_ObjIsCi(pObj) );
        iFan0 = Gia_ObjFaninId0p( p->pGia, pObj );
        if ( p->pSeen[iFan0] != p->Stamp )
        {
            Vec_IntPush( p->vStack, iFan0 );
            continue;
        }
        a = p->pValues[iFan0] ^ (Gia_ObjFaninC0(pObj) ? ~(word)0 : 0);
        if ( Gia_ObjIsCo(pObj) || Gia_ObjIsBuf(pObj) )
            p->pValues[iObj] = a;
        else
        {
            iFan1 = Gia_ObjFaninId1p( p->pGia, pObj );
            if ( p->pSeen[iFan1] != p->Stamp )
            {
                Vec_IntPush( p->vStack, iFan1 );
                continue;
            }
            b = p->pValues[iFan1] ^ (Gia_ObjFaninC1(pObj) ? ~(word)0 : 0);
            p->pValues[iObj] = Gia_ObjIsXor(pObj) ? a ^ b : a & b;
        }
        p->pSeen[iObj] = p->Stamp;
        Vec_IntPop( p->vStack );
    }
    return p->pValues[iRoot];
}

// Find a missing root value, not a recipe. A SAT cube denotes 64 completions
// with the same assigned CIs. UNSAT/UNKNOWN add no samples and no certificate.
static int Cec_TranSigGuideCube( Cec_TranSigGuide_t * p, int iRoot, Vec_Int_t * vPool )
{
    word Value = Cec_TranSimObj(p->pExtra, iRoot)[0];
    Gia_Obj_t * pObj;
    Vec_Int_t * vModel;
    int Lit, Status, i, iObj, Entry;
    abctime clk;
    if ( p->Mode < 2 || (Value != 0 && Value != ~(word)0) ||
         p->nSatCalls >= CEC_TRAN_GUIDE_SAT_QUERIES )
        return 0;
    if ( !p->pSat )
        Cec_TranSigGuideStartSat( p );
    Lit = Abc_LitNotCond( p->pSatLits[iRoot], Value != 0 );
    p->nSatCalls++;
    clk = Abc_Clock();
    // A mapped buffer may be constant; CBS expects a nonconstant query.
    Status = Lit < 2 ? !Lit : Cbs_ManSolveLits( p->pSat, &Lit, 1 );
    p->TimeSat += Abc_Clock() - clk;
    if ( Status != 0 )
    {
        p->nSatNo += Status == 1;
        p->nSatUnknown += Status < 0;
        return 0;
    }
    p->nSatYes++;
    p->Stamp++;
    p->pSeen[0] = p->Stamp;
    p->pValues[0] = 0;
    Gia_ManForEachCi( p->pGia, pObj, i )
    {
        iObj = Gia_ObjId( p->pGia, pObj );
        p->pSeen[iObj] = p->Stamp;
        p->pValues[iObj] = Cec_TranSimObj(p->pExtra, iObj)[0];
    }
    if ( Lit >= 2 )
    {
        vModel = Cbs_ReadModel( p->pSat );
        Vec_IntForEachEntry( vModel, Entry, i )
        {
            assert( Abc_Lit2Var(Entry) < Gia_ManCiNum(p->pGia) );
            iObj = Gia_ObjId( p->pGia, Gia_ManCi(p->pGia, Abc_Lit2Var(Entry)) );
            p->pValues[iObj] = Abc_LitIsCompl(Entry) ? 0 : ~(word)0;
        }
    }
    assert( Cec_TranSigGuideValue(p, iRoot) == ~Value );
    Vec_IntForEachEntry( vPool, iObj, i )
        Cec_TranSigGuideValue( p, iObj );
    return 1;
}

static void Cec_TranSigGuideReserve( Cec_TranSigGuide_t * p, int nSlots )
{
    if ( nSlots > p->nCapacity )
    {
        if ( p->pJoined )
            Cec_TranSimStop( p->pJoined );
        p->pJoined = Cec_TranSimStartRootBatch( p->pGia, nSlots, 1 );
        p->nCapacity = nSlots;
    }
    p->pJoined->nSlots = p->pJoined->nWords = nSlots;
    p->pJoined->nFrames = 1;
}

static int Cec_TranSigGuideAlias( Cec_TranSigGuide_t * p, Cec_TranSim_t * pOld,
    word const * pCare, int iRoot, Vec_Int_t * vPool )
{
    int i, j, iObj, fCompl;
    if ( p->Mode != 3 )
        return 0;
    Vec_IntForEachEntry( vPool, iObj, i )
        for ( fCompl = 0; fCompl < 2; fCompl++ )
        {
            word Phase = fCompl ? ~(word)0 : 0;
            for ( j = 0; j < pOld->nSlots; j++ )
                if ( (Cec_TranSimObj(pOld, iRoot)[j] ^
                      Cec_TranSimObj(pOld, iObj)[j] ^ Phase) & pCare[j] )
                    break;
            if ( j == pOld->nSlots && (Cec_TranSimObj(p->pExtra, iRoot)[0] ^
                    Cec_TranSimObj(p->pExtra, iObj)[0] ^ Phase) )
                return 1;
        }
    return 0;
}

static void Cec_TranSigGuideApply( Cec_TranSigGuide_t * p, int iRoot,
    Vec_Int_t * vPool, Cec_TranSim_t ** ppSim, word ** ppCare, int * pfConflict )
{
    Cec_TranSim_t * pOld = *ppSim;
    word * pOldCare = *ppCare, * pCare, * pPackedCare, Value;
    int i, j, iObj, fOn = 0, fOff = 0, fCube, nSlots, fConflict;
    abctime clk;
    if ( !p || *pfConflict )
        return;
    assert( pOld != p->pJoined && Vec_IntSize(vPool) > 0 );
    clk = Abc_Clock();
    p->nRoots++;
    for ( j = 0; j < pOld->nSlots; j++ )
    {
        Value = Cec_TranSimObj(pOld, iRoot)[j];
        fOn |= (Value & pOldCare[j]) != 0;
        fOff |= (~Value & pOldCare[j]) != 0;
    }
    if ( fOn && fOff )
    {
        if ( !Cec_TranSigGuideAlias(p, pOld, pOldCare, iRoot, vPool) )
            goto finish;
        p->nAliases++;
    }
    else
        p->nLow++;
    fCube = Cec_TranSigGuideCube( p, iRoot, vPool );
    assert( pOld->nSlots < INT_MAX / 64 - 2 );
    nSlots = pOld->nSlots + 1 + fCube;
    Cec_TranSigGuideReserve( p, nSlots );
    for ( i = -1; i < Vec_IntSize(vPool); i++ )
    {
        iObj = i < 0 ? iRoot : Vec_IntEntry(vPool, i);
        memcpy( Cec_TranSimObj(p->pJoined, iObj), Cec_TranSimObj(pOld, iObj),
            pOld->nSlots * sizeof(word) );
        Cec_TranSimObj(p->pJoined, iObj)[pOld->nSlots] = Cec_TranSimObj(p->pExtra, iObj)[0];
        if ( fCube )
            Cec_TranSimObj(p->pJoined, iObj)[pOld->nSlots + 1] = Cec_TranSigGuideValue(p, iObj);
    }
    memset( Cec_TranSimObj(p->pJoined, 0), 0, nSlots * sizeof(word) );
    pCare = ABC_ALLOC( word, nSlots );
    memcpy( pCare, pOldCare, pOld->nSlots * sizeof(word) );
    pCare[pOld->nSlots] = ~(word)0;
    if ( fCube )
        pCare[pOld->nSlots + 1] = ~(word)0;
    for ( j = 0; j < nSlots; j++ )
    {
        p->nRowsBefore += Abc_TtCountOnes( pCare[j] );
        Value = Cec_TranSimObj(p->pJoined, iRoot)[j];
        fOn |= (Value & pCare[j]) != 0;
        fOff |= (~Value & pCare[j]) != 0;
    }
    p->nSplit += fOn && fOff;
    pPackedCare = Cec_TranCexCompactInto( p->pJoined, pCare, NULL, NULL,
        iRoot, vPool, p->pJoined, &fConflict );
    ABC_FREE( pCare );
    for ( j = 0; j < p->pJoined->nSlots; j++ )
        p->nRowsAfter += Abc_TtCountOnes( pPackedCare[j] );
    p->nConflicts += fConflict;
    *pfConflict = fConflict;
    ABC_FREE( pOldCare );
    *ppCare = pPackedCare;
    *ppSim = p->pJoined;
    p->nChanged++;
finish:
    // Includes checks on unchanged roots; SAT time is a subset, not additive.
    p->TimeGuide += Abc_Clock() - clk;
}

static void Cec_TranSigGuideStop( Cec_TranSigGuide_t * p, int iRound, int fProfile )
{
    if ( !p )
        return;
    if ( fProfile )
        Abc_Print(1, "stran-root signature-guide: schema=1 round=%d mode=%d roots=%lld low=%lld aliases=%lld changed=%lld split=%lld conflicts=%lld rows-before=%lld rows-after=%lld slots-max=%d sat=%lld sat-yes=%lld sat-no=%lld sat-unknown=%lld prep-sec=%.6f guide-sec=%.6f sat-sec=%.6f\n",
            iRound, p->Mode, p->nRoots, p->nLow, p->nAliases, p->nChanged,
            p->nSplit, p->nConflicts, p->nRowsBefore, p->nRowsAfter, p->nCapacity,
            p->nSatCalls, p->nSatYes, p->nSatNo, p->nSatUnknown,
            Cec_TranTimeSec(p->TimePrep), Cec_TranTimeSec(p->TimeGuide), Cec_TranTimeSec(p->TimeSat));
    if ( p->pSat ) Cbs_ManStop( p->pSat );
    if ( p->pSatGia ) Gia_ManStop( p->pSatGia );
    Cec_TranSimStop( p->pExtra );
    if ( p->pJoined ) Cec_TranSimStop( p->pJoined );
    Vec_IntFree( p->vStack );
    ABC_FREE( p->pSatLits );
    ABC_FREE( p->pSeen );
    ABC_FREE( p->pValues );
    ABC_FREE( p );
}
