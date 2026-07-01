/**CFile****************************************************************

  FileName    [cecCorrIncrSim.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [Persistent event-driven incremental simulation for &scorr.]

  Description [Keeps packed CI patterns and host-AIG values across CEX batches.
  Only changed CI words are propagated through the frame-aware fanout graph.
  Classes containing truly changed values are fully regrouped.  Structural and
  measured-time budgets fall back to the standard full sweep.]

  Author      [Xiran Zhao]

  Affiliation [University of Chinese Academy of Sciences]

  Date        [Ver. 1.0. Started - Jun 2026.]

***********************************************************************/

#include "cecInt.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

static inline int Cec_SeedSimKey( Cec_SeedSim_t * p, int frame, int objId )
{
    return frame * p->nObjs + objId;
}

static inline unsigned * Cec_SeedSimVal( Cec_SeedSim_t * p, int frame, int objId )
{
    size_t Key = (size_t)Cec_SeedSimKey( p, frame, objId );
    assert( frame >= 0 && frame < p->nFrames );
    assert( objId >= 0 && objId < p->nObjs );
    return p->pVal + Key * p->nWords;
}

static inline int Cec_SeedSimPhase( Cec_SeedSim_t * p, int frame, int objId )
{
    assert( frame >= 0 && frame < p->nFrames );
    assert( objId >= 0 && objId < p->nObjs );
    return Abc_InfoHasBit( p->pPhase + (size_t)frame * p->nPhaseWords, objId );
}

static inline void Cec_SeedSimSetPhase( Cec_SeedSim_t * p,
    int frame, int objId, int Value )
{
    unsigned * pWord = p->pPhase + (size_t)frame * p->nPhaseWords + (objId >> 5);
    unsigned Bit = 1u << (objId & 31);
    *pWord = (*pWord & ~Bit) | (Value ? Bit : 0);
}

static inline int Cec_SeedSimMark( Cec_SeedSim_t * p, int frame, int objId )
{
    int Key = Cec_SeedSimKey( p, frame, objId );
    if ( p->pMark[Key] == p->nMarkVersion )
        return 0;
    p->pMark[Key] = p->nMarkVersion;
    Vec_IntPush( p->vDirtyKeys, Key );
    return 1;
}

static inline int Cec_SeedSimConeHasKey( Cec_SeedSim_t * p, int Key )
{
    return !p->fUseCone || Abc_InfoHasBit( p->pCone, Key );
}

static inline int Cec_SeedSimConeHas( Cec_SeedSim_t * p, int Frame, int ObjId )
{
    return Cec_SeedSimConeHasKey( p, Cec_SeedSimKey(p, Frame, ObjId) );
}

static void Cec_SeedSimConeMark_rec( Cec_SeedSim_t * p, int Frame, int ObjId )
{
    Gia_Obj_t * pObj;
    int Key;
    if ( Frame < 0 || Frame >= p->nFrames || ObjId < 0 || ObjId >= p->nObjs )
        return;
    Key = Cec_SeedSimKey( p, Frame, ObjId );
    if ( Abc_InfoHasBit(p->pCone, Key) )
        return;
    Abc_InfoSetBit( p->pCone, Key );
    p->nConeKeys++;
    Vec_IntPush( p->vConeQueue, Key );
    if ( ObjId == 0 )
        return;
    pObj = Gia_ManObj( p->pAig, ObjId );
    if ( Gia_ObjIsPi(p->pAig, pObj) )
        return;
    if ( Gia_ObjIsRo(p->pAig, pObj) )
    {
        Gia_Obj_t * pRi;
        int RiId;
        if ( Frame == 0 )
            return;
        pRi = Gia_ObjRoToRi( p->pAig, pObj );
        RiId = Gia_ObjId( p->pAig, pRi );
        Cec_SeedSimConeMark_rec( p, Frame - 1,
            Gia_ObjFaninId0(pRi, RiId) );
        return;
    }
    if ( Gia_ObjIsAnd(pObj) )
    {
        Cec_SeedSimConeMark_rec( p, Frame,
            Gia_ObjFaninId0(pObj, ObjId) );
        Cec_SeedSimConeMark_rec( p, Frame,
            Gia_ObjFaninId1(pObj, ObjId) );
    }
}

static void Cec_SeedSimConeCloseClasses( Cec_SeedSim_t * p )
{
    int i;
    for ( i = 0; i < Vec_IntSize(p->vConeQueue); i++ )
    {
        int Key = Vec_IntEntry( p->vConeQueue, i );
        int Frame = Key / p->nObjs;
        int ObjId = Key % p->nObjs;
        int Root, Member, RootKey;
        if ( ObjId == 0 )
            continue;
        if ( Gia_ObjIsConst(p->pAig, ObjId) )
            continue;
        if ( !Gia_ObjIsClass(p->pAig, ObjId) )
            continue;
        Root = Gia_ObjIsHead(p->pAig, ObjId) ? ObjId :
            Gia_ObjRepr(p->pAig, ObjId);
        // close each (frame, class-root) at most once: members and frames repeat
        // in the queue, and re-closing a large class is quadratic
        RootKey = Frame * p->nObjs + Root;
        if ( p->pConeClose[RootKey] == p->nConeCloseVer )
            continue;
        p->pConeClose[RootKey] = p->nConeCloseVer;
        Cec_SeedSimConeMark_rec( p, Frame, Root );
        Gia_ClassForEachObj1( p->pAig, Root, Member )
            Cec_SeedSimConeMark_rec( p, Frame, Member );
    }
}

static void Cec_SeedSimBuildFullClassCone( Cec_SeedSim_t * p )
{
    Gia_Obj_t * pObj;
    int Frame, i;
    Gia_ManForEachObj1( p->pAig, pObj, i )
    {
        if ( !Gia_ObjIsConst(p->pAig, i) && !Gia_ObjIsClass(p->pAig, i) )
            continue;
        for ( Frame = 0; Frame < p->nFrames; Frame++ )
            Cec_SeedSimConeMark_rec( p, Frame, i );
    }
    Cec_SeedSimConeCloseClasses( p );
}

void Cec_SeedSimBuildClassCone( Cec_SeedSim_t * p, Vec_Int_t * vOutputs )
{
    int i, Obj0, Obj1;
    memset( p->pCone, 0, sizeof(unsigned) * p->nConeWords );
    Vec_IntClear( p->vConeQueue );
    p->nConeKeys = 0;
    p->fUseCone = 1;
    if ( ++p->nConeCloseVer == 0 )   // fresh "class already closed" stamps
    {
        memset( p->pConeClose, 0, sizeof(int) * (size_t)p->nFrames * p->nObjs );
        p->nConeCloseVer = 1;
    }
    if ( vOutputs && Vec_IntSize(vOutputs) > 0 )
    {
        Vec_IntForEachEntryDouble( vOutputs, Obj0, Obj1, i )
        {
            Cec_SeedSimConeMark_rec( p, p->iSeedFrame, Obj0 );
            Cec_SeedSimConeMark_rec( p, p->iSeedFrame, Obj1 );
        }
        Cec_SeedSimConeCloseClasses( p );
        if ( p->nConeKeys > 0 )
            return;
    }
    Cec_SeedSimBuildFullClassCone( p );
}

static int Cec_SeedSimEvalActive( Cec_SeedSim_t * p, int Frame, int ObjId, int nLimit )
{
    Gia_Man_t * pAig = p->pAig;
    Gia_Obj_t * pObj = Gia_ManObj( pAig, ObjId );
    int Key = Cec_SeedSimKey( p, Frame, ObjId );
    unsigned * pRes = Cec_SeedSimVal( p, Frame, ObjId );
    int Phase, w;
    if ( p->pEvalMark[Key] == p->nEvalVersion )
        return 1;
    if ( ++p->nEvalKeys > nLimit )
        return 0;
    p->pEvalMark[Key] = p->nEvalVersion;
    Phase = Cec_SeedSimPhase( p, Frame, ObjId );
    pRes[0] = (pRes[0] & ~(unsigned)1) | Phase;
    for ( w = 0; w < p->nWords; w++ )
        if ( p->pActiveMask[w] )
            pRes[w] = Phase ? ~(unsigned)0 : 0;
    if ( ObjId == 0 )
        return 1;
    if ( Gia_ObjIsPi(pAig, pObj) )
    {
        int iPi = Gia_ObjCioId( pObj );
        unsigned * pInput = (unsigned *)Vec_PtrEntry( p->vBatchInfo,
            p->nRegs + Frame * p->nPis + iPi );
        for ( w = 0; w < p->nWords; w++ )
            if ( p->pActiveMask[w] )
                pRes[w] = (pRes[w] & ~p->pActiveMask[w]) |
                          (pInput[w] & p->pActiveMask[w]);
        return 1;
    }
    if ( Gia_ObjIsRo(pAig, pObj) )
    {
        if ( Frame == 0 )
        {
            int iReg = Gia_ObjCioId(pObj) - p->nPis;
            unsigned * pInput = (unsigned *)Vec_PtrEntry( p->vBatchInfo, iReg );
            for ( w = 0; w < p->nWords; w++ )
                if ( p->pActiveMask[w] )
                    pRes[w] = (pRes[w] & ~p->pActiveMask[w]) |
                              (pInput[w] & p->pActiveMask[w]);
        }
        else
        {
            Gia_Obj_t * pRi = Gia_ObjRoToRi( pAig, pObj );
            int RiId = Gia_ObjId( pAig, pRi );
            int DrvId = Gia_ObjFaninId0( pRi, RiId );
            unsigned * pDrv;
            if ( !Cec_SeedSimEvalActive(p, Frame - 1, DrvId, nLimit) )
                return 0;
            pDrv = Cec_SeedSimVal( p, Frame - 1, DrvId );
            for ( w = 0; w < p->nWords; w++ )
            {
                unsigned Value = Gia_ObjFaninC0(pRi) ? ~pDrv[w] : pDrv[w];
                if ( p->pActiveMask[w] )
                    pRes[w] = (pRes[w] & ~p->pActiveMask[w]) |
                              (Value & p->pActiveMask[w]);
            }
        }
        return 1;
    }
    if ( Gia_ObjIsAnd(pObj) )
    {
        int Fan0 = Gia_ObjFaninId0( pObj, ObjId );
        int Fan1 = Gia_ObjFaninId1( pObj, ObjId );
        unsigned * pVal0, * pVal1;
        if ( !Cec_SeedSimEvalActive(p, Frame, Fan0, nLimit) ||
             !Cec_SeedSimEvalActive(p, Frame, Fan1, nLimit) )
            return 0;
        pVal0 = Cec_SeedSimVal( p, Frame, Fan0 );
        pVal1 = Cec_SeedSimVal( p, Frame, Fan1 );
        for ( w = 0; w < p->nWords; w++ )
        {
            unsigned Val0 = Gia_ObjFaninC0(pObj) ? ~pVal0[w] : pVal0[w];
            unsigned Val1 = Gia_ObjFaninC1(pObj) ? ~pVal1[w] : pVal1[w];
            unsigned Value = Val0 & Val1;
            if ( p->pActiveMask[w] )
                pRes[w] = (pRes[w] & ~p->pActiveMask[w]) |
                          (Value & p->pActiveMask[w]);
        }
        return 1;
    }
    return 0;
}

Cec_SeedSim_t * Cec_SeedSimAlloc( Gia_Man_t * pAig, int nFrames, int iSeedFrame, int nWords )
{
    Cec_SeedSim_t * p = ABC_CALLOC( Cec_SeedSim_t, 1 );
    size_t nKeys = (size_t)nFrames * Gia_ManObjNum(pAig);
    int w;
    assert( iSeedFrame >= 0 && iSeedFrame < nFrames );
    p->pAig    = pAig;
    p->nFrames = nFrames;
    p->iSeedFrame = iSeedFrame;
    p->nObjs   = Gia_ManObjNum( pAig );
    p->nPis    = Gia_ManPiNum( pAig );
    p->nRegs   = Gia_ManRegNum( pAig );
    p->nWords  = nWords;
    p->nPhaseWords = Abc_BitWordNum( p->nObjs );
    p->nEventMaskWords = Abc_BitWordNum( nWords );
    p->nConeWords = Abc_BitWordNum( (int)nKeys );
    p->pVal         = ABC_CALLOC( unsigned, nKeys * nWords );
    p->pPhase       = ABC_CALLOC( unsigned, (size_t)nFrames * p->nPhaseWords );
    p->pActiveMask  = ABC_CALLOC( unsigned, nWords );
    p->pCexMask     = ABC_CALLOC( unsigned, nWords );
    p->pFoundMask   = ABC_CALLOC( unsigned, nWords );
    p->pDiffMask    = ABC_CALLOC( unsigned, nWords );
    p->pTempMask    = ABC_CALLOC( unsigned, nWords );
    p->pMark        = ABC_CALLOC( int, nKeys );
    p->pSpecMark    = ABC_CALLOC( int, nKeys );
    p->pDiagMark    = ABC_CALLOC( int, nKeys );
    p->pSplitMark   = ABC_CALLOC( int, nKeys );
    p->pProcessMark = ABC_CALLOC( int, nKeys );
    p->pEvalMark    = ABC_CALLOC( int, nKeys );
    p->pEventWords  = ABC_CALLOC( unsigned, nKeys * p->nEventMaskWords );
    p->pCone        = ABC_CALLOC( unsigned, p->nConeWords );
    p->pConeClose   = ABC_CALLOC( int, nKeys );
    p->pRootMark    = ABC_CALLOC( int, p->nObjs );
    p->pTxnMark     = ABC_CALLOC( int, p->nObjs );
    p->pInputVarMark = ABC_CALLOC( int, p->nRegs + p->nPis * p->nFrames );
    p->vDiagPairs   = Vec_IntAlloc( 192 );
    p->vSpecKeys    = Vec_IntAlloc( 1024 );
    p->vSpecMasks   = Vec_IntAlloc( 1024 * nWords );
    p->vDiagKeys    = Vec_IntAlloc( 1024 );
    p->vDiagRoots   = Vec_IntAlloc( 1024 );
    p->vDiagMasks   = Vec_IntAlloc( 1024 * nWords );
    p->vSplitKeys   = Vec_IntAlloc( 1024 );
    p->vDirtyKeys   = Vec_IntAlloc( 4096 );
    p->vWaveKeys    = Vec_IntAlloc( 4096 );
    p->vQueue       = Vec_IntAlloc( 4096 );
    p->vDirtyRoots  = Vec_IntAlloc( 1024 );
    p->vConstRefined = Vec_IntAlloc( 64 );
    p->vClassAll    = Vec_IntAlloc( 64 );
    p->vClassOld    = Vec_IntAlloc( 64 );
    p->vClassNew    = Vec_IntAlloc( 64 );
    p->vTxnObjs     = Vec_IntAlloc( 1024 );
    p->vTxnReprs    = Vec_IntAlloc( 1024 );
    p->vTxnNexts    = Vec_IntAlloc( 1024 );
    p->vPackTouched = Vec_IntAlloc( 1024 );
    p->vInputUndo   = Vec_IntAlloc( 2048 );
    p->vChangedInputs = Vec_IntAlloc( 1024 );
    p->vValueUndo   = Vec_IntAlloc( 4096 );
    p->vChangedValues = Vec_IntAlloc( 4096 );
    p->vConeQueue   = Vec_IntAlloc( 4096 );
    p->pPhase0      = ABC_ALLOC( unsigned, nWords );
    p->pPhase1      = ABC_ALLOC( unsigned, nWords );
    for ( w = 0; w < nWords; w++ )
    {
        p->pPhase0[w] = 0;
        p->pPhase1[w] = ~(unsigned)0;
    }
    if ( pAig->vFanout == NULL )
    {
        Gia_ManStaticFanoutStart( pAig );
        p->fOwnsFanout = 1;
    }
    return p;
}

void Cec_SeedSimFree( Cec_SeedSim_t * p )
{
    if ( p == NULL )
        return;
    if ( p->fOwnsFanout )
        Gia_ManStaticFanoutStop( p->pAig );
    Vec_IntFreeP( &p->vDiagPairs );
    Vec_IntFreeP( &p->vSpecKeys );
    Vec_IntFreeP( &p->vSpecMasks );
    Vec_IntFreeP( &p->vDiagKeys );
    Vec_IntFreeP( &p->vDiagRoots );
    Vec_IntFreeP( &p->vDiagMasks );
    Vec_IntFreeP( &p->vSplitKeys );
    Vec_IntFreeP( &p->vDirtyKeys );
    Vec_IntFreeP( &p->vWaveKeys );
    Vec_IntFreeP( &p->vQueue );
    Vec_IntFreeP( &p->vDirtyRoots );
    Vec_IntFreeP( &p->vConstRefined );
    Vec_IntFreeP( &p->vClassAll );
    Vec_IntFreeP( &p->vClassOld );
    Vec_IntFreeP( &p->vClassNew );
    Vec_IntFreeP( &p->vTxnObjs );
    Vec_IntFreeP( &p->vTxnReprs );
    Vec_IntFreeP( &p->vTxnNexts );
    Vec_IntFreeP( &p->vPackTouched );
    Vec_IntFreeP( &p->vInputUndo );
    Vec_IntFreeP( &p->vChangedInputs );
    Vec_IntFreeP( &p->vValueUndo );
    Vec_IntFreeP( &p->vChangedValues );
    Vec_IntFreeP( &p->vConeQueue );
    Vec_PtrFreeP( &p->vSimInfo );
    ABC_FREE( p->pVal );
    ABC_FREE( p->pPhase );
    ABC_FREE( p->pActiveMask );
    ABC_FREE( p->pCexMask );
    ABC_FREE( p->pFoundMask );
    ABC_FREE( p->pDiffMask );
    ABC_FREE( p->pTempMask );
    ABC_FREE( p->pMark );
    ABC_FREE( p->pSpecMark );
    ABC_FREE( p->pDiagMark );
    ABC_FREE( p->pSplitMark );
    ABC_FREE( p->pProcessMark );
    ABC_FREE( p->pEvalMark );
    ABC_FREE( p->pEventWords );
    ABC_FREE( p->pCone );
    ABC_FREE( p->pConeClose );
    ABC_FREE( p->pRootMark );
    ABC_FREE( p->pTxnMark );
    ABC_FREE( p->pPackPres );
    ABC_FREE( p->pInputUndoMark );
    ABC_FREE( p->pInputVarMark );
    ABC_FREE( p->pPhase0 );
    ABC_FREE( p->pPhase1 );
    ABC_FREE( p );
}

static void Cec_SeedSimReset( Cec_SeedSim_t * p )
{
    size_t nKeys = (size_t)p->nFrames * p->nObjs;
    int i, Key;
    Vec_IntForEachEntry( p->vSpecKeys, Key, i )
        p->pSpecMark[Key] = 0;
    Vec_IntForEachEntry( p->vDiagKeys, Key, i )
        p->pDiagMark[Key] = 0;
    Vec_IntClear( p->vDiagPairs );
    Vec_IntClear( p->vSpecKeys );
    Vec_IntClear( p->vSpecMasks );
    Vec_IntClear( p->vDiagKeys );
    Vec_IntClear( p->vDiagRoots );
    Vec_IntClear( p->vDiagMasks );
    Vec_IntClear( p->vSplitKeys );
    Vec_IntClear( p->vDirtyKeys );
    Vec_IntClear( p->vWaveKeys );
    Vec_IntClear( p->vQueue );
    for ( i = 0; i < p->nWords; i++ )
        p->pActiveMask[i] = ~(unsigned)0;
    p->pActiveMask[0] &= ~(unsigned)1;
    memset( p->pCexMask, 0, sizeof(unsigned) * p->nWords );
    memset( p->pFoundMask, 0, sizeof(unsigned) * p->nWords );
    p->vBatchInfo = NULL;
    p->nSpecKeys = 0;
    p->nEvalKeys = 0;
    p->nMarkVersion++;
    p->nSplitVersion++;
    p->nProcessVersion++;
    p->nEvalVersion++;
    if ( p->nMarkVersion == 0 )
    {
        memset( p->pMark, 0, sizeof(int) * nKeys );
        p->nMarkVersion = 1;
    }
    if ( p->nSplitVersion == 0 )
    {
        memset( p->pSplitMark, 0, sizeof(int) * nKeys );
        p->nSplitVersion = 1;
    }
    if ( p->nProcessVersion == 0 )
    {
        memset( p->pProcessMark, 0, sizeof(int) * nKeys );
        p->nProcessVersion = 1;
    }
    if ( p->nEvalVersion == 0 )
    {
        memset( p->pEvalMark, 0, sizeof(int) * nKeys );
        p->nEvalVersion = 1;
    }
}

static int Cec_SeedSimAddDiagKey( Cec_SeedSim_t * p, int Frame, int ObjId )
{
    int Key, iDiag, Repr, w;
    if ( ObjId <= 0 || ObjId >= p->nObjs )
        return ObjId == 0;
    Key = Cec_SeedSimKey( p, Frame, ObjId );
    iDiag = p->pDiagMark[Key] - 1;
    if ( iDiag < 0 )
    {
        Repr = Gia_ObjRepr( p->pAig, ObjId );
        iDiag = Vec_IntSize( p->vDiagKeys );
        p->pDiagMark[Key] = iDiag + 1;
        Vec_IntPush( p->vDiagKeys, Key );
        Vec_IntPush( p->vDiagRoots, Repr == 0 ? 0 :
            (Gia_ObjIsHead(p->pAig, ObjId) ? ObjId : Repr) );
        for ( w = 0; w < p->nWords; w++ )
            Vec_IntPush( p->vDiagMasks, 0 );
    }
    return 1;
}

static int Cec_SeedSimAddDiagBit( Cec_SeedSim_t * p, int Frame, int ObjId, int iBit )
{
    int Key, iDiag;
    unsigned * pMask;
    if ( !Cec_SeedSimAddDiagKey(p, Frame, ObjId) )
        return 0;
    if ( ObjId == 0 )
        return 1;
    Key = Cec_SeedSimKey( p, Frame, ObjId );
    iDiag = p->pDiagMark[Key] - 1;
    assert( iDiag >= 0 );
    pMask = (unsigned *)Vec_IntArray(p->vDiagMasks) + (size_t)iDiag * p->nWords;
    Abc_InfoSetBit( pMask, iBit );
    return 1;
}

static int Cec_SeedSimCollectSpecBit( Cec_SeedSim_t * p, int Frame, int ObjId, int iBit, int nLimit );

static int Cec_SeedSimCollectRealBit( Cec_SeedSim_t * p, int Frame, int ObjId, int iBit, int nLimit )
{
    Gia_Obj_t * pObj;
    if ( ObjId < 0 || ObjId >= p->nObjs || Frame < 0 || Frame >= p->nFrames )
        return 0;
    if ( ObjId == 0 )
        return 1;
    pObj = Gia_ManObj( p->pAig, ObjId );
    if ( Gia_ObjIsAnd(pObj) )
    {
        return Cec_SeedSimCollectSpecBit( p, Frame, Gia_ObjFaninId0(pObj, ObjId), iBit, nLimit ) &&
               Cec_SeedSimCollectSpecBit( p, Frame, Gia_ObjFaninId1(pObj, ObjId), iBit, nLimit );
    }
    if ( Gia_ObjIsRo(p->pAig, pObj) && Frame > 0 )
    {
        Gia_Obj_t * pRi = Gia_ObjRoToRi( p->pAig, pObj );
        int RiId = Gia_ObjId( p->pAig, pRi );
        return Cec_SeedSimCollectSpecBit( p, Frame - 1,
            Gia_ObjFaninId0(pRi, RiId), iBit, nLimit );
    }
    return 1;
}

static int Cec_SeedSimCollectSpecBit( Cec_SeedSim_t * p, int Frame, int ObjId, int iBit, int nLimit )
{
    int Key, Repr, iSpec, iWord = iBit >> 5, w;
    unsigned Bit = (unsigned)1 << (iBit & 31);
    unsigned * pMask;
    if ( ObjId < 0 || ObjId >= p->nObjs || Frame < 0 || Frame >= p->nFrames )
        return 0;
    if ( ObjId == 0 )
        return 1;
    Key = Cec_SeedSimKey( p, Frame, ObjId );
    iSpec = p->pSpecMark[Key] - 1;
    if ( iSpec < 0 )
    {
        if ( ++p->nSpecKeys > nLimit )
            return 0;
        iSpec = Vec_IntSize( p->vSpecKeys );
        p->pSpecMark[Key] = iSpec + 1;
        Vec_IntPush( p->vSpecKeys, Key );
        for ( w = 0; w < p->nWords; w++ )
            Vec_IntPush( p->vSpecMasks, 0 );
    }
    pMask = (unsigned *)Vec_IntArray(p->vSpecMasks) + (size_t)iSpec * p->nWords;
    if ( pMask[iWord] & Bit )
        return 1;
    pMask[iWord] |= Bit;
    Repr = Gia_ObjRepr( p->pAig, ObjId );
    if ( Repr != GIA_VOID )
    {
        if ( !Cec_SeedSimAddDiagBit(p, Frame, ObjId, iBit) )
            return 0;
        return Repr == 0 ||
               Cec_SeedSimCollectSpecBit( p, Frame, Repr, iBit, nLimit );
    }
    return Cec_SeedSimCollectRealBit( p, Frame, ObjId, iBit, nLimit );
}

static int Cec_SeedSimCollectDiagnosis( Cec_SeedSim_t * p, Vec_Int_t * vOutputs, Vec_Int_t * vOutBits, int nLimit )
{
    int i, Out, iBit;
    if ( vOutputs == NULL || vOutBits == NULL )
        return 0;
    Vec_IntForEachEntryDouble( vOutBits, Out, iBit, i )
    {
        int Obj0, Obj1;
        if ( Out < 0 || 2*Out + 1 >= Vec_IntSize(vOutputs) )
            return 0;
        Obj0 = Vec_IntEntry( vOutputs, 2*Out );
        Obj1 = Vec_IntEntry( vOutputs, 2*Out + 1 );
        Abc_InfoSetBit( p->pCexMask, iBit );
        Vec_IntPush( p->vDiagPairs, Obj0 );
        Vec_IntPush( p->vDiagPairs, Obj1 );
        Vec_IntPush( p->vDiagPairs, iBit );
        if ( !Cec_SeedSimAddDiagKey(p, p->iSeedFrame, Obj0) ||
             !Cec_SeedSimAddDiagKey(p, p->iSeedFrame, Obj1) )
            return 0;
        if ( !Cec_SeedSimCollectRealBit(p, p->iSeedFrame, Obj0, iBit, nLimit) ||
             !Cec_SeedSimCollectRealBit(p, p->iSeedFrame, Obj1, iBit, nLimit) )
            return 0;
    }
    return Vec_IntSize(vOutBits) > 0;
}

static int Cec_SeedSimCollectShapeSpec( Cec_SeedSim_t * p, int Frame, int ObjId, int nLimit );

static int Cec_SeedSimCollectShapeReal( Cec_SeedSim_t * p, int Frame, int ObjId, int nLimit )
{
    Gia_Obj_t * pObj;
    int Key;
    if ( ObjId < 0 || ObjId >= p->nObjs || Frame < 0 || Frame >= p->nFrames )
        return 0;
    if ( ObjId == 0 )
        return 1;
    Key = Cec_SeedSimKey( p, Frame, ObjId );
    if ( p->pProcessMark[Key] == p->nProcessVersion )
        return 1;
    p->pProcessMark[Key] = p->nProcessVersion;
    Vec_IntPush( p->vDirtyKeys, Key );
    if ( Vec_IntSize(p->vDirtyKeys) > nLimit )
        return 0;
    pObj = Gia_ManObj( p->pAig, ObjId );
    if ( Gia_ObjIsAnd(pObj) )
        return Cec_SeedSimCollectShapeSpec( p, Frame, Gia_ObjFaninId0(pObj, ObjId), nLimit ) &&
               Cec_SeedSimCollectShapeSpec( p, Frame, Gia_ObjFaninId1(pObj, ObjId), nLimit );
    if ( Gia_ObjIsRo(p->pAig, pObj) && Frame > 0 )
    {
        Gia_Obj_t * pRi = Gia_ObjRoToRi( p->pAig, pObj );
        int RiId = Gia_ObjId( p->pAig, pRi );
        return Cec_SeedSimCollectShapeSpec( p, Frame - 1,
            Gia_ObjFaninId0(pRi, RiId), nLimit );
    }
    return 1;
}

static int Cec_SeedSimCollectShapeSpec( Cec_SeedSim_t * p, int Frame, int ObjId, int nLimit )
{
    Gia_Obj_t * pObj;
    int Repr;
    if ( ObjId < 0 || ObjId >= p->nObjs || Frame < 0 || Frame >= p->nFrames )
        return 0;
    if ( ObjId == 0 || !Cec_SeedSimMark(p, Frame, ObjId) )
        return 1;
    if ( Vec_IntSize(p->vDirtyKeys) > nLimit )
        return 0;
    Repr = Gia_ObjRepr( p->pAig, ObjId );
    if ( Repr != GIA_VOID )
        return Repr == 0 || Cec_SeedSimCollectShapeSpec( p, Frame, Repr, nLimit );
    pObj = Gia_ManObj( p->pAig, ObjId );
    if ( Gia_ObjIsAnd(pObj) )
        return Cec_SeedSimCollectShapeSpec( p, Frame, Gia_ObjFaninId0(pObj, ObjId), nLimit ) &&
               Cec_SeedSimCollectShapeSpec( p, Frame, Gia_ObjFaninId1(pObj, ObjId), nLimit );
    if ( Gia_ObjIsRo(p->pAig, pObj) && Frame > 0 )
    {
        Gia_Obj_t * pRi = Gia_ObjRoToRi( p->pAig, pObj );
        int RiId = Gia_ObjId( p->pAig, pRi );
        return Cec_SeedSimCollectShapeSpec( p, Frame - 1,
            Gia_ObjFaninId0(pRi, RiId), nLimit );
    }
    return 1;
}

static int Cec_SeedSimDiagnosisShapeSmall( Cec_SeedSim_t * p,
    Vec_Int_t * vOutputs, Vec_Int_t * vOutBits, int nLimit )
{
    int i, Out, iBit;
    Vec_IntForEachEntryDouble( vOutBits, Out, iBit, i )
    {
        int Obj0, Obj1;
        (void)iBit;
        if ( Out < 0 || 2*Out + 1 >= Vec_IntSize(vOutputs) )
            return 0;
        Obj0 = Vec_IntEntry( vOutputs, 2*Out );
        Obj1 = Vec_IntEntry( vOutputs, 2*Out + 1 );
        if ( !Cec_SeedSimCollectShapeReal(p, p->iSeedFrame, Obj0, nLimit) ||
             !Cec_SeedSimCollectShapeReal(p, p->iSeedFrame, Obj1, nLimit) )
            return 0;
    }
    return 1;
}

static void Cec_SeedSimRestartTfoMarks( Cec_SeedSim_t * p )
{
    size_t nKeys = (size_t)p->nFrames * p->nObjs;
    Vec_IntClear( p->vDirtyKeys );
    Vec_IntClear( p->vQueue );
    p->nMarkVersion++;
    p->nProcessVersion++;
    if ( p->nMarkVersion == 0 )
    {
        memset( p->pMark, 0, sizeof(int) * nKeys );
        p->nMarkVersion = 1;
    }
    if ( p->nProcessVersion == 0 )
    {
        memset( p->pProcessMark, 0, sizeof(int) * nKeys );
        p->nProcessVersion = 1;
    }
}

static void Cec_SeedSimUseCexLanes( Cec_SeedSim_t * p )
{
    int w;
    for ( w = 0; w < p->nWords; w++ )
        p->pActiveMask[w] = p->pCexMask[w] ? ~(unsigned)0 : 0;
    p->pActiveMask[0] &= ~(unsigned)1;
}

static void Cec_SeedSimUsePackedLanes( Cec_SeedSim_t * p )
{
    int w;
    if ( p->nEvalKeys > p->nMaxDirty )
        p->nMaxDirty = p->nEvalKeys;
    for ( w = 0; w < p->nWords; w++ )
        p->pActiveMask[w] = ~(unsigned)0;
    p->pActiveMask[0] &= ~(unsigned)1;
    p->nEvalKeys = 0;
    p->nEvalVersion++;
    if ( p->nEvalVersion == 0 )
    {
        size_t nKeys = (size_t)p->nFrames * p->nObjs;
        memset( p->pEvalMark, 0, sizeof(int) * nKeys );
        p->nEvalVersion = 1;
    }
}

static int Cec_SeedSimComputeTfo( Cec_SeedSim_t * p, int nLimit )
{
    if ( Vec_IntSize(p->vDirtyKeys) > nLimit )
        return 0;
    while ( Vec_IntSize(p->vQueue) > 0 )
    {
        int Key = Vec_IntPop( p->vQueue );
        int Frame = Key / p->nObjs;
        int ObjId = Key % p->nObjs;
        int FanId, i;
        Gia_ObjForEachFanoutStaticId( p->pAig, ObjId, FanId, i )
        {
            Gia_Obj_t * pFan = Gia_ManObj( p->pAig, FanId );
            if ( Gia_ObjIsAnd(pFan) )
            {
                if ( Cec_SeedSimMark( p, Frame, FanId ) )
                {
                    if ( Vec_IntSize(p->vDirtyKeys) > nLimit )
                        return 0;
                    Vec_IntPush( p->vQueue, Cec_SeedSimKey(p, Frame, FanId) );
                }
            }
            else if ( Gia_ObjIsRi(p->pAig, pFan) && Frame + 1 < p->nFrames )
            {
                int RoId = Gia_ObjRiToRoId( p->pAig, FanId );
                if ( Cec_SeedSimMark( p, Frame + 1, RoId ) )
                {
                    if ( Vec_IntSize(p->vDirtyKeys) > nLimit )
                        return 0;
                    Vec_IntPush( p->vQueue, Cec_SeedSimKey(p, Frame + 1, RoId) );
                }
            }
        }
    }
    return 1;
}

static void Cec_SeedSimStartRootSet( Cec_SeedSim_t * p )
{
    p->nRootVersion++;
    if ( p->nRootVersion == 0 )
    {
        memset( p->pRootMark, 0, sizeof(int) * p->nObjs );
        p->nRootVersion = 1;
    }
    Vec_IntClear( p->vDirtyRoots );
    Vec_IntClear( p->vConstRefined );
}

static void Cec_SeedSimAddRoot( Cec_SeedSim_t * p, int ObjId )
{
    Gia_Man_t * pAig = p->pAig;
    int iRoot;
    if ( Gia_ObjIsConst(pAig, ObjId) )
    {
        iRoot = ObjId;
        if ( p->pRootMark[iRoot] != p->nRootVersion )
        {
            p->pRootMark[iRoot] = p->nRootVersion;
            Vec_IntPush( p->vConstRefined, iRoot );
        }
    }
    else if ( Gia_ObjIsClass(pAig, ObjId) )
    {
        iRoot = Gia_ObjIsHead(pAig, ObjId) ? ObjId : Gia_ObjRepr(pAig, ObjId);
        if ( p->pRootMark[iRoot] != p->nRootVersion )
        {
            p->pRootMark[iRoot] = p->nRootVersion;
            Vec_IntPush( p->vDirtyRoots, iRoot );
        }
    }
    else
        return;
}

static int Cec_SeedSimCollectEvalShape( Cec_SeedSim_t * p,
    int Frame, int ObjId, int nLimit )
{
    Gia_Obj_t * pObj;
    int Key;
    if ( ObjId < 0 || ObjId >= p->nObjs || Frame < 0 || Frame >= p->nFrames )
        return 0;
    Key = Cec_SeedSimKey( p, Frame, ObjId );
    if ( p->pProcessMark[Key] == p->nProcessVersion )
        return 1;
    p->pProcessMark[Key] = p->nProcessVersion;
    Vec_IntPush( p->vDirtyKeys, Key );
    if ( Vec_IntSize(p->vDirtyKeys) > nLimit )
        return 0;
    if ( ObjId == 0 )
        return 1;
    pObj = Gia_ManObj( p->pAig, ObjId );
    if ( Gia_ObjIsAnd(pObj) )
        return Cec_SeedSimCollectEvalShape( p, Frame,
                   Gia_ObjFaninId0(pObj, ObjId), nLimit ) &&
               Cec_SeedSimCollectEvalShape( p, Frame,
                   Gia_ObjFaninId1(pObj, ObjId), nLimit );
    if ( Gia_ObjIsRo(p->pAig, pObj) && Frame > 0 )
    {
        Gia_Obj_t * pRi = Gia_ObjRoToRi( p->pAig, pObj );
        int RiId = Gia_ObjId( p->pAig, pRi );
        return Cec_SeedSimCollectEvalShape( p, Frame - 1,
            Gia_ObjFaninId0(pRi, RiId), nLimit );
    }
    return 1;
}

static int Cec_SeedSimDiagnosisEvalShapeSmall( Cec_SeedSim_t * p,
    Vec_Int_t * vKeys, int nLimit )
{
    int iLo = 0;
    Vec_IntSort( vKeys, 0 );
    while ( iLo < Vec_IntSize(vKeys) )
    {
        int Frame = Vec_IntEntry(vKeys, iLo) / p->nObjs;
        int iHi = iLo, i, Key, ObjId, Ent;
        while ( iHi < Vec_IntSize(vKeys) &&
                Vec_IntEntry(vKeys, iHi) / p->nObjs == Frame )
            iHi++;
        Cec_SeedSimStartRootSet( p );
        for ( i = iLo; i < iHi; i++ )
        {
            Key = Vec_IntEntry( vKeys, i );
            ObjId = Key % p->nObjs;
            if ( Gia_ObjIsConst(p->pAig, ObjId) ||
                 Gia_ObjIsClass(p->pAig, ObjId) )
                Cec_SeedSimAddRoot( p, ObjId );
            else if ( !Cec_SeedSimCollectEvalShape(p, Frame, ObjId, nLimit) )
                return 0;
        }
        Vec_IntForEachEntry( p->vDirtyRoots, Ent, i )
        {
            int Member;
            if ( !Cec_SeedSimCollectEvalShape(p, Frame, Ent, nLimit) )
                return 0;
            Gia_ClassForEachObj1( p->pAig, Ent, Member )
                if ( !Cec_SeedSimCollectEvalShape(p, Frame, Member, nLimit) )
                    return 0;
        }
        Vec_IntForEachEntry( p->vConstRefined, Ent, i )
            if ( !Cec_SeedSimCollectEvalShape(p, Frame, Ent, nLimit) )
                return 0;
        iLo = iHi;
    }
    return 1;
}

static void Cec_SeedSimDiffMask( Cec_SeedSim_t * p, unsigned * pValue0,
    unsigned * pValue1, unsigned * pMask, unsigned * pDiff )
{
    int fCompl = (pValue0[0] & 1) != (pValue1[0] & 1);
    int w;
    for ( w = 0; w < p->nWords; w++ )
        pDiff[w] = (pValue0[w] ^ (fCompl ? ~pValue1[w] : pValue1[w])) & pMask[w];
}

static int Cec_SeedSimMaskIsZero( unsigned * pMask, int nWords )
{
    int w;
    for ( w = 0; w < nWords; w++ )
        if ( pMask[w] )
            return 0;
    return 1;
}

static inline unsigned Cec_SeedSimRefineMaskWord( Cec_SeedSim_t * p, int w )
{
    return p->pRefineMask[w] | (w == 0);
}

static int Cec_SeedSimCompareRefine( Cec_SeedSim_t * p,
    unsigned * pValue0, unsigned * pValue1 )
{
    int fCompl = (pValue0[0] & 1) != (pValue1[0] & 1);
    int w;
    if ( fCompl )
    {
        for ( w = 0; w < p->nWords; w++ )
            if ( (pValue0[w] ^ ~pValue1[w]) & Cec_SeedSimRefineMaskWord(p, w) )
                return 0;
    }
    else
    {
        for ( w = 0; w < p->nWords; w++ )
            if ( (pValue0[w] ^ pValue1[w]) & Cec_SeedSimRefineMaskWord(p, w) )
                return 0;
    }
    return 1;
}

static int Cec_SeedSimHashRefine( Cec_SeedSim_t * p,
    unsigned * pValue, int nTableSize )
{
    static int s_Primes[16] = {
        1291, 1699, 1999, 2357, 2953, 3313, 3907, 4177,
        4831, 5147, 5647, 6343, 6899, 7103, 7873, 8147
    };
    unsigned uHash = 0;
    int w;
    if ( pValue[0] & 1 )
        for ( w = 0; w < p->nWords; w++ )
            uHash ^= (~pValue[w] & Cec_SeedSimRefineMaskWord(p, w)) *
                     s_Primes[w & 0xf];
    else
        for ( w = 0; w < p->nWords; w++ )
            uHash ^= (pValue[w] & Cec_SeedSimRefineMaskWord(p, w)) *
                     s_Primes[w & 0xf];
    return (int)(uHash % nTableSize);
}

static int Cec_SeedSimCurrentRoot( Cec_SeedSim_t * p, int ObjId )
{
    if ( ObjId == 0 || Gia_ObjIsConst(p->pAig, ObjId) )
        return 0;
    if ( Gia_ObjIsHead(p->pAig, ObjId) )
        return ObjId;
    if ( Gia_ObjIsClass(p->pAig, ObjId) )
        return Gia_ObjRepr(p->pAig, ObjId);
    return ObjId;
}

static void Cec_SeedSimCheckFailedPairs( Cec_SeedSim_t * p, int Frame )
{
    int i;
    assert( Frame == p->iSeedFrame );
    for ( i = 0; i < Vec_IntSize(p->vDiagPairs); i += 3 )
    {
        int Obj0 = Vec_IntEntry( p->vDiagPairs, i );
        int Obj1 = Vec_IntEntry( p->vDiagPairs, i + 1 );
        int iBit = Vec_IntEntry( p->vDiagPairs, i + 2 );
        int iWord = iBit >> 5;
        unsigned Bit = (unsigned)1 << (iBit & 31);
        unsigned * pValue0, * pValue1;
        if ( Cec_SeedSimCurrentRoot(p, Obj0) != Cec_SeedSimCurrentRoot(p, Obj1) )
        {
            p->pFoundMask[iWord] |= Bit;
            continue;
        }
        pValue0 = Obj0 == 0 ? p->pPhase0 : Cec_SeedSimVal( p, Frame, Obj0 );
        pValue1 = Obj1 == 0 ? p->pPhase0 : Cec_SeedSimVal( p, Frame, Obj1 );
        Cec_SeedSimDiffMask( p, pValue0, pValue1, p->pActiveMask, p->pDiffMask );
        p->pFoundMask[iWord] |= p->pDiffMask[iWord] & Bit;
    }
}

static void Cec_SeedSimAddSplitKey( Cec_SeedSim_t * p, int Frame, int ObjId )
{
    int Key = Cec_SeedSimKey( p, Frame, ObjId );
    if ( p->pSplitMark[Key] == p->nSplitVersion )
        return;
    p->pSplitMark[Key] = p->nSplitVersion;
    Vec_IntPush( p->vSplitKeys, Key );
}

static int Cec_SeedSimPrepareFrame( Cec_SeedSim_t * p, Vec_Int_t * vKeys,
    int Frame, int iLo, int iHi, int nLimit, int fDiagnosis )
{
    Gia_Man_t * pAig = p->pAig;
    int i, Key, Ent;
    Cec_SeedSimStartRootSet( p );
    for ( i = iLo; i < iHi; i++ )
    {
        int ObjId;
        Key = Vec_IntEntry( vKeys, i );
        ObjId = Key % p->nObjs;
        if ( fDiagnosis )
        {
            int iDiag = p->pDiagMark[Key] - 1;
            unsigned * pMask;
            int RootOld;
            assert( iDiag >= 0 );
            pMask = (unsigned *)Vec_IntArray(p->vDiagMasks) + (size_t)iDiag * p->nWords;
            RootOld = Vec_IntEntry( p->vDiagRoots, iDiag );
            int RootNew = Gia_ObjIsConst(pAig, ObjId) ? 0 :
                (Gia_ObjIsHead(pAig, ObjId) ? ObjId :
                 (Gia_ObjIsClass(pAig, ObjId) ? Gia_ObjRepr(pAig, ObjId) : GIA_VOID));
            // Failed endpoints are diagnosis keys as well.  An endpoint
            // outside an equivalence class has no member-to-root assumption.
            if ( RootOld == GIA_VOID )
            {
                if ( !Cec_SeedSimEvalActive(p, Frame, ObjId, nLimit) )
                    return 0;
                continue;
            }
            if ( RootNew != RootOld )
            {
                int w;
                for ( w = 0; w < p->nWords; w++ )
                    p->pFoundMask[w] |= pMask[w];
                continue;
            }
        }
        Cec_SeedSimAddRoot( p, ObjId );
    }
    Vec_IntForEachEntry( p->vDirtyRoots, Ent, i )
    {
        int Member;
        if ( !Cec_SeedSimEvalActive(p, Frame, Ent, nLimit) )
            return 0;
        Gia_ClassForEachObj1( pAig, Ent, Member )
        {
            if ( !Cec_SeedSimEvalActive(p, Frame, Member, nLimit) )
                return 0;
        }
    }
    Vec_IntForEachEntry( p->vConstRefined, Ent, i )
        if ( !Cec_SeedSimEvalActive(p, Frame, Ent, nLimit) )
            return 0;
    if ( fDiagnosis )
    {
        for ( i = iLo; i < iHi; i++ )
        {
            unsigned * pMask, * pValue0, * pValue1;
            int ObjId, RootOld, RootNew, iDiag, w;
            Key = Vec_IntEntry( vKeys, i );
            ObjId = Key % p->nObjs;
            iDiag = p->pDiagMark[Key] - 1;
            assert( iDiag >= 0 );
            RootOld = Vec_IntEntry( p->vDiagRoots, iDiag );
            RootNew = Gia_ObjIsConst(pAig, ObjId) ? 0 :
                (Gia_ObjIsHead(pAig, ObjId) ? ObjId :
                 (Gia_ObjIsClass(pAig, ObjId) ? Gia_ObjRepr(pAig, ObjId) : GIA_VOID));
            pMask = (unsigned *)Vec_IntArray(p->vDiagMasks) + (size_t)iDiag * p->nWords;
            if ( RootOld == GIA_VOID )
                continue;
            if ( RootNew != RootOld )
            {
                for ( w = 0; w < p->nWords; w++ )
                    p->pFoundMask[w] |= pMask[w];
                continue;
            }
            if ( ObjId == RootOld )
                continue;
            pValue0 = Cec_SeedSimVal( p, Frame, ObjId );
            pValue1 = RootOld == 0 ?
                (Gia_ObjPhase(Gia_ManObj(pAig, ObjId)) ? p->pPhase1 : p->pPhase0) :
                Cec_SeedSimVal( p, Frame, RootOld );
            Cec_SeedSimDiffMask( p, pValue0, pValue1, pMask, p->pDiffMask );
            for ( w = 0; w < p->nWords; w++ )
                p->pFoundMask[w] |= p->pDiffMask[w];
        }
        if ( Frame == p->iSeedFrame )
            Cec_SeedSimCheckFailedPairs( p, Frame );
    }
    return 1;
}

static void Cec_SeedSimTxnBegin( Cec_SeedSim_t * p )
{
    assert( !p->fTxnActive );
    assert( p->pAig->pReprs != NULL && p->pAig->pNexts != NULL );
    Vec_IntClear( p->vTxnObjs );
    Vec_IntClear( p->vTxnReprs );
    Vec_IntClear( p->vTxnNexts );
    p->nTxnVersion++;
    if ( p->nTxnVersion == 0 )
    {
        memset( p->pTxnMark, 0, sizeof(int) * p->nObjs );
        p->nTxnVersion = 1;
    }
    p->fTxnActive = 1;
}

static void Cec_SeedSimTxnSaveObj( Cec_SeedSim_t * p, int ObjId )
{
    assert( ObjId >= 0 && ObjId < p->nObjs );
    if ( !p->fTxnActive || p->pTxnMark[ObjId] == p->nTxnVersion )
        return;
    p->pTxnMark[ObjId] = p->nTxnVersion;
    Vec_IntPush( p->vTxnObjs, ObjId );
    Vec_IntPush( p->vTxnReprs, Gia_ObjRepr(p->pAig, ObjId) );
    Vec_IntPush( p->vTxnNexts, Gia_ObjNext(p->pAig, ObjId) );
}

static void Cec_SeedSimTxnSaveVec( Cec_SeedSim_t * p, Vec_Int_t * vObjs )
{
    int i, ObjId;
    Vec_IntForEachEntry( vObjs, ObjId, i )
        Cec_SeedSimTxnSaveObj( p, ObjId );
}

static void Cec_SeedSimTxnCommit( Cec_SeedSim_t * p )
{
    assert( p->fTxnActive );
    p->fTxnActive = 0;
    Vec_IntClear( p->vTxnObjs );
    Vec_IntClear( p->vTxnReprs );
    Vec_IntClear( p->vTxnNexts );
}

static void Cec_SeedSimTxnRollback( Cec_SeedSim_t * p )
{
    int i, ObjId, nChanged = 0;
    assert( p->fTxnActive );
    assert( Vec_IntSize(p->vTxnObjs) == Vec_IntSize(p->vTxnReprs) );
    assert( Vec_IntSize(p->vTxnObjs) == Vec_IntSize(p->vTxnNexts) );
    for ( i = Vec_IntSize(p->vTxnObjs) - 1; i >= 0; i-- )
    {
        ObjId = Vec_IntEntry( p->vTxnObjs, i );
        if ( Gia_ObjRepr(p->pAig, ObjId) != Vec_IntEntry(p->vTxnReprs, i) ||
             Gia_ObjNext(p->pAig, ObjId) != Vec_IntEntry(p->vTxnNexts, i) )
            nChanged++;
        Gia_ObjSetRepr( p->pAig, ObjId, Vec_IntEntry(p->vTxnReprs, i) );
        Gia_ObjSetNext( p->pAig, ObjId, Vec_IntEntry(p->vTxnNexts, i) );
    }
    p->fTxnActive = 0;
    p->nBatchRollback++;
    p->nRollbackObjs += nChanged;
    Vec_IntClear( p->vTxnObjs );
    Vec_IntClear( p->vTxnReprs );
    Vec_IntClear( p->vTxnNexts );
}

static int Cec_SeedSimRefineClass_rec( Cec_SeedSim_t * p, int Frame, int iRoot )
{
    unsigned * pSim0;
    int Ent, Count = 0;
    Vec_IntClear( p->vClassOld );
    Vec_IntClear( p->vClassNew );
    Vec_IntPush( p->vClassOld, iRoot );
    pSim0 = Cec_SeedSimVal( p, Frame, iRoot );
    Gia_ClassForEachObj1( p->pAig, iRoot, Ent )
    {
        unsigned * pSim1 = Cec_SeedSimVal( p, Frame, Ent );
        if ( Cec_SeedSimCompareRefine(p, pSim0, pSim1) )
            Vec_IntPush( p->vClassOld, Ent );
        else
            Vec_IntPush( p->vClassNew, Ent );
    }
    if ( Vec_IntSize(p->vClassNew) == 0 )
        return 0;
    Cec_SeedSimTxnSaveVec( p, p->vClassOld );
    Cec_SeedSimTxnSaveVec( p, p->vClassNew );
    Cec_ManSimClassCreate( p->pAig, p->vClassOld );
    Cec_ManSimClassCreate( p->pAig, p->vClassNew );
    if ( Vec_IntSize(p->vClassNew) > 1 )
        Count += Cec_SeedSimRefineClass_rec( p, Frame, Vec_IntEntry(p->vClassNew, 0) );
    return Count + 1;
}

static int Cec_SeedSimRefineClass( Cec_SeedSim_t * p, int Frame, int iRoot )
{
    unsigned * pRoot = Cec_SeedSimVal( p, Frame, iRoot );
    unsigned * pDiff = p->pDiffMask;
    unsigned * pTemp = p->pTempMask;
    int Ent, i, w, Count;
    memset( pDiff, 0, sizeof(unsigned) * p->nWords );
    Vec_IntClear( p->vClassAll );
    Gia_ClassForEachObj( p->pAig, iRoot, Ent )
    {
        Vec_IntPush( p->vClassAll, Ent );
        if ( Ent == iRoot )
            continue;
        Cec_SeedSimDiffMask( p, pRoot, Cec_SeedSimVal(p, Frame, Ent),
                            p->pRefineMask, pTemp );
        for ( w = 0; w < p->nWords; w++ )
            pDiff[w] |= pTemp[w];
    }
    if ( Cec_SeedSimMaskIsZero(pDiff, p->nWords) )
        return 0;
    Count = Cec_SeedSimRefineClass_rec( p, Frame, iRoot );
    assert( Count > 0 );
    Vec_IntForEachEntry( p->vClassAll, Ent, i )
        Cec_SeedSimAddSplitKey( p, Frame, Ent );
    return Count;
}

static void Cec_SeedSimProcessRefinedConstants( Cec_SeedSim_t * p,
    Cec_ManSim_t * pSim, int Frame )
{
    Gia_Man_t * pAig = p->pAig;
    int * pTable;
    int i, k, Key, iPrev, nTableSize;
    if ( Vec_IntSize(p->vConstRefined) == 0 )
        return;
    Vec_IntForEachEntry( p->vConstRefined, i, k )
    {
        unsigned * pValue = Cec_SeedSimVal( p, Frame, i );
        unsigned * pPhase = Gia_ObjPhase(Gia_ManObj(pAig, i)) ? p->pPhase1 : p->pPhase0;
        unsigned * pDiff = p->pDiffMask;
        Cec_SeedSimDiffMask( p, pValue, pPhase, p->pRefineMask, pDiff );
        if ( Cec_SeedSimMaskIsZero(pDiff, p->nWords) )
        {
            Vec_IntDrop( p->vConstRefined, k-- );
            continue;
        }
        Cec_SeedSimAddSplitKey( p, Frame, i );
    }
    if ( Vec_IntSize(p->vConstRefined) == 0 )
        return;
    Cec_SeedSimTxnSaveVec( p, p->vConstRefined );
    if ( pSim->pPars->fConstCorr )
    {
        Vec_IntForEachEntry( p->vConstRefined, i, k )
            Gia_ObjSetRepr( pAig, i, GIA_VOID );
        return;
    }
    nTableSize = Abc_PrimeCudd( 100 + Vec_IntSize(p->vConstRefined) / 3 );
    pTable = ABC_CALLOC( int, nTableSize );
    Vec_IntForEachEntry( p->vConstRefined, i, k )
    {
        assert( Gia_ObjRepr(pAig, i) == 0 );
        assert( Gia_ObjNext(pAig, i) == 0 );
        Key = Cec_SeedSimHashRefine( p, Cec_SeedSimVal(p, Frame, i), nTableSize );
        iPrev = pTable[Key];
        if ( iPrev == 0 )
            Gia_ObjSetRepr( pAig, i, GIA_VOID );
        else
        {
            assert( iPrev < i );
            Gia_ObjSetNext( pAig, iPrev, i );
            Gia_ObjSetRepr( pAig, i, Gia_ObjRepr(pAig, iPrev) );
            if ( Gia_ObjRepr(pAig, i) == GIA_VOID )
                Gia_ObjSetRepr( pAig, i, iPrev );
        }
        pTable[Key] = i;
    }
    Vec_IntForEachEntry( p->vConstRefined, i, k )
        if ( Gia_ObjIsHead(pAig, i) )
            Cec_SeedSimRefineClass_rec( p, Frame, i );
    ABC_FREE( pTable );
}

static void Cec_SeedSimRefineFrame( Cec_SeedSim_t * p, Cec_ManSim_t * pSim,
    int Frame )
{
    int i, Ent;
    Vec_IntForEachEntry( p->vDirtyRoots, Ent, i )
        if ( Gia_ObjIsHead(p->pAig, Ent) )
            Cec_SeedSimRefineClass( p, Frame, Ent );
    Cec_SeedSimProcessRefinedConstants( p, pSim, Frame );
}

static int Cec_SeedSimProcessKeys( Cec_SeedSim_t * p, Cec_ManSim_t * pSim,
    Vec_Int_t * vKeys, int nLimit, int fDiagnosis )
{
    int iLo = 0;
    p->pRefineMask = p->pActiveMask;
    Vec_IntSort( vKeys, 0 );
    while ( iLo < Vec_IntSize(vKeys) )
    {
        int Frame = Vec_IntEntry(vKeys, iLo) / p->nObjs;
        int iHi = iLo;
        while ( iHi < Vec_IntSize(vKeys) &&
                Vec_IntEntry(vKeys, iHi) / p->nObjs == Frame )
            iHi++;
        if ( !Cec_SeedSimPrepareFrame(p, vKeys, Frame, iLo, iHi, nLimit, fDiagnosis) )
            return 0;
        Cec_SeedSimRefineFrame( p, pSim, Frame );
        iLo = iHi;
    }
    return 1;
}

static int Cec_SeedSimDiagnosisMissing( Cec_SeedSim_t * p )
{
    int Count = 0, w;
    for ( w = 0; w < p->nWords; w++ )
    {
        unsigned Bits = p->pCexMask[w] & ~p->pFoundMask[w];
        while ( Bits )
        {
            Bits &= Bits - 1;
            Count++;
        }
    }
    return Count;
}

static void Cec_SeedSimRecordBatch( Cec_SeedSim_t * p, int nCex )
{
    p->nBatchCex += nCex;
    if ( nCex > p->nBatchCexMax )
        p->nBatchCexMax = nCex;
}

static void Cec_SeedSimBuildPersistentValues( Cec_SeedSim_t * p )
{
    Gia_Obj_t * pObj;
    int Frame, i, w;
    for ( Frame = 0; Frame < p->nFrames; Frame++ )
    {
        memset( Cec_SeedSimVal(p, Frame, 0), 0, sizeof(unsigned) * p->nWords );
        for ( i = 0; i < p->nPis; i++ )
        {
            int ObjId = Gia_ObjId( p->pAig, Gia_ManPi(p->pAig, i) );
            unsigned * pDst = Cec_SeedSimVal( p, Frame, ObjId );
            unsigned * pSrc = (unsigned *)Vec_PtrEntry(
                p->vSimInfo, p->nRegs + Frame * p->nPis + i );
            memcpy( pDst, pSrc, sizeof(unsigned) * p->nWords );
        }
        for ( i = 0; i < p->nRegs; i++ )
        {
            int ObjId = Gia_ObjId( p->pAig, Gia_ManRo(p->pAig, i) );
            unsigned * pDst = Cec_SeedSimVal( p, Frame, ObjId );
            if ( Frame == 0 )
            {
                unsigned * pSrc = (unsigned *)Vec_PtrEntry( p->vSimInfo, i );
                memcpy( pDst, pSrc, sizeof(unsigned) * p->nWords );
            }
            else
            {
                Gia_Obj_t * pRi = Gia_ObjRoToRi( p->pAig, Gia_ManRo(p->pAig, i) );
                int RiId = Gia_ObjId( p->pAig, pRi );
                unsigned * pSrc = Cec_SeedSimVal(
                    p, Frame - 1, Gia_ObjFaninId0(pRi, RiId) );
                if ( Gia_ObjFaninC0(pRi) )
                    for ( w = 0; w < p->nWords; w++ )
                        pDst[w] = ~pSrc[w];
                else
                    memcpy( pDst, pSrc, sizeof(unsigned) * p->nWords );
            }
        }
        Gia_ManForEachAnd( p->pAig, pObj, i )
        {
            unsigned * pDst = Cec_SeedSimVal( p, Frame, i );
            unsigned * pVal0 = Cec_SeedSimVal(
                p, Frame, Gia_ObjFaninId0(pObj, i) );
            unsigned * pVal1 = Cec_SeedSimVal(
                p, Frame, Gia_ObjFaninId1(pObj, i) );
            for ( w = 0; w < p->nWords; w++ )
            {
                unsigned Val0 = Gia_ObjFaninC0(pObj) ? ~pVal0[w] : pVal0[w];
                unsigned Val1 = Gia_ObjFaninC1(pObj) ? ~pVal1[w] : pVal1[w];
                pDst[w] = Val0 & Val1;
            }
        }
    }
}

void Cec_SeedSimEnsurePersistent( Cec_SeedSim_t * p, Cec_ManSim_t * pSim )
{
    int nInputs = p->nRegs + p->nPis * p->nFrames;
    size_t nInputWords = (size_t)nInputs * p->nWords;
    int i, w;
    if ( p->vSimInfo == NULL )
    {
        p->vSimInfo = Vec_PtrAllocSimInfo( nInputs, p->nWords );
        p->pPackPres = ABC_CALLOC( unsigned, nInputWords );
        p->pInputUndoMark = ABC_CALLOC( int, nInputWords );
    }
    if ( p->fInitialized )
        return;
    for ( i = 0; i < nInputs; i++ )
    {
        unsigned * pInfo = (unsigned *)Vec_PtrEntry( p->vSimInfo, i );
        for ( w = 0; w < p->nWords; w++ )
            pInfo[w] = i < p->nRegs ? 0 : Gia_ManRandom( 0 );
        pInfo[0] &= ~(unsigned)1;
    }
    // The baseline full sweep makes every current class consistent with the
    // persistent patterns.  It is paid once; later fallbacks are rolled back
    // to this evolving persistent state without copying the dense value cache.
    Cec_ManSeqResimulateSeed( pSim, p->vSimInfo, p );
    Cec_SeedSimBuildPersistentValues( p );
    p->fInitialized = 1;
}

static void Cec_SeedSimStartInputTxn( Cec_SeedSim_t * p )
{
    size_t nInputWords = (size_t)Vec_PtrSize(p->vSimInfo) * p->nWords;
    Vec_IntClear( p->vInputUndo );
    Vec_IntClear( p->vChangedInputs );
    p->nInputUndoVersion++;
    p->nInputVarVersion++;
    if ( p->nInputUndoVersion == 0 )
    {
        memset( p->pInputUndoMark, 0, sizeof(int) * nInputWords );
        p->nInputUndoVersion = 1;
    }
    if ( p->nInputVarVersion == 0 )
    {
        memset( p->pInputVarMark, 0,
            sizeof(int) * Vec_PtrSize(p->vSimInfo) );
        p->nInputVarVersion = 1;
    }
}

static void Cec_SeedSimSetInputWord( Cec_SeedSim_t * p,
    int iVar, int w, unsigned Value )
{
    int Flat = iVar * p->nWords + w;
    unsigned * pInfo = (unsigned *)Vec_PtrEntry( p->vSimInfo, iVar );
    if ( pInfo[w] == Value )
        return;
    if ( p->pInputUndoMark[Flat] != p->nInputUndoVersion )
    {
        p->pInputUndoMark[Flat] = p->nInputUndoVersion;
        Vec_IntPush( p->vInputUndo, Flat );
        Vec_IntPush( p->vInputUndo, (int)pInfo[w] );
    }
    if ( p->pInputVarMark[iVar] != p->nInputVarVersion )
    {
        p->pInputVarMark[iVar] = p->nInputVarVersion;
        Vec_IntPush( p->vChangedInputs, iVar );
    }
    pInfo[w] = Value;
}

static int Cec_SeedSimPackTry( Cec_SeedSim_t * p,
    int iBit, int * pLits, int nLits )
{
    int i, iVar, w = iBit >> 5;
    unsigned Bit = (unsigned)1 << (iBit & 31);
    for ( i = 0; i < nLits; i++ )
    {
        unsigned * pInfo, * pPres;
        iVar = Abc_Lit2Var( pLits[i] );
        pInfo = (unsigned *)Vec_PtrEntry( p->vSimInfo, iVar );
        pPres = p->pPackPres + (size_t)iVar * p->nWords;
        if ( (pPres[w] & Bit) &&
             ((pInfo[w] & Bit) != (Abc_LitIsCompl(pLits[i]) ? 0 : Bit)) )
            return 0;
    }
    for ( i = 0; i < nLits; i++ )
    {
        unsigned * pInfo, * pPres;
        unsigned Value;
        int Flat;
        iVar = Abc_Lit2Var( pLits[i] );
        pInfo = (unsigned *)Vec_PtrEntry( p->vSimInfo, iVar );
        pPres = p->pPackPres + (size_t)iVar * p->nWords;
        Flat = iVar * p->nWords + w;
        if ( pPres[w] == 0 )
            Vec_IntPush( p->vPackTouched, Flat );
        pPres[w] |= Bit;
        Value = Abc_LitIsCompl(pLits[i]) ? pInfo[w] & ~Bit : pInfo[w] | Bit;
        Cec_SeedSimSetInputWord( p, iVar, w, Value );
    }
    return 1;
}

int Cec_SeedSimLoadPersistentBatch( Cec_SeedSim_t * p, Vec_Int_t * vCexStore,
    int iStart, Vec_Int_t * vPairs, Vec_Int_t * vOutBits )
{
    Vec_Int_t * vPat = Vec_IntAlloc( 100 );
    int nBits = 32 * p->nWords;
    int i, k, nSize, Out, Flat;
    Cec_SeedSimStartInputTxn( p );
    Vec_IntClear( p->vPackTouched );
    Vec_IntClear( vOutBits );
    while ( iStart < Vec_IntSize(vCexStore) )
    {
        Out = Vec_IntEntry( vCexStore, iStart++ );
        nSize = Vec_IntEntry( vCexStore, iStart++ );
        if ( nSize <= 0 )
            continue;
        Vec_IntClear( vPat );
        for ( k = 0; k < nSize; k++ )
            Vec_IntPush( vPat, Vec_IntEntry(vCexStore, iStart++) );
        for ( k = 1; k < nBits; k++ )
            if ( Cec_SeedSimPackTry(
                    p, k, Vec_IntArray(vPat), Vec_IntSize(vPat)) )
                break;
        if ( k < nBits )
        {
            Vec_IntPush( vOutBits, Out );
            Vec_IntPush( vOutBits, k );
        }
        if ( k == nBits - 1 )
            break;
    }
    Vec_IntForEachEntry( p->vPackTouched, Flat, i )
        p->pPackPres[Flat] = 0;
    Vec_IntClear( p->vPackTouched );
    Vec_IntForEachEntryDouble( vPairs, k, Out, i )
    {
        unsigned * pSrc = (unsigned *)Vec_PtrEntry( p->vSimInfo, k );
        for ( nSize = 0; nSize < p->nWords; nSize++ )
            Cec_SeedSimSetInputWord( p, Out, nSize, pSrc[nSize] );
    }
    Vec_IntFree( vPat );
    return iStart;
}

void Cec_SeedSimRestorePersistentInputs( Cec_SeedSim_t * p )
{
    int i, Flat;
    for ( i = Vec_IntSize(p->vInputUndo) - 2; i >= 0; i -= 2 )
    {
        Flat = Vec_IntEntry( p->vInputUndo, i );
        ((unsigned *)Vec_PtrEntry(
            p->vSimInfo, Flat / p->nWords))[Flat % p->nWords] =
            (unsigned)Vec_IntEntry( p->vInputUndo, i + 1 );
    }
    Vec_IntClear( p->vInputUndo );
    Vec_IntClear( p->vChangedInputs );
}

static void Cec_SeedSimCommitPersistentInputs( Cec_SeedSim_t * p )
{
    Vec_IntClear( p->vInputUndo );
    Vec_IntClear( p->vChangedInputs );
}

static void Cec_SeedSimEventHeapPushWord( Cec_SeedSim_t * p, int Key, int w )
{
    unsigned * pWords = p->pEventWords + (size_t)Key * p->nEventMaskWords;
    int i, Parent, fNew = 0;
    if ( p->pMark[Key] != p->nMarkVersion )
    {
        p->pMark[Key] = p->nMarkVersion;
        memset( pWords, 0, sizeof(unsigned) * p->nEventMaskWords );
        Vec_IntPush( p->vQueue, Key );
        fNew = 1;
    }
    else if ( Abc_InfoHasBit(pWords, w) )
        return;
    Abc_InfoSetBit( pWords, w );
    if ( !fNew )
        return;
    for ( i = Vec_IntSize(p->vQueue) - 1; i > 0; i = Parent )
    {
        Parent = (i - 1) >> 1;
        if ( Vec_IntEntry(p->vQueue, Parent) <= Key )
            break;
        Vec_IntWriteEntry( p->vQueue, i,
            Vec_IntEntry(p->vQueue, Parent) );
    }
    Vec_IntWriteEntry( p->vQueue, i, Key );
}

static int Cec_SeedSimEventHeapPop( Cec_SeedSim_t * p )
{
    int Result = Vec_IntEntry( p->vQueue, 0 );
    int Last = Vec_IntPop( p->vQueue );
    int Size = Vec_IntSize( p->vQueue );
    int i = 0;
    if ( Size == 0 )
        return Result;
    while ( 2 * i + 1 < Size )
    {
        int Child = 2 * i + 1;
        if ( Child + 1 < Size &&
             Vec_IntEntry(p->vQueue, Child + 1) <
             Vec_IntEntry(p->vQueue, Child) )
            Child++;
        if ( Vec_IntEntry(p->vQueue, Child) >= Last )
            break;
        Vec_IntWriteEntry( p->vQueue, i,
            Vec_IntEntry(p->vQueue, Child) );
        i = Child;
    }
    Vec_IntWriteEntry( p->vQueue, i, Last );
    return Result;
}

static void Cec_SeedSimEventRecordWord( Cec_SeedSim_t * p,
    int Key, int w, unsigned OldValue )
{
    Vec_IntPush( p->vValueUndo, Key );
    Vec_IntPush( p->vValueUndo, w );
    Vec_IntPush( p->vValueUndo, (int)OldValue );
}

static void Cec_SeedSimEventRecordChanged( Cec_SeedSim_t * p, int Key )
{
    if ( p->pProcessMark[Key] == p->nProcessVersion )
        return;
    p->pProcessMark[Key] = p->nProcessVersion;
    Vec_IntPush( p->vChangedValues, Key );
}

static int Cec_SeedSimEventQueueFanouts( Cec_SeedSim_t * p,
    int Frame, int ObjId, int w, int nEdgeLimit )
{
    int FanId, i;
    Gia_ObjForEachFanoutStaticId( p->pAig, ObjId, FanId, i )
    {
        Gia_Obj_t * pFan = Gia_ManObj( p->pAig, FanId );
        if ( ++p->nEventEdges > nEdgeLimit )
            return 0;
        if ( Gia_ObjIsAnd(pFan) )
        {
            int FanKey = Cec_SeedSimKey(p, Frame, FanId);
            if ( Cec_SeedSimConeHasKey(p, FanKey) )
                Cec_SeedSimEventHeapPushWord( p, FanKey, w );
        }
        else if ( Gia_ObjIsRi(p->pAig, pFan) &&
                  Frame + 1 < p->nFrames )
        {
            int RoKey = Cec_SeedSimKey(
                p, Frame + 1, Gia_ObjRiToRoId(p->pAig, FanId));
            if ( Cec_SeedSimConeHasKey(p, RoKey) )
                Cec_SeedSimEventHeapPushWord( p, RoKey, w );
        }
    }
    return 1;
}

static int Cec_SeedSimEventUpdateInput( Cec_SeedSim_t * p,
    int iVar, int nEdgeLimit )
{
    int Frame, ObjId, w, Key, fChanged = 0;
    unsigned * pInput;
    if ( iVar < p->nRegs )
    {
        Frame = 0;
        ObjId = Gia_ObjId( p->pAig, Gia_ManRo(p->pAig, iVar) );
    }
    else
    {
        int iPi = (iVar - p->nRegs) % p->nPis;
        Frame = (iVar - p->nRegs) / p->nPis;
        ObjId = Gia_ObjId( p->pAig, Gia_ManPi(p->pAig, iPi) );
    }
    Key = Cec_SeedSimKey( p, Frame, ObjId );
    if ( !Cec_SeedSimConeHasKey(p, Key) )
        return 1;
    pInput = (unsigned *)Vec_PtrEntry( p->vSimInfo, iVar );
    for ( w = 0; w < p->nWords; w++ )
    {
        unsigned * pValue = Cec_SeedSimVal( p, Frame, ObjId );
        if ( pValue[w] == pInput[w] )
            continue;
        Cec_SeedSimEventRecordWord(
            p, Key, w, pValue[w] );
        pValue[w] = pInput[w];
        fChanged = 1;
        if ( !Cec_SeedSimEventQueueFanouts(
                 p, Frame, ObjId, w, nEdgeLimit) )
            return 0;
    }
    if ( !fChanged )
        return 1;
    Cec_SeedSimEventRecordChanged( p, Key );
    return 1;
}

static int Cec_SeedSimEventUpdateNode( Cec_SeedSim_t * p,
    int Key, int nNodeLimit, int nEdgeLimit )
{
    int Frame = Key / p->nObjs;
    int ObjId = Key % p->nObjs;
    Gia_Obj_t * pObj = Gia_ManObj( p->pAig, ObjId );
    unsigned * pDst = Cec_SeedSimVal( p, Frame, ObjId );
    unsigned * pVal0, * pVal1 = NULL;
    unsigned * pWords = p->pEventWords + (size_t)Key * p->nEventMaskWords;
    int m, w, fChanged = 0;
    if ( Gia_ObjIsRo(p->pAig, pObj) )
    {
        Gia_Obj_t * pRi;
        int RiId;
        assert( Frame > 0 );
        pRi = Gia_ObjRoToRi( p->pAig, pObj );
        RiId = Gia_ObjId( p->pAig, pRi );
        pVal0 = Cec_SeedSimVal(
            p, Frame - 1, Gia_ObjFaninId0(pRi, RiId) );
        for ( m = 0; m < p->nEventMaskWords; m++ )
        {
            unsigned Bits = pWords[m];
            while ( Bits )
            {
                w = 32 * m + Gia_WordFindFirstBit( Bits );
                Bits &= Bits - 1;
                if ( w >= p->nWords )
                    continue;
                if ( ++p->nEventPops > nNodeLimit )
                    return 0;
                {
                    unsigned Value = Gia_ObjFaninC0(pRi) ? ~pVal0[w] : pVal0[w];
                    if ( pDst[w] == Value )
                        continue;
                    Cec_SeedSimEventRecordWord( p, Key, w, pDst[w] );
                    pDst[w] = Value;
                    fChanged = 1;
                    if ( !Cec_SeedSimEventQueueFanouts(
                             p, Frame, ObjId, w, nEdgeLimit) )
                        return 0;
                }
            }
        }
    }
    else
    {
        assert( Gia_ObjIsAnd(pObj) );
        pVal0 = Cec_SeedSimVal(
            p, Frame, Gia_ObjFaninId0(pObj, ObjId) );
        pVal1 = Cec_SeedSimVal(
            p, Frame, Gia_ObjFaninId1(pObj, ObjId) );
        for ( m = 0; m < p->nEventMaskWords; m++ )
        {
            unsigned Bits = pWords[m];
            while ( Bits )
            {
                w = 32 * m + Gia_WordFindFirstBit( Bits );
                Bits &= Bits - 1;
                if ( w >= p->nWords )
                    continue;
                if ( ++p->nEventPops > nNodeLimit )
                    return 0;
                {
                    unsigned Val0 = Gia_ObjFaninC0(pObj) ? ~pVal0[w] : pVal0[w];
                    unsigned Val1 = Gia_ObjFaninC1(pObj) ? ~pVal1[w] : pVal1[w];
                    unsigned Value = Val0 & Val1;
                    if ( pDst[w] == Value )
                        continue;
                    Cec_SeedSimEventRecordWord( p, Key, w, pDst[w] );
                    pDst[w] = Value;
                    fChanged = 1;
                    if ( !Cec_SeedSimEventQueueFanouts(
                             p, Frame, ObjId, w, nEdgeLimit) )
                        return 0;
                }
            }
        }
    }
    if ( !fChanged )
        return 1;
    Cec_SeedSimEventRecordChanged( p, Key );
    return 1;
}

static void Cec_SeedSimEventRollbackValues( Cec_SeedSim_t * p )
{
    int i, Key, w;
    for ( i = Vec_IntSize(p->vValueUndo) - 3; i >= 0; i -= 3 )
    {
        Key = Vec_IntEntry( p->vValueUndo, i );
        w = Vec_IntEntry( p->vValueUndo, i + 1 );
        Cec_SeedSimVal(
            p, Key / p->nObjs, Key % p->nObjs)[w] =
            (unsigned)Vec_IntEntry( p->vValueUndo, i + 2 );
    }
    Vec_IntClear( p->vValueUndo );
    Vec_IntClear( p->vChangedValues );
}

static void Cec_SeedSimEventRefine( Cec_SeedSim_t * p, Cec_ManSim_t * pSim )
{
    int iLo = 0;
    p->pRefineMask = p->pActiveMask;
    // Baseline classes are value-consistent.  If a pair becomes different,
    // at least one member changed, so regrouping these roots is complete.
    Vec_IntSort( p->vChangedValues, 0 );
    while ( iLo < Vec_IntSize(p->vChangedValues) )
    {
        int Frame = Vec_IntEntry(p->vChangedValues, iLo) / p->nObjs;
        int iHi = iLo, i, Key, ObjId;
        while ( iHi < Vec_IntSize(p->vChangedValues) &&
                Vec_IntEntry(p->vChangedValues, iHi) / p->nObjs == Frame )
            iHi++;
        Cec_SeedSimStartRootSet( p );
        for ( i = iLo; i < iHi; i++ )
        {
            Key = Vec_IntEntry( p->vChangedValues, i );
            ObjId = Key % p->nObjs;
            if ( Gia_ObjIsConst(p->pAig, ObjId) ||
                 Gia_ObjIsClass(p->pAig, ObjId) )
                Cec_SeedSimAddRoot( p, ObjId );
        }
        Cec_SeedSimRefineFrame( p, pSim, Frame );
        iLo = iHi;
    }
}

static void Cec_SeedSimQueueInitialSplits( Cec_SeedSim_t * p, int nInitialSplits )
{
    int i, Key;
    for ( i = 0; i < nInitialSplits; i++ )
    {
        Key = Vec_IntEntry( p->vSplitKeys, i );
        int Frame = Key / p->nObjs;
        int ObjId = Key % p->nObjs;
        if ( Cec_SeedSimMark(p, Frame, ObjId) )
            Vec_IntPush( p->vQueue, Key );
    }
}

static void Cec_SeedSimCollectWave( Cec_SeedSim_t * p )
{
    int i, Key;
    Vec_IntClear( p->vWaveKeys );
    Vec_IntForEachEntry( p->vDirtyKeys, Key, i )
    {
        if ( p->pProcessMark[Key] == p->nProcessVersion )
            continue;
        p->pProcessMark[Key] = p->nProcessVersion;
        Vec_IntPush( p->vWaveKeys, Key );
    }
}

static int Cec_SeedSimTryBatchLegacy( Cec_SeedSim_t * p, Cec_ManSim_t * pSim,
    Vec_Ptr_t * vSimInfo, Vec_Int_t * vOutputs, Vec_Int_t * vOutBits, int nFrames )
{
    ABC_INT64_T nKeys = (ABC_INT64_T)p->nFrames * p->nObjs;
    int nLimit = (int)(nKeys * CEC_SEEDSIM_HARD_FRAC_NUM / CEC_SEEDSIM_HARD_FRAC_DEN);
    int nDiagLimit = (int)(nKeys * CEC_SEEDSIM_DIAG_FRAC_NUM / CEC_SEEDSIM_DIAG_FRAC_DEN);
    int nTfoLimit = (int)(nKeys * CEC_SEEDSIM_TFO_FRAC_NUM / CEC_SEEDSIM_TFO_FRAC_DEN);
    int nBatchCex = Vec_IntSize(vOutBits) / 2;
    int nPackedLanes = 32 * p->nWords - 1;
    int nInitialSplits, nDirty;
    assert( nFrames == p->nFrames );
    assert( Vec_PtrSize(vSimInfo) == p->nRegs + p->nPis * p->nFrames );
    assert( Vec_PtrReadWordsSimInfo(vSimInfo) == p->nWords );
    Cec_SeedSimRecordBatch( p, nBatchCex );
    if ( !p->fInitialized )
    {
        p->nFallbackPre++;
        p->nBatchFull++;
        return CEC_SEEDSIM_RESULT_FULL;
    }
    if ( nBatchCex > CEC_SEEDSIM_CEX_LANE_FACTOR * nPackedLanes )
    {
        p->nFallbackCex++;
        p->nBatchFull++;
        return CEC_SEEDSIM_RESULT_FULL_WIDE;
    }
    Cec_SeedSimReset( p );
    p->vBatchInfo = vSimInfo;
    if ( !Cec_SeedSimDiagnosisShapeSmall(p, vOutputs, vOutBits, nDiagLimit) )
    {
        nDirty = Vec_IntSize( p->vDirtyKeys );
        if ( nDirty > p->nMaxDirty )
            p->nMaxDirty = nDirty;
        p->vBatchInfo = NULL;
        p->nFallbackPre++;
        p->nBatchFull++;
        return CEC_SEEDSIM_RESULT_FULL_WIDE;
    }
    Cec_SeedSimRestartTfoMarks( p );
    if ( !Cec_SeedSimCollectDiagnosis(p, vOutputs, vOutBits, nLimit) ||
         Vec_IntSize(p->vDiagKeys) > nLimit )
    {
        nDirty = Abc_MaxInt( p->nSpecKeys, p->nEvalKeys );
        if ( nDirty > p->nMaxDirty )
            p->nMaxDirty = nDirty;
        p->vBatchInfo = NULL;
        p->nFallbackPre++;
        p->nBatchFull++;
        return CEC_SEEDSIM_RESULT_FULL_WIDE;
    }
    if ( !Cec_SeedSimDiagnosisEvalShapeSmall(p, p->vDiagKeys, nDiagLimit) )
    {
        nDirty = Vec_IntSize( p->vDirtyKeys );
        if ( nDirty > p->nMaxDirty )
            p->nMaxDirty = nDirty;
        p->vBatchInfo = NULL;
        p->nFallbackPre++;
        p->nBatchFull++;
        return CEC_SEEDSIM_RESULT_FULL_WIDE;
    }
    Cec_SeedSimRestartTfoMarks( p );
    Cec_SeedSimUseCexLanes( p );
    Cec_SeedSimTxnBegin( p );
    if ( !Cec_SeedSimProcessKeys(p, pSim, p->vDiagKeys, nLimit, 1) )
    {
        nDirty = Abc_MaxInt( p->nSpecKeys, p->nEvalKeys );
        if ( nDirty > p->nMaxDirty )
            p->nMaxDirty = nDirty;
        Cec_SeedSimTxnRollback( p );
        p->vBatchInfo = NULL;
        p->nFallbackProcess++;
        p->nBatchFull++;
        return CEC_SEEDSIM_RESULT_FULL;
    }
    {
        int nMissing;
        nMissing = Cec_SeedSimDiagnosisMissing( p );
        if ( nMissing )
        {
            nDirty = Abc_MaxInt( p->nSpecKeys, p->nEvalKeys );
            if ( nDirty > p->nMaxDirty )
                p->nMaxDirty = nDirty;
            Cec_SeedSimTxnRollback( p );
            p->vBatchInfo = NULL;
            p->nCoverageMiss += nMissing;
            p->nFallbackCoverage++;
            p->nBatchFull++;
            return CEC_SEEDSIM_RESULT_FULL;
        }
    }
    Cec_SeedSimTxnCommit( p );
    Cec_SeedSimUsePackedLanes( p );
    nInitialSplits = Vec_IntSize( p->vSplitKeys );
    Cec_SeedSimQueueInitialSplits( p, nInitialSplits );
    if ( !Cec_SeedSimComputeTfo(p, nTfoLimit) )
    {
        nDirty = Vec_IntSize( p->vDirtyKeys );
        if ( nDirty > p->nMaxDirty )
            p->nMaxDirty = nDirty;
        p->vBatchInfo = NULL;
        p->nBatchTrunc++;
        p->nTruncCone++;
        p->nBatchLocal++;
        return CEC_SEEDSIM_RESULT_LOCAL;
    }
    Cec_SeedSimCollectWave( p );
    if ( Vec_IntSize(p->vWaveKeys) &&
         !Cec_SeedSimProcessKeys(p, pSim, p->vWaveKeys, nTfoLimit, 0) )
    {
        p->nDeferredSplits += Vec_IntSize(p->vSplitKeys) - nInitialSplits;
        if ( p->nEvalKeys > p->nMaxDirty )
            p->nMaxDirty = p->nEvalKeys;
        p->vBatchInfo = NULL;
        p->nBatchTrunc++;
        p->nTruncEval++;
        p->nBatchLocal++;
        return CEC_SEEDSIM_RESULT_LOCAL;
    }
    p->nDeferredSplits += Vec_IntSize(p->vSplitKeys) - nInitialSplits;
    nDirty = Abc_MaxInt( p->nSpecKeys, Vec_IntSize(p->vDirtyKeys) );
    nDirty = Abc_MaxInt( nDirty, p->nEvalKeys );
    if ( nDirty > p->nMaxDirty )
        p->nMaxDirty = nDirty;
    p->vBatchInfo = NULL;
    p->nBatchLocal++;
    return CEC_SEEDSIM_RESULT_LOCAL;
}

int Cec_SeedSimTryBatch( Cec_SeedSim_t * p, Cec_ManSim_t * pSim,
    Vec_Ptr_t * vSimInfo, Vec_Int_t * vOutputs, Vec_Int_t * vOutBits, int nFrames )
{
    ABC_INT64_T nKeys = (ABC_INT64_T)p->nFrames * p->nObjs;
    ABC_INT64_T nWordKeys = nKeys * p->nWords;
    ABC_INT64_T nNodeLimit64 = nWordKeys *
        CEC_EVENT_NODE_WORD_FRAC_NUM / CEC_EVENT_NODE_WORD_FRAC_DEN;
    ABC_INT64_T nEdgeLimit64 = nWordKeys *
        CEC_EVENT_EDGE_WORD_FRAC_NUM / CEC_EVENT_EDGE_WORD_FRAC_DEN;
    int nNodeLimit = nNodeLimit64 > 0x7fffffff ? 0x7fffffff : (int)nNodeLimit64;
    int nEdgeLimit = nEdgeLimit64 > 0x7fffffff ? 0x7fffffff : (int)nEdgeLimit64;
    int nInputVars = Vec_IntSize( p->vChangedInputs );
    int nInputWords = Vec_IntSize( p->vInputUndo ) / 2;
    int nTotalInputs = p->nRegs + p->nPis * p->nFrames;
    int i, iVar, Key;
    int Status = CEC_SEEDSIM_RESULT_LOCAL;
    assert( nFrames == p->nFrames );
    assert( vSimInfo == p->vSimInfo );
    Cec_SeedSimRecordBatch( p, Vec_IntSize(vOutBits) / 2 );
    p->nEventInputVarsMax = Abc_MaxInt( p->nEventInputVarsMax, nInputVars );
    p->nEventInputWordsMax = Abc_MaxInt( p->nEventInputWordsMax, nInputWords );
    if ( (ABC_INT64_T)nInputVars * CEC_EVENT_INPUT_FRAC_DEN >
         (ABC_INT64_T)nTotalInputs * CEC_EVENT_INPUT_FRAC_NUM )
    {
        p->nFallbackCex++;
        p->nBatchFull++;
        return CEC_SEEDSIM_RESULT_FULL_WIDE;
    }
    (void)vOutputs;
    Cec_SeedSimReset( p );
    Vec_IntClear( p->vValueUndo );
    Vec_IntClear( p->vChangedValues );
    p->nEventPops = p->nEventEdges = 0;

    Vec_IntForEachEntry( p->vChangedInputs, iVar, i )
        if ( !Cec_SeedSimEventUpdateInput(p, iVar, nEdgeLimit) )
        {
            Status = CEC_SEEDSIM_RESULT_FULL_WIDE;
            break;
        }
    while ( Status == CEC_SEEDSIM_RESULT_LOCAL &&
            Vec_IntSize(p->vQueue) > 0 )
    {
        Key = Cec_SeedSimEventHeapPop( p );
        if ( !Cec_SeedSimEventUpdateNode(
                 p, Key, nNodeLimit, nEdgeLimit) )
        {
            Status = CEC_SEEDSIM_RESULT_FULL_WIDE;
            break;
        }
    }
    p->nEventPopsMax = Abc_MaxInt( p->nEventPopsMax, p->nEventPops );
    p->nEventEdgesMax = Abc_MaxInt( p->nEventEdgesMax, p->nEventEdges );
    p->nMaxDirty = Abc_MaxInt(
        p->nMaxDirty, Vec_IntSize(p->vChangedValues) );
    if ( Status != CEC_SEEDSIM_RESULT_LOCAL )
    {
        Cec_SeedSimEventRollbackValues( p );
        p->nEventFallback++;
        p->nEventFallbackWork++;
        p->nFallbackPre++;
        p->nBatchFull++;
        return Status;
    }
    Cec_SeedSimTxnBegin( p );
    Cec_SeedSimEventRefine( p, pSim );
    Cec_SeedSimTxnCommit( p );
    Vec_IntClear( p->vValueUndo );
    Vec_IntClear( p->vChangedValues );
    Cec_SeedSimCommitPersistentInputs( p );
    p->nEventLocal++;
    p->nBatchLocal++;
    return CEC_SEEDSIM_RESULT_LOCAL;
}

void Cec_SeedSimSaveFrameInputs( Cec_SeedSim_t * p, Vec_Ptr_t * vInfoCis, int Frame )
{
    Gia_Obj_t * pObj;
    int i;
    assert( Frame >= 0 && Frame < p->nFrames );
    assert( Vec_PtrSize(vInfoCis) == p->nPis + p->nRegs );
    assert( Vec_PtrReadWordsSimInfo(vInfoCis) == p->nWords );
    Cec_SeedSimSetPhase( p, Frame, 0, 0 );
    Gia_ManForEachCi( p->pAig, pObj, i )
        Cec_SeedSimSetPhase( p, Frame, Gia_ObjId(p->pAig, pObj), 0 );
}

void Cec_SeedSimSaveFrameOutputs( Cec_SeedSim_t * p, Vec_Ptr_t * vInfoCos, int Frame )
{
    Gia_Obj_t * pObj;
    int i;
    assert( Frame >= 0 && Frame < p->nFrames );
    assert( Vec_PtrSize(vInfoCos) == Gia_ManCoNum(p->pAig) );
    assert( Vec_PtrReadWordsSimInfo(vInfoCos) == p->nWords );
    Gia_ManForEachCo( p->pAig, pObj, i )
        Cec_SeedSimSetPhase( p, Frame, Gia_ObjId(p->pAig, pObj),
            ((unsigned *)Vec_PtrEntry(vInfoCos, i))[0] & 1 );
}

void Cec_SeedSimFinishFull( Cec_SeedSim_t * p )
{
    p->fInitialized = 1;
}

void Cec_SeedSimBeginCall( Cec_SeedSim_t * p )
{
    assert( !p->fTxnActive );
    p->nBatchLocal = p->nBatchFull = p->nBatchTrunc = p->nMaxDirty = 0;
    p->nBatchRollback = p->nRollbackObjs = p->nCoverageMiss = 0;
    p->nFallbackPre = p->nFallbackProcess = p->nFallbackCoverage = 0;
    p->nFallbackCex = p->nFallbackBypass = 0;
    p->nTruncCone = p->nTruncEval = 0;
    p->nBatchCex = p->nBatchCexMax = p->nDeferredSplits = 0;
    p->nEventLocal = p->nEventFallback = 0;
    p->nEventPopsMax = p->nEventEdgesMax = 0;
    p->nEventInputVarsMax = p->nEventInputWordsMax = 0;
    p->nEventFallbackWork = 0;
}

void Cec_SeedSimBypassBatch( Cec_SeedSim_t * p, int nCex )
{
    Cec_SeedSimRecordBatch( p, nCex );
    p->nFallbackBypass++;
    p->nBatchFull++;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
