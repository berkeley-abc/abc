/**CFile****************************************************************

  FileName    [bmcUnroll.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based bounded model checking.]

  Synopsis    [Unrolling manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: bmc.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "bmc.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define UNR_DIFF_NULL 0x7FFF

typedef struct Unr_Obj_t_ Unr_Obj_t; // 24 bytes + (RankMax-1) * 4 bytes
struct Unr_Obj_t_
{
    unsigned              hFan0;        // address of the fanin
    unsigned              hFan1;        // address of the fanin
    unsigned              fCompl0 :  1; // complemented bit
    unsigned              fCompl1 :  1; // complemented bit
    unsigned              uRDiff0 : 15; // rank diff of the fanin
    unsigned              uRDiff1 : 15; // rank diff of the fanin
    unsigned              RankMax : 16; // max rank diff between node and its fanout
    unsigned              RankCur : 16; // cur rank of the node
    unsigned              OrigId;       // original object ID
    unsigned              Res[1];       // RankMax entries
};

typedef struct Unr_Man_t_ Unr_Man_t;
struct Unr_Man_t_
{
    // input data
    Gia_Man_t *           pGia;           // the user's AIG manager
//    Gia_Man_t *           pNew;           // unrolling manager
    int                   nObjs;          // the number of objects
    // intermediate data
    Vec_Int_t *           vOrder;         // ordering of GIA objects
    Vec_Int_t *           vOrderLim;      // beginning of each time frame
    Vec_Int_t *           vTents;         // tents of GIA objects
    Vec_Int_t *           vRanks;         // ranks of GIA objects
    // unrolling data
    int *                 pObjs;          // storage for unroling objects
    int *                 pEnd;           // end of storage
    Vec_Int_t *           vObjLim;        // handle of the first object in each frame
    Vec_Int_t *           vResLits;       // resulting literals
    Vec_Int_t *           vCiMap;         // mapping of GIA CIs into unrolling objects
    Vec_Int_t *           vCoMap;         // mapping of GIA POs into unrolling objects
};

static inline Unr_Obj_t * Unr_ManObj( Unr_Man_t * p, int h )  { assert( h >= 0 && h < p->pEnd - p->pObjs ); return (Unr_Obj_t *)(p->pObjs + h);  }
static inline int         Unr_ObjSize( Unr_Obj_t * pObj )     { return 0x7FFFFFFE & (sizeof(Unr_Obj_t) / sizeof(int) + pObj->RankMax);           }
static inline int Unr_ManFanin0Value( Unr_Man_t * p, Unr_Obj_t * pObj )
{
    Unr_Obj_t * pFanin = Unr_ManObj( p, pObj->hFan0 );
    int Index = (pFanin->RankCur + pFanin->RankMax - pObj->uRDiff0) % pFanin->RankMax;
    assert( pFanin->RankCur < pFanin->RankMax );
    assert( pObj->uRDiff0 < pFanin->RankMax );
    return Abc_LitNotCond( pFanin->Res[Index], pObj->fCompl0 );
}
static inline int Unr_ManFanin1Value( Unr_Man_t * p, Unr_Obj_t * pObj )
{
    Unr_Obj_t * pFanin = Unr_ManObj( p, pObj->hFan1 );
    int Index = (pFanin->RankCur + pFanin->RankMax - pObj->uRDiff1) % pFanin->RankMax;
    assert( pFanin->RankCur < pFanin->RankMax );
    assert( pObj->uRDiff1 < pFanin->RankMax );
    return Abc_LitNotCond( pFanin->Res[Index], pObj->fCompl1 );
}
static inline int Unr_ManObjReadValue( Unr_Obj_t * pObj )
{
    assert( pObj->RankCur >= 0 && pObj->RankCur < pObj->RankMax );
    return pObj->Res[ pObj->RankCur ];
}
static inline void Unr_ManObjSetValue( Unr_Obj_t * pObj, int Value )
{
    pObj->RankCur = (0xFFFF & (pObj->RankCur + 1)) % pObj->RankMax;
    pObj->Res[ pObj->RankCur ] = Value;
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vec_IntWriteMaxEntry( Vec_Int_t * p, int i, int Entry )
{
    assert( i >= 0 && i < p->nSize );
    p->pArray[i] = Abc_MaxInt( p->pArray[i], Entry );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Unr_ManProfileRanks( Vec_Int_t * vRanks )
{
    int RankMax = Vec_IntFindMax( vRanks );
    Vec_Int_t * vCounts = Vec_IntStart( RankMax+1 );
    int i, Rank, Count, nExtras = 0;
    Vec_IntForEachEntry( vRanks, Rank, i )
        Vec_IntAddToEntry( vCounts, Rank, 1 );
    Vec_IntForEachEntry( vCounts, Count, i )
    {
        printf( "%2d : %8d  (%6.2f %%)\n", i, Count, 100.0 * Count / Vec_IntSize(vRanks) );
        nExtras += Count * i;
    }
    printf( "Extra space = %d (%6.2f %%)\n", nExtras, 100.0 * nExtras / Vec_IntSize(vRanks) );
    Vec_IntFree( vCounts );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Unr_ManSetup_rec( Unr_Man_t * p, int iObj, int iTent, Vec_Int_t * vRoots )
{
    Gia_Obj_t * pObj;
    int iFanin;
    if ( Vec_IntEntry(p->vTents, iObj) >= 0 )
        return;
    Vec_IntWriteEntry(p->vTents, iObj, iTent);
    pObj = Gia_ManObj( p->pGia, iObj );
    if ( Gia_ObjIsAnd(pObj) || Gia_ObjIsCo(pObj) )
    {
        Unr_ManSetup_rec( p, (iFanin = Gia_ObjFaninId0(pObj, iObj)), iTent, vRoots );
        Vec_IntWriteMaxEntry( p->vRanks, iFanin, Abc_MaxInt(0, iTent - Vec_IntEntry(p->vTents, iFanin) - 1) );
    }
    if ( Gia_ObjIsAnd(pObj) )
    {
        Unr_ManSetup_rec( p, (iFanin = Gia_ObjFaninId1(pObj, iObj)), iTent, vRoots );
        Vec_IntWriteMaxEntry( p->vRanks, iFanin, Abc_MaxInt(0, iTent - Vec_IntEntry(p->vTents, iFanin) - 1) );
    }
    else if ( Gia_ObjIsRo(p->pGia, pObj) )
    {
        Vec_IntPush( vRoots, (iFanin = Gia_ObjId(p->pGia, Gia_ObjRoToRi(p->pGia, pObj))) );
        Vec_IntWriteMaxEntry( p->vRanks, iFanin, 0 );
    }
    Vec_IntPush( p->vOrder, iObj );
}
void Unr_ManSetup( Unr_Man_t * p )
{
    Vec_Int_t * vRoots, * vRoots2, * vMap;
    Unr_Obj_t * pUnrObj;
    Gia_Obj_t * pObj;
    int i, k, t, iObj, Rank, nInts, * pInts;
    abctime clk = Abc_Clock();
    vRoots  = Vec_IntAlloc( 100 );
    vRoots2 = Vec_IntAlloc( 100 );
    // create zero rank
    assert( Vec_IntSize(p->vOrder) == 0 );
    Vec_IntPush( p->vOrder, 0 );
    Vec_IntPush( p->vOrderLim, Vec_IntSize(p->vOrder) );
    Vec_IntWriteEntry( p->vTents, 0, 0 );
    Vec_IntWriteEntry( p->vRanks, 0, 0 );
    // start from the POs
    Gia_ManForEachPo( p->pGia, pObj, i )
        Unr_ManSetup_rec( p, Gia_ObjId(p->pGia, pObj), 0, vRoots );
    // iterate through tents
    while ( Vec_IntSize(vRoots) > 0 )
    {
        Vec_IntPush( p->vOrderLim, Vec_IntSize(p->vOrder) );
        Vec_IntClear( vRoots2 );
        Vec_IntForEachEntry( vRoots, iObj, i )
            Unr_ManSetup_rec( p, iObj, Vec_IntSize(p->vOrderLim)-1, vRoots2 );
        ABC_SWAP( Vec_Int_t *, vRoots, vRoots2 );
    }
    Vec_IntPush( p->vOrderLim, Vec_IntSize(p->vOrder) );
    Vec_IntFree( vRoots );
    Vec_IntFree( vRoots2 );
    // allocate memory
    nInts = Vec_IntSize(p->vOrder) * (sizeof(Unr_Obj_t) / sizeof(int));
    Vec_IntForEachEntry( p->vRanks, Rank, i )
        nInts += 0x7FFFFFFE & (Rank + 1);
    p->pObjs = pInts = ABC_CALLOC( int, nInts );
    p->pEnd = p->pObjs + nInts;
    // create const0 node
    pUnrObj = Unr_ManObj( p, pInts - p->pObjs );
    pUnrObj->RankMax = 1;
    pUnrObj->uRDiff0 = pUnrObj->uRDiff1 = UNR_DIFF_NULL;
    pUnrObj->Res[0]  = 0; // const0
    // map the objects
    vMap = Vec_IntStartFull( p->nObjs );
    Vec_IntWriteEntry( vMap, 0, pInts - p->pObjs );
    pInts += Unr_ObjSize(pUnrObj);
    // mark up the entries
    assert( Vec_IntSize(p->vObjLim) == 0 );
    for ( t = Vec_IntSize(p->vOrderLim) - 2; t >= 0; t-- )
    {
        int Beg = Vec_IntEntry(p->vOrderLim, t);
        int End = Vec_IntEntry(p->vOrderLim, t+1);
        Vec_IntPush( p->vObjLim, pInts - p->pObjs );
        Vec_IntForEachEntryStartStop( p->vOrder, iObj, i, Beg, End )
        {
            pObj = Gia_ManObj( p->pGia, iObj );
            pUnrObj = Unr_ManObj( p, pInts - p->pObjs );
            pUnrObj->uRDiff0 = pUnrObj->uRDiff1 = UNR_DIFF_NULL;
            if ( Gia_ObjIsAnd(pObj) || Gia_ObjIsCo(pObj) )
                pUnrObj->uRDiff0 = Abc_MaxInt(0, Vec_IntEntry(p->vTents, iObj) - Vec_IntEntry(p->vTents, Gia_ObjFaninId0(pObj, iObj)) - 1);
            if ( Gia_ObjIsAnd(pObj) )
                pUnrObj->uRDiff1 = Abc_MaxInt(0, Vec_IntEntry(p->vTents, iObj) - Vec_IntEntry(p->vTents, Gia_ObjFaninId1(pObj, iObj)) - 1);
            else if ( Gia_ObjIsRo(p->pGia, pObj) )
                pUnrObj->uRDiff0 = 0;
            pUnrObj->RankMax = Vec_IntEntry(p->vRanks, iObj) + 1;
            pUnrObj->RankCur = 0xFFFF;
            pUnrObj->OrigId  = iObj;
            for ( k = 0; k < (int)pUnrObj->RankMax; k++ )
                pUnrObj->Res[k] = -1;
            Vec_IntWriteEntry( vMap, iObj, pInts - p->pObjs );
            pInts += Unr_ObjSize( pUnrObj );
        }
    }
    assert( pInts - p->pObjs <= nInts );
Unr_ManProfileRanks( p->vRanks );
    Vec_IntFreeP( &p->vOrder );
    Vec_IntFreeP( &p->vOrderLim );
    Vec_IntFreeP( &p->vRanks );
//    Vec_IntFreeP( &p->vTents );
    // label the objects
    Gia_ManForEachObj( p->pGia, pObj, i )
    {
        if ( Vec_IntEntry(vMap, i) == -1 )
            continue;
        pUnrObj = Unr_ManObj( p, Vec_IntEntry(vMap, i) );
        if ( Gia_ObjIsAnd(pObj) || Gia_ObjIsCo(pObj) )
        {
            pUnrObj->hFan0   = Vec_IntEntry( vMap, Gia_ObjFaninId0(pObj, i) );
            pUnrObj->fCompl0 = Gia_ObjFaninC0(pObj);
            assert( pUnrObj->hFan0 != ~0 );
        }
        if ( Gia_ObjIsAnd(pObj) )
        {
            pUnrObj->hFan1   = Vec_IntEntry( vMap, Gia_ObjFaninId1(pObj, i) );
            pUnrObj->fCompl1 = Gia_ObjFaninC1(pObj);
            assert( pUnrObj->hFan1 != ~0);
        }
        else if ( Gia_ObjIsRo(p->pGia, pObj) )
        {
            pUnrObj->hFan0   = Vec_IntEntry( vMap, Gia_ObjId(p->pGia, Gia_ObjRoToRi(p->pGia, pObj)) );
            pUnrObj->fCompl0 = 0;
        }
    }
    // store CI/PO objects;
    Gia_ManForEachCi( p->pGia, pObj, i )
        Vec_IntPush( p->vCiMap, Vec_IntEntry(vMap, Gia_ObjId(p->pGia, pObj)) );
    Gia_ManForEachCo( p->pGia, pObj, i )
        Vec_IntPush( p->vCoMap, Vec_IntEntry(vMap, Gia_ObjId(p->pGia, pObj)) );
    Vec_IntFreeP( &vMap );

    printf( "Memory usage = %6.2f MB\n", 4.0 * nInts / (1<<20) );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
}



/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Unr_Man_t * Unr_ManAlloc( Gia_Man_t * pGia )
{
    Unr_Man_t * p;
    p = ABC_CALLOC( Unr_Man_t, 1 );
    p->pGia      = pGia;
    p->nObjs     = Gia_ManObjNum(pGia);
//    p->pNew      = Gia_ManStart( 10000 );
    p->vOrder    = Vec_IntAlloc( p->nObjs );
    p->vOrderLim = Vec_IntAlloc( 100 );
    p->vTents    = Vec_IntStartFull( p->nObjs );
    p->vRanks    = Vec_IntStart( p->nObjs );
    p->vObjLim   = Vec_IntAlloc( 100 );
    p->vResLits  = Vec_IntAlloc( Gia_ManPoNum(pGia) );
    p->vCiMap    = Vec_IntAlloc( Gia_ManCiNum(pGia) );
    p->vCoMap    = Vec_IntAlloc( Gia_ManCoNum(pGia) );
    return p;
}
void Unr_ManFree( Unr_Man_t * p )
{
//    Gia_ManStop( p->pNew );
    Vec_IntFreeP( &p->vTents );
    // intermediate data
    Vec_IntFreeP( &p->vOrder );
    Vec_IntFreeP( &p->vOrderLim );
    Vec_IntFreeP( &p->vTents );
    Vec_IntFreeP( &p->vRanks );
    // unrolling data
    Vec_IntFreeP( &p->vObjLim );
    Vec_IntFreeP( &p->vResLits );
    Vec_IntFreeP( &p->vCiMap );
    Vec_IntFreeP( &p->vCoMap );
    ABC_FREE( p->pObjs );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Perform smart unrolling.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Unr_ManUnroll( Unr_Man_t * p, int nFrames )
{
    Gia_Man_t * pTemp, * pFrames;
    Unr_Obj_t * pUnrObj;
    Vec_Int_t * vPiLits;
    int f, i, iLit, iLit0, iLit1, hStart;
    pFrames = Gia_ManStart( 10000 );
    pFrames->pName = Abc_UtilStrsav( p->pGia->pName );
    Gia_ManHashAlloc( pFrames );
    // create flop values
    for ( i = 0; i < Gia_ManRegNum(p->pGia); i++ )
    {
        if ( Vec_IntEntry(p->vCoMap, Gia_ManPoNum(p->pGia) + i) == -1 )
            continue;
        pUnrObj = Unr_ManObj( p, Vec_IntEntry(p->vCoMap, Gia_ManPoNum(p->pGia) + i) );
        Unr_ManObjSetValue( pUnrObj, 0 );
    }
    vPiLits = Vec_IntAlloc( nFrames * Gia_ManPiNum(p->pGia) );
    for ( f = 0; f < nFrames; f++ )
    {
        for ( i = 0; i < Gia_ManPiNum(p->pGia); i++ )
            Vec_IntPush( vPiLits, Gia_ManAppendCi(pFrames) );
        hStart = Vec_IntEntry( p->vObjLim, Abc_MaxInt(0, Vec_IntSize(p->vObjLim)-1-f) );
        while ( p->pObjs + hStart < p->pEnd )
        {
            pUnrObj = Unr_ManObj( p, hStart );
            if ( pUnrObj->uRDiff0 != UNR_DIFF_NULL && pUnrObj->uRDiff1 != UNR_DIFF_NULL )
            {
                iLit0 = Unr_ManFanin0Value( p, pUnrObj );
                iLit1 = Unr_ManFanin1Value( p, pUnrObj );
                iLit  = Gia_ManHashAnd( pFrames, iLit0, iLit1 );
                assert( iLit >= 0 );
                Unr_ManObjSetValue( pUnrObj, iLit );
            }
            else if ( pUnrObj->uRDiff0 != UNR_DIFF_NULL && pUnrObj->uRDiff1 == UNR_DIFF_NULL )
            {
                iLit  = Unr_ManFanin0Value( p, pUnrObj );
                assert( iLit >= 0 );
                Unr_ManObjSetValue( pUnrObj, iLit );
            }
            else
            {
                Gia_Obj_t * pObj = Gia_ManObj(p->pGia, pUnrObj->OrigId);
                assert( Gia_ObjIsPi(p->pGia, pObj) );
                assert( f >= Vec_IntEntry(p->vTents, pUnrObj->OrigId) );
                iLit = Vec_IntEntry( vPiLits, Gia_ManPiNum(p->pGia) * (f - Vec_IntEntry(p->vTents, pUnrObj->OrigId)) + Gia_ObjCioId(pObj) );
                Unr_ManObjSetValue( pUnrObj, iLit );
            }
            hStart += Unr_ObjSize( pUnrObj );
        }
        assert( p->pObjs + hStart == p->pEnd );
        for ( i = 0; i < Gia_ManPoNum(p->pGia); i++ )
        {
            pUnrObj = Unr_ManObj(p, Vec_IntEntry(p->vCoMap, i));
            Gia_ManAppendCo( pFrames, Unr_ManObjReadValue(pUnrObj) );
        }
    }
    Vec_IntFree( vPiLits );
    Gia_ManHashStop( pFrames );
    Gia_ManSetRegNum( pFrames, 0 );
    pFrames = Gia_ManCleanup( pTemp = pFrames );
    Gia_ManStop( pTemp );
    return pFrames;
}

/**Function*************************************************************

  Synopsis    [Perform naive unrolling.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Unr_ManUnrollSimple( Gia_Man_t * pGia, int nFrames )
{
    Gia_Man_t * pFrames;
    Gia_Obj_t * pObj, * pObjRi;
    int f, i; 
    pFrames = Gia_ManStart( 10000 );
    pFrames->pName = Abc_UtilStrsav( pGia->pName );
    Gia_ManHashAlloc( pFrames );
    Gia_ManConst0(pGia)->Value = 0;
    Gia_ManForEachRi( pGia, pObj, i )
        pObj->Value = 0;
    for ( f = 0; f < nFrames; f++ )
    {
        Gia_ManForEachPi( pGia, pObj, i )
            pObj->Value = Gia_ManAppendCi(pFrames);
        Gia_ManForEachRiRo( pGia, pObjRi, pObj, i )
            pObj->Value = pObjRi->Value;
        Gia_ManForEachAnd( pGia, pObj, i )
            pObj->Value = Gia_ManHashAnd( pFrames, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        Gia_ManForEachCo( pGia, pObj, i )
            pObj->Value = Gia_ObjFanin0Copy(pObj);
        Gia_ManForEachPo( pGia, pObj, i )
            Gia_ManAppendCo( pFrames, pObj->Value );
    }
    Gia_ManHashStop( pFrames );
    Gia_ManSetRegNum( pFrames, 0 );
    pFrames = Gia_ManCleanup( pGia = pFrames );
    Gia_ManStop( pGia );
    return pFrames;
}

/**Function*************************************************************

  Synopsis    [Perform evaluation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Unr_ManTest( Gia_Man_t * pGia, int nFrames )
{
    Gia_Man_t * pFrames0, * pFrames1;
    Unr_Man_t * p;

    abctime clk = Abc_Clock();
    p = Unr_ManAlloc( pGia );
    Unr_ManSetup( p );
    Abc_PrintTime( 1, "Prepare", Abc_Clock() - clk );

    clk = Abc_Clock();
    pFrames0 = Unr_ManUnroll( p, nFrames );
    Abc_PrintTime( 1, "Unroll ", Abc_Clock() - clk );

    Unr_ManFree( p );

    clk = Abc_Clock();
    pFrames1 = Unr_ManUnrollSimple( pGia, nFrames );
    Abc_PrintTime( 1, "UnrollS", Abc_Clock() - clk );

Gia_ManPrintStats( pFrames0, 0, 0, 0 );
Gia_ManPrintStats( pFrames1, 0, 0, 0 );
Gia_AigerWrite( pFrames0, "frames0.aig", 0, 0 );
Gia_AigerWrite( pFrames1, "frames1.aig", 0, 0 );
    Gia_ManStop( pFrames0 );
    Gia_ManStop( pFrames1 );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

