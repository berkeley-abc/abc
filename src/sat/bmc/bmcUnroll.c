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
    Gia_Man_t *           pNew;           // unrolling manager
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
    Vec_Int_t *           vPoMap;         // mapping of GIA POs into unrolling objects
};

static inline Unr_Obj_t * Unr_ManObj( Unr_Man_t * p, int h )             { assert( h >= 0 && h < p->pEnd - p->pObjs ); return (Unr_Obj_t *)(p->pObjs + h); }
static inline int Unr_ManFanin0Value( Unr_Man_t * p, Unr_Obj_t * pObj )
{
    Unr_Obj_t * pFanin = Unr_ManObj( p, pObj->hFan0 );
    int Index = (pFanin->RankCur + pFanin->RankMax - pObj->uRDiff0) % pFanin->RankMax;
    assert( pFanin->RankCur <= pFanin->RankMax );
    assert( pObj->uRDiff0 <= pFanin->RankMax );
    return Abc_LitNotCond( pFanin->Res[Index], pObj->fCompl0 );
}
static inline int Unr_ManFanin1Value( Unr_Man_t * p, Unr_Obj_t * pObj )
{
    Unr_Obj_t * pFanin = Unr_ManObj( p, pObj->hFan1 );
    int Index = (pFanin->RankCur + pFanin->RankMax - pObj->uRDiff1) % pFanin->RankMax;
    assert( pFanin->RankCur <= pFanin->RankMax );
    assert( pObj->uRDiff1 <= pFanin->RankMax );
    return Abc_LitNotCond( pFanin->Res[Index], pObj->fCompl1 );
}
static inline void Unr_ManObjSetValue( Unr_Man_t * p, Unr_Obj_t * pObj, int Value )
{
    pObj->Res[ pObj->RankCur ] = Value;
    pObj->RankCur = (pObj->RankCur + 1) % pObj->RankMax;
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
        Vec_IntWriteMaxEntry( p->vRanks, iFanin, iTent - Vec_IntEntry(p->vTents, iFanin) );
    }
    if ( Gia_ObjIsAnd(pObj) )
    {
        Unr_ManSetup_rec( p, (iFanin = Gia_ObjFaninId1(pObj, iObj)), iTent, vRoots );
        Vec_IntWriteMaxEntry( p->vRanks, iFanin, iTent - Vec_IntEntry(p->vTents, iFanin) );
    }
    else if ( Gia_ObjIsRo(p->pGia, pObj) )
    {
        Vec_IntPush( vRoots, (iFanin = Gia_ObjId(p->pGia, Gia_ObjRoToRi(p->pGia, pObj))) );
        Vec_IntWriteMaxEntry( p->vRanks, iFanin, 1 );
    }
    Vec_IntPush( p->vOrder, iObj );
}
void Unr_ManSetup( Unr_Man_t * p )
{
    Vec_Int_t * vRoots, * vRoots2, * vMap;
    Gia_Obj_t * pObj, * pObjRi;
    Unr_Obj_t * pUnrObj;
    int i, k, t, iObj, nInts, * pInts;
    clock_t clk = clock();
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
    Vec_IntWriteEntry( p->vRanks, 0, 0 );
    Vec_IntFree( vRoots );
    Vec_IntFree( vRoots2 );
    // allocate memory
    nInts = Vec_IntSize(p->vOrder) * (sizeof(Unr_Obj_t) / sizeof(int)) + Vec_IntSum(p->vRanks);
    p->pObjs = pInts = ABC_CALLOC( int, nInts );
    p->pEnd = p->pObjs + nInts;
    vMap = Vec_IntStartFull( p->nObjs );
    // create const0 node
    pUnrObj = Unr_ManObj( p, pInts - p->pObjs );
    pUnrObj->RankMax = 1;
    pUnrObj->uRDiff0 = pUnrObj->uRDiff1 = UNR_DIFF_NULL;
    pUnrObj->Res[0]  = 0; // const0
    pInts += sizeof(Unr_Obj_t) / sizeof(int);
    // mark up the entries
    assert( Vec_IntSize(p->vObjLim) == 0 );
    Vec_IntPush( p->vObjLim, pInts - p->pObjs );
    for ( t = Vec_IntSize(p->vOrderLim) - 2; t >= 0; t-- )
    {
        int Beg = Vec_IntEntry(p->vOrderLim, t);
        int End = Vec_IntEntry(p->vOrderLim, t+1);
        Vec_IntForEachEntryStartStop( p->vOrder, iObj, i, Beg, End )
        {
            pObj = Gia_ManObj( p->pGia, iObj );
            pUnrObj = Unr_ManObj( p, pInts - p->pObjs );
            pUnrObj->uRDiff0 = pUnrObj->uRDiff1 = UNR_DIFF_NULL;
            if ( Gia_ObjIsAnd(pObj) || Gia_ObjIsCo(pObj) )
            {
                pUnrObj->hFan0   = Vec_IntEntry( vMap, Gia_ObjFaninId0(pObj, iObj) );
                pUnrObj->fCompl0 = Gia_ObjFaninC0(pObj);
                pUnrObj->uRDiff0 = Vec_IntEntry(p->vTents, iObj) - Vec_IntEntry(p->vTents, Gia_ObjFaninId0(pObj, iObj));
            }
            if ( Gia_ObjIsAnd(pObj) )
            {
                pUnrObj->hFan1   = Vec_IntEntry( vMap, Gia_ObjFaninId1(pObj, iObj) );
                pUnrObj->fCompl1 = Gia_ObjFaninC1(pObj);
                pUnrObj->uRDiff1 = Vec_IntEntry(p->vTents, iObj) - Vec_IntEntry(p->vTents, Gia_ObjFaninId1(pObj, iObj));
            }
            else if ( Gia_ObjIsRo(p->pGia, pObj) )
            {
                pObjRi = Gia_ObjRoToRi(p->pGia, pObj);
                pUnrObj->hFan0   = Vec_IntEntry( vMap, Gia_ObjId(p->pGia, pObjRi) );
                pUnrObj->fCompl0 = 0;
                pUnrObj->uRDiff0 = 1;
            }
            pUnrObj->RankMax = Vec_IntEntry(p->vRanks, iObj) + 1;
            pUnrObj->RankCur = 0;
            pUnrObj->OrigId  = iObj;
            for ( k = 0; k < (int)pUnrObj->RankMax; k++ )
                pUnrObj->Res[k] = -1;
            Vec_IntWriteEntry( vMap, iObj, pInts - p->pObjs );
            pInts += sizeof(Unr_Obj_t) / sizeof(int) + pUnrObj->RankMax - 1;
        }
        Vec_IntPush( p->vObjLim, pInts - p->pObjs );
    }
    assert( pInts - p->pObjs == nInts );
    Vec_IntFreeP( &p->vOrder );
    Vec_IntFreeP( &p->vOrderLim );
    Vec_IntFreeP( &p->vTents );
Unr_ManProfileRanks( p->vRanks );
    Vec_IntFreeP( &p->vRanks );
    // store CI/PO objects;
    Gia_ManForEachCi( p->pGia, pObj, i )
        Vec_IntPush( p->vCiMap, Vec_IntEntry(vMap, Gia_ObjId(p->pGia, pObj)) );
    Gia_ManForEachPo( p->pGia, pObj, i )
        Vec_IntPush( p->vPoMap, Vec_IntEntry(vMap, Gia_ObjId(p->pGia, pObj)) );
    Vec_IntFreeP( &vMap );

    printf( "Memory usage = %6.2f MB\n", 4.0 * nInts / (1<<20) );
    Abc_PrintTime( 1, "Time", clock() - clk );
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
    p->pNew      = Gia_ManStart( 10000 );
    p->vOrder    = Vec_IntAlloc( p->nObjs );
    p->vOrderLim = Vec_IntAlloc( 100 );
    p->vTents    = Vec_IntStartFull( p->nObjs );
    p->vRanks    = Vec_IntStart( p->nObjs );
    p->vObjLim   = Vec_IntAlloc( 100 );
    p->vResLits  = Vec_IntAlloc( Gia_ManPoNum(pGia) );
    p->vCiMap    = Vec_IntAlloc( Gia_ManCiNum(pGia) );
    p->vPoMap    = Vec_IntAlloc( Gia_ManPoNum(pGia) );
    return p;
}
void Unr_ManFree( Unr_Man_t * p )
{
    Gia_ManStop( p->pNew );
    // intermediate data
    Vec_IntFreeP( &p->vOrder );
    Vec_IntFreeP( &p->vOrderLim );
    Vec_IntFreeP( &p->vTents );
    Vec_IntFreeP( &p->vRanks );
    // unrolling data
    Vec_IntFreeP( &p->vObjLim );
    Vec_IntFreeP( &p->vResLits );
    Vec_IntFreeP( &p->vCiMap );
    Vec_IntFreeP( &p->vPoMap );
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
    Gia_Man_t * pGia, * pFrames;
    Unr_Obj_t * pUnrObj;
    int f, i, iLit, iLit0, iLit1, hStart;
    pFrames = Gia_ManStart( 10000 );
    pFrames->pName = Abc_UtilStrsav( p->pGia->pName );
    Gia_ManHashAlloc( pFrames );
    // create flop values
    for ( i = 0; i < Gia_ManRegNum(p->pGia); i++ )
    {
        pUnrObj = Unr_ManObj(p, Vec_IntEntry(p->vCiMap, Gia_ManPiNum(p->pGia) + i));
        Unr_ManObjSetValue( p, pUnrObj, 0 );
    }
    for ( f = 0; f < nFrames; f++ )
    {
        for ( i = 0; i < Gia_ManPiNum(p->pGia); i++ )
        {
            pUnrObj = Unr_ManObj(p, Vec_IntEntry(p->vCiMap, Gia_ManPiNum(p->pGia) + i));
            Unr_ManObjSetValue( p, pUnrObj, Gia_ManAppendCi(pFrames) );
        }
        hStart = f < Vec_IntSize(p->vObjLim)-1 ? Vec_IntEntry( p->vObjLim, Vec_IntSize(p->vObjLim)-2 - f ) : 0;
        while ( p->pObjs + hStart < p->pEnd )
        {
            pUnrObj = Unr_ManObj( p, hStart );
            if ( pUnrObj->uRDiff0 != UNR_DIFF_NULL && pUnrObj->uRDiff1 != UNR_DIFF_NULL )
            {
                iLit0 = Unr_ManFanin0Value( p, pUnrObj );
                iLit1 = Unr_ManFanin1Value( p, pUnrObj );
                iLit  = Gia_ManAppendAnd( pFrames, iLit0, iLit1 );
                Unr_ManObjSetValue( p, pUnrObj, iLit );
            }
            else if ( pUnrObj->uRDiff1 == UNR_DIFF_NULL )
            {
                iLit  = Unr_ManFanin0Value( p, pUnrObj );
                Unr_ManObjSetValue( p, pUnrObj, iLit );
            }
            hStart += sizeof(Unr_Obj_t) / sizeof(int) + pUnrObj->RankMax - 1;
        }
        assert( p->pObjs + hStart == p->pEnd );
    }
    Gia_ManHashStop( pFrames );
    Gia_ManSetRegNum( pFrames, 0 );
    pFrames = Gia_ManCleanup( pGia = pFrames );
    Gia_ManStop( pGia );
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
    pFrames = Gia_ManStart( Gia_ManObjNum(pGia) * nFrames );
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
            pObj->Value = Gia_ManAppendAnd( pFrames, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
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
void Unr_ManTest( Gia_Man_t * pGia )
{
//    Gia_Man_t * pFrames0, * pFrames1;
//    int nFrames = 10;
    Unr_Man_t * p;
    p = Unr_ManAlloc( pGia );
    Unr_ManSetup( p );
//    pFrames0 = Unr_ManUnroll( p, nFrames );
    Unr_ManFree( p );
//    pFrames1 = Unr_ManUnrollSimple( pGia, nFrames );
//Gia_AigerWrite( pFrames0, "frames0.aig", 0, 0 );
//Gia_AigerWrite( pFrames1, "frames1.aig", 0, 0 );
//    Gia_ManStop( pFrames0 );
//    Gia_ManStop( pFrames1 );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

