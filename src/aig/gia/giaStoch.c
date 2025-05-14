/**CFile****************************************************************

  FileName    [giaStoch.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Experiments with synthesis.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaStoch.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "base/main/main.h"
#include "base/cmd/cmd.h"

#ifdef WIN32
#include <process.h> 
#define unlink _unlink
#else
#include <unistd.h>
#endif

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Processing on a single core.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_StochProcessSingle( Gia_Man_t * p, char * pScript, int Rand, int TimeSecs )
{
    Gia_Man_t * pTemp, * pNew = Gia_ManDup( p );
    Abc_FrameUpdateGia( Abc_FrameGetGlobalFrame(), Gia_ManDup(p) );
    if ( Abc_FrameIsBatchMode() )
    {
        if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), pScript) )
        {
            Abc_Print( 1, "Something did not work out with the command \"%s\".\n", pScript );
            return NULL;
        }
    }
    else
    {
        Abc_FrameSetBatchMode( 1 );
        if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), pScript) )
        {
            Abc_Print( 1, "Something did not work out with the command \"%s\".\n", pScript );
            return NULL;
        }
        Abc_FrameSetBatchMode( 0 );
    }
    pTemp = Abc_FrameReadGia(Abc_FrameGetGlobalFrame());
    if ( Gia_ManAndNum(pNew) > Gia_ManAndNum(pTemp) )
    {
        Gia_ManStop( pNew );
        pNew = Gia_ManDup( pTemp );
    }
    return pNew;
}
Vec_Int_t * Gia_StochProcessArray( Vec_Ptr_t * vGias, char * pScript, int TimeSecs, int fVerbose )
{
    Vec_Int_t * vGains = Vec_IntStartFull( Vec_PtrSize(vGias) );
    Gia_Man_t * pGia, * pNew; int i;
    Vec_Int_t * vRands = Vec_IntAlloc( Vec_PtrSize(vGias) ); 
    Abc_Random(1);
    for ( i = 0; i < Vec_PtrSize(vGias); i++ )
        Vec_IntPush( vRands, Abc_Random(0) % 0x1000000 );
    Vec_PtrForEachEntry( Gia_Man_t *, vGias, pGia, i ) 
    {
        pNew = Gia_StochProcessSingle( pGia, pScript, Vec_IntEntry(vRands, i), TimeSecs );
        Vec_IntWriteEntry( vGains, i, Gia_ManAndNum(pGia) - Gia_ManAndNum(pNew) );
        Gia_ManStop( pGia );
        Vec_PtrWriteEntry( vGias, i, pNew );
    }
    Vec_IntFree( vRands );
    return vGains;
}

/**Function*************************************************************

  Synopsis    [Processing on many cores.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_StochProcessOne( Gia_Man_t * p, char * pScript, int Rand, int TimeSecs )
{
    Gia_Man_t * pNew;
    char FileName[100], Command[1000];
    sprintf( FileName, "%06x.aig", Rand );
    Gia_AigerWrite( p, FileName, 0, 0, 0 );
    sprintf( Command, "./abc -q \"&read %s; %s; &write %s\"", FileName, pScript, FileName );
#if defined(__wasm)
    if ( 1 )
#else
    if ( system( (char *)Command ) )    
#endif
    {
        fprintf( stderr, "The following command has returned non-zero exit status:\n" );
        fprintf( stderr, "\"%s\"\n", (char *)Command );
        fprintf( stderr, "Sorry for the inconvenience.\n" );
        fflush( stdout );
        unlink( FileName );
        return Gia_ManDup(p);
    }    
    pNew = Gia_AigerRead( FileName, 0, 0, 0 );
    unlink( FileName );
    if ( pNew && Gia_ManAndNum(pNew) < Gia_ManAndNum(p) )
        return pNew;
    Gia_ManStopP( &pNew );
    return Gia_ManDup(p);
}

/**Function*************************************************************

  Synopsis    [Generic concurrent processing.]

  Description [User-defined problem-specific data and the way to process it.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

typedef struct StochSynData_t_
{
    Gia_Man_t *  pIn;
    Gia_Man_t *  pOut;
    char *       pScript;
    int          Rand;
    int          TimeOut;
} StochSynData_t;

int Gia_StochProcess1( void * p )
{
    StochSynData_t * pData = (StochSynData_t *)p;
    assert( pData->pIn != NULL );
    assert( pData->pOut == NULL );
    pData->pOut = Gia_StochProcessOne( pData->pIn, pData->pScript, pData->Rand, pData->TimeOut );
    return 1;
}

Vec_Int_t * Gia_StochProcess( Vec_Ptr_t * vGias, char * pScript, int nProcs, int TimeSecs, int fVerbose )
{
    if ( nProcs <= 2 ) {
        if ( fVerbose )
            printf( "Running non-concurrent synthesis.\n" ), fflush(stdout);            
        return Gia_StochProcessArray( vGias, pScript, TimeSecs, fVerbose );
    }
    Vec_Int_t * vGains = Vec_IntStartFull( Vec_PtrSize(vGias) );
    StochSynData_t * pData = ABC_CALLOC( StochSynData_t, Vec_PtrSize(vGias) );
    Vec_Ptr_t * vData = Vec_PtrAlloc( Vec_PtrSize(vGias) ); 
    Gia_Man_t * pGia; int i;
    Abc_Random(1);
    Vec_PtrForEachEntry( Gia_Man_t *, vGias, pGia, i ) {
        pData[i].pIn     = pGia;
        pData[i].pOut    = NULL;
        pData[i].pScript = pScript;
        pData[i].Rand    = Abc_Random(0) % 0x1000000;
        pData[i].TimeOut = TimeSecs;
        Vec_PtrPush( vData, pData+i );
    }
    if ( fVerbose )
        printf( "Running concurrent synthesis with %d processes.\n", nProcs ), fflush(stdout);
    Util_ProcessThreads( Gia_StochProcess1, vData, nProcs, TimeSecs, fVerbose );
    // replace old AIGs by new AIGs
    Vec_PtrForEachEntry( Gia_Man_t *, vGias, pGia, i ) {
        Vec_IntWriteEntry( vGains, i, Gia_ManAndNum(pGia) - Gia_ManAndNum(pData[i].pOut) );
        Gia_ManStop( pGia );
        Vec_PtrWriteEntry( vGias, i, pData[i].pOut );
    }
    Vec_PtrFree( vData );
    ABC_FREE( pData );
    return vGains;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManDupMapping( Gia_Man_t * pNew, Gia_Man_t * p )
{
    Gia_Obj_t * pObj, * pFanin; int i, k;
    Vec_Int_t * vMapping = p->vMapping ? Vec_IntAlloc( Vec_IntSize(p->vMapping) ) : NULL;
    if ( p->vMapping == NULL )
        return;
    Vec_IntFill( vMapping, Gia_ManObjNum(p), 0 );
    Gia_ManForEachLut( p, i )
    {
        pObj = Gia_ManObj( p, i );
        Vec_IntWriteEntry( vMapping, Abc_Lit2Var(pObj->Value), Vec_IntSize(vMapping) );
        Vec_IntPush( vMapping, Gia_ObjLutSize(p, i) );
        Gia_LutForEachFaninObj( p, i, pFanin, k )
            Vec_IntPush( vMapping, Abc_Lit2Var(pFanin->Value)  );
        Vec_IntPush( vMapping, Abc_Lit2Var(pObj->Value) );
    }
    pNew->vMapping = vMapping;
}
Gia_Man_t * Gia_ManDupWithMapping( Gia_Man_t * pGia )
{
    Gia_Man_t * pCopy = Gia_ManDup(pGia);
    Gia_ManDupMapping( pCopy, pGia );
    return pCopy;
}
void Gia_ManStochSynthesis( Vec_Ptr_t * vAigs, char * pScript )
{
    Gia_Man_t * pGia, * pNew; int i;
    Vec_PtrForEachEntry( Gia_Man_t *, vAigs, pGia, i )
    {
        Gia_Man_t * pCopy = Gia_ManDupWithMapping(pGia);
        Abc_FrameUpdateGia( Abc_FrameGetGlobalFrame(), pGia );
        if ( Abc_FrameIsBatchMode() )
        {
            if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), pScript) )
            {
                Abc_Print( 1, "Something did not work out with the command \"%s\".\n", pScript );
                return;
            }
        }
        else
        {
            Abc_FrameSetBatchMode( 1 );
            if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), pScript) )
            {
                Abc_Print( 1, "Something did not work out with the command \"%s\".\n", pScript );
                Abc_FrameSetBatchMode( 0 );
                return;
            }
            Abc_FrameSetBatchMode( 0 );
        }
        pNew = Abc_FrameReadGia(Abc_FrameGetGlobalFrame());
        if ( Gia_ManHasMapping(pNew) && Gia_ManHasMapping(pCopy) )
        {
            if ( Gia_ManLutNum(pNew) < Gia_ManLutNum(pCopy) )
            {
                Gia_ManStop( pCopy );
                pCopy = Gia_ManDupWithMapping( pNew );
            }
        }
        else
        {
            if ( Gia_ManAndNum(pNew) < Gia_ManAndNum(pCopy) )
            {
                Gia_ManStop( pCopy );
                pCopy = Gia_ManDup( pNew );
            }
        }
        Vec_PtrWriteEntry( vAigs, i, pCopy );
    }
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManFilterPartitions( Gia_Man_t * p, Vec_Ptr_t * vvIns, Vec_Ptr_t * vvNodes, Vec_Ptr_t * vvOuts, Vec_Ptr_t * vWins, Vec_Int_t * vGains )
{
    int RetValue = Vec_PtrSize(vvIns);
    Vec_Ptr_t * vvInsNew  = Vec_PtrAlloc( 10 );
    Vec_Ptr_t * vvOutsNew = Vec_PtrAlloc( 10 );
    Vec_Ptr_t * vvWinsNew = Vec_PtrAlloc( 10 );
    Gia_ManIncrementTravId( p );
    while ( 1 ) {
        int i, Gain, iEntry = Vec_IntArgMax(vGains);
        if ( iEntry == -1 || Vec_IntEntry(vGains, iEntry) < 0 )
            break;
        //printf( "Selecting partition %d with gain %d.\n", iEntry, Vec_IntEntry(vGains, iEntry) );
        Vec_IntWriteEntry( vGains, iEntry, -1 );
        Vec_PtrPush( vvInsNew,  Vec_IntDup((Vec_Int_t *)Vec_PtrEntry(vvIns,  iEntry)) );
        Vec_PtrPush( vvOutsNew, Vec_IntDup((Vec_Int_t *)Vec_PtrEntry(vvOuts, iEntry)) );
        Vec_PtrPush( vvWinsNew, Gia_ManDupDfs((Gia_Man_t *)Vec_PtrEntry(vWins, iEntry)) );
        extern void Gia_ManMarkTfiTfo( Vec_Int_t * vOne, Gia_Man_t * pMan );
        Gia_ManMarkTfiTfo( (Vec_Int_t *)Vec_PtrEntryLast(vvInsNew), p );
        Vec_IntForEachEntry( vGains, Gain, i ) {
            if ( Gain < 0 )
                continue;
            Vec_Int_t * vNodes  = (Vec_Int_t *)Vec_PtrEntry(vvNodes, i);
            Gia_Obj_t * pNode; int j;
            Gia_ManForEachObjVec( vNodes, p, pNode, j )
                if ( Gia_ObjIsTravIdCurrent(p, pNode) )
                    break;
            if ( j < Vec_IntSize(vNodes) )
                Vec_IntWriteEntry( vGains, i, -1 );
        }         
    }
    ABC_SWAP( Vec_Ptr_t, *vvInsNew,  *vvIns  );
    ABC_SWAP( Vec_Ptr_t, *vvOutsNew, *vvOuts );
    ABC_SWAP( Vec_Ptr_t, *vvWinsNew, *vWins  );
    Vec_PtrFreeFunc( vvInsNew,   (void (*)(void *)) Vec_IntFree );
    Vec_PtrFreeFunc( vvOutsNew,  (void (*)(void *)) Vec_IntFree );           
    Vec_PtrFreeFunc( vvWinsNew,  (void (*)(void *)) Gia_ManStop );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Partitioning.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ObjDfsMark_rec( Gia_Man_t * pGia, Gia_Obj_t * pObj )
{
    assert( !pObj->fMark0 );
    if ( Gia_ObjIsTravIdCurrent( pGia, pObj ) )
        return;
    Gia_ObjSetTravIdCurrent( pGia, pObj );
    if ( Gia_ObjIsCi(pObj) )
        return;
    assert( Gia_ObjIsAnd(pObj) );
    Gia_ObjDfsMark_rec( pGia, Gia_ObjFanin0(pObj) );
    Gia_ObjDfsMark_rec( pGia, Gia_ObjFanin1(pObj) );
}
void Gia_ObjDfsMark2_rec( Gia_Man_t * pGia, Gia_Obj_t * pObj )
{
    Gia_Obj_t * pFanout; int i;
    assert( !pObj->fMark0 );
    if ( Gia_ObjIsTravIdCurrent( pGia, pObj ) )
        return;
    Gia_ObjSetTravIdCurrent( pGia, pObj );    
    Gia_ObjForEachFanoutStatic( pGia, pObj, pFanout, i )
        Gia_ObjDfsMark2_rec( pGia, pFanout );
}
Vec_Int_t * Gia_ManDeriveWinNodes( Gia_Man_t * pMan, Vec_Int_t * vIns, Vec_Wec_t * vStore )
{
    Vec_Int_t * vLevel, * vNodes = Vec_IntAlloc( 100 );
    Gia_Obj_t * pObj, * pNext; int i, k, iLevel;
    Vec_WecForEachLevel( vStore, vLevel, i )
        Vec_IntClear( vLevel );
    // mark the TFI cones of the inputs
    Gia_ManIncrementTravId( pMan );
    Gia_ManForEachObjVec( vIns, pMan, pObj, i )
        Gia_ObjDfsMark_rec( pMan, pObj );
    // add unrelated fanouts of the inputs to storage
    Gia_ManForEachObjVec( vIns, pMan, pObj, i )
        Gia_ObjForEachFanoutStatic( pMan, pObj, pNext, k )
            if ( Gia_ObjIsAnd(pNext) && !Gia_ObjIsTravIdCurrent(pMan, pNext) && !pNext->fMark0 ) {
                pNext->fMark0 = 1;
                Vec_WecPush( vStore, Gia_ObjLevel(pMan, pNext), Gia_ObjId(pMan, pNext) );
            }
    // mark the inputs
    Gia_ManIncrementTravId( pMan );
    Gia_ManForEachObjVec( vIns, pMan, pObj, i )
        Gia_ObjSetTravIdCurrent(pMan, pObj);
    // collect those fanouts that are completely supported by the inputs
    Vec_WecForEachLevel( vStore, vLevel, iLevel )
        Gia_ManForEachObjVec( vLevel, pMan, pObj, i ) {
            assert( !Gia_ObjIsTravIdCurrent(pMan, pObj) );
            assert( pObj->fMark0 );
            pObj->fMark0 = 0;
            if ( !Gia_ObjIsTravIdCurrent(pMan, Gia_ObjFanin0(pObj)) || 
                 !Gia_ObjIsTravIdCurrent(pMan, Gia_ObjFanin1(pObj)) )
                continue;
            Gia_ObjSetTravIdCurrent(pMan, pObj);
            Vec_IntPush( vNodes, Gia_ObjId(pMan, pObj) );
            assert( Gia_ObjIsAnd(pObj) );
            // add fanouts of this node to storage
            Gia_ObjForEachFanoutStatic( pMan, pObj, pNext, k ) 
                if ( Gia_ObjIsAnd(pNext) && !Gia_ObjIsTravIdCurrent(pMan, pNext) && !pNext->fMark0 ) {
                    pNext->fMark0 = 1;
                    assert( Gia_ObjLevel(pMan, pNext) > iLevel );
                    Vec_WecPush( vStore, Gia_ObjLevel(pMan, pNext), Gia_ObjId(pMan, pNext) );
                }
        }
    Vec_IntSort( vNodes, 0 );
    return vNodes;
}
Vec_Ptr_t * Gia_ManDeriveWinNodesAll( Gia_Man_t * pMan, Vec_Ptr_t * vvIns, Vec_Wec_t * vStore )
{
    Vec_Int_t * vIns; int i;
    Vec_Ptr_t * vvNodes = Vec_PtrAlloc( Vec_PtrSize(vvIns) );
    Vec_PtrForEachEntry( Vec_Int_t *, vvIns, vIns, i ) 
        Vec_PtrPush( vvNodes, Gia_ManDeriveWinNodes(pMan, vIns, vStore) );
    return vvNodes;
}
Vec_Int_t * Gia_ManDeriveWinOuts( Gia_Man_t * pMan, Vec_Int_t * vNodes )
{
    Vec_Int_t * vOuts = Vec_IntAlloc( 100 );
    Gia_Obj_t * pObj, * pNext; int i, k;
    // mark the nodes in the window
    Gia_ManIncrementTravId( pMan );
    Gia_ManForEachObjVec( vNodes, pMan, pObj, i )
        Gia_ObjSetTravIdCurrent(pMan, pObj);
    // collect nodes that have unmarked fanouts
    Gia_ManForEachObjVec( vNodes, pMan, pObj, i ) {
        Gia_ObjForEachFanoutStatic( pMan, pObj, pNext, k )
            if ( !Gia_ObjIsTravIdCurrent(pMan, pNext) )
                break;
        if ( k < Gia_ObjFanoutNum(pMan, pObj) )
            Vec_IntPush( vOuts, Gia_ObjId(pMan, pObj) );
    }
    if ( Vec_IntSize(vOuts) == 0 )
        printf( "Window with %d internal nodes has no outputs (are these dangling nodes?).\n", Vec_IntSize(vNodes) );
    return vOuts;
}
Vec_Ptr_t * Gia_ManDeriveWinOutsAll( Gia_Man_t * pMan, Vec_Ptr_t * vvNodes )
{
    Vec_Int_t * vNodes; int i;
    Vec_Ptr_t * vvOuts = Vec_PtrAlloc( Vec_PtrSize(vvNodes) );
    Vec_PtrForEachEntry( Vec_Int_t *, vvNodes, vNodes, i ) 
        Vec_PtrPush( vvOuts, Gia_ManDeriveWinOuts(pMan, vNodes) );
    return vvOuts;
}
void Gia_ManPermuteLevel( Gia_Man_t * pMan, int Level )
{
    Gia_Obj_t * pObj, * pNext; int i, k;
    Gia_ManForEachAnd( pMan, pObj, i ) {
        int LevelMin = Gia_ObjLevel(pMan, pObj), LevelMax = Level + 1;
        Gia_ObjForEachFanoutStatic( pMan, pObj, pNext, k )
            if ( Gia_ObjIsAnd(pNext) )
                LevelMax = Abc_MinInt( LevelMax, Gia_ObjLevel(pMan, pNext) );
        if ( LevelMin == LevelMax ) continue;
        assert( LevelMin < LevelMax );
        // randomly set level between LevelMin and LevelMax-1
        Gia_ObjSetLevel( pMan, pObj, LevelMin + (Abc_Random(0) % (LevelMax - LevelMin)) );
        assert( Gia_ObjLevel(pMan, pObj) < LevelMax );
    }
}
Vec_Int_t * Gia_ManCollectObjectsPointedTo( Gia_Man_t * pMan, int Level )
{
    Vec_Int_t * vRes = Vec_IntAlloc( 100 ); 
    Gia_Obj_t * pObj, * pFanin; int i, n;
    Gia_ManIncrementTravId( pMan );
    Gia_ManForEachAnd( pMan, pObj, i ) {
        if ( Gia_ObjLevel(pMan, pObj) <= Level )
            continue;
        for ( n = 0; n < 2; n++ ) {
            Gia_Obj_t * pFanin = n ? Gia_ObjFanin1(pObj) : Gia_ObjFanin0(pObj);
            if ( Gia_ObjLevel(pMan, pFanin) <= Level && !Gia_ObjIsTravIdCurrent(pMan, pFanin) ) {
                Gia_ObjSetTravIdCurrent(pMan, pFanin);
                Vec_IntPush( vRes, Gia_ObjId(pMan, pFanin) );
            }
        }
    }
    Gia_ManForEachCo( pMan, pObj, i ) {
        pFanin = Gia_ObjFanin0(pObj);
        if ( Gia_ObjLevel(pMan, pFanin) <= Level && !Gia_ObjIsTravIdCurrent(pMan, pFanin) && Gia_ObjIsAnd(pFanin) ) {
            Gia_ObjSetTravIdCurrent(pMan, pFanin);
            Vec_IntPush( vRes, Gia_ObjId(pMan, pFanin) );
        }
    }
    Vec_IntSort( vRes, 0 );
    return vRes;
}
Vec_Wec_t * Gia_ManCollectObjectsWithSuppLimit( Gia_Man_t * pMan, int Level, int nSuppMax )
{
    Vec_Wec_t * vResSupps = NULL;
    Vec_Int_t * vBelow   = Gia_ManCollectObjectsPointedTo( pMan, Level );
    Vec_Wec_t * vSupps   = Vec_WecStart( Vec_IntSize(vBelow) );
    Vec_Int_t * vSuppIds = Vec_IntStartFull( Gia_ManObjNum(pMan) );
    Vec_Int_t * vTemp    = Vec_IntAlloc(100);
    Gia_Obj_t * pObj; int i, Count = 0;
    Gia_ManForEachObjVec( vBelow, pMan, pObj, i ) {
        Vec_IntWriteEntry( vSuppIds, Gia_ObjId(pMan, pObj), i );
        Vec_IntPush( Vec_WecEntry(vSupps, i), Gia_ObjId(pMan, pObj) );
    }
    Gia_ManForEachAnd( pMan, pObj, i ) {
        if ( Gia_ObjLevel(pMan, pObj) <= Level )
            continue;
        int iSuppId0 = Vec_IntEntry( vSuppIds, Gia_ObjFaninId0(pObj, i) );
        int iSuppId1 = Vec_IntEntry( vSuppIds, Gia_ObjFaninId1(pObj, i) );
        if ( iSuppId0 == -1 || iSuppId1 == -1 ) {
            Count++;
            continue;
        }
        Vec_IntClear( vTemp );
        Vec_IntTwoMerge2( Vec_WecEntry(vSupps, iSuppId0), Vec_WecEntry(vSupps, iSuppId1), vTemp );
        if ( Vec_IntSize(vTemp) > nSuppMax ) {
            Count++;
            continue;
        }
        Vec_IntWriteEntry( vSuppIds, i, Vec_WecSize(vSupps) );
        Vec_IntAppend( Vec_WecPushLevel(vSupps), vTemp );
    }
    // remove those supported nodes that are in the TFI cones of others
    Gia_ManIncrementTravId( pMan );
    Gia_ManForEachAnd( pMan, pObj, i )
        if ( Gia_ObjLevel(pMan, pObj) > Level && Vec_IntEntry(vSuppIds, i) >= 0 && !Gia_ObjIsTravIdCurrent(pMan, pObj) ) {
            Gia_ObjDfsMark_rec(pMan, pObj);
            Gia_ObjSetTravIdPrevious(pMan, pObj);
        }
    // create the result
    vResSupps = Vec_WecAlloc( 100 );
    Gia_ManForEachAnd( pMan, pObj, i )
        if ( Gia_ObjLevel(pMan, pObj) > Level && Vec_IntEntry(vSuppIds, i) >= 0 && !Gia_ObjIsTravIdCurrent(pMan, pObj) ) {
            Vec_Int_t * vSupp = Vec_WecEntry( vSupps, Vec_IntEntry(vSuppIds, i) );
            if ( Vec_IntSize(vSupp) < 4 )
                continue;
            Vec_Int_t * vThis = Vec_WecPushLevel( vResSupps );
            Vec_IntGrow( vThis, Vec_IntSize(vSupp) + 1 );
            Vec_IntAppend( vThis, vSupp );
            //Vec_IntPush( vThis, Gia_ObjId(pObj) );
        }
    //printf( "Inputs = %d. Nodes with %d-support = %d. Nodes with larger support = %d. Selected outputs = %d.\n", 
    //    Vec_IntSize(vBelow), nSuppMax, Vec_WecSize(vSupps), Count, Vec_WecSize(vResSupps) );
    Vec_WecFree( vSupps );
    Vec_IntFree( vSuppIds );
    Vec_IntFree( vBelow );
    Vec_IntFree( vTemp );
    return vResSupps;
}
// removes all supports that overlap with this one
void Gia_ManSelectRemove( Vec_Wec_t * vSupps, Vec_Int_t * vOne )
{
    Vec_Int_t * vLevel; int i;
    Vec_WecForEachLevel( vSupps, vLevel, i ) 
        if ( Vec_IntTwoCountCommon(vLevel, vOne) > 0 )
            Vec_IntClear( vLevel );
    Vec_WecRemoveEmpty( vSupps );
}
// marks TFI/TFO of this one
void Gia_ManMarkTfiTfo( Vec_Int_t * vOne, Gia_Man_t * pMan )
{
    int i; Gia_Obj_t * pObj;
    Gia_ManForEachObjVec( vOne, pMan, pObj, i ) {
        //Gia_ObjSetTravIdPrevious(pMan, pObj);
        //Gia_ObjDfsMark_rec( pMan, pObj );
        Gia_ObjSetTravIdPrevious(pMan, pObj);
        Gia_ObjDfsMark2_rec( pMan, pObj );
    }
}
// removes all supports that overlap with the TFI/TFO cones of this one
void Gia_ManSelectRemove2( Vec_Wec_t * vSupps, Vec_Int_t * vOne, Gia_Man_t * pMan )
{
    Vec_Int_t * vLevel; int i, k; Gia_Obj_t * pObj;
    Gia_ManForEachObjVec( vOne, pMan, pObj, i ) {
        Gia_ObjSetTravIdPrevious(pMan, pObj);
        Gia_ObjDfsMark_rec( pMan, pObj );
        Gia_ObjSetTravIdPrevious(pMan, pObj);
        Gia_ObjDfsMark2_rec( pMan, pObj );
    }
    Vec_WecForEachLevel( vSupps, vLevel, i ) {
        Gia_ManForEachObjVec( vLevel, pMan, pObj, k ) 
            if ( Gia_ObjIsTravIdCurrent(pMan, pObj) )
                break;
        if ( k < Vec_IntSize(vLevel) )
            Vec_IntClear( vLevel );
    }
    Vec_WecRemoveEmpty( vSupps );
}
// removes all supports that are contained in this one
void Gia_ManSelectRemove3( Vec_Wec_t * vSupps, Vec_Int_t * vOne )
{
    Vec_Int_t * vLevel; int i;
    Vec_WecForEachLevel( vSupps, vLevel, i )
        if ( Vec_IntTwoCountCommon(vLevel, vOne) == Vec_IntSize(vLevel) )
            Vec_IntClear( vLevel );
    Vec_WecRemoveEmpty( vSupps );
}
Vec_Ptr_t * Gia_ManDeriveWinInsAll( Vec_Wec_t * vSupps, int nSuppMax, Gia_Man_t * pMan, int fOverlap )
{
    Vec_Ptr_t * vRes = Vec_PtrAlloc( 100 );
    Gia_ManIncrementTravId( pMan );
    while ( Vec_WecSize(vSupps) > 0 ) {
        int i, Item, iRand = Abc_Random(0) % Vec_WecSize(vSupps);
        Vec_Int_t * vLevel, * vLevel2 = Vec_WecEntry( vSupps, iRand );
        Vec_Int_t * vCopy = Vec_IntDup( vLevel2 );
        if ( Vec_IntSize(vLevel2) == nSuppMax ) {
            Vec_PtrPush( vRes, vCopy );
            if ( fOverlap )
                Gia_ManSelectRemove3( vSupps, vCopy );
            else
                Gia_ManSelectRemove2( vSupps, vCopy, pMan );
            continue;
        }
        // find another support, which maximizes the union but does not exceed nSuppMax
        int iBest = iRand, nUnion = Vec_IntSize(vCopy);
        Vec_WecForEachLevel( vSupps, vLevel, i ) {
            if ( i == iRand ) continue;
            int nCommon = Vec_IntTwoCountCommon(vLevel, vCopy);
            int nUnionCur = Vec_IntSize(vLevel) + Vec_IntSize(vCopy) - nCommon;
            if ( nUnionCur <= nSuppMax && nUnion < nUnionCur ) {
                nUnion = nUnionCur;
                iBest = i;
            }
        }
        vLevel = Vec_WecEntry( vSupps, iBest );
        Vec_IntForEachEntry( vLevel, Item, i )
            Vec_IntPushUniqueOrder( vCopy, Item );
        Vec_PtrPush( vRes, vCopy );
        if ( fOverlap )
            Gia_ManSelectRemove3( vSupps, vCopy );
        else
            Gia_ManSelectRemove2( vSupps, vCopy, pMan );
    }
    return vRes;
}
Gia_Man_t * Gia_ManDupFromArrays( Gia_Man_t * p, Vec_Int_t * vCis, Vec_Int_t * vAnds, Vec_Int_t * vCos )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i;
    pNew = Gia_ManStart( 5000 );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachObjVec( vCis, p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachObjVec( vAnds, p, pObj, i )
        pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachObjVec( vCos, p, pObj, i )
        pObj->Value = Gia_ManAppendCo( pNew, pObj->Value );
    return pNew;
}
Vec_Ptr_t * Gia_ManDupWindows( Gia_Man_t * pMan, Vec_Ptr_t * vvIns, Vec_Ptr_t * vvNodes, Vec_Ptr_t * vvOuts )
{
    Vec_Int_t * vNodes; int i;
    Vec_Ptr_t * vWins = Vec_PtrAlloc( Vec_PtrSize(vvIns) );
    assert( Vec_PtrSize(vvIns)  == Vec_PtrSize(vvNodes) );
    assert( Vec_PtrSize(vvOuts) == Vec_PtrSize(vvNodes) );
    Gia_ManFillValue( pMan );
    Gia_ManCleanMark01( pMan );
    Vec_PtrForEachEntry( Vec_Int_t *, vvNodes, vNodes, i ) {
        Vec_Int_t * vIns  = (Vec_Int_t *)Vec_PtrEntry(vvIns, i);
        Vec_Int_t * vOuts = (Vec_Int_t *)Vec_PtrEntry(vvOuts, i);
        Gia_Man_t * pNew  = Gia_ManDupFromArrays( pMan, vIns, vNodes, vOuts );
        Vec_PtrPush( vWins, pNew );
    }
    return vWins;
}
int Gia_ManLevelR( Gia_Man_t * pMan )
{
    int i, LevelMax = Gia_ManLevelRNum( pMan );
    Gia_Obj_t * pNode;
    Gia_ManForEachObj( pMan, pNode, i )
        Gia_ObjSetLevel( pMan, pNode, (int)(LevelMax - Gia_ObjLevel(pMan, pNode) + 1) );
    Gia_ManForEachCi( pMan, pNode, i )
        Gia_ObjSetLevel( pMan, pNode, 0 );
    return LevelMax;
}
Vec_Ptr_t * Gia_ManExtractPartitions( Gia_Man_t * pMan, int Iter, int nSuppMax, Vec_Ptr_t ** pvIns, Vec_Ptr_t ** pvOuts, Vec_Ptr_t ** pvNodes, int fOverlap )
{
    // if ( Gia_ManCiNum(pMan) <= nSuppMax ) {
    //     Vec_Ptr_t * vWins = Vec_PtrAlloc( 1 );
    //     Vec_PtrPush( vWins, Gia_ManDupDfs(pMan) );
    //     *pvIns = *pvOuts = *pvNodes = NULL;
    //     return vWins;
    // }
    // int iUseRevL = Iter % 3 == 0 ? 0 : Abc_Random(0) & 1;
    int iUseRevL = Abc_Random(0) & 1;
    int LevelMax = iUseRevL ? Gia_ManLevelR(pMan) : Gia_ManLevelNum(pMan);
    // int LevelCut = Iter % 3 == 0 ? 0 : LevelMax > 8 ? 2 + (Abc_Random(0) % (LevelMax - 4)) : 0;
    int LevelCut = LevelMax > 8 ? (Abc_Random(0) % (LevelMax - 4)) : 0;
    //printf( "Using %s cut level %d (out of %d)\n", iUseRevL ? "reverse": "direct", LevelCut, LevelMax );
    // Gia_ManPermuteLevel( pMan, LevelMax );
    Vec_Wec_t * vStore = Vec_WecStart( LevelMax+1 );
    Vec_Wec_t * vSupps = Gia_ManCollectObjectsWithSuppLimit( pMan, LevelCut, nSuppMax );
    Vec_Ptr_t * vIns   = Gia_ManDeriveWinInsAll( vSupps, nSuppMax, pMan, fOverlap );
    Vec_Ptr_t * vNodes = Gia_ManDeriveWinNodesAll( pMan, vIns, vStore );
    Vec_Ptr_t * vOuts  = Gia_ManDeriveWinOutsAll( pMan, vNodes );
    Vec_Ptr_t * vWins  = Gia_ManDupWindows( pMan, vIns, vNodes, vOuts );
    Vec_WecFree( vSupps );
    Vec_WecFree( vStore );
    *pvIns = vIns;
    *pvOuts = vOuts;
    *pvNodes = vNodes;
    return vWins;
}



/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCollectNodes_rec( Gia_Man_t * p, int iObj, Vec_Int_t * vAnds )
{
    Gia_Obj_t * pObj;
    if ( Gia_ObjUpdateTravIdCurrentId( p, iObj ) )
        return;
    pObj = Gia_ManObj( p, iObj );
    if ( Gia_ObjIsCi(pObj) || iObj == 0 )
        return;
    assert( Gia_ObjIsAnd(pObj) );
    Gia_ManCollectNodes_rec( p, Gia_ObjFaninId0(pObj, iObj), vAnds );
    Gia_ManCollectNodes_rec( p, Gia_ObjFaninId1(pObj, iObj), vAnds );
    Vec_IntPush( vAnds, iObj );
}
void Gia_ManCollectNodes( Gia_Man_t * p, Vec_Int_t * vCis, Vec_Int_t * vAnds, Vec_Int_t * vCos )
{
    int i, iObj;
    if ( !Gia_ManHasMapping(p) )
        return;
    Vec_IntClear( vAnds );
    Gia_ManIncrementTravId( p );
    Vec_IntForEachEntry( vCis, iObj, i )
        Gia_ObjSetTravIdCurrentId( p, iObj );
    Vec_IntForEachEntry( vCos, iObj, i )
        Gia_ManCollectNodes_rec( p, iObj, vAnds );
}
Gia_Man_t * Gia_ManDupDivideOne( Gia_Man_t * p, Vec_Int_t * vCis, Vec_Int_t * vAnds, Vec_Int_t * vCos )
{
    Vec_Int_t * vMapping; int i;
    Gia_Man_t * pNew; Gia_Obj_t * pObj; 
    pNew = Gia_ManStart( 1+Vec_IntSize(vCis)+Vec_IntSize(vAnds)+Vec_IntSize(vCos) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    Gia_ManFillValue(p);
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachObjVec( vCis, p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachObjVec( vAnds, p, pObj, i )
        pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachObjVec( vCos, p, pObj, i )
        Gia_ManAppendCo( pNew, pObj->Value );
    assert( Gia_ManCiNum(pNew) > 0 && Gia_ManCoNum(pNew) > 0 );
    if ( !Gia_ManHasMapping(p) )
        return pNew;
    vMapping = Vec_IntAlloc( 4*Gia_ManObjNum(pNew) );
    Vec_IntFill( vMapping, Gia_ManObjNum(pNew), 0 );
    Gia_ManForEachObjVec( vAnds, p, pObj, i )
    {
        Gia_Obj_t * pFanin; int k; 
        int iObj = Gia_ObjId(p, pObj);
        if ( !Gia_ObjIsLut(p, iObj) )
            continue;
        Vec_IntWriteEntry( vMapping, Abc_Lit2Var(pObj->Value), Vec_IntSize(vMapping) );
        Vec_IntPush( vMapping, Gia_ObjLutSize(p, iObj) );
        Gia_LutForEachFaninObj( p, iObj, pFanin, k )
            Vec_IntPush( vMapping, Abc_Lit2Var(pFanin->Value)  );
        Vec_IntPush( vMapping, Abc_Lit2Var(pObj->Value) );
    }
    pNew->vMapping = vMapping;
    return pNew;
}
Vec_Ptr_t * Gia_ManDupDivide( Gia_Man_t * p, Vec_Wec_t * vCis, Vec_Wec_t * vAnds, Vec_Wec_t * vCos, char * pScript, int nProcs, int TimeOut )
{
    Vec_Ptr_t * vAigs = Vec_PtrAlloc( Vec_WecSize(vCis) );  int i;
    for ( i = 0; i < Vec_WecSize(vCis); i++ )
    {
        Gia_ManCollectNodes( p, Vec_WecEntry(vCis, i), Vec_WecEntry(vAnds, i), Vec_WecEntry(vCos, i) );
        Vec_PtrPush( vAigs, Gia_ManDupDivideOne(p, Vec_WecEntry(vCis, i), Vec_WecEntry(vAnds, i), Vec_WecEntry(vCos, i)) );
    }
    //Gia_ManStochSynthesis( vAigs, pScript );
    Vec_Int_t * vGains = Gia_StochProcess( vAigs, pScript, nProcs, TimeOut, 0 );
    Vec_IntFree( vGains );
    return vAigs;
}
Gia_Man_t * Gia_ManDupStitch( Gia_Man_t * p, Vec_Wec_t * vCis, Vec_Wec_t * vAnds, Vec_Wec_t * vCos, Vec_Ptr_t * vAigs, int fHash )
{
    Gia_Man_t * pGia, * pNew;
    Gia_Obj_t * pObj; int i, k;
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManCleanValue( p );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    if ( fHash )
        Gia_ManHashAlloc( pNew );
    Vec_PtrForEachEntry( Gia_Man_t *, vAigs, pGia, i )
    {
        Vec_Int_t * vCi = Vec_WecEntry( vCis, i );
        Vec_Int_t * vCo = Vec_WecEntry( vCos, i );
        Gia_ManCleanValue( pGia );
        Gia_ManConst0(pGia)->Value = 0;
        Gia_ManForEachObjVec( vCi, p, pObj, k )
            Gia_ManCi(pGia, k)->Value = pObj->Value;
        if ( fHash )
            Gia_ManForEachAnd( pGia, pObj, k )
                pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) ); 
        else
            Gia_ManForEachAnd( pGia, pObj, k )
                pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) ); 
        Gia_ManForEachObjVec( vCo, p, pObj, k )
            pObj->Value = Gia_ObjFanin0Copy(Gia_ManCo(pGia, k));
    }
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    if ( fHash )
    {
        pNew = Gia_ManCleanup( pGia = pNew );
        Gia_ManStop( pGia );
    }
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    return pNew;
}
Gia_Man_t * Gia_ManDupStitchMap( Gia_Man_t * p, Vec_Wec_t * vCis, Vec_Wec_t * vAnds, Vec_Wec_t * vCos, Vec_Ptr_t * vAigs )
{
    Vec_Int_t * vMapping; int n;
    Gia_Man_t * pGia, * pNew = Gia_ManDupStitch( p, vCis, vAnds, vCos, vAigs, !Gia_ManHasMapping(p) ); 
    if ( !Gia_ManHasMapping(p) )
        return pNew;
    vMapping = Vec_IntAlloc( Vec_IntSize(p->vMapping) );
    Vec_IntFill( vMapping, Gia_ManObjNum(pNew), 0 );
    Vec_PtrForEachEntry( Gia_Man_t *, vAigs, pGia, n )
    {
        Gia_Obj_t * pFanin; int iObj, k; 
        //printf( "Gia %d has %d Luts\n", n, Gia_ManLutNum(pGia) );

        Gia_ManForEachLut( pGia, iObj )
        {
            Gia_Obj_t * pObj = Gia_ManObj( pGia, iObj );
            Vec_IntWriteEntry( vMapping, Abc_Lit2Var(pObj->Value), Vec_IntSize(vMapping) );
            Vec_IntPush( vMapping, Gia_ObjLutSize(pGia, iObj) );
            Gia_LutForEachFaninObj( pGia, iObj, pFanin, k )
                Vec_IntPush( vMapping, Abc_Lit2Var(pFanin->Value)  );
            Vec_IntPush( vMapping, Abc_Lit2Var(pObj->Value) );
        }
    }
    pNew->vMapping = vMapping;
    return pNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Wec_t * Gia_ManStochNodes( Gia_Man_t * p, int nMaxSize, int Seed )
{
    Vec_Wec_t * vRes = Vec_WecAlloc( 100 ); 
    Vec_Int_t * vPart = Vec_WecPushLevel( vRes );
    int i, iStart = Seed % Gia_ManCoNum(p);
    //Gia_ManLevelNum( p );
    Gia_ManIncrementTravId( p );
    for ( i = 0; i < Gia_ManCoNum(p); i++ )
    {
        Gia_Obj_t * pObj = Gia_ManCo( p, (iStart+i) % Gia_ManCoNum(p) );
        if ( Vec_IntSize(vPart) > nMaxSize )
            vPart = Vec_WecPushLevel( vRes );
        Gia_ManCollectNodes_rec( p, Gia_ObjFaninId0p(p, pObj), vPart );
    }
    if ( Vec_IntSize(vPart) == 0 )
        Vec_WecShrink( vRes, Vec_WecSize(vRes)-1 );
    //Vec_WecPrint( vRes, 0 );
    return vRes;
}
Vec_Wec_t * Gia_ManStochInputs( Gia_Man_t * p, Vec_Wec_t * vAnds )
{
    Vec_Wec_t * vRes = Vec_WecAlloc( 100 ); 
    Vec_Int_t * vLevel; Gia_Obj_t * pObj; int i, k, iObj, iFan, f;
    Vec_WecForEachLevel( vAnds, vLevel, i )
    {
        Vec_Int_t * vVec = Vec_WecPushLevel( vRes );
        assert( Vec_IntSize(vVec) == 0 );
        Gia_ManIncrementTravId( p );
        Vec_IntForEachEntry( vLevel, iObj, k )
            Gia_ObjSetTravIdCurrentId( p, iObj );
        if ( Gia_ManHasMapping(p) )
        {
            Vec_IntForEachEntry( vLevel, iObj, k )
                if ( Gia_ObjIsLut(p, iObj) )
                    Gia_LutForEachFanin( p, iObj, iFan, f )
                        if ( !Gia_ObjUpdateTravIdCurrentId(p, iFan) )
                            Vec_IntPush( vVec, iFan );
        }
        else
        {
            Gia_ManForEachObjVec( vLevel, p, pObj, k )
            {
                iObj = Gia_ObjFaninId0p(p, pObj);
                if ( !Gia_ObjUpdateTravIdCurrentId(p, iObj) )
                    Vec_IntPush( vVec, iObj );
                iObj = Gia_ObjFaninId1p(p, pObj);
                if ( !Gia_ObjUpdateTravIdCurrentId(p, iObj) )
                    Vec_IntPush( vVec, iObj );
            }
        }
        assert( Vec_IntSize(vVec) > 0 );
    }
    return vRes;
}
Vec_Wec_t * Gia_ManStochOutputs( Gia_Man_t * p, Vec_Wec_t * vAnds )
{
    Vec_Wec_t * vRes = Vec_WecAlloc( 100 ); 
    Vec_Int_t * vLevel; Gia_Obj_t * pObj; int i, k, iObj, iFan, f;
    if ( Gia_ManHasMapping(p) )
    {
        Gia_ManSetLutRefs( p );
        Vec_WecForEachLevel( vAnds, vLevel, i )
        {
            Vec_Int_t * vVec = Vec_WecPushLevel( vRes );
            assert( Vec_IntSize(vVec) == 0 );
            Vec_IntForEachEntry( vLevel, iObj, k )
                if ( Gia_ObjIsLut(p, iObj) )
                    Gia_LutForEachFanin( p, iObj, iFan, f )
                        Gia_ObjLutRefDecId( p, iFan );
            Vec_IntForEachEntry( vLevel, iObj, k )
                if ( Gia_ObjIsLut(p, iObj) )
                    if ( Gia_ObjLutRefNumId(p, iObj) )
                        Vec_IntPush( vVec, iObj );
            Vec_IntForEachEntry( vLevel, iObj, k )
                if ( Gia_ObjIsLut(p, iObj) )
                    Gia_LutForEachFanin( p, iObj, iFan, f )
                        Gia_ObjLutRefIncId( p, iFan );
            assert( Vec_IntSize(vVec) > 0 );
        }
    }
    else
    {
        Gia_ManCreateRefs( p );
        Vec_WecForEachLevel( vAnds, vLevel, i )
        {
            Vec_Int_t * vVec = Vec_WecPushLevel( vRes );
            Gia_ManForEachObjVec( vLevel, p, pObj, k )
            {
                Gia_ObjRefDecId( p, Gia_ObjFaninId0p(p, pObj) );
                Gia_ObjRefDecId( p, Gia_ObjFaninId1p(p, pObj) );
            }
            Gia_ManForEachObjVec( vLevel, p, pObj, k )
                if ( Gia_ObjRefNum(p, pObj) )
                    Vec_IntPush( vVec, Gia_ObjId(p, pObj) );
            Gia_ManForEachObjVec( vLevel, p, pObj, k )
            {
                Gia_ObjRefIncId( p, Gia_ObjFaninId0p(p, pObj) );
                Gia_ObjRefIncId( p, Gia_ObjFaninId1p(p, pObj) );
            }
        }
    }
    return vRes;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManStochSyn( int nSuppMax, int nMaxSize, int nIters, int TimeOut, int Seed, int fVerbose, char * pScript, int nProcs )
{
    abctime nTimeToStop  = TimeOut ? Abc_Clock() + TimeOut * CLOCKS_PER_SEC : 0;
    abctime clkStart     = Abc_Clock();
    int fMapped          = Gia_ManHasMapping(Abc_FrameReadGia(Abc_FrameGetGlobalFrame()));
    int nLutEnd, nLutBeg = fMapped ? Gia_ManLutNum(Abc_FrameReadGia(Abc_FrameGetGlobalFrame())) : 0;
    int i, nEnd, nBeg    = Gia_ManAndNum(Abc_FrameReadGia(Abc_FrameGetGlobalFrame()));
    Abc_Random(1);
    for ( i = 0; i < 10+Seed; i++ )
        Abc_Random(0);
    if ( fVerbose ) {
        printf( "Running %d iterations of the script \"%s\"", nIters, pScript );
        if ( nProcs > 2 )
            printf( " using %d concurrent threads.\n", nProcs-1 );
        else
            printf( " without concurrency.\n" );
        fflush(stdout);
    }
    if ( !nSuppMax ) {
        for ( i = 0; i < nIters; i++ )
        {
            abctime clk = Abc_Clock();
            Gia_Man_t * pGia  = Gia_ManDupWithMapping( Abc_FrameReadGia(Abc_FrameGetGlobalFrame()) );
            Vec_Wec_t * vAnds = Gia_ManStochNodes( pGia, nMaxSize, Abc_Random(0) & 0x7FFFFFFF );
            Vec_Wec_t * vIns  = Gia_ManStochInputs( pGia, vAnds );
            Vec_Wec_t * vOuts = Gia_ManStochOutputs( pGia, vAnds );
            Vec_Ptr_t * vAigs = Gia_ManDupDivide( pGia, vIns, vAnds, vOuts, pScript, nProcs, TimeOut );
            Gia_Man_t * pNew  = Gia_ManDupStitchMap( pGia, vIns, vAnds, vOuts, vAigs );
            int fMapped = Gia_ManHasMapping(pGia) && Gia_ManHasMapping(pNew);
            Abc_FrameUpdateGia( Abc_FrameGetGlobalFrame(), pNew );
            if ( fVerbose )
            printf( "Iteration %3d : Using %3d partitions. Reducing %6d to %6d %s.  ", 
                i, Vec_PtrSize(vAigs), fMapped ? Gia_ManLutNum(pGia) : Gia_ManAndNum(pGia), 
                                    fMapped ? Gia_ManLutNum(pNew) : Gia_ManAndNum(pNew),
                                    fMapped ? "LUTs" : "ANDs" ); 
            if ( fVerbose )
            Abc_PrintTime( 0, "Time", Abc_Clock() - clk );
            Gia_ManStop( pGia );
            Vec_PtrFreeFunc( vAigs, (void (*)(void *)) Gia_ManStop );
            Vec_WecFree( vAnds );
            Vec_WecFree( vIns );
            Vec_WecFree( vOuts );
            if ( nTimeToStop && Abc_Clock() > nTimeToStop )
            {
                printf( "Runtime limit (%d sec) is reached after %d iterations.\n", TimeOut, i );
                break;
            }
        }
    }
    else {
        int fOverlap = 1;
        Vec_Ptr_t * vIns = NULL, * vOuts = NULL, * vNodes = NULL;
        for ( i = 0; i < nIters; i++ )
        {
            extern Gia_Man_t * Gia_ManDupInsertWindows( Gia_Man_t * p, Vec_Ptr_t * vvIns, Vec_Ptr_t * vvOuts, Vec_Ptr_t * vAigs );
            abctime clk        = Abc_Clock();
            Gia_Man_t * pGia   = Gia_ManDup( Abc_FrameReadGia(Abc_FrameGetGlobalFrame()) ); Gia_ManStaticFanoutStart(pGia);
            Vec_Ptr_t * vAigs  = Gia_ManExtractPartitions( pGia, i, nSuppMax, &vIns, &vOuts, &vNodes, fOverlap );
            Vec_Int_t * vGains = Gia_StochProcess( vAigs, pScript, nProcs, TimeOut, 0 );
            int nPartsInit     = fOverlap ? Gia_ManFilterPartitions( pGia, vIns, vNodes, vOuts, vAigs, vGains ) : Vec_PtrSize(vIns);
            Gia_Man_t * pNew   = Gia_ManDupInsertWindows( pGia, vIns, vOuts, vAigs );       Gia_ManStaticFanoutStop(pGia);
            Abc_FrameUpdateGia( Abc_FrameGetGlobalFrame(), pNew );
            if ( fVerbose )
            printf( "Iteration %3d : Using %3d -> %3d partitions. Reducing node count from %6d to %6d.  ", 
                i, nPartsInit, Vec_PtrSize(vAigs), Gia_ManAndNum(pGia), Gia_ManAndNum(pNew) ); 
            if ( fVerbose )
            Abc_PrintTime( 0, "Time", Abc_Clock() - clk );
            // cleanup
            Gia_ManStop( pGia );
            Vec_PtrFreeFunc( vAigs,  (void (*)(void *)) Gia_ManStop );
            Vec_IntFreeP( &vGains );
            if ( vIns )   Vec_PtrFreeFunc( vIns,   (void (*)(void *)) Vec_IntFree );
            if ( vOuts )  Vec_PtrFreeFunc( vOuts,  (void (*)(void *)) Vec_IntFree );                
            if ( vNodes ) Vec_PtrFreeFunc( vNodes, (void (*)(void *)) Vec_IntFree );                
            if ( nTimeToStop && Abc_Clock() > nTimeToStop )
            {
                printf( "Runtime limit (%d sec) is reached after %d iterations.\n", TimeOut, i );
                break;
            }
        }
    }
    fMapped &= Gia_ManHasMapping(Abc_FrameReadGia(Abc_FrameGetGlobalFrame()));
    nLutEnd  = fMapped ? Gia_ManLutNum(Abc_FrameReadGia(Abc_FrameGetGlobalFrame())) : 0;
    nEnd     = Gia_ManAndNum(Abc_FrameReadGia(Abc_FrameGetGlobalFrame()));
    if ( fVerbose )
    printf( "Cumulatively reduced %d %s (%.2f %%) after %d iterations.  ", 
        fMapped ? nLutBeg - nLutEnd : nBeg - nEnd, fMapped ? "LUTs" : "nodes", 100.0*(nBeg - nEnd)/Abc_MaxInt(nBeg, 1), nIters );
    if ( fVerbose )
    Abc_PrintTime( 0, "Total time", Abc_Clock() - clkStart );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

