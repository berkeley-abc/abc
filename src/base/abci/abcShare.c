/**CFile****************************************************************

  FileName    [abcShare.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Shared logic extraction.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcShare.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "src/base/abc/abc.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define SHARE_NUM 2

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

static inline word  Abc_NtkSharePack( int Lev, int Id )   { return (((word)Lev) << 32) | Id;    }
static inline int   Abc_NtkShareUnpackLev( word Num )     { return (Num >> 32);                 }
static inline int   Abc_NtkShareUnpackId( word Num )      { return Num & 0xFFFF;                }

/**Function*************************************************************

  Synopsis    [Collects one multi-input XOR.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Wrd_t * Abc_NtkShareSuperXor( Abc_Obj_t * pObjInit, int * pfCompl )
{
    int fCompl = Abc_ObjIsComplement(pObjInit);
    Abc_Obj_t * pObj = Abc_ObjRegular(pObjInit);
    Abc_Ntk_t * pNtk = Abc_ObjNtk(pObj);
    Abc_Obj_t * pObjC, * pObj0, * pObj1, * pRoot;
    Vec_Wrd_t * vSuper;
    word Num, NumNext;
    int i, k;
    assert( Abc_NodeIsExorType(pObj) );
    // start iteration
    vSuper = Vec_WrdAlloc( 10 );
    Vec_WrdPush( vSuper, Abc_NtkSharePack(Abc_ObjLevel(pObj), Abc_ObjId(pObj)) );
    while ( Vec_WrdSize(vSuper) > 0 )
    {
        // make sure there are no duplicates
        Num = Vec_WrdEntry( vSuper, 0 );
        Vec_WrdForEachEntryStart( vSuper, NumNext, i, 1 )
        {
            assert( Num != NumNext );
            Num = NumNext;
        }
        // extract XOR gate decomposable on the topmost level
        Vec_WrdForEachEntryReverse( vSuper, Num, i )
        {
            pRoot = Abc_NtkObj( pNtk, Abc_NtkShareUnpackId(Num) );
            if ( Abc_NodeIsExorType(pRoot) )
            {
                Vec_WrdRemove( vSuper, Num );
                break;
            }
        }
        if ( i == -1 )
            break;
        // extract
        pObjC = Abc_NodeRecognizeMux( pRoot, &pObj1, &pObj0 );
        assert( pObj1 == Abc_ObjNot(pObj0) );
        fCompl ^= Abc_ObjIsComplement(pObjC);  pObjC = Abc_ObjRegular(pObjC);
        fCompl ^= Abc_ObjIsComplement(pObj0);  pObj0 = Abc_ObjRegular(pObj0);
        Vec_WrdPushOrder( vSuper, Abc_NtkSharePack(Abc_ObjLevel(pObjC), Abc_ObjId(pObjC)) );
        Vec_WrdPushOrder( vSuper, Abc_NtkSharePack(Abc_ObjLevel(pObj0), Abc_ObjId(pObj0)) );
        // remove duplicates
        k = 0;
        Vec_WrdForEachEntry( vSuper, Num, i )
        {
            if ( i + 1 == Vec_WrdSize(vSuper) )
            {
                Vec_WrdWriteEntry( vSuper, k++, Num );
                break;
            }
            NumNext = Vec_WrdEntry( vSuper, i+1 );
            assert( Num <= NumNext );
            if ( Num == NumNext )
                i++;
            else
                Vec_WrdWriteEntry( vSuper, k++, Num );
        }
        Vec_WrdShrink( vSuper, k );
    }
    *pfCompl = fCompl;
    Vec_WrdForEachEntry( vSuper, Num, i )
        Vec_WrdWriteEntry( vSuper, i, Abc_NtkShareUnpackId(Num) );
    return vSuper;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_NtkShareFindBest_( Vec_Ptr_t * vBuckets )
{
    Vec_Ptr_t * vBucket;
    int i;
    Vec_PtrForEachEntryReverse( Vec_Ptr_t *, vBuckets, vBucket, i )
    {
        if ( Vec_PtrSize(vBucket) == 0 )
            continue;
        return (Vec_Int_t *)Vec_PtrPop( vBucket );
    }
    return NULL;
}
Vec_Int_t * Abc_NtkShareFindBestMatch_( Vec_Ptr_t * vBuckets, Vec_Int_t * vInput2 )
{
    Vec_Ptr_t * vBucket, * vBucketBest = NULL;
    Vec_Int_t * vInput, * vInputBest = NULL;
    int i, k, Cost, CostBest = 0;
    Vec_PtrForEachEntry( Vec_Ptr_t *, vBuckets, vBucket, i )
        Vec_PtrForEachEntry( Vec_Int_t *, vBucket, vInput, k )
        {
            vInput->pArray += SHARE_NUM;
            vInput2->pArray += SHARE_NUM;
            vInput->nSize -= SHARE_NUM;
            vInput2->nSize -= SHARE_NUM;

            Cost = Vec_IntTwoCountCommon(vInput, vInput2);

            vInput->pArray -= SHARE_NUM;
            vInput2->pArray -= SHARE_NUM;
            vInput->nSize += SHARE_NUM;
            vInput2->nSize += SHARE_NUM;

            if ( Cost < 2 )
                continue;

            if ( CostBest < Cost )
            {
                CostBest = Cost;
                vInputBest = vInput;
                vBucketBest = vBucket;
            }
        }
    if ( vInputBest )
        Vec_PtrRemove( vBucketBest, (Vec_Int_t *)vInputBest ); 
    printf( "%d ", CostBest );
    return vInputBest;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkShareFindBestMatch( Vec_Ptr_t * vBuckets, Vec_Int_t ** pvInput, Vec_Int_t ** pvInput2 )
{
    int nPoolSize = 40;
    Vec_Ptr_t * vPool = Vec_PtrAlloc( nPoolSize );
    Vec_Ptr_t * vBucket;
    Vec_Int_t * vInput, * vInput2, * vInputBest = NULL, * vInputBest2 = NULL;
    int i, k, Cost, CostBest = 0, Delay, DelayBest = 0;

    Vec_PtrForEachEntryReverse( Vec_Ptr_t *, vBuckets, vBucket, i )
        Vec_PtrForEachEntry( Vec_Int_t *, vBucket, vInput, k )
        {
            Vec_PtrPush( vPool, vInput );
            if ( Vec_PtrSize(vPool) == nPoolSize )
                goto outside;
        }
outside:

    Vec_PtrForEachEntryReverse( Vec_Int_t *, vPool, vInput, i )
    Vec_PtrForEachEntryReverse( Vec_Int_t *, vPool, vInput2, k )
    {
        if ( i == k )
            continue;

        vInput->pArray += SHARE_NUM;
        vInput2->pArray += SHARE_NUM;
        vInput->nSize -= SHARE_NUM;
        vInput2->nSize -= SHARE_NUM;

        Cost = Vec_IntTwoCountCommon(vInput, vInput2);

        vInput->pArray -= SHARE_NUM;
        vInput2->pArray -= SHARE_NUM;
        vInput->nSize += SHARE_NUM;
        vInput2->nSize += SHARE_NUM;

        if ( Cost < 2 )
            continue;

        Delay = Abc_MaxInt( Vec_IntEntry(vInput, 1), Vec_IntEntry(vInput2, 1) );

        if ( CostBest < Cost || (CostBest == Cost && (DelayBest > Delay)) )
        {
            CostBest = Cost;
            DelayBest = Delay;
            vInputBest = vInput;
            vInputBest2 = vInput2;
        }
    }
    Vec_PtrFree( vPool );

    *pvInput  = vInputBest;
    *pvInput2 = vInputBest2;

    if ( vInputBest == NULL )
        return;

    Vec_PtrRemove( (Vec_Ptr_t *)Vec_PtrEntry(vBuckets, Vec_IntSize(vInputBest)-SHARE_NUM),  (Vec_Int_t *)vInputBest ); 
    Vec_PtrRemove( (Vec_Ptr_t *)Vec_PtrEntry(vBuckets, Vec_IntSize(vInputBest2)-SHARE_NUM), (Vec_Int_t *)vInputBest2 ); 
}

void Abc_NtkSharePrint( Abc_Ntk_t * pNtk, Vec_Ptr_t * vBuckets, int Counter )
{
    Vec_Ptr_t * vBucket;
    Vec_Int_t * vInput;
    int i, k, j, ObjId;
    char * pBuffer = ABC_ALLOC( char, Counter + 1 );
    int * pCounters = ABC_CALLOC( int, Counter + 1 );
    int nTotal = 0;
    Vec_PtrForEachEntry( Vec_Ptr_t *, vBuckets, vBucket, i )
    Vec_PtrForEachEntry( Vec_Int_t *, vBucket, vInput, j )
    {
        for ( k = 0; k < Counter; k++ )
            pBuffer[k] = '0';
        pBuffer[k] = 0;

        Vec_IntForEachEntryStart( vInput, ObjId, k, SHARE_NUM )
        {
            assert( ObjId < Counter );
            pBuffer[ObjId] = '1';
            pCounters[ObjId]++;
        }

        printf( "%4d%3d: %s\n", Vec_IntEntry(vInput, 0), Vec_IntEntry(vInput, 1), pBuffer );
    }
    ABC_FREE( pBuffer );

    for ( i = 0; i < Counter; i++ )
        if ( pCounters[i] > 0 )
            printf( "%d=%d ", i, pCounters[i] ); 

    nTotal = 0;
    for ( i = 0; i < Abc_NtkCoNum(pNtk); i++ )
        nTotal += pCounters[i] - 1;
    printf( "Total = %d.\n", nTotal );
    printf( "Xors = %d.\n", Counter - Abc_NtkCoNum(pNtk) + nTotal );

    ABC_FREE( pCounters );
}

void Abc_NtkShareOptimize( Abc_Ntk_t * pNtk, Vec_Ptr_t * vBuckets, int * pCounter )
{
    Abc_Obj_t * pObj, * pObj0, * pObj1;
    Vec_Int_t * vInput, * vInput2;
    Vec_Int_t * vNew, * vOld1, * vOld2;
    int i, iLit;
    for ( i = 0; ; i++ )
    {
        Abc_NtkShareFindBestMatch( vBuckets, &vInput, &vInput2 );
        if ( vInput == NULL )
            break;

        // create new node
        pObj0 = Abc_ObjFromLit( pNtk, Vec_IntEntry(vInput,  0) );
        pObj1 = Abc_ObjFromLit( pNtk, Vec_IntEntry(vInput2, 0) );
        pObj  = Abc_AigXor( (Abc_Aig_t *)pNtk->pManFunc, pObj0, pObj1 );
        iLit  = Abc_ObjToLit( pObj );

        // save new node
        vOld1 = Vec_IntAlloc( 16 );  Vec_IntPush( vOld1, Vec_IntEntry(vInput,  0) );  Vec_IntPush( vOld1, Vec_IntEntry(vInput,  1) );
        vOld2 = Vec_IntAlloc( 16 );  Vec_IntPush( vOld2, Vec_IntEntry(vInput2, 0) );  Vec_IntPush( vOld2, Vec_IntEntry(vInput2, 1) );
        vNew  = Vec_IntAlloc( 16 );  Vec_IntPush( vNew,  iLit );                      Vec_IntPush( vNew, Abc_ObjLevel(Abc_ObjRegular(pObj)) );

        // compute new arrays
        vInput->pArray += SHARE_NUM;
        vInput2->pArray += SHARE_NUM;
        vInput->nSize -= SHARE_NUM;
        vInput2->nSize -= SHARE_NUM;

        Vec_IntTwoSplit( vInput, vInput2, vNew, vOld1, vOld2 );

        vInput->pArray -= SHARE_NUM;
        vInput2->pArray -= SHARE_NUM;
        vInput->nSize += SHARE_NUM;
        vInput2->nSize += SHARE_NUM;

        // add to the old ones
        Vec_IntPush( vOld1, *pCounter );
        Vec_IntPush( vOld2, *pCounter );
        (*pCounter)++;

        Vec_PtrPush( (Vec_Ptr_t *)Vec_PtrEntry(vBuckets, Vec_IntSize(vOld1)-SHARE_NUM), vOld1 );
        Vec_PtrPush( (Vec_Ptr_t *)Vec_PtrEntry(vBuckets, Vec_IntSize(vOld2)-SHARE_NUM), vOld2 );
        Vec_PtrPush( (Vec_Ptr_t *)Vec_PtrEntry(vBuckets, Vec_IntSize(vNew)-SHARE_NUM), vNew );

        Vec_IntFree( vInput );
        Vec_IntFree( vInput2 );
    }
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    [Extracts one multi-output XOR.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkShareXor( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vBuckets, * vBucket;
    Vec_Ptr_t * vInputs;
    Vec_Int_t * vInput;
    Vec_Wrd_t * vSuper;
    Abc_Obj_t * pObj;
    word Num;
    int i, k, ObjId, fCompl, nOnesMax, Counter;
    assert( Abc_NtkIsStrash(pNtk) );

    vInputs = Vec_PtrStart( Abc_NtkObjNumMax(pNtk) );
    Abc_NtkForEachCo( pNtk, pObj, i )
    {
        if ( !Abc_NodeIsExorType(Abc_ObjFanin0(pObj)) )
            continue;
        vSuper = Abc_NtkShareSuperXor( Abc_ObjChild0(pObj), &fCompl );
//printf( "%d ", Vec_WrdSize(vSuper) );

        pObj->fMarkA = fCompl;
        Vec_WrdForEachEntry( vSuper, Num, k )
        {
            ObjId = Abc_NtkShareUnpackId(Num);
            vInput = (Vec_Int_t *)Vec_PtrEntry( vInputs, ObjId );
            if ( vInput == NULL )
            {
                vInput = Vec_IntAlloc( 10 );
                Vec_IntPush( vInput, Abc_Var2Lit(ObjId, 0) );
                Vec_IntPush( vInput, Abc_ObjLevel(Abc_NtkObj(pNtk, ObjId)) );
                assert( SHARE_NUM == Vec_IntSize(vInput) );
                Vec_PtrWriteEntry( vInputs, ObjId, vInput );
            }
//            Vec_IntPush( vInput, Abc_ObjFaninId0(pObj) );
//            Vec_IntPush( vInput, Abc_ObjId(pObj) );
            Vec_IntPush( vInput, i );
        }
        Vec_WrdFree( vSuper );
    }
//printf( "\n" );

    // find the largest number of 1s
    nOnesMax = 0;
    Vec_PtrForEachEntry( Vec_Int_t *, vInputs, vInput, i )
        if ( vInput )
            nOnesMax = Abc_MaxInt( nOnesMax, Vec_IntSize(vInput)-SHARE_NUM );

    vBuckets = Vec_PtrAlloc( nOnesMax + 1 );
    for ( i = 0; i <= nOnesMax; i++ )
        Vec_PtrPush( vBuckets, Vec_PtrAlloc(10) );

    Vec_PtrForEachEntry( Vec_Int_t *, vInputs, vInput, i )
        if ( vInput )
            Vec_PtrPush( (Vec_Ptr_t *)Vec_PtrEntry(vBuckets, Vec_IntSize(vInput)-SHARE_NUM), vInput );

    // find the best match
    Counter = Abc_NtkCoNum(pNtk);
    Abc_NtkShareOptimize( pNtk, vBuckets, &Counter );

    Abc_NtkSharePrint( pNtk, vBuckets, Counter );

    // clean up
    Vec_PtrForEachEntry( Vec_Ptr_t *, vBuckets, vBucket, i )
        printf( "%d ", Vec_PtrSize(vBucket) );
    printf( "\n" );

    Vec_PtrForEachEntry( Vec_Ptr_t *, vBuckets, vBucket, i )
        Vec_VecFree( (Vec_Vec_t *)vBucket );
    Vec_PtrFree( vBuckets );

/*
    // print
    Vec_PtrForEachEntry( Vec_Int_t *, vInputs, vInput, i )
    {
        if ( vInput == NULL )
            continue;
        pObj = Abc_NtkObj(pNtk, i);
        assert( Abc_ObjIsCi(pObj) );

        Vec_IntForEachEntryStart( vInput, ObjId, k, SHARE_NUM )
            Abc_NtkObj( pNtk, ObjId )->fMarkA = 1;

        Abc_NtkForEachCo( pNtk, pObj, k )
            printf( "%d", pObj->fMarkA );
        printf( "\n" );

        Vec_IntForEachEntryStart( vInput, ObjId, k, SHARE_NUM )
            Abc_NtkObj( pNtk, ObjId )->fMarkA = 0;
    }

    Vec_PtrForEachEntry( Vec_Int_t *, vInputs, vInput, i )
        Vec_IntFreeP( &vInput );
*/
    Vec_PtrFree( vInputs );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

