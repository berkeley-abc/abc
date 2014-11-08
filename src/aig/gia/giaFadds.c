/**CFile****************************************************************

  FileName    [giaFadds.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Extraction of full-adders.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaFadds.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

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
#define Dtc_ForEachCut( pList, pCut, i ) for ( i = 0, pCut = pList + 1; i < pList[0]; i++, pCut += pCut[0] + 1 )
int Dtc_ManCutMergeOne( int * pCut0, int * pCut1, int * pCut )
{
    int i, k;
    for ( k = 0; k <= pCut1[0]; k++ )
        pCut[k] = pCut1[k];
    for ( i = 1; i <= pCut0[0]; i++ )
    {
        for ( k = 1; k <= pCut1[0]; k++ )
            if ( pCut0[i] == pCut1[k] )
                break;
        if ( k <= pCut1[0] )
            continue;
        if ( pCut[0] == 3 )
            return 0;
        pCut[1+pCut[0]++] = pCut0[i];
    }
    assert( pCut[0] == 2 || pCut[0] == 3 );
    if ( pCut[1] > pCut[2] )
        ABC_SWAP( int, pCut[1], pCut[2] );
    assert( pCut[1] < pCut[2] );
    if ( pCut[0] == 2 )
        return 1;
    if ( pCut[2] > pCut[3] )
        ABC_SWAP( int, pCut[2], pCut[3] );
    if ( pCut[1] > pCut[2] )
        ABC_SWAP( int, pCut[1], pCut[2] );
    assert( pCut[1] < pCut[2] );
    assert( pCut[2] < pCut[3] );
    return 1;
}
int Dtc_ManCutCheckEqual( Vec_Int_t * vCuts, int * pCutNew )
{
    int * pList = Vec_IntArray( vCuts );
    int i, k, * pCut;
    Dtc_ForEachCut( pList, pCut, i )
    {
        for ( k = 0; k <= pCut[0]; k++ )
            if ( pCut[k] != pCutNew[k] )
                break;
        if ( k > pCut[0] )
            return 1;
    }
    return 0;
}
int Dtc_ObjComputeTruth_rec( Gia_Obj_t * pObj )
{
    int Truth0, Truth1;
    if ( pObj->Value )
        return pObj->Value;
    assert( Gia_ObjIsAnd(pObj) );
    Truth0 = Dtc_ObjComputeTruth_rec( Gia_ObjFanin0(pObj) );
    Truth1 = Dtc_ObjComputeTruth_rec( Gia_ObjFanin1(pObj) );
    return (pObj->Value = (Gia_ObjFaninC0(pObj) ? ~Truth0 : Truth0) & (Gia_ObjFaninC1(pObj) ? ~Truth1 : Truth1));
}
void Dtc_ObjCleanTruth_rec( Gia_Obj_t * pObj )
{
    if ( !pObj->Value )
        return;
    pObj->Value = 0;
    if ( !Gia_ObjIsAnd(pObj) )
        return;
    Dtc_ObjCleanTruth_rec( Gia_ObjFanin0(pObj) );
    Dtc_ObjCleanTruth_rec( Gia_ObjFanin1(pObj) );
}
int Dtc_ObjComputeTruth( Gia_Man_t * p, int iObj, int * pCut )
{
    unsigned Truth, Truths[3] = { 0xAA, 0xCC, 0xF0 }; int i;
    for ( i = 1; i <= pCut[0]; i++ )
        Gia_ManObj(p, pCut[i])->Value = Truths[i-1];
    Truth = 0xFF & Dtc_ObjComputeTruth_rec( Gia_ManObj(p, iObj) );
    Dtc_ObjCleanTruth_rec( Gia_ManObj(p, iObj) );
    if ( Truth == 0x69 || Truth == 0x96 )
        return 1;
    if ( Truth == 0x8E || Truth == 0x4D || Truth == 0x2B || Truth == 0xE8 ||
         Truth == 0x71 || Truth == 0xB2 || Truth == 0xD4 || Truth == 0x17 )
    {
//        printf( "%2x ", Truth );
        return 2;
    }
    return 0;
}
void Dtc_ManCutMerge( Gia_Man_t * p, int iObj, int * pList0, int * pList1, Vec_Int_t * vCuts, Vec_Int_t * vCutsXor, Vec_Int_t * vCutsMaj )
{
    Vec_Int_t * vTemp;
    int i, k, c, Type, * pCut0, * pCut1, pCut[4];
    Vec_IntFill( vCuts, 2, 1 );
    Vec_IntPush( vCuts, iObj );
    Dtc_ForEachCut( pList0, pCut0, i )
    Dtc_ForEachCut( pList1, pCut1, k )
    {
        if ( !Dtc_ManCutMergeOne(pCut0, pCut1, pCut) )
            continue;
        if ( Dtc_ManCutCheckEqual(vCuts, pCut) )
            continue;
        Vec_IntAddToEntry( vCuts, 0, 1 );  
        for ( c = 0; c <= pCut[0]; c++ )
            Vec_IntPush( vCuts, pCut[c] );
        if ( pCut[0] != 3 )
            continue;
        Type = Dtc_ObjComputeTruth( p, iObj, pCut );
        if ( Type == 0 )
            continue;
        vTemp = Type == 1 ? vCutsXor : vCutsMaj;
        for ( c = 1; c <= pCut[0]; c++ )
            Vec_IntPush( vTemp, pCut[c] );
        Vec_IntPush( vTemp, iObj );
    }
}
void Dtc_ManComputeCuts( Gia_Man_t * p, Vec_Int_t ** pvCutsXor, Vec_Int_t ** pvCutsMaj )
{
    Gia_Obj_t * pObj; 
    int * pList0, * pList1, i, nCuts = 0;
    Vec_Int_t * vTemp = Vec_IntAlloc( 1000 );
    Vec_Int_t * vCutsXor = Vec_IntAlloc( Gia_ManAndNum(p) );
    Vec_Int_t * vCutsMaj = Vec_IntAlloc( Gia_ManAndNum(p) );
    Vec_Int_t * vCuts = Vec_IntAlloc( 30 * Gia_ManAndNum(p) );
    Vec_IntFill( vCuts, Gia_ManObjNum(p), 0 );
    Gia_ManCleanValue( p );
    Gia_ManForEachCi( p, pObj, i )
    {
        Vec_IntWriteEntry( vCuts, Gia_ObjId(p, pObj), Vec_IntSize(vCuts) );
        Vec_IntPush( vCuts, 1 );
        Vec_IntPush( vCuts, 1 );
        Vec_IntPush( vCuts, Gia_ObjId(p, pObj) );
    }
    Gia_ManForEachAnd( p, pObj, i )
    {
        pList0 = Vec_IntEntryP( vCuts, Vec_IntEntry(vCuts, Gia_ObjFaninId0(pObj, i)) );
        pList1 = Vec_IntEntryP( vCuts, Vec_IntEntry(vCuts, Gia_ObjFaninId1(pObj, i)) );
        Dtc_ManCutMerge( p, i, pList0, pList1, vTemp, vCutsXor, vCutsMaj );
        Vec_IntWriteEntry( vCuts, i, Vec_IntSize(vCuts) );
        Vec_IntAppend( vCuts, vTemp );
        nCuts += Vec_IntSize( vTemp );
    }
    printf( "Nodes = %d.  Cuts = %d.  Cuts/Node = %.2f.  Ints/Node = %.2f.\n", 
        Gia_ManAndNum(p), nCuts, 1.0*nCuts/Gia_ManAndNum(p), 1.0*Vec_IntSize(vCuts)/Gia_ManAndNum(p) );
    Vec_IntFree( vTemp );
    Vec_IntFree( vCuts );
    *pvCutsXor = vCutsXor;
    *pvCutsMaj = vCutsMaj;
}
int Dtc_ManCompare( int * pCut0, int * pCut1 )
{
    if ( pCut0[0] < pCut1[0] ) return -1;
    if ( pCut0[0] > pCut1[0] ) return  1;
    if ( pCut0[1] < pCut1[1] ) return -1;
    if ( pCut0[1] > pCut1[1] ) return  1;
    if ( pCut0[2] < pCut1[2] ) return -1;
    if ( pCut0[2] > pCut1[2] ) return  1;
    return 0;
}
Vec_Int_t * Dtc_ManFindCommonCuts( Gia_Man_t * p, Vec_Int_t * vCutsXor, Vec_Int_t * vCutsMaj )
{
    int * pCuts0 = Vec_IntArray(vCutsXor);
    int * pCuts1 = Vec_IntArray(vCutsMaj);
    int * pLimit0 = Vec_IntLimit(vCutsXor);
    int * pLimit1 = Vec_IntLimit(vCutsMaj);   int i;
    Vec_Int_t * vFadds = Vec_IntAlloc( 1000 );
    assert( Vec_IntSize(vCutsXor) % 4 == 0 );
    assert( Vec_IntSize(vCutsMaj) % 4 == 0 );
    while ( pCuts0 < pLimit0 && pCuts1 < pLimit1 )
    {
        for ( i = 0; i < 3; i++ )
            if ( pCuts0[i] != pCuts1[i] )
                break;
        if ( i == 3 )
        {
            for ( i = 0; i < 4; i++ )
                Vec_IntPush( vFadds, pCuts0[i] );
            Vec_IntPush( vFadds, pCuts1[3] );
            pCuts0 += 4;
            pCuts1 += 4;
        }
        else if ( pCuts0[i] < pCuts1[i] )
            pCuts0 += 4;
        else if ( pCuts0[i] > pCuts1[i] )
            pCuts1 += 4;
    }
    return vFadds;
}
void Dtc_ManPrintFadds( Vec_Int_t * vFadds )
{
    int i, nObjs = Vec_IntSize(vFadds)/5;
    assert( Vec_IntSize(vFadds) % 5 == 0 );
    for ( i = 0; i < nObjs; i++ )
    {
        printf( "%6d : ", i );
        printf( "%6d ", Vec_IntEntry(vFadds, 5*i+0) );
        printf( "%6d ", Vec_IntEntry(vFadds, 5*i+1) );
        printf( "%6d ", Vec_IntEntry(vFadds, 5*i+2) );
        printf( " ->  " );
        printf( "%6d ", Vec_IntEntry(vFadds, 5*i+3) );
        printf( "%6d ", Vec_IntEntry(vFadds, 5*i+4) );
        printf( "\n" );
    }
}
void Dtc_ManSortChains( Gia_Man_t * p, Vec_Int_t * vFadds )
{
    Vec_Int_t * vMap = Vec_IntStartFull( Gia_ManObjNum(p) );
    int i, iFadd, Count = 0, nObjs = Vec_IntSize(vFadds)/5;
    assert( Vec_IntSize(vFadds) % 5 == 0 );
    for ( i = 0; i < nObjs; i++ )
        Vec_IntWriteEntry( vMap, Vec_IntEntry(vFadds, 5*i+4), i );
    for ( i = 0; i < nObjs; i++ )
    {
        int fFound = 0;
        if ( (iFadd = Vec_IntEntry( vMap, Vec_IntEntry(vFadds, 5*i+0) )) >= 0 )
            printf( "%d -> %d\n", iFadd, i ), fFound++;
        if ( (iFadd = Vec_IntEntry( vMap, Vec_IntEntry(vFadds, 5*i+1) )) >= 0 )
            printf( "%d -> %d\n", iFadd, i ), fFound++;
        if ( (iFadd = Vec_IntEntry( vMap, Vec_IntEntry(vFadds, 5*i+2) )) >= 0 )
            printf( "%d -> %d\n", iFadd, i ), fFound++;
        if ( !fFound )
            printf( "\n" );
        if ( fFound > 1 )
            Count++;
    }
//    printf( "%d \n", Count );
    Vec_IntFree( vMap );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManDetectCarryChains( Gia_Man_t * p )
{
    Vec_Int_t * vCutsXor, * vCutsMaj, * vFadds;
    Dtc_ManComputeCuts( p, &vCutsXor, &vCutsMaj );
    qsort( Vec_IntArray(vCutsXor), Vec_IntSize(vCutsXor)/4, 16, (int (*)(const void *, const void *))Dtc_ManCompare );
    qsort( Vec_IntArray(vCutsMaj), Vec_IntSize(vCutsMaj)/4, 16, (int (*)(const void *, const void *))Dtc_ManCompare );
    vFadds = Dtc_ManFindCommonCuts( p, vCutsXor, vCutsMaj );
    printf( "XOR3 cuts = %d.  MAJ cuts = %d.  Fadds = %d.\n", Vec_IntSize(vCutsXor)/4, Vec_IntSize(vCutsMaj)/4, Vec_IntSize(vFadds)/5 );
//    Dtc_ManPrintFadds( vFadds );
    Dtc_ManSortChains( p, vFadds );
    Vec_IntFree( vCutsXor );
    Vec_IntFree( vCutsMaj );
    Vec_IntFree( vFadds );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

