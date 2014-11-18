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
#include "misc/vec/vecWec.h"
#include "misc/tim/tim.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define Dtc_ForEachCut( pList, pCut, i ) for ( i = 0, pCut = pList + 1; i < pList[0]; i++, pCut += pCut[0] + 1 )
#define Dtc_ForEachFadd( vFadds, i )     for ( i = 0; i < Vec_IntSize(vFadds)/5; i++ )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Derive GIA with boxes containing adder-chains.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManIllustrateBoxes( Gia_Man_t * p )
{
    Tim_Man_t * pManTime = (Tim_Man_t *)p->pManTime;
    int nBoxes = Tim_ManBoxNum( pManTime );
    int i, k, curCi, curCo, nBoxIns, nBoxOuts;
    Gia_Obj_t * pObj;
    // walk through the boxes
    curCi = Tim_ManPiNum(pManTime);
    curCo = 0;
    for ( i = 0; i < nBoxes; i++ )
    {
        nBoxIns = Tim_ManBoxInputNum(pManTime, i);
        nBoxOuts = Tim_ManBoxOutputNum(pManTime, i);
        printf( "Box %4d  [%d x %d] :   ", i, nBoxIns, nBoxOuts );
        printf( "Input obj IDs = " );
        for ( k = 0; k < nBoxIns; k++ )
        {
            pObj = Gia_ManCo( p, curCo + k );
            printf( "%d ", Gia_ObjId(p, pObj) );
        }
        printf( "  Output obj IDs = " );
        for ( k = 0; k < nBoxOuts; k++ )
        {
            pObj = Gia_ManCi( p, curCi + k );
            printf( "%d ", Gia_ObjId(p, pObj) );
        }
        curCo += nBoxIns;
        curCi += nBoxOuts;
        printf( "\n" );
    }
    curCo += Tim_ManPoNum(pManTime);
    // verify counts
    assert( curCi == Gia_ManCiNum(p) );
    assert( curCo == Gia_ManCoNum(p) );
}

/**Function*************************************************************

  Synopsis    [Detecting FADDs in the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
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
int Dtc_ObjComputeTruth( Gia_Man_t * p, int iObj, int * pCut, int * pTruth )
{
    unsigned Truth, Truths[3] = { 0xAA, 0xCC, 0xF0 }; int i;
    for ( i = 1; i <= pCut[0]; i++ )
        Gia_ManObj(p, pCut[i])->Value = Truths[i-1];
    Truth = 0xFF & Dtc_ObjComputeTruth_rec( Gia_ManObj(p, iObj) );
    Dtc_ObjCleanTruth_rec( Gia_ManObj(p, iObj) );
    if ( pTruth ) 
        *pTruth = Truth;
    if ( Truth == 0x96 || Truth == 0x69 )
        return 1;
    if ( Truth == 0xE8 || Truth == 0xD4 || Truth == 0xB2 || Truth == 0x71 ||
         Truth == 0x17 || Truth == 0x2B || Truth == 0x4D || Truth == 0x8E )
        return 2;
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
        Type = Dtc_ObjComputeTruth( p, iObj, pCut, NULL );
        if ( Type == 0 )
            continue;
        vTemp = Type == 1 ? vCutsXor : vCutsMaj;
        for ( c = 1; c <= pCut[0]; c++ )
            Vec_IntPush( vTemp, pCut[c] );
        Vec_IntPush( vTemp, iObj );
    }
}
void Dtc_ManComputeCuts( Gia_Man_t * p, Vec_Int_t ** pvCutsXor, Vec_Int_t ** pvCutsMaj, int fVerbose )
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
        nCuts += Vec_IntEntry( vTemp, 0 );
    }
    if ( fVerbose )
        printf( "Nodes = %d.  Cuts = %d.  Cuts/Node = %.2f.  Ints/Node = %.2f.\n", 
            Gia_ManAndNum(p), nCuts, 1.0*nCuts/Gia_ManAndNum(p), 1.0*Vec_IntSize(vCuts)/Gia_ManAndNum(p) );
    Vec_IntFree( vTemp );
    Vec_IntFree( vCuts );
    *pvCutsXor = vCutsXor;
    *pvCutsMaj = vCutsMaj;
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
    assert( Vec_IntSize(vFadds) % 5 == 0 );
    return vFadds;
}
void Dtc_ManPrintFadds( Vec_Int_t * vFadds )
{
    int i;
    Dtc_ForEachFadd( vFadds, i )
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
int Dtc_ManCompare2( int * pCut0, int * pCut1 )
{
    if ( pCut0[4] < pCut1[4] ) return -1;
    if ( pCut0[4] > pCut1[4] ) return  1;
    return 0;
}
// returns array of 5-tuples containing inputs/sum/cout of each full adder
Vec_Int_t * Gia_ManDetectFullAdders( Gia_Man_t * p, int fVerbose )
{
    Vec_Int_t * vCutsXor, * vCutsMaj, * vFadds;
    Dtc_ManComputeCuts( p, &vCutsXor, &vCutsMaj, fVerbose );
    qsort( Vec_IntArray(vCutsXor), Vec_IntSize(vCutsXor)/4, 16, (int (*)(const void *, const void *))Dtc_ManCompare );
    qsort( Vec_IntArray(vCutsMaj), Vec_IntSize(vCutsMaj)/4, 16, (int (*)(const void *, const void *))Dtc_ManCompare );
    vFadds = Dtc_ManFindCommonCuts( p, vCutsXor, vCutsMaj );
    qsort( Vec_IntArray(vFadds), Vec_IntSize(vFadds)/5, 20, (int (*)(const void *, const void *))Dtc_ManCompare2 );
    if ( fVerbose )
        printf( "XOR3 cuts = %d.  MAJ cuts = %d.  Full-adders = %d.\n", Vec_IntSize(vCutsXor)/4, Vec_IntSize(vCutsMaj)/4, Vec_IntSize(vFadds)/5 );
    //Dtc_ManPrintFadds( vFadds );
    Vec_IntFree( vCutsXor );
    Vec_IntFree( vCutsMaj );
    return vFadds;
}

/**Function*************************************************************

  Synopsis    [Map each MAJ into the topmost MAJ of its chain.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
// maps MAJ nodes into FADD indexes
Vec_Int_t * Gia_ManCreateMap( Gia_Man_t * p, Vec_Int_t * vFadds )
{
    Vec_Int_t * vMap = Vec_IntStartFull( Gia_ManObjNum(p) );  int i;
    Dtc_ForEachFadd( vFadds, i )
        Vec_IntWriteEntry( vMap, Vec_IntEntry(vFadds, 5*i+4), i );
    return vMap;
}
// find chain length (for each MAJ, how many FADDs are rooted in its first input)
int Gia_ManFindChains_rec( Gia_Man_t * p, int iMaj, Vec_Int_t * vFadds, Vec_Int_t * vMap, Vec_Int_t * vLength )
{
    assert( Vec_IntEntry(vMap, iMaj) >= 0 ); // MAJ
    if ( Vec_IntEntry(vLength, iMaj) >= 0 )
        return Vec_IntEntry(vLength, iMaj);
    assert( Gia_ObjIsAnd(Gia_ManObj(p, iMaj)) );
    {
        int iFadd = Vec_IntEntry( vMap, iMaj );
        int iXor0 = Vec_IntEntry( vFadds, 5*iFadd+0 );
        int iXor1 = Vec_IntEntry( vFadds, 5*iFadd+1 );
        int iXor2 = Vec_IntEntry( vFadds, 5*iFadd+2 );
        int iLen0 = Vec_IntEntry( vMap, iXor0 ) == -1 ? 0 : Gia_ManFindChains_rec( p, iXor0, vFadds, vMap, vLength );
        int iLen1 = Vec_IntEntry( vMap, iXor1 ) == -1 ? 0 : Gia_ManFindChains_rec( p, iXor1, vFadds, vMap, vLength );
        int iLen2 = Vec_IntEntry( vMap, iXor2 ) == -1 ? 0 : Gia_ManFindChains_rec( p, iXor2, vFadds, vMap, vLength );
        int iLen = Abc_MaxInt( iLen0, Abc_MaxInt(iLen1, iLen2) );
        if ( iLen0 < iLen )
        {
            if ( iLen == iLen1 )
            {
                ABC_SWAP( int, Vec_IntArray(vFadds)[5*iFadd+0], Vec_IntArray(vFadds)[5*iFadd+1] );
            }
            else if ( iLen == iLen2 )
            {
                ABC_SWAP( int, Vec_IntArray(vFadds)[5*iFadd+0], Vec_IntArray(vFadds)[5*iFadd+2] );
            }
        }
        Vec_IntWriteEntry( vLength, iMaj, iLen + 1 );
        return iLen + 1;
    }
}
// for each FADD find the longest chain and reorder its inputs
void Gia_ManFindChains( Gia_Man_t * p, Vec_Int_t * vFadds, Vec_Int_t * vMap )
{
    int i;
    // for each FADD find the longest chain rooted in it
    Vec_Int_t * vLength = Vec_IntStartFull( Gia_ManObjNum(p) );
    Dtc_ForEachFadd( vFadds, i )
        Gia_ManFindChains_rec( p, Vec_IntEntry(vFadds, 5*i+4), vFadds, vMap, vLength );
    Vec_IntFree( vLength );
}
// collect one carry-chain
void Gia_ManCollectOneChain( Gia_Man_t * p, Vec_Int_t * vFadds, int iFaddTop, Vec_Int_t * vMap, Vec_Int_t * vChain )
{
    int iFadd;
    Vec_IntClear( vChain );
    for ( iFadd = iFaddTop; iFadd >= 0 && 
          !Gia_ObjIsTravIdCurrentId(p, Vec_IntEntry(vFadds, 5*iFadd+3)) && 
          !Gia_ObjIsTravIdCurrentId(p, Vec_IntEntry(vFadds, 5*iFadd+4)); 
          iFadd = Vec_IntEntry(vMap, Vec_IntEntry(vFadds, 5*iFadd+0)) )
          {
                Vec_IntPush( vChain, iFadd );
          }
    Vec_IntReverseOrder( vChain );
}
void Gia_ManMarkWithTravId_rec( Gia_Man_t * p, int Id )
{
    Gia_Obj_t * pObj;
    if ( Gia_ObjIsTravIdCurrentId(p, Id) )
        return;
    Gia_ObjSetTravIdCurrentId(p, Id);
    pObj = Gia_ManObj( p, Id );
    if ( Gia_ObjIsAnd(pObj) )
        Gia_ManMarkWithTravId_rec( p, Gia_ObjFaninId0(pObj, Id) );
    if ( Gia_ObjIsAnd(pObj) )
        Gia_ManMarkWithTravId_rec( p, Gia_ObjFaninId1(pObj, Id) );
}
// returns mapping of each MAJ into the topmost elements of its chain
Vec_Wec_t * Gia_ManCollectTopmost( Gia_Man_t * p, Vec_Int_t * vFadds, Vec_Int_t * vMap, int nFaddMin )
{
    int i, j, iFadd;
    Vec_Int_t * vChain  = Vec_IntAlloc( 100 );
    Vec_Wec_t * vChains = Vec_WecAlloc( Vec_IntSize(vFadds)/5 );
    // erase elements appearing as FADD inputs
    Vec_Bit_t * vMarksTop = Vec_BitStart( Vec_IntSize(vFadds)/5 );
    Dtc_ForEachFadd( vFadds, i )
        if ( (iFadd = Vec_IntEntry(vMap, Vec_IntEntry(vFadds, 5*i+0))) >= 0 )
            Vec_BitWriteEntry( vMarksTop, iFadd, 1 );
    // compress the remaining ones
    Gia_ManIncrementTravId( p );
    Dtc_ForEachFadd( vFadds, i )
    {
        if ( Vec_BitEntry(vMarksTop, i) )
            continue;
        Gia_ManCollectOneChain( p, vFadds, i, vMap, vChain );
        if ( Vec_IntSize(vChain) < nFaddMin )
            continue;
        Vec_IntAppend( Vec_WecPushLevel(vChains), vChain );
        Vec_IntForEachEntry( vChain, iFadd, j )
        {
            assert( !Gia_ObjIsTravIdCurrentId(p, Vec_IntEntry(vFadds, 5*iFadd+3)) );
            assert( !Gia_ObjIsTravIdCurrentId(p, Vec_IntEntry(vFadds, 5*iFadd+4)) );
            Gia_ManMarkWithTravId_rec( p, Vec_IntEntry(vFadds, 5*iFadd+3) );
            Gia_ManMarkWithTravId_rec( p, Vec_IntEntry(vFadds, 5*iFadd+4) );
        }
    }
    // cleanup
    Vec_BitFree( vMarksTop );
    Vec_IntFree( vChain );
    return vChains;
}
// prints chains beginning in majority nodes contained in vTops
void Gia_ManPrintChains( Gia_Man_t * p, Vec_Int_t * vFadds, Vec_Int_t * vMap, Vec_Wec_t * vChains )
{
    Vec_Int_t * vChain;
    int i, k, iFadd, Count = 0;
    Vec_WecForEachLevel( vChains, vChain, i )
    {
        Count += Vec_IntSize(vChain);
        if ( i < 10 )
        {
            printf( "Chain %4d : %4d    ", i, Vec_IntSize(vChain) );
            Vec_IntForEachEntry( vChain, iFadd, k )
            {
                printf( "%d(%d) ", iFadd, Vec_IntEntry(vFadds, 5*iFadd+4) );
                if ( k != Vec_IntSize(vChain) - 1 )
                    printf( "-> " );
                if ( k > 6 )
                {
                    printf( "..." );
                    break;
                }
            }
            printf( "\n" );
        }
        else if ( i == 10 )
            printf( "...\n" );

    }
    printf( "Total chains = %d. Total full-adders = %d.\n", Vec_WecSize(vChains), Count );
}
// map SUM bits and topmost MAJ into topmost FADD number
Vec_Int_t * Gia_ManFindMapping( Gia_Man_t * p, Vec_Int_t * vFadds, Vec_Int_t * vMap, Vec_Wec_t * vChains )
{
    Vec_Int_t * vChain;
    int i, k, iFadd = -1;
    Vec_Int_t * vMap2Chain = Vec_IntStartFull( Gia_ManObjNum(p) );
    Vec_WecForEachLevel( vChains, vChain, i )
    {
        assert( Vec_IntSize(vChain) > 0 );
        Vec_IntForEachEntry( vChain, iFadd, k )
        {
            //printf( "Chain %d: setting SUM %d (obj %d)\n", i, k, Vec_IntEntry(vFadds, 5*iFadd+3) );
            assert( Vec_IntEntry(vMap2Chain, Vec_IntEntry(vFadds, 5*iFadd+3)) == -1 );
            Vec_IntWriteEntry( vMap2Chain, Vec_IntEntry(vFadds, 5*iFadd+3), i );
        }
        //printf( "Chain %d: setting CARRY (obj %d)\n", i, Vec_IntEntry(vFadds, 5*iFadd+4) );
        assert( Vec_IntEntry(vMap2Chain, Vec_IntEntry(vFadds, 5*iFadd+4)) == -1 );
        Vec_IntWriteEntry( vMap2Chain, Vec_IntEntry(vFadds, 5*iFadd+4), i );
    }
    return vMap2Chain;
}

/**Function*************************************************************

  Synopsis    [Derive GIA with boxes containing adder-chains.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_ManCollectTruthTables( Gia_Man_t * p, Vec_Int_t * vFadds )
{
    int i, k, Type, Truth, pCut[4] = {3};
    Vec_Int_t * vTruths = Vec_IntAlloc( 2*Vec_IntSize(vFadds)/5 );
    Gia_ManCleanValue( p );
    Dtc_ForEachFadd( vFadds, i )
    {
        for ( k = 0; k < 3; k++ )
            pCut[k+1] = Vec_IntEntry( vFadds, 5*i+k );
        Type = Dtc_ObjComputeTruth( p, Vec_IntEntry(vFadds, 5*i+3), pCut, &Truth );
        assert( Type == 1 );
        Vec_IntPush( vTruths, Truth );
        Type = Dtc_ObjComputeTruth( p, Vec_IntEntry(vFadds, 5*i+4), pCut, &Truth );
        assert( Type == 2 );
        Vec_IntPush( vTruths, Truth );
    }
    return vTruths;
}
float * Gia_ManGenerateDelayTableFloat( int nIns, int nOuts )
{
    int i, Total = nIns * nOuts;
    float * pDelayTable = ABC_ALLOC( float, Total + 3 );
    pDelayTable[0] = 0;
    pDelayTable[1] = nIns;
    pDelayTable[2] = nOuts;
    for ( i = 0; i < Total; i++ )
        pDelayTable[i+3] = 1;
    pDelayTable[i+3 - nIns] = -ABC_INFINITY;
    return pDelayTable;
}
Tim_Man_t * Gia_ManGenerateTim( int nPis, int nPos, int nBoxes, int nIns, int nOuts )
{
    Tim_Man_t * pMan;
    int i, curPi, curPo;
    Vec_Ptr_t * vDelayTables = Vec_PtrAlloc( 1 );
    Vec_PtrPush( vDelayTables, Gia_ManGenerateDelayTableFloat(nIns, nOuts) );
    pMan = Tim_ManStart( nPis + nOuts * nBoxes, nPos + nIns * nBoxes );
    Tim_ManSetDelayTables( pMan, vDelayTables );
    curPi = nPis;
    curPo = 0;
    for ( i = 0; i < nBoxes; i++ )
    {
        Tim_ManCreateBox( pMan, curPo, nIns, curPi, nOuts, 0 );
        curPi += nOuts;
        curPo += nIns;
    }
    curPo += nPos;
    assert( curPi == Tim_ManCiNum(pMan) );
    assert( curPo == Tim_ManCoNum(pMan) );
    //Tim_ManPrint( pMan );
    return pMan;
}
Gia_Man_t * Gia_ManGenerateExtraAig( int nBoxes, int nIns, int nOuts )
{
    Gia_Man_t * pNew = Gia_ManStart( nBoxes * 20 );
    int i, k, pInLits[16], pOutLits[16];
    assert( nIns < 16 && nOuts < 16 );
    for ( i = 0; i < nIns; i++ )
        pInLits[i] = Gia_ManAppendCi( pNew );
    pOutLits[0] = Gia_ManAppendXor( pNew, Gia_ManAppendXor(pNew, pInLits[0], pInLits[1]), pInLits[2] );
    pOutLits[1] = Gia_ManAppendMaj( pNew, pInLits[0], pInLits[1], pInLits[2] );
    for ( i = 0; i < nBoxes; i++ )
        for ( k = 0; k < nOuts; k++ )
            Gia_ManAppendCo( pNew, pOutLits[k] );
    return pNew;
}
void Gia_ManDupFadd( Gia_Man_t * pNew, Gia_Man_t * p, Vec_Int_t * vChain, Vec_Int_t * vFadds, Vec_Int_t * vMap, Vec_Wec_t * vChains, Vec_Int_t * vMap2Chain, Vec_Int_t * vTruths )
{
    extern void Gia_ManDupWithFaddBoxes_rec( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vFadds, Vec_Int_t * vMap, Vec_Wec_t * vChains, Vec_Int_t * vMap2Chain, Vec_Int_t * vTruths );
    int i, k, iFadd, iCiLit, pLits[3];
    Gia_Obj_t * pObj;
    // construct FADD inputs
    Vec_IntForEachEntry( vChain, iFadd, i )
        for ( k = 0; k < 3; k++ )
        {
            if ( i && !k ) continue;
            pObj = Gia_ManObj( p, Vec_IntEntry(vFadds, 5*iFadd+k) );
            Gia_ManDupWithFaddBoxes_rec( pNew, p, pObj, vFadds, vMap, vChains, vMap2Chain, vTruths );
        }
    // construct boxes
    iCiLit = 0;
    Vec_IntForEachEntry( vChain, iFadd, i )
    {
        int iXorTruth = Vec_IntEntry( vTruths, 2*iFadd+0 );
        int iMajTruth = Vec_IntEntry( vTruths, 2*iFadd+1 );
        for ( k = 0; k < 3; k++ )
        {
            pObj = Gia_ManObj( p, Vec_IntEntry(vFadds, 5*iFadd+k) );
            pLits[k] = (!k && iCiLit) ? iCiLit : pObj->Value;
            assert( pLits[k] >= 0 );
        }
        // normalize truth table
        //    if ( Truth == 0xE8 || Truth == 0xD4 || Truth == 0xB2 || Truth == 0x71 ||
        //         Truth == 0x17 || Truth == 0x2B || Truth == 0x4D || Truth == 0x8E )
        if ( iMajTruth == 0x4D )
            pLits[0] = Abc_LitNot(pLits[0]), iMajTruth = 0x8E, iXorTruth = 0xFF & ~iXorTruth;
        else if ( iMajTruth == 0xD4 )
            pLits[0] = Abc_LitNot(pLits[0]), iMajTruth = 0xE8, iXorTruth = 0xFF & ~iXorTruth;
        else if ( iMajTruth == 0x2B )
            pLits[1] = Abc_LitNot(pLits[1]), iMajTruth = 0x8E, iXorTruth = 0xFF & ~iXorTruth;
        else if ( iMajTruth == 0xB2 )
            pLits[1] = Abc_LitNot(pLits[1]), iMajTruth = 0xE8, iXorTruth = 0xFF & ~iXorTruth;
        if ( iMajTruth == 0x8E )
            pLits[2] = Abc_LitNot(pLits[2]), iMajTruth = 0xE8, iXorTruth = 0xFF & ~iXorTruth;
        else if ( iMajTruth == 0x71 )
            pLits[2] = Abc_LitNot(pLits[2]), iMajTruth = 0x17, iXorTruth = 0xFF & ~iXorTruth;
        else assert( iMajTruth == 0xE8 || iMajTruth == 0x17 );
        // normalize carry-in
        if ( Abc_LitIsCompl(pLits[0]) )
        {
            for ( k = 0; k < 3; k++ )
                pLits[k] = Abc_LitNot(pLits[k]);
            iXorTruth = 0xFF & ~iXorTruth;
            iMajTruth = 0xFF & ~iMajTruth;
        }
        // add COs
        assert( !Abc_LitIsCompl(pLits[0]) );
        for ( k = 0; k < 3; k++ )
            Gia_ManAppendCo( pNew, pLits[k] );
        // create CI
        assert( iXorTruth == 0x96 || iXorTruth == 0x69 );
        pObj = Gia_ManObj( p, Vec_IntEntry(vFadds, 5*iFadd+3) );
        pObj->Value = Abc_LitNotCond( Gia_ManAppendCi(pNew), (int)(iXorTruth == 0x69) );
        // create CI
        assert( iMajTruth == 0xE8 || iMajTruth == 0x17 );
        iCiLit = Abc_LitNotCond( Gia_ManAppendCi(pNew), (int)(iMajTruth == 0x17) );
    }   
    // assign carry out
    assert( iFadd == Vec_IntEntryLast(vChain) );
    pObj = Gia_ManObj( p, Vec_IntEntry(vFadds, 5*iFadd+4) );
    pObj->Value = iCiLit;
}
void Gia_ManDupWithFaddBoxes_rec( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vFadds, Vec_Int_t * vMap, Vec_Wec_t * vChains, Vec_Int_t * vMap2Chain, Vec_Int_t * vTruths )
{
    int iChain;
    if ( ~pObj->Value )
        return;
    assert( Gia_ObjIsAnd(pObj) );
    iChain = Vec_IntEntry( vMap2Chain, Gia_ObjId(p, pObj) );
/*
    assert( iChain == -1 );
    if ( iChain >= 0 )
    {
        Gia_ManDupFadd( pNew, p, Vec_WecEntry(vChains, iChain), vFadds, vMap, vChains, vMap2Chain, vTruths );
        assert( ~pObj->Value );
        return;
    }
*/
    Gia_ManDupWithFaddBoxes_rec( pNew, p, Gia_ObjFanin0(pObj), vFadds, vMap, vChains, vMap2Chain, vTruths );
    Gia_ManDupWithFaddBoxes_rec( pNew, p, Gia_ObjFanin1(pObj), vFadds, vMap, vChains, vMap2Chain, vTruths );
    pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
}
Gia_Man_t * Gia_ManDupWithFaddBoxes( Gia_Man_t * p, int nFaddMin, int fVerbose )
{
    abctime clk = Abc_Clock();
    Gia_Man_t * pNew, * pTemp;
    Vec_Int_t * vFadds, * vMap, * vMap2Chain, * vTruths, * vChain;
    Vec_Wec_t * vChains;
    Gia_Obj_t * pObj;  
    int i, nBoxes;

    // detect FADDs
    vFadds = Gia_ManDetectFullAdders( p, fVerbose );
    assert( Vec_IntSize(vFadds) % 5 == 0 );
    // map MAJ into its FADD
    vMap = Gia_ManCreateMap( p, vFadds );
    // for each FADD, find the longest chain and reorder its inputs
    Gia_ManFindChains( p, vFadds, vMap );
    // returns the set of topmost MAJ nodes
    vChains = Gia_ManCollectTopmost( p, vFadds, vMap, nFaddMin );
    if ( fVerbose )
        Gia_ManPrintChains( p, vFadds, vMap, vChains );
    if ( Vec_WecSize(vChains) == 0 )
    {
        Vec_IntFree( vFadds );
        Vec_IntFree( vMap );
        Vec_WecFree( vChains );
        return Gia_ManDup( p );
    }
    // returns mapping of each MAJ into the topmost elements of its chain
    vMap2Chain = Gia_ManFindMapping( p, vFadds, vMap, vChains );
    // compute truth tables for FADDs
    vTruths = Gia_ManCollectTruthTables( p, vFadds );
    if ( fVerbose )
        Abc_PrintTime( 1, "Carry-chain detection time", Abc_Clock() - clk );

    // duplicate
    clk = Abc_Clock();
    Gia_ManFillValue( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Vec_WecForEachLevel( vChains, vChain, i )
        Gia_ManDupFadd( pNew, p, vChain, vFadds, vMap, vChains, vMap2Chain, vTruths );
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManDupWithFaddBoxes_rec( pNew, p, Gia_ObjFanin0(pObj), vFadds, vMap, vChains, vMap2Chain, vTruths );
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    if ( Gia_ManRegNum(p) )
    {
        if ( fVerbose )
            printf( "Warning: Sequential design is coverted into combinational one by adding white boxes.\n" );
        pNew->nRegs = 0;
    }
    assert( !Gia_ManHasDangling(pNew) );

    // cleanup
    Vec_IntFree( vFadds );
    Vec_IntFree( vMap );
    Vec_WecFree( vChains );
    Vec_IntFree( vMap2Chain );
    Vec_IntFree( vTruths );
    
    // other information
    nBoxes = (Gia_ManCiNum(pNew) - Gia_ManCiNum(p)) / 2;
    assert( nBoxes == (Gia_ManCoNum(pNew) - Gia_ManCoNum(p)) / 3 );
    pNew->pManTime  = Gia_ManGenerateTim( Gia_ManCiNum(p), Gia_ManCoNum(p), nBoxes, 3, 2 );
    pNew->pAigExtra = Gia_ManGenerateExtraAig( nBoxes, 3, 2 );

    // normalize
    pNew = Gia_ManDupNormalize( pTemp = pNew );
    pNew->pManTime  = pTemp->pManTime;  pTemp->pManTime  = NULL;
    pNew->pAigExtra = pTemp->pAigExtra; pTemp->pAigExtra = NULL;
    Gia_ManStop( pTemp );

    //pNew = Gia_ManDupCollapse( pTemp = pNew, pNew->pAigExtra, NULL );
    //Gia_ManStop( pTemp );

    //Gia_ManIllustrateBoxes( pNew );
    if ( fVerbose )
        Abc_PrintTime( 1, "AIG with boxes construction time", Abc_Clock() - clk );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

