/**CFile****************************************************************

  FileName    [acecOrder.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [CEC for arithmetic circuits.]

  Synopsis    [Node ordering.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: acecOrder.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "acecInt.h"

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
Vec_Int_t * Gia_PolynReorder( Gia_Man_t * pGia, int fVerbose )
{
    int fDumpLeftOver = 0;
    Vec_Int_t * vOrder, * vOrder2;
    Gia_Obj_t * pFan0, * pFan1;
    int i, k, iDriver, Iter, iXor, iMaj, Entry, fFound;
    Vec_Int_t * vFadds = Gia_ManDetectFullAdders( pGia, fVerbose );
    Vec_Int_t * vHadds = Gia_ManDetectHalfAdders( pGia, fVerbose );
    Vec_Int_t * vRecord = Vec_IntAlloc( 100 );

    Vec_Int_t * vMap = Vec_IntStart( Gia_ManObjNum(pGia) );
    Gia_ManForEachCoDriverId( pGia, iDriver, i )
        Vec_IntWriteEntry( vMap, iDriver, 1 );

    for ( Iter = 0; ; Iter++ )
    {
        int fFoundAll = 0;
        printf( "Iteration %d\n", Iter );

        // find the last one
        iDriver = -1;
        Vec_IntForEachEntryReverse( vMap, Entry, i )
            if ( Entry )
            {
                iDriver = i;
                break;
            }

        if ( iDriver > 0 && Gia_ObjRecognizeExor(Gia_ManObj(pGia, iDriver), &pFan0, &pFan1) && Vec_IntFind(vFadds, iDriver) == -1 && Vec_IntFind(vHadds, iDriver) == -1 )
        {
            Vec_IntWriteEntry( vMap, iDriver, 0 );
            Vec_IntWriteEntry( vMap, Gia_ObjId(pGia, pFan0), 1 );
            Vec_IntWriteEntry( vMap, Gia_ObjId(pGia, pFan1), 1 );
            Vec_IntPush( vRecord, iDriver );
            printf( "Recognizing %d => XOR(%d %d)\n", iDriver, Gia_ObjId(pGia, pFan0), Gia_ObjId(pGia, pFan1) );
        }

        // check if we can extract FADDs
        do {
            fFound = 0;
            for ( i = 0; i < Vec_IntSize(vFadds)/5; i++ )
            {
                iXor = Vec_IntEntry(vFadds, 5*i+3);
                iMaj = Vec_IntEntry(vFadds, 5*i+4);
                if ( Vec_IntEntry(vMap, iXor) && Vec_IntEntry(vMap, iMaj) )
                {
                    Vec_IntWriteEntry( vMap, iXor, 0 );
                    Vec_IntWriteEntry( vMap, iMaj, 0 );
                    Vec_IntWriteEntry( vMap, Vec_IntEntry(vFadds, 5*i+0), 1 );
                    Vec_IntWriteEntry( vMap, Vec_IntEntry(vFadds, 5*i+1), 1 );
                    Vec_IntWriteEntry( vMap, Vec_IntEntry(vFadds, 5*i+2), 1 );
                    Vec_IntPush( vRecord, iXor );
                    Vec_IntPush( vRecord, iMaj );
                    fFound = 1;
                    fFoundAll = 1;
                    printf( "Recognizing (%d %d) => FA(%d %d %d)\n", iXor, iMaj, Vec_IntEntry(vFadds, 5*i+0), Vec_IntEntry(vFadds, 5*i+1), Vec_IntEntry(vFadds, 5*i+2)  );
                }
            }
        } while ( fFound );
        // check if we can extract HADDs
        do {
            fFound = 0;
            Vec_IntForEachEntryDouble( vHadds, iXor, iMaj, i )
            {
                if ( Vec_IntEntry(vMap, iXor) && Vec_IntEntry(vMap, iMaj) )
                {
                    Gia_Obj_t * pAnd = Gia_ManObj( pGia, iMaj );
                    Vec_IntWriteEntry( vMap, iXor, 0 );
                    Vec_IntWriteEntry( vMap, iMaj, 0 );
                    Vec_IntWriteEntry( vMap, Gia_ObjFaninId0(pAnd, iMaj), 1 );
                    Vec_IntWriteEntry( vMap, Gia_ObjFaninId1(pAnd, iMaj), 1 );
                    Vec_IntPush( vRecord, iXor );
                    Vec_IntPush( vRecord, iMaj );
                    fFound = 1;
                    fFoundAll = 1;
                    printf( "Recognizing (%d %d) => HA(%d %d)\n", iXor, iMaj, Gia_ObjFaninId0(pAnd, iMaj), Gia_ObjFaninId1(pAnd, iMaj) );
                }
            }
        } while ( fFound );
        if ( fFoundAll == 0 )
            break;
    }

    //Vec_IntPrint( vRecord );
    printf( "Remaining: " );
    Vec_IntForEachEntry( vMap, Entry, i )
        if ( Entry )
            printf( "%d ", i );
    printf( "\n" );

    // collect remaining nodes
    k = 0;
    Vec_IntForEachEntry( vMap, Entry, i )
        if ( Entry && Gia_ObjIsAnd(Gia_ManObj(pGia, i)) )
            Vec_IntWriteEntry( vMap, k++, i );
    Vec_IntShrink( vMap, k );

    // dump remaining nodes as an AIG
    if ( fDumpLeftOver )
    {        
        Gia_Man_t * pNew = Gia_ManDupAndCones( pGia, Vec_IntArray(vMap), Vec_IntSize(vMap), 0 );
        Gia_AigerWrite( pNew, "leftover.aig", 0, 0 );
        Gia_ManStop( pNew );
    }

    // collect nodes
    vOrder = Vec_IntAlloc( Gia_ManAndNum(pGia) );
    Gia_ManIncrementTravId( pGia );
    Gia_ManCollectAnds( pGia, Vec_IntArray(vMap), Vec_IntSize(vMap), vOrder, NULL );
    Vec_IntForEachEntryReverse( vRecord, Entry, i )
        Gia_ManCollectAnds_rec( pGia, Entry, vOrder );
    assert( Vec_IntSize(vOrder) == Gia_ManAndNum(pGia) );

    // remap order
    vOrder2 = Vec_IntStart( Gia_ManObjNum(pGia) );
    Vec_IntForEachEntry( vOrder, Entry, i )
        Vec_IntWriteEntry( vOrder2, Entry, i+1 );
    Vec_IntFree( vOrder );

    Vec_IntFree( vMap );
    Vec_IntFree( vRecord );
    Vec_IntFree( vFadds );
    Vec_IntFree( vHadds );
    return vOrder2;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

