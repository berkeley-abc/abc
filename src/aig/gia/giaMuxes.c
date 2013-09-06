/**CFile****************************************************************

  FileName    [giaMuxes.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Multiplexer profiling algorithm.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaMuxes.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

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

  Synopsis    [Derives GIA with MUXes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDupMuxes( Gia_Man_t * p )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj, * pFan0, * pFan1, * pFanC;
    int i;
    assert( p->pMuxes == NULL );
    // start the new manager
    pNew = Gia_ManStart( 5000 );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    pNew->pMuxes = ABC_CALLOC( unsigned, pNew->nObjsAlloc );
    // create constant
    Gia_ManConst0(p)->Value = 0;
    // create PIs
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    // create internal nodes
    Gia_ManHashStart( pNew );
    Gia_ManForEachAnd( p, pObj, i )
    {
        if ( !Gia_ObjIsMuxType(pObj) )
            pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        else if ( Gia_ObjRecognizeExor(pObj, &pFan0, &pFan1) )
            pObj->Value = Gia_ManHashXorReal( pNew, Gia_ObjLitCopy(p, Gia_ObjToLit(p, pFan0)), Gia_ObjLitCopy(p, Gia_ObjToLit(p, pFan1)) );
        else
        {
            pFanC = Gia_ObjRecognizeMux( pObj, &pFan1, &pFan0 );
            pObj->Value = Gia_ManHashMuxReal( pNew, Gia_ObjLitCopy(p, Gia_ObjToLit(p, pFanC)), Gia_ObjLitCopy(p, Gia_ObjToLit(p, pFan1)), Gia_ObjLitCopy(p, Gia_ObjToLit(p, pFan0)) );
        }
    }
    Gia_ManHashStop( pNew );
    // create ROs
    Gia_ManForEachCo( p, pObj, i )
        pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    // perform cleanup
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Derives GIA without MUXes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDupNoMuxes( Gia_Man_t * p )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    int i;
    assert( p->pMuxes != NULL );
    // start the new manager
    pNew = Gia_ManStart( 5000 );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    // create constant
    Gia_ManConst0(p)->Value = 0;
    // create PIs
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    // create internal nodes
    Gia_ManHashStart( pNew );
    Gia_ManForEachAnd( p, pObj, i )
    {
        if ( Gia_ObjIsMux(p, i) )
            pObj->Value = Gia_ManHashMux( pNew, Gia_ObjFanin2Copy(p, pObj), Gia_ObjFanin1Copy(pObj), Gia_ObjFanin0Copy(pObj) );
        else if ( Gia_ObjIsXor(pObj) )
            pObj->Value = Gia_ManHashXor( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        else 
            pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    }
    Gia_ManHashStop( pNew );
    // create ROs
    Gia_ManForEachCo( p, pObj, i )
        pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    // perform cleanup
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Test these procedures.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDupMuxesTest( Gia_Man_t * p )
{
    Gia_Man_t * pNew, * pNew2;
    pNew = Gia_ManDupMuxes( p );
    pNew2 = Gia_ManDupNoMuxes( pNew );
    Gia_ManPrintStats( p, NULL );
    Gia_ManPrintStats( pNew, NULL );
    Gia_ManPrintStats( pNew2, NULL );
    Gia_ManStop( pNew );
//    Gia_ManStop( pNew2 );
    return pNew2;
}


/**Function*************************************************************

  Synopsis    [Returns the size of MUX structure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_MuxRef_rec( Gia_Man_t * p, int iObj )
{
    Gia_Obj_t * pObj;
    if ( !Gia_ObjIsMux(p, iObj) )
        return 0;
    pObj = Gia_ManObj( p, iObj );
    if ( Gia_ObjRefInc(p, pObj) )
        return 0;
    return Gia_MuxRef_rec( p, Gia_ObjFaninId0p(p, pObj) ) + 
           Gia_MuxRef_rec( p, Gia_ObjFaninId1p(p, pObj) ) + 
           Gia_MuxRef_rec( p, Gia_ObjFaninId2p(p, pObj) ) + 1;
}
int Gia_MuxRef( Gia_Man_t * p, int iObj )
{
    Gia_Obj_t * pObj = Gia_ManObj( p, iObj );
    assert( Gia_ObjIsMux(p, iObj) );
    return Gia_MuxRef_rec( p, Gia_ObjFaninId0p(p, pObj) ) + 
           Gia_MuxRef_rec( p, Gia_ObjFaninId1p(p, pObj) ) + 
           Gia_MuxRef_rec( p, Gia_ObjFaninId2p(p, pObj) ) + 1;
}
int Gia_MuxDeref_rec( Gia_Man_t * p, int iObj )
{
    Gia_Obj_t * pObj;
    if ( !Gia_ObjIsMux(p, iObj) )
        return 0;
    pObj = Gia_ManObj( p, iObj );
    if ( Gia_ObjRefDec(p, pObj) )
        return 0;
    return Gia_MuxDeref_rec( p, Gia_ObjFaninId0p(p, pObj) ) + 
           Gia_MuxDeref_rec( p, Gia_ObjFaninId1p(p, pObj) ) + 
           Gia_MuxDeref_rec( p, Gia_ObjFaninId2p(p, pObj) ) + 1;
}
int Gia_MuxDeref( Gia_Man_t * p, int iObj )
{
    Gia_Obj_t * pObj = Gia_ManObj( p, iObj );
    assert( Gia_ObjIsMux(p, iObj) );
    return Gia_MuxDeref_rec( p, Gia_ObjFaninId0p(p, pObj) ) + 
           Gia_MuxDeref_rec( p, Gia_ObjFaninId1p(p, pObj) ) + 
           Gia_MuxDeref_rec( p, Gia_ObjFaninId2p(p, pObj) ) + 1;
}
int Gia_MuxMffcSize( Gia_Man_t * p, int iObj )
{
    int Count1, Count2;
    if ( !Gia_ObjIsMux(p, iObj) )
        return 0;
    Count1 = Gia_MuxDeref( p, iObj );
    Count2 = Gia_MuxRef( p, iObj );
    assert( Count1 == Count2 );
    return Count1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_MuxStructPrint_rec( Gia_Man_t * p, int iObj, int fFirst )
{
    Gia_Obj_t * pObj = Gia_ManObj( p, iObj );
    if ( !fFirst && (!Gia_ObjIsMux(p, iObj) || Gia_ObjRefNumId(p, iObj) > 0) )
        return;
    printf( " [(%s", Gia_ObjFaninC2(p, pObj)? "!": "" );
    if ( !Gia_ObjIsMux(p, Gia_ObjFaninId2p(p, pObj)) )
        printf( "%d", Gia_ObjFaninId2p(p, pObj) );
    else
        Gia_MuxStructPrint_rec( p, Gia_ObjFaninId2p(p, pObj), 0 );
    printf( ")" );
    Gia_MuxStructPrint_rec( p, Gia_ObjFaninId0p(p, pObj), 0 );
    printf( "|" );
    Gia_MuxStructPrint_rec( p, Gia_ObjFaninId1p(p, pObj), 0 );
    printf( "] " );
}
void Gia_MuxStructPrint( Gia_Man_t * p, int iObj )
{
    int Count1, Count2;
    assert( Gia_ObjIsMux(p, iObj) );
    Count1 = Gia_MuxDeref( p, iObj );
    Gia_MuxStructPrint_rec( p, iObj, 1 );
    Count2 = Gia_MuxRef( p, iObj );
    assert( Count1 == Count2 );
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManMuxProfiling( Gia_Man_t * p )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    Vec_Int_t * vFans;
    Vec_Int_t * vCounts;
    int i, nRefs, Size, Count, Total = 0, Roots = 0;

    pNew = Gia_ManDupMuxes( p );
    Gia_ManCreateRefs( pNew );
    Gia_ManForEachCo( pNew, pObj, i )
        Gia_ObjRefFanin0Inc( pNew, pObj );

    vFans = Gia_ManFirstFanouts( pNew );
    vCounts = Vec_IntStart( 100 );
    Gia_ManForEachMux( pNew, pObj, i )
    {
        Total++;
        nRefs = Gia_ObjRefNumId(pNew, i);
        assert( nRefs > 0 );
        if ( nRefs > 1 || !Gia_ObjIsMux(pNew, Vec_IntEntry(vFans, i)) )
        {
            Roots++;
            Size = Gia_MuxMffcSize(pNew, i);
            Vec_IntAddToEntry( vCounts, Abc_MinInt(Size, 99), 1 );

            if ( Size > 3 )
            {
                printf( "%d ", Size );
                Gia_MuxStructPrint( pNew, i );
            }
        }
    }
    printf( "MUXes: Total = %d. Roots = %d.\n", Total, Roots );

    Vec_IntForEachEntry( vCounts, Count, i )
        if ( Count )
            printf( "%d=%d ", i, Count );
    printf( "\n" );

    Vec_IntFree( vCounts );
    Vec_IntFree( vFans );
    Gia_ManStop( pNew );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

