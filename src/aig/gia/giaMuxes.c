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
#include "misc/util/utilNam.h"
#include "misc/vec/vecWec.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Counts XORs and MUXes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCountMuxXor( Gia_Man_t * p, int * pnMuxes, int * pnXors )
{
    Gia_Obj_t * pObj, * pFan0, * pFan1; int i;
    *pnMuxes = *pnXors = 0;
    Gia_ManForEachAnd( p, pObj, i )
    {
        if ( !Gia_ObjIsMuxType(pObj) )
            continue;
        if ( Gia_ObjRecognizeExor(pObj, &pFan0, &pFan1) )
            (*pnXors)++;
        else
            (*pnMuxes)++;
    }
}
void Gia_ManPrintMuxStats( Gia_Man_t * p )
{
    int nAnds, nMuxes, nXors, nTotal;
    if ( p->pMuxes )
    {
        nAnds  = Gia_ManAndNotBufNum(p)-Gia_ManXorNum(p)-Gia_ManMuxNum(p);
        nXors  = Gia_ManXorNum(p);
        nMuxes = Gia_ManMuxNum(p);
        nTotal = nAnds + 3*nXors + 3*nMuxes;
    }
    else 
    {
        Gia_ManCountMuxXor( p, &nMuxes, &nXors );
        nAnds  = Gia_ManAndNotBufNum(p) - 3*nMuxes - 3*nXors;
        nTotal = Gia_ManAndNotBufNum(p);
    }
    Abc_Print( 1, "stats:  " );
    Abc_Print( 1, "xor =%8d %6.2f %%   ", nXors,  300.0*nXors/nTotal );
    Abc_Print( 1, "mux =%8d %6.2f %%   ", nMuxes, 300.0*nMuxes/nTotal );
    Abc_Print( 1, "and =%8d %6.2f %%   ", nAnds,  100.0*nAnds/nTotal );
    Abc_Print( 1, "obj =%8d  ", Gia_ManAndNotBufNum(p) );
    fflush( stdout );
}

/**Function*************************************************************

  Synopsis    [Derives GIA with MUXes.]

  Description [Create MUX if the sum of fanin references does not exceed limit.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDupMuxes( Gia_Man_t * p, int Limit )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj, * pFan0, * pFan1, * pFanC, * pSiblNew, * pObjNew;
    int i;
    assert( p->pMuxes == NULL );
    assert( Limit >= 2 );
    ABC_FREE( p->pRefs );
    Gia_ManCreateRefs( p ); 
    // start the new manager
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    pNew->pMuxes = ABC_CALLOC( unsigned, pNew->nObjsAlloc );
    if ( Gia_ManHasChoices(p) )
        pNew->pSibls = ABC_CALLOC( int, pNew->nObjsAlloc );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManHashStart( pNew );
    Gia_ManForEachObj1( p, pObj, i )
    {
        if ( Gia_ObjIsCi(pObj) )
            pObj->Value = Gia_ManAppendCi( pNew );
        else if ( Gia_ObjIsCo(pObj) )
            pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
        else if ( Gia_ObjIsBuf(pObj) )
            pObj->Value = Gia_ManAppendBuf( pNew, Gia_ObjFanin0Copy(pObj) );
        else if ( !Gia_ObjIsMuxType(pObj) || Gia_ObjSibl(p, Gia_ObjFaninId0(pObj, i)) || Gia_ObjSibl(p, Gia_ObjFaninId1(pObj, i)) )
            pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        else if ( Gia_ObjRecognizeExor(pObj, &pFan0, &pFan1) )
            pObj->Value = Gia_ManHashXorReal( pNew, Gia_ObjLitCopy(p, Gia_ObjToLit(p, pFan0)), Gia_ObjLitCopy(p, Gia_ObjToLit(p, pFan1)) );
        else if ( Gia_ObjRefNum(p, Gia_ObjFanin0(pObj)) + Gia_ObjRefNum(p, Gia_ObjFanin1(pObj)) > Limit )
            pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        else
        {
            pFanC = Gia_ObjRecognizeMux( pObj, &pFan1, &pFan0 );
            pObj->Value = Gia_ManHashMuxReal( pNew, Gia_ObjLitCopy(p, Gia_ObjToLit(p, pFanC)), Gia_ObjLitCopy(p, Gia_ObjToLit(p, pFan1)), Gia_ObjLitCopy(p, Gia_ObjToLit(p, pFan0)) );
        }
        if ( !Gia_ObjSibl(p, i) )
            continue;
        pObjNew  = Gia_ManObj( pNew, Abc_Lit2Var(pObj->Value) );
        pSiblNew = Gia_ManObj( pNew, Abc_Lit2Var(Gia_ObjSiblObj(p, i)->Value) );
        if ( Gia_ObjIsAnd(pObjNew) && Gia_ObjIsAnd(pSiblNew) && Gia_ObjId(pNew, pObjNew) > Gia_ObjId(pNew, pSiblNew) )
            pNew->pSibls[Gia_ObjId(pNew, pObjNew)] = Gia_ObjId(pNew, pSiblNew);
    }
    Gia_ManHashStop( pNew );
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
    Gia_ManConst0(p)->Value = 0;
    Gia_ManHashStart( pNew );
    Gia_ManForEachObj1( p, pObj, i )
    {
        if ( Gia_ObjIsCi(pObj) )
            pObj->Value = Gia_ManAppendCi( pNew );
        else if ( Gia_ObjIsCo(pObj) )
            pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
        else if ( Gia_ObjIsBuf(pObj) )
            pObj->Value = Gia_ManAppendBuf( pNew, Gia_ObjFanin0Copy(pObj) );
        else if ( Gia_ObjIsMuxId(p, i) )
            pObj->Value = Gia_ManHashMux( pNew, Gia_ObjFanin2Copy(p, pObj), Gia_ObjFanin1Copy(pObj), Gia_ObjFanin0Copy(pObj) );
        else if ( Gia_ObjIsXor(pObj) )
            pObj->Value = Gia_ManHashXor( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        else 
            pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    }
    Gia_ManHashStop( pNew );
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
    pNew = Gia_ManDupMuxes( p, 2 );
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
    if ( !Gia_ObjIsMuxId(p, iObj) )
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
    assert( Gia_ObjIsMuxId(p, iObj) );
    return Gia_MuxRef_rec( p, Gia_ObjFaninId0p(p, pObj) ) + 
           Gia_MuxRef_rec( p, Gia_ObjFaninId1p(p, pObj) ) + 
           Gia_MuxRef_rec( p, Gia_ObjFaninId2p(p, pObj) ) + 1;
}
int Gia_MuxDeref_rec( Gia_Man_t * p, int iObj )
{
    Gia_Obj_t * pObj;
    if ( !Gia_ObjIsMuxId(p, iObj) )
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
    assert( Gia_ObjIsMuxId(p, iObj) );
    return Gia_MuxDeref_rec( p, Gia_ObjFaninId0p(p, pObj) ) + 
           Gia_MuxDeref_rec( p, Gia_ObjFaninId1p(p, pObj) ) + 
           Gia_MuxDeref_rec( p, Gia_ObjFaninId2p(p, pObj) ) + 1;
}
int Gia_MuxMffcSize( Gia_Man_t * p, int iObj )
{
    int Count1, Count2;
    if ( !Gia_ObjIsMuxId(p, iObj) )
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
    int iCtrl;
    if ( !fFirst && (!Gia_ObjIsMuxId(p, iObj) || Gia_ObjRefNumId(p, iObj) > 0) )
    {
//        printf( "%d", iObj );
        printf( "<%02d>", Gia_ObjLevelId(p, iObj) );
        return;
    }
    iCtrl = Gia_ObjFaninId2p(p, pObj);
    printf( " [(" );
    if ( Gia_ObjIsMuxId(p, iCtrl) && Gia_ObjRefNumId(p, iCtrl) == 0 )
        Gia_MuxStructPrint_rec( p, iCtrl, 0 );
    else
    {
        printf( "%d", iCtrl );
        printf( "<%d>", Gia_ObjLevelId(p, iCtrl) );
    }
    printf( ")" );
    if ( Gia_ObjFaninC2(p, pObj) )
    {
        Gia_MuxStructPrint_rec( p, Gia_ObjFaninId0p(p, pObj), 0 );
        printf( "|" );
        Gia_MuxStructPrint_rec( p, Gia_ObjFaninId1p(p, pObj), 0 );
        printf( "]" );
    }
    else
    {
        Gia_MuxStructPrint_rec( p, Gia_ObjFaninId1p(p, pObj), 0 );
        printf( "|" );
        Gia_MuxStructPrint_rec( p, Gia_ObjFaninId0p(p, pObj), 0 );
        printf( "]" );
    }
}
void Gia_MuxStructPrint( Gia_Man_t * p, int iObj )
{
    int Count1, Count2;
    assert( Gia_ObjIsMuxId(p, iObj) );
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
void Gia_MuxStructDump_rec( Gia_Man_t * p, int iObj, int fFirst, Vec_Str_t * vStr, int nDigitsId )
{
    Gia_Obj_t * pObj = Gia_ManObj( p, iObj );
    int iCtrl;
    if ( !fFirst && (!Gia_ObjIsMuxId(p, iObj) || Gia_ObjRefNumId(p, iObj) > 0) )
        return;
    iCtrl = Gia_ObjFaninId2p(p, pObj);
    Vec_StrPush( vStr, '[' );
    Vec_StrPush( vStr, '(' );
    if ( Gia_ObjIsMuxId(p, iCtrl) && Gia_ObjRefNumId(p, iCtrl) == 0 )
        Gia_MuxStructDump_rec( p, iCtrl, 0, vStr, nDigitsId );
    else
        Vec_StrPrintNumStar( vStr, iCtrl, nDigitsId );
    Vec_StrPush( vStr, ')' );
    if ( Gia_ObjFaninC2(p, pObj) )
    {
        Gia_MuxStructDump_rec( p, Gia_ObjFaninId0p(p, pObj), 0, vStr, nDigitsId );
        Vec_StrPush( vStr, '|' );
        Gia_MuxStructDump_rec( p, Gia_ObjFaninId1p(p, pObj), 0, vStr, nDigitsId );
        Vec_StrPush( vStr, ']' );
    }
    else
    {
        Gia_MuxStructDump_rec( p, Gia_ObjFaninId1p(p, pObj), 0, vStr, nDigitsId );
        Vec_StrPush( vStr, '|' );
        Gia_MuxStructDump_rec( p, Gia_ObjFaninId0p(p, pObj), 0, vStr, nDigitsId );
        Vec_StrPush( vStr, ']' );
    }
}
int Gia_MuxStructDump( Gia_Man_t * p, int iObj, Vec_Str_t * vStr, int nDigitsNum, int nDigitsId )
{
    int Count1, Count2;
    assert( Gia_ObjIsMuxId(p, iObj) );
    Count1 = Gia_MuxDeref( p, iObj );
    Vec_StrClear( vStr );
    Vec_StrPrintNumStar( vStr, Count1, nDigitsNum );
    Gia_MuxStructDump_rec( p, iObj, 1, vStr, nDigitsId );
    Vec_StrPush( vStr, '\0' );
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
int Gia_ManMuxCompare( char ** pp1, char ** pp2 )
{
    int Diff = strcmp( *pp1, *pp2 );
    if ( Diff < 0 )
        return 1;
    if ( Diff > 0) 
        return -1;
    return 0; 
}
int Gia_ManMuxCountOne( char * p )
{
    int Count = 0;
    for ( ; *p; p++ )
        Count += (*p == '[');
    return Count;
}

typedef struct Mux_Man_t_ Mux_Man_t; 
struct Mux_Man_t_
{
    Gia_Man_t *     pGia;      // manager
    Abc_Nam_t *     pNames;    // hashing name into ID
    Vec_Wec_t *     vTops;     // top nodes for each struct
};

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Mux_Man_t * Mux_ManAlloc( Gia_Man_t * pGia )
{
    Mux_Man_t * p;
    p = ABC_CALLOC( Mux_Man_t, 1 );
    p->pGia   = pGia;
    p->pNames = Abc_NamStart( 10000, 50 );
    p->vTops  = Vec_WecAlloc( 1000 );
    Vec_WecPushLevel( p->vTops );
    return p;
}
void Mux_ManFree( Mux_Man_t * p )
{
    Abc_NamStop( p->pNames );
    Vec_WecFree( p->vTops );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManMuxProfile( Mux_Man_t * p, int fWidth )
{
    int i, Entry, Counter, Total;
    Vec_Int_t * vVec, * vCounts;
    vCounts = Vec_IntStart( 1000 );
    if ( fWidth )
    {
        Vec_WecForEachLevelStart( p->vTops, vVec, i, 1 )
            Vec_IntAddToEntry( vCounts, Abc_MinInt(Vec_IntSize(vVec), 999), 1 );
    }
    else
    {
        for ( i = 1; i < Vec_WecSize(p->vTops); i++ )
            Vec_IntAddToEntry( vCounts, Abc_MinInt(atoi(Abc_NamStr(p->pNames, i)), 999), 1 );
    }
    Total = Vec_IntCountPositive(vCounts);
    if ( Total == 0 )
        return 0;
    printf( "The distribution of MUX tree %s:\n", fWidth ? "widths" : "sizes"  );
    Counter = 0;
    Vec_IntForEachEntry( vCounts, Entry, i )
    {
        if ( !Entry ) continue;
        if ( ++Counter == 12 )
            printf( "\n" ), Counter = 0;
        printf( "  %d=%d", i, Entry );
    }
    printf( "\nSummary: " );
    printf( "Max = %d  ", Vec_IntFindMax(vCounts) );
    printf( "Ave = %.2f", 1.0*Vec_IntSum(vCounts)/Total );
    printf( "\n" );
    Vec_IntFree( vCounts );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManMuxProfiling( Gia_Man_t * p )
{
    Mux_Man_t * pMan;
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    Vec_Str_t * vStr;
    Vec_Int_t * vFans, * vVec;
    int i, Counter, fFound, iStructId, nDigitsId;
    abctime clk = Abc_Clock();

    pNew = Gia_ManDupMuxes( p, 2 );
    nDigitsId = Abc_Base10Log( Gia_ManObjNum(pNew) );

    pMan = Mux_ManAlloc( pNew );
     
    Gia_ManLevelNum( pNew );
    Gia_ManCreateRefs( pNew );
    Gia_ManForEachCo( pNew, pObj, i )
        Gia_ObjRefFanin0Inc( pNew, pObj );

    vStr = Vec_StrAlloc( 1000 );
    vFans = Gia_ManFirstFanouts( pNew );
    Gia_ManForEachMux( pNew, pObj, i )
    {
        // skip MUXes in the middle of the tree (which have only one MUX fanout)
        if ( Gia_ObjRefNumId(pNew, i) == 1 && Gia_ObjIsMuxId(pNew, Vec_IntEntry(vFans, i)) )
            continue;
        // this node is the root of the MUX structure - create hash key
        Counter = Gia_MuxStructDump( pNew, i, vStr, 3, nDigitsId );
        if ( Counter == 1 )
            continue;
        iStructId = Abc_NamStrFindOrAdd( pMan->pNames, Vec_StrArray(vStr), &fFound );
        if ( !fFound )
            Vec_WecPushLevel( pMan->vTops );
        assert( Abc_NamObjNumMax(pMan->pNames) == Vec_WecSize(pMan->vTops) );
        Vec_IntPush( Vec_WecEntry(pMan->vTops, iStructId), i );
    }
    Vec_StrFree( vStr );
    Vec_IntFree( vFans );

    printf( "MUX structure profile for AIG \"%s\":\n", p->pName );
    printf( "Total MUXes = %d.  Total trees = %d.  Unique trees = %d.  Memory = %.2f MB   ", 
        Gia_ManMuxNum(pNew), Vec_WecSizeSize(pMan->vTops), Vec_WecSize(pMan->vTops)-1, 
        1.0*Abc_NamMemUsed(pMan->pNames)/(1<<20) );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );

    if ( Gia_ManMuxProfile(pMan, 0) )
    {
        Gia_ManMuxProfile( pMan, 1 );

        // short the first ones
        printf( "The first %d structures: \n", 10 );
        Vec_WecForEachLevelStartStop( pMan->vTops, vVec, i, 1, Abc_MinInt(Vec_WecSize(pMan->vTops), 10) )
        {
            char * pTemp = Abc_NamStr(pMan->pNames, i);
            printf( "%5d : ", i );
            printf( "Occur = %4d   ", Vec_IntSize(vVec) );
            printf( "Size = %4d   ", atoi(pTemp) );
            printf( "%s\n", pTemp );
        }

        // print trees for the first one
        Counter = 0;
        Vec_WecForEachLevelStart( pMan->vTops, vVec, i, 1 )
        {
            char * pTemp = Abc_NamStr(pMan->pNames, i);
            if ( Vec_IntSize(vVec) > 5 && atoi(pTemp) > 5 )
            {
                int k, Entry;
                printf( "For example, structure %d has %d MUXes and bit-width %d:\n", i, atoi(pTemp), Vec_IntSize(vVec) );
                Vec_IntForEachEntry( vVec, Entry, k )
                    Gia_MuxStructPrint( pNew, Entry );
                if ( ++Counter == 5 )
                    break;
            }
        }
    }

    Mux_ManFree( pMan );
    Gia_ManStop( pNew );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

