/**CFile****************************************************************

  FileName    [wlcGraft.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Verilog parser.]

  Synopsis    [Parses several flavors of word-level Verilog.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 22, 2014.]

  Revision    [$Id: wlcGraft.c,v 1.00 2014/09/12 00:00:00 alanmi Exp $]

***********************************************************************/

#include "wlc.h"
#include "sat/bsat/satStore.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Internal simulation APIs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline word * Wlc_ObjSim( Gia_Man_t * p, int iObj )
{
    return Vec_WrdEntryP( p->vSims, p->nSimWords * iObj );
}
static inline void Wlc_ObjSimPi( Gia_Man_t * p, int iObj )
{
    int w;
    word * pSim = Wlc_ObjSim( p, iObj );
    for ( w = 0; w < p->nSimWords; w++ )
        pSim[w] = Gia_ManRandomW( 0 );
    pSim[0] <<= 1;
}
static inline void Wlc_ObjSimRo( Gia_Man_t * p, int iObj )
{
    int w;
    word * pSimRo = Wlc_ObjSim( p, iObj );
    word * pSimRi = Wlc_ObjSim( p, Gia_ObjRoToRiId(p, iObj) );
    for ( w = 0; w < p->nSimWords; w++ )
        pSimRo[w] = pSimRi[w];
}
static inline void Wlc_ObjSimCo( Gia_Man_t * p, int iObj )
{
    int w;
    Gia_Obj_t * pObj = Gia_ManObj( p, iObj );
    word * pSimCo  = Wlc_ObjSim( p, iObj );
    word * pSimDri = Wlc_ObjSim( p, Gia_ObjFaninId0(pObj, iObj) );
    if ( Gia_ObjFaninC0(pObj) )
        for ( w = 0; w < p->nSimWords; w++ )
            pSimCo[w] = ~pSimDri[w];
    else
        for ( w = 0; w < p->nSimWords; w++ )
            pSimCo[w] =  pSimDri[w];
}
static inline void Wlc_ObjSimAnd( Gia_Man_t * p, int iObj )
{
    int w;
    Gia_Obj_t * pObj = Gia_ManObj( p, iObj );
    word * pSim  = Wlc_ObjSim( p, iObj );
    word * pSim0 = Wlc_ObjSim( p, Gia_ObjFaninId0(pObj, iObj) );
    word * pSim1 = Wlc_ObjSim( p, Gia_ObjFaninId1(pObj, iObj) );
    if ( Gia_ObjFaninC0(pObj) && Gia_ObjFaninC1(pObj) )
        for ( w = 0; w < p->nSimWords; w++ )
            pSim[w] = ~pSim0[w] & ~pSim1[w];
    else if ( Gia_ObjFaninC0(pObj) && !Gia_ObjFaninC1(pObj) )
        for ( w = 0; w < p->nSimWords; w++ )
            pSim[w] = ~pSim0[w] & pSim1[w];
    else if ( !Gia_ObjFaninC0(pObj) && Gia_ObjFaninC1(pObj) )
        for ( w = 0; w < p->nSimWords; w++ )
            pSim[w] = pSim0[w] & ~pSim1[w];
    else
        for ( w = 0; w < p->nSimWords; w++ )
            pSim[w] = pSim0[w] & pSim1[w];
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Wlc_NtkCollectObjs_rec( Wlc_Ntk_t * p, Wlc_Obj_t * pObj, Vec_Int_t * vObjs )
{
    int i, iFanin, Count = 0;
    if ( Wlc_ObjIsCi(pObj) )
        return 0;
    if ( pObj->Mark )
        return 0;
    pObj->Mark = 1;
    Wlc_ObjForEachFanin( pObj, iFanin, i )
        Count += Wlc_NtkCollectObjs_rec( p, Wlc_NtkObj(p, iFanin), vObjs );
    Vec_IntPush( vObjs, Wlc_ObjId(p, pObj) );
    return Count + (int)(pObj->Type == WLC_OBJ_ARI_MULTI);
}
Vec_Int_t * Wlc_NtkCollectObjs( Wlc_Ntk_t * p, int fEven, int * pCount )
{
    Vec_Int_t * vObjs = Vec_IntAlloc( 100 );
    Wlc_Obj_t * pObj; 
    int i, Count = 0;
    Wlc_NtkCleanMarks( p );
    Wlc_NtkForEachCo( p, pObj, i )
        if ( (i & 1) == fEven )
            Count += Wlc_NtkCollectObjs_rec( p, pObj, vObjs );
    Wlc_NtkCleanMarks( p );
    if ( pCount )
        *pCount = Count;
    return vObjs;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Wlc_NtkSaveOneNode( Wlc_Ntk_t * p, Wlc_Obj_t * pWlcObj, Gia_Man_t * pGia, Vec_Mem_t * vTtMem )
{
    int k, Entry;
    int nWords = Vec_MemEntrySize(vTtMem);
    int nBits = Wlc_ObjRange(pWlcObj);
    int iFirst = Vec_IntEntry( &p->vCopies, Wlc_ObjId(p, pWlcObj) );
    for ( k = 0; k < nBits; k++ )
    {
        int iLit = Vec_IntEntry( &p->vBits, iFirst + k );
        word * pInfoObj = Wlc_ObjSim( pGia, Abc_Lit2Var(iLit) );
        int fCompl = pInfoObj[0] & 1;
        if ( fCompl ) Abc_TtNot( pInfoObj, nWords );
        Entry = Vec_MemHashInsert( vTtMem, pInfoObj );
        if ( fCompl ) Abc_TtNot( pInfoObj, nWords );
        printf( "%2d(%d) ", Entry, fCompl ^ Abc_LitIsCompl(iLit) );
        Extra_PrintHex( stdout, (unsigned*)pInfoObj, 8 );
        printf( "\n" );
    }
    printf( "\n" );
}
void Wlc_NtkFindOneNode( Wlc_Ntk_t * p, Wlc_Obj_t * pWlcObj, Gia_Man_t * pGia, Vec_Mem_t * vTtMem )
{
    int k, Entry;
    int nWords = Vec_MemEntrySize(vTtMem);
    int nBits = Wlc_ObjRange(pWlcObj);
    int iFirst = Vec_IntEntry( &p->vCopies, Wlc_ObjId(p, pWlcObj) );
    for ( k = 0; k < nBits; k++ )
    {
        int iLit = Vec_IntEntry( &p->vBits, iFirst + k );
        word * pInfoObj = Wlc_ObjSim( pGia, Abc_Lit2Var(iLit) );
        int fCompl = pInfoObj[0] & 1;
        if ( fCompl ) Abc_TtNot( pInfoObj, nWords );
        Entry = *Vec_MemHashLookup( vTtMem, pInfoObj );
        if ( Entry > 0 )
            printf( "Obj %4d.  Range = %2d.  Bit %2d.  Entry %d(%d).  %s\n", Wlc_ObjId(p, pWlcObj), Wlc_ObjRange(pWlcObj), k, Entry, fCompl ^ Abc_LitIsCompl(iLit), Wlc_ObjName(p, Wlc_ObjId(p, pWlcObj)) );
        if ( fCompl ) Abc_TtNot( pInfoObj, nWords );
        //printf( "%2d ", Entry );
        //Extra_PrintHex( stdout, (unsigned*)pInfoObj, 8 );
        //printf( "\n" );
    }
    //printf( "\n" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Wlc_Ntk_t * Wlc_NtkGraftMulti( Wlc_Ntk_t * p, int fVerbose )
{
    int nWords = 4;
    int i, nMultiLHS, nMultiRHS;
    word * pInfoObj;
    Wlc_Ntk_t * pNew = NULL;
    Wlc_Obj_t * pWlcObj;
    Gia_Obj_t * pObj;
    Vec_Int_t * vObjsLHS = Wlc_NtkCollectObjs( p, 0, &nMultiLHS );
    Vec_Int_t * vObjsRHS = Wlc_NtkCollectObjs( p, 1, &nMultiRHS );
    Gia_Man_t * pGia = Wlc_NtkBitBlast( p, NULL, -1, 0, 0, 0, 0, 1 );
    Vec_Mem_t * vTtMem = Vec_MemAlloc( nWords, 10 );
    Vec_MemHashAlloc( vTtMem, 10000 );

    // check if there are multipliers
    if ( nMultiLHS == 0 && nMultiRHS == 0 )
    {
        printf( "No multipliers are present.\n" );
        return NULL;
    }
    // compare multipliers
    if ( nMultiLHS > 0 && nMultiRHS > 0 )
    {
        printf( "Multipliers are present in both sides of the miter.\n" );
        return NULL;
    }
    // swap if wrong side
    if ( nMultiRHS > 0 )
    {
        ABC_SWAP( Vec_Int_t *, vObjsLHS, vObjsRHS );
        ABC_SWAP( int, nMultiLHS, nMultiRHS );
    }
    assert( nMultiLHS > 0 );
    assert( nMultiRHS == 0 );

    // allocate simulation info for one timeframe
    Vec_WrdFreeP( &pGia->vSims );
    pGia->vSims = Vec_WrdStart( Gia_ManObjNum(pGia) * nWords );
    pGia->nSimWords = nWords;
    // perform simulation
    Gia_ManRandomW( 1 );
    Gia_ManForEachObj1( pGia, pObj, i )
    {
        if ( Gia_ObjIsAnd(pObj) )
            Wlc_ObjSimAnd( pGia, i );
        else if ( Gia_ObjIsCo(pObj) )
            Wlc_ObjSimCo( pGia, i );
        else if ( Gia_ObjIsCi(pObj) )
            Wlc_ObjSimPi( pGia, i );
        else assert( 0 );
    }

    // hash constant 0
    pInfoObj = Wlc_ObjSim( pGia, 0 );
    Vec_MemHashInsert( vTtMem, pInfoObj );

    // hash sim info on the multiplier boundary
    Wlc_NtkForEachObjVec( vObjsLHS, p, pWlcObj, i )
        if ( Wlc_ObjType(pWlcObj) == WLC_OBJ_ARI_MULTI )
        {
            Wlc_NtkSaveOneNode( p, Wlc_ObjFanin0(p, pWlcObj), pGia, vTtMem );
            Wlc_NtkSaveOneNode( p, Wlc_ObjFanin1(p, pWlcObj), pGia, vTtMem );
            Wlc_NtkSaveOneNode( p, pWlcObj, pGia, vTtMem );
        }

    // check if there are similar signals in LHS
    Wlc_NtkForEachObjVec( vObjsRHS, p, pWlcObj, i )
        Wlc_NtkFindOneNode( p, pWlcObj, pGia, vTtMem );

    // perform grafting


    Vec_MemHashFree( vTtMem );
    Vec_MemFreeP( &vTtMem );

    // cleanup
    Vec_WrdFreeP( &pGia->vSims );
    pGia->nSimWords = 0;

    Vec_IntFree( vObjsLHS );
    Vec_IntFree( vObjsRHS );
    Gia_ManStop( pGia );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

