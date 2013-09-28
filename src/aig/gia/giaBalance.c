/**CFile****************************************************************

  FileName    [giaBalance.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [AIG balancing.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaBalance.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

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

  Synopsis    [Simplify multi-input AND/XOR.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManSimplifyXor( Vec_Int_t * vSuper )
{
    int i, k = 0, Prev = -1, This, fCompl = 0;
    Vec_IntForEachEntry( vSuper, This, i )
    {
        if ( This == 0 )
            continue;
        if ( This == 1 )
            fCompl ^= 1; 
        else if ( Prev != This )
            Vec_IntWriteEntry( vSuper, k++, This ), Prev = This;
        else
            Prev = -1, k--;
    }
    Vec_IntShrink( vSuper, k );
    if ( !fCompl )
        return;
    if ( Vec_IntSize( vSuper ) == 0 )
        Vec_IntPush( vSuper, 1 );
    else
        Vec_IntWriteEntry( vSuper, 0, Abc_LitNot(Vec_IntEntry(vSuper, 0)) );
}
void Gia_ManSimplifyAnd( Vec_Int_t * vSuper )
{
    int i, k = 0, Prev = -1, This;
    Vec_IntForEachEntry( vSuper, This, i )
    {
        if ( This == 0 )
            { Vec_IntClear( vSuper ); return; }
        if ( This == 1 )
            continue;
        if ( Prev == -1 || Abc_Lit2Var(Prev) != Abc_Lit2Var(This) )
            Vec_IntWriteEntry( vSuper, k++, This ), Prev = This;
        else if ( Prev != This )
            { Vec_IntClear( vSuper ); return; }
    }
    Vec_IntShrink( vSuper, k );
}

/**Function*************************************************************

  Synopsis    [Collect multi-input AND/XOR.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManSuperCollectXor_rec( Gia_Man_t * p, Gia_Obj_t * pObj )
{
    assert( !Gia_IsComplement(pObj) );
    if ( !Gia_ObjIsXor(pObj) || Gia_ObjRefNum(p, pObj) > 1 || Vec_IntSize(p->vSuper) > 10000 )
    {
        Vec_IntPush( p->vSuper, Gia_ObjToLit(p, pObj) );
        return;
    }
    assert( !Gia_ObjFaninC0(pObj) && !Gia_ObjFaninC1(pObj) );
    Gia_ManSuperCollectXor_rec( p, Gia_ObjFanin0(pObj) );
    Gia_ManSuperCollectXor_rec( p, Gia_ObjFanin1(pObj) );
}
void Gia_ManSuperCollectAnd_rec( Gia_Man_t * p, Gia_Obj_t * pObj )
{
    if ( Gia_IsComplement(pObj) || !Gia_ObjIsAndReal(p, pObj) || Gia_ObjRefNum(p, pObj) > 1 || Vec_IntSize(p->vSuper) > 10000 )
    {
        Vec_IntPush( p->vSuper, Gia_ObjToLit(p, pObj) );
        return;
    }
    Gia_ManSuperCollectAnd_rec( p, Gia_ObjChild0(pObj) );
    Gia_ManSuperCollectAnd_rec( p, Gia_ObjChild1(pObj) );
}
void Gia_ManSuperCollect( Gia_Man_t * p, Gia_Obj_t * pObj )
{
    Vec_IntClear( p->vSuper );
    if ( Gia_ObjIsXor(pObj) )
    {
        assert( !Gia_ObjFaninC0(pObj) && !Gia_ObjFaninC1(pObj) );
        Gia_ManSuperCollectXor_rec( p, Gia_ObjFanin0(pObj) );
        Gia_ManSuperCollectXor_rec( p, Gia_ObjFanin1(pObj) );
        Vec_IntSort( p->vSuper, 0 );
        Gia_ManSimplifyXor( p->vSuper );
    }
    else if ( Gia_ObjIsAndReal(p, pObj) )
    {
        Gia_ManSuperCollectAnd_rec( p, Gia_ObjChild0(pObj) );
        Gia_ManSuperCollectAnd_rec( p, Gia_ObjChild1(pObj) );
        Vec_IntSort( p->vSuper, 0 );
        Gia_ManSimplifyAnd( p->vSuper );
    }
    else assert( 0 );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCreateGate( Gia_Man_t * pNew, Vec_Int_t * vSuper, Gia_Obj_t * pObj )
{
    int iLit0 = Vec_IntPop(vSuper);
    int iLit1 = Vec_IntPop(vSuper);
    int iLit, i;
    if ( Gia_ObjIsXor(pObj) )
        iLit = Gia_ManHashXorReal( pNew, iLit0, iLit1 );
    else
        iLit = Gia_ManHashAnd( pNew, iLit0, iLit1 );
    Vec_IntPush( vSuper, iLit );
    Gia_ObjSetGateLevel( pNew, Gia_ManObj(pNew, Abc_Lit2Var(iLit)) );
    // shift to the corrent location
    for ( i = Vec_IntSize(vSuper)-1; i > 0; i-- )
    {
        int iLit1 = Vec_IntEntry(vSuper, i);
        int iLit2 = Vec_IntEntry(vSuper, i-1);
        Gia_Obj_t * pNode1 = Gia_ManObj( pNew, Abc_Lit2Var(iLit1) );
        Gia_Obj_t * pNode2 = Gia_ManObj( pNew, Abc_Lit2Var(iLit2) );
        if ( Gia_ObjLevel(pNew, pNode1) <= Gia_ObjLevel(pNew, pNode2) )
            break;
        Vec_IntWriteEntry( vSuper, i,   iLit2 );
        Vec_IntWriteEntry( vSuper, i-1, iLit1 );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManBalance_rec( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj )
{
    int i, iLit, iBeg, iEnd;
    if ( ~pObj->Value )
        return;
    assert( Gia_ObjIsAnd(pObj) );
    // handle MUX
    if ( Gia_ObjIsMux(p, pObj) )
    {
        Gia_ManBalance_rec( pNew, p, Gia_ObjFanin0(pObj) );
        Gia_ManBalance_rec( pNew, p, Gia_ObjFanin1(pObj) );
        Gia_ManBalance_rec( pNew, p, Gia_ObjFanin2(p, pObj) );
        pObj->Value = Gia_ManHashMuxReal( pNew, Gia_ObjFanin2Copy(p, pObj), Gia_ObjFanin1Copy(pObj), Gia_ObjFanin0Copy(pObj) );
        Gia_ObjSetGateLevel( pNew, Gia_ManObj(pNew, Abc_Lit2Var(pObj->Value)) );
        return;
    }
    // find supergate
    Gia_ManSuperCollect( p, pObj );
    if ( Vec_IntSize(p->vSuper) == 0 )
    {
        pObj->Value = 0;
        return;
    }
    // save entries
    iBeg = Vec_IntSize( p->vStore );
    Vec_IntAppend( p->vStore, p->vSuper );
    iEnd = Vec_IntSize( p->vStore );
    // call recursively
    Vec_IntForEachEntryStartStop( p->vStore, iLit, i, iBeg, iEnd )
    {
        Gia_Obj_t * pTemp = Gia_ManObj( p, Abc_Lit2Var(iLit) );
        Gia_ManBalance_rec( pNew, p, pTemp );
        Vec_IntWriteEntry( p->vStore, i, Abc_LitNotCond(pTemp->Value, Abc_LitIsCompl(iLit)) );
    }
    assert( Vec_IntSize(p->vStore) == iEnd );
    // extract entries
    Vec_IntClear( p->vSuper );
    Vec_IntForEachEntryStartStop( p->vStore, iLit, i, iBeg, iEnd )
        Vec_IntPush( p->vSuper, iLit );
    // consider general case
    if ( Vec_IntSize(p->vSuper) > 2 )
    {
        // replace entries by their level
        int nSize, * pArray, * pPerm;
        Vec_IntForEachEntry( p->vSuper, iLit, i )
        {
            Gia_Obj_t * pTemp = Gia_ManObj( pNew, Abc_Lit2Var(iLit) );
            Vec_IntWriteEntry( p->vSuper, i, Gia_ObjLevel(pNew, pTemp) );
        }
        // allocate space
        nSize = Vec_IntSize( p->vSuper );
        Vec_IntGrow( p->vSuper, 4 * nSize );        
        pArray = Vec_IntArray( p->vSuper );
        pPerm = pArray + nSize;
        Abc_QuickSortCostData( pArray, nSize, 1, (word *)(pArray + 2 * nSize), pPerm );
        // collect entries in the increasing order of level
        for ( i = 0; i < nSize; i++ )
            Vec_IntWriteEntry( p->vSuper, i, Vec_IntEntry(p->vStore, iBeg + pPerm[i]) );
        Vec_IntShrink( p->vSuper, nSize );
        // perform incremental extraction
//        Vec_IntForEachEntry( p->vSuper, iLit, i )
//            printf( "%d ", Gia_ObjLevel(pNew, Gia_ManObj( pNew, Abc_Lit2Var(iLit) )) );
//        printf( "\n" );
        while ( Vec_IntSize(p->vSuper) > 1 )
            Gia_ManCreateGate( pNew, p->vSuper, pObj );
    }
    // consider trivial case
    else if ( Vec_IntSize(p->vSuper) == 2 )
        Gia_ManCreateGate( pNew, p->vSuper, pObj );
    assert( Vec_IntSize(p->vSuper) == 1 );
    pObj->Value = Vec_IntEntry( p->vSuper, 0 );
    Vec_IntShrink( p->vStore, iBeg );
}
Gia_Man_t * Gia_ManBalanceInt( Gia_Man_t * p )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    int i;
    Gia_ManFillValue( p );
    Gia_ManCreateRefs( p ); 
    assert( p->vStore == NULL );
    p->vStore = Vec_IntAlloc( 1000 );
    p->vSuper = Vec_IntAlloc( 1000 );
    // start the new manager
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    pNew->pMuxes = ABC_CALLOC( unsigned, pNew->nObjsAlloc );
    pNew->vLevels = Vec_IntStart( pNew->nObjsAlloc );
    // create constant and inputs
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    // create internal nodes
    Gia_ManHashStart( pNew );
    Gia_ManForEachCo( p, pObj, i )
    {
        Gia_ManBalance_rec( pNew, p, Gia_ObjFanin0(pObj) );
        pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    }
    assert( Gia_ManObjNum(pNew) <= Gia_ManObjNum(p) );
    Gia_ManHashStop( pNew );
    Vec_IntFree( p->vStore );
    Vec_IntFree( p->vSuper );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    // perform cleanup
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManBalance( Gia_Man_t * p, int fSimpleAnd, int fVerbose )
{
    Gia_Man_t * pNew, * pNew1, * pNew2;
    if ( fVerbose )      Gia_ManPrintStats( p, NULL );
    pNew = fSimpleAnd ? Gia_ManDup( p ) : Gia_ManDupMuxes( p );
    if ( fVerbose )      Gia_ManPrintStats( pNew, NULL );
    pNew1 = Gia_ManBalanceInt( pNew );
    if ( fVerbose )      Gia_ManPrintStats( pNew1, NULL );
    Gia_ManStop( pNew );
    pNew2 = Gia_ManDupNoMuxes( pNew1 );
    if ( fVerbose )      Gia_ManPrintStats( pNew2, NULL );
    Gia_ManStop( pNew1 );
    return pNew2;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

