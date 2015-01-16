/**CFile****************************************************************

  FileName    [cbaBlast.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Verilog parser.]

  Synopsis    [Parses several flavors of word-level Verilog.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 29, 2014.]

  Revision    [$Id: cbaBlast.c,v 1.00 2014/11/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cba.h"
#include "base/abc/abc.h"

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
int Cba_ManAddBarbuf( Gia_Man_t * pNew, int iRes, Cba_Man_t * p, int iLNtk, int iLObj, int iRNtk, int iRObj )
{
//    if ( iRes == 0 || iRes == 1 )
//        return iRes;
    Vec_IntPush( p->vBuf2LeafNtk, iLNtk );
    Vec_IntPush( p->vBuf2LeafObj, iLObj );
    Vec_IntPush( p->vBuf2RootNtk, iRNtk );
    Vec_IntPush( p->vBuf2RootObj, iRObj );
    return Gia_ManAppendBuf( pNew, iRes );
}
int Cba_ManExtract_rec( Gia_Man_t * pNew, Cba_Ntk_t * p, int i )
{
    int iRes = Cba_NtkCopy( p, i );
    if ( iRes >= 0 )
        return iRes;
    if ( Cba_ObjIsCo(p, i) )
        iRes = Cba_ManExtract_rec( pNew, p, Cba_ObjFanin0(p, i) );
    else if ( Cba_ObjIsBo(p, i) )
    {
        Cba_Ntk_t * pBox = Cba_ObjBoModel( p, i );
        int iObj = Cba_NtkPo( pBox, Cba_ObjCioIndex(p, i) );
        iRes = Cba_ManExtract_rec( pNew, pBox, iObj );
        iRes = Cba_ManAddBarbuf( pNew, iRes, p->pDesign, Cba_NtkId(p), i, Cba_NtkId(pBox), iObj );
    }
    else if ( Cba_ObjIsPi(p, i) )
    {
        Cba_Ntk_t * pHost = Cba_NtkHostNtk( p );
        int iObj = Cba_ObjBoxBi( pHost, Cba_NtkHostObj(p), Cba_ObjCioIndex(p, i) );
        iRes = Cba_ManExtract_rec( pNew, pHost, iObj );
        iRes = Cba_ManAddBarbuf( pNew, iRes, p->pDesign, Cba_NtkId(p), i, Cba_NtkId(pHost), iObj );
    }
    else if ( Cba_ObjIsNode(p, i) )
    {
        int * pFanins = Cba_ObjFaninArray(p, i);
        int k, pLits[3], Type = Cba_ObjNodeType(p, i);
        assert( pFanins[0] <= 3 );
        if ( pFanins[0] == 0 )
        {
            if ( Type == CBA_NODE_C0 )
                iRes = 0;
            else if ( Type == CBA_NODE_C1 )
                iRes = 1;
            else assert( 0 );
        }
        else if ( pFanins[0] == 1 )
        {
            if ( Type == CBA_NODE_BUF )
                iRes = Cba_ManExtract_rec( pNew, p, pFanins[1] );
            else if ( Type == CBA_NODE_INV )
                iRes = Abc_LitNot( Cba_ManExtract_rec( pNew, p, pFanins[1] ) );
            else assert( 0 );
        }
        else
        {
            for ( k = 0; k < pFanins[0]; k++ )
                pLits[k] = Cba_ManExtract_rec( pNew, p, pFanins[k+1] );
            if ( Type == CBA_NODE_AND )
                iRes = Gia_ManHashAnd( pNew, pLits[0], pLits[1] );
            else if ( Type == CBA_NODE_OR )
                iRes = Gia_ManHashOr( pNew, pLits[0], pLits[1] );
            else if ( Type == CBA_NODE_XOR )
                iRes = Gia_ManHashXor( pNew, pLits[0], pLits[1] );
            else if ( Type == CBA_NODE_XNOR )
                iRes = Abc_LitNot( Gia_ManHashXor( pNew, pLits[0], pLits[1] ) );
            else assert( 0 );
        }
    }
    else assert( 0 );
    Cba_NtkSetCopy( p, i, iRes );
    return iRes;
}
Gia_Man_t * Cba_ManExtract( Cba_Man_t * p, int fVerbose )
{
    Cba_Ntk_t * pRoot = Cba_ManRoot(p);
    Gia_Man_t * pNew, * pTemp; 
    int i, iObj;
    Vec_IntFreeP( &p->vBuf2LeafNtk );
    Vec_IntFreeP( &p->vBuf2LeafObj );
    Vec_IntFreeP( &p->vBuf2RootNtk );
    Vec_IntFreeP( &p->vBuf2RootObj );
    p->vBuf2LeafNtk = Vec_IntAlloc( 1000 );
    p->vBuf2LeafObj = Vec_IntAlloc( 1000 );
    p->vBuf2RootNtk = Vec_IntAlloc( 1000 );
    p->vBuf2RootObj = Vec_IntAlloc( 1000 );

    // start the manager
    pNew = Gia_ManStart( Cba_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav(p->pName);
    pNew->pSpec = Abc_UtilStrsav(p->pSpec);
    Vec_IntFill( &p->vCopies, Cba_ManObjNum(p), -1 );
    Cba_NtkForEachPi( pRoot, iObj, i )
        Cba_NtkSetCopy( pRoot, iObj, Gia_ManAppendCi(pNew) );
    Gia_ManHashAlloc( pNew );
    Cba_NtkForEachPo( pRoot, iObj, i )
        Cba_ManExtract_rec( pNew, pRoot, iObj );
    Gia_ManHashStop( pNew );
    Cba_NtkForEachPo( pRoot, iObj, i )
        Gia_ManAppendCo( pNew, Cba_NtkCopy(pRoot, iObj) );
    assert( Vec_IntSize(p->vBuf2LeafNtk) == pNew->nBufs );

    // cleanup
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    Gia_ManPrintStats( pNew, NULL );
//    pNew = Gia_ManSweepHierarchy( pTemp = pNew );
//    Gia_ManStop( pTemp );
//    Gia_ManPrintStats( pNew, NULL );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Returns the number of objects in each network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Cba_ManCountGia( Cba_Man_t * p, Gia_Man_t * pGia, int fAlwaysAdd )
{
    Cba_Ntk_t * pNtk;
    Gia_Obj_t * pObj; 
    int i, k, iBox, Count = 0;
    Vec_Int_t * vNtkSizes = Vec_IntStart( Cba_ManNtkNum(p) + 1 );
    Vec_Int_t * vDrivenCos = Vec_IntStart( Cba_ManNtkNum(p) + 1 );
    assert( Vec_IntSize(p->vBuf2LeafNtk) == Gia_ManBufNum(pGia) );
    // assing for each GIA node, the network it belongs to and count nodes for all networks
    Gia_ManConst0(pGia)->Value = 1;
    Gia_ManForEachPi( pGia, pObj, i )
        pObj->Value = 1;
    Gia_ManForEachAnd( pGia, pObj, i )
    {
        if ( Gia_ObjIsBuf(pObj) )
        {
            if ( Gia_ObjIsAnd(Gia_ObjFanin0(pObj)) )
                Vec_IntAddToEntry( vDrivenCos, Gia_ObjFanin0(pObj)->Value, 1 );
            pObj->Value = Vec_IntEntry( p->vBuf2LeafNtk, Count++ );
        }
        else
        {
            pObj->Value = Gia_ObjFanin0(pObj)->Value;
            assert( pObj->Value == Gia_ObjFanin1(pObj)->Value );
            Vec_IntAddToEntry( vNtkSizes, pObj->Value, 1 );
        }
    }
    assert( Count == Gia_ManBufNum(pGia) );
    Gia_ManForEachPo( pGia, pObj, i )
    {
        assert( Gia_ObjFanin0(pObj)->Value == 1 );
        pObj->Value = Gia_ObjFanin0(pObj)->Value;
        if ( Gia_ObjIsAnd(Gia_ObjFanin0(pObj)) )
            Vec_IntAddToEntry( vDrivenCos, pObj->Value, 1 );
    }
    // for each network, count the total number of COs
    Cba_ManForEachNtk( p, pNtk, i )
    {
        Count = Cba_NtkPiNum(pNtk) + 2 * Cba_NtkPoNum(pNtk) - (fAlwaysAdd ? 0 : Vec_IntEntry(vDrivenCos, i));
        Cba_NtkForEachBox( pNtk, iBox, k )
            Count += Cba_ObjBoxSize(pNtk, iBox) + Cba_ObjBoxBiNum(pNtk, iBox);
        Vec_IntAddToEntry( vNtkSizes, i, Count );
    }
    Vec_IntFree( vDrivenCos );
    return vNtkSizes;
}
void Cba_ManRemapBarbufs( Cba_Man_t * pNew, Cba_Man_t * p )
{
    Cba_Ntk_t * pNtk;  int Entry, i;
    assert( p->vBuf2RootNtk != NULL );
    assert( pNew->vBuf2RootNtk == NULL );
    pNew->vBuf2RootNtk = Vec_IntDup( p->vBuf2RootNtk );
    pNew->vBuf2RootObj = Vec_IntDup( p->vBuf2RootObj );
    pNew->vBuf2LeafNtk = Vec_IntDup( p->vBuf2LeafNtk );
    pNew->vBuf2LeafObj = Vec_IntDup( p->vBuf2LeafObj );
    Vec_IntForEachEntry( p->vBuf2LeafObj, Entry, i )
    {
        pNtk = Cba_ManNtk( p, Vec_IntEntry(p->vBuf2LeafNtk, i) );
        Vec_IntWriteEntry( pNew->vBuf2LeafObj, i, Cba_NtkCopy(pNtk, Entry) );
    }
    Vec_IntForEachEntry( p->vBuf2RootObj, Entry, i )
    {
        pNtk = Cba_ManNtk( p, Vec_IntEntry(p->vBuf2RootNtk, i) );
        Vec_IntWriteEntry( pNew->vBuf2RootObj, i, Cba_NtkCopy(pNtk, Entry) );
    }
}
void Cba_NtkCreateAndConnectBuffer( Gia_Man_t * pGia, Gia_Obj_t * pObj, Cba_Ntk_t * pNtk, int iTerm )
{
    Vec_IntWriteEntry( &pNtk->vTypes, pNtk->nObjs, CBA_OBJ_NODE );
    if ( !pGia || !Gia_ObjFaninId0p(pGia, pObj) )
    {
        Vec_IntWriteEntry( &pNtk->vFuncs,  pNtk->nObjs, pGia && Gia_ObjFaninC0(pObj) ? CBA_NODE_C1 : CBA_NODE_C0 );
        Vec_IntWriteEntry( &pNtk->vFanins, pNtk->nObjs, Cba_ManHandleBuffer(pNtk->pDesign, -1) );
    }
    else
    {
        Vec_IntWriteEntry( &pNtk->vFuncs,  pNtk->nObjs, Gia_ObjFaninC0(pObj) ? CBA_NODE_INV : CBA_NODE_BUF );
        Vec_IntWriteEntry( &pNtk->vFanins, pNtk->nObjs, Cba_ManHandleBuffer(pNtk->pDesign, Gia_ObjFanin0(pObj)->Value) );
    }
    Vec_IntWriteEntry( &pNtk->vNameIds, pNtk->nObjs, Cba_ObjNameId(pNtk, iTerm) );
    Vec_IntWriteEntry( &pNtk->vFanins, iTerm, pNtk->nObjs++ );
}
void Cba_NtkInsertGia( Cba_Man_t * p, Gia_Man_t * pGia )
{
    Cba_Ntk_t * pNtk, * pRoot = Cba_ManRoot( p );
    Vec_Int_t * vTemp = Vec_IntAlloc( 100 );
    int i, j, k, iBox, iTerm, Count = 0;
    Gia_Obj_t * pObj;

    Gia_ManConst0(pGia)->Value = ~0;
    Gia_ManForEachPi( pGia, pObj, i )
        pObj->Value = Cba_NtkPi( pRoot, i );
    Gia_ManForEachAnd( pGia, pObj, i )
    {
        if ( Gia_ObjIsBuf(pObj) )
        {
            pNtk = Cba_ManNtk( p, Vec_IntEntry(p->vBuf2RootNtk, Count) );
            iTerm = Vec_IntEntry( p->vBuf2RootObj, Count );
            assert( Cba_ObjIsCo(pNtk, iTerm) );
            Cba_NtkCreateAndConnectBuffer( pGia, pObj, pNtk, iTerm );
            // prepare leaf
            pObj->Value = Vec_IntEntry( p->vBuf2LeafObj, Count++ );
        }
        else
        {
            Cba_NodeType_t Type;
            pNtk = Cba_ManNtk( p, pObj->Value );
            if ( Gia_ObjFaninC0(pObj) && Gia_ObjFaninC1(pObj) )
                Type = CBA_NODE_AND00;
            else if ( Gia_ObjFaninC0(pObj) )
                Type = CBA_NODE_AND01;
            else if ( Gia_ObjFaninC1(pObj) )
                Type = CBA_NODE_AND10;
            else 
                Type = CBA_NODE_AND;
            Vec_IntFillTwo( vTemp, 2, Gia_ObjFanin0(pObj)->Value, Gia_ObjFanin1(pObj)->Value );
            Vec_IntWriteEntry( &pNtk->vTypes,  pNtk->nObjs, CBA_OBJ_NODE );
            Vec_IntWriteEntry( &pNtk->vFuncs,  pNtk->nObjs, Type );
            Vec_IntWriteEntry( &pNtk->vFanins, pNtk->nObjs, Cba_ManHandleArray(p, vTemp) );
            pObj->Value = pNtk->nObjs++;
        }
    }
    assert( Count == Gia_ManBufNum(pGia) );
    Vec_IntFree( vTemp );

    // create constant 0 drivers for COs without barbufs
    Cba_ManForEachNtk( p, pNtk, i )
    {
        Cba_NtkForEachBox( pNtk, iBox, k )
            Cba_BoxForEachBi( pNtk, iBox, iTerm, j )
                if ( Cba_ObjFanin0(pNtk, iTerm) == -1 )
                    Cba_NtkCreateAndConnectBuffer( NULL, NULL, pNtk, iTerm );
        Cba_NtkForEachPo( pNtk, iTerm, k )
            if ( pNtk != pRoot && Cba_ObjFanin0(pNtk, iTerm) == -1 )
                Cba_NtkCreateAndConnectBuffer( NULL, NULL, pNtk, iTerm );
    }
    // create node and connect POs
    Gia_ManForEachPo( pGia, pObj, i )
        Cba_NtkCreateAndConnectBuffer( pGia, pObj, pRoot, Cba_NtkPo(pRoot, i) );
    assert( Cba_NtkObjNum(pRoot) == pRoot->nObjs );
}
Cba_Man_t * Cba_ManInsertGia( Cba_Man_t * p, Gia_Man_t * pGia )
{
    Vec_Int_t * vNtkSizes = Cba_ManCountGia( p, pGia, 1 );
    Cba_Man_t * pNew = Cba_ManDupStart( p, vNtkSizes );
    Cba_ManRemapBarbufs( pNew, p );
    Cba_NtkInsertGia( pNew, pGia );
    Vec_IntFree( vNtkSizes );
    return pNew;

}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cba_Man_t * Cba_ManBlastTest( Cba_Man_t * p )
{
    Gia_Man_t * pGia = Cba_ManExtract( p, 0 );
    Cba_Man_t * pNew = Cba_ManInsertGia( p, pGia );
    Gia_ManStop( pGia );
    Cba_ManAssignInternNames( pNew );
    return pNew;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

