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
void Cba_ManExtractSave( Cba_Man_t * p, int iLNtk, int iLObj, int iRNtk, int iRObj )
{
    Vec_IntPush( p->vBuf2LeafNtk, iLNtk );
    Vec_IntPush( p->vBuf2LeafObj, iLObj );
    Vec_IntPush( p->vBuf2RootNtk, iRNtk );
    Vec_IntPush( p->vBuf2RootObj, iRObj );
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
        iRes = Gia_ManAppendBuf( pNew, iRes );
        Cba_ManExtractSave( p->pDesign, Cba_NtkId(p), i, Cba_NtkId(pBox), iObj );
    }
    else if ( Cba_ObjIsPi(p, i) )
    {
        Cba_Ntk_t * pHost = Cba_NtkHost( p );
        int iObj = Cba_ObjBoxBi( pHost, p->iBoxObj, Cba_ObjCioIndex(p, i) );
        iRes = Cba_ManExtract_rec( pNew, pHost, iObj );
        iRes = Gia_ManAppendBuf( pNew, iRes );
        Cba_ManExtractSave( p->pDesign, Cba_NtkId(p), i, Cba_NtkId(pHost), iObj );
    }
    else if ( Cba_ObjIsNode(p, i) )
    {
        int * pFanins = Cba_ObjFaninArray(p, i);
        int k, pLits[3], Type = Cba_ObjNodeType(p, i);
        assert( pFanins[0] <= 3 );
        for ( k = 0; k < pFanins[0]; k++ )
            pLits[k] = Cba_ManExtract_rec( pNew, p, pFanins[k+1] );
        if ( Type == CBA_NODE_AND )
            iRes = Gia_ManHashAnd( pNew, pLits[0], pLits[1] );
        else if ( Type == CBA_NODE_OR )
            iRes = Gia_ManHashAnd( pNew, pLits[0], pLits[1] );
        else if ( Type == CBA_NODE_XOR )
            iRes = Gia_ManHashXor( pNew, pLits[0], pLits[1] );
        else if ( Type == CBA_NODE_XNOR )
            iRes = Abc_LitNot( Gia_ManHashXor( pNew, pLits[0], pLits[1] ) );
        else assert( 0 ), iRes = -1;
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
    Cba_NtkForEachPo( pRoot, iObj, i )
        Cba_ManExtract_rec( pNew, pRoot, iObj );
    Cba_NtkForEachPo( pRoot, iObj, i )
        Gia_ManAppendCo( pNew, Cba_NtkCopy(pRoot, iObj) );
    assert( Vec_IntSize(p->vBuf2LeafNtk) == pNew->nBufs );

    // cleanup
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
//    Gia_ManPrintStats( pNew, NULL );
//    pNew = Gia_ManSweepHierarchy( pTemp = pNew );
//    Gia_ManStop( pTemp );
//    Gia_ManPrintStats( pNew, NULL );
    return pNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
// return the array of object counters for each network
void Cba_ManCountNodes_rec( Cba_Man_t * p, Abc_Obj_t * pObj, int iNtk, Vec_Int_t * vObjCounts, Vec_Int_t * vBufDrivers, Vec_Int_t * vObj2Ntk, Vec_Int_t * vObj2Obj ) 
{
    if ( Abc_ObjIsBarBuf(pObj) )
    {
        Abc_Obj_t * pFanin = Abc_ObjFanin0(pObj);
        if ( Abc_ObjIsPi(pFanin) || (Abc_ObjIsNode(pFanin) && Abc_ObjFaninNum(pFanin) > 0) )
            Vec_IntAddToEntry( vBufDrivers, iNtk, 1 );
        Cba_ManCountNodes_rec( p, Abc_ObjFanin0(pObj), pObj->iTemp, vObjCounts, vBufDrivers, vObj2Ntk, vObj2Obj );
    }
    else if ( Abc_ObjFaninNum(pObj) > 0 )
    {
        Abc_Obj_t * pFanin; int i;
        Abc_ObjForEachFanin( pObj, pFanin, i )
            Cba_ManCountNodes_rec( p, pFanin, iNtk, vObjCounts, vBufDrivers, vObj2Ntk, vObj2Obj );
        Vec_IntWriteEntry( vObj2Ntk, Abc_ObjId(pObj), iNtk );
        Vec_IntWriteEntry( vObj2Obj, Abc_ObjId(pObj), Vec_IntEntry(vObjCounts, iNtk) );
        Vec_IntAddToEntry( vObjCounts, iNtk, 1 );
    }
}
Vec_Int_t * Cba_ManCountNodes( Cba_Man_t * p, Abc_Ntk_t * pAbcNtk, Vec_Int_t * vBuf2RootNtk, Vec_Int_t ** pvObj2Ntk, Vec_Int_t ** pvObj2Obj )
{
    Cba_Ntk_t * pNtk; 
    Abc_Obj_t * pObj;
    Vec_Int_t * vObjCounts = Vec_IntStart( Cba_ManNtkNum(p) + 1 );
    Vec_Int_t * vBufDrivers = Vec_IntStart( Cba_ManNtkNum(p) + 1 );
    // set networks to which barbufs belong
    int i, k, iBox, iBarBuf = Vec_IntSize( vBuf2RootNtk );
    assert( Vec_IntSize(vBuf2RootNtk) == pAbcNtk->nBarBufs2 );
    Abc_NtkForEachNodeReverse( pAbcNtk, pObj, i )
        pObj->iTemp = Vec_IntEntry( vBuf2RootNtk, --iBarBuf );
    assert( iBarBuf == 0 );
    // start with primary inputs
    Cba_ManForEachNtk( p, pNtk, i )
    {
        Vec_IntAddToEntry( vObjCounts, i, Cba_NtkPiNum(pNtk) );
        Cba_NtkForEachBox( pNtk, iBox, k )
            Vec_IntAddToEntry( vObjCounts, i, Cba_NtkPiNum(Cba_ObjBoxModel(pNtk, iBox)) + Cba_NtkPoNum(Cba_ObjBoxModel(pNtk, iBox)) + 1 );
    }
    // count internal nodes (network is in topo order)
    *pvObj2Ntk = Vec_IntStartFull( Abc_NtkObjNumMax(pAbcNtk) );
    *pvObj2Obj = Vec_IntStartFull( Abc_NtkObjNumMax(pAbcNtk) );
    Abc_NtkForEachPo( pAbcNtk, pObj, i )
        Cba_ManCountNodes_rec( p, Abc_ObjFanin0(pObj), p->iRoot, vObjCounts, vBufDrivers, *pvObj2Ntk, *pvObj2Obj );
    // count PIs, POs, and PO drivers
    Cba_ManForEachNtk( p, pNtk, i )
        Vec_IntAddToEntry( vObjCounts, i, 2 * Cba_NtkPoNum(pNtk) - Vec_IntEntry(vBufDrivers, i) );
    Vec_IntFree( vBufDrivers );
    return vObjCounts;
}
Cba_Man_t * Cba_ManInsert( Cba_Man_t * p, Abc_Ntk_t * pAbcNtk, int fVerbose )
{
    Cba_Man_t * pNew;
    Cba_Ntk_t * pNtk;
    Abc_Obj_t * pObj, * pFanin;
    Vec_Int_t * vObj2Ntk, * vObj2Obj;
    Vec_Int_t * vObjCounts = Cba_ManCountNodes( p, pAbcNtk, p->vBuf2RootNtk, &vObj2Ntk, &vObj2Obj );
    Vec_Int_t * vFanins;
    int i, k, iNtk, iBuf = 0;
    // create initial mapping
    pNew = Cba_ManDupStart( p, vObjCounts );
    // set PIs point to the leaves
    Abc_NtkForEachPi( pAbcNtk, pObj, i )
    {
        Vec_IntWriteEntry( vObj2Ntk, Abc_ObjId(pObj), p->iRoot );
        Vec_IntWriteEntry( vObj2Obj, Abc_ObjId(pObj), i );
    }
    // set buffers to point to the leaves
    assert( Vec_IntSize(p->vBuf2LeafNtk) == pAbcNtk->nBarBufs2 );
    assert( Vec_IntSize(p->vBuf2LeafObj) == pAbcNtk->nBarBufs2 );
    Abc_NtkForEachBarBuf( pAbcNtk, pObj, i )
    {
        Vec_IntWriteEntry( vObj2Ntk, Abc_ObjId(pObj), Vec_IntEntry(p->vBuf2LeafNtk, iBuf) );
        Vec_IntWriteEntry( vObj2Obj, Abc_ObjId(pObj), Vec_IntEntry(p->vBuf2LeafObj, iBuf) );
        iBuf++;
    }
    assert( iBuf == pAbcNtk->nBarBufs2 );
    // copy internal nodes
    vFanins = Vec_IntAlloc( 100 );
    Abc_NtkForEachNode( pAbcNtk, pObj, i )
    {
        if ( Abc_ObjIsBarBuf(pObj) )
            continue;
        if ( Abc_ObjFaninNum(pObj) == 0 )
            continue;
        Vec_IntClear( vFanins );
        iNtk = Vec_IntEntry(vObj2Ntk, Abc_ObjId(pObj));
        Abc_ObjForEachFanin( pObj, pFanin, k )
        {
            assert( Vec_IntEntry(vObj2Ntk, Abc_ObjId(pFanin)) == iNtk );
            Vec_IntPush( vFanins, Vec_IntEntry(vObj2Obj, Abc_ObjId(pFanin)) );
        }
        pNtk = Cba_ManNtk( pNew, iNtk );
        Vec_IntPush( &pNtk->vTypes,   CBA_OBJ_NODE );
        Vec_IntPush( &pNtk->vFuncs,   -1 );
        Vec_IntPush( &pNtk->vFanins,  Cba_ManHandleArray(pNew, vFanins) );
    }
    // set buffers to point to the roots
    assert( Vec_IntSize(p->vBuf2RootNtk) == pAbcNtk->nBarBufs2 );
    assert( Vec_IntSize(p->vBuf2RootObj) == pAbcNtk->nBarBufs2 );
    iBuf = 0;
    Abc_NtkForEachBarBuf( pAbcNtk, pObj, i )
    {
        Vec_IntWriteEntry( vObj2Ntk, Abc_ObjId(pObj), Vec_IntEntry(p->vBuf2RootNtk, iBuf) );
        Vec_IntWriteEntry( vObj2Obj, Abc_ObjId(pObj), Vec_IntEntry(p->vBuf2RootObj, iBuf) );
        iBuf++;
    }
    assert( iBuf == pAbcNtk->nBarBufs2 );
    // connect driven root nodes


    Vec_IntFree( vObj2Ntk );
    Vec_IntFree( vObj2Obj );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

