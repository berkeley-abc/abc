/**CFile****************************************************************

  FileName    [abcHieGia.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Procedures to handle hierarchy.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcHieGia.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "misc/util/utilNam.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Transfers the AIG from one manager into another.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeStrashToGia_rec( Gia_Man_t * pNew, Hop_Obj_t * pObj )
{
    assert( !Hop_IsComplement(pObj) );
    if ( !Hop_ObjIsNode(pObj) || Hop_ObjIsMarkA(pObj) )
        return;
    Abc_NodeStrashToGia_rec( pNew, Hop_ObjFanin0(pObj) ); 
    Abc_NodeStrashToGia_rec( pNew, Hop_ObjFanin1(pObj) );
    pObj->iData = Gia_ManHashAnd( pNew, Hop_ObjChild0CopyI(pObj), Hop_ObjChild1CopyI(pObj) );
    assert( !Hop_ObjIsMarkA(pObj) ); // loop detection
    Hop_ObjSetMarkA( pObj );
}
int Abc_NodeStrashToGia( Gia_Man_t * pNew, Abc_Obj_t * pNode )
{
    Hop_Man_t * pMan = (Hop_Man_t *)pNode->pNtk->pManFunc;
    Hop_Obj_t * pRoot = (Hop_Obj_t *)pNode->pData;
    Abc_Obj_t * pFanin;  int i;
    assert( Abc_ObjIsNode(pNode) );
    assert( Abc_NtkHasAig(pNode->pNtk) && !Abc_NtkIsStrash(pNode->pNtk) );
    // check the constant case
    if ( Abc_NodeIsConst(pNode) || Hop_Regular(pRoot) == Hop_ManConst1(pMan) )
        return Abc_LitNotCond( 1, Hop_IsComplement(pRoot) );
    // set elementary variables
    Abc_ObjForEachFanin( pNode, pFanin, i )
        assert( pFanin->iTemp != -1 );
    Abc_ObjForEachFanin( pNode, pFanin, i )
        Hop_IthVar(pMan, i)->iData = pFanin->iTemp;
    // strash the AIG of this node
    Abc_NodeStrashToGia_rec( pNew, Hop_Regular(pRoot) );
    Hop_ConeUnmark_rec( Hop_Regular(pRoot) );
    return Abc_LitNotCond( Hop_Regular(pRoot)->iData, Hop_IsComplement(pRoot) );
}


/**Function*************************************************************

  Synopsis    [Flattens the logic hierarchy of the netlist.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManFlattenLogicHierarchy2_rec( Gia_Man_t * pNew, Abc_Ntk_t * pNtk, int * pCounter, Vec_Int_t * vBufs )
{
    Vec_Ptr_t * vDfs = (Vec_Ptr_t *)pNtk->pData;
    Abc_Obj_t * pObj, * pTerm; 
    int i, k; (*pCounter)++;
    //printf( "[%d:%d] ", Abc_NtkPiNum(pNtk), Abc_NtkPoNum(pNtk) );
    Vec_PtrForEachEntry( Abc_Obj_t *, vDfs, pObj, i )
    {
        if ( Abc_ObjIsNode(pObj) )
            Abc_ObjFanout0(pObj)->iTemp = Abc_NodeStrashToGia( pNew, pObj );
        else
        {
            int iBufStart = Gia_ManBufNum(pNew);
            Abc_Ntk_t * pModel = (Abc_Ntk_t *)pObj->pData;
            assert( !Abc_ObjIsLatch(pObj) );
            assert( Abc_NtkPiNum(pModel) == Abc_ObjFaninNum(pObj) );
            assert( Abc_NtkPoNum(pModel) == Abc_ObjFanoutNum(pObj) );
            Abc_NtkFillTemp( pModel );
            Abc_ObjForEachFanin( pObj, pTerm, k )
            {
                assert( Abc_ObjIsNet(Abc_ObjFanin0(pTerm)) );
                Abc_ObjFanout0(Abc_NtkPi(pModel, k))->iTemp = Abc_ObjFanin0(pTerm)->iTemp;
            }
            if ( vBufs )
                Abc_ObjForEachFanin( pObj, pTerm, k )
                    Abc_ObjFanout0(Abc_NtkPi(pModel, k))->iTemp = Gia_ManAppendBuf( pNew, Abc_ObjFanout0(Abc_NtkPi(pModel, k))->iTemp );
            Gia_ManFlattenLogicHierarchy2_rec( pNew, pModel, pCounter, vBufs );
            if ( vBufs )
                Abc_ObjForEachFanout( pObj, pTerm, k )
                    Abc_ObjFanin0(Abc_NtkPo(pModel, k))->iTemp = Gia_ManAppendBuf( pNew, Abc_ObjFanin0(Abc_NtkPo(pModel, k))->iTemp );
            Abc_ObjForEachFanout( pObj, pTerm, k )
            {
                assert( Abc_ObjIsNet(Abc_ObjFanout0(pTerm)) );
                Abc_ObjFanout0(pTerm)->iTemp = Abc_ObjFanin0(Abc_NtkPo(pModel, k))->iTemp;
            }
            // save buffers
            if ( vBufs == NULL )
                continue;
            Vec_IntPush( vBufs, iBufStart );
            Vec_IntPush( vBufs, Abc_NtkPiNum(pModel) );
            Vec_IntPush( vBufs, Gia_ManBufNum(pNew) - Abc_NtkPoNum(pModel) );
            Vec_IntPush( vBufs, Abc_NtkPoNum(pModel) );
        }
    }
}
Gia_Man_t * Gia_ManFlattenLogicHierarchy2( Abc_Ntk_t * pNtk )
{
    int fUseBufs = 1;
    int fUseInter = 0;
    Gia_Man_t * pNew, * pTemp; 
    Abc_Ntk_t * pModel;
    Abc_Obj_t * pTerm;
    int i, Counter = -1;
    assert( Abc_NtkIsNetlist(pNtk) );
//    Abc_NtkPrintBoxInfo( pNtk );
    Abc_NtkFillTemp( pNtk );

    // start the manager
    pNew = Gia_ManStart( Abc_NtkObjNumMax(pNtk) );
    pNew->pName = Abc_UtilStrsav(pNtk->pName);
    pNew->pSpec = Abc_UtilStrsav(pNtk->pSpec);
    if ( fUseBufs )
        pNew->vBarBufs = Vec_IntAlloc( 1000 );

    // create PIs and buffers
    Abc_NtkForEachPi( pNtk, pTerm, i )
        pTerm->iTemp = Gia_ManAppendCi( pNew );
    Abc_NtkForEachPi( pNtk, pTerm, i )
        Abc_ObjFanout0(pTerm)->iTemp = fUseInter ? Gia_ManAppendBuf(pNew, pTerm->iTemp) : pTerm->iTemp;

    // create DFS order of nets
    if ( !pNtk->pDesign )
        pNtk->pData = Abc_NtkDfsWithBoxes( pNtk );
    else
        Vec_PtrForEachEntry( Abc_Ntk_t *, pNtk->pDesign->vModules, pModel, i )
            pModel->pData = Abc_NtkDfsWithBoxes( pModel );

    // call recursively
    Gia_ManHashAlloc( pNew );
    Gia_ManFlattenLogicHierarchy2_rec( pNew, pNtk, &Counter, pNew->vBarBufs );
    Gia_ManHashStop( pNew );
    printf( "Hierarchy reader flattened %d instances of logic boxes.\n", Counter );

    // delete DFS order of nets
    if ( !pNtk->pDesign )
        Vec_PtrFreeP( (Vec_Ptr_t **)&pNtk->pData );
    else
        Vec_PtrForEachEntry( Abc_Ntk_t *, pNtk->pDesign->vModules, pModel, i )
            Vec_PtrFreeP( (Vec_Ptr_t **)&pModel->pData );

    // create buffers and POs
    Abc_NtkForEachPo( pNtk, pTerm, i )
        pTerm->iTemp = fUseInter ? Gia_ManAppendBuf(pNew, Abc_ObjFanin0(pTerm)->iTemp) : Abc_ObjFanin0(pTerm)->iTemp;
    Abc_NtkForEachPo( pNtk, pTerm, i )
        Gia_ManAppendCo( pNew, pTerm->iTemp );

    // save buffers
    if ( fUseInter )
    {
        Vec_IntPush( pNew->vBarBufs, 0 );
        Vec_IntPush( pNew->vBarBufs, Abc_NtkPiNum(pNtk) );
        Vec_IntPush( pNew->vBarBufs, Gia_ManBufNum(pNew) - Abc_NtkPoNum(pNtk) );
        Vec_IntPush( pNew->vBarBufs, Abc_NtkPoNum(pNtk) );
    }
    if ( fUseBufs )
        Vec_IntPrint( pNew->vBarBufs );

    // cleanup
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}


/**Function*************************************************************

  Synopsis    [Flattens the logic hierarchy of the netlist.]

  Description [This procedure requires that models are uniqified.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManFlattenLogicPrepare( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pTerm, * pBox; 
    int i, k;
    Abc_NtkFillTemp( pNtk );
    Abc_NtkForEachPi( pNtk, pTerm, i )
        pTerm->iData = i;
    Abc_NtkForEachPo( pNtk, pTerm, i )
        pTerm->iData = i;
    Abc_NtkForEachBox( pNtk, pBox, i )
    {
        assert( !Abc_ObjIsLatch(pBox) );
        Abc_ObjForEachFanin( pBox, pTerm, k )
            pTerm->iData = k;
        Abc_ObjForEachFanout( pBox, pTerm, k )
            pTerm->iData = k;
    }
}
int Gia_ManFlattenLogicHierarchy_rec( Gia_Man_t * pNew, Vec_Ptr_t * vSupers, Abc_Obj_t * pObj, Vec_Int_t * vBufs )
{
    Abc_Ntk_t * pModel;
    Abc_Obj_t * pBox, * pFanin;  
    int iLit, i;
    if ( pObj->iTemp != -1 )
        return pObj->iTemp;
    if ( Abc_ObjIsNet(pObj) || Abc_ObjIsPo(pObj) || Abc_ObjIsBi(pObj) )
        return (pObj->iTemp = Gia_ManFlattenLogicHierarchy_rec(pNew, vSupers, Abc_ObjFanin0(pObj), vBufs));
    if ( Abc_ObjIsPi(pObj) )
    {
        pBox   = (Abc_Obj_t *)Vec_PtrPop( vSupers );
        pModel = (Abc_Ntk_t *)pBox->pData;
        //printf( "   Exiting %s\n", Abc_NtkName(pModel) );
        assert( Abc_ObjFaninNum(pBox) == Abc_NtkPiNum(pModel) );
        assert( pObj->iData >= 0 && pObj->iData < Abc_NtkPiNum(pModel) );
        pFanin = Abc_ObjFanin( pBox, pObj->iData );
        iLit   = Gia_ManFlattenLogicHierarchy_rec( pNew, vSupers, pFanin, vBufs );
        Vec_PtrPush( vSupers, pBox );
        return (pObj->iTemp = (vBufs ? Gia_ManAppendBuf(pNew, iLit) : iLit));
    }
    if ( Abc_ObjIsBo(pObj) )
    {
        pBox   = Abc_ObjFanin0(pObj);
        assert( Abc_ObjIsBox(pBox) );
        Vec_PtrPush( vSupers, pBox );
        pModel = (Abc_Ntk_t *)pBox->pData;
        //printf( "Entering %s\n", Abc_NtkName(pModel) );
        assert( Abc_ObjFanoutNum(pBox) == Abc_NtkPoNum(pModel) );
        assert( pObj->iData >= 0 && pObj->iData < Abc_NtkPoNum(pModel) );
        pFanin = Abc_NtkPo( pModel, pObj->iData );
        iLit   = Gia_ManFlattenLogicHierarchy_rec( pNew, vSupers, pFanin, vBufs );
        Vec_PtrPop( vSupers );
        return (pObj->iTemp = (vBufs ? Gia_ManAppendBuf(pNew, iLit) : iLit));
    }
    assert( Abc_ObjIsNode(pObj) );
    Abc_ObjForEachFanin( pObj, pFanin, i )
        Gia_ManFlattenLogicHierarchy_rec( pNew, vSupers, pFanin, vBufs );
    return (pObj->iTemp = Abc_NodeStrashToGia( pNew, pObj ));
}
Gia_Man_t * Gia_ManFlattenLogicHierarchy( Abc_Ntk_t * pNtk )
{
    int fUseBufs = 1;
    Gia_Man_t * pNew, * pTemp; 
    Abc_Ntk_t * pModel;
    Abc_Obj_t * pTerm;
    Vec_Ptr_t * vSupers;
    int i;//, Counter = -1;
    assert( Abc_NtkIsNetlist(pNtk) );
//    Abc_NtkPrintBoxInfo( pNtk );

    // create DFS order of nets
    if ( !pNtk->pDesign )
        Gia_ManFlattenLogicPrepare( pNtk );
    else
        Vec_PtrForEachEntry( Abc_Ntk_t *, pNtk->pDesign->vModules, pModel, i )
            Gia_ManFlattenLogicPrepare( pModel );

    // start the manager
    pNew = Gia_ManStart( Abc_NtkObjNumMax(pNtk) );
    pNew->pName = Abc_UtilStrsav(pNtk->pName);
    pNew->pSpec = Abc_UtilStrsav(pNtk->pSpec);
    if ( fUseBufs )
        pNew->vBarBufs = Vec_IntAlloc( 1000 );

    // create PIs and buffers
    Abc_NtkForEachPi( pNtk, pTerm, i )
        pTerm->iTemp = Gia_ManAppendCi( pNew );

    // call recursively
    vSupers = Vec_PtrAlloc( 100 );
    Gia_ManHashAlloc( pNew );
    Abc_NtkForEachPo( pNtk, pTerm, i )
        Gia_ManFlattenLogicHierarchy_rec( pNew, vSupers, pTerm, pNew->vBarBufs );
    Gia_ManHashStop( pNew );
    Vec_PtrFree( vSupers );
    printf( "Hierarchy reader flattened %d instances of boxes.\n", pNtk->pDesign ? Vec_PtrSize(pNtk->pDesign->vModules)-1 : 0 );

    // create buffers and POs
    Abc_NtkForEachPo( pNtk, pTerm, i )
        Gia_ManAppendCo( pNew, pTerm->iTemp );
    // save buffers
//    Vec_IntPrint( pNew->vBarBufs );

    // cleanup
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}




/*
design = array containing design name (as the first entry in the array) followed by pointers to modules
module = array containing module name (as the first entry in the array) followed by pointers to four arrays: 
         {array of input names; array of output names; array of nodes; array of boxes}
node   = array containing output name, followed by node type, followed by input names
box    = array containing model name, instance name, followed by pairs of formal/actual names for each port
*/


/**Function*************************************************************

  Synopsis    [Node type conversions.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

typedef enum { 
    PTR_OBJ_NONE,    // 0: non-existent object
    PTR_OBJ_CONST0,  // 1: constant node
    PTR_OBJ_PI,      // 2: primary input
    PTR_OBJ_PO,      // 3: primary output
    PTR_OBJ_FAN,     // 4: box output
    PTR_OBJ_FLOP,    // 5: flip-flop
    PTR_OBJ_BOX,     // 6: box
    PTR_OBJ_NODE,    // 7: logic node

    PTR_OBJ_C0,      // 8: logic node
    PTR_OBJ_C1,      // 9: logic node
    PTR_OBJ_BUF,     // 0: logic node
    PTR_OBJ_INV,     // 1: logic node
    PTR_OBJ_AND,     // 2: logic node
    PTR_OBJ_OR,      // 3: logic node
    PTR_OBJ_XOR,     // 4: logic node
    PTR_OBJ_NAND,    // 5: logic node
    PTR_OBJ_NOR,     // 6: logic node
    PTR_OBJ_XNOR,    // 7: logic node
    PTR_OBJ_MUX,     // 8: logic node
    PTR_OBJ_MAJ,     // 9: logic node

    PTR_VOID         // 0: placeholder
} Ptr_ObjType_t;

char * Ptr_TypeToName( Ptr_ObjType_t Type )
{
    if ( Type == PTR_OBJ_BUF )   return "buf";
    if ( Type == PTR_OBJ_INV )   return "not";
    if ( Type == PTR_OBJ_AND )   return "and";
    if ( Type == PTR_OBJ_OR )    return "or";
    if ( Type == PTR_OBJ_XOR )   return "xor";
    if ( Type == PTR_OBJ_XNOR )  return "xnor";
    assert( 0 );
    return "???";
}
Ptr_ObjType_t Ptr_SopToType( char * pSop )
{
    if ( !strcmp(pSop, "1 1\n") )        return PTR_OBJ_BUF;
    if ( !strcmp(pSop, "0 1\n") )        return PTR_OBJ_INV;
    if ( !strcmp(pSop, "11 1\n") )       return PTR_OBJ_AND;
    if ( !strcmp(pSop, "00 0\n") )       return PTR_OBJ_OR;
    if ( !strcmp(pSop, "-1 1\n1- 1\n") ) return PTR_OBJ_OR;
    if ( !strcmp(pSop, "1- 1\n-1 1\n") ) return PTR_OBJ_OR;
    if ( !strcmp(pSop, "01 1\n10 1\n") ) return PTR_OBJ_XOR;
    if ( !strcmp(pSop, "10 1\n01 1\n") ) return PTR_OBJ_XOR;
    if ( !strcmp(pSop, "11 1\n00 1\n") ) return PTR_OBJ_XNOR;
    if ( !strcmp(pSop, "00 1\n11 1\n") ) return PTR_OBJ_XNOR;
    assert( 0 );
    return PTR_OBJ_NONE;
}
Ptr_ObjType_t Ptr_HopToType( Abc_Obj_t * pObj )
{
    static word uTruth, uTruths6[3] = {
        ABC_CONST(0xAAAAAAAAAAAAAAAA),
        ABC_CONST(0xCCCCCCCCCCCCCCCC),
        ABC_CONST(0xF0F0F0F0F0F0F0F0),
    };
    assert( Abc_ObjIsNode(pObj) );
    uTruth = Hop_ManComputeTruth6( (Hop_Man_t *)Abc_ObjNtk(pObj)->pManFunc, (Hop_Obj_t *)pObj->pData, Abc_ObjFaninNum(pObj) );
    if ( uTruth ==  uTruths6[0] )                 return PTR_OBJ_BUF;
    if ( uTruth == ~uTruths6[0] )                 return PTR_OBJ_INV;
    if ( uTruth == (uTruths6[0] & uTruths6[1]) )  return PTR_OBJ_AND;
    if ( uTruth == (uTruths6[0] | uTruths6[1]) )  return PTR_OBJ_OR;
    if ( uTruth == (uTruths6[0] ^ uTruths6[1]) )  return PTR_OBJ_XOR;
    if ( uTruth == (uTruths6[0] ^~uTruths6[1]) )  return PTR_OBJ_XNOR;
    assert( 0 );
    return PTR_OBJ_NONE;
}

/**Function*************************************************************

  Synopsis    [Dumping hierarchical Abc_Ntk_t in Ptr form.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline char * Ptr_ObjName( Abc_Obj_t * pObj )
{
    if ( Abc_ObjIsNet(pObj) || Abc_ObjIsBox(pObj) )
        return Abc_ObjName(pObj);
    if ( Abc_ObjIsCi(pObj) || Abc_ObjIsNode(pObj) )
        return Ptr_ObjName(Abc_ObjFanout0(pObj));
    if ( Abc_ObjIsCo(pObj) )
        return Ptr_ObjName(Abc_ObjFanin0(pObj));
    assert( 0 );
    return NULL;
}
int Ptr_ManCheckArray( Vec_Ptr_t * vArray )
{
    if ( Vec_PtrSize(vArray) == 0 )
        return 1;
    if ( Abc_MaxInt(8, Vec_PtrSize(vArray)) == Vec_PtrCap(vArray) )
        return 1;
    assert( 0 );
    return 0;
}
Vec_Ptr_t * Ptr_ManDumpNode( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanin; int i;
    Vec_Ptr_t * vNode = Vec_PtrAlloc( 2 + Abc_ObjFaninNum(pObj) );
    assert( Abc_ObjIsNode(pObj) );
    Vec_PtrPush( vNode, Ptr_ObjName(pObj) );
    Vec_PtrPush( vNode, Abc_Int2Ptr(Ptr_HopToType(pObj)) );
    Abc_ObjForEachFanin( pObj, pFanin, i )
        Vec_PtrPush( vNode, Ptr_ObjName(pFanin) );
    assert( Ptr_ManCheckArray(vNode) );
    return vNode;
}
Vec_Ptr_t * Ptr_ManDumpNodes( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj; int i;
    Vec_Ptr_t * vNodes = Vec_PtrAlloc( Abc_NtkNodeNum(pNtk) );
    Abc_NtkForEachNode( pNtk, pObj, i )
        Vec_PtrPush( vNodes, Ptr_ManDumpNode(pObj) );
    assert( Ptr_ManCheckArray(vNodes) );
    return vNodes;
}

Vec_Ptr_t * Ptr_ManDumpBox( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pNext; int i;
    Abc_Ntk_t * pModel = Abc_ObjModel(pObj);
    Vec_Ptr_t * vBox = Vec_PtrAlloc( 2 + 2 * Abc_ObjFaninNum(pObj) + 2 * Abc_ObjFanoutNum(pObj) );
    assert( Abc_ObjIsBox(pObj) );
    Vec_PtrPush( vBox, Abc_NtkName(pModel) );
    Vec_PtrPush( vBox, Ptr_ObjName(pObj) );
    Abc_ObjForEachFanin( pObj, pNext, i )
    {
        Vec_PtrPush( vBox, Ptr_ObjName(Abc_NtkPi(pModel, i)) );
        Vec_PtrPush( vBox, Ptr_ObjName(pNext) );
    }
    Abc_ObjForEachFanout( pObj, pNext, i )
    {
        Vec_PtrPush( vBox, Ptr_ObjName(Abc_NtkPo(pModel, i)) );
        Vec_PtrPush( vBox, Ptr_ObjName(pNext) );
    }
    assert( Ptr_ManCheckArray(vBox) );
    return vBox;
}
Vec_Ptr_t * Ptr_ManDumpBoxes( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj; int i;
    Vec_Ptr_t * vBoxes = Vec_PtrAlloc( Abc_NtkBoxNum(pNtk) );
    Abc_NtkForEachBox( pNtk, pObj, i )
        Vec_PtrPush( vBoxes, Ptr_ManDumpBox(pObj) );
    assert( Ptr_ManCheckArray(vBoxes) );
    return vBoxes;
}

Vec_Ptr_t * Ptr_ManDumpInputs( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj; int i;
    Vec_Ptr_t * vSigs = Vec_PtrAlloc( Abc_NtkPiNum(pNtk) );
    Abc_NtkForEachPi( pNtk, pObj, i )
        Vec_PtrPush( vSigs, Ptr_ObjName(pObj) );
    assert( Ptr_ManCheckArray(vSigs) );
    return vSigs;
}
Vec_Ptr_t * Ptr_ManDumpOutputs( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj; int i;
    Vec_Ptr_t * vSigs = Vec_PtrAlloc( Abc_NtkPoNum(pNtk) );
    Abc_NtkForEachPo( pNtk, pObj, i )
        Vec_PtrPush( vSigs, Ptr_ObjName(pObj) );
    assert( Ptr_ManCheckArray(vSigs) );
    return vSigs;
}
Vec_Ptr_t * Ptr_ManDumpNtk( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vNtk = Vec_PtrAlloc( 5 );
    Vec_PtrPush( vNtk, Abc_NtkName(pNtk) );
    Vec_PtrPush( vNtk, Ptr_ManDumpInputs(pNtk) );
    Vec_PtrPush( vNtk, Ptr_ManDumpOutputs(pNtk) );
    Vec_PtrPush( vNtk, Ptr_ManDumpNodes(pNtk) );
    Vec_PtrPush( vNtk, Ptr_ManDumpBoxes(pNtk) );
    assert( Ptr_ManCheckArray(vNtk) );
    return vNtk;
}
Vec_Ptr_t * Ptr_ManDumpDes( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vDes;
    Abc_Ntk_t * pTemp; int i;
    vDes = Vec_PtrAlloc( 1 + Vec_PtrSize(pNtk->pDesign->vModules) );
    Vec_PtrPush( vDes, pNtk->pDesign->pName );
    Vec_PtrForEachEntry( Abc_Ntk_t *, pNtk->pDesign->vModules, pTemp, i )
        Vec_PtrPush( vDes, Ptr_ManDumpNtk(pTemp) );
    assert( Ptr_ManCheckArray(vDes) );
    return vDes;
}

/**Function*************************************************************

  Synopsis    [Dumping Ptr into a Verilog file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ptr_ManDumpNodeToFile( FILE * pFile, Vec_Ptr_t * vNode )
{
    char * pName;  int i;
    fprintf( pFile, "%s", Ptr_TypeToName( (Ptr_ObjType_t)Abc_Ptr2Int(Vec_PtrEntry(vNode, 1)) ) );
    fprintf( pFile, "( %s", (char *)Vec_PtrEntry(vNode, 0) );
    Vec_PtrForEachEntryStart( char *, vNode, pName, i, 2 )
        fprintf( pFile, ", %s", pName );
    fprintf( pFile, " );\n" );
}
void Ptr_ManDumpNodesToFile( FILE * pFile, Vec_Ptr_t * vNodes )
{
    Vec_Ptr_t * vNode; int i;
    Vec_PtrForEachEntry( Vec_Ptr_t *, vNodes, vNode, i )
        Ptr_ManDumpNodeToFile( pFile, vNode );
}

void Ptr_ManDumpBoxToFile( FILE * pFile, Vec_Ptr_t * vBox )
{
    char * pName; int i;
    fprintf( pFile, "%s %s (", (char *)Vec_PtrEntry(vBox, 0), (char *)Vec_PtrEntry(vBox, 1) );
    Vec_PtrForEachEntryStart( char *, vBox, pName, i, 2 )
        fprintf( pFile, " .%s(%s)%s", pName, (char *)Vec_PtrEntry(vBox, ++i), i >= Vec_PtrSize(vBox)-2 ? "" : "," );
    fprintf( pFile, " );\n" );
}
void Ptr_ManDumpBoxesToFile( FILE * pFile, Vec_Ptr_t * vBoxes )
{
    Vec_Ptr_t * vBox; int i;
    Vec_PtrForEachEntry( Vec_Ptr_t *, vBoxes, vBox, i )
        Ptr_ManDumpBoxToFile( pFile, vBox );
}

void Ptr_ManDumpSignalsToFile( FILE * pFile, Vec_Ptr_t * vSigs, int fSkipLastComma )
{
    char * pSig; int i;
    Vec_PtrForEachEntry( char *, vSigs, pSig, i )
        fprintf( pFile, " %s%s", pSig, (fSkipLastComma && i == Vec_PtrSize(vSigs)-1) ? "" : "," );
}
void Ptr_ManDumpModuleToFile( FILE * pFile, Vec_Ptr_t * vNtk )
{
    fprintf( pFile, "module %s\n", (char *)Vec_PtrEntry(vNtk, 0) );
    fprintf( pFile, "(\n" );
    Ptr_ManDumpSignalsToFile( pFile, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 1), 0 );
    fprintf( pFile, "\n" );
    Ptr_ManDumpSignalsToFile( pFile, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 2), 1 );
    fprintf( pFile, "\n);\ninput" );
    Ptr_ManDumpSignalsToFile( pFile, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 1), 1 );
    fprintf( pFile, ";\noutput" );
    Ptr_ManDumpSignalsToFile( pFile, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 2), 1 );
    fprintf( pFile, ";\n\n" );
    Ptr_ManDumpNodesToFile( pFile, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 3) );
    fprintf( pFile, "\n" );
    Ptr_ManDumpBoxesToFile( pFile, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 4) );
    fprintf( pFile, "endmodule\n\n" );
}
void Ptr_ManDumpToFile( char * pFileName, Vec_Ptr_t * vDes )
{
    FILE * pFile;
    Vec_Ptr_t * vNtk; int i;
    pFile = fopen( pFileName, "wb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open output file \"%s\".\n", pFileName );
        return;
    }
    fprintf( pFile, "// Design \"%s\" written by ABC on %s\n\n", (char *)Vec_PtrEntry(vDes, 0), Extra_TimeStamp() );
    Vec_PtrForEachEntryStart( Vec_Ptr_t *, vDes, vNtk, i, 1 )
        Ptr_ManDumpModuleToFile( pFile, vNtk );
    fclose( pFile );
}

/**Function*************************************************************

  Synopsis    [Count memory used by Ptr.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ptr_ManMemArray( Vec_Ptr_t * vArray )
{
    return (int)Vec_PtrMemory(vArray);
}
int Ptr_ManMemArrayArray( Vec_Ptr_t * vArrayArray )
{
    Vec_Ptr_t * vArray; int i, nBytes = 0;
    Vec_PtrForEachEntry( Vec_Ptr_t *, vArrayArray, vArray, i )
        nBytes += Ptr_ManMemArray(vArray);
    return nBytes;
}
int Ptr_ManMemNtk( Vec_Ptr_t * vNtk )
{
    int nBytes = (int)Vec_PtrMemory(vNtk);
    nBytes += Ptr_ManMemArray( (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 1) );
    nBytes += Ptr_ManMemArray( (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 2) );
    nBytes += Ptr_ManMemArrayArray( (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 3) );
    nBytes += Ptr_ManMemArrayArray( (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 4) );
    return nBytes;
}
int Ptr_ManMemDes( Vec_Ptr_t * vDes )
{
    Vec_Ptr_t * vNtk; int i, nBytes = (int)Vec_PtrMemory(vDes);
    Vec_PtrForEachEntryStart( Vec_Ptr_t *, vDes, vNtk, i, 1 )
        nBytes += Ptr_ManMemNtk(vNtk);
    return nBytes;
}

/**Function*************************************************************

  Synopsis    [Free Ptr.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ptr_ManFreeNtk( Vec_Ptr_t * vNtk )
{
    Vec_PtrFree( (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 1) );
    Vec_PtrFree( (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 2) );
    Vec_VecFree( (Vec_Vec_t *)Vec_PtrEntry(vNtk, 3) );
    Vec_VecFree( (Vec_Vec_t *)Vec_PtrEntry(vNtk, 4) );
    Vec_PtrFree( vNtk );
}
void Ptr_ManFreeDes( Vec_Ptr_t * vDes )
{
    Vec_Ptr_t * vNtk; int i;
    Vec_PtrForEachEntryStart( Vec_Ptr_t *, vDes, vNtk, i, 1 )
        Ptr_ManFreeNtk( vNtk );
    Vec_PtrFree( vDes );
}

/**Function*************************************************************

  Synopsis    [Count memory use used by Ptr.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ptr_ManExperiment( Abc_Ntk_t * pNtk )
{
    abctime clk = Abc_Clock();
    Vec_Ptr_t * vDes = Ptr_ManDumpDes( pNtk );
    printf( "Converting to Ptr:  Memory = %6.3f MB  ", 1.0*Ptr_ManMemDes(vDes)/(1<<20) );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    Ptr_ManDumpToFile( Extra_FileNameGenericAppend(pNtk->pDesign->pName, "_out.v"), vDes );
    printf( "Finished writing output file \"%s\".\n", Extra_FileNameGenericAppend(pNtk->pDesign->pName, "_out.v") );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    Ptr_ManFreeDes( vDes );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
}


/**Function*************************************************************

  Synopsis    [Transform Ptr into Int.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Ptr_ManDumpArrayToInt( Abc_Nam_t * pNames, Vec_Ptr_t * vVec, int fNode )
{
    char * pName; int i;
    Vec_Int_t * vNew = Vec_IntAlloc( Vec_PtrSize(vVec) );
    Vec_PtrForEachEntry( char *, vVec, pName, i )
        Vec_IntPush( vNew, (fNode && i == 1) ? Abc_Ptr2Int(pName) : Abc_NamStrFind(pNames, pName) );
    return vNew;
}
Vec_Ptr_t * Ptr_ManDumpArrarArrayToInt( Abc_Nam_t * pNames, Vec_Ptr_t * vNodes, int fNode )
{
    Vec_Ptr_t * vNode; int i;
    Vec_Ptr_t * vNew = Vec_PtrAlloc( Vec_PtrSize(vNodes) );
    Vec_PtrForEachEntry( Vec_Ptr_t *, vNodes, vNode, i )
        Vec_PtrPush( vNew, Ptr_ManDumpArrayToInt(pNames, vNode, fNode) );
    assert( Ptr_ManCheckArray(vNew) );
    return vNew;
}
Vec_Ptr_t * Ptr_ManDumpNtkToInt( Abc_Nam_t * pNames, Vec_Ptr_t * vNtk, int i )
{
    Vec_Ptr_t * vNew   = Vec_PtrAlloc( 5 );
    assert( Abc_NamStrFind(pNames, (char *)Vec_PtrEntry(vNtk, 0)) == i );
    Vec_PtrPush( vNew, Abc_Int2Ptr(i) );
    Vec_PtrPush( vNew, Ptr_ManDumpArrayToInt(pNames, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 1), 0) );
    Vec_PtrPush( vNew, Ptr_ManDumpArrayToInt(pNames, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 2), 0) );
    Vec_PtrPush( vNew, Ptr_ManDumpArrarArrayToInt(pNames, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 3), 1) );
    Vec_PtrPush( vNew, Ptr_ManDumpArrarArrayToInt(pNames, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 4), 0) );
    assert( Ptr_ManCheckArray(vNew) );
    return vNew;
}
Vec_Ptr_t * Ptr_ManDumpToInt( Vec_Ptr_t * vDes )
{
    Vec_Ptr_t * vNew = Vec_PtrAlloc( Vec_PtrSize(vDes) );
    Vec_Ptr_t * vNtk; int i;
    // create module names
    Abc_Nam_t * pNames = Abc_NamStart( 1000, 20 );
    Vec_PtrForEachEntryStart( Vec_Ptr_t *, vDes, vNtk, i, 1 )
        Abc_NamStrFind( pNames, (char *)Vec_PtrEntry(vNtk, 0) );
    assert( i == Abc_NamObjNumMax(pNames) );
    // create resulting array
    Vec_PtrPush( vNew, pNames );
    Vec_PtrForEachEntryStart( Vec_Ptr_t *, vDes, vNtk, i, 1 )
        Vec_PtrPush( vNew, Ptr_ManDumpNtkToInt(pNames, vNtk, i) );
    assert( Ptr_ManCheckArray(vNew) );
    return vNew;
}


/**Function*************************************************************

  Synopsis    [Transform Ptr into Int.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
typedef struct Int_Des_t_ Int_Des_t;
struct Int_Des_t_
{
    char *           pName;   // design name
    Abc_Nam_t *      pNames;  // name manager
    Vec_Ptr_t        vModels; // models
};
typedef struct Int_Obj_t_ Int_Obj_t;
struct Int_Obj_t_
{
    int              iModel;
    int              iFunc;
    Vec_Wrd_t        vFanins;
};
typedef struct Int_Ntk_t_ Int_Ntk_t;
struct Int_Ntk_t_
{
    int              iName;
    int              nObjs;
    Int_Des_t *      pMan;
    Vec_Ptr_t        vInstances;
    Vec_Wrd_t        vOutputs;
    Vec_Int_t        vInputNames;
    Vec_Int_t        vOutputNames;
    Vec_Int_t *      vCopies;
    Vec_Int_t *      vCopies2;
};

static inline char *      Int_DesName( Int_Des_t * p )       { return p->pName;                                     }
static inline int         Int_DesNtkNum( Int_Des_t * p )     { return Vec_PtrSize( &p->vModels ) - 1;               }
static inline Int_Ntk_t * Int_DesNtk( Int_Des_t * p, int i ) { return (Int_Ntk_t *)Vec_PtrEntry( &p->vModels, i );  }

static inline char *      Int_NtkName( Int_Ntk_t * p )       { return Abc_NamStr( p->pMan->pNames, p->iName );      }
static inline int         Int_NtkPiNum( Int_Ntk_t * p )      { return Vec_IntSize( &p->vInputNames );               }
static inline int         Int_NtkPoNum( Int_Ntk_t * p )      { return Vec_IntSize( &p->vOutputNames );              }

static inline int         Int_ObjInputNum( Int_Ntk_t * p, Int_Obj_t * pObj )  { return pObj->iModel ? Int_NtkPiNum(Int_DesNtk(p->pMan, pObj->iModel)) : Vec_WrdSize(&pObj->vFanins); }
static inline int         Int_ObjOutputNum( Int_Ntk_t * p, Int_Obj_t * pObj ) { return pObj->iModel ? Int_NtkPoNum(Int_DesNtk(p->pMan, pObj->iModel)) : 1;                           }

Int_Obj_t * Int_ObjAlloc( int nFanins )
{
    Int_Obj_t * p = (Int_Obj_t *)ABC_CALLOC( char, sizeof(Int_Obj_t) + sizeof(word) * nFanins );
    p->vFanins.pArray = (word *)((char *)p + sizeof(Int_Obj_t));
    p->vFanins.nCap = nFanins;
    return p;
}
void Int_ObjFree( Int_Obj_t * p )
{
    ABC_FREE( p );
}
Int_Ntk_t * Int_NtkAlloc( Int_Des_t * pMan, int Id, int nPis, int nPos, int nInsts )
{
    Int_Ntk_t * p = ABC_CALLOC( Int_Ntk_t, 1 );
    p->iName = Id;
    p->nObjs = nPis + nInsts;
    p->pMan  = pMan;
    Vec_PtrGrow( &p->vInstances,   nInsts );
    Vec_WrdGrow( &p->vOutputs,     nPos );
    Vec_IntGrow( &p->vInputNames,  nPis );
    Vec_IntGrow( &p->vOutputNames, nPos );
    return p;
}
void Int_NtkFree( Int_Ntk_t * p )
{
    Int_Obj_t * pObj; int i;
    Vec_PtrForEachEntry( Int_Obj_t *, &p->vInstances, pObj, i )
        Int_ObjFree( pObj );
    ABC_FREE( p->vInstances.pArray );
    ABC_FREE( p->vOutputs.pArray );
    ABC_FREE( p->vInputNames.pArray );
    ABC_FREE( p->vOutputNames.pArray );
    Vec_IntFreeP( &p->vCopies );
    Vec_IntFreeP( &p->vCopies2 );
    ABC_FREE( p );
}
Int_Des_t * Int_DesAlloc( char * pName, Abc_Nam_t * pNames, int nModels )
{
    Int_Des_t * p = ABC_CALLOC( Int_Des_t, 1 );
    p->pName  = pName;
    p->pNames = pNames;
    Vec_PtrGrow( &p->vModels, nModels );
    return p;
}
void Int_DesFree( Int_Des_t * p )
{
    Int_Ntk_t * pTemp; int i;
    Vec_PtrForEachEntry( Int_Ntk_t *, &p->vModels, pTemp, i )
        Int_NtkFree( pTemp );
    ABC_FREE( p );
}

// replaces formal inputs by their indixes
void Ptr_ManFindInputOutputNumbers( Int_Ntk_t * pModel, Vec_Int_t * vBox, Vec_Int_t * vMap ) 
{
    int i, iFormal, iName, nPis = Int_NtkPiNum(pModel);
    Vec_IntForEachEntry( &pModel->vInputNames, iFormal, i )
        Vec_IntWriteEntry( vMap, iFormal, i );
    Vec_IntForEachEntry( &pModel->vOutputNames, iFormal, i )
        Vec_IntWriteEntry( vMap, iFormal, nPis+i );
    Vec_IntForEachEntryDouble( vBox, iFormal, iName, i )
    {
        if ( i == 0 ) continue;
        assert( Vec_IntEntry(vMap, iFormal) >= 0 );
        Vec_IntWriteEntry( vBox, i, Vec_IntEntry(vMap, iFormal) );
    }
    Vec_IntForEachEntry( &pModel->vInputNames, iFormal, i )
        Vec_IntWriteEntry( vMap, iFormal, -1 );
    Vec_IntForEachEntry( &pModel->vOutputNames, iFormal, i )
        Vec_IntWriteEntry( vMap, iFormal, -1 );
}
void Ptr_ManConvertNtk( Int_Ntk_t * pNtk, Vec_Ptr_t * vNtk, Vec_Wrd_t * vMap, Vec_Int_t * vMap2 )
{
    Vec_Int_t * vInputs  = (Vec_Int_t *)Vec_PtrEntry(vNtk, 1);
    Vec_Int_t * vOutputs = (Vec_Int_t *)Vec_PtrEntry(vNtk, 2);
    Vec_Ptr_t * vNodes   = (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 3);
    Vec_Ptr_t * vBoxes   = (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 4);
    Vec_Int_t * vNode, * vBox;
    Int_Ntk_t * pModel;
    Int_Obj_t * pObj;
    int i, k, iFormal, iName, nPis, nOffset, nNonDriven = 0;

    // map primary inputs
    Vec_IntForEachEntry( vInputs, iName, i )
    {
        assert( ~Vec_WrdEntry(vMap, iName) == 0 ); // driven twice
        Vec_WrdWriteEntry( vMap, iName, i );
    }
    // map internal nodes
    nOffset = Vec_IntSize(vInputs);
    Vec_PtrForEachEntry( Vec_Int_t *, vNodes, vNode, i )
    {
        iName = Vec_IntEntry(vNode, 0);
        assert( ~Vec_WrdEntry(vMap, iName) == 0 ); // driven twice
        Vec_WrdWriteEntry( vMap, iName, nOffset + i );
    }
    // map internal boxes
    nOffset += Vec_PtrSize(vNodes);
    Vec_PtrForEachEntry( Vec_Int_t *, vBoxes, vBox, i )
    {
        // get model name
        iName = Vec_IntEntry( vBox, 0 );
        assert( iName >= 1 && iName <= Int_DesNtkNum(pNtk->pMan) ); // bad model name
        pModel = Int_DesNtk( pNtk->pMan, iName );
        nPis = Int_NtkPiNum( pModel );
        // replace inputs/outputs by their IDs
        Ptr_ManFindInputOutputNumbers( pModel, vBox, vMap2 );
        // go through outputs of this box
        Vec_IntForEachEntryDouble( vBox, iFormal, iName, k )
            if ( k > 0 && i >= nPis )  // output
            {
                assert( ~Vec_WrdEntry(vMap, iName) == 0 ); // driven twice
                Vec_WrdWriteEntry( vMap, iName, (nOffset + i) | ((word)iFormal << 32) );
            }
    }

    // save input names
    Vec_IntForEachEntry( vInputs, iName, i )
        Vec_IntPush( &pNtk->vInputNames, iName );
    // create nodes with the given connectivity
    Vec_PtrForEachEntry( Vec_Int_t *, vNodes, vNode, i )
    {
        pObj = Int_ObjAlloc( Vec_IntSize(vNode) - 2 );
        pObj->iFunc = Vec_IntEntry(vNode, 1);
        Vec_IntForEachEntryStart( vNode, iName, k, 2 )
        {
            Vec_WrdPush( &pObj->vFanins, Vec_WrdEntry(vMap, iName) );
            nNonDriven += (~Vec_WrdEntry(vMap, iName) == 0);
        }
        Vec_PtrPush( &pNtk->vInstances, pObj );
    }
    // create boxes with the given connectivity
    Vec_PtrForEachEntry( Vec_Int_t *, vBoxes, vBox, i )
    {
        pModel = Int_DesNtk( pNtk->pMan, Vec_IntEntry(vBox, 0) );
        nPis = Int_NtkPiNum( pModel );
        pObj = Int_ObjAlloc( nPis );
        Vec_IntForEachEntryDouble( vBox, iFormal, iName, k )
            if ( k > 0 && iFormal < nPis ) // input
            {
                Vec_WrdPush( &pObj->vFanins, Vec_WrdEntry(vMap, iName) );
                nNonDriven += (~Vec_WrdEntry(vMap, iName) == 0);
            }
        Vec_PtrPush( &pNtk->vInstances, pObj );
    }
    // save output names
    Vec_IntForEachEntry( vOutputs, iName, i )
    {
        Vec_IntPush( &pNtk->vOutputNames, iName );
        Vec_WrdPush( &pNtk->vOutputs, Vec_WrdEntry(vMap, iName) );
        nNonDriven += (~Vec_WrdEntry(vMap, iName) == 0);
    }
    if ( nNonDriven )
        printf( "Model %s has %d non-driven nets.\n", Int_NtkName(pNtk), nNonDriven );
}
Int_Ntk_t * Ptr_ManConvertNtkInter( Int_Des_t * pDes, Vec_Ptr_t * vNtk, int Id )
{
    Vec_Int_t * vInputs  = (Vec_Int_t *)Vec_PtrEntry(vNtk, 1);
    Vec_Int_t * vOutputs = (Vec_Int_t *)Vec_PtrEntry(vNtk, 2);
    Vec_Ptr_t * vNodes   = (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 3);
    Vec_Ptr_t * vBoxes   = (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 4);
    return Int_NtkAlloc( pDes, Id, Vec_IntSize(vInputs), Vec_IntSize(vOutputs), Vec_PtrSize(vNodes) + Vec_PtrSize(vBoxes) );
}
Int_Des_t * Ptr_ManConvert( Vec_Ptr_t * vDesPtr )
{
    Vec_Ptr_t * vNtk; int i;
    char * pName = (char *)Vec_PtrEntry(vDesPtr, 0);
    Vec_Ptr_t * vDes = Ptr_ManDumpToInt( vDesPtr );
    Abc_Nam_t * pNames = (Abc_Nam_t *)Vec_PtrEntry(vDes, 0);
    Vec_Wrd_t * vMap = Vec_WrdStartFull( Abc_NamObjNumMax(pNames) + 1 );
    Vec_Int_t * vMap2 = Vec_IntStartFull( Abc_NamObjNumMax(pNames) + 1 );
    Int_Des_t * pDes = Int_DesAlloc( pName, pNames, Vec_PtrSize(vDes)-1 );
    Vec_PtrForEachEntryStart( Vec_Ptr_t *, vDes, vNtk, i, 1 )
        Vec_PtrPush( &pDes->vModels, Ptr_ManConvertNtkInter(pDes, vNtk, i) );
    Vec_PtrForEachEntryStart( Vec_Ptr_t *, vDes, vNtk, i, 1 )
        Ptr_ManConvertNtk( Int_DesNtk(pDes, i), vNtk, vMap, vMap2 );
    Ptr_ManFreeDes( vDes );
    Vec_IntFree( vMap2 );
    Vec_WrdFree( vMap );
    return pDes;
}


/**Function*************************************************************

  Synopsis    [Allocates ccpy structures for each literal in the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Int_NtkCopyAlloc( Int_Ntk_t * p )
{
    Vec_Int_t * vCopies;
    Int_Obj_t * pObj; int i, k, nOuts;
    int nInputs = Vec_IntSize(&p->vInputNames);
    int nEntries0 = nInputs + Vec_PtrSize(&p->vInstances);
    int nEntries = nEntries0;
    // count the number of entries
    Vec_PtrForEachEntry( Int_Obj_t *, &p->vInstances, pObj, i )
        nEntries += Int_ObjOutputNum(p, pObj) - 1;
    if ( nEntries == nEntries0 )
        return NULL;
    // allocate the entries
    vCopies = Vec_IntAlloc( nEntries );
    Vec_IntFill( vCopies, nEntries0, -1 );
    Vec_PtrForEachEntry( Int_Obj_t *, &p->vInstances, pObj, i )
    {
        nOuts = Int_ObjOutputNum( p, pObj );
        Vec_IntWriteEntry( vCopies, nInputs + i, Vec_IntSize(vCopies) );
        for ( k = 0; k < nOuts; k++ )
            Vec_IntPush( vCopies, -1 );
    }
    assert( Vec_IntSize(vCopies) == nEntries );
    return vCopies;
}
int Int_NtkCopyLookup( Int_Ntk_t * p, int iObj, int iOut )
{
    if ( iOut == 0 )
        return Vec_IntEntry( p->vCopies, iObj );
    return Vec_IntEntry( p->vCopies2, Vec_IntEntry(p->vCopies2, iObj) + iOut );
}
void Int_NtkCopyInsert( Int_Ntk_t * p, int iObj, int iOut, int Item )
{
    if ( iOut == 0 )
        Vec_IntWriteEntry( p->vCopies, iObj, Item );
    else
        Vec_IntWriteEntry( p->vCopies2, Vec_IntEntry(p->vCopies2, iObj) + iOut, Item );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

