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
#include <ctype.h>

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
void Abc_NtkFlattenHierarchyGia2_rec( Gia_Man_t * pNew, Abc_Ntk_t * pNtk, int * pCounter, Vec_Int_t * vBufs )
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
            Abc_NtkFlattenHierarchyGia2_rec( pNew, pModel, pCounter, vBufs );
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
Gia_Man_t * Abc_NtkFlattenHierarchyGia2( Abc_Ntk_t * pNtk )
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
    Abc_NtkFlattenHierarchyGia2_rec( pNew, pNtk, &Counter, pNew->vBarBufs );
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

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManPrintBarBufDrivers( Gia_Man_t * p )
{
    Vec_Int_t * vMap, * vFan, * vCrits;
    Gia_Obj_t * pObj;
    int i, iFanin, CountCrit[2] = {0}, CountFans[2] = {0};
    // map barbuf drivers into barbuf literals of the first barbuf driven by them
    vMap = Vec_IntStart( Gia_ManObjNum(p) );
    vFan = Vec_IntStart( Gia_ManObjNum(p) );
    vCrits = Vec_IntAlloc( 100 );
    Gia_ManForEachObj( p, pObj, i )
    {
        // count fanouts
        if ( Gia_ObjIsBuf(pObj) || Gia_ObjIsCo(pObj) )
            Vec_IntAddToEntry( vFan, Gia_ObjFaninId0(pObj, i), 1 );
        else if ( Gia_ObjIsAnd(pObj) )
        {
            Vec_IntAddToEntry( vFan, Gia_ObjFaninId0(pObj, i), 1 );
            Vec_IntAddToEntry( vFan, Gia_ObjFaninId1(pObj, i), 1 );
        }
        // count critical barbufs
        if ( Gia_ObjIsBuf(pObj) )
        {
            iFanin = Gia_ObjFaninId0( pObj, i );
            if ( iFanin == 0 || Vec_IntEntry(vMap, iFanin) != 0 )
            {
                CountCrit[(int)(iFanin != 0)]++;
                Vec_IntPush( vCrits, i );
                continue;
            }
            Vec_IntWriteEntry( vMap, iFanin, Abc_Var2Lit(i, Gia_ObjFaninC0(pObj)) );
        }
    }
    // check fanouts of the critical barbufs
    Gia_ManForEachObjVec( vCrits, p, pObj, i )
    {
        assert( Gia_ObjIsBuf(pObj) );
        if ( Vec_IntEntry(vFan, i) == 0 )
            continue;
        iFanin = Gia_ObjFaninId0p( p, pObj );
        CountFans[(int)(iFanin != 0)]++;
    }
    printf( "Detected %d const (out of %d) and %d shared (out of %d) barbufs with fanout.\n", 
        CountFans[0], CountCrit[0], CountFans[1], CountCrit[1] );
    Vec_IntFree( vMap );
    Vec_IntFree( vFan );
    Vec_IntFree( vCrits );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Gia_ManPatchBufDriver( Gia_Man_t * p, int iBuf, int iLit0 )  
{
    Gia_Obj_t * pObjBuf  = Gia_ManObj( p, iBuf );
    assert( Gia_ObjIsBuf(pObjBuf) );
    assert( Gia_ObjId(p, pObjBuf) > Abc_Lit2Var(iLit0) );
    pObjBuf->iDiff1  = pObjBuf->iDiff0  = Gia_ObjId(p, pObjBuf) - Abc_Lit2Var(iLit0);
    pObjBuf->fCompl1 = pObjBuf->fCompl0 = Abc_LitIsCompl(iLit0);
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManSweepHierarchy( Gia_Man_t * p )
{
    Vec_Int_t * vMap = Vec_IntStart( Gia_ManObjNum(p) );
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj, * pObjNew, * pObjNewR;
    int i, iFanin, CountReals[2] = {0};

    // duplicate AIG while propagating constants and equivalences 
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManHashAlloc( pNew );
    Gia_ManForEachObj1( p, pObj, i )
    {
        if ( Gia_ObjIsBuf(pObj) )
        {
            pObj->Value = Gia_ManAppendBuf( pNew, Gia_ObjFanin0Copy(pObj) );
            pObjNew = Gia_ManObj( pNew, Abc_Lit2Var(pObj->Value) );
            iFanin = Gia_ObjFaninId0p( pNew, pObjNew );
            if ( iFanin == 0 )
            {
                pObj->Value = Gia_ObjFaninC0(pObjNew);
                CountReals[0]++;
                Gia_ManPatchBufDriver( pNew, Gia_ObjId(pNew, pObjNew), 0 );
            }
            else if ( Vec_IntEntry(vMap, iFanin) )
            {
                pObjNewR = Gia_ManObj( pNew, Vec_IntEntry(vMap, iFanin) );
                pObj->Value = Abc_Var2Lit( Vec_IntEntry(vMap, iFanin), Gia_ObjFaninC0(pObjNewR) ^ Gia_ObjFaninC0(pObjNew) );
                CountReals[1]++;
                Gia_ManPatchBufDriver( pNew, Gia_ObjId(pNew, pObjNew), 0 );
            }
            else
                Vec_IntWriteEntry( vMap, iFanin, Gia_ObjId(pNew, pObjNew) );
        }
        else if ( Gia_ObjIsAnd(pObj) )
            pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        else if ( Gia_ObjIsCi(pObj) )
            pObj->Value = Gia_ManAppendCi( pNew );
        else if ( Gia_ObjIsCo(pObj) )
            pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    }
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
//    printf( "Updated %d const and %d shared.\n", CountReals[0], CountReals[1] );
    Vec_IntFree( vMap );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Flattens the logic hierarchy of the netlist.]

  Description [This procedure requires that models are uniqified.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManFlattenLogicPrepare( Abc_Ntk_t * pNtk )
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
    return Abc_NtkPiNum(pNtk) + Abc_NtkPoNum(pNtk);
}
int Abc_NtkFlattenHierarchyGia_rec( Gia_Man_t * pNew, Vec_Ptr_t * vSupers, Abc_Obj_t * pObj, Vec_Ptr_t * vBuffers )
{
    Abc_Ntk_t * pModel;
    Abc_Obj_t * pBox, * pFanin;  
    int iLit, i;
    if ( pObj->iTemp != -1 )
        return pObj->iTemp;
    if ( Abc_ObjIsNet(pObj) || Abc_ObjIsPo(pObj) || Abc_ObjIsBi(pObj) )
        return (pObj->iTemp = Abc_NtkFlattenHierarchyGia_rec(pNew, vSupers, Abc_ObjFanin0(pObj), vBuffers));
    if ( Abc_ObjIsPi(pObj) )
    {
        pBox   = (Abc_Obj_t *)Vec_PtrPop( vSupers );
        pModel = Abc_ObjModel(pBox);
        //printf( "   Exiting %s\n", Abc_NtkName(pModel) );
        assert( Abc_ObjFaninNum(pBox) == Abc_NtkPiNum(pModel) );
        assert( pObj->iData >= 0 && pObj->iData < Abc_NtkPiNum(pModel) );
        pFanin = Abc_ObjFanin( pBox, pObj->iData );
        iLit   = Abc_NtkFlattenHierarchyGia_rec( pNew, vSupers, pFanin, vBuffers );
        Vec_PtrPush( vSupers, pBox );
        //if ( vBuffers ) Vec_PtrPush( vBuffers, pFanin ); // save BI
        if ( vBuffers ) Vec_PtrPush( vBuffers, pObj );   // save PI
        return (pObj->iTemp = (vBuffers ? Gia_ManAppendBuf(pNew, iLit) : iLit));
    }
    if ( Abc_ObjIsBo(pObj) )
    {
        pBox   = Abc_ObjFanin0(pObj);
        assert( Abc_ObjIsBox(pBox) );
        Vec_PtrPush( vSupers, pBox );
        pModel = Abc_ObjModel(pBox);
        //printf( "Entering %s\n", Abc_NtkName(pModel) );
        assert( Abc_ObjFanoutNum(pBox) == Abc_NtkPoNum(pModel) );
        assert( pObj->iData >= 0 && pObj->iData < Abc_NtkPoNum(pModel) );
        pFanin = Abc_NtkPo( pModel, pObj->iData );
        iLit   = Abc_NtkFlattenHierarchyGia_rec( pNew, vSupers, pFanin, vBuffers );
        Vec_PtrPop( vSupers );
        //if ( vBuffers ) Vec_PtrPush( vBuffers, pObj );   // save BO
        if ( vBuffers ) Vec_PtrPush( vBuffers, pFanin ); // save PO
        return (pObj->iTemp = (vBuffers ? Gia_ManAppendBuf(pNew, iLit) : iLit));
    }
    assert( Abc_ObjIsNode(pObj) );
    Abc_ObjForEachFanin( pObj, pFanin, i )
        Abc_NtkFlattenHierarchyGia_rec( pNew, vSupers, pFanin, vBuffers );
    return (pObj->iTemp = Abc_NodeStrashToGia( pNew, pObj ));
}
Gia_Man_t * Abc_NtkFlattenHierarchyGia( Abc_Ntk_t * pNtk, Vec_Ptr_t ** pvBuffers, int fVerbose )
{
    int fUseBufs = 1;
    Gia_Man_t * pNew, * pTemp; 
    Abc_Ntk_t * pModel;
    Abc_Obj_t * pTerm;
    Vec_Ptr_t * vSupers;
    Vec_Ptr_t * vBuffers = fUseBufs ? Vec_PtrAlloc(1000) : NULL;
    int i, Counter = 0; 
    assert( Abc_NtkIsNetlist(pNtk) );
//    Abc_NtkPrintBoxInfo( pNtk );

    // set the PI/PO numbers
    Counter -= Abc_NtkPiNum(pNtk) + Abc_NtkPoNum(pNtk);
    if ( !pNtk->pDesign )
        Counter += Gia_ManFlattenLogicPrepare( pNtk );
    else
        Vec_PtrForEachEntry( Abc_Ntk_t *, pNtk->pDesign->vModules, pModel, i )
            Counter += Gia_ManFlattenLogicPrepare( pModel );

    // start the manager
    pNew = Gia_ManStart( Abc_NtkObjNumMax(pNtk) );
    pNew->pName = Abc_UtilStrsav(pNtk->pName);
    pNew->pSpec = Abc_UtilStrsav(pNtk->pSpec);

    // create PIs and buffers
    Abc_NtkForEachPi( pNtk, pTerm, i )
        pTerm->iTemp = Gia_ManAppendCi( pNew );

    // call recursively
    vSupers = Vec_PtrAlloc( 100 );
    Gia_ManHashAlloc( pNew );
    Abc_NtkForEachPo( pNtk, pTerm, i )
        Abc_NtkFlattenHierarchyGia_rec( pNew, vSupers, pTerm, vBuffers );
    Gia_ManHashStop( pNew );
    Vec_PtrFree( vSupers );
    printf( "Hierarchy reader flattened %d instances of boxes and added %d barbufs (out of %d).\n", 
        pNtk->pDesign ? Vec_PtrSize(pNtk->pDesign->vModules)-1 : 0, Vec_PtrSize(vBuffers), Counter );

    // create buffers and POs
    Abc_NtkForEachPo( pNtk, pTerm, i )
        Gia_ManAppendCo( pNew, pTerm->iTemp );

    if ( pvBuffers )
        *pvBuffers = vBuffers;
    else
        Vec_PtrFreeP( &vBuffers );

    // cleanup
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
//    Gia_ManPrintStats( pNew, NULL );
    pNew = Gia_ManSweepHierarchy( pTemp = pNew );
    Gia_ManStop( pTemp );
//    Gia_ManPrintStats( pNew, NULL );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Inserts the result of mapping into logic hierarchy.]

  Description [When this procedure is called PIs/POs of pNtk
  point to the corresponding nodes in network with barbufs.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Gia_ManInsertOne_rec( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNew, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanin;  int i;
    if ( pObj == NULL )
        return Abc_NtkCreateNodeConst0( pNtk );
    assert( Abc_ObjNtk(pObj) == pNew );
    if ( pObj->pCopy )
        return pObj->pCopy;
    Abc_ObjForEachFanin( pObj, pFanin, i )
        Gia_ManInsertOne_rec( pNtk, pNew, pFanin );
    pObj->pCopy = Abc_NtkDupObj( pNtk, pObj, 0 );
    Abc_ObjForEachFanin( pObj, pFanin, i )
        Abc_ObjAddFanin( pObj, pFanin );
    return pObj->pCopy;
}
void Gia_ManInsertOne( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNew )
{
    Abc_Obj_t * pObj, * pBox;  int i, k;
    assert( !Abc_NtkHasMapping(pNtk) );
    assert( Abc_NtkHasMapping(pNew) );
    // check that PIs point to barbufs
    Abc_NtkForEachPi( pNtk, pObj, i )
        assert( !pObj->pCopy || Abc_ObjNtk(pObj->pCopy) == pNew );
    // make barbufs point to box outputs
    Abc_NtkForEachBox( pNtk, pBox, i )
        Abc_ObjForEachFanout( pBox, pObj, k )
        {
            pObj->pCopy = Abc_NtkPo(Abc_ObjModel(pBox), k)->pCopy;
            assert( !pObj->pCopy || Abc_ObjNtk(pObj->pCopy) == pNew );
        }
    // remove internal nodes
    Abc_NtkForEachNode( pNtk, pObj, i )
        Abc_NtkDeleteObj( pObj );
    // start traversal from box inputs
    Abc_NtkForEachBox( pNtk, pBox, i )
        Abc_ObjForEachFanin( pBox, pObj, k )
            if ( Abc_ObjFaninNum(pObj) == 0 )
                Abc_ObjAddFanin( pObj, Gia_ManInsertOne_rec(pNtk, pNew, Abc_NtkPi(Abc_ObjModel(pBox), k)->pCopy) );
    // start traversal from primary outputs
    Abc_NtkForEachPo( pNtk, pObj, i )
        if ( Abc_ObjFaninNum(pObj) == 0 )
            Abc_ObjAddFanin( pObj, Gia_ManInsertOne_rec(pNtk, pNew, pObj->pCopy) );
    // update the functionality manager
    pNtk->pManFunc = pNew->pManFunc;
    pNtk->ntkFunc  = pNew->ntkFunc;
    assert( Abc_NtkHasMapping(pNtk) );
}
void Abc_NtkInsertHierarchyGia( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNew, int fVerbose )
{
    Vec_Ptr_t * vBuffers;
    Gia_Man_t * pGia = Abc_NtkFlattenHierarchyGia( pNtk, &vBuffers, 0 );
    Abc_Ntk_t * pModel;  
    Abc_Obj_t * pObj; 
    int i, k = 0;

    assert( Gia_ManPiNum(pGia) == Abc_NtkPiNum(pNtk) );
    assert( Gia_ManPiNum(pGia) == Abc_NtkPiNum(pNew) );
    assert( Gia_ManPoNum(pGia) == Abc_NtkPoNum(pNtk) );
    assert( Gia_ManPoNum(pGia) == Abc_NtkPoNum(pNew) );
    assert( Gia_ManBufNum(pGia) == Vec_PtrSize(vBuffers) );
    assert( Gia_ManBufNum(pGia) == pNew->nBarBufs2 );
    Gia_ManStop( pGia );

    // clean the networks
    if ( !pNtk->pDesign )
        Abc_NtkCleanCopy( pNtk );
    else
        Vec_PtrForEachEntry( Abc_Ntk_t *, pNtk->pDesign->vModules, pModel, i )
            Abc_NtkCleanCopy( pModel );

    // annotate PIs and POs of each network with barbufs
    Abc_NtkForEachPi( pNew, pObj, i )
        Abc_NtkPi(pNtk, i)->pCopy = pObj;
    Abc_NtkForEachPo( pNew, pObj, i )
        Abc_NtkPo(pNtk, i)->pCopy = pObj;
    Abc_NtkForEachBarBuf( pNew, pObj, i )
        ((Abc_Obj_t *)Vec_PtrEntry(vBuffers, k++))->pCopy = pObj;
    Vec_PtrFree( vBuffers );

    // connect each model
    Abc_NtkCleanCopy( pNew );
    Gia_ManInsertOne( pNtk, pNew );
    if ( pNtk->pDesign )
        Vec_PtrForEachEntry( Abc_Ntk_t *, pNtk->pDesign->vModules, pModel, i )
            if ( pModel != pNtk )
                Gia_ManInsertOne( pModel, pNew );
}

static Vec_Bit_t * GiaHie_GenUsed( Gia_Man_t * p, int fBuf )
{
    Gia_Obj_t * pObj; int i;
    Vec_Bit_t * vUsed = Vec_BitStart( Gia_ManObjNum(p) );
    Gia_ManForEachAnd( p, pObj, i )
    {
        if ( fBuf )
            Vec_BitWriteEntry( vUsed, i, 1 );
        if ( Gia_ObjFaninC0(pObj) ^ fBuf )
            Vec_BitWriteEntry( vUsed, Gia_ObjFaninId0(pObj, i), 1 );
        if ( Gia_ObjFaninC1(pObj) ^ fBuf )
            Vec_BitWriteEntry( vUsed, Gia_ObjFaninId1(pObj, i), 1 );
    }
    Gia_ManForEachCo( p, pObj, i )
        if ( Gia_ObjFaninC0(pObj) ^ fBuf )
            Vec_BitWriteEntry( vUsed, Gia_ObjFaninId0p(p, pObj), 1 );
    Vec_BitWriteEntry( vUsed, 0, 0 ); // clean zero
    return vUsed;
}
static int GiaHie_NameIsLegalInVerilog( char * pName )
{
    // identifier ::= simple_identifier | escaped_identifier
    // simple_identifier ::= [a-zA-Z_][a-zA-Z0-9_$]
    // escaped_identifier ::= \ {Any_ASCII_character_except_white_space} white_space
    // white_space ::= space | tab | newline
    assert( pName != NULL && *pName != '\0' );
    if ( *pName == '\\' )
        return 1;
    if ( (*pName < 'a' || *pName > 'z') && (*pName < 'A' || *pName > 'Z') && *pName != '_' )
        return 0;
    while ( *(++pName) )
        if ( (*pName < 'a' || *pName > 'z') && (*pName < 'A' || *pName > 'Z') && (*pName < '0' || *pName > '9') && *pName != '_' && *pName != '$' ) 
            return 0;
    return 1;
}
static char * GiaHie_ObjGetDumpName( Vec_Ptr_t * vNames, char c, int i, int d )
{
    static char pBuffer[10000];
    if ( vNames )
    {
        char * pName = (char *)Vec_PtrEntry(vNames, i);
        if ( GiaHie_NameIsLegalInVerilog(pName) )
            sprintf( pBuffer, "%s", pName );
        else
            sprintf( pBuffer, "\\%s ", pName );
    }
    else
        sprintf( pBuffer, "%c%0*d%c", c, d, i, c );
    return pBuffer;
}
static void GiaHie_WriteNames( FILE * pFile, char c, int n, Vec_Ptr_t * vNames, int Start, int Skip, Vec_Bit_t * vObjs, int fReverse )
{
    int Digits = Abc_Base10Log( n );
    int Length = Start, i, fFirst = 1; 
    char * pName;
    for ( i = 0; i < n; i++ )
    {
        int k = fReverse ? n-1-i : i;
        if ( vObjs && !Vec_BitEntry(vObjs, k) )
            continue;
        pName = GiaHie_ObjGetDumpName( vNames, c, k, Digits );
        Length += strlen(pName) + 2;
        if ( Length > 60 )
        {
            fprintf( pFile, ",\n    " );
            Length = Skip;
            fFirst = 1;
        }
        fprintf( pFile, "%s%s", fFirst ? "":", ", pName );
        fFirst = 0;
    }
}
static void GiaHie_PrintOneName( FILE * pFile, char * pName, int Size )
{
    int i;
    for ( i = 0; i < Size; i++ )
        fprintf( pFile, "%c", pName[i] );
}
static int GiaHie_CountSymbs( char * pName )
{
    int i;
    for ( i = 0; pName[i]; i++ )
        if ( pName[i] == '[' )
            break;
    return i;
}
static int GiaHie_ReadRangeNum( char * pName, int Size )
{
    if ( pName[Size] == 0 )
        return -1;
    assert( pName[Size] == '[' );
    return atoi(pName+Size+1);
}
static Vec_Int_t * GiaHie_CountSymbsAll( Vec_Ptr_t * vNames )
{
    char * pNameLast = (char *)Vec_PtrEntry(vNames, 0), * pName;
    int i, nSymbsLast = GiaHie_CountSymbs(pNameLast);
    Vec_Int_t * vArray = Vec_IntAlloc( Vec_PtrSize(vNames) * 2 );
    Vec_IntPush( vArray, 0 );
    Vec_IntPush( vArray, nSymbsLast );
    Vec_PtrForEachEntryStart( char *, vNames, pName, i, 1 )
    {
        int nSymbs = GiaHie_CountSymbs(pName);
        if ( nSymbs == nSymbsLast && !strncmp(pName, pNameLast, nSymbsLast) )
            continue;
        Vec_IntPush( vArray, i );
        Vec_IntPush( vArray, nSymbs );
        pNameLast  = pName;
        nSymbsLast = nSymbs;
    }
    return vArray;
}
static void GiaHie_DumpIoList( Gia_Man_t * p, FILE * pFile, int fOuts, int fReverse )
{
    Vec_Ptr_t * vNames = fOuts ? p->vNamesOut : p->vNamesIn;
    if ( vNames == NULL )
        fprintf( pFile, "_%c_", fOuts ? 'o' : 'i' );
    else
    {
        Vec_Int_t * vArray = GiaHie_CountSymbsAll( vNames );
        int iName, Size, i;
        Vec_IntForEachEntryDouble( vArray, iName, Size, i )
        {
            if ( fReverse )
            {
                iName = Vec_IntEntry(vArray, Vec_IntSize(vArray)-2-i);
                Size  = Vec_IntEntry(vArray, Vec_IntSize(vArray)-1-i);
            }
            if ( i ) fprintf( pFile, ", " );
            GiaHie_PrintOneName( pFile, (char *)Vec_PtrEntry(vNames, iName), Size );
        }
        Vec_IntFree( vArray );            
    }
}
static Vec_Bit_t * GiaHie_CollectMultiBits( Vec_Ptr_t * vNames, int n )
{
    Vec_Bit_t * vBits = Vec_BitStart( n );
    if ( n == 0 )
        return vBits;
    if ( vNames == NULL )
    {
        if ( n > 1 )
        {
            int i;
            for ( i = 0; i < n; i++ )
                Vec_BitWriteEntry( vBits, i, 1 );
        }
        return vBits;
    }
    {
        Vec_Int_t * vArray = GiaHie_CountSymbsAll( vNames );
        int iName, Size, i;
        int nNames = Vec_PtrSize( vNames );
        Vec_IntForEachEntryDouble( vArray, iName, Size, i )
        {
            int iNameNext = Vec_IntSize(vArray) > i+2 ? Vec_IntEntry(vArray, i+2) : nNames;
            int k;
            if ( iNameNext - iName <= 1 )
                continue;
            for ( k = iName; k < iNameNext && k < n; k++ )
                Vec_BitWriteEntry( vBits, k, 1 );
        }
        Vec_IntFree( vArray );
    }
    return vBits;
}
static int GiaHie_DumpIoListMulti( Gia_Man_t * p, FILE * pFile, int fOuts, int fReverse )
{
    Vec_Ptr_t * vNames = fOuts ? p->vNamesOut : p->vNamesIn;
    int nNames = vNames ? Vec_PtrSize(vNames) : (fOuts ? Gia_ManCoNum(p) : Gia_ManCiNum(p));
    if ( vNames == NULL )
    {
        if ( nNames > 1 )
        {
            fprintf( pFile, "_%c_", fOuts ? 'o' : 'i' );
            return 1;
        }
        return 0;
    }
    {
        Vec_Int_t * vArray = GiaHie_CountSymbsAll( vNames );
        int nGroups = Vec_IntSize(vArray) / 2;
        int idx, fFirst = 1;
        for ( idx = 0; idx < nGroups; idx++ )
        {
            int g = fReverse ? (nGroups - 1 - idx) : idx;
            int iName = Vec_IntEntry(vArray, 2*g);
            int Size = Vec_IntEntry(vArray, 2*g + 1);
            int iNameNext = (g + 1 < nGroups) ? Vec_IntEntry(vArray, 2*(g + 1)) : nNames;
            if ( iNameNext - iName <= 1 )
                continue;
            if ( !fFirst )
                fprintf( pFile, ", " );
            GiaHie_PrintOneName( pFile, (char *)Vec_PtrEntry(vNames, iName), Size );
            fFirst = 0;
        }
        Vec_IntFree( vArray );
        return !fFirst;
    }
}
static void GiaHie_DumpIoRanges( Gia_Man_t * p, FILE * pFile, int fOuts )
{
    Vec_Ptr_t * vNames = fOuts ? p->vNamesOut : p->vNamesIn;
    if ( p->vNamesOut == NULL )
        fprintf( pFile, "%s [%d:0] _%c_;\n", fOuts ? "output" : "input", fOuts ? Gia_ManPoNum(p)-1 : Gia_ManPiNum(p)-1, fOuts ? 'o' : 'i' );
    else
    {
        Vec_Int_t * vArray = GiaHie_CountSymbsAll( vNames );
        int iName, Size, i;
        Vec_IntForEachEntryDouble( vArray, iName, Size, i )
        {
            int iNameNext    = Vec_IntSize(vArray) > i+2 ? Vec_IntEntry(vArray, i+2) : Vec_PtrSize(vNames);
            char * pName     = (char *)Vec_PtrEntry(vNames, iName);
            char * pNameLast = (char *)Vec_PtrEntry(vNames, iNameNext-1);
            assert( !strncmp(pName, pNameLast, Size) );
            int NumBeg = GiaHie_ReadRangeNum( pName,     Size );
            int NumEnd = GiaHie_ReadRangeNum( pNameLast, Size );
            fprintf( pFile, "  %s ", fOuts ? "output" : "input" );
            if ( NumBeg != -1 && iName < iNameNext-1 )
                fprintf( pFile, "[%d:%d] ", NumEnd, NumBeg );
            GiaHie_PrintOneName( pFile, pName, Size );
            fprintf( pFile, ";\n" );                
        }
        Vec_IntFree( vArray );            
    }
}
static void GiaHie_DumpModuleName( FILE * pFile, char * pName )
{
    int i;
    if ( pName == NULL || pName[0] == '\0' )
    {
        fprintf( pFile, "top" );
        return;
    }
    if ( !isalpha(pName[0]) && pName[0] != '_' )
        fprintf( pFile, "m" );
    for ( i = 0; i < (int)strlen(pName); i++ )
        if ( isalpha(pName[i]) || isdigit(pName[i]) || pName[i] == '_' )
            fprintf( pFile, "%c", pName[i] );
        else
            fprintf( pFile, "_" );
}
static void GiaHie_DumpInterfaceGates( Gia_Man_t * p, char * pFileName )
{
    Gia_Obj_t * pObj;
    Vec_Bit_t * vInvs, * vUsed;
    int nDigits  = Abc_Base10Log( Gia_ManObjNum(p) );
    int nDigitsI = Abc_Base10Log( Gia_ManPiNum(p) );
    int nDigitsO = Abc_Base10Log( Gia_ManPoNum(p) );
    int i;

    FILE * pFile = fopen( pFileName, "wb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open output file \"%s\".\n", pFileName );
        return;
    }

    vInvs = GiaHie_GenUsed( p, 0 );
    vUsed = GiaHie_GenUsed( p, 1 );

    fprintf( pFile, "module " );
    GiaHie_DumpModuleName( pFile, p->pName );
    fprintf( pFile, " ( " );
    GiaHie_DumpIoList( p, pFile, 0, 0 );
    fprintf( pFile, ", " );
    GiaHie_DumpIoList( p, pFile, 1, 0 );    
    fprintf( pFile, " );\n\n" );
    GiaHie_DumpIoRanges( p, pFile, 0 );
    GiaHie_DumpIoRanges( p, pFile, 1 );
    fprintf( pFile, "\n" );

    fprintf( pFile, "  wire " );
    GiaHie_WriteNames( pFile, 'x', Gia_ManPiNum(p), p->vNamesIn, 8, 4, NULL, 0 );
    fprintf( pFile, ";\n\n" );

    fprintf( pFile, "  wire " );
    GiaHie_WriteNames( pFile, 'z', Gia_ManPoNum(p), p->vNamesOut, 9, 4, NULL, 0 );
    fprintf( pFile, ";\n\n" );

    {
        Vec_Bit_t * vMultiIn = GiaHie_CollectMultiBits( p->vNamesIn, Gia_ManCiNum(p) );
        Vec_Bit_t * vMultiOut = GiaHie_CollectMultiBits( p->vNamesOut, Gia_ManCoNum(p) );
        int fHasMultiIn = Vec_BitCount( vMultiIn );
        int fHasMultiOut = Vec_BitCount( vMultiOut );
        if ( fHasMultiIn )
        {
            fprintf( pFile, "  assign { " );
            GiaHie_WriteNames( pFile, 'x', Gia_ManCiNum(p), p->vNamesIn, 8, 4, vMultiIn, 1 );
            fprintf( pFile, " } = { " );
            GiaHie_DumpIoListMulti( p, pFile, 0, 1 );
            fprintf( pFile, " };\n\n" );
        }
        if ( fHasMultiOut )
        {
            fprintf( pFile, "  assign { " );
            GiaHie_DumpIoListMulti( p, pFile, 1, 1 );
            fprintf( pFile, " } = { " );
            GiaHie_WriteNames( pFile, 'z', Gia_ManCoNum(p), p->vNamesOut, 9, 4, vMultiOut, 1 );
            fprintf( pFile, " };\n\n" );
        }
        Vec_BitFree( vMultiIn );
        Vec_BitFree( vMultiOut );
    }

    if ( Vec_BitCount(vUsed) )
    {
        fprintf( pFile, "  wire " );
        GiaHie_WriteNames( pFile, 'n', Gia_ManObjNum(p), NULL, 7, 4, vUsed, 0 );
        fprintf( pFile, ";\n\n" );
    }

    if ( Vec_BitCount(vInvs) )
    {
        fprintf( pFile, "  wire " );
        GiaHie_WriteNames( pFile, 'i', Gia_ManObjNum(p), NULL, 7, 4, vInvs, 0 );
        fprintf( pFile, ";\n\n" );
    }

    // input inverters
    Gia_ManForEachCi( p, pObj, i )
    {
        if ( Vec_BitEntry(vUsed, Gia_ObjId(p, pObj)) )
        {
            fprintf( pFile, "  buf ( %s,", GiaHie_ObjGetDumpName(NULL, 'n', Gia_ObjId(p, pObj), nDigits) );
            fprintf( pFile, " %s );\n",   GiaHie_ObjGetDumpName(p->vNamesIn, 'x', i, nDigitsI) );
        }
        if ( Vec_BitEntry(vInvs, Gia_ObjId(p, pObj)) )
        {
            fprintf( pFile, "  not ( %s,", GiaHie_ObjGetDumpName(NULL, 'i', Gia_ObjId(p, pObj), nDigits) );
            fprintf( pFile, " %s );\n",   GiaHie_ObjGetDumpName(p->vNamesIn, 'x', i, nDigitsI) );
        }
    }

    // internal nodes and their inverters
    fprintf( pFile, "\n" );
    Gia_ManForEachAnd( p, pObj, i )
    {
        fprintf( pFile, "  and ( %s,", GiaHie_ObjGetDumpName(NULL, 'n', i, nDigits) );
        fprintf( pFile, " %s,",       GiaHie_ObjGetDumpName(NULL, (char)(Gia_ObjFaninC0(pObj)? 'i':'n'), Gia_ObjFaninId0(pObj, i), nDigits) );
        fprintf( pFile, " %s );\n",   GiaHie_ObjGetDumpName(NULL, (char)(Gia_ObjFaninC1(pObj)? 'i':'n'), Gia_ObjFaninId1(pObj, i), nDigits) );
        if ( Vec_BitEntry(vInvs, i) )
        {
            fprintf( pFile, "  not ( %s,", GiaHie_ObjGetDumpName(NULL, 'i', i, nDigits) );
            fprintf( pFile, " %s );\n",   GiaHie_ObjGetDumpName(NULL, 'n', i, nDigits) );
        }
    }
    
    // output drivers
    fprintf( pFile, "\n" );
    Gia_ManForEachCo( p, pObj, i )
    {
        fprintf( pFile, "  buf ( %s, ", GiaHie_ObjGetDumpName(p->vNamesOut, 'z', i, nDigitsO) );
        if ( Gia_ObjIsConst0(Gia_ObjFanin0(pObj)) )
            fprintf( pFile, "1\'b%d );\n", Gia_ObjFaninC0(pObj) );
        else 
            fprintf( pFile, "%s );\n", GiaHie_ObjGetDumpName(NULL, (char)(Gia_ObjFaninC0(pObj)? 'i':'n'), Gia_ObjFaninId0p(p, pObj), nDigits) );
    }

    fprintf( pFile, "\nendmodule\n\n" );
    fclose( pFile );

    Vec_BitFree( vInvs );
    Vec_BitFree( vUsed );
}

static void GiaHie_PrintObjName( FILE * pFile, int ObjId, int nDigits )
{
    fprintf( pFile, "n%0*d", nDigits, ObjId );
}
static void GiaHie_PrintObjLit( FILE * pFile, int ObjId, int fCompl, int nDigits )
{
    fprintf( pFile, "%c", fCompl ? '~' : ' ' );
    GiaHie_PrintObjName( pFile, ObjId, nDigits );
}
static void GiaHie_WriteObjRange( FILE * pFile, Gia_Man_t * p, int iStart, int iStop, int nDigits, int Start, int Skip, int fReverse, int fCis )
{
    int Length = Start, i, fFirst = 1;
    int n = iStop - iStart;
    for ( i = 0; i < n; i++ )
    {
        int Idx = fReverse ? (iStop - 1 - i) : (iStart + i);
        int ObjId = fCis ? Gia_ManCiIdToId(p, Idx) : Gia_ManCoIdToId(p, Idx);
        char pName[64];
        sprintf( pName, "n%0*d", nDigits, ObjId );
        Length += strlen(pName) + 2;
        if ( Length > 100 )
        {
            fprintf( pFile, ",\n    " );
            Length = Skip;
            fFirst = 1;
        }
        fprintf( pFile, "%s%s", fFirst ? "":", ", pName );
        fFirst = 0;
    }
}
static void GiaHie_WritePiPoNames( FILE * pFile, const char * pPrefix, int nBits, int nDigits, int Start, int Skip, int fReverse )
{
    int Length = Start, i, fFirst = 1;
    for ( i = 0; i < nBits; i++ )
    {
        int Idx = fReverse ? (nBits - 1 - i) : i;
        char pName[64];
        sprintf( pName, "%s%0*d", pPrefix, nDigits, Idx );
        Length += strlen(pName) + 2;
        if ( Length > 100 )
        {
            fprintf( pFile, ",\n    " );
            Length = Skip;
            fFirst = 1;
        }
        fprintf( pFile, "%s%s", fFirst ? "":", ", pName );
        fFirst = 0;
    }
}
static int GiaHie_IsBitLevelNames( Vec_Ptr_t * vNames )
{
    int nNames, nGroups, idx;
    Vec_Int_t * vArray;
    if ( vNames == NULL )
        return 1;
    nNames = Vec_PtrSize( vNames );
    if ( nNames == 0 )
        return 1;
    vArray = GiaHie_CountSymbsAll( vNames );
    nGroups = Vec_IntSize(vArray) / 2;
    for ( idx = 0; idx < nGroups; idx++ )
    {
        int iName = Vec_IntEntry(vArray, 2*idx);
        int iNameNext = (idx + 1 < nGroups) ? Vec_IntEntry(vArray, 2*(idx + 1)) : nNames;
        if ( iNameNext - iName > 1 )
        {
            Vec_IntFree( vArray );
            return 0;
        }
    }
    Vec_IntFree( vArray );
    return 1;
}
static void GiaHie_DumpPortDeclsOne( Gia_Man_t * p, FILE * pFile, int fOuts, int * pfFirst )
{
    Vec_Ptr_t * vNames = fOuts ? p->vNamesOut : p->vNamesIn;
    int nBits = fOuts ? Gia_ManPoNum(p) : Gia_ManPiNum(p);
    int fUsePiPo = (nBits > 2) && GiaHie_IsBitLevelNames( vNames );
    if ( nBits == 0 )
        return;
    if ( fUsePiPo )
    {
        int nDigits = Abc_Base10Log( nBits );
        if ( nDigits < 2 )
            nDigits = 2;
        if ( !(*pfFirst) )
            fprintf( pFile, ",\n" );
        fprintf( pFile, "  %s ", fOuts ? "output" : "input" );
        GiaHie_WritePiPoNames( pFile, fOuts ? "po" : "pi", nBits, nDigits, 8, 4, 0 );
        *pfFirst = 0;
        return;
    }
    if ( vNames == NULL )
    {
        if ( !(*pfFirst) )
            fprintf( pFile, ",\n" );
        fprintf( pFile, "  %s [%d:0] _%c_", fOuts ? "output" : "input", nBits-1, fOuts ? 'o' : 'i' );
        *pfFirst = 0;
        return;
    }
    {
        Vec_Int_t * vArray = GiaHie_CountSymbsAll( vNames );
        int iName, Size, i;
        Vec_IntForEachEntryDouble( vArray, iName, Size, i )
        {
            int iNameNext    = Vec_IntSize(vArray) > i+2 ? Vec_IntEntry(vArray, i+2) : Vec_PtrSize(vNames);
            char * pName     = (char *)Vec_PtrEntry(vNames, iName);
            char * pNameLast = (char *)Vec_PtrEntry(vNames, iNameNext-1);
            assert( !strncmp(pName, pNameLast, Size) );
            int NumBeg = GiaHie_ReadRangeNum( pName,     Size );
            int NumEnd = GiaHie_ReadRangeNum( pNameLast, Size );
            if ( !(*pfFirst) )
                fprintf( pFile, ",\n" );
            fprintf( pFile, "  %s ", fOuts ? "output" : "input" );
            if ( NumBeg != -1 && iName < iNameNext-1 )
                fprintf( pFile, "[%d:%d] ", NumEnd, NumBeg );
            GiaHie_PrintOneName( pFile, pName, Size );
            *pfFirst = 0;
        }
        Vec_IntFree( vArray );            
    }
}
static void GiaHie_DumpPortDecls( Gia_Man_t * p, FILE * pFile )
{
    int fFirst = 1;
    GiaHie_DumpPortDeclsOne( p, pFile, 0, &fFirst );
    GiaHie_DumpPortDeclsOne( p, pFile, 1, &fFirst );
}
static int GiaHie_ConstUsed( Gia_Man_t * p )
{
    Gia_Obj_t * pObj; int i;
    Gia_ManForEachAnd( p, pObj, i )
        if ( Gia_ObjFaninId0(pObj, i) == 0 || Gia_ObjFaninId1(pObj, i) == 0 )
            return 1;
    Gia_ManForEachCo( p, pObj, i )
        if ( Gia_ObjIsConst0(Gia_ObjFanin0(pObj)) )
            return 1;
    return 0;
}
static void GiaHie_DumpInputAssigns( Gia_Man_t * p, FILE * pFile, int nDigits )
{
    Vec_Ptr_t * vNames = p->vNamesIn;
    int nCis = Gia_ManCiNum(p);
    int fUsePiPo = (nCis > 2) && GiaHie_IsBitLevelNames( vNames );
    if ( nCis == 0 )
        return;
    if ( fUsePiPo )
    {
        int nDigitsPi = Abc_Base10Log( nCis );
        if ( nDigitsPi < 2 )
            nDigitsPi = 2;
        fprintf( pFile, "  assign { " );
        GiaHie_WriteObjRange( pFile, p, 0, nCis, nDigits, 11, 4, 1, 1 );
        fprintf( pFile, " } =\n    { " );
        GiaHie_WritePiPoNames( pFile, "pi", nCis, nDigitsPi, 18, 4, 1 );
        fprintf( pFile, " };\n" );
        return;
    }
    if ( vNames == NULL )
    {
        if ( nCis == 1 )
        {
            fprintf( pFile, "  assign " );
            GiaHie_PrintObjName( pFile, Gia_ManCiIdToId(p, 0), nDigits );
            fprintf( pFile, " = _i_;\n" );
        }
        else
        {
            fprintf( pFile, "  assign { " );
            GiaHie_WriteObjRange( pFile, p, 0, nCis, nDigits, 11, 4, 1, 1 );
            fprintf( pFile, " } = { _i_ };\n" );
        }
        return;
    }
    {
        Vec_Int_t * vArray = GiaHie_CountSymbsAll( vNames );
        int iName, Size, i;
        Vec_IntForEachEntryDouble( vArray, iName, Size, i )
        {
            int iNameNext = Vec_IntSize(vArray) > i+2 ? Vec_IntEntry(vArray, i+2) : Vec_PtrSize(vNames);
            int nBits = iNameNext - iName;
            char * pName = (char *)Vec_PtrEntry(vNames, iName);
            if ( nBits > 1 )
            {
                fprintf( pFile, "  assign { " );
                GiaHie_WriteObjRange( pFile, p, iName, iNameNext, nDigits, 11, 4, 1, 1 );
                fprintf( pFile, " } =\n    { " );
                GiaHie_PrintOneName( pFile, pName, Size );
                fprintf( pFile, " };\n" );
            }
            else
            {
                fprintf( pFile, "  assign " );
                GiaHie_PrintObjName( pFile, Gia_ManCiIdToId(p, iName), nDigits );
                fprintf( pFile, " = " );
                GiaHie_PrintOneName( pFile, pName, Size );
                fprintf( pFile, ";\n" );
            }
        }
        Vec_IntFree( vArray );
    }
}
static void GiaHie_DumpOutputAssigns( Gia_Man_t * p, FILE * pFile, int nDigits )
{
    Vec_Ptr_t * vNames = p->vNamesOut;
    int nCos = Gia_ManCoNum(p);
    int fUsePiPo = (nCos > 2) && GiaHie_IsBitLevelNames( vNames );
    if ( nCos == 0 )
        return;
    if ( fUsePiPo )
    {
        int nDigitsPo = Abc_Base10Log( nCos );
        if ( nDigitsPo < 2 )
            nDigitsPo = 2;
        fprintf( pFile, "  assign { " );
        GiaHie_WritePiPoNames( pFile, "po", nCos, nDigitsPo, 11, 4, 1 );
        fprintf( pFile, " } =\n    { " );
        GiaHie_WriteObjRange( pFile, p, 0, nCos, nDigits, 18, 4, 1, 0 );
        fprintf( pFile, " };\n" );
        return;
    }
    if ( vNames == NULL )
    {
        if ( nCos == 1 )
        {
            fprintf( pFile, "  assign _o_ = " );
            GiaHie_PrintObjName( pFile, Gia_ManCoIdToId(p, 0), nDigits );
            fprintf( pFile, ";\n" );
        }
        else
        {
            fprintf( pFile, "  assign { _o_ } = { " );
            GiaHie_WriteObjRange( pFile, p, 0, nCos, nDigits, 18, 4, 1, 0 );
            fprintf( pFile, " };\n" );
        }
        return;
    }
    {
        Vec_Int_t * vArray = GiaHie_CountSymbsAll( vNames );
        int iName, Size, i;
        Vec_IntForEachEntryDouble( vArray, iName, Size, i )
        {
            int iNameNext = Vec_IntSize(vArray) > i+2 ? Vec_IntEntry(vArray, i+2) : Vec_PtrSize(vNames);
            int nBits = iNameNext - iName;
            char * pName = (char *)Vec_PtrEntry(vNames, iName);
            if ( nBits > 1 )
            {
                fprintf( pFile, "  assign { " );
                GiaHie_PrintOneName( pFile, pName, Size );
                fprintf( pFile, " } =\n    { " );
                GiaHie_WriteObjRange( pFile, p, iName, iNameNext, nDigits, 18, 4, 1, 0 );
                fprintf( pFile, " };\n" );
            }
            else
            {
                fprintf( pFile, "  assign " );
                GiaHie_PrintOneName( pFile, pName, Size );
                fprintf( pFile, " = " );
                GiaHie_PrintObjName( pFile, Gia_ManCoIdToId(p, iName), nDigits );
                fprintf( pFile, ";\n" );
            }
        }
        Vec_IntFree( vArray );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void GiaHie_DumpInterfaceAssigns( Gia_Man_t * p, char * pFileName )
{
    Gia_Obj_t * pObj;
    int nDigits = Abc_Base10Log( Gia_ManObjNum(p) );
    int nPerLine = 4;
    int nOnLine = 0;
    int i;
    FILE * pFile = fopen( pFileName, "wb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open output file \"%s\".\n", pFileName );
        return;
    }

    fprintf( pFile, "module " );
    GiaHie_DumpModuleName( pFile, p->pName );
    fprintf( pFile, " (\n" );
    GiaHie_DumpPortDecls( p, pFile );
    fprintf( pFile, "\n);\n\n" );

    if ( Gia_ManCiNum(p) )
    {
        fprintf( pFile, "  wire " );
        GiaHie_WriteObjRange( pFile, p, 0, Gia_ManCiNum(p), nDigits, 7, 4, 0, 1 );
        fprintf( pFile, ";\n\n" );
        GiaHie_DumpInputAssigns( p, pFile, nDigits );
        fprintf( pFile, "\n" );
    }

    if ( Gia_ManCoNum(p) )
    {
        fprintf( pFile, "  wire " );
        GiaHie_WriteObjRange( pFile, p, 0, Gia_ManCoNum(p), nDigits, 7, 4, 0, 0 );
        fprintf( pFile, ";\n\n" );
        GiaHie_DumpOutputAssigns( p, pFile, nDigits );
        fprintf( pFile, "\n" );
    }

    if ( GiaHie_ConstUsed(p) )
        fprintf( pFile, "  wire n%0*d = 1'b0;\n\n", nDigits, 0 );

    Gia_ManForEachAnd( p, pObj, i )
    {
        if ( nOnLine == 0 )
            fprintf( pFile, "  " );
        fprintf( pFile, "wire n%0*d = ", nDigits, i );
        GiaHie_PrintObjLit( pFile, Gia_ObjFaninId0(pObj, i), Gia_ObjFaninC0(pObj), nDigits );
        fprintf( pFile, " & " );
        GiaHie_PrintObjLit( pFile, Gia_ObjFaninId1(pObj, i), Gia_ObjFaninC1(pObj), nDigits );
        fprintf( pFile, "; " );
        nOnLine++;
        if ( nOnLine == nPerLine )
        {
            fprintf( pFile, "\n" );
            nOnLine = 0;
        }
        else
            fprintf( pFile, " " );
    }
    if ( nOnLine != 0 )
        fprintf( pFile, "\n" );
    if ( Gia_ManAndNum(p) )
        fprintf( pFile, "\n" );

    Gia_ManForEachCo( p, pObj, i )
    {
        fprintf( pFile, "  assign n%0*d = ", nDigits, Gia_ManCoIdToId(p, i) );
        GiaHie_PrintObjLit( pFile, Gia_ObjFaninId0p(p, pObj), Gia_ObjFaninC0(pObj), nDigits );
        fprintf( pFile, ";\n" );
    }

    fprintf( pFile, "\nendmodule\n\n" );
    fclose( pFile );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_WriteVerilog( char * pFileName, Gia_Man_t * pGia, int fUseGates, int fVerbose )
{
    (void)fVerbose;
    if ( pFileName == NULL || pGia == NULL )
        return;
    if ( fUseGates )
        GiaHie_DumpInterfaceGates( pGia, pFileName );
    else
        GiaHie_DumpInterfaceAssigns( pGia, pFileName );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
