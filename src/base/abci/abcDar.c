/**CFile****************************************************************

  FileName    [abcDar.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [DAG-aware rewriting.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcDar.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "aig.h"
#include "saig.h"
#include "dar.h"
#include "cnf.h"
#include "fra.h"
#include "fraig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Converts the network from the AIG manager into ABC.]

  Description [Assumes that registers are ordered after PIs/POs.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters )
{
    Aig_Man_t * pMan;
    Aig_Obj_t * pObjNew;
    Abc_Obj_t * pObj;
    int i, nNodes, nDontCares;
    // make sure the latches follow PIs/POs
    if ( fRegisters ) 
    { 
        assert( Abc_NtkBoxNum(pNtk) == Abc_NtkLatchNum(pNtk) );
        Abc_NtkForEachCi( pNtk, pObj, i )
            if ( i < Abc_NtkPiNum(pNtk) )
            {
                assert( Abc_ObjIsPi(pObj) );
                if ( !Abc_ObjIsPi(pObj) )
                    printf( "Abc_NtkToDar(): Temporary bug: The PI ordering is wrong!\n" );
            }
            else
                assert( Abc_ObjIsBo(pObj) );
        Abc_NtkForEachCo( pNtk, pObj, i )
            if ( i < Abc_NtkPoNum(pNtk) )
            {
                assert( Abc_ObjIsPo(pObj) );
                if ( !Abc_ObjIsPo(pObj) )
                    printf( "Abc_NtkToDar(): Temporary bug: The PO ordering is wrong!\n" );
            }
            else
                assert( Abc_ObjIsBi(pObj) );
        // print warning about initial values
        nDontCares = 0;
        Abc_NtkForEachLatch( pNtk, pObj, i )
            if ( Abc_LatchIsInitDc(pObj) )
            {
                Abc_LatchSetInit0(pObj);
                nDontCares++;
            }
        if ( nDontCares )
        {
            printf( "Warning: %d registers in this network have don't-care init values.\n", nDontCares );
            printf( "The don't-care are assumed to be 0. The result may not verify.\n" );
            printf( "Use command \"print_latch\" to see the init values of registers.\n" );
            printf( "Use command \"zero\" to convert or \"init\" to change the values.\n" );
        }
    }
    // create the manager
    pMan = Aig_ManStart( Abc_NtkNodeNum(pNtk) + 100 );
    pMan->fCatchExor = fExors;

    pMan->pName = Extra_UtilStrsav( pNtk->pName );
    // save the number of registers
    if ( fRegisters )
    {
        pMan->nRegs = Abc_NtkLatchNum(pNtk);
        pMan->vFlopNums = Vec_IntStartNatural( pMan->nRegs );
//        pMan->vFlopNums = NULL;
//        pMan->vOnehots = Abc_NtkConverLatchNamesIntoNumbers( pNtk );
        if ( pNtk->vOnehots )
            pMan->vOnehots = (Vec_Ptr_t *)Vec_VecDupInt( (Vec_Vec_t *)pNtk->vOnehots );
    }
    // transfer the pointers to the basic nodes
    Abc_AigConst1(pNtk)->pCopy = (Abc_Obj_t *)Aig_ManConst1(pMan);
    Abc_NtkForEachCi( pNtk, pObj, i )
        pObj->pCopy = (Abc_Obj_t *)Aig_ObjCreatePi(pMan);
    // complement the 1-values registers
    if ( fRegisters )
        Abc_NtkForEachLatch( pNtk, pObj, i )
            if ( Abc_LatchIsInit1(pObj) )
                Abc_ObjFanout0(pObj)->pCopy = Abc_ObjNot(Abc_ObjFanout0(pObj)->pCopy);
    // perform the conversion of the internal nodes (assumes DFS ordering)
//    pMan->fAddStrash = 1;
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        pObj->pCopy = (Abc_Obj_t *)Aig_And( pMan, (Aig_Obj_t *)Abc_ObjChild0Copy(pObj), (Aig_Obj_t *)Abc_ObjChild1Copy(pObj) );
//        printf( "%d->%d ", pObj->Id, ((Aig_Obj_t *)pObj->pCopy)->Id );
    }
    pMan->fAddStrash = 0;
    // create the POs
    Abc_NtkForEachCo( pNtk, pObj, i )
        Aig_ObjCreatePo( pMan, (Aig_Obj_t *)Abc_ObjChild0Copy(pObj) );
    // complement the 1-valued registers
    if ( fRegisters )
        Aig_ManForEachLiSeq( pMan, pObjNew, i )
            if ( Abc_LatchIsInit1(Abc_ObjFanout0(Abc_NtkCo(pNtk,i))) )
                pObjNew->pFanin0 = Aig_Not(pObjNew->pFanin0);
    // remove dangling nodes
    nNodes = Aig_ManCleanup( pMan );
    if ( !fExors && nNodes )
        printf( "Abc_NtkToDar(): Unexpected %d dangling nodes when converting to AIG!\n", nNodes );
//Aig_ManDumpVerilog( pMan, "test.v" );
    if ( !Aig_ManCheck( pMan ) )
    {
        printf( "Abc_NtkToDar: AIG check has failed.\n" );
        Aig_ManStop( pMan );
        return NULL;
    }
    return pMan;
}

/**Function*************************************************************

  Synopsis    [Converts the network from the AIG manager into ABC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkFromDar( Abc_Ntk_t * pNtkOld, Aig_Man_t * pMan )
{
    Vec_Ptr_t * vNodes;
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pObjNew;
    Aig_Obj_t * pObj;
    int i;
    assert( pMan->nAsserts == 0 );
//    assert( Aig_ManRegNum(pMan) == Abc_NtkLatchNum(pNtkOld) );
    // perform strashing
    pNtkNew = Abc_NtkStartFrom( pNtkOld, ABC_NTK_STRASH, ABC_FUNC_AIG );
    // transfer the pointers to the basic nodes
    Aig_ManConst1(pMan)->pData = Abc_AigConst1(pNtkNew);
    Aig_ManForEachPi( pMan, pObj, i )
        pObj->pData = Abc_NtkCi(pNtkNew, i);
    // rebuild the AIG
    vNodes = Aig_ManDfs( pMan, 1 );
    Vec_PtrForEachEntry( vNodes, pObj, i )
        if ( Aig_ObjIsBuf(pObj) )
            pObj->pData = (Abc_Obj_t *)Aig_ObjChild0Copy(pObj);
        else
            pObj->pData = Abc_AigAnd( pNtkNew->pManFunc, (Abc_Obj_t *)Aig_ObjChild0Copy(pObj), (Abc_Obj_t *)Aig_ObjChild1Copy(pObj) );
    Vec_PtrFree( vNodes );
    // connect the PO nodes
    Aig_ManForEachPo( pMan, pObj, i )
    {
        if ( pMan->nAsserts && i == Aig_ManPoNum(pMan) - pMan->nAsserts )
            break;
        Abc_ObjAddFanin( Abc_NtkCo(pNtkNew, i), (Abc_Obj_t *)Aig_ObjChild0Copy(pObj) );
    }
    // if there are assertions, add them
    if ( pMan->nAsserts > 0 )
        Aig_ManForEachAssert( pMan, pObj, i )
        {
            pObjNew = Abc_NtkCreateAssert(pNtkNew);
            Abc_ObjAssignName( pObjNew, "assert_", Abc_ObjName(pObjNew) );
            Abc_ObjAddFanin( pObjNew, (Abc_Obj_t *)Aig_ObjChild0Copy(pObj) );
        }
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkFromDar(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Converts the network from the AIG manager into ABC.]

  Description [This procedure should be called after seq sweeping, 
  which changes the number of registers.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkFromDarSeqSweep( Abc_Ntk_t * pNtkOld, Aig_Man_t * pMan )
{
    Vec_Ptr_t * vNodes; 
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pObjNew, * pLatch;
    Aig_Obj_t * pObj, * pObjLo, * pObjLi;
    int i, iNodeId, nDigits; 
    assert( pMan->nAsserts == 0 );
//    assert( Aig_ManRegNum(pMan) != Abc_NtkLatchNum(pNtkOld) );
    // perform strashing
    pNtkNew = Abc_NtkStartFromNoLatches( pNtkOld, ABC_NTK_STRASH, ABC_FUNC_AIG );
    // consider the case of target enlargement
    if ( Abc_NtkCiNum(pNtkNew) < Aig_ManPiNum(pMan) - Aig_ManRegNum(pMan) )
    {
        for ( i = Aig_ManPiNum(pMan) - Aig_ManRegNum(pMan) - Abc_NtkCiNum(pNtkNew); i > 0; i-- )
        {
            pObjNew = Abc_NtkCreatePi( pNtkNew );
            Abc_ObjAssignName( pObjNew, Abc_ObjName(pObjNew), NULL );
        }
        Abc_NtkOrderCisCos( pNtkNew );
    }
    assert( Abc_NtkCiNum(pNtkNew) == Aig_ManPiNum(pMan) - Aig_ManRegNum(pMan) );
    assert( Abc_NtkCoNum(pNtkNew) == Aig_ManPoNum(pMan) - Aig_ManRegNum(pMan) );
    // transfer the pointers to the basic nodes
    Aig_ManConst1(pMan)->pData = Abc_AigConst1(pNtkNew);
    Aig_ManForEachPiSeq( pMan, pObj, i )
        pObj->pData = Abc_NtkCi(pNtkNew, i);
    // create as many latches as there are registers in the manager
    Aig_ManForEachLiLoSeq( pMan, pObjLi, pObjLo, i )
    {
        pObjNew = Abc_NtkCreateLatch( pNtkNew );
        pObjLi->pData = Abc_NtkCreateBi( pNtkNew );
        pObjLo->pData = Abc_NtkCreateBo( pNtkNew );
        Abc_ObjAddFanin( pObjNew, pObjLi->pData );
        Abc_ObjAddFanin( pObjLo->pData, pObjNew );
        Abc_LatchSetInit0( pObjNew );
    }
    // rebuild the AIG
    vNodes = Aig_ManDfs( pMan, 1 );
    Vec_PtrForEachEntry( vNodes, pObj, i )
        if ( Aig_ObjIsBuf(pObj) )
            pObj->pData = (Abc_Obj_t *)Aig_ObjChild0Copy(pObj);
        else
            pObj->pData = Abc_AigAnd( pNtkNew->pManFunc, (Abc_Obj_t *)Aig_ObjChild0Copy(pObj), (Abc_Obj_t *)Aig_ObjChild1Copy(pObj) );
    Vec_PtrFree( vNodes );
    // connect the PO nodes
    Aig_ManForEachPo( pMan, pObj, i )
    {
//        if ( pMan->nAsserts && i == Aig_ManPoNum(pMan) - pMan->nAsserts )
//            break;
        iNodeId = Nm_ManFindIdByNameTwoTypes( pNtkNew->pManName, Abc_ObjName(Abc_NtkCo(pNtkNew, i)), ABC_OBJ_PI, ABC_OBJ_BO );
        if ( iNodeId >= 0 )
            pObjNew = Abc_NtkObj( pNtkNew, iNodeId );
        else
            pObjNew = (Abc_Obj_t *)Aig_ObjChild0Copy(pObj);
        Abc_ObjAddFanin( Abc_NtkCo(pNtkNew, i), pObjNew );
    }
    if ( pMan->vFlopNums == NULL )
        Abc_NtkAddDummyBoxNames( pNtkNew );
    else
    {
/*
        {
            int i, k, iFlop, Counter = 0;
            FILE * pFile;
            pFile = fopen( "out.txt", "w" );
            fprintf( pFile, "The total of %d registers were removed (out of %d):\n", 
                Abc_NtkLatchNum(pNtkOld)-Vec_IntSize(pMan->vFlopNums), Abc_NtkLatchNum(pNtkOld) );
            for ( i = 0; i < Abc_NtkLatchNum(pNtkOld); i++ )
            {
                Vec_IntForEachEntry( pMan->vFlopNums, iFlop, k )
                {
                    if ( i == iFlop )
                        break;
                }
                if ( k == Vec_IntSize(pMan->vFlopNums) )
                    fprintf( pFile, "%6d (%6d)  :  %s\n", ++Counter, i, Abc_ObjName( Abc_ObjFanout0(Abc_NtkBox(pNtkOld, i)) ) );
            }
            fclose( pFile );
            //printf( "\n" );
        }
*/
        assert( Abc_NtkBoxNum(pNtkOld) == Abc_NtkLatchNum(pNtkOld) );
        nDigits = Extra_Base10Log( Abc_NtkLatchNum(pNtkNew) );
        Abc_NtkForEachLatch( pNtkNew, pObjNew, i )
        {
            pLatch = Abc_NtkBox( pNtkOld, Vec_IntEntry( pMan->vFlopNums, i ) );
            iNodeId = Nm_ManFindIdByName( pNtkNew->pManName, Abc_ObjName(Abc_ObjFanout0(pLatch)), ABC_OBJ_PO );
            if ( iNodeId >= 0 )
            {
                Abc_ObjAssignName( pObjNew, Abc_ObjNameDummy("l", i, nDigits), NULL );
                Abc_ObjAssignName( Abc_ObjFanin0(pObjNew), Abc_ObjNameDummy("li", i, nDigits), NULL );
                Abc_ObjAssignName( Abc_ObjFanout0(pObjNew), Abc_ObjNameDummy("lo", i, nDigits), NULL );
//printf( "happening   %s -> %s\n", Abc_ObjName(Abc_ObjFanin0(pObjNew)), Abc_ObjName(Abc_ObjFanout0(pObjNew)) );
                continue;
            }
            Abc_ObjAssignName( pObjNew, Abc_ObjName(pLatch), NULL );
            Abc_ObjAssignName( Abc_ObjFanin0(pObjNew),  Abc_ObjName(Abc_ObjFanin0(pLatch)), NULL );
            Abc_ObjAssignName( Abc_ObjFanout0(pObjNew), Abc_ObjName(Abc_ObjFanout0(pLatch)), NULL );
        }
    }
    // if there are assertions, add them
    if ( pMan->nAsserts > 0 )
        Aig_ManForEachAssert( pMan, pObj, i )
        {
            pObjNew = Abc_NtkCreateAssert(pNtkNew);
            Abc_ObjAssignName( pObjNew, "assert_", Abc_ObjName(pObjNew) );
            Abc_ObjAddFanin( pObjNew, (Abc_Obj_t *)Aig_ObjChild0Copy(pObj) );
        }
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkFromDar(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Converts the network from the AIG manager into ABC.]

  Description [This procedure should be called after seq sweeping, 
  which changes the number of registers.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkFromAigPhase( Aig_Man_t * pMan )
{
    Vec_Ptr_t * vNodes; 
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pObjNew;
    Aig_Obj_t * pObj, * pObjLo, * pObjLi;
    int i; 
    assert( pMan->nAsserts == 0 );
    // perform strashing
    pNtkNew = Abc_NtkAlloc( ABC_NTK_STRASH, ABC_FUNC_AIG, 1 );
    Aig_ManConst1(pMan)->pData = Abc_AigConst1(pNtkNew);
    // create PIs
    Aig_ManForEachPiSeq( pMan, pObj, i )
    {
        pObjNew = Abc_NtkCreatePi( pNtkNew );
        Abc_ObjAssignName( pObjNew, Abc_ObjName(pObjNew), NULL );
        pObj->pData = pObjNew;
    }
    // create POs
    Aig_ManForEachPoSeq( pMan, pObj, i )
    {
        pObjNew = Abc_NtkCreatePo( pNtkNew );
        Abc_ObjAssignName( pObjNew, Abc_ObjName(pObjNew), NULL );
        pObj->pData = pObjNew;
    }
    assert( Abc_NtkCiNum(pNtkNew) == Aig_ManPiNum(pMan) - Aig_ManRegNum(pMan) );
    assert( Abc_NtkCoNum(pNtkNew) == Aig_ManPoNum(pMan) - Aig_ManRegNum(pMan) );
    // create as many latches as there are registers in the manager
    Aig_ManForEachLiLoSeq( pMan, pObjLi, pObjLo, i )
    {
        pObjNew = Abc_NtkCreateLatch( pNtkNew );
        pObjLi->pData = Abc_NtkCreateBi( pNtkNew );
        pObjLo->pData = Abc_NtkCreateBo( pNtkNew );
        Abc_ObjAddFanin( pObjNew, pObjLi->pData );
        Abc_ObjAddFanin( pObjLo->pData, pObjNew );
        Abc_LatchSetInit0( pObjNew );
        Abc_ObjAssignName( pObjLi->pData, Abc_ObjName(pObjLi->pData), NULL );
        Abc_ObjAssignName( pObjLo->pData, Abc_ObjName(pObjLo->pData), NULL );
    }
    // rebuild the AIG
    vNodes = Aig_ManDfs( pMan, 1 );
    Vec_PtrForEachEntry( vNodes, pObj, i )
        if ( Aig_ObjIsBuf(pObj) )
            pObj->pData = (Abc_Obj_t *)Aig_ObjChild0Copy(pObj);
        else
            pObj->pData = Abc_AigAnd( pNtkNew->pManFunc, (Abc_Obj_t *)Aig_ObjChild0Copy(pObj), (Abc_Obj_t *)Aig_ObjChild1Copy(pObj) );
    Vec_PtrFree( vNodes );
    // connect the PO nodes
    Aig_ManForEachPo( pMan, pObj, i )
    {
        pObjNew = (Abc_Obj_t *)Aig_ObjChild0Copy(pObj);
        Abc_ObjAddFanin( Abc_NtkCo(pNtkNew, i), pObjNew );
    }
    // check the resulting AIG
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkFromAigPhase(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Converts the network from the AIG manager into ABC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkFromDarChoices( Abc_Ntk_t * pNtkOld, Aig_Man_t * pMan )
{
    Vec_Ptr_t * vNodes;
    Abc_Ntk_t * pNtkNew;
    Aig_Obj_t * pObj, * pTemp;
    int i;
    assert( pMan->pEquivs != NULL );
    assert( Aig_ManBufNum(pMan) == 0 );
    // perform strashing
    pNtkNew = Abc_NtkStartFrom( pNtkOld, ABC_NTK_STRASH, ABC_FUNC_AIG );
    // transfer the pointers to the basic nodes
    Aig_ManConst1(pMan)->pData = Abc_AigConst1(pNtkNew);
    Aig_ManForEachPi( pMan, pObj, i )
        pObj->pData = Abc_NtkCi(pNtkNew, i);

    // rebuild the AIG
    vNodes = Aig_ManDfsChoices( pMan );
    Vec_PtrForEachEntry( vNodes, pObj, i )
    {
        pObj->pData = Abc_AigAnd( pNtkNew->pManFunc, (Abc_Obj_t *)Aig_ObjChild0Copy(pObj), (Abc_Obj_t *)Aig_ObjChild1Copy(pObj) );
        if ( (pTemp = Aig_ObjEquiv(pMan, pObj)) )
        {
            Abc_Obj_t * pAbcRepr, * pAbcObj;
            assert( pTemp->pData != NULL );
            pAbcRepr = pObj->pData;
            pAbcObj  = pTemp->pData;
            pAbcObj->pData  = pAbcRepr->pData;
            pAbcRepr->pData = pAbcObj;
        }
    }
//printf( "Total = %d.  Collected = %d.\n", Aig_ManNodeNum(pMan), Vec_PtrSize(vNodes) );
    Vec_PtrFree( vNodes );
    // connect the PO nodes
    Aig_ManForEachPo( pMan, pObj, i )
        Abc_ObjAddFanin( Abc_NtkCo(pNtkNew, i), (Abc_Obj_t *)Aig_ObjChild0Copy(pObj) );
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkFromDar(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Converts the network from the AIG manager into ABC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkFromDarSeq( Abc_Ntk_t * pNtkOld, Aig_Man_t * pMan )
{
    Vec_Ptr_t * vNodes;
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pObjNew, * pFaninNew, * pFaninNew0, * pFaninNew1;
    Aig_Obj_t * pObj;
    int i;
//    assert( Aig_ManLatchNum(pMan) > 0 );
    // perform strashing
    pNtkNew = Abc_NtkStartFromNoLatches( pNtkOld, ABC_NTK_STRASH, ABC_FUNC_AIG );
    // transfer the pointers to the basic nodes
    Aig_ManConst1(pMan)->pData = Abc_AigConst1(pNtkNew);
    Aig_ManForEachPi( pMan, pObj, i )
        pObj->pData = Abc_NtkPi(pNtkNew, i);
    // create latches of the new network
    Aig_ManForEachObj( pMan, pObj, i )
    {
        pObjNew = Abc_NtkCreateLatch( pNtkNew );
        pFaninNew0 = Abc_NtkCreateBi( pNtkNew );
        pFaninNew1 = Abc_NtkCreateBo( pNtkNew );
        Abc_ObjAddFanin( pObjNew, pFaninNew0 );
        Abc_ObjAddFanin( pFaninNew1, pObjNew );
        Abc_LatchSetInit0( pObjNew );
        pObj->pData = Abc_ObjFanout0( pObjNew );
    }
    Abc_NtkAddDummyBoxNames( pNtkNew );
    // rebuild the AIG
    vNodes = Aig_ManDfs( pMan, 1 );
    Vec_PtrForEachEntry( vNodes, pObj, i )
    {
        // add the first fanin
        pObj->pData = pFaninNew0 = (Abc_Obj_t *)Aig_ObjChild0Copy(pObj);
        if ( Aig_ObjIsBuf(pObj) )
            continue;
        // add the second fanin
        pFaninNew1 = (Abc_Obj_t *)Aig_ObjChild1Copy(pObj);
        // create the new node
        if ( Aig_ObjIsExor(pObj) )
            pObj->pData = pObjNew = Abc_AigXor( pNtkNew->pManFunc, pFaninNew0, pFaninNew1 );
        else
            pObj->pData = pObjNew = Abc_AigAnd( pNtkNew->pManFunc, pFaninNew0, pFaninNew1 );
    }
    Vec_PtrFree( vNodes );
    // connect the PO nodes
    Aig_ManForEachPo( pMan, pObj, i )
    {
        pFaninNew = (Abc_Obj_t *)Aig_ObjChild0Copy( pObj );
        Abc_ObjAddFanin( Abc_NtkPo(pNtkNew, i), pFaninNew );
    }
    // connect the latches
    Aig_ManForEachObj( pMan, pObj, i )
    {
        pFaninNew = (Abc_Obj_t *)Aig_ObjChild0Copy( pObj );
        Abc_ObjAddFanin( Abc_ObjFanin0(Abc_ObjFanin0(pObj->pData)), pFaninNew );
    }
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkFromIvySeq(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Collect latch values.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_NtkGetLatchValues( Abc_Ntk_t * pNtk )
{
    Vec_Int_t * vInits;
    Abc_Obj_t * pLatch;
    int i;
    vInits = Vec_IntAlloc( Abc_NtkLatchNum(pNtk) );
    Abc_NtkForEachLatch( pNtk, pLatch, i )
    {
        if ( Abc_LatchIsInit0(pLatch) )
            Vec_IntPush( vInits, 0 );
        else if ( Abc_LatchIsInit1(pLatch) )
            Vec_IntPush( vInits, 1 );
        else if ( Abc_LatchIsInitDc(pLatch) )
            Vec_IntPush( vInits, 2 );
        else
            assert( 0 );
    }
    return vInits;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDar( Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkAig = NULL;
    Aig_Man_t * pMan;
    extern void Fra_ManPartitionTest( Aig_Man_t * p, int nComLim );

    assert( Abc_NtkIsStrash(pNtk) );
    // convert to the AIG manager
    pMan = Abc_NtkToDar( pNtk, 0, 0 );
    if ( pMan == NULL )
        return NULL;

    // perform computation
//    Fra_ManPartitionTest( pMan, 4 );
    pNtkAig = Abc_NtkFromDar( pNtk, pMan );
    Aig_ManStop( pMan );

    // make sure everything is okay
    if ( pNtkAig && !Abc_NtkCheck( pNtkAig ) )
    {
        printf( "Abc_NtkDar: The network check has failed.\n" );
        Abc_NtkDelete( pNtkAig );
        return NULL;
    }
    return pNtkAig;
}


/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarFraig( Abc_Ntk_t * pNtk, int nConfLimit, int fDoSparse, int fProve, int fTransfer, int fSpeculate, int fChoicing, int fVerbose )
{
    Fra_Par_t Pars, * pPars = &Pars; 
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan, * pTemp;
    pMan = Abc_NtkToDar( pNtk, 0, 0 );
    if ( pMan == NULL )
        return NULL;
    Fra_ParamsDefault( pPars );
    pPars->nBTLimitNode = nConfLimit;
    pPars->fChoicing    = fChoicing;
    pPars->fDoSparse    = fDoSparse;
    pPars->fSpeculate   = fSpeculate;
    pPars->fProve       = fProve;
    pPars->fVerbose     = fVerbose;
    pMan = Fra_FraigPerform( pTemp = pMan, pPars );
    if ( fChoicing )
        pNtkAig = Abc_NtkFromDarChoices( pNtk, pMan );
    else
        pNtkAig = Abc_NtkFromDar( pNtk, pMan );
    Aig_ManStop( pTemp );
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarFraigPart( Abc_Ntk_t * pNtk, int nPartSize, int nConfLimit, int nLevelMax, int fVerbose )
{
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan, * pTemp;
    pMan = Abc_NtkToDar( pNtk, 0, 0 );
    if ( pMan == NULL )
        return NULL;
    pMan = Aig_ManFraigPartitioned( pTemp = pMan, nPartSize, nConfLimit, nLevelMax, fVerbose );
    Aig_ManStop( pTemp );
    pNtkAig = Abc_NtkFromDar( pNtk, pMan );
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkCSweep( Abc_Ntk_t * pNtk, int nCutsMax, int nLeafMax, int fVerbose )
{
    extern Aig_Man_t * Csw_Sweep( Aig_Man_t * pAig, int nCutsMax, int nLeafMax, int fVerbose );
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan, * pTemp;
    pMan = Abc_NtkToDar( pNtk, 0, 0 );
    if ( pMan == NULL )
        return NULL;
    pMan = Csw_Sweep( pTemp = pMan, nCutsMax, nLeafMax, fVerbose );
    pNtkAig = Abc_NtkFromDar( pNtk, pMan );
    Aig_ManStop( pTemp );
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDRewrite( Abc_Ntk_t * pNtk, Dar_RwrPar_t * pPars )
{
    Aig_Man_t * pMan, * pTemp;
    Abc_Ntk_t * pNtkAig;
    int clk;
    assert( Abc_NtkIsStrash(pNtk) );
    pMan = Abc_NtkToDar( pNtk, 0, 0 );
    if ( pMan == NULL )
        return NULL;
//    Aig_ManPrintStats( pMan );
/*
//    Aig_ManSupports( pMan );
    {
        Vec_Vec_t * vParts;
        vParts = Aig_ManPartitionSmart( pMan, 50, 1, NULL );
        Vec_VecFree( vParts );
    }
*/
    Dar_ManRewrite( pMan, pPars );
//    pMan = Dar_ManBalance( pTemp = pMan, pPars->fUpdateLevel );
//    Aig_ManStop( pTemp );

clk = clock();
    pMan = Aig_ManDupDfs( pTemp = pMan ); 
    Aig_ManStop( pTemp );
//PRT( "time", clock() - clk );

//    Aig_ManPrintStats( pMan );
    pNtkAig = Abc_NtkFromDar( pNtk, pMan );
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDRefactor( Abc_Ntk_t * pNtk, Dar_RefPar_t * pPars )
{
    Aig_Man_t * pMan, * pTemp;
    Abc_Ntk_t * pNtkAig;
    int clk;
    assert( Abc_NtkIsStrash(pNtk) );
    pMan = Abc_NtkToDar( pNtk, 0, 0 );
    if ( pMan == NULL )
        return NULL;
//    Aig_ManPrintStats( pMan );

    Dar_ManRefactor( pMan, pPars );
//    pMan = Dar_ManBalance( pTemp = pMan, pPars->fUpdateLevel );
//    Aig_ManStop( pTemp );

clk = clock();
    pMan = Aig_ManDupDfs( pTemp = pMan ); 
    Aig_ManStop( pTemp );
//PRT( "time", clock() - clk );

//    Aig_ManPrintStats( pMan );
    pNtkAig = Abc_NtkFromDar( pNtk, pMan );
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDCompress2( Abc_Ntk_t * pNtk, int fBalance, int fUpdateLevel, int fFanout, int fVerbose )
{
    Aig_Man_t * pMan, * pTemp;
    Abc_Ntk_t * pNtkAig;
    int clk;
    assert( Abc_NtkIsStrash(pNtk) );
    pMan = Abc_NtkToDar( pNtk, 0, 0 );
    if ( pMan == NULL )
        return NULL;
//    Aig_ManPrintStats( pMan );

clk = clock();
    pMan = Dar_ManCompress2( pTemp = pMan, fBalance, fUpdateLevel, fFanout, fVerbose ); 
    Aig_ManStop( pTemp );
//PRT( "time", clock() - clk );

//    Aig_ManPrintStats( pMan );
    pNtkAig = Abc_NtkFromDar( pNtk, pMan );
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDChoice( Abc_Ntk_t * pNtk, int fBalance, int fUpdateLevel, int fConstruct, int nConfMax, int nLevelMax, int fVerbose )
{
    Aig_Man_t * pMan, * pTemp;
    Abc_Ntk_t * pNtkAig;
    assert( Abc_NtkIsStrash(pNtk) );
    pMan = Abc_NtkToDar( pNtk, 0, 0 );
    if ( pMan == NULL )
        return NULL;
    pMan = Dar_ManChoice( pTemp = pMan, fBalance, fUpdateLevel, fConstruct, nConfMax, nLevelMax, fVerbose );
    Aig_ManStop( pTemp );
    pNtkAig = Abc_NtkFromDarChoices( pNtk, pMan );
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDrwsat( Abc_Ntk_t * pNtk, int fBalance, int fVerbose )
{
    Aig_Man_t * pMan, * pTemp;
    Abc_Ntk_t * pNtkAig;
    int clk;
    assert( Abc_NtkIsStrash(pNtk) );
    pMan = Abc_NtkToDar( pNtk, 0, 0 );
    if ( pMan == NULL )
        return NULL;
//    Aig_ManPrintStats( pMan );

clk = clock();
    pMan = Dar_ManRwsat( pTemp = pMan, fBalance, fVerbose ); 
    Aig_ManStop( pTemp );
//PRT( "time", clock() - clk );

//    Aig_ManPrintStats( pMan );
    pNtkAig = Abc_NtkFromDar( pNtk, pMan );
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkConstructFromCnf( Abc_Ntk_t * pNtk, Cnf_Man_t * p, Vec_Ptr_t * vMapped )
{
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pNode, * pNodeNew;
    Aig_Obj_t * pObj, * pLeaf;
    Cnf_Cut_t * pCut;
    Vec_Int_t * vCover;
    unsigned uTruth;
    int i, k, nDupGates;
    // create the new network
    pNtkNew = Abc_NtkStartFrom( pNtk, ABC_NTK_LOGIC, ABC_FUNC_SOP );
    // make the mapper point to the new network
    Aig_ManConst1(p->pManAig)->pData = Abc_NtkCreateNodeConst1(pNtkNew);
    Abc_NtkForEachCi( pNtk, pNode, i )
        Aig_ManPi(p->pManAig, i)->pData = pNode->pCopy;
    // process the nodes in topological order
    vCover = Vec_IntAlloc( 1 << 16 );
    Vec_PtrForEachEntry( vMapped, pObj, i )
    {
        // create new node
        pNodeNew = Abc_NtkCreateNode( pNtkNew );
        // add fanins according to the cut
        pCut = pObj->pData;
        Cnf_CutForEachLeaf( p->pManAig, pCut, pLeaf, k )
            Abc_ObjAddFanin( pNodeNew, pLeaf->pData );
        // add logic function
        if ( pCut->nFanins < 5 )
        {
            uTruth = 0xFFFF & *Cnf_CutTruth(pCut);
            Cnf_SopConvertToVector( p->pSops[uTruth], p->pSopSizes[uTruth], vCover );
            pNodeNew->pData = Abc_SopCreateFromIsop( pNtkNew->pManFunc, pCut->nFanins, vCover );
        }
        else
            pNodeNew->pData = Abc_SopCreateFromIsop( pNtkNew->pManFunc, pCut->nFanins, pCut->vIsop[1] );
        // save the node
        pObj->pData = pNodeNew;
    }
    Vec_IntFree( vCover );
    // add the CO drivers
    Abc_NtkForEachCo( pNtk, pNode, i )
    {
        pObj = Aig_ManPo(p->pManAig, i);
        pNodeNew = Abc_ObjNotCond( Aig_ObjFanin0(pObj)->pData, Aig_ObjFaninC0(pObj) );
        Abc_ObjAddFanin( pNode->pCopy, pNodeNew );
    }

    // remove the constant node if not used
    pNodeNew = (Abc_Obj_t *)Aig_ManConst1(p->pManAig)->pData;
    if ( Abc_ObjFanoutNum(pNodeNew) == 0 )
        Abc_NtkDeleteObj( pNodeNew );
    // minimize the node
//    Abc_NtkSweep( pNtkNew, 0 );
    // decouple the PO driver nodes to reduce the number of levels
    nDupGates = Abc_NtkLogicMakeSimpleCos( pNtkNew, 1 );
//    if ( nDupGates && If_ManReadVerbose(pIfMan) )
//        printf( "Duplicated %d gates to decouple the CO drivers.\n", nDupGates );
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkConstructFromCnf(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarToCnf( Abc_Ntk_t * pNtk, char * pFileName )
{
    Vec_Ptr_t * vMapped;
    Aig_Man_t * pMan;
    Cnf_Man_t * pManCnf;
    Cnf_Dat_t * pCnf;
    Abc_Ntk_t * pNtkNew = NULL;
    assert( Abc_NtkIsStrash(pNtk) );

    // convert to the AIG manager
    pMan = Abc_NtkToDar( pNtk, 0, 0 );
    if ( pMan == NULL )
        return NULL;
    if ( !Aig_ManCheck( pMan ) )
    {
        printf( "Abc_NtkDarToCnf: AIG check has failed.\n" );
        Aig_ManStop( pMan );
        return NULL;
    }
    // perform balance
    Aig_ManPrintStats( pMan );

    // derive CNF
    pCnf = Cnf_Derive( pMan, 0 );
    pManCnf = Cnf_ManRead();

    // write the network for verification
    vMapped = Cnf_ManScanMapping( pManCnf, 1, 0 );
    pNtkNew = Abc_NtkConstructFromCnf( pNtk, pManCnf, vMapped );
    Vec_PtrFree( vMapped );

    // write CNF into a file
    Cnf_DataWriteIntoFile( pCnf, pFileName, 0 );
    Cnf_DataFree( pCnf );
    Cnf_ClearMemory();

    Aig_ManStop( pMan );
    return pNtkNew;
}


/**Function*************************************************************

  Synopsis    [Solves combinational miter using a SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkDSat( Abc_Ntk_t * pNtk, sint64 nConfLimit, sint64 nInsLimit, int fVerbose )
{
    Aig_Man_t * pMan;
    int RetValue;//, clk = clock();
    assert( Abc_NtkIsStrash(pNtk) );
    assert( Abc_NtkLatchNum(pNtk) == 0 );
    assert( Abc_NtkPoNum(pNtk) == 1 );
    pMan = Abc_NtkToDar( pNtk, 0, 0 );
    RetValue = Fra_FraigSat( pMan, nConfLimit, nInsLimit, fVerbose ); 
    pNtk->pModel = pMan->pData, pMan->pData = NULL;
    Aig_ManStop( pMan );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkDarCec( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int fPartition, int fVerbose )
{
    Aig_Man_t * pMan, * pMan1, * pMan2;
    Abc_Ntk_t * pMiter;
    int RetValue, clkTotal = clock();

    // cannot partition if it is already a miter
    if ( pNtk2 == NULL && fPartition == 1 )
    {
        printf( "Abc_NtkDarCec(): Switching to non-partitioned CEC for the miter.\n" );
        fPartition = 0;
    }

    // if partitioning is selected, call partitioned CEC
    if ( fPartition )
    {
        pMan1 = Abc_NtkToDar( pNtk1, 0, 0 );
        pMan2 = Abc_NtkToDar( pNtk2, 0, 0 );
        RetValue = Fra_FraigCecPartitioned( pMan1, pMan2, 100, 1, fVerbose );
        Aig_ManStop( pMan1 );
        Aig_ManStop( pMan2 );
        goto finish;
    }

    if ( pNtk2 != NULL )
    {
        // get the miter of the two networks
        pMiter = Abc_NtkMiter( pNtk1, pNtk2, 0, 0, 0 );
        if ( pMiter == NULL )
        {
            printf( "Miter computation has failed.\n" );
            return 0;
        }
    }
    else
    {
        pMiter = Abc_NtkDup( pNtk1 );
    }
    RetValue = Abc_NtkMiterIsConstant( pMiter );
    if ( RetValue == 0 )
    {
//        extern void Abc_NtkVerifyReportErrorSeq( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int * pModel, int nFrames );
        printf( "Networks are NOT EQUIVALENT after structural hashing.\n" );
        // report the error
        if ( pNtk2 == NULL )
            pNtk1->pModel = Abc_NtkVerifyGetCleanModel( pNtk1, 1 );
//        pMiter->pModel = Abc_NtkVerifyGetCleanModel( pMiter, nFrames );
//        Abc_NtkVerifyReportErrorSeq( pNtk1, pNtk2, pMiter->pModel, nFrames );
//        FREE( pMiter->pModel );
        Abc_NtkDelete( pMiter );
        return 0;
    }
    if ( RetValue == 1 )
    {
        Abc_NtkDelete( pMiter );
        printf( "Networks are equivalent after structural hashing.\n" );
        return 1;
    }

    // derive the AIG manager
    pMan = Abc_NtkToDar( pMiter, 0, 0 );
    Abc_NtkDelete( pMiter );
    if ( pMan == NULL )
    {
        printf( "Converting miter into AIG has failed.\n" );
        return -1;
    }
    // perform verification
    RetValue = Fra_FraigCec( &pMan, fVerbose );
    // transfer model if given
    if ( pNtk2 == NULL )
        pNtk1->pModel = pMan->pData, pMan->pData = NULL;
    Aig_ManStop( pMan );

finish:
    // report the miter
    if ( RetValue == 1 )
    {
        printf( "Networks are equivalent.   " );
PRT( "Time", clock() - clkTotal );
    }
    else if ( RetValue == 0 )
    {
        printf( "Networks are NOT EQUIVALENT.   " );
PRT( "Time", clock() - clkTotal );
    }
    else
    {
        printf( "Networks are UNDECIDED.   " );
PRT( "Time", clock() - clkTotal );
    }
    fflush( stdout );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarSeqSweep( Abc_Ntk_t * pNtk, Fra_Ssw_t * pPars )
{
    Fraig_Params_t Params;
    Abc_Ntk_t * pNtkAig = NULL, * pNtkFraig;
    Aig_Man_t * pMan, * pTemp;
    int clk = clock();

    // preprocess the miter by fraiging it
    // (note that for each functional class, fraiging leaves one representative;
    // so fraiging does not reduce the number of functions represented by nodes
    Fraig_ParamsSetDefault( &Params );
    Params.nBTLimit = 100000;
    if ( pPars->fFraiging && pPars->nPartSize == 0 )
    {
        pNtkFraig = Abc_NtkFraig( pNtk, &Params, 0, 0 );
if ( pPars->fVerbose ) 
{
PRT( "Initial fraiging time", clock() - clk );
}
    }
    else
        pNtkFraig = Abc_NtkDup( pNtk );

    pMan = Abc_NtkToDar( pNtkFraig, 0, 1 );
    Abc_NtkDelete( pNtkFraig );
    if ( pMan == NULL )
        return NULL;

//    pPars->TimeLimit = 5.0;
    pMan = Fra_FraigInduction( pTemp = pMan, pPars );
    Aig_ManStop( pTemp );
    if ( pMan )
    {
        if ( Aig_ManRegNum(pMan) < Abc_NtkLatchNum(pNtk) )
            pNtkAig = Abc_NtkFromDarSeqSweep( pNtk, pMan );
        else
        {
            Abc_Obj_t * pObj;
            int i;
            pNtkAig = Abc_NtkFromDar( pNtk, pMan );
            Abc_NtkForEachLatch( pNtkAig, pObj, i )
                Abc_LatchSetInit0( pObj );
        }
        Aig_ManStop( pMan );
    }
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Computes latch correspondence.]

  Description [] 
               
  SideEffects []

  SeeAlso     []
 
***********************************************************************/
Abc_Ntk_t * Abc_NtkDarLcorr( Abc_Ntk_t * pNtk, int nFramesP, int nConfMax, int fVerbose )
{
    Aig_Man_t * pMan, * pTemp;
    Abc_Ntk_t * pNtkAig = NULL;
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return NULL;
    pMan = Fra_FraigLatchCorrespondence( pTemp = pMan, nFramesP, nConfMax, 0, fVerbose, NULL, 0.0 );
    Aig_ManStop( pTemp );
    if ( pMan )
    {
        if ( Aig_ManRegNum(pMan) < Abc_NtkLatchNum(pNtk) )
            pNtkAig = Abc_NtkFromDarSeqSweep( pNtk, pMan );
        else
        {
            Abc_Obj_t * pObj;
            int i;
            pNtkAig = Abc_NtkFromDar( pNtk, pMan );
            Abc_NtkForEachLatch( pNtkAig, pObj, i )
                Abc_LatchSetInit0( pObj );
        }
        Aig_ManStop( pMan );
    }
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkDarBmc( Abc_Ntk_t * pNtk, int nFrames, int nSizeMax, int nBTLimit, int fRewrite, int fNewAlgo, int fVerbose )
{
    Aig_Man_t * pMan;
    int RetValue = -1, clk = clock();
    // derive the AIG manager
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
    {
        printf( "Converting miter into AIG has failed.\n" );
        return RetValue;
    }
    assert( pMan->nRegs > 0 );
    pMan->nTruePis = Aig_ManPiNum(pMan) - Aig_ManRegNum(pMan);
    pMan->nTruePos = Aig_ManPoNum(pMan) - Aig_ManRegNum(pMan);
    // perform verification
    if ( fNewAlgo )
    {
        int iFrame;
        RetValue = Saig_ManBmcSimple( pMan, nFrames, nSizeMax, nBTLimit, fRewrite, fVerbose, &iFrame );
        pNtk->pSeqModel = pMan->pSeqModel; pMan->pSeqModel = NULL;
        if ( RetValue == 1 )
            printf( "No output was asserted in %d frames. ", nFrames );
        else if ( RetValue == -1 )
            printf( "No output was asserted in %d frames. Reached conflict limit (%d). ", iFrame, nBTLimit );
        else // if ( RetValue == 0 )
        {
            Fra_Cex_t * pCex = pNtk->pSeqModel;
            printf( "Output %d was asserted in frame %d (use \"write_counter\" to dump the trace). ", pCex->iPo, pCex->iFrame );
        }
    }
    else
    {
        Fra_BmcPerformSimple( pMan, nFrames, nBTLimit, fRewrite, fVerbose );
        pNtk->pSeqModel = pMan->pSeqModel; pMan->pSeqModel = NULL;
        if ( pNtk->pSeqModel )
        {
            Fra_Cex_t * pCex = pNtk->pSeqModel;
            printf( "Output %d was asserted in frame %d (use \"write_counter\" to dump the trace). ", pCex->iPo, pCex->iFrame );
            RetValue = 0;
        }
        else
        {
            printf( "No output was asserted in %d frames. ", nFrames );
            RetValue = 1;
        }
    }
PRT( "Time", clock() - clk );
    Aig_ManStop( pMan );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkDarBmcInter( Abc_Ntk_t * pNtk, int nConfLimit, int fRewrite, int fTransLoop, int fVerbose )
{
    Aig_Man_t * pMan;
    int RetValue, Depth, clk = clock();
    // derive the AIG manager
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
    {
        printf( "Converting miter into AIG has failed.\n" );
        return -1;
    }
    assert( pMan->nRegs > 0 );
    pMan->nTruePis = Aig_ManPiNum(pMan) - Aig_ManRegNum(pMan);
    pMan->nTruePos = Aig_ManPoNum(pMan) - Aig_ManRegNum(pMan);
    RetValue = Saig_Interpolate( pMan, nConfLimit, fRewrite, fTransLoop, fVerbose, &Depth );
    if ( RetValue == 1 )
        printf( "Property proved.  " );
    else if ( RetValue == 0 )
        printf( "Property DISPROVED with counter-example at depth %d.  ", Depth );
    else if ( RetValue == -1 )
        printf( "Property UNDECIDED.  " );
    else
        assert( 0 );
PRT( "Time", clock() - clk );
    Aig_ManStop( pMan );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkDarProve( Abc_Ntk_t * pNtk, int fTryComb, int fTryBmc, int nFrames, int fPhaseAbstract, int fRetimeFirst, int fRetimeRegs, int fFraiging, int fVerbose, int fVeryVerbose, int TimeLimit )
{
    Aig_Man_t * pMan;
    int RetValue;
    if ( fTryComb )
    {
        Prove_Params_t Params, * pParams = &Params;
        Abc_Ntk_t * pNtkComb;
        int RetValue, clk = clock();
        // create combinational network
        pNtkComb = Abc_NtkDup( pNtk );
        Abc_NtkMakeComb( pNtkComb, 1 );
        // solve it using combinational equivalence checking
        Prove_ParamsSetDefault( pParams );
        RetValue = Abc_NtkIvyProve( &pNtkComb, pParams );
        // transfer model if given
        pNtk->pModel = pNtkComb->pModel; pNtkComb->pModel = NULL;
        Abc_NtkDelete( pNtkComb );
        // return the result, if solved
        if ( RetValue == 1 )
        {
            printf( "Networks are equivalent after CEC.   " );
            PRT( "Time", clock() - clk );
            return RetValue;
        }
    }
    if ( fTryBmc )
    {
        RetValue = Abc_NtkDarBmc( pNtk, 20, 100000, 1000, 0, 1, 0 );
        if ( RetValue == 0 )
            return RetValue;
    }
    // derive the AIG manager
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
    {
        printf( "Converting miter into AIG has failed.\n" );
        return -1;
    }
    assert( pMan->nRegs > 0 );
    // perform verification
    RetValue = Fra_FraigSec( pMan, nFrames, fPhaseAbstract, fRetimeFirst, fRetimeRegs, fFraiging, fVerbose, fVeryVerbose, TimeLimit );
    pNtk->pSeqModel = pMan->pSeqModel; pMan->pSeqModel = NULL;
    if ( pNtk->pSeqModel )
    {
        Fra_Cex_t * pCex = pNtk->pSeqModel;
        printf( "Output %d was asserted in frame %d (use \"write_counter\" to dump the trace).\n", pCex->iPo, pCex->iFrame );
    }
    Aig_ManStop( pMan );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkDarSec( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nFrames, int fPhaseAbstract, int fRetimeFirst, int fRetimeRegs, int fFraiging, int fVerbose, int fVeryVerbose )
{
//    Fraig_Params_t Params;
    Aig_Man_t * pMan;
    Abc_Ntk_t * pMiter;//, * pTemp;
    int RetValue;
 
    // get the miter of the two networks
    pMiter = Abc_NtkMiter( pNtk1, pNtk2, 0, 0, 0 );
    if ( pMiter == NULL )
    {
        printf( "Miter computation has failed.\n" );
        return 0;
    }
    RetValue = Abc_NtkMiterIsConstant( pMiter );
    if ( RetValue == 0 )
    {
        extern void Abc_NtkVerifyReportErrorSeq( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int * pModel, int nFrames );
        printf( "Networks are NOT EQUIVALENT after structural hashing.\n" );
        // report the error
        pMiter->pModel = Abc_NtkVerifyGetCleanModel( pMiter, nFrames );
        Abc_NtkVerifyReportErrorSeq( pNtk1, pNtk2, pMiter->pModel, nFrames );
        FREE( pMiter->pModel );
        Abc_NtkDelete( pMiter );
        return 0;
    }
    if ( RetValue == 1 )
    {
        Abc_NtkDelete( pMiter );
        printf( "Networks are equivalent after structural hashing.\n" );
        return 1;
    }

    // commented out because something became non-inductive
/*
    // preprocess the miter by fraiging it
    // (note that for each functional class, fraiging leaves one representative;
    // so fraiging does not reduce the number of functions represented by nodes
    Fraig_ParamsSetDefault( &Params );
    Params.nBTLimit = 100000;
    pMiter = Abc_NtkFraig( pTemp = pMiter, &Params, 0, 0 );
    Abc_NtkDelete( pTemp );
    RetValue = Abc_NtkMiterIsConstant( pMiter );
    if ( RetValue == 0 )
    {
        extern void Abc_NtkVerifyReportErrorSeq( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int * pModel, int nFrames );
        printf( "Networks are NOT EQUIVALENT after structural hashing.\n" );
        // report the error
        pMiter->pModel = Abc_NtkVerifyGetCleanModel( pMiter, nFrames );
        Abc_NtkVerifyReportErrorSeq( pNtk1, pNtk2, pMiter->pModel, nFrames );
        FREE( pMiter->pModel );
        Abc_NtkDelete( pMiter );
        return 0;
    }
    if ( RetValue == 1 )
    {
        Abc_NtkDelete( pMiter );
        printf( "Networks are equivalent after structural hashing.\n" );
        return 1;
    }
*/
    // derive the AIG manager
    pMan = Abc_NtkToDar( pMiter, 0, 1 );
    Abc_NtkDelete( pMiter );
    if ( pMan == NULL )
    {
        printf( "Converting miter into AIG has failed.\n" );
        return -1;
    }
    assert( pMan->nRegs > 0 );

    // perform verification
    RetValue = Fra_FraigSec( pMan, nFrames, fPhaseAbstract, fRetimeFirst, fRetimeRegs, fFraiging, fVerbose, fVeryVerbose, 0 );
    Aig_ManStop( pMan );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarLatchSweep( Abc_Ntk_t * pNtk, int fLatchConst, int fLatchEqual, int fVerbose )
{
    extern void Aig_ManPrintControlFanouts( Aig_Man_t * p );
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan, * pTemp;
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return NULL;
//    Aig_ManSeqCleanup( pMan );
//    if ( fLatchConst && pMan->nRegs )
//        pMan = Aig_ManConstReduce( pMan, fVerbose );
//    if ( fLatchEqual && pMan->nRegs )
//        pMan = Aig_ManReduceLaches( pMan, fVerbose );
    if ( pMan->vFlopNums )
        Vec_IntFree( pMan->vFlopNums );
    pMan->vFlopNums = NULL;
    pMan = Aig_ManScl( pTemp = pMan, fLatchConst, fLatchEqual, fVerbose );
    Aig_ManStop( pTemp );
    pNtkAig = Abc_NtkFromDarSeqSweep( pNtk, pMan );
//Aig_ManPrintControlFanouts( pMan );
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarRetime( Abc_Ntk_t * pNtk, int nStepsMax, int fVerbose )
{
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan, * pTemp;
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return NULL;
//    Aig_ManReduceLachesCount( pMan );
    if ( pMan->vFlopNums )
        Vec_IntFree( pMan->vFlopNums ); 
    pMan->vFlopNums = NULL;

    pMan = Rtm_ManRetime( pTemp = pMan, 1, nStepsMax, fVerbose );
    Aig_ManStop( pTemp );

//    pMan = Aig_ManReduceLaches( pMan, 1 );
//    pMan = Aig_ManConstReduce( pMan, 1 );

    pNtkAig = Abc_NtkFromDarSeqSweep( pNtk, pMan );
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarRetimeF( Abc_Ntk_t * pNtk, int nStepsMax, int fVerbose )
{
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan, * pTemp;
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return NULL;
//    Aig_ManReduceLachesCount( pMan );
    if ( pMan->vFlopNums )
        Vec_IntFree( pMan->vFlopNums ); 
    pMan->vFlopNums = NULL;

    pMan = Aig_ManRetimeFrontier( pTemp = pMan, nStepsMax );
    Aig_ManStop( pTemp );

//    pMan = Aig_ManReduceLaches( pMan, 1 );
//    pMan = Aig_ManConstReduce( pMan, 1 );

    pNtkAig = Abc_NtkFromDarSeqSweep( pNtk, pMan );
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarRetimeMostFwd( Abc_Ntk_t * pNtk, int nMaxIters, int fVerbose )
{
    extern Aig_Man_t * Saig_ManRetimeForward( Aig_Man_t * p, int nIters, int fVerbose );

    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan, * pTemp;
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return NULL;
//    Aig_ManReduceLachesCount( pMan );
    if ( pMan->vFlopNums )
        Vec_IntFree( pMan->vFlopNums ); 
    pMan->vFlopNums = NULL;

    pMan->nTruePis = Aig_ManPiNum(pMan) - Aig_ManRegNum(pMan); 
    pMan->nTruePos = Aig_ManPoNum(pMan) - Aig_ManRegNum(pMan); 

    pMan = Saig_ManRetimeForward( pTemp = pMan, nMaxIters, fVerbose );
    Aig_ManStop( pTemp );

//    pMan = Aig_ManReduceLaches( pMan, 1 );
//    pMan = Aig_ManConstReduce( pMan, 1 );

    pNtkAig = Abc_NtkFromDarSeqSweep( pNtk, pMan );
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarRetimeMinArea( Abc_Ntk_t * pNtk, int nMaxIters, int fForwardOnly, int fBackwardOnly, int fInitial, int fVerbose )
{
    extern Aig_Man_t * Saig_ManRetimeMinArea( Aig_Man_t * p, int nMaxIters, int fForwardOnly, int fBackwardOnly, int fInitial, int fVerbose );
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan, * pTemp;
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return NULL;
    if ( pMan->vFlopNums )
        Vec_IntFree( pMan->vFlopNums ); 
    pMan->vFlopNums = NULL;

    pMan->nTruePis = Aig_ManPiNum(pMan) - Aig_ManRegNum(pMan); 
    pMan->nTruePos = Aig_ManPoNum(pMan) - Aig_ManRegNum(pMan); 

    pMan = Saig_ManRetimeMinArea( pTemp = pMan, nMaxIters, fForwardOnly, fBackwardOnly, fInitial, fVerbose );
    Aig_ManStop( pTemp );

    pNtkAig = Abc_NtkFromDarSeqSweep( pNtk, pMan );
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarRetimeStep( Abc_Ntk_t * pNtk, int fVerbose )
{
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan;
    assert( Abc_NtkIsStrash(pNtk) );
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return NULL;
    if ( pMan->vFlopNums )
        Vec_IntFree( pMan->vFlopNums ); 
    pMan->vFlopNums = NULL;

    pMan->nTruePis = Aig_ManPiNum(pMan) - Aig_ManRegNum(pMan); 
    pMan->nTruePos = Aig_ManPoNum(pMan) - Aig_ManRegNum(pMan); 

    Aig_ManPrintStats(pMan);
    Saig_ManRetimeSteps( pMan, 1, 0 );
    Aig_ManPrintStats(pMan);

    pNtkAig = Abc_NtkFromDarSeqSweep( pNtk, pMan );
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkDarHaigRecord( Abc_Ntk_t * pNtk )
{
/*
    Aig_Man_t * pMan;
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return;
//    Aig_ManReduceLachesCount( pMan );
    if ( pMan->vFlopNums )
        Vec_IntFree( pMan->vFlopNums ); 
    pMan->vFlopNums = NULL;
    Aig_ManHaigRecord( pMan );
    Aig_ManStop( pMan );
*/
}

/**Function*************************************************************

  Synopsis    [Performs random simulation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkDarSeqSim( Abc_Ntk_t * pNtk, int nFrames, int nWords, int fVerbose )
{
    Aig_Man_t * pMan;
    Fra_Sml_t * pSml;
    Fra_Cex_t * pCex;
    int RetValue, clk = clock();
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    pSml = Fra_SmlSimulateSeq( pMan, 0, nFrames, nWords );
    if ( pSml->fNonConstOut )
    {
        pCex = Fra_SmlGetCounterExample( pSml );
        if ( pCex )
            printf( "Simulation of %d frames with %d words asserted output %d in frame %d. ", 
                nFrames, nWords, pCex->iPo, pCex->iFrame );
        pNtk->pSeqModel = pCex;
        RetValue = 1;
    }
    else
    {
        RetValue = 0;
        printf( "Simulation of %d frames with %d words did not assert the outputs. ", 
            nFrames, nWords );
    }
    PRT( "Time", clock() - clk );
    Fra_SmlStop( pSml );
    Aig_ManStop( pMan );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkDarClau( Abc_Ntk_t * pNtk, int nFrames, int nPref, int nClauses, int nLutSize, int nLevels, int nCutsMax, int nBatches, int fStepUp, int fBmc, int fRefs, int fTarget, int fVerbose, int fVeryVerbose )
{
    extern int Fra_Clau( Aig_Man_t * pMan, int nIters, int fVerbose, int fVeryVerbose );
    extern int Fra_Claus( Aig_Man_t * pAig, int nFrames, int nPref, int nClauses, int nLutSize, int nLevels, int nCutsMax, int nBatches, int fStepUp, int fBmc, int fRefs, int fTarget, int fVerbose, int fVeryVerbose );
    Aig_Man_t * pMan;
    if ( fTarget && Abc_NtkPoNum(pNtk) != 1 )
    {
        printf( "The number of outputs should be 1.\n" );
        return 1;
    }
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return 1;
//    Aig_ManReduceLachesCount( pMan );
    if ( pMan->vFlopNums )
        Vec_IntFree( pMan->vFlopNums ); 
    pMan->vFlopNums = NULL;

//    Fra_Clau( pMan, nStepsMax, fVerbose, fVeryVerbose );
    Fra_Claus( pMan, nFrames, nPref, nClauses, nLutSize, nLevels, nCutsMax, nBatches, fStepUp, fBmc, fRefs, fTarget, fVerbose, fVeryVerbose );
    Aig_ManStop( pMan );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Performs targe enlargement.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarEnlarge( Abc_Ntk_t * pNtk, int nFrames, int fVerbose )
{
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan, * pTemp;
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return NULL;
    pMan = Aig_ManFrames( pTemp = pMan, nFrames, 0, 1, 1, 1, NULL );
    Aig_ManStop( pTemp );
    pNtkAig = Abc_NtkFromDarSeqSweep( pNtk, pMan );
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Interplates two networks.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkInterOne( Abc_Ntk_t * pNtkOn, Abc_Ntk_t * pNtkOff, int fRelation, int fVerbose )
{
    extern Aig_Man_t * Aig_ManInter( Aig_Man_t * pManOn, Aig_Man_t * pManOff, int fRelation, int fVerbose );
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pManOn, * pManOff, * pManAig;
    if ( Abc_NtkCoNum(pNtkOn) != 1 || Abc_NtkCoNum(pNtkOff) != 1 )
    {
        printf( "Currently works only for single-output networks.\n" );
        return NULL;
    }
    if ( Abc_NtkCiNum(pNtkOn) != Abc_NtkCiNum(pNtkOff) )
    {
        printf( "The number of PIs should be the same.\n" );
        return NULL;
    }
    // create internal AIGs
    pManOn = Abc_NtkToDar( pNtkOn, 0, 0 );
    if ( pManOn == NULL )
        return NULL;
    pManOff = Abc_NtkToDar( pNtkOff, 0, 0 );
    if ( pManOff == NULL )
        return NULL;
    // derive the interpolant
    pManAig = Aig_ManInter( pManOn, pManOff, fRelation, fVerbose );
    if ( pManAig == NULL )
    {
        printf( "Interpolant computation failed.\n" );
        return NULL;
    }
    Aig_ManStop( pManOn );
    Aig_ManStop( pManOff );
    // for the relation, add an extra input
    if ( fRelation )
    {
        Abc_Obj_t * pObj;
        pObj = Abc_NtkCreatePi( pNtkOff );
        Abc_ObjAssignName( pObj, "New", NULL );
    }
    // create logic network
    pNtkAig = Abc_NtkFromDar( pNtkOff, pManAig );
    Aig_ManStop( pManAig );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Fast interpolation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkInterFast( Abc_Ntk_t * pNtkOn, Abc_Ntk_t * pNtkOff, int fVerbose )
{
    extern void Aig_ManInterFast( Aig_Man_t * pManOn, Aig_Man_t * pManOff, int fVerbose );
    Aig_Man_t * pManOn, * pManOff;
    // create internal AIGs
    pManOn = Abc_NtkToDar( pNtkOn, 0, 0 );
    if ( pManOn == NULL )
        return;
    pManOff = Abc_NtkToDar( pNtkOff, 0, 0 );
    if ( pManOff == NULL )
        return;
    Aig_ManInterFast( pManOn, pManOff, fVerbose );
    Aig_ManStop( pManOn );
    Aig_ManStop( pManOff );
}

int timeCnf;
int timeSat;
int timeInt;

/**Function*************************************************************

  Synopsis    [Interplates two networks.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkInter( Abc_Ntk_t * pNtkOn, Abc_Ntk_t * pNtkOff, int fRelation, int fVerbose )
{
    Abc_Ntk_t * pNtkOn1, * pNtkOff1, * pNtkInter1, * pNtkInter;
    Abc_Obj_t * pObj;
    int i, clk = clock();
    if ( Abc_NtkCoNum(pNtkOn) != Abc_NtkCoNum(pNtkOff) )
    {
        printf( "Currently works only for networks with equal number of POs.\n" );
        return NULL;
    }
    // compute the fast interpolation time
//    Abc_NtkInterFast( pNtkOn, pNtkOff, fVerbose );
    // consider the case of one output
    if ( Abc_NtkCoNum(pNtkOn) == 1 )
        return Abc_NtkInterOne( pNtkOn, pNtkOff, fRelation, fVerbose );
    // start the new newtork
    pNtkInter = Abc_NtkAlloc( ABC_NTK_STRASH, ABC_FUNC_AIG, 1 );
    pNtkInter->pName = Extra_UtilStrsav(pNtkOn->pName);
    Abc_NtkForEachPi( pNtkOn, pObj, i )
        Abc_NtkDupObj( pNtkInter, pObj, 1 );
    // process each POs separately
timeCnf = 0;
timeSat = 0;
timeInt = 0;
    Abc_NtkForEachCo( pNtkOn, pObj, i )
    {
        pNtkOn1 = Abc_NtkCreateCone( pNtkOn, Abc_ObjFanin0(pObj), Abc_ObjName(pObj), 1 );
        if ( Abc_ObjFaninC0(pObj) )
            Abc_ObjXorFaninC( Abc_NtkPo(pNtkOn1, 0), 0 );

        pObj   = Abc_NtkCo(pNtkOff, i);
        pNtkOff1 = Abc_NtkCreateCone( pNtkOff, Abc_ObjFanin0(pObj), Abc_ObjName(pObj), 1 );
        if ( Abc_ObjFaninC0(pObj) )
            Abc_ObjXorFaninC( Abc_NtkPo(pNtkOff1, 0), 0 );

        if ( Abc_NtkNodeNum(pNtkOn1) == 0 )
            pNtkInter1 = Abc_NtkDup( pNtkOn1 );
        else if ( Abc_NtkNodeNum(pNtkOff1) == 0 )
        {
            pNtkInter1 = Abc_NtkDup( pNtkOff1 );
            Abc_ObjXorFaninC( Abc_NtkPo(pNtkInter1, 0), 0 );
        }
        else
            pNtkInter1 = Abc_NtkInterOne( pNtkOn1, pNtkOff1, 0, fVerbose );
        if ( pNtkInter1 )
        {
            Abc_NtkAppend( pNtkInter, pNtkInter1, 1 );
            Abc_NtkDelete( pNtkInter1 );
        }

        Abc_NtkDelete( pNtkOn1 );
        Abc_NtkDelete( pNtkOff1 );
    }
//    PRT( "CNF", timeCnf );
//    PRT( "SAT", timeSat );
//    PRT( "Int", timeInt );
//    PRT( "Slow interpolation time", clock() - clk );

    // return the network
    if ( !Abc_NtkCheck( pNtkInter ) )
        fprintf( stdout, "Abc_NtkAttachBottom(): Network check has failed.\n" );
    return pNtkInter;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkPrintSccs( Abc_Ntk_t * pNtk, int fVerbose )
{
//    extern Vec_Ptr_t * Aig_ManRegPartitionLinear( Aig_Man_t * pAig, int nPartSize );
    Aig_Man_t * pMan;
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return;
    Aig_ManComputeSccs( pMan );
//    Aig_ManRegPartitionLinear( pMan, 1000 );
    Aig_ManStop( pMan );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkDarPrintCone( Abc_Ntk_t * pNtk )
{
    extern void Saig_ManPrintCones( Aig_Man_t * pAig );
    Aig_Man_t * pMan;
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return;
    assert( Aig_ManRegNum(pMan) > 0 );
    pMan->nTruePis = Aig_ManPiNum(pMan) - Aig_ManRegNum(pMan); 
    pMan->nTruePos = Aig_ManPoNum(pMan) - Aig_ManRegNum(pMan); 
    Saig_ManPrintCones( pMan );
    Aig_ManStop( pMan );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []
 
***********************************************************************/
Abc_Ntk_t * Abc_NtkBalanceExor( Abc_Ntk_t * pNtk, int fUpdateLevel, int fVerbose )
{
    extern void Dar_BalancePrintStats( Aig_Man_t * p );
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan, * pTemp;//, * pTemp2;
    assert( Abc_NtkIsStrash(pNtk) );
    // derive AIG with EXORs
    pMan = Abc_NtkToDar( pNtk, 1, 0 );
    if ( pMan == NULL )
        return NULL;
//    Aig_ManPrintStats( pMan );
    if ( fVerbose )
        Dar_BalancePrintStats( pMan );
    // perform balancing
    pTemp = Dar_ManBalance( pMan, fUpdateLevel );
//    Aig_ManPrintStats( pTemp );
    // create logic network
    pNtkAig = Abc_NtkFromDar( pNtk, pTemp );
    Aig_ManStop( pTemp );
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Performs phase abstraction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkPhaseAbstract( Abc_Ntk_t * pNtk, int nFrames, int fIgnore, int fPrint, int fVerbose )
{
    extern Aig_Man_t * Saig_ManPhaseAbstract( Aig_Man_t * p, Vec_Int_t * vInits, int nFrames, int fIgnore, int fPrint, int fVerbose );
    Vec_Int_t * vInits;
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan, * pTemp;
    pMan = Abc_NtkToDar( pNtk, 0, 0 );
    pMan->nRegs = Abc_NtkLatchNum(pNtk);
    pMan->nTruePis = Aig_ManPiNum(pMan) - Aig_ManRegNum(pMan); 
    pMan->nTruePos = Aig_ManPoNum(pMan) - Aig_ManRegNum(pMan); 
    if ( pMan == NULL )
        return NULL;
    vInits = Abc_NtkGetLatchValues(pNtk);
    pMan = Saig_ManPhaseAbstract( pTemp = pMan, vInits, nFrames, fIgnore, fPrint, fVerbose );
    Vec_IntFree( vInits );
    Aig_ManStop( pTemp );
    if ( pMan == NULL )
        return NULL;
    pNtkAig = Abc_NtkFromAigPhase( pMan );
    pNtkAig->pName = Extra_UtilStrsav(pNtk->pName);
    pNtkAig->pSpec = Extra_UtilStrsav(pNtk->pSpec);
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Performs BDD-based reachability analysis.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkDarReach( Abc_Ntk_t * pNtk, int nBddMax, int nIterMax, int fPartition, int fReorder, int fVerbose )
{
    extern int Aig_ManVerifyUsingBdds( Aig_Man_t * p, int nBddMax, int nIterMax, int fPartition, int fReorder, int fVerbose );
    Aig_Man_t * pMan;
    pMan = Abc_NtkToDar( pNtk, 0, 0 );
    pMan->nRegs = Abc_NtkLatchNum(pNtk);
    pMan->nTruePis = Aig_ManPiNum(pMan) - Aig_ManRegNum(pMan); 
    pMan->nTruePos = Aig_ManPoNum(pMan) - Aig_ManRegNum(pMan); 
    if ( pMan == NULL )
        return;
    Aig_ManVerifyUsingBdds( pMan, nBddMax, nIterMax, fPartition, fReorder, fVerbose );
    Aig_ManStop( pMan );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


