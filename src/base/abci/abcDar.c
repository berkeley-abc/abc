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

#include "src/base/abc/abc.h"
#include "src/base/main/main.h"
#include "src/aig/gia/giaAig.h"
#include "src/opt/dar/dar.h"
#include "src/sat/cnf/cnf.h"
#include "src/proof/fra/fra.h"
#include "src/proof/fraig/fraig.h"
#include "src/proof/int/int.h"
#include "src/proof/dch/dch.h"
#include "src/proof/ssw/ssw.h"
#include "src/opt/cgt/cgt.h"
#include "src/proof/bbr/bbr.h"
#include "src/aig/gia/gia.h"
#include "src/proof/cec/cec.h"
#include "src/opt/csw/csw.h"
#include "src/proof/pdr/pdr.h"

ABC_NAMESPACE_IMPL_START

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
    pMan->nConstrs = pNtk->nConstrs;

    pMan->pName = Extra_UtilStrsav( pNtk->pName );
    // transfer the pointers to the basic nodes
    Abc_AigConst1(pNtk)->pCopy = (Abc_Obj_t *)Aig_ManConst1(pMan);
    Abc_NtkForEachCi( pNtk, pObj, i )
        pObj->pCopy = (Abc_Obj_t *)Aig_ObjCreatePi(pMan);
    // complement the 1-values registers
    if ( fRegisters ) {
        Abc_NtkForEachLatch( pNtk, pObj, i )
            if ( Abc_LatchIsInit1(pObj) )
                Abc_ObjFanout0(pObj)->pCopy = Abc_ObjNot(Abc_ObjFanout0(pObj)->pCopy);
    }
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
    Aig_ManSetRegNum( pMan, Abc_NtkLatchNum(pNtk) );
    if ( fRegisters )
        Aig_ManForEachLiSeq( pMan, pObjNew, i )
            if ( Abc_LatchIsInit1(Abc_ObjFanout0(Abc_NtkCo(pNtk,i))) )
                pObjNew->pFanin0 = Aig_Not(pObjNew->pFanin0);
    // remove dangling nodes
    nNodes = (Abc_NtkGetChoiceNum(pNtk) == 0)? Aig_ManCleanup( pMan ) : 0;
    if ( !fExors && nNodes )
        printf( "Abc_NtkToDar(): Unexpected %d dangling nodes when converting to AIG!\n", nNodes );
//Aig_ManDumpVerilog( pMan, "test.v" );
    // save the number of registers
    if ( fRegisters )
    {
        Aig_ManSetRegNum( pMan, Abc_NtkLatchNum(pNtk) );
        pMan->vFlopNums = Vec_IntStartNatural( pMan->nRegs );
//        pMan->vFlopNums = NULL;
//        pMan->vOnehots = Abc_NtkConverLatchNamesIntoNumbers( pNtk );
        if ( pNtk->vOnehots )
            pMan->vOnehots = (Vec_Ptr_t *)Vec_VecDupInt( (Vec_Vec_t *)pNtk->vOnehots );
    }
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

  Description [Assumes that registers are ordered after PIs/POs.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Abc_NtkToDarChoices( Abc_Ntk_t * pNtk )
{
    Aig_Man_t * pMan;
    Abc_Obj_t * pObj, * pPrev, * pFanin;
    Vec_Ptr_t * vNodes;
    int i;
    vNodes = Abc_AigDfs( pNtk, 0, 0 );
    // create the manager
    pMan = Aig_ManStart( Abc_NtkNodeNum(pNtk) + 100 );
    pMan->pName = Extra_UtilStrsav( pNtk->pName );
    pMan->nConstrs = pNtk->nConstrs;
    if ( Abc_NtkGetChoiceNum(pNtk) )
    {
        pMan->pEquivs = ABC_ALLOC( Aig_Obj_t *, Abc_NtkObjNum(pNtk) );
        memset( pMan->pEquivs, 0, sizeof(Aig_Obj_t *) * Abc_NtkObjNum(pNtk) );
    }
    // transfer the pointers to the basic nodes
    Abc_AigConst1(pNtk)->pCopy = (Abc_Obj_t *)Aig_ManConst1(pMan);
    Abc_NtkForEachCi( pNtk, pObj, i )
        pObj->pCopy = (Abc_Obj_t *)Aig_ObjCreatePi(pMan);
    // perform the conversion of the internal nodes (assumes DFS ordering)
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pObj, i )
    {
        pObj->pCopy = (Abc_Obj_t *)Aig_And( pMan, (Aig_Obj_t *)Abc_ObjChild0Copy(pObj), (Aig_Obj_t *)Abc_ObjChild1Copy(pObj) );
//        printf( "%d->%d ", pObj->Id, ((Aig_Obj_t *)pObj->pCopy)->Id );
        if ( Abc_AigNodeIsChoice( pObj ) )
        {
            for ( pPrev = pObj, pFanin = (Abc_Obj_t *)pObj->pData; pFanin; pPrev = pFanin, pFanin = (Abc_Obj_t *)pFanin->pData )
                Aig_ObjSetEquiv( pMan, (Aig_Obj_t *)pPrev->pCopy, (Aig_Obj_t *)pFanin->pCopy );
//            Aig_ManCreateChoice( pIfMan, (Aig_Obj_t *)pNode->pCopy );
        }
    }
    Vec_PtrFree( vNodes );
    // create the POs
    Abc_NtkForEachCo( pNtk, pObj, i )
        Aig_ObjCreatePo( pMan, (Aig_Obj_t *)Abc_ObjChild0Copy(pObj) );
    // complement the 1-valued registers
    Aig_ManSetRegNum( pMan, 0 );
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
    Aig_Obj_t * pObj;
    int i;
    assert( pMan->nAsserts == 0 );
//    assert( Aig_ManRegNum(pMan) == Abc_NtkLatchNum(pNtkOld) );
    // perform strashing
    pNtkNew = Abc_NtkStartFrom( pNtkOld, ABC_NTK_STRASH, ABC_FUNC_AIG );
    pNtkNew->nConstrs = pMan->nConstrs;
    // transfer the pointers to the basic nodes
    Aig_ManConst1(pMan)->pData = Abc_AigConst1(pNtkNew);
    Aig_ManForEachPi( pMan, pObj, i )
        pObj->pData = Abc_NtkCi(pNtkNew, i);
    // rebuild the AIG
    vNodes = Aig_ManDfs( pMan, 1 );
    Vec_PtrForEachEntry( Aig_Obj_t *, vNodes, pObj, i )
        if ( Aig_ObjIsBuf(pObj) )
            pObj->pData = (Abc_Obj_t *)Aig_ObjChild0Copy(pObj);
        else
            pObj->pData = Abc_AigAnd( (Abc_Aig_t *)pNtkNew->pManFunc, (Abc_Obj_t *)Aig_ObjChild0Copy(pObj), (Abc_Obj_t *)Aig_ObjChild1Copy(pObj) );
    Vec_PtrFree( vNodes );
    // connect the PO nodes
    Aig_ManForEachPo( pMan, pObj, i )
    {
        if ( pMan->nAsserts && i == Aig_ManPoNum(pMan) - pMan->nAsserts )
            break;
        Abc_ObjAddFanin( Abc_NtkCo(pNtkNew, i), (Abc_Obj_t *)Aig_ObjChild0Copy(pObj) );
    }
    // if there are assertions, add them
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
    pNtkNew->nConstrs = pMan->nConstrs;
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
        Abc_ObjAddFanin( pObjNew, (Abc_Obj_t *)pObjLi->pData );
        Abc_ObjAddFanin( (Abc_Obj_t *)pObjLo->pData, pObjNew );
        Abc_LatchSetInit0( pObjNew );
    }
    // rebuild the AIG
    vNodes = Aig_ManDfs( pMan, 1 );
    Vec_PtrForEachEntry( Aig_Obj_t *, vNodes, pObj, i )
        if ( Aig_ObjIsBuf(pObj) )
            pObj->pData = (Abc_Obj_t *)Aig_ObjChild0Copy(pObj);
        else
            pObj->pData = Abc_AigAnd( (Abc_Aig_t *)pNtkNew->pManFunc, (Abc_Obj_t *)Aig_ObjChild0Copy(pObj), (Abc_Obj_t *)Aig_ObjChild1Copy(pObj) );
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
        nDigits = Abc_Base10Log( Abc_NtkLatchNum(pNtkNew) );
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
    pNtkNew->nConstrs = pMan->nConstrs;
    // duplicate the name and the spec
//    pNtkNew->pName = Extra_UtilStrsav(pMan->pName);
//    pNtkNew->pSpec = Extra_UtilStrsav(pMan->pSpec);
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
        Abc_ObjAddFanin( pObjNew, (Abc_Obj_t *)pObjLi->pData );
        Abc_ObjAddFanin( (Abc_Obj_t *)pObjLo->pData, pObjNew );
        Abc_LatchSetInit0( pObjNew );
        Abc_ObjAssignName( (Abc_Obj_t *)pObjLi->pData, Abc_ObjName((Abc_Obj_t *)pObjLi->pData), NULL );
        Abc_ObjAssignName( (Abc_Obj_t *)pObjLo->pData, Abc_ObjName((Abc_Obj_t *)pObjLo->pData), NULL );
    }
    // rebuild the AIG
    vNodes = Aig_ManDfs( pMan, 1 );
    Vec_PtrForEachEntry( Aig_Obj_t *, vNodes, pObj, i )
        if ( Aig_ObjIsBuf(pObj) )
            pObj->pData = (Abc_Obj_t *)Aig_ObjChild0Copy(pObj);
        else
            pObj->pData = Abc_AigAnd( (Abc_Aig_t *)pNtkNew->pManFunc, (Abc_Obj_t *)Aig_ObjChild0Copy(pObj), (Abc_Obj_t *)Aig_ObjChild1Copy(pObj) );
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

  Description [This procedure should be called after seq sweeping, 
  which changes the number of registers.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkAfterTrim( Aig_Man_t * pMan, Abc_Ntk_t * pNtkOld )
{
    Vec_Ptr_t * vNodes; 
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pObjNew, * pObjOld;
    Aig_Obj_t * pObj, * pObjLo, * pObjLi;
    int i; 
    assert( pMan->nAsserts == 0 );
    assert( Aig_ManRegNum(pMan) <= Abc_NtkLatchNum(pNtkOld) );
    assert( Saig_ManPiNum(pMan) <= Abc_NtkCiNum(pNtkOld) );
    assert( Saig_ManPoNum(pMan) == Abc_NtkPoNum(pNtkOld) );
    assert( pMan->vCiNumsOrig != NULL );
    // perform strashing
    pNtkNew = Abc_NtkAlloc( ABC_NTK_STRASH, ABC_FUNC_AIG, 1 );
    pNtkNew->nConstrs = pMan->nConstrs;
    // duplicate the name and the spec
//    pNtkNew->pName = Extra_UtilStrsav(pMan->pName);
//    pNtkNew->pSpec = Extra_UtilStrsav(pMan->pSpec);
    Aig_ManConst1(pMan)->pData = Abc_AigConst1(pNtkNew);
    // create PIs
    Aig_ManForEachPiSeq( pMan, pObj, i )
    {
        pObjNew = Abc_NtkCreatePi( pNtkNew );
        pObj->pData = pObjNew;
        // find the name
        pObjOld = Abc_NtkCi( pNtkOld, Vec_IntEntry(pMan->vCiNumsOrig, i) );
        Abc_ObjAssignName( pObjNew, Abc_ObjName(pObjOld), NULL );
    }
    // create POs
    Aig_ManForEachPoSeq( pMan, pObj, i )
    {
        pObjNew = Abc_NtkCreatePo( pNtkNew );
        pObj->pData = pObjNew;
        // find the name
        pObjOld = Abc_NtkCo( pNtkOld, i );
        Abc_ObjAssignName( pObjNew, Abc_ObjName(pObjOld), NULL );
    }
    assert( Abc_NtkCiNum(pNtkNew) == Aig_ManPiNum(pMan) - Aig_ManRegNum(pMan) );
    assert( Abc_NtkCoNum(pNtkNew) == Aig_ManPoNum(pMan) - Aig_ManRegNum(pMan) );
    // create as many latches as there are registers in the manager
    Aig_ManForEachLiLoSeq( pMan, pObjLi, pObjLo, i )
    {
        pObjNew = Abc_NtkCreateLatch( pNtkNew );
        pObjLi->pData = Abc_NtkCreateBi( pNtkNew );
        pObjLo->pData = Abc_NtkCreateBo( pNtkNew );
        Abc_ObjAddFanin( pObjNew, (Abc_Obj_t *)pObjLi->pData );
        Abc_ObjAddFanin( (Abc_Obj_t *)pObjLo->pData, pObjNew );
        Abc_LatchSetInit0( pObjNew );
        // find the name
        pObjOld = Abc_NtkCi( pNtkOld, Vec_IntEntry(pMan->vCiNumsOrig, Saig_ManPiNum(pMan)+i) );
        Abc_ObjAssignName( (Abc_Obj_t *)pObjLo->pData, Abc_ObjName(pObjOld), NULL );
        // find the name
        pObjOld = Abc_NtkCo( pNtkOld, Saig_ManPoNum(pMan)+i );
        Abc_ObjAssignName( (Abc_Obj_t *)pObjLi->pData, Abc_ObjName(pObjOld), NULL );
    }
    // rebuild the AIG
    vNodes = Aig_ManDfs( pMan, 1 );
    Vec_PtrForEachEntry( Aig_Obj_t *, vNodes, pObj, i )
        if ( Aig_ObjIsBuf(pObj) )
            pObj->pData = (Abc_Obj_t *)Aig_ObjChild0Copy(pObj);
        else
            pObj->pData = Abc_AigAnd( (Abc_Aig_t *)pNtkNew->pManFunc, (Abc_Obj_t *)Aig_ObjChild0Copy(pObj), (Abc_Obj_t *)Aig_ObjChild1Copy(pObj) );
    Vec_PtrFree( vNodes );
    // connect the PO nodes
    Aig_ManForEachPo( pMan, pObj, i )
    {
        pObjNew = (Abc_Obj_t *)Aig_ObjChild0Copy(pObj);
        Abc_ObjAddFanin( Abc_NtkCo(pNtkNew, i), pObjNew );
    }
    // check the resulting AIG
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkAfterTrim(): Network check has failed.\n" );
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
    pNtkNew->nConstrs = pMan->nConstrs;
    // transfer the pointers to the basic nodes
    Aig_ManConst1(pMan)->pData = Abc_AigConst1(pNtkNew);
    Aig_ManForEachPi( pMan, pObj, i )
        pObj->pData = Abc_NtkCi(pNtkNew, i);

    // rebuild the AIG
    vNodes = Aig_ManDfsChoices( pMan );
    Vec_PtrForEachEntry( Aig_Obj_t *, vNodes, pObj, i )
    {
        pObj->pData = Abc_AigAnd( (Abc_Aig_t *)pNtkNew->pManFunc, (Abc_Obj_t *)Aig_ObjChild0Copy(pObj), (Abc_Obj_t *)Aig_ObjChild1Copy(pObj) );
        if ( (pTemp = Aig_ObjEquiv(pMan, pObj)) )
        {
            Abc_Obj_t * pAbcRepr, * pAbcObj;
            assert( pTemp->pData != NULL );
            pAbcRepr = (Abc_Obj_t *)pObj->pData;
            pAbcObj  = (Abc_Obj_t *)pTemp->pData;
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
    pNtkNew->nConstrs = pMan->nConstrs;
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
    Vec_PtrForEachEntry( Aig_Obj_t *, vNodes, pObj, i )
    {
        // add the first fanin
        pObj->pData = pFaninNew0 = (Abc_Obj_t *)Aig_ObjChild0Copy(pObj);
        if ( Aig_ObjIsBuf(pObj) )
            continue;
        // add the second fanin
        pFaninNew1 = (Abc_Obj_t *)Aig_ObjChild1Copy(pObj);
        // create the new node
        if ( Aig_ObjIsExor(pObj) )
            pObj->pData = pObjNew = Abc_AigXor( (Abc_Aig_t *)pNtkNew->pManFunc, pFaninNew0, pFaninNew1 );
        else
            pObj->pData = pObjNew = Abc_AigAnd( (Abc_Aig_t *)pNtkNew->pManFunc, pFaninNew0, pFaninNew1 );
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
        Abc_ObjAddFanin( Abc_ObjFanin0(Abc_ObjFanin0((Abc_Obj_t *)pObj->pData)), pFaninNew );
    }
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkFromIvySeq(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Collects CI of the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkCollectCiNames( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    int i;
    Vec_Ptr_t * vNames;
    vNames = Vec_PtrAlloc( 100 );
    Abc_NtkForEachCi( pNtk, pObj, i )
        Vec_PtrPush( vNames, Extra_UtilStrsav(Abc_ObjName(pObj)) );
    return vNames;
}

/**Function*************************************************************

  Synopsis    [Collects CO of the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkCollectCoNames( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    int i;
    Vec_Ptr_t * vNames;
    vNames = Vec_PtrAlloc( 100 );
    Abc_NtkForEachCo( pNtk, pObj, i )
        Vec_PtrPush( vNames, Extra_UtilStrsav(Abc_ObjName(pObj)) );
    return vNames;
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
//    extern Aig_Man_t * Csw_Sweep( Aig_Man_t * pAig, int nCutsMax, int nLeafMax, int fVerbose );
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
//ABC_PRT( "time", clock() - clk );

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
//ABC_PRT( "time", clock() - clk );

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
Abc_Ntk_t * Abc_NtkDC2( Abc_Ntk_t * pNtk, int fBalance, int fUpdateLevel, int fFanout, int fPower, int fVerbose )
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
    pMan = Dar_ManCompress2( pTemp = pMan, fBalance, fUpdateLevel, fFanout, fPower, fVerbose ); 
    Aig_ManStop( pTemp );
//ABC_PRT( "time", clock() - clk );

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
Abc_Ntk_t * Abc_NtkDch( Abc_Ntk_t * pNtk, Dch_Pars_t * pPars )
{
    extern Gia_Man_t * Dar_NewChoiceSynthesis( Aig_Man_t * pAig, int fBalance, int fUpdateLevel, int fPower, int fLightSynth, int fVerbose );
    extern Aig_Man_t * Cec_ComputeChoices( Gia_Man_t * pGia, Dch_Pars_t * pPars );

    Aig_Man_t * pMan, * pTemp;
    Abc_Ntk_t * pNtkAig;
    Gia_Man_t * pGia;
    int clk;
    assert( Abc_NtkIsStrash(pNtk) );
    pMan = Abc_NtkToDar( pNtk, 0, 0 );
    if ( pMan == NULL )
        return NULL;
clk = clock();
    if ( pPars->fSynthesis )
        pGia = Dar_NewChoiceSynthesis( pMan, 1, 1, pPars->fPower, pPars->fLightSynth, pPars->fVerbose );
    else
    {
        pGia = Gia_ManFromAig( pMan );
        Aig_ManStop( pMan );
    }
pPars->timeSynth = clock() - clk;
    if ( pPars->fUseGia )
        pMan = Cec_ComputeChoices( pGia, pPars );
    else
    {
        pMan = Gia_ManToAigSkip( pGia, 3 );
        Gia_ManStop( pGia );
        pMan = Dch_ComputeChoices( pTemp = pMan, pPars );
        Aig_ManStop( pTemp );
    }
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
//ABC_PRT( "time", clock() - clk );

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
    Vec_PtrForEachEntry( Aig_Obj_t *, vMapped, pObj, i )
    {
        // create new node
        pNodeNew = Abc_NtkCreateNode( pNtkNew );
        // add fanins according to the cut
        pCut = (Cnf_Cut_t *)pObj->pData;
        Cnf_CutForEachLeaf( p->pManAig, pCut, pLeaf, k )
            Abc_ObjAddFanin( pNodeNew, (Abc_Obj_t *)pLeaf->pData );
        // add logic function
        if ( pCut->nFanins < 5 )
        {
            uTruth = 0xFFFF & *Cnf_CutTruth(pCut);
            Cnf_SopConvertToVector( p->pSops[uTruth], p->pSopSizes[uTruth], vCover );
            pNodeNew->pData = Abc_SopCreateFromIsop( (Mem_Flex_t *)pNtkNew->pManFunc, pCut->nFanins, vCover );
        }
        else
            pNodeNew->pData = Abc_SopCreateFromIsop( (Mem_Flex_t *)pNtkNew->pManFunc, pCut->nFanins, pCut->vIsop[1] );
        // save the node
        pObj->pData = pNodeNew;
    }
    Vec_IntFree( vCover );
    // add the CO drivers
    Abc_NtkForEachCo( pNtk, pNode, i )
    {
        pObj = Aig_ManPo(p->pManAig, i);
        pNodeNew = Abc_ObjNotCond( (Abc_Obj_t *)Aig_ObjFanin0(pObj)->pData, Aig_ObjFaninC0(pObj) );
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
Abc_Ntk_t * Abc_NtkDarToCnf( Abc_Ntk_t * pNtk, char * pFileName, int fFastAlgo, int fChangePol, int fVerbose )
{
    Vec_Ptr_t * vMapped = NULL;
    Aig_Man_t * pMan;
    Cnf_Man_t * pManCnf = NULL;
    Cnf_Dat_t * pCnf;
    Abc_Ntk_t * pNtkNew = NULL;
    int clk = clock();
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
    if ( fVerbose )
    Aig_ManPrintStats( pMan );

    // derive CNF
    if ( fFastAlgo )
        pCnf = Cnf_DeriveFast( pMan, 0 );
    else
        pCnf = Cnf_Derive( pMan, 0 );

    // adjust polarity
    if ( fChangePol )
        Cnf_DataTranformPolarity( pCnf, 0 );

    // print stats
    if ( fVerbose )
    {
        printf( "Vars = %6d. Clauses = %7d. Literals = %8d.   ", pCnf->nVars, pCnf->nClauses, pCnf->nLiterals );
        Abc_PrintTime( 1, "Time", clock() - clk );
    }

/*
    // write the network for verification
    pManCnf = Cnf_ManRead();
    vMapped = Cnf_ManScanMapping( pManCnf, 1, 0 );
    pNtkNew = Abc_NtkConstructFromCnf( pNtk, pManCnf, vMapped );
    Vec_PtrFree( vMapped );
*/
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
int Abc_NtkDSat( Abc_Ntk_t * pNtk, ABC_INT64_T nConfLimit, ABC_INT64_T nInsLimit, int fAlignPol, int fAndOuts, int fNewSolver, int fVerbose )
{
    Aig_Man_t * pMan;
    int RetValue;//, clk = clock();
    assert( Abc_NtkIsStrash(pNtk) );
    assert( Abc_NtkLatchNum(pNtk) == 0 );
//    assert( Abc_NtkPoNum(pNtk) == 1 );
    pMan = Abc_NtkToDar( pNtk, 0, 0 );
    RetValue = Fra_FraigSat( pMan, nConfLimit, nInsLimit, fAlignPol, fAndOuts, fNewSolver, fVerbose ); 
    pNtk->pModel = (int *)pMan->pData, pMan->pData = NULL;
    Aig_ManStop( pMan );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Solves combinational miter using a SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkPartitionedSat( Abc_Ntk_t * pNtk, int nAlgo, int nPartSize, int nConfPart, int nConfTotal, int fAlignPol, int fSynthesize, int fVerbose )
{
    extern int Aig_ManPartitionedSat( Aig_Man_t * pNtk, int nAlgo, int nPartSize, int nConfPart, int nConfTotal, int fAlignPol, int fSynthesize, int fVerbose );
    Aig_Man_t * pMan;
    int RetValue;//, clk = clock();
    assert( Abc_NtkIsStrash(pNtk) );
    assert( Abc_NtkLatchNum(pNtk) == 0 );
    pMan = Abc_NtkToDar( pNtk, 0, 0 );
    RetValue = Aig_ManPartitionedSat( pMan, nAlgo, nPartSize, nConfPart, nConfTotal, fAlignPol, fSynthesize, fVerbose ); 
    pNtk->pModel = (int *)pMan->pData, pMan->pData = NULL;
    Aig_ManStop( pMan );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkDarCec( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nConfLimit, int fPartition, int fVerbose )
{
    Aig_Man_t * pMan, * pMan1, * pMan2;
    Abc_Ntk_t * pMiter;
    int RetValue, clkTotal = clock();
/*
    {
    extern void Cec_ManVerifyTwoAigs( Aig_Man_t * pAig0, Aig_Man_t * pAig1, int fVerbose );
    Aig_Man_t * pAig0 = Abc_NtkToDar( pNtk1, 0, 0 );
    Aig_Man_t * pAig1 = Abc_NtkToDar( pNtk2, 0, 0 );
    Cec_ManVerifyTwoAigs( pAig0, pAig1, 1 );
    Aig_ManStop( pAig0 );
    Aig_ManStop( pAig1 );
    return 1;
    }
*/
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
        RetValue = Fra_FraigCecPartitioned( pMan1, pMan2, nConfLimit, 100, 1, fVerbose );
        Aig_ManStop( pMan1 );
        Aig_ManStop( pMan2 );
        goto finish;
    }

    if ( pNtk2 != NULL )
    {
        // get the miter of the two networks
        pMiter = Abc_NtkMiter( pNtk1, pNtk2, 0, 0, 0, 0 );
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
//        ABC_FREE( pMiter->pModel );
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
    RetValue = Fra_FraigCec( &pMan, 100000, fVerbose );
    // transfer model if given
    if ( pNtk2 == NULL )
        pNtk1->pModel = (int *)pMan->pData, pMan->pData = NULL;
    Aig_ManStop( pMan );

finish:
    // report the miter
    if ( RetValue == 1 )
    {
        printf( "Networks are equivalent.   " );
ABC_PRT( "Time", clock() - clkTotal );
    }
    else if ( RetValue == 0 )
    {
        printf( "Networks are NOT EQUIVALENT.   " );
ABC_PRT( "Time", clock() - clkTotal );
    }
    else
    {
        printf( "Networks are UNDECIDED.   " );
ABC_PRT( "Time", clock() - clkTotal );
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
ABC_PRT( "Initial fraiging time", clock() - clk );
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

  Synopsis    [Print Latch Equivalence Classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkPrintLatchEquivClasses( Abc_Ntk_t * pNtk, Aig_Man_t * pAig )
{
    int header_dumped = 0;
    int num_orig_latches = Abc_NtkLatchNum(pNtk);
    char **pNames = ABC_ALLOC( char *, num_orig_latches );
    int *p_irrelevant = ABC_ALLOC( int, num_orig_latches );
    char * pFlopName, * pReprName;
    Aig_Obj_t * pFlop, * pRepr;
    Abc_Obj_t * pNtkFlop; 
    int repr_idx;
    int i;

    Abc_NtkForEachLatch( pNtk, pNtkFlop, i )
    {
        char *temp_name = Abc_ObjName( Abc_ObjFanout0(pNtkFlop) );
        pNames[i] = ABC_ALLOC( char , strlen(temp_name)+1);
        strcpy(pNames[i], temp_name);
    }
    i = 0;
    
    Aig_ManSetPioNumbers( pAig );
    Saig_ManForEachLo( pAig, pFlop, i )
    {
        p_irrelevant[i] = false;
        
        pFlopName = pNames[i];

        pRepr = Aig_ObjRepr(pAig, pFlop);

        if ( pRepr == NULL )
        {
            // printf("Nothing equivalent to flop %s\n", pFlopName);
//            p_irrelevant[i] = true;
            continue;
        }

        if (!header_dumped)
        {
            printf("Here are the flop equivalences:\n");
            header_dumped = true;
        }

        // pRepr is representative of the equivalence class, to which pFlop belongs
        if ( Aig_ObjIsConst1(pRepr) )
        {
            printf( "Original flop %s is proved equivalent to constant.\n", pFlopName );
            // printf( "Original flop # %d is proved equivalent to constant.\n", i );
            continue;
        }

        assert( Saig_ObjIsLo( pAig, pRepr ) );
        repr_idx = Aig_ObjPioNum(pRepr) - Saig_ManPiNum(pAig);
        pReprName = pNames[repr_idx];
        printf( "Original flop %s is proved equivalent to flop %s.\n",  pFlopName, pReprName );
        // printf( "Original flop # %d is proved equivalent to flop # %d.\n",  i, repr_idx );
    }

    header_dumped = false;
    for (i=0; i<num_orig_latches; ++i)
    {
        if (p_irrelevant[i])
        {
            if (!header_dumped)
            {
                printf("The following flops have been deemed irrelevant:\n");
                header_dumped = true;
            }
            printf("%s ", pNames[i]);
        }
        
        ABC_FREE(pNames[i]);
    }
    if (header_dumped)
        printf("\n");
    
    ABC_FREE(pNames);
    ABC_FREE(p_irrelevant);
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarSeqSweep2( Abc_Ntk_t * pNtk, Ssw_Pars_t * pPars )
{
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan, * pTemp;

    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return NULL;

    pMan = Ssw_SignalCorrespondence( pTemp = pMan, pPars );

    if ( pPars->fFlopVerbose )
        Abc_NtkPrintLatchEquivClasses(pNtk, pTemp);

    Aig_ManStop( pTemp );
    if ( pMan == NULL )
        return NULL;

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

  Synopsis    [Computes latch correspondence.]

  Description [] 
               
  SideEffects []

  SeeAlso     []
 
***********************************************************************/
Abc_Ntk_t * Abc_NtkDarLcorrNew( Abc_Ntk_t * pNtk, int nVarsMax, int nConfMax, int fVerbose )
{
    Ssw_Pars_t Pars, * pPars = &Pars;
    Aig_Man_t * pMan, * pTemp;
    Abc_Ntk_t * pNtkAig = NULL;
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return NULL;
    Ssw_ManSetDefaultParams( pPars );
    pPars->fLatchCorrOpt = 1;
    pPars->nBTLimit      = nConfMax;
    pPars->nSatVarMax    = nVarsMax;
    pPars->fVerbose      = fVerbose;
    pMan = Ssw_SignalCorrespondence( pTemp = pMan, pPars );
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

/*
#include <signal.h>
#include "src/misc/util/utilMem.h"
static void sigfunc( int signo ) 
{
    if (signo == SIGINT) {
        printf("SIGINT received!\n");
        s_fInterrupt = 1;
    }
}
*/

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkDarBmc( Abc_Ntk_t * pNtk, int nStart, int nFrames, int nSizeMax, int nNodeDelta, int nTimeOut, int nBTLimit, int nBTLimitAll, int fRewrite, int fNewAlgo, int nCofFanLit, int fVerbose, int * piFrames )
{
    Aig_Man_t * pMan;
    int status, RetValue = -1, clk = clock();
    int nTimeLimit = nTimeOut ? time(NULL) + nTimeOut : 0;

    // derive the AIG manager
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
    {
        printf( "Converting miter into AIG has failed.\n" );
        return RetValue;
    }
    assert( pMan->nRegs > 0 );
    // perform verification
    if ( fNewAlgo )
    {
        int iFrame;
        RetValue = Saig_ManBmcSimple( pMan, nFrames, nSizeMax, nBTLimit, fRewrite, fVerbose, &iFrame, nCofFanLit );
        if ( piFrames )
            *piFrames = iFrame;
        ABC_FREE( pNtk->pModel );
        ABC_FREE( pNtk->pSeqModel );
        pNtk->pSeqModel = pMan->pSeqModel; pMan->pSeqModel = NULL;
        if ( RetValue == 1 )
        {
//            printf( "No output asserted in %d frames. ", iFrame );
            printf( "Incorrect return value.  " );
        }
        else if ( RetValue == -1 )
        {
            printf( "No output asserted in %d frames. Resource limit reached ", iFrame );
            if ( time(NULL) > nTimeLimit )
                printf( "(timeout %d sec). ", nTimeLimit );
            else
                printf( "(conf limit %d). ", nBTLimit );
        }
        else // if ( RetValue == 0 )
        {
//            extern void Aig_ManCounterExampleValueTest( Aig_Man_t * pAig, Abc_Cex_t * pCex );

            Abc_Cex_t * pCex = pNtk->pSeqModel;
            printf( "Output %d asserted in frame %d (use \"write_counter\" to dump a witness). ", pCex->iPo, pCex->iFrame );

//            Aig_ManCounterExampleValueTest( pMan, pCex );
        }
ABC_PRT( "Time", clock() - clk );
    }
    else
    { 
/*
        Fra_BmcPerformSimple( pMan, nFrames, nBTLimit, fRewrite, fVerbose );
        ABC_FREE( pNtk->pModel );
        ABC_FREE( pNtk->pSeqModel );
        pNtk->pSeqModel = pMan->pSeqModel; pMan->pSeqModel = NULL;
        if ( pNtk->pSeqModel )
        {
            Abc_Cex_t * pCex = pNtk->pSeqModel;
            printf( "Output %d asserted in frame %d (use \"write_counter\" to dump a witness). ", pCex->iPo, pCex->iFrame );
            RetValue = 0;
        }
        else
        {
            printf( "No output asserted in %d frames. ", nFrames );
            RetValue = 1;
        }
*/
/*
        int iFrame;
        RetValue = Ssw_BmcDynamic( pMan, nFrames, nBTLimit, fVerbose, &iFrame );
        ABC_FREE( pNtk->pModel );
        ABC_FREE( pNtk->pSeqModel );
        pNtk->pSeqModel = pMan->pSeqModel; pMan->pSeqModel = NULL;
        if ( RetValue == 1 )
            printf( "No output asserted in %d frames. ", iFrame );
        else if ( RetValue == -1 )
            printf( "No output asserted in %d frames. Reached conflict limit (%d). ", iFrame, nBTLimit );
        else // if ( RetValue == 0 )
        {
            Abc_Cex_t * pCex = pNtk->pSeqModel;
            printf( "Output %d asserted in frame %d (use \"write_counter\" to dump a witness). ", pCex->iPo, pCex->iFrame );
        }
*/
        RetValue = Saig_BmcPerform( pMan, nStart, nFrames, nNodeDelta, nTimeOut, nBTLimit, nBTLimitAll, fVerbose, 0, piFrames );
        ABC_FREE( pNtk->pModel );
        ABC_FREE( pNtk->pSeqModel );
        pNtk->pSeqModel = pMan->pSeqModel; pMan->pSeqModel = NULL;
    }
    // verify counter-example
    if ( pNtk->pSeqModel ) 
    {
        status = Saig_ManVerifyCex( pMan, pNtk->pSeqModel );
        if ( status == 0 )
            printf( "Abc_NtkDarBmc(): Counter-example verification has FAILED.\n" );
    }
    Aig_ManStop( pMan );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkDarBmc3( Abc_Ntk_t * pNtk, Saig_ParBmc_t * pPars )
{
    Aig_Man_t * pMan;
    int status, RetValue = -1, clk = clock();
    int nTimeOut = pPars->nTimeOut ? time(NULL) + pPars->nTimeOut : 0;
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
    {
        printf( "Converting miter into AIG has failed.\n" );
        return RetValue;
    }
    assert( pMan->nRegs > 0 );
    RetValue = Saig_ManBmcScalable( pMan, pPars );
    ABC_FREE( pNtk->pModel );
    ABC_FREE( pNtk->pSeqModel );
    pNtk->pSeqModel = pMan->pSeqModel; pMan->pSeqModel = NULL;
    if ( RetValue == 1 )
    {
        printf( "Explored all reachable states after completing %d frames.  ", 1<<Aig_ManRegNum(pMan) );
    }
    else if ( RetValue == -1 )
    {
        if ( pPars->nFailOuts == 0 )
        {
            printf( "No output asserted in %d frames. Resource limit reached ", pPars->iFrame );
            if ( time(NULL) > nTimeOut )
                printf( "(timeout %d sec). ", pPars->nTimeOut );
            else
                printf( "(conf limit %d). ", pPars->nConfLimit );
        }
        else
        {
            printf( "The total of %d outputs asserted in %d frames. Resource limit reached ", pPars->nFailOuts, pPars->iFrame );
            if ( time(NULL) > nTimeOut )
                printf( "(timeout %d sec). ", pPars->nTimeOut );
            else
                printf( "(conf limit %d). ", pPars->nConfLimit );
//            if ( pNtk->vSeqModelVec )
//                Vec_PtrFreeFree( pNtk->vSeqModelVec );
//            pNtk->vSeqModelVec = pMan->vSeqModelVec;  pMan->vSeqModelVec = NULL;
        }
    }
    else // if ( RetValue == 0 )
    {
        if ( !pPars->fSolveAll )
        {
            Abc_Cex_t * pCex = pNtk->pSeqModel;
            printf( "Output %d asserted in frame %d (use \"write_counter\" to dump a witness). ", pCex->iPo, pCex->iFrame );
        }
        else
        {
            int nOutputs = Saig_ManPoNum(pMan) - Saig_ManConstrNum(pMan);
            if ( Vec_PtrCountZero(pMan->vSeqModelVec) == 0 )
                printf( "All %d outputs are found to be SAT.   ", nOutputs );
            else if ( Vec_PtrCountZero(pMan->vSeqModelVec) == nOutputs )
                printf( "None of the %d outputs is found to be SAT.   ", nOutputs );
            else
                printf( "Some outputs (%d out of %d) are proved SAT.   ", 
                    nOutputs - Vec_PtrCountZero(pMan->vSeqModelVec), nOutputs );
            if ( pNtk->vSeqModelVec )
                Vec_PtrFreeFree( pNtk->vSeqModelVec );
            pNtk->vSeqModelVec = pMan->vSeqModelVec;  pMan->vSeqModelVec = NULL;
        }
    }
    ABC_PRT( "Time", clock() - clk );
    if ( pNtk->pSeqModel ) 
    {
        status = Saig_ManVerifyCex( pMan, pNtk->pSeqModel );
        if ( status == 0 )
            printf( "Abc_NtkDarBmc3(): Counter-example verification has FAILED.\n" );
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
int Abc_NtkDarBmcInter_int( Aig_Man_t * pMan, Inter_ManParams_t * pPars, Aig_Man_t ** ppNtkRes )
{
    int RetValue, iFrame, clk = clock();
    int nTotalProvedSat = 0;
    assert( pMan->nRegs > 0 );
    if ( ppNtkRes )
        *ppNtkRes = NULL;
    if ( pPars->fUseSeparate )
    {
        Aig_Man_t * pTemp, * pAux;
        Aig_Obj_t * pObjPo;
        int i, Counter = 0;
        Saig_ManForEachPo( pMan, pObjPo, i )
        {
            if ( Aig_ObjFanin0(pObjPo) == Aig_ManConst1(pMan) )
                continue;
            if ( pPars->fVerbose )
                printf( "Solving output %2d (out of %2d):\n", i, Saig_ManPoNum(pMan) );
            pTemp = Aig_ManDupOneOutput( pMan, i, 1 );
            pTemp = Aig_ManScl( pAux = pTemp, 1, 1, 0, -1, -1, 0, 0 );
            Aig_ManStop( pAux );
            if ( Aig_ManRegNum(pTemp) == 0 )
            {
                pTemp->pSeqModel = NULL;
                RetValue = Fra_FraigSat( pTemp, pPars->nBTLimit, 0, 0, 0, 0, 0 ); 
                if ( pTemp->pData )
                    pTemp->pSeqModel = Abc_CexCreate( Aig_ManRegNum(pMan), Saig_ManPiNum(pMan), (int *)pTemp->pData, 0, i, 1 );
//                pNtk->pModel = pTemp->pData, pTemp->pData = NULL;
            }
            else
                RetValue = Inter_ManPerformInterpolation( pTemp, pPars, &iFrame );
            if ( pTemp->pSeqModel )
            {
                if ( pPars->fDropSatOuts )
                {
                    printf( "Output %d proved SAT in frame %d (replacing by const 0 and continuing...)\n", i, pTemp->pSeqModel->iFrame );
                    Aig_ObjPatchFanin0( pMan, pObjPo, Aig_ManConst0(pMan) );
                    Aig_ManStop( pTemp );
                    nTotalProvedSat++;
                    continue;
                }
                else
                {
                    Abc_Cex_t * pCex;
                    pCex = pMan->pSeqModel = pTemp->pSeqModel; pTemp->pSeqModel = NULL;
                    pCex->iPo = i;
                    Aig_ManStop( pTemp );
                    break;
                }
            }
            // if solved, remove the output
            if ( RetValue == 1 )
            {
                Aig_ObjPatchFanin0( pMan, pObjPo, Aig_ManConst0(pMan) );
//                    printf( "Output %3d : Solved ", i );
            }
            else
            {
                Counter++;
//                    printf( "Output %3d : Undec  ", i );
            }
//                Aig_ManPrintStats( pTemp );
            Aig_ManStop( pTemp );
            printf( "Solving output %3d (out of %3d) using interpolation.\r", i, Saig_ManPoNum(pMan) );
        }
        Aig_ManCleanup( pMan );
        if ( pMan->pSeqModel == NULL )
        {
            printf( "Interpolation left %d (out of %d) outputs unsolved              \n", Counter, Saig_ManPoNum(pMan) );
            if ( Counter )
                RetValue = -1;
        }
        if ( ppNtkRes )
        {
            pTemp = Aig_ManDupUnsolvedOutputs( pMan, 1 );
            *ppNtkRes = Aig_ManScl( pTemp, 1, 1, 0, -1, -1, 0, 0 );
            Aig_ManStop( pTemp );
        }
    }
    else
    {    
        RetValue = Inter_ManPerformInterpolation( pMan, pPars, &iFrame );
    }
    if ( nTotalProvedSat )
        printf( "The total of %d outputs proved SAT and replaced by const 0 in this run.\n", nTotalProvedSat );
    if ( RetValue == 1 )
        printf( "Property proved.  " );
    else if ( RetValue == 0 )
        printf( "Property DISPROVED in frame %d (use \"write_counter\" to dump a witness).  ", iFrame );
    else if ( RetValue == -1 )
        printf( "Property UNDECIDED.  " );
    else
        assert( 0 );
ABC_PRT( "Time", clock() - clk );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkDarBmcInter( Abc_Ntk_t * pNtk, Inter_ManParams_t * pPars, Abc_Ntk_t ** ppNtkRes )
{
    Aig_Man_t * pMan;
    int RetValue;
    if ( ppNtkRes )
        *ppNtkRes = NULL;
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
    {
        printf( "Converting miter into AIG has failed.\n" );
        return -1;
    }
    if ( pPars->fUseSeparate && ppNtkRes )
    {
        Aig_Man_t * pManNew;
        RetValue = Abc_NtkDarBmcInter_int( pMan, pPars, &pManNew );
        *ppNtkRes = Abc_NtkFromAigPhase( pManNew );
        Aig_ManStop( pManNew );
    }
    else
    {
        RetValue = Abc_NtkDarBmcInter_int( pMan, pPars, NULL );
    }
    ABC_FREE( pNtk->pModel );
    ABC_FREE( pNtk->pSeqModel );
    pNtk->pSeqModel = pMan->pSeqModel; pMan->pSeqModel = NULL;
    Aig_ManStop( pMan );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkDarDemiter( Abc_Ntk_t * pNtk )
{ 
    char * pFileNameGeneric, pFileName0[1000], pFileName1[1000];
    Aig_Man_t * pMan, * pPart0, * pPart1;//, * pMiter;
    // derive the AIG manager
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
    {
        printf( "Converting network into AIG has failed.\n" );
        return 0;
    }
//    if ( !Saig_ManDemiterSimple( pMan, &pPart0, &pPart1 ) )
    if ( !Saig_ManDemiterSimpleDiff( pMan, &pPart0, &pPart1 ) )
    {
        printf( "Demitering has failed.\n" );
        return 0;
    }
    // create file names
    pFileNameGeneric = Extra_FileNameGeneric( pNtk->pSpec );
    sprintf( pFileName0,  "%s%s",  pFileNameGeneric, "_part0.aig" ); 
    sprintf( pFileName1,  "%s%s",  pFileNameGeneric, "_part1.aig" ); 
    ABC_FREE( pFileNameGeneric );
    // dump files
    Ioa_WriteAiger( pPart0, pFileName0, 0, 0 );
    Ioa_WriteAiger( pPart1, pFileName1, 0, 0 );
    printf( "Demitering produced two files \"%s\" and \"%s\".\n", pFileName0, pFileName1 );
    // create two-level miter
//    pMiter = Saig_ManCreateMiterTwo( pPart0, pPart1, 2 );
//    Aig_ManDumpBlif( pMiter, "miter01.blif", NULL, NULL );
//    Aig_ManStop( pMiter );
//    printf( "The new miter is written into file \"%s\".\n", "miter01.blif" );
    Aig_ManStop( pPart0 );
    Aig_ManStop( pPart1 );
    Aig_ManStop( pMan );
    return 1;
} 

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkDarDemiterNew( Abc_Ntk_t * pNtk )
{ 
    char * pFileNameGeneric, pFileName0[1000], pFileName1[1000];
    Aig_Man_t * pMan, * pPart0, * pPart1;//, * pMiter;
    // derive the AIG manager
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
    {
        printf( "Converting network into AIG has failed.\n" );
        return 0;
    }

    Saig_ManDemiterNew( pMan );
    Aig_ManStop( pMan );
    return 1;

//    if ( !Saig_ManDemiterSimple( pMan, &pPart0, &pPart1 ) )
    if ( !Saig_ManDemiterSimpleDiff( pMan, &pPart0, &pPart1 ) )
    {
        printf( "Demitering has failed.\n" );
        return 0;
    }
    // create file names
    pFileNameGeneric = Extra_FileNameGeneric( pNtk->pSpec );
    sprintf( pFileName0,  "%s%s",  pFileNameGeneric, "_part0.aig" ); 
    sprintf( pFileName1,  "%s%s",  pFileNameGeneric, "_part1.aig" ); 
    ABC_FREE( pFileNameGeneric );
    // dump files
    Ioa_WriteAiger( pPart0, pFileName0, 0, 0 );
    Ioa_WriteAiger( pPart1, pFileName1, 0, 0 );
    printf( "Demitering produced two files \"%s\" and \"%s\".\n", pFileName0, pFileName1 );
    // create two-level miter
//    pMiter = Saig_ManCreateMiterTwo( pPart0, pPart1, 2 );
//    Aig_ManDumpBlif( pMiter, "miter01.blif", NULL, NULL );
//    Aig_ManStop( pMiter );
//    printf( "The new miter is written into file \"%s\".\n", "miter01.blif" );
    Aig_ManStop( pPart0 );
    Aig_ManStop( pPart1 );
    Aig_ManStop( pMan );
    return 1;
} 

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkDarDemiterDual( Abc_Ntk_t * pNtk, int fVerbose )
{ 
    char * pFileNameGeneric, pFileName0[1000], pFileName1[1000];
    Aig_Man_t * pMan, * pPart0, * pPart1;//, * pMiter;
    if ( (Abc_NtkPoNum(pNtk) & 1) )
    {
        printf( "The number of POs should be even.\n" );
        return 0;
    }
    // derive the AIG manager
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
    {
        printf( "Converting network into AIG has failed.\n" );
        return 0;
    }
//    if ( !Saig_ManDemiterSimple( pMan, &pPart0, &pPart1 ) )
    if ( !Saig_ManDemiterDual( pMan, &pPart0, &pPart1 ) )
    {
        printf( "Demitering has failed.\n" );
        return 0;
    }
    // create new AIG
    ABC_FREE( pPart0->pName );
    pPart0->pName = Abc_UtilStrsav( "part0" );
    // create new AIGs
    ABC_FREE( pPart1->pName );
    pPart1->pName = Abc_UtilStrsav( "part1" );
    // create file names
    pFileNameGeneric = Extra_FileNameGeneric( pNtk->pSpec );
    sprintf( pFileName0,  "%s%s",  pFileNameGeneric, "_part0.aig" ); 
    sprintf( pFileName1,  "%s%s",  pFileNameGeneric, "_part1.aig" ); 
    ABC_FREE( pFileNameGeneric );
    Ioa_WriteAiger( pPart0, pFileName0, 0, 0 );
    Ioa_WriteAiger( pPart1, pFileName1, 0, 0 );
    printf( "Demitering produced two files \"%s\" and \"%s\".\n", pFileName0, pFileName1 );
    // dump files
    if ( fVerbose )
    {
//        printf( "Init:  " );
        Aig_ManPrintStats( pMan );
//        printf( "Part1: " );
        Aig_ManPrintStats( pPart0 );
//        printf( "Part2: " );
        Aig_ManPrintStats( pPart1 );
    }
    // create two-level miter
//    pMiter = Saig_ManCreateMiterTwo( pPart0, pPart1, 2 );
//    Aig_ManDumpBlif( pMiter, "miter01.blif", NULL, NULL );
//    Aig_ManStop( pMiter );
//    printf( "The new miter is written into file \"%s\".\n", "miter01.blif" );
    Aig_ManStop( pPart0 );
    Aig_ManStop( pPart1 );
    Aig_ManStop( pMan );
    return 1;
} 
 
/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkDarProve( Abc_Ntk_t * pNtk, Fra_Sec_t * pSecPar, int nBmcFramesMax, int nBmcConfMax )
{
    Aig_Man_t * pMan;
    int iFrame = -1, RetValue = -1, clkTotal = clock();
    if ( pSecPar->fTryComb || Abc_NtkLatchNum(pNtk) == 0 )
    {
        Prove_Params_t Params, * pParams = &Params;
        Abc_Ntk_t * pNtkComb;
        int RetValue, clk = clock();
        if ( Abc_NtkLatchNum(pNtk) == 0 )
            printf( "The network has no latches. Running CEC.\n" );
        // create combinational network
        pNtkComb = Abc_NtkDup( pNtk );
        Abc_NtkMakeComb( pNtkComb, 1 );
        // solve it using combinational equivalence checking
        Prove_ParamsSetDefault( pParams );
        pParams->fVerbose = 1;
        RetValue = Abc_NtkIvyProve( &pNtkComb, pParams );
        // transfer model if given
//        pNtk->pModel = pNtkComb->pModel; pNtkComb->pModel = NULL;
        if ( RetValue == 0  && (Abc_NtkLatchNum(pNtk) == 0) )
        {
            pNtk->pModel = pNtkComb->pModel; pNtkComb->pModel = NULL;
            printf( "Networks are not equivalent.\n" );
            ABC_PRT( "Time", clock() - clk );
            if ( pSecPar->fReportSolution )
            {
                printf( "SOLUTION: FAIL       " );
                ABC_PRT( "Time", clock() - clkTotal );
            }
            return RetValue;
        }
        Abc_NtkDelete( pNtkComb );
        // return the result, if solved
        if ( RetValue == 1 )
        {
            printf( "Networks are equivalent after CEC.   " );
            ABC_PRT( "Time", clock() - clk );
            if ( pSecPar->fReportSolution )
            {
            printf( "SOLUTION: PASS       " );
            ABC_PRT( "Time", clock() - clkTotal );
            }
            return RetValue;
        }
    }
    // derive the AIG manager
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
    {
        printf( "Converting miter into AIG has failed.\n" );
        return -1;
    }
    assert( pMan->nRegs > 0 );

    if ( pSecPar->fTryBmc )
    {
        RetValue = Saig_BmcPerform( pMan, 0, nBmcFramesMax, 2000, 0, nBmcConfMax, 0, pSecPar->fVerbose, 0, &iFrame );
        if ( RetValue == 0 )
        {
            printf( "Networks are not equivalent.\n" );
            if ( pSecPar->fReportSolution )
            {
                printf( "SOLUTION: FAIL       " );
                ABC_PRT( "Time", clock() - clkTotal );
            }
            // return the counter-example generated
            ABC_FREE( pNtk->pModel );
            ABC_FREE( pNtk->pSeqModel );
            pNtk->pSeqModel = pMan->pSeqModel; pMan->pSeqModel = NULL;
            Aig_ManStop( pMan );
            return RetValue;
        }
    } 
    // perform verification
    if ( pSecPar->fUseNewProver )
    {
        RetValue = Ssw_SecGeneralMiter( pMan, NULL );
    }
    else
    {
        RetValue = Fra_FraigSec( pMan, pSecPar, NULL );
        ABC_FREE( pNtk->pModel );
        ABC_FREE( pNtk->pSeqModel );
        pNtk->pSeqModel = pMan->pSeqModel; pMan->pSeqModel = NULL;
        if ( pNtk->pSeqModel )
        {
            Abc_Cex_t * pCex = pNtk->pSeqModel;
            printf( "Output %d asserted in frame %d (use \"write_counter\" to dump a witness).\n", pCex->iPo, pCex->iFrame );
            if ( !Saig_ManVerifyCex( pMan, pNtk->pSeqModel ) )
                printf( "Abc_NtkDarProve(): Counter-example verification has FAILED.\n" );
        }
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
int Abc_NtkDarSec( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, Fra_Sec_t * pSecPar )
{
//    Fraig_Params_t Params;
    Aig_Man_t * pMan;
    Abc_Ntk_t * pMiter;//, * pTemp;
    int RetValue;
 
    // get the miter of the two networks
    pMiter = Abc_NtkMiter( pNtk1, pNtk2, 0, 0, 0, 0 );
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
        pMiter->pModel = Abc_NtkVerifyGetCleanModel( pMiter, pSecPar->nFramesMax );
//        Abc_NtkVerifyReportErrorSeq( pNtk1, pNtk2, pMiter->pModel, pSecPar->nFramesMax );
        ABC_FREE( pMiter->pModel );
        Abc_NtkDelete( pMiter );
        return 0;
    }
    if ( RetValue == 1 )
    {
        Abc_NtkDelete( pMiter );
        printf( "Networks are equivalent after structural hashing.\n" );
        return 1;
    }

    // commented out because sometimes the problem became non-inductive
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
        ABC_FREE( pMiter->pModel );
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
    RetValue = Fra_FraigSec( pMan, pSecPar, NULL );
    Aig_ManStop( pMan );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkDarPdr( Abc_Ntk_t * pNtk, Pdr_Par_t * pPars, Abc_Cex_t ** ppCex )
{
    int RetValue = -1, clk = clock();
    Aig_Man_t * pMan;
    *ppCex = NULL;
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
    {
        printf( "Converting network into AIG has failed.\n" );
        return -1;
    }
    // perform ORing the primary outputs
    if ( pPars->iOutput == -1 )
    {
        Aig_Man_t * pTemp = Saig_ManDupOrpos( pMan );
        RetValue = Pdr_ManSolve( pTemp, pPars, ppCex );
        if ( RetValue == 0 )
            (*ppCex)->iPo = Saig_ManFindFailedPoCex( pMan, *ppCex );
        Aig_ManStop( pTemp );
    }
    else
        RetValue = Pdr_ManSolve( pMan, pPars, ppCex );
    // output the result
    if ( RetValue == 1 )
        printf( "Property proved.  " );
    else if ( RetValue == 0 )
        printf( "Property DISPROVED in frame %d (use \"write_counter\" to dump a witness).  ", ppCex? (*ppCex)->iFrame : -1 );
    else if ( RetValue == -1 )
        printf( "Property UNDECIDED.  " );
    else
        assert( 0 );
ABC_PRT( "Time", clock() - clk );

    if ( *ppCex && !Saig_ManVerifyCex( pMan, *ppCex ) )
        printf( "Abc_NtkDarPdr(): Counter-example verification has FAILED.\n" );
    Aig_ManStop( pMan );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Performs BDD-based reachability analysis.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkDarAbSec( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nFrames, int fVerbose )
{
    Aig_Man_t * pMan1, * pMan2 = NULL;
    int RetValue;
    // derive AIG manager
    pMan1 = Abc_NtkToDar( pNtk1, 0, 1 );
    if ( pMan1 == NULL )
    {
        printf( "Converting miter into AIG has failed.\n" );
        return -1;
    }
    assert( Aig_ManRegNum(pMan1) > 0 );
    // derive AIG manager
    if ( pNtk2 )
    {
        pMan2 = Abc_NtkToDar( pNtk2, 0, 1 );
        if ( pMan2 == NULL )
        {
            Aig_ManStop( pMan1 );
            printf( "Converting miter into AIG has failed.\n" );
            return -1;
        }
        assert( Aig_ManRegNum(pMan2) > 0 );
        if ( Saig_ManPiNum(pMan1) != Saig_ManPiNum(pMan2) )
        {
            Aig_ManStop( pMan1 );
            Aig_ManStop( pMan2 );
            printf( "The networks have different number of PIs.\n" );
            return -1;
        }
        if ( Saig_ManPoNum(pMan1) != Saig_ManPoNum(pMan2) )
        {
            Aig_ManStop( pMan1 );
            Aig_ManStop( pMan2 );
            printf( "The networks have different number of POs.\n" );
            return -1;
        }
        if ( Aig_ManRegNum(pMan1) != Aig_ManRegNum(pMan2) )
        {
            Aig_ManStop( pMan1 );
            Aig_ManStop( pMan2 );
            printf( "The networks have different number of flops.\n" );
            return -1;
        }
    }
    // perform verification
    RetValue = Ssw_SecSpecialMiter( pMan1, pMan2, nFrames, fVerbose );
    Aig_ManStop( pMan1 );
    if ( pMan2 )
        Aig_ManStop( pMan2 );
    return RetValue;
}


/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkDarSimSec( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, Ssw_Pars_t * pPars )
{
    Aig_Man_t * pMan1, * pMan2 = NULL;
    int RetValue;
    // derive AIG manager
    pMan1 = Abc_NtkToDar( pNtk1, 0, 1 );
    if ( pMan1 == NULL )
    {
        printf( "Converting miter into AIG has failed.\n" );
        return -1;
    }
    assert( Aig_ManRegNum(pMan1) > 0 );
    // derive AIG manager
    if ( pNtk2 )
    {
        pMan2 = Abc_NtkToDar( pNtk2, 0, 1 );
        if ( pMan2 == NULL )
        {
            printf( "Converting miter into AIG has failed.\n" );
            return -1;
        }
        assert( Aig_ManRegNum(pMan2) > 0 );
    }

    // perform verification
    RetValue = Ssw_SecWithSimilarity( pMan1, pMan2, pPars );
    Aig_ManStop( pMan1 );
    if ( pMan2 )
        Aig_ManStop( pMan2 );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarMatch( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nDist, int fVerbose )
{
    extern Vec_Int_t * Saig_StrSimPerformMatching( Aig_Man_t * p0, Aig_Man_t * p1, int nDist, int fVerbose, Aig_Man_t ** ppMiter );
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan1, * pMan2 = NULL, * pManRes;
    Vec_Int_t * vPairs;
    assert( Abc_NtkIsStrash(pNtk1) );
    // derive AIG manager
    pMan1 = Abc_NtkToDar( pNtk1, 0, 1 );
    if ( pMan1 == NULL )
    {
        printf( "Converting miter into AIG has failed.\n" );
        return NULL;
    }
    assert( Aig_ManRegNum(pMan1) > 0 );
    // derive AIG manager
    if ( pNtk2 )
    {
        pMan2 = Abc_NtkToDar( pNtk2, 0, 1 );
        if ( pMan2 == NULL )
        {
            printf( "Converting miter into AIG has failed.\n" );
            return NULL;
        }
        assert( Aig_ManRegNum(pMan2) > 0 );
    }

    // perform verification
    vPairs = Saig_StrSimPerformMatching( pMan1, pMan2, nDist, 1, &pManRes );
    pNtkAig = Abc_NtkFromAigPhase( pManRes );
    if ( vPairs )
        Vec_IntFree( vPairs );
    if ( pManRes )
        Aig_ManStop( pManRes );
    Aig_ManStop( pMan1 );
    if ( pMan2 )
        Aig_ManStop( pMan2 );
    return pNtkAig;
}


/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarLatchSweep( Abc_Ntk_t * pNtk, int fLatchConst, int fLatchEqual, int fSaveNames, int fUseMvSweep, int nFramesSymb, int nFramesSatur, int fVerbose, int fVeryVerbose )
{
    extern void Aig_ManPrintControlFanouts( Aig_Man_t * p );
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan, * pTemp;
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return NULL;
    if ( fSaveNames )
    {
        Aig_ManSeqCleanup( pMan );
        if ( fLatchConst && pMan->nRegs )
            pMan = Aig_ManConstReduce( pMan, fUseMvSweep, nFramesSymb, nFramesSatur, fVerbose, fVeryVerbose );
        if ( fLatchEqual && pMan->nRegs )
            pMan = Aig_ManReduceLaches( pMan, fVerbose );
    }
    else
    {
        if ( pMan->vFlopNums )
            Vec_IntFree( pMan->vFlopNums );
        pMan->vFlopNums = NULL;
        pMan = Aig_ManScl( pTemp = pMan, fLatchConst, fLatchEqual, fUseMvSweep, nFramesSymb, nFramesSatur, fVerbose, fVeryVerbose );
        Aig_ManStop( pTemp );
    }

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
//    pMan = Aig_ManConstReduce( pMan, 1, 0 );

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
//    pMan = Aig_ManConstReduce( pMan, 1, 0 );

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

    pMan = Saig_ManRetimeForward( pTemp = pMan, nMaxIters, fVerbose );
    Aig_ManStop( pTemp );

//    pMan = Aig_ManReduceLaches( pMan, 1 );
//    pMan = Aig_ManConstReduce( pMan, 1, 0 );

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

    Aig_ManPrintStats(pMan);
    Saig_ManRetimeSteps( pMan, 1000, 1, 0 );
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
/*
Abc_Ntk_t * Abc_NtkDarHaigRecord( Abc_Ntk_t * pNtk, int nIters, int nSteps, int fRetimingOnly, int fAddBugs, int fUseCnf, int fVerbose )
{
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan, * pTemp;
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return NULL;
    if ( pMan->vFlopNums )
        Vec_IntFree( pMan->vFlopNums ); 
    pMan->vFlopNums = NULL;

    pMan = Saig_ManHaigRecord( pTemp = pMan, nIters, nSteps, fRetimingOnly, fAddBugs, fUseCnf, fVerbose );
    Aig_ManStop( pTemp );

    pNtkAig = Abc_NtkFromDarSeqSweep( pNtk, pMan );
    Aig_ManStop( pMan );
    return pNtkAig;
}
*/

/**Function*************************************************************

  Synopsis    [Performs random simulation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkDarSeqSim( Abc_Ntk_t * pNtk, int nFrames, int nWords, int TimeOut, int fNew, int fComb, int fMiter, int fVerbose )
{
    extern int Cec_ManSimulate( Aig_Man_t * pAig, int nWords, int nIters, int TimeLimit, int fMiter, int fVerbose );
    extern int Raig_ManSimulate( Aig_Man_t * pAig, int nWords, int nIters, int TimeLimit, int fMiter, int fVerbose );
    Aig_Man_t * pMan;
    Abc_Cex_t * pCex;
    int status, RetValue = -1, clk = clock();
    if ( Abc_NtkGetChoiceNum(pNtk) )
    {
        printf( "Removing %d choices from the AIG.\n", Abc_NtkGetChoiceNum(pNtk) );
        Abc_AigCleanup((Abc_Aig_t *)pNtk->pManFunc);
    }
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( fComb || Abc_NtkLatchNum(pNtk) == 0 )
    {
/*
        if ( Cec_ManSimulate( pMan, nWords, nFrames, TimeOut, fMiter, fVerbose ) )
        {
            pCex = pMan->pSeqModel;
            if ( pCex )
            {
            printf( "Simulation iterated %d times with %d words asserted output %d in frame %d. ", 
                nFrames, nWords, pCex->iPo, pCex->iFrame );
            status = Saig_ManVerifyCex( pMan, pCex );
            if ( status == 0 )
                printf( "Abc_NtkDarSeqSim(): Counter-example verification has FAILED.\n" );
            }
            ABC_FREE( pNtk->pModel );
            ABC_FREE( pNtk->pSeqModel );
            pNtk->pSeqModel = pCex;
            RetValue = 1;
        } 
        else
        {
            RetValue = 0;
            printf( "Simulation iterated %d times with %d words did not assert the outputs. ", 
                nFrames, nWords );
        }
*/
        printf( "Comb simulation is temporarily disabled.\n" );
    }
    else if ( fNew )
    {
/*
        if ( Raig_ManSimulate( pMan, nWords, nFrames, TimeOut, fVerbose ) )
        {
            if ( (pCex = pMan->pSeqModel) )
            {
                printf( "Simulation of %d frames with %d words asserted output %d in frame %d. ", 
                    nFrames, nWords, pCex->iPo, pCex->iFrame );
                status = Saig_ManVerifyCex( pMan, pCex );
                if ( status == 0 )
                    printf( "Abc_NtkDarSeqSim(): Counter-example verification has FAILED.\n" );
            }
            ABC_FREE( pNtk->pModel );
            ABC_FREE( pNtk->pSeqModel );
            pNtk->pSeqModel = pCex; pMan->pSeqModel = NULL;
            RetValue = 1;
        }
        else
        {
            RetValue = 0;
            printf( "Simulation of %d frames with %d words did not assert the outputs. ", 
                nFrames, nWords );
        }
*/
/*
        Fsim_ParSim_t Pars, * pPars = &Pars;
        Fsim_ManSetDefaultParamsSim( pPars );
        pPars->nWords = nWords;
        pPars->nIters = nFrames;
        pPars->TimeLimit = TimeOut;
        pPars->fCheckMiter = fMiter;
        pPars->fVerbose = fVerbose;
        if ( Fsim_ManSimulate( pMan, pPars ) )
        { 
            if ( (pCex = pMan->pSeqModel) )
            {
                printf( "Simulation of %d frames with %d words asserted output %d in frame %d. ", 
                    nFrames, nWords, pCex->iPo, pCex->iFrame );
                status = Saig_ManVerifyCex( pMan, pCex );
                if ( status == 0 )
                    printf( "Abc_NtkDarSeqSim(): Counter-example verification has FAILED.\n" );
            }
            ABC_FREE( pNtk->pModel );
            ABC_FREE( pNtk->pSeqModel );
            pNtk->pSeqModel = pCex; pMan->pSeqModel = NULL;
            RetValue = 1;
        }
        else
        {
            RetValue = 0;
            printf( "Simulation of %d frames with %d words did not assert the outputs. ", 
                nFrames, nWords );
        }
*/ 
        Gia_Man_t * pGia;
        Gia_ParSim_t Pars, * pPars = &Pars;
        Gia_ManSimSetDefaultParams( pPars );
        pPars->nWords = nWords;
        pPars->nIters = nFrames;
        pPars->TimeLimit = TimeOut;
        pPars->fCheckMiter = fMiter;
        pPars->fVerbose = fVerbose;
        pGia = Gia_ManFromAig( pMan );
        if ( Gia_ManSimSimulate( pGia, pPars ) )
        { 
            if ( pGia->pCexSeq )
            {
                printf( "Simulation of %d frames with %d words asserted output %d in frame %d. ", 
                    nFrames, nWords, pGia->pCexSeq->iPo, pGia->pCexSeq->iFrame );
                status = Saig_ManVerifyCex( pMan, pGia->pCexSeq );
                if ( status == 0 )
                    printf( "Abc_NtkDarSeqSim(): Counter-example verification has FAILED.\n" );
            }
            ABC_FREE( pNtk->pModel );
            ABC_FREE( pNtk->pSeqModel );
            pNtk->pSeqModel = pGia->pCexSeq; pGia->pCexSeq = NULL;
            RetValue = 0;
        }
        else
        {
            printf( "Simulation of %d frames with %d words did not assert the outputs.    ", 
                nFrames, nWords );
        }
        Gia_ManStop( pGia );
    }
    else
    {
        Fra_Sml_t * pSml;
        pSml = Fra_SmlSimulateSeq( pMan, 0, nFrames, nWords, fMiter );
        if ( pSml->fNonConstOut )
        {
            pCex = Fra_SmlGetCounterExample( pSml );
            if ( pCex )
            {
                printf( "Simulation of %d frames with %d words asserted output %d in frame %d. ", 
                    nFrames, nWords, pCex->iPo, pCex->iFrame );
                status = Saig_ManVerifyCex( pMan, pCex );
                if ( status == 0 )
                    printf( "Abc_NtkDarSeqSim(): Counter-example verification has FAILED.\n" );
            }
            ABC_FREE( pNtk->pModel );
            ABC_FREE( pNtk->pSeqModel );
            pNtk->pSeqModel = pCex;
            RetValue = 0;
        }
        else
        {
            printf( "Simulation of %d frames with %d words did not assert the outputs.    ", 
                nFrames, nWords );
        }
        Fra_SmlStop( pSml );
/*
        if ( Raig_ManSimulate( pMan, nWords, nFrames, TimeOut, fMiter, fVerbose ) )
        {
            if ( (pCex = pMan->pSeqModel) )
            {
                printf( "Simulation of %d frames with %d words asserted output %d in frame %d. ", 
                    nFrames, nWords, pCex->iPo, pCex->iFrame );
                status = Saig_ManVerifyCex( pMan, pCex );
                if ( status == 0 )
                    printf( "Abc_NtkDarSeqSim(): Counter-example verification has FAILED.\n" );
            }
            ABC_FREE( pNtk->pModel );
            ABC_FREE( pNtk->pSeqModel );
            pNtk->pSeqModel = pCex; pMan->pSeqModel = NULL;
            RetValue = 1;
        }
        else
        {
            RetValue = 0;
            printf( "Simulation of %d frames with %d words did not assert the outputs. ", 
                nFrames, nWords );
        }
*/
    }
    ABC_PRT( "Time", clock() - clk );
    Aig_ManStop( pMan );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Performs random simulation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkDarSeqSim3( Abc_Ntk_t * pNtk, int nFrames, int nWords, int nBinSize, int nRounds, int nRandSeed, int TimeOut, int fVerbose )
{
    Aig_Man_t * pMan;
    int status, RetValue = -1, clk = clock();
    if ( Abc_NtkGetChoiceNum(pNtk) )
    {
        printf( "Removing %d choices from the AIG.\n", Abc_NtkGetChoiceNum(pNtk) );
        Abc_AigCleanup((Abc_Aig_t *)pNtk->pManFunc);
    }
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( Ssw_RarSimulate( pMan, nFrames, nWords, nBinSize, nRounds, nRandSeed, TimeOut, fVerbose ) == 0 )
    { 
        if ( pMan->pSeqModel )
        {
            printf( "Simulation of %d frames with %d words asserted output %d in frame %d. ", 
                nFrames, nWords, pMan->pSeqModel->iPo, pMan->pSeqModel->iFrame );
            status = Saig_ManVerifyCex( pMan, pMan->pSeqModel );
            if ( status == 0 )
                printf( "Abc_NtkDarSeqSim(): Counter-example verification has FAILED.\n" );
        }
        ABC_FREE( pNtk->pModel );
        ABC_FREE( pNtk->pSeqModel );
        pNtk->pSeqModel = pMan->pSeqModel; pMan->pSeqModel = NULL;
        RetValue = 0;
    }
    else
    {
//        printf( "Simulation of %d frames with %d words did not assert the outputs.    ", 
//            nFrames, nWords );
    }
    ABC_PRT( "Time", clock() - clk );
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

  Synopsis    [Performs targe enlargement.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarTempor( Abc_Ntk_t * pNtk, int nFrames, int TimeOut, int nConfLimit, int fUseBmc, int fUseTransSigs, int fVerbose, int fVeryVerbose )
{
    extern Aig_Man_t * Saig_ManTempor( Aig_Man_t * pAig, int nFrames, int TimeOut, int nConfLimit, int fUseBmc, int fUseTransSigs, int fVerbose, int fVeryVerbose );
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan, * pTemp;
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return NULL;
    pTemp = Saig_ManTempor( pMan, nFrames, TimeOut, nConfLimit, fUseBmc, fUseTransSigs, fVerbose, fVeryVerbose );
    Aig_ManStop( pMan );
    if ( pTemp == NULL )
        return Abc_NtkDup( pNtk );
    pNtkAig = Abc_NtkFromDarSeqSweep( pNtk, pTemp );
    Aig_ManStop( pTemp );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Performs induction for property only.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkDarInduction( Abc_Ntk_t * pNtk, int nFramesMax, int nConfMax, int fUnique, int fUniqueAll, int fGetCex, int fVerbose, int fVeryVerbose )
{ 
    Aig_Man_t * pMan;
    int clkTotal = clock();
    int RetValue;
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return -1;
    RetValue = Saig_ManInduction( pMan, nFramesMax, nConfMax, fUnique, fUniqueAll, fGetCex, fVerbose, fVeryVerbose );
    if ( RetValue == 1 )
    {
        printf( "Networks are equivalent.   " );
ABC_PRT( "Time", clock() - clkTotal );
    }
    else if ( RetValue == 0 )
    {
        printf( "Networks are NOT EQUIVALENT.   " );
ABC_PRT( "Time", clock() - clkTotal );
    }
    else
    {
        printf( "Networks are UNDECIDED.   " );
ABC_PRT( "Time", clock() - clkTotal );
    }
    if ( fGetCex )
    {
        ABC_FREE( pNtk->pModel );
        ABC_FREE( pNtk->pSeqModel );
        pNtk->pSeqModel = pMan->pSeqModel; pMan->pSeqModel = NULL;
    }
    Aig_ManStop( pMan );
    return RetValue;
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
    int i; //, clk = clock();
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
    // start the new network
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
//    ABC_PRT( "CNF", timeCnf );
//    ABC_PRT( "SAT", timeSat );
//    ABC_PRT( "Int", timeInt );
//    ABC_PRT( "Slow interpolation time", clock() - clk );

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
int Abc_NtkDarPrintCone( Abc_Ntk_t * pNtk )
{
    extern void Saig_ManPrintCones( Aig_Man_t * pAig );
    Aig_Man_t * pMan;
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return 0;
    assert( Aig_ManRegNum(pMan) > 0 );
    Saig_ManPrintCones( pMan );
    Aig_ManStop( pMan );
    return 1;
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
Abc_Ntk_t * Abc_NtkPhaseAbstract( Abc_Ntk_t * pNtk, int nFrames, int nPref, int fIgnore, int fPrint, int fVerbose )
{
    extern Aig_Man_t * Saig_ManPhaseAbstract( Aig_Man_t * p, Vec_Int_t * vInits, int nFrames, int nPref, int fIgnore, int fPrint, int fVerbose );
    Vec_Int_t * vInits;
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan, * pTemp;
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return NULL;
    vInits = Abc_NtkGetLatchValues(pNtk);
    pMan = Saig_ManPhaseAbstract( pTemp = pMan, vInits, nFrames, nPref, fIgnore, fPrint, fVerbose );
    Vec_IntFree( vInits );
    Aig_ManStop( pTemp );
    if ( pMan == NULL )
        return NULL;
    pNtkAig = Abc_NtkFromAigPhase( pMan );
//    pNtkAig->pName = Extra_UtilStrsav(pNtk->pName);
//    pNtkAig->pSpec = Extra_UtilStrsav(pNtk->pSpec);
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Performs phase abstraction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkPhaseFrameNum( Abc_Ntk_t * pNtk )
{
    extern int Saig_ManPhaseFrameNum( Aig_Man_t * p, Vec_Int_t * vInits );
    Vec_Int_t * vInits;
    Aig_Man_t * pMan;
    int nFrames;
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return 1;
    vInits = Abc_NtkGetLatchValues(pNtk);
    nFrames = Saig_ManPhaseFrameNum( pMan, vInits );
    Vec_IntFree( vInits );
    Aig_ManStop( pMan );
    return nFrames;
}

/**Function*************************************************************

  Synopsis    [Performs phase abstraction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarSynchOne( Abc_Ntk_t * pNtk, int nWords, int fVerbose )
{
    extern Aig_Man_t * Saig_SynchSequenceApply( Aig_Man_t * pAig, int nWords, int fVerbose );
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan, * pTemp;
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return NULL;
    pMan = Saig_SynchSequenceApply( pTemp = pMan, nWords, fVerbose );
    Aig_ManStop( pTemp );
    if ( pMan == NULL )
        return NULL;
    pNtkAig = Abc_NtkFromDar( pNtk, pMan );
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Performs phase abstraction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarSynch( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nWords, int fVerbose )
{
    extern Aig_Man_t * Saig_Synchronize( Aig_Man_t * pAig1, Aig_Man_t * pAig2, int nWords, int fVerbose );
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan1, * pMan2, * pMan;
    pMan1 = Abc_NtkToDar( pNtk1, 0, 1 );
    if ( pMan1 == NULL )
        return NULL;
    pMan2 = Abc_NtkToDar( pNtk2, 0, 1 );
    if ( pMan2 == NULL )
    {
        Aig_ManStop( pMan1 );
        return NULL;
    }
    pMan = Saig_Synchronize( pMan1, pMan2, nWords, fVerbose );
    Aig_ManStop( pMan1 );
    Aig_ManStop( pMan2 );
    if ( pMan == NULL )
        return NULL;
    pNtkAig = Abc_NtkFromAigPhase( pMan );
//    pNtkAig->pName = Extra_UtilStrsav("miter");
//    pNtkAig->pSpec = NULL;
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Performs phase abstraction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarClockGate( Abc_Ntk_t * pNtk, Abc_Ntk_t * pCare, Cgt_Par_t * pPars )
{
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan1, * pMan2 = NULL, * pMan;
    pMan1 = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan1 == NULL )
        return NULL;
    if ( pCare )
    {
        pMan2 = Abc_NtkToDar( pCare, 0, 0 );
        if ( pMan2 == NULL )
        {
            Aig_ManStop( pMan1 );
            return NULL;
        }
    }
    pMan = Cgt_ClockGating( pMan1, pMan2, pPars );
    Aig_ManStop( pMan1 );
    if ( pMan2 )
        Aig_ManStop( pMan2 );
    if ( pMan == NULL )
        return NULL;
    pNtkAig = Abc_NtkFromDar( pNtk, pMan );
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Performs phase abstraction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarExtWin( Abc_Ntk_t * pNtk, int nObjId, int nDist, int fVerbose )
{
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan1, * pMan;
    Aig_Obj_t * pObj;
    pMan1 = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan1 == NULL )
        return NULL;
    if ( nObjId == -1 )
    {
        pObj = Saig_ManFindPivot( pMan1 );
        printf( "Selected object %d as a window pivot.\n", pObj->Id );
    }
    else
    {
        if ( nObjId >= Aig_ManObjNumMax(pMan1) )
        {
            Aig_ManStop( pMan1 );
            printf( "The ID is too large.\n" );
            return NULL;
        }
        pObj = Aig_ManObj( pMan1, nObjId );
        if ( pObj == NULL )
        {
            Aig_ManStop( pMan1 );
            printf( "Object with ID %d does not exist.\n", nObjId );
            return NULL;
        }
        if ( !Saig_ObjIsLo(pMan1, pObj) && !Aig_ObjIsNode(pObj) )
        {
            Aig_ManStop( pMan1 );
            printf( "Object with ID %d is not a node or reg output.\n", nObjId );
            return NULL;
        }
    }
    pMan = Saig_ManWindowExtract( pMan1, pObj, nDist );
    Aig_ManStop( pMan1 );
    if ( pMan == NULL )
        return NULL;
    pNtkAig = Abc_NtkFromAigPhase( pMan );
    pNtkAig->pName = Extra_UtilStrsav(pNtk->pName);
    pNtkAig->pSpec = Extra_UtilStrsav(pNtk->pSpec);
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Performs phase abstraction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarInsWin( Abc_Ntk_t * pNtk, Abc_Ntk_t * pCare, int nObjId, int nDist, int fVerbose )
{
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan1, * pMan2 = NULL, * pMan;
    Aig_Obj_t * pObj;
    pMan1 = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan1 == NULL )
        return NULL;
    if ( nObjId == -1 )
    {
        pObj = Saig_ManFindPivot( pMan1 );
        printf( "Selected object %d as a window pivot.\n", pObj->Id );
    }
    else
    {
        if ( nObjId >= Aig_ManObjNumMax(pMan1) )
        {
            Aig_ManStop( pMan1 );
            printf( "The ID is too large.\n" );
            return NULL;
        }
        pObj = Aig_ManObj( pMan1, nObjId );
        if ( pObj == NULL )
        {
            Aig_ManStop( pMan1 );
            printf( "Object with ID %d does not exist.\n", nObjId );
            return NULL;
        }
        if ( !Saig_ObjIsLo(pMan1, pObj) && !Aig_ObjIsNode(pObj) )
        {
            Aig_ManStop( pMan1 );
            printf( "Object with ID %d is not a node or reg output.\n", nObjId );
            return NULL;
        }
    }
    if ( pCare )
    {
        pMan2 = Abc_NtkToDar( pCare, 0, 0 );
        if ( pMan2 == NULL )
        {
            Aig_ManStop( pMan1 );
            return NULL;
        }
    }
    pMan = Saig_ManWindowInsert( pMan1, pObj, nDist, pMan2 );
    Aig_ManStop( pMan1 );
    if ( pMan2 )
        Aig_ManStop( pMan2 );
    if ( pMan == NULL )
        return NULL;
    pNtkAig = Abc_NtkFromDarSeqSweep( pNtk, pMan );
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Performs phase abstraction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarFrames( Abc_Ntk_t * pNtk, int nPrefix, int nFrames, int fInit, int fVerbose )
{
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan, * pTemp;
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return NULL;
    pMan = Saig_ManTimeframeSimplify( pTemp = pMan, nPrefix, nFrames, fInit, fVerbose );
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

  Synopsis    [Performs phase abstraction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarCleanupAig( Abc_Ntk_t * pNtk, int fCleanupPis, int fCleanupPos, int fVerbose )
{
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan;
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return NULL;
    if ( fCleanupPis )
    {
        int Temp = Aig_ManPiCleanup( pMan );
        if ( fVerbose )
            printf( "Cleanup removed %d primary inputs without fanout.\n", Temp );                                                                     
    }
    if ( fCleanupPos )
    {
        int Temp = Aig_ManPoCleanup( pMan );
        if ( fVerbose )
            printf( "Cleanup removed %d primary outputs driven by const-0.\n", Temp );                                                                     
    }
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
int Abc_NtkDarReach( Abc_Ntk_t * pNtk, Saig_ParBbr_t * pPars )
{
    Aig_Man_t * pMan;
    int RetValue;
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return -1;
    RetValue = Aig_ManVerifyUsingBdds( pMan, pPars );
    ABC_FREE( pNtk->pModel );
    ABC_FREE( pNtk->pSeqModel );
    pNtk->pSeqModel = pMan->pSeqModel; pMan->pSeqModel = NULL;
    Aig_ManStop( pMan );
    return RetValue;
}

ABC_NAMESPACE_IMPL_END

#include "src/map/amap/amap.h"
#include "src/map/mio/mio.h"

ABC_NAMESPACE_IMPL_START


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Amap_ManProduceNetwork( Abc_Ntk_t * pNtk, Vec_Ptr_t * vMapping )
{
//    extern void * Abc_FrameReadLibGen();
    Mio_Library_t * pLib = (Mio_Library_t *)Abc_FrameReadLibGen();
    Amap_Out_t * pRes;
    Vec_Ptr_t * vNodesNew;
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pNodeNew, * pFaninNew;
    int i, k, iPis, iPos, nDupGates;
    // make sure gates exist in the current library
    Vec_PtrForEachEntry( Amap_Out_t *, vMapping, pRes, i )
        if ( pRes->pName && Mio_LibraryReadGateByName( pLib, pRes->pName ) == NULL )
        {
            printf( "Current library does not contain gate \"%s\".\n", pRes->pName );
            return NULL;
        }
    // create the network
    pNtkNew = Abc_NtkStartFrom( pNtk, ABC_NTK_LOGIC, ABC_FUNC_MAP );
    pNtkNew->pManFunc = pLib;
    iPis = iPos = 0;
    vNodesNew = Vec_PtrAlloc( Vec_PtrSize(vMapping) );
    Vec_PtrForEachEntry( Amap_Out_t *, vMapping, pRes, i )
    {
        if ( pRes->Type == -1 )
            pNodeNew = Abc_NtkCi( pNtkNew, iPis++ );
        else if ( pRes->Type == 1 )
            pNodeNew = Abc_NtkCo( pNtkNew, iPos++ );
        else
        {
            pNodeNew = Abc_NtkCreateNode( pNtkNew );
            pNodeNew->pData = Mio_LibraryReadGateByName( pLib, pRes->pName );
        }
        for ( k = 0; k < pRes->nFans; k++ )
        {
            pFaninNew = (Abc_Obj_t *)Vec_PtrEntry( vNodesNew, pRes->pFans[k] );
            Abc_ObjAddFanin( pNodeNew, pFaninNew );
        }
        Vec_PtrPush( vNodesNew, pNodeNew );
    }
    Vec_PtrFree( vNodesNew );
    assert( iPis == Abc_NtkCiNum(pNtkNew) );
    assert( iPos == Abc_NtkCoNum(pNtkNew) );
    // decouple the PO driver nodes to reduce the number of levels
    nDupGates = Abc_NtkLogicMakeSimpleCos( pNtkNew, 0 );
//    if ( nDupGates && Map_ManReadVerbose(pMan) )
//        printf( "Duplicated %d gates to decouple the CO drivers.\n", nDupGates );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarAmap( Abc_Ntk_t * pNtk, Amap_Par_t * pPars )
{
    extern Vec_Ptr_t * Amap_ManTest( Aig_Man_t * pAig, Amap_Par_t * pPars );
    Vec_Ptr_t * vMapping;
    Abc_Ntk_t * pNtkAig = NULL;
    Aig_Man_t * pMan;
    Aig_MmFlex_t * pMem;

    assert( Abc_NtkIsStrash(pNtk) );
    // convert to the AIG manager
    pMan = Abc_NtkToDarChoices( pNtk );
    if ( pMan == NULL )
        return NULL;

    // perform computation
    vMapping = Amap_ManTest( pMan, pPars );
    Aig_ManStop( pMan );
    if ( vMapping == NULL )
        return NULL;
    pMem = (Aig_MmFlex_t *)Vec_PtrPop( vMapping );
    pNtkAig = Amap_ManProduceNetwork( pNtk, vMapping );
    Aig_MmFlexStop( pMem, 0 );
    Vec_PtrFree( vMapping );

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

  Synopsis    [Performs BDD-based reachability analysis.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkDarConstr( Abc_Ntk_t * pNtk, int nFrames, int nConfs, int nProps, int fStruct, int fOldAlgo, int fVerbose )
{
    Aig_Man_t * pMan;//, * pMan2;//, * pTemp;
    assert( Abc_NtkIsStrash(pNtk) );
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return;
    if ( fStruct )
        Saig_ManDetectConstrTest( pMan );
    else
        Saig_ManDetectConstrFuncTest( pMan, nFrames, nConfs, nProps, fOldAlgo, fVerbose );
    Aig_ManStop( pMan );
}

/**Function*************************************************************

  Synopsis    [Performs BDD-based reachability analysis.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarOutdec( Abc_Ntk_t * pNtk, int nLits, int fVerbose )
{
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan, * pTemp;
    assert( Abc_NtkIsStrash(pNtk) );
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return NULL;
    pMan = Saig_ManDecPropertyOutput( pTemp = pMan, nLits, fVerbose );
    Aig_ManStop( pTemp );
    if ( pMan == NULL )
        return NULL;
    pNtkAig = Abc_NtkFromAigPhase( pMan );
    pNtkAig->pName = Extra_UtilStrsav(pMan->pName);
    pNtkAig->pSpec = Extra_UtilStrsav(pMan->pSpec);
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Performs BDD-based reachability analysis.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarUnfold( Abc_Ntk_t * pNtk, int nFrames, int nConfs, int nProps, int fStruct, int fOldAlgo, int fVerbose )
{
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan, * pTemp;
    assert( Abc_NtkIsStrash(pNtk) );
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return NULL;
    if ( fStruct )
        pMan = Saig_ManDupUnfoldConstrs( pTemp = pMan );
    else
        pMan = Saig_ManDupUnfoldConstrsFunc( pTemp = pMan, nFrames, nConfs, nProps, fOldAlgo, fVerbose );
    Aig_ManStop( pTemp );
    if ( pMan == NULL )
        return NULL;
    pNtkAig = Abc_NtkFromAigPhase( pMan );
    pNtkAig->pName = Extra_UtilStrsav(pMan->pName);
    pNtkAig->pSpec = Extra_UtilStrsav(pMan->pSpec);
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Performs BDD-based reachability analysis.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarFold( Abc_Ntk_t * pNtk, int fCompl, int fVerbose )
{
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan, * pTemp;
    assert( Abc_NtkIsStrash(pNtk) );
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return NULL;
    pMan = Saig_ManDupFoldConstrsFunc( pTemp = pMan, fCompl, fVerbose );
    Aig_ManStop( pTemp );
    pNtkAig = Abc_NtkFromAigPhase( pMan );
    pNtkAig->pName = Extra_UtilStrsav(pMan->pName);
    pNtkAig->pSpec = Extra_UtilStrsav(pMan->pSpec);
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Performs BDD-based reachability analysis.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkDarConstrProfile( Abc_Ntk_t * pNtk, int fVerbose )
{
    extern int Ssw_ManProfileConstraints( Aig_Man_t * p, int nWords, int nFrames, int fVerbose );
    extern Vec_Int_t * Saig_ManComputeSwitchProbs( Aig_Man_t * p, int nFrames, int nPref, int fProbOne );
    Aig_Man_t * pMan;
//    Vec_Int_t * vProbOne;
//    Aig_Obj_t * pObj;
//    int i, Entry;
    assert( Abc_NtkIsStrash(pNtk) );
    assert( Abc_NtkConstrNum(pNtk) );
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return;
    // value in the init state
//    Abc_AigSetNodePhases( pNtk );
/*
    // derive probabilities
    vProbOne = Saig_ManComputeSwitchProbs( pMan, 48, 16, 1 );
    // iterate over the constraint outputs
    Saig_ManForEachPo( pMan, pObj, i )
    {
        Entry = Vec_IntEntry( vProbOne, Aig_ObjId(pObj) );
        if ( i < Saig_ManPoNum(pMan) - Saig_ManConstrNum(pMan) )
            printf( "Primary output :  ", i );
        else
            printf( "Constraint %3d :  ", i-(Saig_ManPoNum(pMan) - Saig_ManConstrNum(pMan)) );
        printf( "ProbOne = %f  ", Abc_Int2Float(Entry) );
        printf( "AllZeroValue = %d ", Aig_ObjPhase(pObj) );
        printf( "\n" );
    }
*/
    // double-check
    Ssw_ManProfileConstraints( pMan, 16, 64, 1 );
    printf( "TwoFrameSatValue = %d.\n", Ssw_ManSetConstrPhases(pMan, 2, NULL) );
    // clean up
//    Vec_IntFree( vProbOne );
    Aig_ManStop( pMan );
}

/**Function*************************************************************

  Synopsis    [Performs BDD-based reachability analysis.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkDarTest( Abc_Ntk_t * pNtk, int Num )
{
//    extern void Saig_ManDetectConstr( Aig_Man_t * p );
//    extern void Saig_ManDetectConstrFuncTest( Aig_Man_t * p );
//    extern void Saig_ManFoldConstrTest( Aig_Man_t * pAig );
    extern void Llb_ManComputeDomsTest( Aig_Man_t * pAig, int Num );



//    extern void Fsim_ManTest( Aig_Man_t * pAig );
    extern Vec_Int_t * Saig_StrSimPerformMatching( Aig_Man_t * p0, Aig_Man_t * p1, int nDist, int fVerbose, Aig_Man_t ** ppMiter );
//    Vec_Int_t * vPairs;
    Aig_Man_t * pMan;//, * pMan2;//, * pTemp;
    assert( Abc_NtkIsStrash(pNtk) );
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return;
/*
Aig_ManSetRegNum( pMan, pMan->nRegs );
Aig_ManPrintStats( pMan );
Saig_ManDumpBlif( pMan, "_temp_.blif" );
Aig_ManStop( pMan );
pMan = Saig_ManReadBlif( "_temp_.blif" );
Aig_ManPrintStats( pMan );
*/
/*
    Aig_ManSetRegNum( pMan, pMan->nRegs );
    pTemp = Ssw_SignalCorrespondeceTestPairs( pMan );
    Aig_ManStop( pTemp );
*/

/*
//    Ssw_SecSpecialMiter( pMan, NULL, 2, 1 );
    pMan2 = Aig_ManDupSimple(pMan);
    vPairs = Saig_StrSimPerformMatching( pMan, pMan2, 0, 1, NULL );
    Vec_IntFree( vPairs );
    Aig_ManStop( pMan );
    Aig_ManStop( pMan2 );
*/
//    Ioa_WriteAigerBufferTest( pMan, "test.aig", 0, 0 );
//    Saig_ManFoldConstrTest( pMan );
    {
    extern void Saig_ManBmcSectionsTest( Aig_Man_t * p );
    extern void Saig_ManBmcTerSimTest( Aig_Man_t * p );
    extern void Saig_ManBmcSupergateTest( Aig_Man_t * p );
    extern void Saig_ManBmcMappingTest( Aig_Man_t * p );
//    Saig_ManBmcSectionsTest( pMan );
//    Saig_ManBmcTerSimTest( pMan );
//    Saig_ManBmcSupergateTest( pMan );
//    Saig_ManBmcMappingTest( pMan );
    }

    {
//        void Pdr_ManEquivClasses( Aig_Man_t * pMan );
//        Pdr_ManEquivClasses( pMan );
    }

//    Llb_ManComputeDomsTest( pMan, Num );
    {
        extern void Llb_ManMinCutTest( Aig_Man_t * pMan, int Num );
        extern void Llb_BddStructAnalysis( Aig_Man_t * pMan );
        extern void Llb_NonlinExperiment( Aig_Man_t * pAig, int Num );
//        Llb_BddStructAnalysis( pMan );
        Llb_ManMinCutTest( pMan, Num );
//        Llb_NonlinExperiment( pMan, Num );
    }

//    Saig_MvManSimulate( pMan, 1 );
//    Saig_ManDetectConstr( pMan );
//    Saig_ManDetectConstrFuncTest( pMan );

//    Fsim_ManTest( pMan );
    Aig_ManStop( pMan );

}

/**Function*************************************************************

  Synopsis    [Performs BDD-based reachability analysis.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarTestNtk( Abc_Ntk_t * pNtk )
{
//    extern Aig_Man_t * Saig_ManDualRail( Aig_Man_t * p, int fMiter );

/*
    extern Aig_Man_t * Ssw_SignalCorrespondeceTestPairs( Aig_Man_t * pAig );

    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan, * pTemp;
    assert( Abc_NtkIsStrash(pNtk) );
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return NULL;

    Aig_ManSetRegNum( pMan, pMan->nRegs );
    pMan = Ssw_SignalCorrespondeceTestPairs( pTemp = pMan );
    Aig_ManStop( pTemp );
    if ( pMan == NULL )
        return NULL;

    pNtkAig = Abc_NtkFromAigPhase( pMan );
    pNtkAig->pName = Extra_UtilStrsav(pNtk->pName);
    pNtkAig->pSpec = Extra_UtilStrsav(pNtk->pSpec);
    Aig_ManStop( pMan );
    return pNtkAig;
*/
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan;//, * pTemp;
    assert( Abc_NtkIsStrash(pNtk) );
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
        return NULL;

/*
    Aig_ManSetRegNum( pMan, pMan->nRegs );
    pMan = Saig_ManDualRail( pTemp = pMan, 1 );
    Aig_ManStop( pTemp );
    if ( pMan == NULL )
        return NULL;

    pNtkAig = Abc_NtkFromAigPhase( pMan );
    pNtkAig->pName = Extra_UtilStrsav(pNtk->pName);
    pNtkAig->pSpec = Extra_UtilStrsav(pNtk->pSpec);
    Aig_ManStop( pMan );
*/

    pNtkAig = Abc_NtkFromDar( pNtk, pMan );
    Aig_ManStop( pMan );

    return pNtkAig;

}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

