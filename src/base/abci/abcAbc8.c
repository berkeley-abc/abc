/**CFile****************************************************************

  FileName    [abcAbc8.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcAbc8.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "nwk.h"
#include "mfx.h"

#include "main.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Converts old ABC network into new ABC network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Nwk_Man_t * Abc_NtkToNtkNew( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vNodes;
    Nwk_Man_t * pNtkNew;
    Nwk_Obj_t * pObjNew;
    Abc_Obj_t * pObj, * pFanin;
    int i, k;
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        fprintf( stdout, "This is not a logic network.\n" );
        return 0;
    }
    // convert into the AIG
    if ( !Abc_NtkToAig(pNtk) )
    {
        fprintf( stdout, "Converting to AIGs has failed.\n" );
        return 0;
    }
    assert( Abc_NtkHasAig(pNtk) );
    // construct the network
    pNtkNew = Nwk_ManAlloc();
    pNtkNew->pName = Extra_UtilStrsav( pNtk->pName );
    pNtkNew->pSpec = Extra_UtilStrsav( pNtk->pSpec );
    Abc_NtkForEachCi( pNtk, pObj, i )
        pObj->pCopy = (Abc_Obj_t *)Nwk_ManCreateCi( pNtkNew, Abc_ObjFanoutNum(pObj) );
    vNodes = Abc_NtkDfs( pNtk, 1 );
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pObj, i )
    {
        pObjNew = Nwk_ManCreateNode( pNtkNew, Abc_ObjFaninNum(pObj), Abc_ObjFanoutNum(pObj) );
        Abc_ObjForEachFanin( pObj, pFanin, k )
            Nwk_ObjAddFanin( pObjNew, (Nwk_Obj_t *)pFanin->pCopy );
        pObjNew->pFunc = Hop_Transfer( (Hop_Man_t *)pNtk->pManFunc, pNtkNew->pManHop, (Hop_Obj_t *)pObj->pData, Abc_ObjFaninNum(pObj) );
        pObj->pCopy = (Abc_Obj_t *)pObjNew;
    }
    Vec_PtrFree( vNodes );
    Abc_NtkForEachCo( pNtk, pObj, i )
    {
        pObjNew = Nwk_ManCreateCo( pNtkNew );
        Nwk_ObjAddFanin( pObjNew, (Nwk_Obj_t *)Abc_ObjFanin0(pObj)->pCopy );
    }
//    if ( !Nwk_ManCheck( pNtkNew ) )
//        fprintf( stdout, "Abc_NtkToNtkNew(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Converts new ABC network into old ABC network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkFromNtkNew( Abc_Ntk_t * pNtkOld, Nwk_Man_t * pNtk )
{
    Vec_Ptr_t * vNodes;
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pObjNew, * pFaninNew;
    Nwk_Obj_t * pObj, * pFanin;
    int i, k;
    // construct the network
    pNtkNew = Abc_NtkAlloc( ABC_NTK_LOGIC, ABC_FUNC_AIG, 1 );
    pNtkNew->pName = Extra_UtilStrsav( pNtk->pName );
    pNtkNew->pSpec = Extra_UtilStrsav( pNtk->pSpec );
    Nwk_ManForEachCi( pNtk, pObj, i )
    {
        pObjNew = Abc_NtkCreatePi( pNtkNew );
        pObj->pCopy = (Nwk_Obj_t *)pObjNew;
        Abc_ObjAssignName( pObjNew, Abc_ObjName( Abc_NtkCi(pNtkOld, i) ), NULL );
    }
    vNodes = Nwk_ManDfs( pNtk );
    Vec_PtrForEachEntry( Nwk_Obj_t *, vNodes, pObj, i )
    {
        if ( !Nwk_ObjIsNode(pObj) )
            continue;
        pObjNew = Abc_NtkCreateNode( pNtkNew );
        Nwk_ObjForEachFanin( pObj, pFanin, k )
            Abc_ObjAddFanin( pObjNew, (Abc_Obj_t *)pFanin->pCopy );
        pObjNew->pData = Hop_Transfer( pNtk->pManHop, (Hop_Man_t *)pNtkNew->pManFunc, pObj->pFunc, Nwk_ObjFaninNum(pObj) );
        pObj->pCopy = (Nwk_Obj_t *)pObjNew;
    }
    Vec_PtrFree( vNodes );
    Nwk_ManForEachCo( pNtk, pObj, i )
    {
        pObjNew = Abc_NtkCreatePo( pNtkNew );
        if ( pObj->fInvert )
            pFaninNew = Abc_NtkCreateNodeInv( pNtkNew, (Abc_Obj_t *)Nwk_ObjFanin0(pObj)->pCopy );
        else
            pFaninNew = (Abc_Obj_t *)Nwk_ObjFanin0(pObj)->pCopy;
        Abc_ObjAddFanin( pObjNew, pFaninNew );
        Abc_ObjAssignName( pObjNew, Abc_ObjName( Abc_NtkCo(pNtkOld, i) ), NULL );
    }
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkFromNtkNew(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkNtkTest2( Abc_Ntk_t * pNtk ) 
{
    extern void Abc_NtkSupportSum( Abc_Ntk_t * pNtk );
    Abc_Ntk_t * pNtkNew;
    Nwk_Man_t * pMan;
    int clk;

clk = clock();
    Abc_NtkSupportSum( pNtk );
ABC_PRT( "Time", clock() - clk );

    pMan = Abc_NtkToNtkNew( pNtk );
clk = clock();
    Nwk_ManSupportSum( pMan );
ABC_PRT( "Time", clock() - clk );

    pNtkNew = Abc_NtkFromNtkNew( pNtk, pMan );
    Nwk_ManFree( pMan );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkNtkTest3( Abc_Ntk_t * pNtk ) 
{
    extern void Abc_NtkSupportSum( Abc_Ntk_t * pNtk );
    extern void *          Abc_FrameReadLibLut();                    

    Abc_Ntk_t * pNtkNew;
    Nwk_Man_t * pMan;
    int clk;

clk = clock();
    printf( "%6.2f\n", Abc_NtkDelayTraceLut( pNtk, 1 ) );
ABC_PRT( "Time", clock() - clk );

    pMan = Abc_NtkToNtkNew( pNtk );
    pMan->pLutLib = (If_Lib_t *)Abc_FrameReadLibLut();
clk = clock();
    printf( "%6.2f\n", Nwk_ManDelayTraceLut( pMan ) );
ABC_PRT( "Time", clock() - clk );

    pNtkNew = Abc_NtkFromNtkNew( pNtk, pMan );
    Nwk_ManFree( pMan );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkNtkTest4( Abc_Ntk_t * pNtk, If_Lib_t * pLutLib ) 
{

    Mfx_Par_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtkNew;
    Nwk_Man_t * pMan;
    pMan = Abc_NtkToNtkNew( pNtk );

    Mfx_ParsDefault( pPars );
    Mfx_Perform( pMan, pPars, pLutLib );

    pNtkNew = Abc_NtkFromNtkNew( pNtk, pMan );
    Nwk_ManFree( pMan );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkNtkTest( Abc_Ntk_t * pNtk, If_Lib_t * pLutLib ) 
{
    Vec_Ptr_t * vNodes;
    extern Vec_Ptr_t * Nwk_ManRetimeCutForward( Nwk_Man_t * pMan, int nLatches, int fVerbose );
    extern Vec_Ptr_t * Nwk_ManRetimeCutBackward( Nwk_Man_t * pMan, int nLatches, int fVerbose );

    Abc_Ntk_t * pNtkNew;
    Nwk_Man_t * pMan;
    pMan = Abc_NtkToNtkNew( pNtk );

    vNodes = Nwk_ManRetimeCutBackward( pMan, Abc_NtkLatchNum(pNtk), 1 );
//    vNodes = Nwk_ManRetimeCutForward( pMan, Abc_NtkLatchNum(pNtk), 1 );
    Vec_PtrFree( vNodes );

    pNtkNew = Abc_NtkFromNtkNew( pNtk, pMan );
    Nwk_ManFree( pMan );
    return pNtkNew;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

