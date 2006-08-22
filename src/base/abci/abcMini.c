/**CFile****************************************************************

  FileName    [abcMini.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Interface to the minimalistic AIG package.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcMini.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Aig_Man_t * Abc_NtkToAig( Abc_Ntk_t * pNtk );
static Abc_Ntk_t * Abc_NtkFromAig( Abc_Ntk_t * pNtkOld, Aig_Man_t * pMan );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkMiniBalance( Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan, * pTemp;
    assert( Abc_NtkIsStrash(pNtk) );
    // convert to the AIG manager
    pMan = Abc_NtkToAig( pNtk );
    if ( pMan == NULL )
        return NULL;
    if ( !Aig_ManCheck( pMan ) )
    {
        printf( "AIG check has failed.\n" );
        Aig_ManStop( pMan );
        return NULL;
    }
    // perform balance
    Aig_ManPrintStats( pMan );
    pMan = Aig_ManBalance( pTemp = pMan, 1 );
    Aig_ManStop( pTemp );
    Aig_ManPrintStats( pMan );
    // convert from the AIG manager
    pNtkAig = Abc_NtkFromAig( pNtk, pMan );
    if ( pNtkAig == NULL )
        return NULL;
    Aig_ManStop( pMan );
    // make sure everything is okay
    if ( !Abc_NtkCheck( pNtkAig ) )
    {
        printf( "Abc_NtkStrash: The network check has failed.\n" );
        Abc_NtkDelete( pNtkAig );
        return NULL;
    }
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Converts the network from the AIG manager into ABC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Abc_NtkToAig( Abc_Ntk_t * pNtk )
{
    Aig_Man_t * pMan;
    Abc_Obj_t * pObj;
    int i;
    // create the manager
    pMan = Aig_ManStart();
    // transfer the pointers to the basic nodes
    Abc_AigConst1(pNtk)->pCopy = (Abc_Obj_t *)Aig_ManConst1(pMan);
    Abc_NtkForEachCi( pNtk, pObj, i )
        pObj->pCopy = (Abc_Obj_t *)Aig_ObjCreatePi(pMan);
    // perform the conversion of the internal nodes (assumes DFS ordering)
    Abc_NtkForEachNode( pNtk, pObj, i )
        pObj->pCopy = (Abc_Obj_t *)Aig_And( pMan, (Aig_Obj_t *)Abc_ObjChild0Copy(pObj), (Aig_Obj_t *)Abc_ObjChild1Copy(pObj) );
    // create the POs
    Abc_NtkForEachCo( pNtk, pObj, i )
        Aig_ObjCreatePo( pMan, (Aig_Obj_t *)Abc_ObjChild0Copy(pObj) );
    Aig_ManCleanup( pMan );
    return pMan;
}

/**Function*************************************************************

  Synopsis    [Converts the network from the AIG manager into ABC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkFromAig( Abc_Ntk_t * pNtk, Aig_Man_t * pMan )
{
    Vec_Ptr_t * vNodes;
    Abc_Ntk_t * pNtkNew;
    Aig_Obj_t * pObj;
    int i;
    // perform strashing
    pNtkNew = Abc_NtkStartFrom( pNtk, ABC_NTK_STRASH, ABC_FUNC_AIG );
    // transfer the pointers to the basic nodes
    Aig_ManConst1(pMan)->pData = Abc_AigConst1(pNtkNew);
    Aig_ManForEachPi( pMan, pObj, i )
        pObj->pData = Abc_NtkCi(pNtkNew, i);
    // rebuild the AIG
    vNodes = Aig_ManDfs( pMan );
    Vec_PtrForEachEntry( vNodes, pObj, i )
        pObj->pData = Abc_AigAnd( pNtkNew->pManFunc, (Abc_Obj_t *)Aig_ObjChild0Copy(pObj), (Abc_Obj_t *)Aig_ObjChild1Copy(pObj) );
    Vec_PtrFree( vNodes );
    // connect the PO nodes
    Aig_ManForEachPo( pMan, pObj, i )
        Abc_ObjAddFanin( Abc_NtkCo(pNtkNew, i), (Abc_Obj_t *)Aig_ObjChild0Copy(pObj) );
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkFromAig(): Network check has failed.\n" );
    return pNtkNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


