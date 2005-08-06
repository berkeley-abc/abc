/**CFile****************************************************************

  FileName    [abcNetlist.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Transforms netlist into a logic network and vice versa.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcNetlist.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
 
////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Transform the netlist into a logic network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkLogic( Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkNew; 
    Abc_Obj_t * pObj, * pFanin;
    int i, k;
    assert( Abc_NtkIsNetlist(pNtk) );
    // start the network
    pNtkNew = Abc_NtkAlloc( ABC_NTK_LOGIC_SOP );
    // duplicate the name and the spec
    pNtkNew->pName = util_strsav(pNtk->pName);
    pNtkNew->pSpec = util_strsav(pNtk->pSpec);
    // clean the copy field
    Abc_NtkCleanCopy( pNtk );
    // create the PIs and point to them from the nets
    Abc_NtkForEachPi( pNtk, pObj, i )
        pObj->pCopy = Abc_NtkCreateTermPi( pNtkNew );
    // create the latches and point to them from the latch fanout nets
    Abc_NtkForEachLatch( pNtk, pObj, i )
        Abc_ObjFanout0(pObj)->pCopy = Abc_NtkDupObj(pNtkNew, pObj);
    // duplicate the nodes and point to them from the fanout nets
    Abc_NtkForEachNode( pNtk, pObj, i )
        Abc_ObjFanout0(pObj)->pCopy = Abc_NtkDupObj(pNtkNew, pObj);
    // reconnect the internal nodes in the new network
    Abc_NtkForEachNode( pNtk, pObj, i )
        Abc_ObjForEachFanin( pObj, pFanin, k )
            Abc_ObjAddFanin( pObj->pCopy, pFanin->pCopy );
    // create and connect the POs
    Abc_NtkForEachPo( pNtk, pObj, i )
    {
        if ( Abc_ObjFaninNum(pObj) == 0 )
            Abc_ObjAddFanin( Abc_NtkCreateTermPo(pNtkNew), pObj->pCopy );
        else
            Abc_ObjAddFanin( Abc_NtkCreateTermPo(pNtkNew), Abc_ObjFanin0(pObj)->pCopy );
    }
    // connect the latches
    Abc_NtkForEachLatch( pNtk, pObj, i )
        Abc_ObjAddFanin( pObj->pCopy, Abc_ObjFanin0(pObj)->pCopy );
    // add the latches to the PI/PO arrays to make them look at CIs/COs
    Abc_NtkForEachLatch( pNtk, pObj, i )
        Vec_PtrPush( pNtkNew->vPis, pObj->pCopy );
    Abc_NtkForEachLatch( pNtk, pObj, i )
        Vec_PtrPush( pNtkNew->vPos, pObj->pCopy );
    // transfer the names
    Abc_NtkCreateNameArrays( pNtk, pNtkNew );
    // duplicate EXDC 
    if ( pNtk->pExdc )
        pNtkNew->pExdc = Abc_NtkLogic( pNtk->pExdc );
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkLogic(): Network check has failed.\n" );
    return pNtkNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


