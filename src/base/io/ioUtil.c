/**CFile****************************************************************

  FileName    [ioUtil.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Procedures to write the network in BENCH format.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ioUtil.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "io.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates PI terminal and net.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Io_ReadCreatePi( Abc_Ntk_t * pNtk, char * pName )
{
    Abc_Obj_t * pNet, * pTerm;
    // get the PI net
    pNet  = Abc_NtkFindNet( pNtk, pName );
    if ( pNet )
        printf( "Warning: PI \"%s\" appears twice in the list.\n", pName );
    pNet  = Abc_NtkFindOrCreateNet( pNtk, pName );
    // add the PI node
    pTerm = Abc_NtkCreatePi( pNtk );
    Abc_ObjAddFanin( pNet, pTerm );
    return pTerm;
}

/**Function*************************************************************

  Synopsis    [Creates PO terminal and net.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Io_ReadCreatePo( Abc_Ntk_t * pNtk, char * pName )
{
    Abc_Obj_t * pNet, * pTerm;
    // get the PO net
    pNet  = Abc_NtkFindNet( pNtk, pName );
    if ( pNet && Abc_ObjFaninNum(pNet) == 0 )
        printf( "Warning: PO \"%s\" appears twice in the list.\n", pName );
    pNet  = Abc_NtkFindOrCreateNet( pNtk, pName );
    // add the PO node
    pTerm = Abc_NtkCreatePo( pNtk );
    Abc_ObjAddFanin( pTerm, pNet );
    return pTerm;
}

/**Function*************************************************************

  Synopsis    [Create a latch with the given input/output.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Io_ReadCreateLatch( Abc_Ntk_t * pNtk, char * pNetLI, char * pNetLO )
{
    Abc_Obj_t * pLatch, * pNet;
    // create a new latch and add it to the network
    pLatch = Abc_NtkCreateLatch( pNtk );
    // get the LI net
    pNet = Abc_NtkFindOrCreateNet( pNtk, pNetLI );
    Abc_ObjAddFanin( pLatch, pNet );
    // get the LO net
    pNet = Abc_NtkFindOrCreateNet( pNtk, pNetLO );
    Abc_ObjAddFanin( pNet, pLatch );
    return pLatch;
}

/**Function*************************************************************

  Synopsis    [Create node and the net driven by it.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Io_ReadCreateNode( Abc_Ntk_t * pNtk, char * pNameOut, char * pNamesIn[], int nInputs )
{
    Abc_Obj_t * pNet, * pNode;
    int i;
    // create a new node 
    pNode = Abc_NtkCreateNode( pNtk );
    // add the fanin nets
    for ( i = 0; i < nInputs; i++ )
    {
        pNet = Abc_NtkFindOrCreateNet( pNtk, pNamesIn[i] );
        Abc_ObjAddFanin( pNode, pNet );
    }
    // add the fanout net
    pNet = Abc_NtkFindOrCreateNet( pNtk, pNameOut );
    Abc_ObjAddFanin( pNet, pNode );
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Create a constant 0 node driving the net with this name.]

  Description [Assumes that the net already exists.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Io_ReadCreateConst( Abc_Ntk_t * pNtk, char * pName, bool fConst1 )
{
    Abc_Obj_t * pNet, * pTerm;
    pTerm = fConst1? Abc_NodeCreateConst1(pNtk) : Abc_NodeCreateConst0(pNtk);
    pNet  = Abc_NtkFindNet(pNtk, pName);    assert( pNet );
    Abc_ObjAddFanin( pNet, pTerm );
    return pTerm;
}

/**Function*************************************************************

  Synopsis    [Create an inverter or buffer for the given net.]

  Description [Assumes that the nets already exist.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Io_ReadCreateInv( Abc_Ntk_t * pNtk, char * pNameIn, char * pNameOut )
{
    Abc_Obj_t * pNet, * pNode;
    pNet  = Abc_NtkFindNet(pNtk, pNameIn);     assert( pNet );
    pNode = Abc_NodeCreateInv(pNtk, pNet);
    pNet  = Abc_NtkFindNet(pNtk, pNameOut);    assert( pNet );
    Abc_ObjAddFanin( pNet, pNode );
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Create an inverter or buffer for the given net.]

  Description [Assumes that the nets already exist.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Io_ReadCreateBuf( Abc_Ntk_t * pNtk, char * pNameIn, char * pNameOut )
{
    Abc_Obj_t * pNet, * pNode;
    pNet  = Abc_NtkFindNet(pNtk, pNameIn);     assert( pNet );
    pNode = Abc_NodeCreateBuf(pNtk, pNet);
    pNet  = Abc_NtkFindNet(pNtk, pNameOut);    assert( pNet );
    Abc_ObjAddFanin( pNet, pNode );
    return pNet;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


