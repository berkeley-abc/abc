/**CFile****************************************************************

  FileName    [abcCheck.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Consistency checking procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcCheck.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "main.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static bool Abc_NtkDoCheck( Abc_Ntk_t * pNtk );
static bool Abc_NtkCheckNames( Abc_Ntk_t * pNtk );
static bool Abc_NtkCheckPis( Abc_Ntk_t * pNtk );
static bool Abc_NtkCheckPos( Abc_Ntk_t * pNtk );
//static bool Abc_NtkCheckObj( Abc_Ntk_t * pNtk, Abc_Obj_t * pObj );
static bool Abc_NtkCheckNet( Abc_Ntk_t * pNtk, Abc_Obj_t * pNet );
static bool Abc_NtkCheckNode( Abc_Ntk_t * pNtk, Abc_Obj_t * pNode );
static bool Abc_NtkCheckLatch( Abc_Ntk_t * pNtk, Abc_Obj_t * pLatch );

static bool Abc_NtkComparePis( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int fComb );
static bool Abc_NtkComparePos( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int fComb );
static bool Abc_NtkCompareLatches( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int fComb );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Checks the integrity of the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkCheck( Abc_Ntk_t * pNtk )
{
   return !Abc_FrameIsFlagEnabled( "check" ) || Abc_NtkDoCheck( pNtk );
}

/**Function*************************************************************

  Synopsis    [Checks the integrity of the network after reading.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkCheckRead( Abc_Ntk_t * pNtk )
{
   return !Abc_FrameIsFlagEnabled( "checkread" ) || Abc_NtkDoCheck( pNtk );
}

/**Function*************************************************************

  Synopsis    [Checks the integrity of the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkDoCheck( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj, * pNet, * pNode;
    int i;

    if ( !Abc_NtkIsNetlist(pNtk) && !Abc_NtkIsLogic(pNtk) && !Abc_NtkIsStrash(pNtk) && !Abc_NtkIsSeq(pNtk) )
    {
        fprintf( stdout, "NetworkCheck: Unknown network type.\n" );
        return 0;
    }
    if ( !Abc_NtkHasSop(pNtk) && !Abc_NtkHasBdd(pNtk) && !Abc_NtkHasAig(pNtk) && !Abc_NtkHasMapping(pNtk) )
    {
        fprintf( stdout, "NetworkCheck: Unknown functionality type.\n" );
        return 0;
    }
    if ( Abc_NtkHasMapping(pNtk) )
    {
        if ( pNtk->pManFunc != Abc_FrameReadLibGen(Abc_FrameGetGlobalFrame()) )
        {
            fprintf( stdout, "NetworkCheck: The library of the mapped network is not the global library.\n" );
            return 0;
        }
    }

    // check the names
    if ( !Abc_NtkCheckNames( pNtk ) )
        return 0;

    // check PIs and POs
    Abc_NtkCleanCopy( pNtk );
    if ( !Abc_NtkCheckPis( pNtk ) )
        return 0;
    if ( !Abc_NtkCheckPos( pNtk ) )
        return 0;

    // check the connectivity of objects
    Abc_NtkForEachObj( pNtk, pObj, i )
        if ( !Abc_NtkCheckObj( pNtk, pObj ) )
            return 0;

    // if it is a netlist change nets and latches
    if ( Abc_NtkIsNetlist(pNtk) )
    {
        if ( Abc_NtkNetNum(pNtk) == 0 )
        {
            fprintf( stdout, "NetworkCheck: Netlist has no nets.\n" );
            return 0;
        }
        // check the nets
        Abc_NtkForEachNet( pNtk, pNet, i )
            if ( !Abc_NtkCheckNet( pNtk, pNet ) )
                return 0;
    }
    else
    {
        if ( Abc_NtkNetNum(pNtk) != 0 )
        {
            fprintf( stdout, "NetworkCheck: A network that is not a netlist has nets.\n" );
            return 0;
        }
    }

    // check the nodes
    if ( Abc_NtkHasAig(pNtk) )
    {
        if ( Abc_NtkIsStrash(pNtk) ) 
            Abc_AigCheck( pNtk->pManFunc );
    }
    else
    {
        Abc_NtkForEachNode( pNtk, pNode, i )
            if ( !Abc_NtkCheckNode( pNtk, pNode ) )
                return 0;
    }

    // check the latches
    Abc_NtkForEachLatch( pNtk, pNode, i )
        if ( !Abc_NtkCheckLatch( pNtk, pNode ) )
            return 0;

    // finally, check for combinational loops
//  clk = clock();
    if ( !Abc_NtkIsSeq( pNtk ) && !Abc_NtkIsAcyclic( pNtk ) )
    {
        fprintf( stdout, "NetworkCheck: Network contains a combinational loop.\n" );
        return 0;
    }
//  PRT( "Acyclic  ", clock() - clk );

    // check the EXDC network if present
    if ( pNtk->pExdc )
    {
//        if ( pNtk->Type != pNtk->pExdc->Type )
//        {
//            fprintf( stdout, "NetworkCheck: Network and its EXDC have different types.\n" );
//            return 0;
//        }
        return Abc_NtkCheck( pNtk->pExdc );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Checks the names.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkCheckNames( Abc_Ntk_t * pNtk )
{
    stmm_generator * gen;
    Abc_Obj_t * pNet, * pNet2, * pObj;
    char * pName;
    int i;

    if ( Abc_NtkIsNetlist(pNtk) )
    {
        // check that the nets in the table are also in the network
        stmm_foreach_item( pNtk->tName2Net, gen, &pName, (char**)&pNet )
        {
            if ( pNet->pData != pName )
            {
                fprintf( stdout, "NetworkCheck: Net \"%s\" has different name compared to the one in the name table.\n", pNet->pData );
                return 0;
            }
        }
        // check that the nets with names are also in the table
        Abc_NtkForEachNet( pNtk, pNet, i )
        {
            if ( pNet->pData && !stmm_lookup( pNtk->tName2Net, pNet->pData, (char**)&pNet2 ) )
            {
                fprintf( stdout, "NetworkCheck: Net \"%s\" is in the network but not in the name table.\n", pNet->pData );
                return 0;
            }
        }
    }

    // check PI/PO/latch names
    Abc_NtkForEachPi( pNtk, pObj, i )
    {
        if ( !stmm_lookup( pNtk->tObj2Name, (char *)pObj, &pName ) )
        {
            fprintf( stdout, "NetworkCheck: PI \"%s\" is in the network but not in the name table.\n", Abc_ObjName(pObj) );
            return 0;
        }
        if ( Abc_NtkIsNetlist(pNtk) && strcmp( Abc_ObjName(Abc_ObjFanout0(pObj)), pName ) )
        {
            fprintf( stdout, "NetworkCheck: PI \"%s\" has a different name compared to its net.\n", Abc_ObjName(pObj) );
            return 0;
        }
    }
    Abc_NtkForEachPo( pNtk, pObj, i )
    {
        if ( !stmm_lookup( pNtk->tObj2Name, (char *)pObj, &pName ) )
        {
            fprintf( stdout, "NetworkCheck: PO \"%s\" is in the network but not in the name table.\n", Abc_ObjName(pObj) );
            return 0;
        }
        if ( Abc_NtkIsNetlist(pNtk) && strcmp( Abc_ObjName(Abc_ObjFanin0(pObj)), pName ) )
        {
            fprintf( stdout, "NetworkCheck: PO \"%s\" has a different name compared to its net.\n", Abc_ObjName(pObj) );
            return 0;
        }
    }
    Abc_NtkForEachLatch( pNtk, pObj, i )
    {
        if ( !stmm_lookup( pNtk->tObj2Name, (char *)pObj, &pName ) )
        {
            fprintf( stdout, "NetworkCheck: Latch \"%s\" is in the network but not in the name table.\n", Abc_ObjName(pObj) );
            return 0;
        }
        if ( Abc_NtkIsNetlist(pNtk) && strcmp( Abc_ObjName(Abc_ObjFanout0(pObj)), pName ) )
        {
            fprintf( stdout, "NetworkCheck: Latch \"%s\" has a different name compared to its net.\n", Abc_ObjName(pObj) );
            return 0;
        }
    }
    return 1;
}


/**Function*************************************************************

  Synopsis    [Checks the PIs of the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkCheckPis( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    int i;

    if ( Abc_NtkCiNum(pNtk) != Abc_NtkPiNum(pNtk) + Abc_NtkLatchNum(pNtk) )
    {
        fprintf( stdout, "NetworkCheck: Incorrect size of the PI array.\n" );
        return 0;
    }

    // check that PIs are indeed PIs
    Abc_NtkForEachPi( pNtk, pObj, i )
    {
        if ( !Abc_ObjIsPi(pObj) )
        {
            fprintf( stdout, "NetworkCheck: Object \"%s\" (id=%d) is in the PI list but is not a PI.\n", Abc_ObjName(pObj), pObj->Id );
            return 0;
        }
        if ( pObj->pData )
        {
            fprintf( stdout, "NetworkCheck: A PI \"%s\" has a logic function.\n", Abc_ObjName(pObj) );
            return 0;
        }
        if ( Abc_ObjFaninNum(pObj) > 0 )
        {
            fprintf( stdout, "NetworkCheck: A PI \"%s\" has fanins.\n", Abc_ObjName(pObj) );
            return 0;
        }
        pObj->pCopy = (Abc_Obj_t *)1;
    }
    Abc_NtkForEachObj( pNtk, pObj, i )
    {
        if ( pObj->pCopy == NULL && Abc_ObjIsPi(pObj) )
        {
            fprintf( stdout, "NetworkCheck: Object \"%s\" (id=%d) is a PI but is not in the PI list.\n", Abc_ObjName(pObj), pObj->Id );
            return 0;
        }
        pObj->pCopy = NULL;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Checks the POs of the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkCheckPos( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    int i;

    if ( Abc_NtkCoNum(pNtk) != Abc_NtkPoNum(pNtk) + Abc_NtkLatchNum(pNtk) )
    {
        fprintf( stdout, "NetworkCheck: Incorrect size of the PO array.\n" );
        return 0;
    }

    // check that POs are indeed POs
    Abc_NtkForEachPo( pNtk, pObj, i )
    {
        if ( !Abc_ObjIsPo(pObj) )
        {
            fprintf( stdout, "NetworkCheck: Net \"%s\" (id=%d) is in the PO list but is not a PO.\n", Abc_ObjName(pObj), pObj->Id );
            return 0;
        }
        if ( pObj->pData )
        {
            fprintf( stdout, "NetworkCheck: A PO \"%s\" has a logic function.\n", Abc_ObjName(pObj) );
            return 0;
        }
        if ( Abc_ObjFaninNum(pObj) != 1 )
        {
            fprintf( stdout, "NetworkCheck: A PO \"%s\" does not have one fanin.\n", Abc_ObjName(pObj) );
            return 0;
        }
        if ( Abc_ObjFanoutNum(pObj) > 0 )
        {
            fprintf( stdout, "NetworkCheck: A PO \"%s\" has fanouts.\n", Abc_ObjName(pObj) );
            return 0;
        }
        pObj->pCopy = (Abc_Obj_t *)1;
    }
    Abc_NtkForEachObj( pNtk, pObj, i )
    {
        if ( pObj->pCopy == NULL && Abc_ObjIsPo(pObj) )
        {
            fprintf( stdout, "NetworkCheck: Net \"%s\" (id=%d) is in a PO but is not in the PO list.\n", Abc_ObjName(pObj), pObj->Id );
            return 0;
        }
        pObj->pCopy = NULL;
    }
    return 1;
}


/**Function*************************************************************

  Synopsis    [Checks the connectivity of the object.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkCheckObj( Abc_Ntk_t * pNtk, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanin, * pFanout;
    int i, Value = 1;
    int k;

    // check the network
    if ( pObj->pNtk != pNtk )
    {
        fprintf( stdout, "NetworkCheck: Object \"%s\" does not belong to the network.\n", Abc_ObjName(pObj) );
        return 0;
    }
    // check the object ID
    if ( pObj->Id < 0 || (int)pObj->Id >= Abc_NtkObjNumMax(pNtk) )
    {
        fprintf( stdout, "NetworkCheck: Object \"%s\" has incorrect ID.\n", Abc_ObjName(pObj) );
        return 0;
    }
    // go through the fanins of the object and make sure fanins have this object as a fanout
    Abc_ObjForEachFanin( pObj, pFanin, i )
    {
        if ( Vec_FanFindEntry( &pFanin->vFanouts, pObj->Id ) == -1 )
        {
            fprintf( stdout, "NodeCheck: Object \"%s\" has fanin ", Abc_ObjName(pObj) );
            fprintf( stdout, "\"%s\" but the fanin does not have it as a fanout.\n", Abc_ObjName(pFanin) );
            Value = 0;
        }
    }
    // go through the fanouts of the object and make sure fanouts have this object as a fanin
    Abc_ObjForEachFanout( pObj, pFanout, i )
    {
        if ( Vec_FanFindEntry( &pFanout->vFanins, pObj->Id ) == -1 )
        {
            fprintf( stdout, "NodeCheck: Object \"%s\" has fanout ", Abc_ObjName(pObj) );
            fprintf( stdout, "\"%s\" but the fanout does not have it as a fanin.\n", Abc_ObjName(pFanout) );
            Value = 0;
        }
    }

    if ( !Abc_FrameIsFlagEnabled("checkfio") )
        return Value;

    // make sure fanins are not duplicated
    for ( i = 0; i < pObj->vFanins.nSize; i++ )
        for ( k = i + 1; k < pObj->vFanins.nSize; k++ )
            if ( pObj->vFanins.pArray[k].iFan == pObj->vFanins.pArray[i].iFan )
            {
                printf( "Warning: Node %s has", Abc_ObjName(pObj) );
                printf( " duplicated fanin %s.\n", Abc_ObjName(Abc_ObjFanin(pObj,k)) );
            }

    // save time: do not check large fanout lists
    if ( pObj->vFanouts.nSize > 100 )
        return Value;

    // make sure fanouts are not duplicated
    for ( i = 0; i < pObj->vFanouts.nSize; i++ )
        for ( k = i + 1; k < pObj->vFanouts.nSize; k++ )
            if ( pObj->vFanouts.pArray[k].iFan == pObj->vFanouts.pArray[i].iFan )
            {
                printf( "Warning: Node %s has", Abc_ObjName(pObj) );
                printf( " duplicated fanout %s.\n", Abc_ObjName(Abc_ObjFanout(pObj,k)) );
            }

    return Value;
}

/**Function*************************************************************

  Synopsis    [Checks the integrity of a net.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkCheckNet( Abc_Ntk_t * pNtk, Abc_Obj_t * pNet )
{
    if ( Abc_ObjFaninNum(pNet) == 0 )
    {
        fprintf( stdout, "NetworkCheck: Net \"%s\" is not driven.\n", Abc_ObjName(pNet) );
        return 0;
    }
    if ( Abc_ObjFaninNum(pNet) > 1 )
    {
        fprintf( stdout, "NetworkCheck: Net \"%s\" has more than one driver.\n", Abc_ObjName(pNet) );
        return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Checks the integrity of a node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkCheckNode( Abc_Ntk_t * pNtk, Abc_Obj_t * pNode )
{
    // detect internal nodes that do not have nets
    if ( Abc_NtkIsNetlist(pNtk) && Abc_ObjFanoutNum(pNode) == 0 )
    {
        fprintf( stdout, "Node (id = %d) has no net to drive.\n", pNode->Id );
        return 0;
    }
    // the node should have a function assigned unless it is an AIG
    if ( pNode->pData == NULL )
    {
        fprintf( stdout, "NodeCheck: An internal node \"%s\" does not have a logic function.\n", Abc_ObjName(pNode) );
        return 0;
    }
    // the netlist and SOP logic network should have SOPs
    if ( Abc_NtkHasSop(pNtk) )
    {
        if ( !Abc_SopCheck( pNode->pData, Abc_ObjFaninNum(pNode) ) )
        {
            fprintf( stdout, "NodeCheck: SOP check for node \"%s\" has failed.\n", Abc_ObjName(pNode) );
            return 0;
        }
    }
    else if ( Abc_NtkHasBdd(pNtk) )
    {
        int nSuppSize = Cudd_SupportSize(pNtk->pManFunc, pNode->pData);
        if ( nSuppSize > Abc_ObjFaninNum(pNode) )
        {
            fprintf( stdout, "NodeCheck: BDD of the node \"%s\" has incorrect support size.\n", Abc_ObjName(pNode) );
            return 0;
        }
    }
    else if ( !Abc_NtkHasMapping(pNtk) )
    {
        assert( 0 );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Checks the integrity of a latch.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkCheckLatch( Abc_Ntk_t * pNtk, Abc_Obj_t * pLatch )
{
    int Value = 1;
    if ( pNtk->vLats->nSize != Abc_NtkLatchNum(pNtk) )
    {
        fprintf( stdout, "NetworkCheck: Incorrect size of the latch array.\n" );
        return 0;
    }
    // check whether the object is a latch
    if ( !Abc_ObjIsLatch(pLatch) )
    {
        fprintf( stdout, "NodeCheck: Latch \"%s\" is in a latch list but has not latch label.\n", Abc_ObjName(pLatch) );
        Value = 0;
    }
    // make sure the latch has a reasonable return value
    if ( (int)pLatch->pData < 0 || (int)pLatch->pData > 2 )
    {
        fprintf( stdout, "NodeCheck: Latch \"%s\" has incorrect reset value (%d).\n", 
            Abc_ObjName(pLatch), (int)pLatch->pData );
        Value = 0;
    }
    // make sure the latch has only one fanin
    if ( Abc_ObjFaninNum(pLatch) != 1 )
    {
        fprintf( stdout, "NodeCheck: Latch \"%s\" has wrong number (%d) of fanins.\n", Abc_ObjName(pLatch), Abc_ObjFaninNum(pLatch) );
        Value = 0;
    }
    return Value;
}




/**Function*************************************************************

  Synopsis    [Compares the PIs of the two networks.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkComparePis( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int fComb )
{
    Abc_Obj_t * pObj1;
    int i;
    if ( Abc_NtkPiNum(pNtk1) != Abc_NtkPiNum(pNtk2) )
    {
        printf( "Networks have different number of primary inputs.\n" );
        return 0;
    }
    // for each PI of pNet1 find corresponding PI of pNet2 and reorder them
    Abc_NtkForEachPi( pNtk1, pObj1, i )
    {
        if ( strcmp( Abc_ObjName(pObj1), Abc_ObjName(Abc_NtkPi(pNtk2,i)) ) != 0 )
        {
            printf( "Primary input #%d is different in network 1 ( \"%s\") and in network 2 (\"%s\").\n", 
                i, Abc_ObjName(pObj1), Abc_ObjName(Abc_NtkPi(pNtk2,i)) );
            return 0;
        }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Compares the POs of the two networks.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkComparePos( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int fComb )
{
    Abc_Obj_t * pObj1;
    int i;
    if ( Abc_NtkPoNum(pNtk1) != Abc_NtkPoNum(pNtk2) )
    {
        printf( "Networks have different number of primary outputs.\n" );
        return 0;
    }
    // for each PO of pNet1 find corresponding PO of pNet2 and reorder them
    Abc_NtkForEachPo( pNtk1, pObj1, i )
    {
        if ( strcmp( Abc_ObjName(pObj1), Abc_ObjName(Abc_NtkPo(pNtk2,i)) ) != 0 )
        {
            printf( "Primary output #%d is different in network 1 ( \"%s\") and in network 2 (\"%s\").\n", 
                i, Abc_ObjName(pObj1), Abc_ObjName(Abc_NtkPo(pNtk2,i)) );
            return 0;
        }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Compares the latches of the two networks.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkCompareLatches( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int fComb )
{
    Abc_Obj_t * pObj1;
    int i;
    if ( !fComb )
        return 1;
    if ( Abc_NtkLatchNum(pNtk1) != Abc_NtkLatchNum(pNtk2) )
    {
        printf( "Networks have different number of latches.\n" );
        return 0;
    }
    // for each PI of pNet1 find corresponding PI of pNet2 and reorder them
    Abc_NtkForEachLatch( pNtk1, pObj1, i )
    {
        if ( strcmp( Abc_ObjName(pObj1), Abc_ObjName(Abc_NtkLatch(pNtk2,i)) ) != 0 )
        {
            printf( "Latch #%d is different in network 1 ( \"%s\") and in network 2 (\"%s\").\n", 
                i, Abc_ObjName(pObj1), Abc_ObjName(Abc_NtkLatch(pNtk2,i)) );
            return 0;
        }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Compares the signals of the networks.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkCompareSignals( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int fComb )
{
    Abc_NtkOrderObjsByName( pNtk1, fComb );
    Abc_NtkOrderObjsByName( pNtk2, fComb );
    if ( !Abc_NtkCompareLatches( pNtk1, pNtk2, fComb ) )
        return 0;
    if ( !Abc_NtkComparePis( pNtk1, pNtk2, fComb ) )
        return 0;
    if ( !Abc_NtkComparePos( pNtk1, pNtk2, fComb ) )
        return 0;
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


