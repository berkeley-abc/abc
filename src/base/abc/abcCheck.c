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

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static bool Abc_NtkCheckNames( Abc_Ntk_t * pNtk );
static bool Abc_NtkCheckPis( Abc_Ntk_t * pNtk );
static bool Abc_NtkCheckPos( Abc_Ntk_t * pNtk );
static bool Abc_NtkCheckObj( Abc_Ntk_t * pNtk, Abc_Obj_t * pObj );
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
    Abc_Obj_t * pObj, * pNet, * pNode;
    int i;

    if ( !Abc_NtkIsNetlist(pNtk) && !Abc_NtkIsAig(pNtk) && !Abc_NtkIsLogic(pNtk) )
    {
        fprintf( stdout, "NetworkCheck: Unknown network type.\n" );
        return 0;
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
        // check the nets
        Abc_NtkForEachNet( pNtk, pNet, i )
            if ( !Abc_NtkCheckNet( pNtk, pNet ) )
                return 0;
    }

    // check the nodes
    Abc_NtkForEachNode( pNtk, pNode, i )
        if ( !Abc_NtkCheckNode( pNtk, pNode ) )
            return 0;
    // check the latches
    Abc_NtkForEachLatch( pNtk, pNode, i )
        if ( !Abc_NtkCheckLatch( pNtk, pNode ) )
            return 0;

    // finally, check for combinational loops
//  clk = clock();
    if ( !Abc_NtkIsAcyclic( pNtk ) )
    {
        fprintf( stdout, "NetworkCheck: Network contains a combinational loop.\n" );
        return 0;
    }
//  PRT( "Acyclic  ", clock() - clk );

    // check the EXDC network if present
    if ( pNtk->pExdc )
    {
        if ( pNtk->Type != pNtk->pExdc->Type )
        {
            fprintf( stdout, "NetworkCheck: Network and its EXDC have different types.\n" );
            return 0;
        }
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
    Abc_Obj_t * pNet, * pNet2;
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
    else
    {
        if ( pNtk->vPis->nSize != pNtk->nPis + pNtk->nLatches )
        {
            fprintf( stdout, "NetworkCheck: Incorrect size of the PI array.\n" );
            return 0;
        }
        if ( pNtk->vPos->nSize != pNtk->nPos + pNtk->nLatches )
        {
            fprintf( stdout, "NetworkCheck: Incorrect size of the PO array.\n" );
            return 0;
        }
        if ( pNtk->vLatches->nSize != pNtk->nLatches )
        {
            fprintf( stdout, "NetworkCheck: Incorrect size of the latch array.\n" );
            return 0;
        }

        if ( pNtk->vNamesPi->nSize != pNtk->vPis->nSize )
        {
            fprintf( stdout, "NetworkCheck: Incorrect size of the PI names array.\n" );
            return 0;
        }
        if ( pNtk->vNamesPo->nSize != pNtk->vPos->nSize )
        {
            fprintf( stdout, "NetworkCheck: Incorrect size of the PO names array.\n" );
            return 0;
        }
        if ( pNtk->vNamesLatch->nSize != pNtk->vLatches->nSize )
        {
            fprintf( stdout, "NetworkCheck: Incorrect size of the latch names array.\n" );
            return 0;
        }

        /*
        Abc_Obj_t * pNode, * pNode2;
        Abc_NtkForEachPi( pNtk, pNode, i )
        {
            if ( !stmm_lookup( pNtk->tName2Net, Abc_NtkNamePi(pNtk,i), (char**)&pNode2 ) )
            {
                fprintf( stdout, "NetworkCheck: PI \"%s\" is in the network but not in the name table.\n", Abc_NtkNamePi(pNtk,i) );
                return 0;
            }
            if ( pNode != pNode2 )
            {
                fprintf( stdout, "NetworkCheck: PI \"%s\" has a different pointer in the name table.\n", Abc_NtkNamePi(pNtk,i) );
                return 0;
            }
        }
        Abc_NtkForEachPo( pNtk, pNode, i )
        {
            if ( !stmm_lookup( pNtk->tName2Net, Abc_NtkNamePo(pNtk,i), (char**)&pNode2 ) )
            {
                fprintf( stdout, "NetworkCheck: PO \"%s\" is in the network but not in the name table.\n", Abc_NtkNamePo(pNtk,i) );
                return 0;
            }
            if ( pNode != pNode2 )
            {
                fprintf( stdout, "NetworkCheck: PO \"%s\" has a different pointer in the name table.\n", Abc_NtkNamePo(pNtk,i) );
                return 0;
            }
        }
        Abc_NtkForEachLatch( pNtk, pNode, i )
        {
            if ( !stmm_lookup( pNtk->tName2Net, Abc_NtkNameLatch(pNtk,i), (char**)&pNode2 ) )
            {
                fprintf( stdout, "NetworkCheck: Latch \"%s\" is in the network but not in the name table.\n", Abc_NtkNameLatch(pNtk,i) );
                return 0;
            }
            if ( pNode != pNode2 )
            {
                fprintf( stdout, "NetworkCheck: Latch \"%s\" has a different pointer in the name table.\n", Abc_NtkNameLatch(pNtk,i) );
                return 0;
            }
        }
        */
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

    // check that PIs are indeed PIs
    Abc_NtkForEachPi( pNtk, pObj, i )
    {
        if ( Abc_NtkIsNetlist(pNtk) )
        {
            if ( !Abc_ObjIsNet(pObj) )
            {
                fprintf( stdout, "NetworkCheck: A PI \"%s\" is not a net.\n", Abc_ObjName(pObj) );
                return 0;
            }
        }
        else
        {
            if ( !Abc_ObjIsTerm(pObj) )
            {
                fprintf( stdout, "NetworkCheck: A PI \"%s\" is not a terminal node.\n", Abc_ObjName(pObj) );
                return 0;
            }
            if ( pObj->pData )
            {
                fprintf( stdout, "NetworkCheck: A PI \"%s\" has a logic function.\n", Abc_ObjName(pObj) );
                return 0;
            }
        }
        if ( !Abc_ObjIsPi(pObj) )
        {
            fprintf( stdout, "NetworkCheck: Object \"%s\" (id=%d) is in the PI list but is not a PI.\n", Abc_ObjName(pObj), pObj->Id );
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

    // check that POs are indeed POs
    Abc_NtkForEachPo( pNtk, pObj, i )
    {
        if ( Abc_NtkIsNetlist(pNtk) )
        {
            if ( !Abc_ObjIsNet(pObj) )
            {
                fprintf( stdout, "NetworkCheck: A PO \"%s\" is not a net.\n", Abc_ObjName(pObj) );
                return 0;
            }
        }
        else
        {
            if ( !Abc_ObjIsTerm(pObj) )
            {
                fprintf( stdout, "NetworkCheck: A PO \"%s\" is not a terminal node.\n", Abc_ObjName(pObj) );
                return 0;
            }
            if ( pObj->pData )
            {
                fprintf( stdout, "NetworkCheck: A PO \"%s\" has a logic function.\n", Abc_ObjName(pObj) );
                return 0;
            }
        }
        if ( !Abc_ObjIsPo(pObj) )
        {
            fprintf( stdout, "NetworkCheck: Net \"%s\" (id=%d) is in the PO list but is not a PO.\n", Abc_ObjName(pObj), pObj->Id );
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

    // check the network
    if ( pObj->pNtk != pNtk )
    {
        fprintf( stdout, "NetworkCheck: Object \"%s\" does not belong to the network.\n", Abc_ObjName(pObj) );
        return 0;
    }
    // the object cannot be a net if it is not a netlist
    if ( Abc_ObjIsNet(pObj) && !Abc_NtkIsNetlist(pNtk) )
    {
        fprintf( stdout, "NetworkCheck: Object \"%s\" is a net but the network is not a netlist.\n", Abc_ObjName(pObj) );
        return 0;
    }
    // check the object ID
    if ( pObj->Id < 0 || (int)pObj->Id > pNtk->vObjs->nSize )
    {
        fprintf( stdout, "NetworkCheck: Object \"%s\" has incorrect ID.\n", Abc_ObjName(pObj) );
        return 0;
    }
    // a PI has no fanins
    if ( Abc_ObjIsPi(pObj) && Abc_ObjFaninNum(pObj) > 0 )
    {
        fprintf( stdout, "PI \"%s\" has fanins.\n", Abc_ObjName(pObj) );
        return 0;
    }
    // detect internal nets that are not driven
    if ( !Abc_ObjIsPi(pObj) && Abc_ObjFaninNum(pObj) == 0 && Abc_ObjIsNet(pObj) )
    {
        fprintf( stdout, "Net \"%s\" is not driven.\n", Abc_ObjName(pObj) );
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
    // the node should have a function assigned unless it is an AIG
    if ( pNode->pData == NULL && !Abc_NtkIsAig(pNtk) )
    {
        fprintf( stdout, "NodeCheck: An internal node \"%s\" has no logic function.\n", Abc_ObjName(pNode) );
        return 0;
    }

    // the netlist and SOP logic network should have SOPs
    if ( Abc_NtkIsNetlist(pNtk) || Abc_NtkIsLogicSop(pNtk) )
    {
        if ( !Abc_SopCheck( pNode->pData, Abc_ObjFaninNum(pNode) ) )
        {
            fprintf( stdout, "NodeCheck: SOP check for node \"%s\" has failed.\n", Abc_ObjName(pNode) );
            return 0;
        }
    }
    else if ( Abc_NtkIsLogicBdd(pNtk) )
    {
        int nSuppSize = Cudd_SupportSize(pNtk->pManFunc, pNode->pData);
        if ( nSuppSize > Abc_ObjFaninNum(pNode) )
        {
            fprintf( stdout, "NodeCheck: BDD of the node \"%s\" has incorrect support size.\n", Abc_ObjName(pNode) );
            return 0;
        }
    }
    else if ( !Abc_NtkIsAig(pNtk) && !Abc_NtkIsLogicMap(pNtk) )
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
    Abc_Obj_t * pObj;
    int Value = 1;
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
    // make sure the latch has fanins and fanouts that are labeled accordingly
    if ( Abc_NtkIsNetlist(pNtk) )
    {
        pObj = Abc_ObjFanin0( pLatch );
        if ( !Abc_ObjIsLi(pObj) )
        {
            fprintf( stdout, "NodeCheck: Latch \"%s\" has a fanin that is not labeled as LI.\n", Abc_ObjName(pLatch) );
            Value = 0;
        }
        pObj = Abc_ObjFanout0( pLatch );
        if ( !Abc_ObjIsLo(pObj) )
        {
            fprintf( stdout, "NodeCheck: Latch \"%s\" has a fanout that is not labeled as LO.\n", Abc_ObjName(pLatch) );
            Value = 0;
        }
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
    Abc_Obj_t * pNode1;
    int i;
    if ( Abc_NtkPiNum(pNtk1) != Abc_NtkPiNum(pNtk2) )
    {
        printf( "Networks have different number of primary inputs.\n" );
        return 0;
    }
    // for each PI of pNet1 find corresponding PI of pNet2 and reorder them
    Abc_NtkForEachPi( pNtk1, pNode1, i )
    {
        if ( strcmp( Abc_NtkNamePi(pNtk1,i), Abc_NtkNamePi(pNtk2,i) ) != 0 )
        {
            printf( "Primary input #%d is different in network 1 ( \"%s\") and in network 2 (\"%s\").\n", 
                i, Abc_NtkNamePi(pNtk1,i), Abc_NtkNamePi(pNtk2,i) );
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
    Abc_Obj_t * pNode1;
    int i;
    if ( Abc_NtkPoNum(pNtk1) != Abc_NtkPoNum(pNtk2) )
    {
        printf( "Networks have different number of primary outputs.\n" );
        return 0;
    }
    // for each PI of pNet1 find corresponding PI of pNet2 and reorder them
    Abc_NtkForEachPo( pNtk1, pNode1, i )
    {
        if ( strcmp( Abc_NtkNamePo(pNtk1,i), Abc_NtkNamePo(pNtk2,i) ) != 0 )
        {
            printf( "Primary output #%d is different in network 1 ( \"%s\") and in network 2 (\"%s\").\n", 
                i, Abc_NtkNamePo(pNtk1,i), Abc_NtkNamePo(pNtk2,i) );
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
    Abc_Obj_t * pNode1;
    int i;
    if ( !fComb )
        return 1;
    if ( Abc_NtkLatchNum(pNtk1) != Abc_NtkLatchNum(pNtk2) )
    {
        printf( "Networks have different number of latches.\n" );
        return 0;
    }
    // for each PI of pNet1 find corresponding PI of pNet2 and reorder them
    Abc_NtkForEachLatch( pNtk1, pNode1, i )
    {
        if ( strcmp( Abc_NtkNameLatch(pNtk1,i), Abc_NtkNameLatch(pNtk2,i) ) != 0 )
        {
            printf( "Latch #%d is different in network 1 ( \"%s\") and in network 2 (\"%s\").\n", 
                i, Abc_NtkNameLatch(pNtk1,i), Abc_NtkNameLatch(pNtk2,i) );
            return 0;
        }
    }
    return 1;
}


/**Function*************************************************************

  Synopsis    [Compares the PIs of the two networks.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkComparePis2( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int fComb )
{
    Abc_Obj_t * pNode1, * pNode2;
    Vec_Ptr_t * vNodesNew, * vNamesNew;
    stmm_table * tNames;
    int i;

    if ( Abc_NtkPiNum(pNtk1) != Abc_NtkPiNum(pNtk2) )
    {
        printf( "Networks have different number of primary inputs.\n" );
        return 0;
    }

    // for each PI of pNet1 find corresponding PI of pNet2 and reorder them
    vNodesNew = Vec_PtrAlloc( 100 );
    vNamesNew = Vec_PtrAlloc( 100 );
    tNames    = Abc_NtkLogicHashNames( pNtk2, 0, fComb );
    Abc_NtkForEachCi( pNtk1, pNode1, i )
    {
        if ( stmm_lookup( tNames, Abc_NtkNamePi(pNtk1,i), (char **)&pNode2 ) )
        {
            Vec_PtrPush( vNodesNew, pNode2 );
            Vec_PtrPush( vNamesNew, pNode2->pCopy );
        }
        else
        {
            printf( "Primary input \"%s\" of network 1 is not in network 2.\n", pNtk1->vNamesPi->pArray[i] );
            Vec_PtrFree( vNodesNew );
            Vec_PtrFree( vNamesNew );
            return 0;
        }
        if ( !fComb && i == Abc_NtkPiNum(pNtk2)-1 )
            break;
    }
    stmm_free_table( tNames );
    // add latches to the PI/PO lists to work as CIs/COs
    if ( !fComb )
    {
        Abc_NtkForEachLatch( pNtk2, pNode2, i )
        {
            Vec_PtrPush( vNodesNew, pNode2 );
            Vec_PtrPush( vNamesNew, Abc_NtkNameLatch(pNtk2,i) );
        }
    }
    Vec_PtrFree( pNtk2->vPis );      pNtk2->vPis     = vNodesNew;  vNodesNew = NULL;
    Vec_PtrFree( pNtk2->vNamesPi );  pNtk2->vNamesPi = vNamesNew;  vNamesNew = NULL;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Compares the POs of the two networks.]

  Description [If the flag is 1, compares the first n POs of pNet1, where
  n is the number of POs in pNet2.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkComparePos2( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int fComb )
{
    Abc_Obj_t * pNode1, * pNode2;
    Vec_Ptr_t * vNodesNew, * vNamesNew;
    stmm_table * tNames;
    int i;

    if ( Abc_NtkPoNum(pNtk1) != Abc_NtkPoNum(pNtk2) )
    {
        printf( "Networks have different number of primary outputs.\n" );
        return 0;
    }

    // for each PO of pNet1 find corresponding PO of pNet2 and reorder them
    vNodesNew = Vec_PtrAlloc( 100 );
    vNamesNew = Vec_PtrAlloc( 100 );
    tNames    = Abc_NtkLogicHashNames( pNtk2, 1, fComb );
    Abc_NtkForEachCo( pNtk1, pNode1, i )
    {
        if ( stmm_lookup( tNames, Abc_NtkNamePo(pNtk1,i), (char **)&pNode2 ) )
        {
            Vec_PtrPush( vNodesNew, pNode2 );
            Vec_PtrPush( vNamesNew, pNode2->pCopy );
        }
        else
        {
            printf( "Primary output \"%s\" of network 1 is not in network 2.\n", pNtk1->vNamesPo->pArray[i] );
            Vec_PtrFree( vNodesNew );
            Vec_PtrFree( vNamesNew );
            return 0;
        }
        if ( !fComb && i == Abc_NtkPoNum(pNtk2)-1 )
            break;
    }
    stmm_free_table( tNames );
    // add latches to the PI/PO lists to work as CIs/COs
    if ( !fComb )
    {
        Abc_NtkForEachLatch( pNtk2, pNode2, i )
        {
            Vec_PtrPush( vNodesNew, pNode2 );
            Vec_PtrPush( vNamesNew, Abc_NtkNameLatch(pNtk2,i) );
        }
    }
    Vec_PtrFree( pNtk2->vPos );      pNtk2->vPos = vNodesNew;      vNodesNew = NULL;
    Vec_PtrFree( pNtk2->vNamesPo );  pNtk2->vNamesPo = vNamesNew;  vNamesNew = NULL;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Compares the latches of the two networks.]

  Description [This comparison procedure should be always called before
  the other two.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkCompareLatches2( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int fComb )
{
    Abc_Obj_t * pNode1, * pNode2;
    Vec_Ptr_t * vNodesNew, * vNamesNew;
    stmm_table * tNames;
    int i;

    if ( !fComb )
        return 1;

    if ( Abc_NtkLatchNum(pNtk1) != Abc_NtkLatchNum(pNtk2) )
    {
        printf( "Networks have different number of latches.\n" );
        return 0;
    }

    // for each latch of pNet1 find corresponding latch of pNet2 and reorder them
    vNodesNew = Vec_PtrAlloc( 100 );
    vNamesNew = Vec_PtrAlloc( 100 );
    tNames    = Abc_NtkLogicHashNames( pNtk2, 2, fComb );
    Abc_NtkForEachLatch( pNtk1, pNode1, i )
    {
        if ( stmm_lookup( tNames, Abc_NtkNameLatch(pNtk1,i), (char **)&pNode2 ) )
        {
            Vec_PtrPush( vNodesNew, pNode2 );
            Vec_PtrPush( vNamesNew, pNode2->pCopy );
        }
        else
        {
            printf( "Latch \"%s\" of network 1 is not in network 2.\n", pNtk1->vNamesLatch->pArray[i] );
            Vec_PtrFree( vNodesNew );
            Vec_PtrFree( vNamesNew );
            return 0;
        }
    }
    stmm_free_table( tNames );
    Vec_PtrFree( pNtk2->vLatches );      pNtk2->vLatches = vNodesNew;      vNodesNew = NULL;
    Vec_PtrFree( pNtk2->vNamesLatch );   pNtk2->vNamesLatch = vNamesNew;   vNamesNew = NULL;
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
    if ( !Abc_NtkCompareLatches( pNtk1, pNtk2, fComb ) )
        return 0;
    if ( !Abc_NtkComparePis( pNtk1, pNtk2, fComb ) )
        return 0;
//    if ( !Abc_NtkComparePos( pNtk1, pNtk2, fComb ) )
//        return 0;
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


