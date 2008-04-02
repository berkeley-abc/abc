/**CFile****************************************************************

  FileName    [nwkUtil.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Logic network representation.]

  Synopsis    [Various utilities.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: nwkUtil.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "nwk.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Increments the current traversal ID of the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nwk_ManIncrementTravId( Nwk_Man_t * pNtk )
{
    Nwk_Obj_t * pObj;
    int i;
    if ( pNtk->nTravIds >= (1<<26)-1 )
    {
        pNtk->nTravIds = 0;
        Nwk_ManForEachObj( pNtk, pObj, i )
            pObj->TravId = 0;
    }
    pNtk->nTravIds++;
}

/**Function*************************************************************

  Synopsis    [Reads the maximum number of fanins.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Nwk_ManGetFaninMax( Nwk_Man_t * pNtk )
{
    Nwk_Obj_t * pNode;
    int i, nFaninsMax = 0;
    Nwk_ManForEachNode( pNtk, pNode, i )
    {
        if ( nFaninsMax < Nwk_ObjFaninNum(pNode) )
            nFaninsMax = Nwk_ObjFaninNum(pNode);
    }
    return nFaninsMax;
}

/**Function*************************************************************

  Synopsis    [Reads the total number of all fanins.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Nwk_ManGetTotalFanins( Nwk_Man_t * pNtk )
{
    Nwk_Obj_t * pNode;
    int i, nFanins = 0;
    Nwk_ManForEachNode( pNtk, pNode, i )
        nFanins += Nwk_ObjFaninNum(pNode);
    return nFanins;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Nwk_ManPiNum( Nwk_Man_t * pNtk )
{
    Nwk_Obj_t * pNode;
    int i, Counter = 0;
    Nwk_ManForEachCi( pNtk, pNode, i )
        Counter += Nwk_ObjIsPi( pNode );
    return Counter;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Nwk_ManPoNum( Nwk_Man_t * pNtk )
{
    Nwk_Obj_t * pNode;
    int i, Counter = 0;
    Nwk_ManForEachCo( pNtk, pNode, i )
        Counter += Nwk_ObjIsPo( pNode );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Reads the number of BDD nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Nwk_ManGetAigNodeNum( Nwk_Man_t * pNtk )
{
    Nwk_Obj_t * pNode;
    int i, nNodes = 0;
    Nwk_ManForEachNode( pNtk, pNode, i )
    {
        if ( pNode->pFunc == NULL )
        {
            printf( "Nwk_ManGetAigNodeNum(): Local AIG of node %d is not assigned.\n", pNode->Id );
            continue;
        }
        if ( Nwk_ObjFaninNum(pNode) < 2 )
            continue;
        nNodes += Hop_DagSize( pNode->pFunc );
    }
    return nNodes;
}

/**Function*************************************************************

  Synopsis    [Procedure used for sorting the nodes in increasing order of levels.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Nwk_NodeCompareLevelsIncrease( Nwk_Obj_t ** pp1, Nwk_Obj_t ** pp2 )
{
    int Diff = (*pp1)->Level - (*pp2)->Level;
    if ( Diff < 0 )
        return -1;
    if ( Diff > 0 ) 
        return 1;
    return 0; 
}

/**Function*************************************************************

  Synopsis    [Procedure used for sorting the nodes in decreasing order of levels.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Nwk_NodeCompareLevelsDecrease( Nwk_Obj_t ** pp1, Nwk_Obj_t ** pp2 )
{
    int Diff = (*pp1)->Level - (*pp2)->Level;
    if ( Diff > 0 )
        return -1;
    if ( Diff < 0 ) 
        return 1;
    return 0; 
}

/**Function*************************************************************

  Synopsis    [Deletes the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nwk_ObjPrint( Nwk_Obj_t * pObj )
{
    Nwk_Obj_t * pNext;
    int i;
    printf( "ObjId = %5d.  ", pObj->Id );
    if ( Nwk_ObjIsPi(pObj) )
        printf( "PI" );
    if ( Nwk_ObjIsPo(pObj) )
        printf( "PO" );
    if ( Nwk_ObjIsNode(pObj) )
        printf( "Node" );
    printf( "   Fanins = " );
    Nwk_ObjForEachFanin( pObj, pNext, i )
        printf( "%d ", pNext->Id );
    printf( "   Fanouts = " );
    Nwk_ObjForEachFanout( pObj, pNext, i )
        printf( "%d ", pNext->Id );
    printf( "\n" );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


