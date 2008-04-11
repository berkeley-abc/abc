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
#include "math.h"

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

/**Function*************************************************************

  Synopsis    [Deletes the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nwk_ManDumpBlif( Nwk_Man_t * pNtk, char * pFileName, Vec_Ptr_t * vCiNames, Vec_Ptr_t * vCoNames )
{
    printf( "Dumping logic network is currently not supported.\n" );
}

/**Function*************************************************************

  Synopsis    [Prints the distribution of fanins/fanouts in the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nwk_ManPrintFanioNew( Nwk_Man_t * pNtk )
{
    char Buffer[100];
    Nwk_Obj_t * pNode;
    Vec_Int_t * vFanins, * vFanouts;
    int nFanins, nFanouts, nFaninsMax, nFanoutsMax, nFaninsAll, nFanoutsAll;
    int i, k, nSizeMax;

    // determine the largest fanin and fanout
    nFaninsMax = nFanoutsMax = 0;
    nFaninsAll = nFanoutsAll = 0;
    Nwk_ManForEachNode( pNtk, pNode, i )
    {
        nFanins  = Nwk_ObjFaninNum(pNode);
        nFanouts = Nwk_ObjFanoutNum(pNode);
        nFaninsAll  += nFanins;
        nFanoutsAll += nFanouts;
        nFaninsMax   = AIG_MAX( nFaninsMax, nFanins );
        nFanoutsMax  = AIG_MAX( nFanoutsMax, nFanouts );
    }

    // allocate storage for fanin/fanout numbers
    nSizeMax = AIG_MAX( 10 * (Aig_Base10Log(nFaninsMax) + 1), 10 * (Aig_Base10Log(nFanoutsMax) + 1) );
    vFanins  = Vec_IntStart( nSizeMax );
    vFanouts = Vec_IntStart( nSizeMax );

    // count the number of fanins and fanouts
    Nwk_ManForEachNode( pNtk, pNode, i )
    {
        nFanins  = Nwk_ObjFaninNum(pNode);
        nFanouts = Nwk_ObjFanoutNum(pNode);
//        nFanouts = Nwk_NodeMffcSize(pNode);

        if ( nFanins < 10 )
            Vec_IntAddToEntry( vFanins, nFanins, 1 );
        else if ( nFanins < 100 )
            Vec_IntAddToEntry( vFanins, 10 + nFanins/10, 1 );
        else if ( nFanins < 1000 )
            Vec_IntAddToEntry( vFanins, 20 + nFanins/100, 1 );
        else if ( nFanins < 10000 )
            Vec_IntAddToEntry( vFanins, 30 + nFanins/1000, 1 );
        else if ( nFanins < 100000 )
            Vec_IntAddToEntry( vFanins, 40 + nFanins/10000, 1 );
        else if ( nFanins < 1000000 )
            Vec_IntAddToEntry( vFanins, 50 + nFanins/100000, 1 );
        else if ( nFanins < 10000000 )
            Vec_IntAddToEntry( vFanins, 60 + nFanins/1000000, 1 );

        if ( nFanouts < 10 )
            Vec_IntAddToEntry( vFanouts, nFanouts, 1 );
        else if ( nFanouts < 100 )
            Vec_IntAddToEntry( vFanouts, 10 + nFanouts/10, 1 );
        else if ( nFanouts < 1000 )
            Vec_IntAddToEntry( vFanouts, 20 + nFanouts/100, 1 );
        else if ( nFanouts < 10000 )
            Vec_IntAddToEntry( vFanouts, 30 + nFanouts/1000, 1 );
        else if ( nFanouts < 100000 )
            Vec_IntAddToEntry( vFanouts, 40 + nFanouts/10000, 1 );
        else if ( nFanouts < 1000000 )
            Vec_IntAddToEntry( vFanouts, 50 + nFanouts/100000, 1 );
        else if ( nFanouts < 10000000 )
            Vec_IntAddToEntry( vFanouts, 60 + nFanouts/1000000, 1 );
    }

    printf( "The distribution of fanins and fanouts in the network:\n" );
    printf( "         Number   Nodes with fanin  Nodes with fanout\n" );
    for ( k = 0; k < nSizeMax; k++ )
    {
        if ( vFanins->pArray[k] == 0 && vFanouts->pArray[k] == 0 )
            continue;
        if ( k < 10 )
            printf( "%15d : ", k );
        else
        {
            sprintf( Buffer, "%d - %d", (int)pow(10, k/10) * (k%10), (int)pow(10, k/10) * (k%10+1) - 1 ); 
            printf( "%15s : ", Buffer );
        }
        if ( vFanins->pArray[k] == 0 )
            printf( "              " );
        else
            printf( "%12d  ", vFanins->pArray[k] );
        printf( "    " );
        if ( vFanouts->pArray[k] == 0 )
            printf( "              " );
        else
            printf( "%12d  ", vFanouts->pArray[k] );
        printf( "\n" );
    }
    Vec_IntFree( vFanins );
    Vec_IntFree( vFanouts );

    printf( "Fanins: Max = %d. Ave = %.2f.  Fanouts: Max = %d. Ave =  %.2f.\n", 
        nFaninsMax,  1.0*nFaninsAll/Nwk_ManNodeNum(pNtk), 
        nFanoutsMax, 1.0*nFanoutsAll/Nwk_ManNodeNum(pNtk)  );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


