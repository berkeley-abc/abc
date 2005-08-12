/**CFile****************************************************************

  FileName    [abcPrint.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Printing statistics.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcPrint.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "ft.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Print the vital stats of the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkPrintStats( FILE * pFile, Abc_Ntk_t * pNtk )
{
    fprintf( pFile, "%-15s:",       pNtk->pName );
    fprintf( pFile, "  i/o = %3d/%3d", Abc_NtkPiNum(pNtk), Abc_NtkPoNum(pNtk) );
    fprintf( pFile, "  lat = %4d", Abc_NtkLatchNum(pNtk) );

    if ( Abc_NtkIsNetlist(pNtk) )
    {
        fprintf( pFile, "  net = %5d", Abc_NtkNetNum(pNtk) );
        fprintf( pFile, "  nd = %5d", Abc_NtkNodeNum(pNtk) );
    }
    else if ( Abc_NtkIsAig(pNtk) )
    {
        fprintf( pFile, "  and = %5d", Abc_NtkNodeNum(pNtk) );
        fprintf( pFile, "  choice = %5d", Abc_NtkCountChoiceNodes(pNtk) );
    }
    else 
        fprintf( pFile, "  nd = %5d", Abc_NtkNodeNum(pNtk) );

    if ( Abc_NtkIsLogicSop(pNtk) )   
    {
        fprintf( pFile, "  cube = %5d",  Abc_NtkGetCubeNum(pNtk) );
        fprintf( pFile, "  lit(sop) = %5d",  Abc_NtkGetLitNum(pNtk) );
        fprintf( pFile, "  lit(fac) = %5d",  Abc_NtkGetLitFactNum(pNtk) );
    }
    else if ( Abc_NtkIsLogicBdd(pNtk) )
        fprintf( pFile, "  bdd = %5d",  Abc_NtkGetBddNodeNum(pNtk) );
    else if ( Abc_NtkIsLogicMap(pNtk) )
    {
        fprintf( pFile, "  area = %5.2f", Abc_NtkGetMappedArea(pNtk) );
        fprintf( pFile, "  delay = %5.2f", Abc_NtkDelayTrace(pNtk) );
    }
    else if ( !Abc_NtkIsAig(pNtk) )
    {
        assert( 0 );
    }
    fprintf( pFile, "  lev = %2d", Abc_NtkGetLevelNum(pNtk) );
    fprintf( pFile, "\n" );
}

/**Function*************************************************************

  Synopsis    [Prints PIs/POs and LIs/LOs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkPrintIo( FILE * pFile, Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    int i;

    fprintf( pFile, "Primary inputs (%d): ", Abc_NtkPiNum(pNtk) );    
    Abc_NtkForEachPi( pNtk, pObj, i )
        fprintf( pFile, " %s", Abc_ObjName(pObj) );
    fprintf( pFile, "\n" );   

    fprintf( pFile, "Primary outputs (%d):", Abc_NtkPoNum(pNtk) );    
    Abc_NtkForEachPo( pNtk, pObj, i )
        fprintf( pFile, " %s", Abc_ObjName(pObj) );
    fprintf( pFile, "\n" );    

    fprintf( pFile, "Latches (%d):  ", Abc_NtkLatchNum(pNtk) );  
    Abc_NtkForEachLatch( pNtk, pObj, i )
        fprintf( pFile, " %s", Abc_ObjName(pObj) );
    fprintf( pFile, "\n" );   
}

/**Function*************************************************************

  Synopsis    [Prints statistics about latches.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkPrintLatch( FILE * pFile, Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pLatch;
    int i, Counter0, Counter1, Counter2;
    int Init0, Init1, Init2;

    if ( Abc_NtkLatchNum(pNtk) == 0 )
    {
        fprintf( pFile, "The network is combinational.\n" );
        return;
    }

    assert( !Abc_NtkIsNetlist(pNtk) );

    Init0 = Init1 = Init2 = 0;
    Counter0 = Counter1 = Counter2 = 0;

    Abc_NtkForEachLatch( pNtk, pLatch, i )
    {
        if ( pLatch->pData == (void *)0 )
            Init0++;
        else if ( pLatch->pData == (void *)1 )
            Init1++;
        else if ( pLatch->pData == (void *)2 )
            Init2++;
        else
            assert( 0 );

        if ( Abc_ObjFaninNum( Abc_ObjFanin0(pLatch) ) == 0 )
        {
            Counter0++;
            if ( pLatch->pData == (void *)2 )
                Counter1++;
            else 
            {
                if ( Abc_NtkIsAig(pNtk) )
                {
                    if ( (pLatch->pData == (void *)1) ^ Abc_ObjFaninC0(pLatch) )
                        Counter2++;
                }
                else
                {
                    if ( (pLatch->pData == (void *)1) ^ Abc_NodeIsConst0(pLatch) )
                        Counter2++;
                }
            }
        }
    }
    fprintf( pFile, "Latches = %5d:  Init 0 = %5d. Init 1 = %5d. Init any = %5d.\n", Abc_NtkLatchNum(pNtk), Init0, Init1, Init2 );
    fprintf( pFile, "Constant driver = %4d. Init any = %4d. Init match = %4d.\n", Counter0, Counter1, Counter2 );
    fprintf( pFile, "The network has %d self-feeding latches.\n", Abc_NtkCountSelfFeedLatches(pNtk) );
}

/**Function*************************************************************

  Synopsis    [Prints the distribution of fanins/fanouts in the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkPrintFanio( FILE * pFile, Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    int i, k, nFanins, nFanouts;
    Vec_Int_t * vFanins, * vFanouts;
    int nOldSize, nNewSize;

    vFanins  = Vec_IntAlloc( 0 );
    vFanouts = Vec_IntAlloc( 0 );
    Vec_IntFill( vFanins,  100, 0 );
    Vec_IntFill( vFanouts, 100, 0 );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        nFanins  = Abc_ObjFaninNum(pNode);
        if ( Abc_NtkIsNetlist(pNtk) )
            nFanouts = Abc_ObjFanoutNum( Abc_ObjFanout0(pNode) );
        else
            nFanouts = Abc_ObjFanoutNum(pNode);
        if ( nFanins > vFanins->nSize || nFanouts > vFanouts->nSize )
        {
            nOldSize = vFanins->nSize;
            nNewSize = ABC_MAX(nFanins, nFanouts) + 10;
            Vec_IntGrow( vFanins,  nNewSize  );
            Vec_IntGrow( vFanouts, nNewSize );
            for ( k = nOldSize; k < nNewSize; k++ )
            {
                Vec_IntPush( vFanins,  0  );
                Vec_IntPush( vFanouts, 0 );
            }
        }
        vFanins->pArray[nFanins]++;
        vFanouts->pArray[nFanouts]++;
    }
    fprintf( pFile, "The distribution of fanins and fanouts in the network:\n" );
    fprintf( pFile, "  Number   Nodes with fanin  Nodes with fanout\n" );
    for ( k = 0; k < vFanins->nSize; k++ )
    {
        if ( vFanins->pArray[k] == 0 && vFanouts->pArray[k] == 0 )
            continue;
        fprintf( pFile, "%5d : ", k );
        if ( vFanins->pArray[k] == 0 )
            fprintf( pFile, "              " );
        else
            fprintf( pFile, "%12d  ", vFanins->pArray[k] );
        fprintf( pFile, "    " );
        if ( vFanouts->pArray[k] == 0 )
            fprintf( pFile, "              " );
        else
            fprintf( pFile, "%12d  ", vFanouts->pArray[k] );
        fprintf( pFile, "\n" );
    }
    Vec_IntFree( vFanins );
    Vec_IntFree( vFanouts );
}

/**Function*************************************************************

  Synopsis    [Prints the fanins/fanouts of a node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodePrintFanio( FILE * pFile, Abc_Obj_t * pNode )
{
    Abc_Obj_t * pNode2;
    int i;
    if ( Abc_ObjIsPo(pNode) )
        pNode = Abc_ObjFanin0(pNode);

    fprintf( pFile, "Fanins (%d): ", Abc_ObjFaninNum(pNode) );    
    Abc_ObjForEachFanin( pNode, pNode2, i )
    {
        pNode2->pCopy = NULL;
        fprintf( pFile, " %s", Abc_ObjName(pNode2) );
    }
    fprintf( pFile, "\n" ); 
    
    fprintf( pFile, "\n" );    
    fprintf( pFile, "Fanouts (%d): ", Abc_ObjFaninNum(pNode) );    
    Abc_ObjForEachFanout( pNode, pNode2, i )
    {
        pNode2->pCopy = NULL;
        fprintf( pFile, " %s", Abc_ObjName(pNode2) );
    }
    fprintf( pFile, "\n" );   
}

/**Function*************************************************************

  Synopsis    [Prints the factored form of one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkPrintFactor( FILE * pFile, Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    int i;
    assert( Abc_NtkIsLogicSop(pNtk) );
    Abc_NtkForEachNode( pNtk, pNode, i )
        Abc_NodePrintFactor( pFile, pNode );
}

/**Function*************************************************************

  Synopsis    [Prints the factored form of one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodePrintFactor( FILE * pFile, Abc_Obj_t * pNode )
{
    Vec_Int_t * vFactor;
    if ( Abc_ObjIsCo(pNode) )
        pNode = Abc_ObjFanin0(pNode);
    if ( Abc_ObjIsPi(pNode) )
    {
        printf( "Skipping the PI node.\n" );
        return;
    }
    if ( Abc_ObjIsLatch(pNode) )
    {
        printf( "Skipping the latch.\n" );
        return;
    }
    assert( Abc_ObjIsNode(pNode) );
    vFactor = Ft_Factor( pNode->pData );
    pNode->pCopy = NULL;
    Ft_FactorPrint( stdout, vFactor, NULL, Abc_ObjName(pNode) );
    Vec_IntFree( vFactor );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


