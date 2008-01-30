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
#include "dec.h"

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
void Abc_NtkPrintStats( FILE * pFile, Abc_Ntk_t * pNtk, int fFactored )
{
    int Num;

    fprintf( pFile, "%-13s:",       pNtk->pName );
    fprintf( pFile, " i/o = %4d/%4d", Abc_NtkPiNum(pNtk), Abc_NtkPoNum(pNtk) );

    if ( !Abc_NtkIsSeq(pNtk) )
        fprintf( pFile, "  lat = %4d", Abc_NtkLatchNum(pNtk) );
    else
        fprintf( pFile, "  lat = %4d", Abc_NtkSeqLatchNum(pNtk) );

    if ( Abc_NtkIsNetlist(pNtk) )
    {
        fprintf( pFile, "  net = %5d", Abc_NtkNetNum(pNtk) );
        fprintf( pFile, "  nd = %5d", Abc_NtkNodeNum(pNtk) );
    }
    else if ( Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pFile, "  and = %5d", Abc_NtkNodeNum(pNtk) );
        if ( Num = Abc_NtkGetChoiceNum(pNtk) )
            fprintf( pFile, " (choice = %d)", Num );
        if ( Num = Abc_NtkGetExorNum(pNtk) )
            fprintf( pFile, " (exor = %d)", Num );
    }
    else if ( Abc_NtkIsSeq(pNtk) )
        fprintf( pFile, "  and = %5d", Abc_NtkNodeNum(pNtk) );
    else 
        fprintf( pFile, "  nd = %5d", Abc_NtkNodeNum(pNtk) );

    if ( Abc_NtkHasSop(pNtk) )   
    {
        fprintf( pFile, "  cube = %5d",  Abc_NtkGetCubeNum(pNtk) );
//        fprintf( pFile, "  lit(sop) = %5d",  Abc_NtkGetLitNum(pNtk) );
        if ( fFactored )
            fprintf( pFile, "  lit(fac) = %5d",  Abc_NtkGetLitFactNum(pNtk) );
    }
    else if ( Abc_NtkHasBdd(pNtk) )
        fprintf( pFile, "  bdd = %5d",  Abc_NtkGetBddNodeNum(pNtk) );
    else if ( Abc_NtkHasMapping(pNtk) )
    {
        fprintf( pFile, "  area = %5.2f", Abc_NtkGetMappedArea(pNtk) );
        fprintf( pFile, "  delay = %5.2f", Abc_NtkDelayTrace(pNtk) );
    }
    else if ( !Abc_NtkHasAig(pNtk) )
    {
        assert( 0 );
    }

    if ( Abc_NtkIsStrash(pNtk) )
        fprintf( pFile, "  lev = %3d", Abc_AigGetLevelNum(pNtk) );
    else if ( !Abc_NtkIsSeq(pNtk) )
        fprintf( pFile, "  lev = %3d", Abc_NtkGetLevelNum(pNtk) );

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
    Abc_Obj_t * pLatch, * pFanin;
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
        if ( Abc_LatchIsInit0(pLatch) )
            Init0++;
        else if ( Abc_LatchIsInit1(pLatch) )
            Init1++;
        else if ( Abc_LatchIsInitDc(pLatch) )
            Init2++;
        else
            assert( 0 );

        pFanin = Abc_ObjFanin0(pLatch);
        if ( !Abc_ObjIsNode(pFanin) || !Abc_NodeIsConst(pFanin) )
            continue;

        // the latch input is a constant node
        Counter0++;
        if ( Abc_LatchIsInitDc(pLatch) )
        {
            Counter1++;
            continue;
        }
        // count the number of cases when the constant is equal to the initial value
        if ( Abc_NtkIsStrash(pNtk) )
        {
            if ( Abc_LatchIsInit1(pLatch) == !Abc_ObjFaninC0(pLatch) )
                Counter2++;
        }
        else
        {
            if ( Abc_LatchIsInit1(pLatch) == Abc_NodeIsConst1(pLatch) )
                Counter2++;
        }
    }
//    fprintf( pFile, "%-15s: ", pNtk->pName );
//    fprintf( pFile, "L = %5d: 0 = %4d. 1 = %3d. DC = %4d. ", Abc_NtkLatchNum(pNtk), Init0, Init1, Init2 );
//    fprintf( pFile, "Con = %3d. DC = %3d. Mat = %3d. ", Counter0, Counter1, Counter2 );
//    fprintf( pFile, "SFeed = %2d.\n", Abc_NtkCountSelfFeedLatches(pNtk) );
    fprintf( pFile, "%-15s:  ", pNtk->pName );
    fprintf( pFile, "Lat = %5d: 0 = %4d. 1 = %3d. DC = %4d. \n", Abc_NtkLatchNum(pNtk), Init0, Init1, Init2 );
    fprintf( pFile, "Con = %3d. DC = %3d. Mat = %3d. ", Counter0, Counter1, Counter2 );
    fprintf( pFile, "SFeed = %2d.\n", Abc_NtkCountSelfFeedLatches(pNtk) );
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

    fprintf( pFile, "Node %s", Abc_ObjName(pNode) );    
    fprintf( pFile, "\n" ); 

    fprintf( pFile, "Fanins (%d): ", Abc_ObjFaninNum(pNode) );    
    Abc_ObjForEachFanin( pNode, pNode2, i )
        fprintf( pFile, " %s", Abc_ObjName(pNode2) );
    fprintf( pFile, "\n" ); 
    
    fprintf( pFile, "Fanouts (%d): ", Abc_ObjFaninNum(pNode) );    
    Abc_ObjForEachFanout( pNode, pNode2, i )
        fprintf( pFile, " %s", Abc_ObjName(pNode2) );
    fprintf( pFile, "\n" );   
}

/**Function*************************************************************

  Synopsis    [Prints the factored form of one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkPrintFactor( FILE * pFile, Abc_Ntk_t * pNtk, int fUseRealNames )
{
    Abc_Obj_t * pNode;
    int i;
    assert( Abc_NtkIsSopLogic(pNtk) );
    Abc_NtkForEachNode( pNtk, pNode, i )
        Abc_NodePrintFactor( pFile, pNode, fUseRealNames );
}

/**Function*************************************************************

  Synopsis    [Prints the factored form of one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodePrintFactor( FILE * pFile, Abc_Obj_t * pNode, int fUseRealNames )
{
    Dec_Graph_t * pGraph;
    Vec_Ptr_t * vNamesIn;
    if ( Abc_ObjIsCo(pNode) )
        pNode = Abc_ObjFanin0(pNode);
    if ( Abc_ObjIsPi(pNode) )
    {
        fprintf( pFile, "Skipping the PI node.\n" );
        return;
    }
    if ( Abc_ObjIsLatch(pNode) )
    {
        fprintf( pFile, "Skipping the latch.\n" );
        return;
    }
    assert( Abc_ObjIsNode(pNode) );
    pGraph = Dec_Factor( pNode->pData );
    if ( fUseRealNames )
    {
        vNamesIn = Abc_NodeGetFaninNames(pNode);
        Dec_GraphPrint( stdout, pGraph, (char **)vNamesIn->pArray, Abc_ObjName(pNode) );
        Abc_NodeFreeNames( vNamesIn );
    }
    else
        Dec_GraphPrint( stdout, pGraph, (char **)NULL, Abc_ObjName(pNode) );
    Dec_GraphFree( pGraph );
}


/**Function*************************************************************

  Synopsis    [Prints the level stats of the PO node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkPrintLevel( FILE * pFile, Abc_Ntk_t * pNtk, int fProfile )
{
    Abc_Obj_t * pNode;
    int i, Length;

    // print the delay profile
    if ( fProfile && Abc_NtkHasMapping(pNtk) )
    {
        int nIntervals = 12;
        float DelayMax, DelayCur, DelayDelta;
        int * pLevelCounts;
        int DelayInt, nOutsSum, nOutsTotal;

        // get the max delay and delta
        DelayMax   = Abc_NtkDelayTrace( pNtk );
        DelayDelta = DelayMax/nIntervals;
        // collect outputs by delay
        pLevelCounts = ALLOC( int, nIntervals );
        memset( pLevelCounts, 0, sizeof(int) * nIntervals );
        Abc_NtkForEachCo( pNtk, pNode, i )
        {
            DelayCur  = Abc_NodeReadArrival( Abc_ObjFanin0(pNode) )->Worst;
            DelayInt  = (int)(DelayCur / DelayDelta);
            if ( DelayInt >= nIntervals )
                DelayInt = nIntervals - 1;
            pLevelCounts[DelayInt]++;
        }

        nOutsSum   = 0;
        nOutsTotal = Abc_NtkCoNum(pNtk);
        for ( i = 0; i < nIntervals; i++ )
        {
            nOutsSum += pLevelCounts[i];
            printf( "[%8.2f - %8.2f] :   COs = %4d.   %5.1f %%\n", 
                DelayDelta * i, DelayDelta * (i+1), pLevelCounts[i], 100.0 * nOutsSum/nOutsTotal );
        }
        free( pLevelCounts );
        return;
    }
    else if ( fProfile )
    {
        int LevelMax, * pLevelCounts;
        int nOutsSum, nOutsTotal;

        if ( !Abc_NtkIsStrash(pNtk) )
            Abc_NtkGetLevelNum(pNtk);

        LevelMax = 0;
        Abc_NtkForEachCo( pNtk, pNode, i )
            if ( LevelMax < (int)Abc_ObjFanin0(pNode)->Level )
                LevelMax = Abc_ObjFanin0(pNode)->Level;
        pLevelCounts = ALLOC( int, LevelMax + 1 );
        memset( pLevelCounts, 0, sizeof(int) * (LevelMax + 1) );
        Abc_NtkForEachCo( pNtk, pNode, i )
            pLevelCounts[Abc_ObjFanin0(pNode)->Level]++;

        nOutsSum   = 0;
        nOutsTotal = Abc_NtkCoNum(pNtk);
        for ( i = 0; i <= LevelMax; i++ )
            if ( pLevelCounts[i] )
            {
                nOutsSum += pLevelCounts[i];
                printf( "Level = %4d.  COs = %4d.   %5.1f %%\n", i, pLevelCounts[i], 100.0 * nOutsSum/nOutsTotal );
            }
        free( pLevelCounts );
        return;
    }
    assert( Abc_NtkIsStrash(pNtk) );

    // find the longest name
    Length = 0;
    Abc_NtkForEachCo( pNtk, pNode, i )
        if ( Length < (int)strlen(Abc_ObjName(pNode)) )
            Length = strlen(Abc_ObjName(pNode));
    if ( Length < 5 )
        Length = 5;
    // print stats for each output
    Abc_NtkForEachCo( pNtk, pNode, i )
    {
        fprintf( pFile, "CO %4d :  %*s    ", i, Length, Abc_ObjName(pNode) ); 
        Abc_NodePrintLevel( pFile, pNode );
    }
}

/**Function*************************************************************

  Synopsis    [Prints the factored form of one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodePrintLevel( FILE * pFile, Abc_Obj_t * pNode )
{
    Abc_Obj_t * pDriver;
    Vec_Ptr_t * vNodes;

    pDriver = Abc_ObjIsCo(pNode)? Abc_ObjFanin0(pNode) : pNode;
    if ( Abc_ObjIsPi(pDriver) )
    {
        fprintf( pFile, "Primary input.\n" );
        return;
    }
    if ( Abc_ObjIsLatch(pDriver) )
    {
        fprintf( pFile, "Latch.\n" );
        return;
    }
    if ( Abc_NodeIsConst(pDriver) )
    {
        fprintf( pFile, "Constant %d.\n", !Abc_ObjFaninC0(pNode) );
        return;
    }
    // print the level
    fprintf( pFile, "Level = %3d.  ", pDriver->Level );
    // print the size of MFFC
    fprintf( pFile, "Mffc = %5d.  ", Abc_NodeMffcSize(pDriver) );
    // print the size of the shole cone
    vNodes = Abc_NtkDfsNodes( pNode->pNtk, &pDriver, 1 );
    fprintf( pFile, "Cone = %5d.  ", Vec_PtrSize(vNodes) );
    Vec_PtrFree( vNodes );
    fprintf( pFile, "\n" );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


