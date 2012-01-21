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

#include <math.h>
#include "src/base/abc/abc.h"
#include "src/bool/dec/dec.h"
#include "src/base/main/main.h"
#include "src/map/mio/mio.h"
#include "src/aig/aig/aig.h"
#include "src/map/if/if.h"
#include "src/misc/extra/extraBdd.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

//extern int s_TotalNodes = 0;
//extern int s_TotalChanges = 0;

int s_MappingTime = 0;
int s_MappingMem = 0;
int s_ResubTime = 0;
int s_ResynTime = 0;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [If the network is best, saves it in "best.blif" and returns 1.]

  Description [If the networks are incomparable, saves the new network, 
  returns its parameters in the internal parameter structure, and returns 1.
  If the new network is not a logic network, quits without saving and returns 0.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkCompareAndSaveBest( Abc_Ntk_t * pNtk )
{
    extern void Io_Write( Abc_Ntk_t * pNtk, char * pFileName, Io_FileType_t FileType );
    static struct ParStruct {
        char * pName;  // name of the best saved network
        int    Depth;  // depth of the best saved network
        int    Flops;  // flops in the best saved network 
        int    Nodes;  // nodes in the best saved network
        int    nPis;   // the number of primary inputs
        int    nPos;   // the number of primary outputs
    } ParsNew, ParsBest = { 0 };
    // free storage for the name
    if ( pNtk == NULL )
    {
        ABC_FREE( ParsBest.pName );
        return 0;
    }
    // quit if not a logic network
    if ( !Abc_NtkIsLogic(pNtk) )
        return 0;
    // get the parameters
    ParsNew.Depth = Abc_NtkLevel( pNtk );
    ParsNew.Flops = Abc_NtkLatchNum( pNtk );
    ParsNew.Nodes = Abc_NtkNodeNum( pNtk );
    ParsNew.nPis  = Abc_NtkPiNum( pNtk );
    ParsNew.nPos  = Abc_NtkPoNum( pNtk );
    // reset the parameters if the network has the same name
    if (  ParsBest.pName == NULL ||
          strcmp(ParsBest.pName, pNtk->pName) ||
          ParsBest.Depth >  ParsNew.Depth ||
         (ParsBest.Depth == ParsNew.Depth && ParsBest.Flops >  ParsNew.Flops) ||
         (ParsBest.Depth == ParsNew.Depth && ParsBest.Flops == ParsNew.Flops && ParsBest.Nodes >  ParsNew.Nodes) )
    {
        ABC_FREE( ParsBest.pName );
        ParsBest.pName = Extra_UtilStrsav( pNtk->pName );
        ParsBest.Depth = ParsNew.Depth; 
        ParsBest.Flops = ParsNew.Flops; 
        ParsBest.Nodes = ParsNew.Nodes; 
        ParsBest.nPis  = ParsNew.nPis; 
        ParsBest.nPos  = ParsNew.nPos;
        // writ the network
        Io_Write( pNtk, "best.blif", IO_FILE_BLIF );
        return 1;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Marks nodes for power-optimization.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float Abc_NtkMfsTotalSwitching( Abc_Ntk_t * pNtk )
{
    extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
    extern Vec_Int_t * Saig_ManComputeSwitchProbs( Aig_Man_t * p, int nFrames, int nPref, int fProbOne );
    Vec_Int_t * vSwitching;
    float * pSwitching;
    Abc_Ntk_t * pNtkStr;
    Aig_Man_t * pAig;
    Aig_Obj_t * pObjAig;
    Abc_Obj_t * pObjAbc, * pObjAbc2;
    float Result = (float)0;
    int i;
    // strash the network
    pNtkStr = Abc_NtkStrash( pNtk, 0, 1, 0 );
    Abc_NtkForEachObj( pNtk, pObjAbc, i )
        if ( Abc_ObjRegular((Abc_Obj_t *)pObjAbc->pTemp)->Type == ABC_FUNC_NONE )
            pObjAbc->pTemp = NULL;
    // map network into an AIG
    pAig = Abc_NtkToDar( pNtkStr, 0, (int)(Abc_NtkLatchNum(pNtk) > 0) );
    vSwitching = Saig_ManComputeSwitchProbs( pAig, 48, 16, 0 );
    pSwitching = (float *)vSwitching->pArray;
    Abc_NtkForEachObj( pNtk, pObjAbc, i )
    {
        if ( (pObjAbc2 = Abc_ObjRegular((Abc_Obj_t *)pObjAbc->pTemp)) && (pObjAig = Aig_Regular((Aig_Obj_t *)pObjAbc2->pTemp)) )
        {
            Result += Abc_ObjFanoutNum(pObjAbc) * pSwitching[pObjAig->Id];
//            printf( "%d = %.2f\n", i, Abc_ObjFanoutNum(pObjAbc) * pSwitching[pObjAig->Id] );
        }
    }
    Vec_IntFree( vSwitching );
    Aig_ManStop( pAig );
    Abc_NtkDelete( pNtkStr );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Compute area using LUT library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float Abc_NtkGetArea( Abc_Ntk_t * pNtk )
{
    If_Lib_t * pLutLib;
    Abc_Obj_t * pObj;
    float Counter = 0.0;
    int i;
    assert( Abc_NtkIsLogic(pNtk) );
    // get the library
    pLutLib = (If_Lib_t *)Abc_FrameReadLibLut();
    if ( pLutLib && pLutLib->LutMax >= Abc_NtkGetFaninMax(pNtk) )
    {
        Abc_NtkForEachNode( pNtk, pObj, i )
            Counter += pLutLib->pLutAreas[Abc_ObjFaninNum(pObj)];
    }
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Print the vital stats of the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkPrintStats( Abc_Ntk_t * pNtk, int fFactored, int fSaveBest, int fDumpResult, int fUseLutLib, int fPrintMuxes, int fPower, int fGlitch )
{
    FILE * pFile = stdout;
    int Num;
    if ( fSaveBest )
        Abc_NtkCompareAndSaveBest( pNtk );
    if ( fDumpResult )
    {
        char Buffer[1000] = {0};
        const char * pNameGen = pNtk->pSpec? Extra_FileNameGeneric( pNtk->pSpec ) : "nameless_";
        sprintf( Buffer, "%s_dump.blif", pNameGen );
        Io_Write( pNtk, Buffer, IO_FILE_BLIF );
        if ( pNtk->pSpec ) ABC_FREE( pNameGen );
    }

//    if ( Abc_NtkIsStrash(pNtk) )
//        Abc_AigCountNext( pNtk->pManFunc );

    fprintf( pFile, "%-13s:",       pNtk->pName );
    fprintf( pFile, " i/o =%5d/%5d", Abc_NtkPiNum(pNtk), Abc_NtkPoNum(pNtk) );
    if ( Abc_NtkConstrNum(pNtk) )
        fprintf( pFile, "(c=%d)", Abc_NtkConstrNum(pNtk) );
    if ( pNtk->nRealPos )
        fprintf( pFile, "(p=%d)", Abc_NtkPoNum(pNtk) - pNtk->nRealPos );
    fprintf( pFile, "  lat =%5d", Abc_NtkLatchNum(pNtk) );
    if ( Abc_NtkIsNetlist(pNtk) )
    {
        fprintf( pFile, "  net =%5d", Abc_NtkNetNum(pNtk) );
        fprintf( pFile, "  nd =%5d",  Abc_NtkNodeNum(pNtk) );
        fprintf( pFile, "  wbox =%3d", Abc_NtkWhiteboxNum(pNtk) );
        fprintf( pFile, "  bbox =%3d", Abc_NtkBlackboxNum(pNtk) );
    }
    else if ( Abc_NtkIsStrash(pNtk) )
    {        
        fprintf( pFile, "  and =%7d", Abc_NtkNodeNum(pNtk) );
        if ( (Num = Abc_NtkGetChoiceNum(pNtk)) )
            fprintf( pFile, " (choice = %d)", Num );
        if ( fPrintMuxes )
        {
            extern int Abc_NtkCountMuxes( Abc_Ntk_t * pNtk );
            Num = Abc_NtkGetExorNum(pNtk);
            fprintf( pFile, " (exor = %d)", Num );
            fprintf( pFile, " (mux = %d)", Abc_NtkCountMuxes(pNtk)-Num );
            fprintf( pFile, " (pure and = %d)", Abc_NtkNodeNum(pNtk) - (Abc_NtkCountMuxes(pNtk) * 3) );
        }
    }
    else 
    {
        fprintf( pFile, "  nd =%6d", Abc_NtkNodeNum(pNtk) );
        fprintf( pFile, "  edge =%7d", Abc_NtkGetTotalFanins(pNtk) );
    }

    if ( Abc_NtkIsStrash(pNtk) || Abc_NtkIsNetlist(pNtk) )
    {
    }
    else if ( Abc_NtkHasSop(pNtk) )   
    {

        fprintf( pFile, "  cube =%6d",  Abc_NtkGetCubeNum(pNtk) );
//        fprintf( pFile, "  lit(sop) = %5d",  Abc_NtkGetLitNum(pNtk) );
        if ( fFactored )
            fprintf( pFile, "  lit(fac) =%6d",  Abc_NtkGetLitFactNum(pNtk) );
    }
    else if ( Abc_NtkHasAig(pNtk) )
        fprintf( pFile, "  aig  =%6d",  Abc_NtkGetAigNodeNum(pNtk) );
    else if ( Abc_NtkHasBdd(pNtk) )
        fprintf( pFile, "  bdd  =%6d",  Abc_NtkGetBddNodeNum(pNtk) );
    else if ( Abc_NtkHasMapping(pNtk) )
    {
        fprintf( pFile, "  area =%5.2f", Abc_NtkGetMappedArea(pNtk) );
        fprintf( pFile, "  delay =%5.2f", Abc_NtkDelayTrace(pNtk) );
    }
    else if ( !Abc_NtkHasBlackbox(pNtk) )
    {
        assert( 0 );
    }

    if ( Abc_NtkIsStrash(pNtk) )
    {
        extern int Abc_NtkGetMultiRefNum( Abc_Ntk_t * pNtk );
        fprintf( pFile, "  lev =%3d", Abc_AigLevel(pNtk) );
//        fprintf( pFile, "  ff = %5d", Abc_NtkNodeNum(pNtk) + 2 * (Abc_NtkCoNum(pNtk)+Abc_NtkGetMultiRefNum(pNtk)) );
//        fprintf( pFile, "  var = %5d", Abc_NtkCiNum(pNtk) + Abc_NtkCoNum(pNtk)+Abc_NtkGetMultiRefNum(pNtk) );
    }
    else 
        fprintf( pFile, "  lev =%3d", Abc_NtkLevel(pNtk) );
    if ( fUseLutLib && Abc_FrameReadLibLut() )
        fprintf( pFile, "  delay =%5.2f", Abc_NtkDelayTraceLut(pNtk, 1) );
    if ( fUseLutLib && Abc_FrameReadLibLut() )
        fprintf( pFile, "  area =%5.2f", Abc_NtkGetArea(pNtk) );
    if ( fPower )
        fprintf( pFile, "  power =%7.2f", Abc_NtkMfsTotalSwitching(pNtk) );
    if ( fGlitch )
    {
        extern float Abc_NtkMfsTotalGlitching( Abc_Ntk_t * pNtk );
        if ( Abc_NtkIsLogic(pNtk) && Abc_NtkGetFaninMax(pNtk) <= 6 )
            fprintf( pFile, "  glitch =%7.2f %%", Abc_NtkMfsTotalGlitching(pNtk) );
        else
            printf( "\nCurrently computes glitching only for K-LUT networks with K <= 6." ); 
    }
    fprintf( pFile, "\n" );

    {
//        extern int Abc_NtkPrintSubraphSizes( Abc_Ntk_t * pNtk );
//        Abc_NtkPrintSubraphSizes( pNtk );
    }

//    Abc_NtkCrossCut( pNtk );

    // print the statistic into a file
/*
    {
        FILE * pTable;
        pTable = fopen( "ibm/seq_stats.txt", "a+" );
//        fprintf( pTable, "%s ",  pNtk->pName );
//        fprintf( pTable, "%d ", Abc_NtkPiNum(pNtk) );
//        fprintf( pTable, "%d ", Abc_NtkPoNum(pNtk) );
        fprintf( pTable, "%d ", Abc_NtkNodeNum(pNtk) );
        fprintf( pTable, "%d ", Abc_NtkLatchNum(pNtk) );
        fprintf( pTable, "%d ", Abc_NtkLevel(pNtk) );
        fprintf( pTable, "\n" );
        fclose( pTable );
    }
*/

/*
    // print the statistic into a file
    {
        FILE * pTable;
        pTable = fopen( "ucsb/stats.txt", "a+" );
//        fprintf( pTable, "%s ",  pNtk->pSpec );
        fprintf( pTable, "%d ",  Abc_NtkNodeNum(pNtk) );
//        fprintf( pTable, "%d ",  Abc_NtkLevel(pNtk) );
//        fprintf( pTable, "%.0f ", Abc_NtkGetMappedArea(pNtk) );
//        fprintf( pTable, "%.2f ", Abc_NtkDelayTrace(pNtk) );
        fprintf( pTable, "\n" );
        fclose( pTable );
    }
*/

/*
    // print the statistic into a file
    {
        FILE * pTable;
        pTable = fopen( "x/stats_new.txt", "a+" );
        fprintf( pTable, "%s ",  pNtk->pName );
//        fprintf( pTable, "%d ", Abc_NtkPiNum(pNtk) );
//        fprintf( pTable, "%d ", Abc_NtkPoNum(pNtk) );
//        fprintf( pTable, "%d ", Abc_NtkLevel(pNtk) );
//        fprintf( pTable, "%d ", Abc_NtkNodeNum(pNtk) );
//        fprintf( pTable, "%d ", Abc_NtkGetTotalFanins(pNtk) );
//        fprintf( pTable, "%d ", Abc_NtkLatchNum(pNtk) );
//        fprintf( pTable, "%.2f ", (float)(s_MappingMem)/(float)(1<<20) );
        fprintf( pTable, "%.2f", (float)(s_MappingTime)/(float)(CLOCKS_PER_SEC) );
//        fprintf( pTable, "%.2f", (float)(s_ResynTime)/(float)(CLOCKS_PER_SEC) );
        fprintf( pTable, "\n" );
        fclose( pTable );

        s_ResynTime = 0;
    }
*/

/*
    // print the statistic into a file
    {
        static int Counter = 0;
        extern int timeRetime;
        FILE * pTable;
        Counter++;
        pTable = fopen( "d/stats.txt", "a+" );
        fprintf( pTable, "%s ", pNtk->pName );
//        fprintf( pTable, "%d ", Abc_NtkPiNum(pNtk) );
//        fprintf( pTable, "%d ", Abc_NtkPoNum(pNtk) );
//        fprintf( pTable, "%d ", Abc_NtkLatchNum(pNtk) );
        fprintf( pTable, "%d ", Abc_NtkNodeNum(pNtk) );
        fprintf( pTable, "%.2f ", (float)(timeRetime)/(float)(CLOCKS_PER_SEC) );
        fprintf( pTable, "\n" );
        fclose( pTable );
    }


/*
    s_TotalNodes += Abc_NtkNodeNum(pNtk);
    printf( "Total nodes = %6d   %6.2f Mb   Changes = %6d.\n", 
        s_TotalNodes, s_TotalNodes * 20.0 / (1<<20), s_TotalChanges );
*/

//    if ( Abc_NtkHasSop(pNtk) )
//        printf( "The total number of cube pairs = %d.\n", Abc_NtkGetCubePairNum(pNtk) );
   
    fflush( stdout );
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
//        fprintf( pFile, " %s(%d)", Abc_ObjName(pObj), Abc_ObjFanoutNum(pObj) );
    fprintf( pFile, "\n" );   

    fprintf( pFile, "Primary outputs (%d):", Abc_NtkPoNum(pNtk) );    
    Abc_NtkForEachPo( pNtk, pObj, i )
        fprintf( pFile, " %s", Abc_ObjName(pObj) );
    fprintf( pFile, "\n" );    

    fprintf( pFile, "Latches (%d):  ", Abc_NtkLatchNum(pNtk) );  
    Abc_NtkForEachLatch( pNtk, pObj, i )
        fprintf( pFile, " %s(%s=%s)", Abc_ObjName(pObj), 
            Abc_ObjName(Abc_ObjFanout0(pObj)), Abc_ObjName(Abc_ObjFanin0(pObj)) );
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
    int InitNums[4], Init;

    assert( !Abc_NtkIsNetlist(pNtk) );
    if ( Abc_NtkLatchNum(pNtk) == 0 )
    {
        fprintf( pFile, "The network is combinational.\n" );
        return;
    }

    for ( i = 0; i < 4; i++ )    
        InitNums[i] = 0;
    Counter0 = Counter1 = Counter2 = 0;
    Abc_NtkForEachLatch( pNtk, pLatch, i )
    {
        Init = Abc_LatchInit( pLatch );
        assert( Init < 4 );
        InitNums[Init]++;

        pFanin = Abc_ObjFanin0(Abc_ObjFanin0(pLatch));
        if ( Abc_NtkIsLogic(pNtk) )
        {
            if ( !Abc_NodeIsConst(pFanin) )
                continue;
        }
        else if ( Abc_NtkIsStrash(pNtk) )
        {
            if ( !Abc_AigNodeIsConst(pFanin) )
                continue;
        }
        else
            assert( 0 );

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
            if ( Abc_LatchIsInit1(pLatch) == Abc_NodeIsConst1(Abc_ObjFanin0(Abc_ObjFanin0(pLatch))) )
                Counter2++;
        }
    }
//    fprintf( pFile, "%-15s:  ", pNtk->pName );
    fprintf( pFile, "Total latches = %5d. Init0 = %d. Init1 = %d. InitDC = %d. Const data = %d.\n", 
        Abc_NtkLatchNum(pNtk), InitNums[1], InitNums[2], InitNums[3], Counter0 );
//    fprintf( pFile, "Const fanin = %3d. DC init = %3d. Matching init = %3d. ", Counter0, Counter1, Counter2 );
//    fprintf( pFile, "Self-feed latches = %2d.\n", -1 ); //Abc_NtkCountSelfFeedLatches(pNtk) );
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
//            nFanouts = Abc_NodeMffcSize(pNode);
        if ( nFanins > vFanins->nSize || nFanouts > vFanouts->nSize )
        {
            nOldSize = vFanins->nSize;
            nNewSize = Abc_MaxInt(nFanins, nFanouts) + 10;
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

  Synopsis    [Prints the distribution of fanins/fanouts in the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkPrintFanioNew( FILE * pFile, Abc_Ntk_t * pNtk, int fMffc )
{
    char Buffer[100];
    Abc_Obj_t * pNode;
    Vec_Int_t * vFanins, * vFanouts;
    int nFanins, nFanouts, nFaninsMax, nFanoutsMax, nFaninsAll, nFanoutsAll;
    int i, k, nSizeMax;

    // determine the largest fanin and fanout
    nFaninsMax = nFanoutsMax = 0;
    nFaninsAll = nFanoutsAll = 0;
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        if ( fMffc && Abc_ObjFanoutNum(pNode) == 1 )
            continue;
        nFanins  = Abc_ObjFaninNum(pNode);
        if ( Abc_NtkIsNetlist(pNtk) )
            nFanouts = Abc_ObjFanoutNum( Abc_ObjFanout0(pNode) );
        else if ( fMffc )
            nFanouts = Abc_NodeMffcSize(pNode);
        else
            nFanouts = Abc_ObjFanoutNum(pNode);
        nFaninsAll  += nFanins;
        nFanoutsAll += nFanouts;
        nFaninsMax   = Abc_MaxInt( nFaninsMax, nFanins );
        nFanoutsMax  = Abc_MaxInt( nFanoutsMax, nFanouts );
    }

    // allocate storage for fanin/fanout numbers
    nSizeMax = Abc_MaxInt( 10 * (Abc_Base10Log(nFaninsMax) + 1), 10 * (Abc_Base10Log(nFanoutsMax) + 1) );
    vFanins  = Vec_IntStart( nSizeMax );
    vFanouts = Vec_IntStart( nSizeMax );

    // count the number of fanins and fanouts
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        if ( fMffc && Abc_ObjFanoutNum(pNode) == 1 )
            continue;
        nFanins  = Abc_ObjFaninNum(pNode);
        if ( Abc_NtkIsNetlist(pNtk) )
            nFanouts = Abc_ObjFanoutNum( Abc_ObjFanout0(pNode) );
        else if ( fMffc )
            nFanouts = Abc_NodeMffcSize(pNode);
        else
            nFanouts = Abc_ObjFanoutNum(pNode);

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

    fprintf( pFile, "The distribution of fanins and fanouts in the network:\n" );
    fprintf( pFile, "         Number   Nodes with fanin  Nodes with fanout\n" );
    for ( k = 0; k < nSizeMax; k++ )
    {
        if ( vFanins->pArray[k] == 0 && vFanouts->pArray[k] == 0 )
            continue;
        if ( k < 10 )
            fprintf( pFile, "%15d : ", k );
        else
        {
            sprintf( Buffer, "%d - %d", (int)pow((double)10, k/10) * (k%10), (int)pow((double)10, k/10) * (k%10+1) - 1 ); 
            fprintf( pFile, "%15s : ", Buffer );
        }
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

    fprintf( pFile, "Fanins: Max = %d. Ave = %.2f.  Fanouts: Max = %d. Ave =  %.2f.\n", 
        nFaninsMax,  1.0*nFaninsAll/Abc_NtkNodeNum(pNtk), 
        nFanoutsMax, 1.0*nFanoutsAll/Abc_NtkNodeNum(pNtk)  );
/*
    Abc_NtkForEachCi( pNtk, pNode, i )
    {
        printf( "%d ", Abc_ObjFanoutNum(pNode) );
    }
    printf( "\n" );
*/
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

  Synopsis    [Prints the MFFCs of the nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkPrintMffc( FILE * pFile, Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    int i;
    extern void Abc_NodeMffcConeSuppPrint( Abc_Obj_t * pNode );
    Abc_NtkForEachNode( pNtk, pNode, i )
        if ( Abc_ObjFanoutNum(pNode) > 1 )
            Abc_NodeMffcConeSuppPrint( pNode );
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
    pGraph = Dec_Factor( (char *)pNode->pData );
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
void Abc_NtkPrintLevel( FILE * pFile, Abc_Ntk_t * pNtk, int fProfile, int fListNodes )
{
    Abc_Obj_t * pNode;
    int i, k, Length;

    if ( fListNodes )
    {
        int nLevels;
        nLevels = Abc_NtkLevel(pNtk);
        printf( "Nodes by level:\n" );
        for ( i = 0; i <= nLevels; i++ )
        {
            printf( "%2d : ", i );
            Abc_NtkForEachNode( pNtk, pNode, k )
                if ( (int)pNode->Level == i )
                    printf( " %s", Abc_ObjName(pNode) );
            printf( "\n" );
        }
        return;
    }

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
        pLevelCounts = ABC_ALLOC( int, nIntervals );
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
        ABC_FREE( pLevelCounts );
        return;
    }
    else if ( fProfile )
    {
        int LevelMax, * pLevelCounts;
        int nOutsSum, nOutsTotal;

        if ( !Abc_NtkIsStrash(pNtk) )
            Abc_NtkLevel(pNtk);

        LevelMax = 0;
        Abc_NtkForEachCo( pNtk, pNode, i )
            if ( LevelMax < (int)Abc_ObjFanin0(pNode)->Level )
                LevelMax = Abc_ObjFanin0(pNode)->Level;
        pLevelCounts = ABC_ALLOC( int, LevelMax + 1 );
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
        ABC_FREE( pLevelCounts );
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

/**Function*************************************************************

  Synopsis    [Prints the factored form of one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodePrintKMap( Abc_Obj_t * pNode, int fUseRealNames )
{
    Vec_Ptr_t * vNamesIn;
    if ( fUseRealNames )
    {
        vNamesIn = Abc_NodeGetFaninNames(pNode);
        Extra_PrintKMap( stdout, (DdManager *)pNode->pNtk->pManFunc, (DdNode *)pNode->pData, Cudd_Not(pNode->pData), 
            Abc_ObjFaninNum(pNode), NULL, 0, (char **)vNamesIn->pArray );
        Abc_NodeFreeNames( vNamesIn );
    }
    else
        Extra_PrintKMap( stdout, (DdManager *)pNode->pNtk->pManFunc, (DdNode *)pNode->pData, Cudd_Not(pNode->pData), 
            Abc_ObjFaninNum(pNode), NULL, 0, NULL );

}

/**Function*************************************************************

  Synopsis    [Prints statistics about gates used in the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkPrintGates( Abc_Ntk_t * pNtk, int fUseLibrary )
{
    Abc_Obj_t * pObj;
    int fHasBdds, i;
    int CountConst, CountBuf, CountInv, CountAnd, CountOr, CountOther, CounterTotal;
    char * pSop;

    if ( fUseLibrary && Abc_NtkHasMapping(pNtk) )
    {
        Mio_Gate_t ** ppGates;
        double Area, AreaTotal;
        int Counter, nGates, i;

        // clean value of all gates
        nGates = Mio_LibraryReadGateNum( (Mio_Library_t *)pNtk->pManFunc );
        ppGates = Mio_LibraryReadGatesByName( (Mio_Library_t *)pNtk->pManFunc );
        for ( i = 0; i < nGates; i++ )
            Mio_GateSetValue( ppGates[i], 0 );

        // count the gates by name
        CounterTotal = 0;
        Abc_NtkForEachNode( pNtk, pObj, i )
        {
            if ( i == 0 ) continue;
            Mio_GateSetValue( (Mio_Gate_t *)pObj->pData, 1 + Mio_GateReadValue((Mio_Gate_t *)pObj->pData) );
            CounterTotal++;
        }
        // print the gates
        AreaTotal = Abc_NtkGetMappedArea(pNtk);
        for ( i = 0; i < nGates; i++ )
        {
            Counter = Mio_GateReadValue( ppGates[i] );
            if ( Counter == 0 )
                continue;
            Area = Counter * Mio_GateReadArea( ppGates[i] );
            printf( "%-12s   Fanin = %2d   Instance = %8d   Area = %10.2f   %6.2f %%\n", 
                Mio_GateReadName( ppGates[i] ), 
                Mio_GateReadInputs( ppGates[i] ), 
                Counter, Area, 100.0 * Area / AreaTotal );
        }
        printf( "%-12s                Instance = %8d   Area = %10.2f   %6.2f %%\n", "TOTAL", 
            CounterTotal, AreaTotal, 100.0 );
        return;
    }

    if ( Abc_NtkIsAigLogic(pNtk) )
        return;

    // transform logic functions from BDD to SOP
    if ( (fHasBdds = Abc_NtkIsBddLogic(pNtk)) )
    {
        if ( !Abc_NtkBddToSop(pNtk, 0) )
        {
            printf( "Abc_NtkPrintGates(): Converting to SOPs has failed.\n" );
            return;
        }
    }

    // get hold of the SOP of the node
    CountConst = CountBuf = CountInv = CountAnd = CountOr = CountOther = CounterTotal = 0;
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        if ( i == 0 ) continue;
        if ( Abc_NtkHasMapping(pNtk) )
            pSop = Mio_GateReadSop((Mio_Gate_t *)pObj->pData);
        else
            pSop = (char *)pObj->pData;
        // collect the stats
        if ( Abc_SopIsConst0(pSop) || Abc_SopIsConst1(pSop) )
            CountConst++;
        else if ( Abc_SopIsBuf(pSop) )
            CountBuf++;
        else if ( Abc_SopIsInv(pSop) )
            CountInv++;
        else if ( (!Abc_SopIsComplement(pSop) && Abc_SopIsAndType(pSop)) ||
                  ( Abc_SopIsComplement(pSop) && Abc_SopIsOrType(pSop)) )
            CountAnd++;
        else if ( ( Abc_SopIsComplement(pSop) && Abc_SopIsAndType(pSop)) ||
                  (!Abc_SopIsComplement(pSop) && Abc_SopIsOrType(pSop)) )
            CountOr++;
        else
            CountOther++;
        CounterTotal++;
    }
    printf( "Const        = %8d    %6.2f %%\n", CountConst  ,  100.0 * CountConst   / CounterTotal );
    printf( "Buffer       = %8d    %6.2f %%\n", CountBuf    ,  100.0 * CountBuf     / CounterTotal );
    printf( "Inverter     = %8d    %6.2f %%\n", CountInv    ,  100.0 * CountInv     / CounterTotal );
    printf( "And          = %8d    %6.2f %%\n", CountAnd    ,  100.0 * CountAnd     / CounterTotal );
    printf( "Or           = %8d    %6.2f %%\n", CountOr     ,  100.0 * CountOr      / CounterTotal );
    printf( "Other        = %8d    %6.2f %%\n", CountOther  ,  100.0 * CountOther   / CounterTotal );
    printf( "TOTAL        = %8d    %6.2f %%\n", CounterTotal,  100.0 * CounterTotal / CounterTotal );

    // convert the network back into BDDs if this is how it was
    if ( fHasBdds )
        Abc_NtkSopToBdd(pNtk);
}

/**Function*************************************************************

  Synopsis    [Prints statistics about gates used in the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkPrintSharing( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vNodes1, * vNodes2;
    Abc_Obj_t * pObj1, * pObj2, * pNode1, * pNode2;
    int i, k, m, n, Counter;

    // print the template
    printf( "Statistics about sharing of logic nodes among the CO pairs.\n" );
    printf( "(CO1,CO2)=NumShared : " );
    // go though the CO pairs
    Abc_NtkForEachCo( pNtk, pObj1, i )
    {
        vNodes1 = Abc_NtkDfsNodes( pNtk, &pObj1, 1 );
        // mark the nodes
        Vec_PtrForEachEntry( Abc_Obj_t *, vNodes1, pNode1, m )
            pNode1->fMarkA = 1;
        // go through the second COs
        Abc_NtkForEachCo( pNtk, pObj2, k )
        {
            if ( i >= k )
                continue;
            vNodes2 = Abc_NtkDfsNodes( pNtk, &pObj2, 1 );
            // count the number of marked
            Counter = 0;
            Vec_PtrForEachEntry( Abc_Obj_t *, vNodes2, pNode2, n )
                Counter += pNode2->fMarkA;
            // print
            printf( "(%d,%d)=%d ", i, k, Counter );
            Vec_PtrFree( vNodes2 );
        }
        // unmark the nodes
        Vec_PtrForEachEntry( Abc_Obj_t *, vNodes1, pNode1, m )
            pNode1->fMarkA = 0;
        Vec_PtrFree( vNodes1 );
    }
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    [Prints info for each output cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkPrintStrSupports( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vSupp, * vNodes;
    Abc_Obj_t * pObj;
    int i;
    printf( "Structural support info:\n" );
    Abc_NtkForEachCo( pNtk, pObj, i )
    {
        vSupp  = Abc_NtkNodeSupport( pNtk, &pObj, 1 );
        vNodes = Abc_NtkDfsNodes( pNtk, &pObj, 1 );
        printf( "%5d  %20s :  Cone = %5d.  Supp = %5d.\n", 
            i, Abc_ObjName(pObj), vNodes->nSize, vSupp->nSize );
        Vec_PtrFree( vNodes );
        Vec_PtrFree( vSupp );
    }
}

/**Function*************************************************************

  Synopsis    [Prints information about the object.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ObjPrint( FILE * pFile, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanin;
    int i;
    fprintf( pFile, "Object %5d : ", pObj->Id );
    switch ( pObj->Type )
    {
        case ABC_OBJ_NONE: 
            fprintf( pFile, "NONE   " );  
            break;
        case ABC_OBJ_CONST1: 
            fprintf( pFile, "Const1 " );  
            break;
        case ABC_OBJ_PI:     
            fprintf( pFile, "PI     " );  
            break;
        case ABC_OBJ_PO:     
            fprintf( pFile, "PO     " );  
            break;
        case ABC_OBJ_BI:     
            fprintf( pFile, "BI     " );  
            break;
        case ABC_OBJ_BO:     
            fprintf( pFile, "BO     " );  
            break;
        case ABC_OBJ_NET:  
            fprintf( pFile, "Net    " );  
            break;
        case ABC_OBJ_NODE: 
            fprintf( pFile, "Node   " );  
            break;
        case ABC_OBJ_LATCH:     
            fprintf( pFile, "Latch  " );  
            break;
        case ABC_OBJ_WHITEBOX: 
            fprintf( pFile, "Whitebox" );  
            break;
        case ABC_OBJ_BLACKBOX:     
            fprintf( pFile, "Blackbox" );  
            break;
        default:
            assert(0); 
            break;
    }
    // print the fanins
    fprintf( pFile, " Fanins ( " );
    Abc_ObjForEachFanin( pObj, pFanin, i )
        fprintf( pFile, "%d ", pFanin->Id );
    fprintf( pFile, ") " );
/*
    fprintf( pFile, " Fanouts ( " );
    Abc_ObjForEachFanout( pObj, pFanin, i )
        fprintf( pFile, "%d(%c) ", pFanin->Id, Abc_NodeIsTravIdCurrent(pFanin)? '+' : '-' );
    fprintf( pFile, ") " );
*/
    // print the logic function
    if ( Abc_ObjIsNode(pObj) && Abc_NtkIsSopLogic(pObj->pNtk) )
        fprintf( pFile, " %s", (char*)pObj->pData );
    else
        fprintf( pFile, "\n" );
}


/**Function*************************************************************

  Synopsis    [Checks the status of the miter.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkPrintMiter( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj, * pChild, * pConst1 = Abc_AigConst1(pNtk);
    int i, iOut = -1, Time = clock();
    int nUnsat = 0;
    int nSat   = 0;
    int nUndec = 0;
    int nPis   = 0;
    Abc_NtkForEachPi( pNtk, pObj, i )
        nPis += (int)( Abc_ObjFanoutNum(pObj) > 0 );
    Abc_NtkForEachPo( pNtk, pObj, i )
    {
        pChild = Abc_ObjChild0(pObj);
        // check if the output is constant 0
        if ( pChild == Abc_ObjNot(pConst1) )
            nUnsat++;
        // check if the output is constant 1
        else if ( pChild == pConst1 )
        {
            nSat++;
            if ( iOut == -1 )
                iOut = i;
        }
        // check if the output is a primary input
        else if ( Abc_ObjIsPi(Abc_ObjRegular(pChild)) )
        {
            nSat++;
            if ( iOut == -1 )
                iOut = i;
        }
    // check if the output is 1 for the 0000 pattern
        else if ( Abc_ObjRegular(pChild)->fPhase != (unsigned)Abc_ObjIsComplement(pChild) )
        {
            nSat++;
            if ( iOut == -1 )
                iOut = i;
        }
        else
            nUndec++;
    }
    printf( "Miter:  I =%6d", nPis );
    printf( "  N =%7d", Abc_NtkNodeNum(pNtk) );
    printf( "  ? =%7d", nUndec );
    printf( "  U =%6d", nUnsat );
    printf( "  S =%6d", nSat );
    Time = clock() - Time;
    printf(" %7.2f sec\n", (float)(Time)/(float)(CLOCKS_PER_SEC));
    if ( iOut >= 0 )
        printf( "The first satisfiable output is number %d (%d).\n", iOut, Abc_ObjName( Abc_NtkPo(pNtk, iOut) ) );
}




typedef struct Gli_Man_t_ Gli_Man_t;

extern Gli_Man_t * Gli_ManAlloc( int nObjs, int nRegs, int nFanioPairs );
extern void        Gli_ManStop( Gli_Man_t * p );
extern int         Gli_ManCreateCi( Gli_Man_t * p, int nFanouts );
extern int         Gli_ManCreateCo( Gli_Man_t * p, int iFanin );
extern int         Gli_ManCreateNode( Gli_Man_t * p, Vec_Int_t * vFanins, int nFanouts, unsigned * puTruth );

extern void        Gli_ManSwitchesAndGlitches( Gli_Man_t * p, int nPatterns, float PiTransProb, int fVerbose );
extern int         Gli_ObjNumSwitches( Gli_Man_t * p, int iNode );
extern int         Gli_ObjNumGlitches( Gli_Man_t * p, int iNode );

/**Function*************************************************************

  Synopsis    [Returns the percentable of increased power due to glitching.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float Abc_NtkMfsTotalGlitching( Abc_Ntk_t * pNtk )
{
    int nSwitches, nGlitches;
    Gli_Man_t * p;
    Vec_Ptr_t * vNodes;
    Vec_Int_t * vFanins, * vTruth;
    Abc_Obj_t * pObj, * pFanin;
    unsigned * puTruth;
    int i, k;
    assert( Abc_NtkIsLogic(pNtk) );
    assert( Abc_NtkGetFaninMax(pNtk) <= 6 );
    if ( Abc_NtkGetFaninMax(pNtk) > 6 )
    {
        printf( "Abc_NtkMfsTotalGlitching() This procedure works only for mapped networks with LUTs size up to 6 inputs.\n" );
        return -1.0;
    }
    Abc_NtkToAig( pNtk );
    vNodes = Abc_NtkDfs( pNtk, 0 );
    vFanins = Vec_IntAlloc( 6 );
    vTruth = Vec_IntAlloc( 1 << 12 );

    // derive network for glitch computation
    p = Gli_ManAlloc( Vec_PtrSize(vNodes) + Abc_NtkCiNum(pNtk) + Abc_NtkCoNum(pNtk), 
        Abc_NtkLatchNum(pNtk), Abc_NtkGetTotalFanins(pNtk) + Abc_NtkCoNum(pNtk) );
    Abc_NtkForEachObj( pNtk, pObj, i )
        pObj->iTemp = -1;
    Abc_NtkForEachCi( pNtk, pObj, i )
        pObj->iTemp = Gli_ManCreateCi( p, Abc_ObjFanoutNum(pObj) );
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pObj, i )
    {
        Vec_IntClear( vFanins );
        Abc_ObjForEachFanin( pObj, pFanin, k )
            Vec_IntPush( vFanins, pFanin->iTemp );
        puTruth = Hop_ManConvertAigToTruth( (Hop_Man_t *)pNtk->pManFunc, (Hop_Obj_t *)pObj->pData, Abc_ObjFaninNum(pObj), vTruth, 0 );
        pObj->iTemp = Gli_ManCreateNode( p, vFanins, Abc_ObjFanoutNum(pObj), puTruth );
    }
    Abc_NtkForEachCo( pNtk, pObj, i )
        Gli_ManCreateCo( p, Abc_ObjFanin0(pObj)->iTemp );

    // compute glitching
    Gli_ManSwitchesAndGlitches( p, 4000, 1.0/8.0, 0 );

    // compute the ratio
    nSwitches = nGlitches = 0;
    Abc_NtkForEachObj( pNtk, pObj, i )
        if ( pObj->iTemp >= 0 )
        {
            nSwitches += Abc_ObjFanoutNum(pObj) * Gli_ObjNumSwitches(p, pObj->iTemp);
            nGlitches += Abc_ObjFanoutNum(pObj) * Gli_ObjNumGlitches(p, pObj->iTemp);
        }

    Gli_ManStop( p );
    Vec_PtrFree( vNodes );
    Vec_IntFree( vTruth );
    Vec_IntFree( vFanins );
    return nSwitches ? 100.0*(nGlitches-nSwitches)/nSwitches : 0.0;
}

/**Function*************************************************************

  Synopsis    [Prints K-map of 6-var function represented by truth table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_Show6VarFunc( word F0, word F1 )
{
    // order of cells in the Karnaugh map
//    int Cells[8] = { 0, 1, 3, 2, 6, 7, 5, 4 };
    int Cells[8] = { 0, 4, 6, 2, 3, 7, 5, 1 };
    // intermediate variables
    int s; // symbol counter
    int h; // horizontal coordinate;
    int v; // vertical coordinate;
    assert( (F0 & F1) == 0 );

    // output minterms above
    for ( s = 0; s < 4; s++ )
        printf( " " );
    printf( " " );
    for ( h = 0; h < 8; h++ )
    {
        for ( s = 0; s < 3; s++ )
            printf( "%d",  ((Cells[h] >> (2-s)) & 1) );
        printf( " " );
    }
    printf( "\n" );

    // output horizontal line above
    for ( s = 0; s < 4; s++ )
        printf( " " );
    printf( "+" );
    for ( h = 0; h < 8; h++ )
    {
        for ( s = 0; s < 3; s++ )
            printf( "-" );
        printf( "+" );
    }
    printf( "\n" );

    // output lines with function values
    for ( v = 0; v < 8; v++ )
    {
        for ( s = 0; s < 3; s++ )
            printf( "%d",  ((Cells[v] >> (2-s)) & 1) );
        printf( " |" );

        for ( h = 0; h < 8; h++ )
        {
            printf( " " );
            if ( ((F0 >> ((Cells[v]*8)+Cells[h])) & 1) )
                printf( "0" );
            else if ( ((F1 >> ((Cells[v]*8)+Cells[h])) & 1) )
                printf( "1" );
            else
                printf( " " );
            printf( " |" );
        }
        printf( "\n" );

        // output horizontal line above
        for ( s = 0; s < 4; s++ )
            printf( " " );
//        printf( "%c", v == 7 ? '+' : '|' );
        printf( "+" );
        for ( h = 0; h < 8; h++ )
        {
            for ( s = 0; s < 3; s++ )
                printf( "-" );
//            printf( "%c", v == 7 ? '+' : '|' );
            printf( "%c", (v == 7 || h == 7) ? '+' : '|' );
        }
        printf( "\n" );
    }
}

/**Function*************************************************************

  Synopsis    [Prints K-map of 6-var function represented by truth table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkShow6VarFunc( char * pF0, char * pF1 )
{
    word F0, F1;
    if ( strlen(pF0) != 16 )
    {
        printf( "Wrong length (%d) of 6-var truth table (%s).\n", strlen(pF0), pF0 );
        return;
    }
    if ( strlen(pF1) != 16 )
    {
        printf( "Wrong length (%d) of 6-var truth table (%s).\n", strlen(pF1), pF1 );
        return;
    }
    Extra_ReadHexadecimal( (unsigned *)&F0, pF0, 6 );
    Extra_ReadHexadecimal( (unsigned *)&F1, pF1, 6 );
    Abc_Show6VarFunc( F0, F1 );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

