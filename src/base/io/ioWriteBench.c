/**CFile****************************************************************

  FileName    [ioWriteBench.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Procedures to write the network in BENCH format.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ioWriteBench.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "io.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int    Io_WriteBenchOne( FILE * pFile, Abc_Ntk_t * pNtk );
static int    Io_WriteBenchOneNode( FILE * pFile, Abc_Obj_t * pNode );
static char * Io_BenchNodeName( Abc_Obj_t * pObj, int fPhase );
static char * Io_BenchNodeNameInv( Abc_Obj_t * pObj );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Writes the network in BENCH format.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Io_WriteBench( Abc_Ntk_t * pNtk, char * pFileName )
{
    Abc_Ntk_t * pExdc;
    FILE * pFile;
    assert( Abc_NtkIsAig(pNtk) );
    pFile = fopen( pFileName, "w" );
    if ( pFile == NULL )
    {
        fprintf( stdout, "Io_WriteBench(): Cannot open the output file.\n" );
        return 0;
    }
    fprintf( pFile, "# Benchmark \"%s\" written by ABC on %s\n", pNtk->pSpec, Extra_TimeStamp() );
    // write the network
    Io_WriteBenchOne( pFile, pNtk );
    // write EXDC network if it exists
    pExdc = Abc_NtkExdc( pNtk );
    if ( pExdc )
    {
        printf( "Io_WriteBench: EXDC is not written (warning).\n" );
//        fprintf( pFile, "\n" );
//        fprintf( pFile, ".exdc\n" );
//        Io_LogicWriteOne( pFile, pExdc );
    }
    // finalize the file
    fclose( pFile );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Writes the network in BENCH format.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Io_WriteBenchOne( FILE * pFile, Abc_Ntk_t * pNtk )
{
    ProgressBar * pProgress;
    Abc_Obj_t * pNode;
    int i;

    assert( Abc_NtkIsLogicSop(pNtk) || Abc_NtkIsAig(pNtk) );

    // write the PIs/POs/latches
    Abc_NtkForEachPi( pNtk, pNode, i )
        fprintf( pFile, "INPUT(%s)\n", Abc_NtkNamePi(pNtk,i) );
    Abc_NtkForEachPo( pNtk, pNode, i )
        fprintf( pFile, "OUTPUT(%s)\n", Abc_NtkNamePo(pNtk,i) );
    Abc_NtkForEachLatch( pNtk, pNode, i )
        fprintf( pFile, "%-11s = DFF(%s)\n", 
            Abc_NtkNameLatch(pNtk,i), Abc_NtkNameLatchInput(pNtk,i) );

    // set the node names 
    Abc_NtkCleanCopy( pNtk );
    Abc_NtkForEachCi( pNtk, pNode, i )
        pNode->pCopy = (Abc_Obj_t *)Abc_NtkNameCi(pNtk,i);

    // write intervers for COs appearing in negative polarity
    Abc_NtkForEachCi( pNtk, pNode, i )
    {
        if ( Abc_AigNodeIsUsedCompl(pNode) )
            fprintf( pFile, "%-11s = NOT(%s)\n", 
                Io_BenchNodeNameInv(pNode), 
                Abc_NtkNameCi(pNtk,i) );
    }

    // write internal nodes
    pProgress = Extra_ProgressBarStart( stdout, Abc_NtkNodeNum(pNtk) );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        if ( Abc_NodeIsConst(pNode) )
            continue;
        Io_WriteBenchOneNode( pFile, pNode );
    }
    Extra_ProgressBarStop( pProgress );

    // write buffers for CO
    Abc_NtkForEachCo( pNtk, pNode, i )
    {
        fprintf( pFile, "%-11s = BUFF(%s)\n", 
            (i < Abc_NtkPoNum(pNtk))? Abc_NtkNamePo(pNtk,i) : 
                Abc_NtkNameLatchInput( pNtk, i-Abc_NtkPoNum(pNtk) ), 
            Io_BenchNodeName( Abc_ObjFanin0(pNode), !Abc_ObjFaninC0(pNode) ) );
    }
    Abc_NtkCleanCopy( pNtk );
    return 1;
}


/**Function*************************************************************

  Synopsis    [Writes the network in BENCH format.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Io_WriteBenchOneNode( FILE * pFile, Abc_Obj_t * pNode )
{
    assert( Abc_ObjIsNode(pNode) );
    // write the AND gate
    fprintf( pFile, "%-11s",       Io_BenchNodeName( pNode, 1 ) );
    fprintf( pFile, " = AND(%s, ", Io_BenchNodeName( Abc_ObjFanin0(pNode), !Abc_ObjFaninC0(pNode) ) ); 
    fprintf( pFile, "%s)\n",       Io_BenchNodeName( Abc_ObjFanin1(pNode), !Abc_ObjFaninC1(pNode) ) );

    // write the inverter if necessary
    if ( Abc_AigNodeIsUsedCompl(pNode) )
    {
        fprintf( pFile, "%-11s = NOT(",   Io_BenchNodeName( pNode, 0 ) );
        fprintf( pFile, "%s)\n",          Io_BenchNodeName( pNode, 1 ) );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Returns the name of an internal AIG node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Io_BenchNodeName( Abc_Obj_t * pObj, int fPhase )
{
    static char Buffer[500];
    if ( pObj->pCopy ) // PIs and latches
    {
        sprintf( Buffer, "%s%s", (char *)pObj->pCopy, (fPhase? "":"_c") );
        return Buffer;
    }
    assert( Abc_ObjIsNode(pObj) );
    if ( Abc_NodeIsConst(pObj) ) // constant node
    {
        if ( fPhase )
            sprintf( Buffer, "%s", "vdd" );
        else
            sprintf( Buffer, "%s", "gnd" );
        return Buffer;
    }
    // internal nodes
    sprintf( Buffer, "%s%s", Abc_ObjName(pObj), (fPhase? "":"_c") );
    return Buffer;
}

/**Function*************************************************************

  Synopsis    [Returns the name of an internal AIG node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Io_BenchNodeNameInv( Abc_Obj_t * pObj )
{
    static char Buffer[500];
    sprintf( Buffer, "%s%s", Abc_ObjName(pObj), "_c" );
    return Buffer;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


