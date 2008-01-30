/**CFile****************************************************************

  FileName    [ioWriteBlif.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Procedures to write BLIF files.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ioWriteBlif.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "io.h"
#include "main.h"
#include "mio.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void Io_NtkWriteOne( FILE * pFile, Abc_Ntk_t * pNtk, int fWriteLatches );
static void Io_NtkWritePis( FILE * pFile, Abc_Ntk_t * pNtk, int fWriteLatches );
static void Io_NtkWritePos( FILE * pFile, Abc_Ntk_t * pNtk, int fWriteLatches );
static void Io_NtkWriteNodeGate( FILE * pFile, Abc_Obj_t * pNode );
static void Io_NtkWriteNodeFanins( FILE * pFile, Abc_Obj_t * pNode );
static void Io_NtkWriteNode( FILE * pFile, Abc_Obj_t * pNode );
static void Io_NtkWriteLatch( FILE * pFile, Abc_Obj_t * pLatch );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Write the network into a BLIF file with the given name.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_WriteBlifLogic( Abc_Ntk_t * pNtk, char * FileName, int fWriteLatches )
{
    Abc_Ntk_t * pNtkTemp;
    // derive the netlist
    pNtkTemp = Abc_NtkLogicToNetlist(pNtk);
    if ( pNtkTemp == NULL )
    {
        fprintf( stdout, "Writing BLIF has failed.\n" );
        return;
    }
    Io_WriteBlif( pNtkTemp, FileName, fWriteLatches );
    Abc_NtkDelete( pNtkTemp );
}

/**Function*************************************************************

  Synopsis    [Write the network into a BLIF file with the given name.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_WriteBlif( Abc_Ntk_t * pNtk, char * FileName, int fWriteLatches )
{
    Abc_Ntk_t * pExdc;
    FILE * pFile;
    assert( Abc_NtkIsNetlist(pNtk) );
    pFile = fopen( FileName, "w" );
    if ( pFile == NULL )
    {
        fprintf( stdout, "Io_WriteBlif(): Cannot open the output file.\n" );
        return;
    }
    // write the model name
    fprintf( pFile, "# Benchmark \"%s\" written by ABC on %s\n", pNtk->pName, Extra_TimeStamp() );
    fprintf( pFile, ".model %s\n", Abc_NtkName(pNtk) );
    // write the network
    Io_NtkWriteOne( pFile, pNtk, fWriteLatches );
    // write EXDC network if it exists
    pExdc = Abc_NtkExdc( pNtk );
    if ( pExdc )
    {
        fprintf( pFile, "\n" );
        fprintf( pFile, ".exdc\n" );
        Io_NtkWriteOne( pFile, pExdc, fWriteLatches );
    }
    // finalize the file
    fprintf( pFile, ".end\n" );
    fclose( pFile );
}

/**Function*************************************************************

  Synopsis    [Write one network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_NtkWriteOne( FILE * pFile, Abc_Ntk_t * pNtk, int fWriteLatches )
{
    ProgressBar * pProgress;
    Abc_Obj_t * pNode, * pLatch;
    int i;

    // write the PIs
    fprintf( pFile, ".inputs" );
    Io_NtkWritePis( pFile, pNtk, fWriteLatches );
    fprintf( pFile, "\n" );

    // write the POs
    fprintf( pFile, ".outputs" );
    Io_NtkWritePos( pFile, pNtk, fWriteLatches );
    fprintf( pFile, "\n" );

    // write the timing info
    Io_WriteTimingInfo( pFile, pNtk );

    // write the latches
    if ( fWriteLatches && !Abc_NtkIsComb(pNtk) )
    {
        fprintf( pFile, "\n" );
        Abc_NtkForEachLatch( pNtk, pLatch, i )
            Io_NtkWriteLatch( pFile, pLatch );
        fprintf( pFile, "\n" );
    }

    // write each internal node
    pProgress = Extra_ProgressBarStart( stdout, Abc_NtkObjNumMax(pNtk) );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        Io_NtkWriteNode( pFile, pNode );
    }
    Extra_ProgressBarStop( pProgress );
}


/**Function*************************************************************

  Synopsis    [Writes the primary input list.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_NtkWritePis( FILE * pFile, Abc_Ntk_t * pNtk, int fWriteLatches )
{
    Abc_Obj_t * pTerm, * pNet;
    int LineLength;
    int AddedLength;
    int NameCounter;
    int i;

    LineLength  = 7;
    NameCounter = 0;

    if ( fWriteLatches )
    {
        Abc_NtkForEachPi( pNtk, pTerm, i )
        {
            pNet = Abc_ObjFanout0(pTerm);
            // get the line length after this name is written
            AddedLength = strlen(Abc_ObjName(pNet)) + 1;
            if ( NameCounter && LineLength + AddedLength + 3 > IO_WRITE_LINE_LENGTH )
            { // write the line extender
                fprintf( pFile, " \\\n" );
                // reset the line length
                LineLength  = 0;
                NameCounter = 0;
            }
            fprintf( pFile, " %s", Abc_ObjName(pNet) );
            LineLength += AddedLength;
            NameCounter++;
        }
    }
    else
    {
        Abc_NtkForEachCi( pNtk, pTerm, i )
        {
            pNet = Abc_ObjFanout0(pTerm);
            // get the line length after this name is written
            AddedLength = strlen(Abc_ObjName(pNet)) + 1;
            if ( NameCounter && LineLength + AddedLength + 3 > IO_WRITE_LINE_LENGTH )
            { // write the line extender
                fprintf( pFile, " \\\n" );
                // reset the line length
                LineLength  = 0;
                NameCounter = 0;
            }
            fprintf( pFile, " %s", Abc_ObjName(pNet) );
            LineLength += AddedLength;
            NameCounter++;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Writes the primary input list.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_NtkWritePos( FILE * pFile, Abc_Ntk_t * pNtk, int fWriteLatches )
{
    Abc_Obj_t * pTerm, * pNet;
    int LineLength;
    int AddedLength;
    int NameCounter;
    int i;

    LineLength  = 8;
    NameCounter = 0;

    if ( fWriteLatches )
    {
        Abc_NtkForEachPo( pNtk, pTerm, i )
        {
            pNet = Abc_ObjFanin0(pTerm);
            // get the line length after this name is written
            AddedLength = strlen(Abc_ObjName(pNet)) + 1;
            if ( NameCounter && LineLength + AddedLength + 3 > IO_WRITE_LINE_LENGTH )
            { // write the line extender
                fprintf( pFile, " \\\n" );
                // reset the line length
                LineLength  = 0;
                NameCounter = 0;
            }
            fprintf( pFile, " %s", Abc_ObjName(pNet) );
            LineLength += AddedLength;
            NameCounter++;
        }
    }
    else
    {
        Abc_NtkForEachCo( pNtk, pTerm, i )
        {
            pNet = Abc_ObjFanin0(pTerm);
            // get the line length after this name is written
            AddedLength = strlen(Abc_ObjName(pNet)) + 1;
            if ( NameCounter && LineLength + AddedLength + 3 > IO_WRITE_LINE_LENGTH )
            { // write the line extender
                fprintf( pFile, " \\\n" );
                // reset the line length
                LineLength  = 0;
                NameCounter = 0;
            }
            fprintf( pFile, " %s", Abc_ObjName(pNet) );
            LineLength += AddedLength;
            NameCounter++;
        }
    }
}


/**Function*************************************************************

  Synopsis    [Write the latch into a file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_NtkWriteLatch( FILE * pFile, Abc_Obj_t * pLatch )
{
    Abc_Obj_t * pNetLi, * pNetLo;
    int Reset;
    pNetLi = Abc_ObjFanin0( pLatch );
    pNetLo = Abc_ObjFanout0( pLatch );
    Reset  = (int)Abc_ObjData( pLatch );
    // write the latch line
    fprintf( pFile, ".latch" );
    fprintf( pFile, " %10s",    Abc_ObjName(pNetLi) );
    fprintf( pFile, " %10s",    Abc_ObjName(pNetLo) );
    fprintf( pFile, "  %d\n",   Reset );
}


/**Function*************************************************************

  Synopsis    [Write the node into a file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_NtkWriteNode( FILE * pFile, Abc_Obj_t * pNode )
{
    if ( Abc_NtkHasMapping(pNode->pNtk) )
    {
        // write the .gate line
        fprintf( pFile, ".gate" );
        Io_NtkWriteNodeGate( pFile, pNode );
        fprintf( pFile, "\n" );
    }
    else
    {
        // write the .names line
        fprintf( pFile, ".names" );
        Io_NtkWriteNodeFanins( pFile, pNode );
        fprintf( pFile, "\n" );
        // write the cubes
        fprintf( pFile, "%s", Abc_ObjData(pNode) );
    }
}

/**Function*************************************************************

  Synopsis    [Writes the primary input list.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_NtkWriteNodeGate( FILE * pFile, Abc_Obj_t * pNode )
{
    Mio_Gate_t * pGate = pNode->pData;
    Mio_Pin_t * pGatePin;
    int i;
    // write the node
    fprintf( pFile, " %s ", Mio_GateReadName(pGate) );
    for ( pGatePin = Mio_GateReadPins(pGate), i = 0; pGatePin; pGatePin = Mio_PinReadNext(pGatePin), i++ )
        fprintf( pFile, "%s=%s ", Mio_PinReadName(pGatePin), Abc_ObjName( Abc_ObjFanin(pNode,i) ) );
    assert ( i == Abc_ObjFaninNum(pNode) );
    fprintf( pFile, "%s=%s", Mio_GateReadOutName(pGate), Abc_ObjName(pNode) );
}

/**Function*************************************************************

  Synopsis    [Writes the primary input list.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_NtkWriteNodeFanins( FILE * pFile, Abc_Obj_t * pNode )
{
    Abc_Obj_t * pNet;
    int LineLength;
    int AddedLength;
    int NameCounter;
    char * pName;
    int i;

    LineLength  = 6;
    NameCounter = 0;
    Abc_ObjForEachFanin( pNode, pNet, i )
    {
        // get the fanin name
        pName = Abc_ObjName(pNet);
        // get the line length after the fanin name is written
        AddedLength = strlen(pName) + 1;
        if ( NameCounter && LineLength + AddedLength + 3 > IO_WRITE_LINE_LENGTH )
        { // write the line extender
            fprintf( pFile, " \\\n" );
            // reset the line length
            LineLength  = 0;
            NameCounter = 0;
        }
        fprintf( pFile, " %s", pName );
        LineLength += AddedLength;
        NameCounter++;
    }

    // get the output name
    pName = Abc_ObjName(Abc_ObjFanout0(pNode));
    // get the line length after the output name is written
    AddedLength = strlen(pName) + 1;
    if ( NameCounter && LineLength + AddedLength > 75 )
    { // write the line extender
        fprintf( pFile, " \\\n" );
        // reset the line length
        LineLength  = 0;
        NameCounter = 0;
    }
    fprintf( pFile, " %s", pName );
}

/**Function*************************************************************

  Synopsis    [Writes the timing info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_WriteTimingInfo( FILE * pFile, Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    Abc_Time_t * pTime, * pTimeDef;
    int i;

    if ( pNtk->pManTime == NULL )
        return;

    pTimeDef = Abc_NtkReadDefaultArrival( pNtk );
    fprintf( pFile, ".default_input_arrival %g %g\n", pTimeDef->Rise, pTimeDef->Fall );
    Abc_NtkForEachPi( pNtk, pNode, i )
    {
        pTime = Abc_NodeReadArrival(pNode);
        if ( pTime->Rise == pTimeDef->Rise && pTime->Fall == pTimeDef->Fall )
            continue;
        fprintf( pFile, ".input_arrival %s %g %g\n", Abc_ObjName(pNode), pTime->Rise, pTime->Fall );
    }
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


