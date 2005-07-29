/**CFile****************************************************************

  FileName    [ioWriteGate.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Procedures to write the mapped network.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ioWriteGate.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "io.h"
#include "main.h"
#include "mio.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void   Io_WriteGateOne( FILE * pFile, Abc_Ntk_t * pNtk );
static void   Io_WriteGatePis( FILE * pFile, Abc_Ntk_t * pNtk );
static void   Io_WriteGatePos( FILE * pFile, Abc_Ntk_t * pNtk );
static void   Io_WriteGateNode( FILE * pFile, Abc_Obj_t * pNode, Mio_Gate_t * pGate );
static char * Io_ReadNodeName( Abc_Obj_t * pNode );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Writes mapped network into a BLIF file compatible with SIS.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Io_WriteGate( Abc_Ntk_t * pNtk, char * pFileName )
{
    Abc_Ntk_t * pExdc;
    FILE * pFile;

    assert( Abc_NtkIsLogicMap(pNtk) );
    pFile = fopen( pFileName, "w" );
    if ( pFile == NULL )
    {
        fprintf( stdout, "Io_WriteGate(): Cannot open the output file.\n" );
        return 0;
    }
    // write the model name
    fprintf( pFile, ".model %s\n", Abc_NtkName(pNtk) );
    // write the network
    Io_WriteGateOne( pFile, pNtk );
    // write EXDC network if it exists
    pExdc = Abc_NtkExdc( pNtk );
    if ( pExdc )
        printf( "Io_WriteGate: EXDC is not written (warning).\n" );
    // finalize the file
    fprintf( pFile, ".end\n" );
    fclose( pFile );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Write one network.]

  Description [Writes a network composed of PIs, POs, internal nodes,
  and latches. The following rules are used to print the names of 
  internal nodes: ]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_WriteGateOne( FILE * pFile, Abc_Ntk_t * pNtk )
{
    ProgressBar * pProgress;
    Abc_Obj_t * pNode, * pLatch;
    int i;

    assert( Abc_NtkIsLogicMap(pNtk) );
    assert( Abc_NtkLogicHasSimplePos(pNtk) );

    // write the PIs
    fprintf( pFile, ".inputs" );
    Io_WriteGatePis( pFile, pNtk );
    fprintf( pFile, "\n" );

    // write the POs
    fprintf( pFile, ".outputs" );
    Io_WriteGatePos( pFile, pNtk );
    fprintf( pFile, "\n" );

    // write the timing info
    Io_WriteTimingInfo( pFile, pNtk );

    // write the latches
    if ( Abc_NtkLatchNum(pNtk) )
    {
        fprintf( pFile, "\n" );
        Abc_NtkForEachLatch( pNtk, pLatch, i )
            fprintf( pFile, ".latch %s %s  %d\n", 
                Abc_NtkNameLatchInput(pNtk,i), Abc_NtkNameLatch(pNtk,i), (int)pLatch->pData );
        fprintf( pFile, "\n" );
    }
    // set the node names
    Abc_NtkLogicTransferNames( pNtk );
    // write internal nodes
    pProgress = Extra_ProgressBarStart( stdout, Abc_NtkNodeNum(pNtk) );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        Io_WriteGateNode( pFile, pNode, pNode->pData );
    }
    Extra_ProgressBarStop( pProgress );
    Abc_NtkCleanCopy( pNtk );
}


/**Function*************************************************************

  Synopsis    [Writes the primary input list.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_WriteGatePis( FILE * pFile, Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    char * pName;
    int LineLength;
    int AddedLength;
    int NameCounter;
    int i;

    LineLength  = 7;
    NameCounter = 0;
    Abc_NtkForEachPi( pNtk, pNode, i )
    {
        pName = pNtk->vNamesPi->pArray[i];
        // get the line length after this name is written
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
}

/**Function*************************************************************

  Synopsis    [Writes the primary input list.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_WriteGatePos( FILE * pFile, Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    int LineLength;
    int AddedLength;
    int NameCounter;
    char * pName;
    int i;

    LineLength  = 8;
    NameCounter = 0;
    Abc_NtkForEachPo( pNtk, pNode, i )
    {
        pName = pNtk->vNamesPo->pArray[i];
        // get the line length after this name is written
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
}

/**Function*************************************************************

  Synopsis    [Write the node into a file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_WriteGateNode( FILE * pFile, Abc_Obj_t * pNode, Mio_Gate_t * pGate )
{
    Mio_Pin_t * pGatePin;
    int i;
    // do not write the buffer whose input and output have the same name
    if ( Abc_ObjFaninNum(pNode) == 1 && Abc_ObjFanin0(pNode)->pCopy && pNode->pCopy )
        if ( strcmp( (char*)Abc_ObjFanin0(pNode)->pCopy, (char*)pNode->pCopy ) == 0 )
            return;
    // write the node
    fprintf( pFile, ".gate %s ", Mio_GateReadName(pGate) );
    for ( pGatePin = Mio_GateReadPins(pGate), i = 0; pGatePin; pGatePin = Mio_PinReadNext(pGatePin), i++ )
        fprintf( pFile, "%s=%s ", Mio_PinReadName(pGatePin), Io_ReadNodeName( Abc_ObjFanin(pNode,i) ) );
    assert ( i == Abc_ObjFaninNum(pNode) );
    fprintf( pFile, "%s=%s\n", Mio_GateReadOutName(pGate), Io_ReadNodeName(pNode) );
}

/**Function*************************************************************

  Synopsis    [Returns the name of the node to write.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Io_ReadNodeName( Abc_Obj_t * pNode )
{
    if ( pNode->pCopy )
        return (char *)pNode->pCopy;
    return Abc_ObjName(pNode);
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


