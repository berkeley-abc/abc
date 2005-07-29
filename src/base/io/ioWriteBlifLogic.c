/**CFile****************************************************************

  FileName    [ioWriteBlifLogic.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Procedures to write BLIF files for a logic network.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ioWriteBlifLogic.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "io.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void Io_LogicWriteOne( FILE * pFile, Abc_Ntk_t * pNtk, int fWriteLatches );
static void Io_LogicWritePis( FILE * pFile, Abc_Ntk_t * pNtk, int fWriteLatches );
static void Io_LogicWritePos( FILE * pFile, Abc_Ntk_t * pNtk, int fWriteLatches );
static void Io_LogicWriteNodeFanins( FILE * pFile, Abc_Obj_t * pNode, int fMark );
static void Io_LogicWriteNode( FILE * pFile, Abc_Obj_t * pNode );

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
    Abc_Ntk_t * pExdc;
    FILE * pFile;
    assert( !Abc_NtkIsNetlist(pNtk) );
    pFile = fopen( FileName, "w" );
    if ( pFile == NULL )
    {
        fprintf( stdout, "Io_WriteBlifLogic(): Cannot open the output file.\n" );
        return;
    }
    // write the model name
    fprintf( pFile, ".model %s\n", Abc_NtkName(pNtk) );
    // write the network
    Io_LogicWriteOne( pFile, pNtk, fWriteLatches );
    // write EXDC network if it exists
    pExdc = Abc_NtkExdc( pNtk );
    if ( pExdc )
    {
        fprintf( pFile, "\n" );
        fprintf( pFile, ".exdc\n" );
        Io_LogicWriteOne( pFile, pExdc, 0 );
    }
    // finalize the file
    fprintf( pFile, ".end\n" );
    fclose( pFile );
}

/**Function*************************************************************

  Synopsis    [Write one network.]

  Description [Writes a network composed of PIs, POs, internal nodes,
  and latches. The following rules are used to print the names of 
  internal nodes: ]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_LogicWriteOne( FILE * pFile, Abc_Ntk_t * pNtk, int fWriteLatches )
{
    ProgressBar * pProgress;
    Abc_Obj_t * pNode, * pLatch, * pDriver;
    Vec_Ptr_t * vNodes;
    int i;

    assert( Abc_NtkIsLogicSop(pNtk) || Abc_NtkIsAig(pNtk) );

    // print a warning about choice nodes
    if ( i = Abc_NtkCountChoiceNodes( pNtk ) )
        printf( "Warning: The AIG is written into the file, including %d choice nodes.\n", i );

    // write the PIs
    fprintf( pFile, ".inputs" );
    Io_LogicWritePis( pFile, pNtk, fWriteLatches );
    fprintf( pFile, "\n" );

    // write the POs
    fprintf( pFile, ".outputs" );
    Io_LogicWritePos( pFile, pNtk, fWriteLatches );
    fprintf( pFile, "\n" );

    if ( fWriteLatches )
    {
        // write the timing info
        Io_WriteTimingInfo( pFile, pNtk );
        // write the latches
        if ( Abc_NtkLatchNum(pNtk) )
        {
            fprintf( pFile, "\n" );
            Abc_NtkForEachLatch( pNtk, pLatch, i )
                fprintf( pFile, ".latch %10s %10s  %d\n", 
                    Abc_NtkNameLatchInput(pNtk,i), Abc_NtkNameLatch(pNtk,i), (int)pLatch->pData );
            fprintf( pFile, "\n" );
        }
    }

    // set the node names 
    Abc_NtkLogicTransferNames( pNtk );

    // collect internal nodes
    if ( Abc_NtkIsAig(pNtk) )
        vNodes = Abc_AigDfs( pNtk );
    else
        vNodes = Abc_NtkDfs( pNtk );
    // write internal nodes
    pProgress = Extra_ProgressBarStart( stdout, vNodes->nSize );
    for ( i = 0; i < vNodes->nSize; i++ )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        Io_LogicWriteNode( pFile, Vec_PtrEntry(vNodes, i) );
    }
    Extra_ProgressBarStop( pProgress );
    Vec_PtrFree( vNodes );

    // write inverters/buffers for each CO
    Abc_NtkForEachLatch( pNtk, pLatch, i )
    {
        pDriver = Abc_ObjFanin0(pLatch);
        // consider the case when the latch is driving itself
        if ( pDriver == pLatch )
        {
            fprintf( pFile, ".names %s %s\n%d 1\n", 
                Abc_NtkNameLatch(pNtk,i), Abc_NtkNameLatchInput(pNtk,i), !Abc_ObjFaninC0(pLatch) );
            continue;
        }
        // skip if they have the same name
        if ( pDriver->pCopy && strcmp( (char *)pDriver->pCopy, Abc_NtkNameLatchInput(pNtk,i) ) == 0 )
        {
            /*
            Abc_Obj_t * pFanout;
            int k;
            printf( "latch name = %s.\n", (char *)pLatch->pCopy );
            printf( "driver name = %s.\n", (char *)pDriver->pCopy );
            Abc_ObjForEachFanout( pDriver, pFanout, k )
                printf( "driver's fanout name = %s. Fanins = %d. Compl0 = %d. \n", 
                    Abc_ObjName(pFanout), Abc_ObjFaninNum(pFanout), Abc_ObjFaninC0(pFanout) );
            */
            assert( !Abc_ObjFaninC0(pLatch) );
            continue;
        }
        // write inverter/buffer depending on whether the edge is complemented
        fprintf( pFile, ".names %s %s\n%d 1\n", 
            Abc_ObjName(pDriver), Abc_NtkNameLatchInput(pNtk,i), !Abc_ObjFaninC0(pLatch) );
    }
    Abc_NtkForEachPo( pNtk, pNode, i )
    {
        pDriver = Abc_ObjFanin0(pNode);
        // skip if they have the same name
        if ( pDriver->pCopy && strcmp( (char *)pDriver->pCopy, Abc_NtkNamePo(pNtk,i) ) == 0 )
        {
            assert( !Abc_ObjFaninC0(pNode) );
            continue;
        }
        // write inverter/buffer depending on whether the PO is complemented
        fprintf( pFile, ".names %s %s\n%d 1\n", 
            Abc_ObjName(pDriver), Abc_NtkNamePo(pNtk,i), !Abc_ObjFaninC0(pNode) );
    }
    Abc_NtkCleanCopy( pNtk );
}


/**Function*************************************************************

  Synopsis    [Writes the primary input list.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_LogicWritePis( FILE * pFile, Abc_Ntk_t * pNtk, int fWriteLatches )
{
    char * pName;
    int LineLength;
    int AddedLength;
    int NameCounter;
    int nLimit;
    int i;

    LineLength  = 7;
    NameCounter = 0;
    nLimit = fWriteLatches? Abc_NtkPiNum(pNtk) : Abc_NtkCiNum(pNtk);
    for ( i = 0; i < nLimit; i++ )
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
void Io_LogicWritePos( FILE * pFile, Abc_Ntk_t * pNtk, int fWriteLatches )
{
    char * pName;
    int LineLength;
    int AddedLength;
    int NameCounter;
    int nLimit;
    int i;

    LineLength  = 8;
    NameCounter = 0;
    nLimit = fWriteLatches? Abc_NtkPoNum(pNtk) : Abc_NtkCoNum(pNtk);
    for ( i = 0; i < nLimit; i++ )
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
void Io_LogicWriteNode( FILE * pFile, Abc_Obj_t * pNode )
{
    Abc_Obj_t * pTemp;
    int i, k, nFanins, fMark;

    assert( !Abc_ObjIsComplement( pNode ) );
    assert( Abc_ObjIsNode(pNode) );

    // set the mark that is true if the node is a choice node
    fMark = Abc_NtkIsAig(pNode->pNtk) && Abc_NodeIsChoice(pNode);

    // write the .names line
    fprintf( pFile, ".names" );
    Io_LogicWriteNodeFanins( pFile, pNode, fMark );
    fprintf( pFile, "\n" );
    // write the cubes
    if ( Abc_NtkIsLogicSop(pNode->pNtk) )
        fprintf( pFile, "%s", Abc_ObjData(pNode) );
    else if ( Abc_NtkIsAig(pNode->pNtk) )
    {
        if ( pNode == Abc_AigConst1(pNode->pNtk->pManFunc) )
        {
            fprintf( pFile, " 1\n" );
            return;
        }

        assert( Abc_ObjFaninNum(pNode) == 2 );
        // write the AND gate
        for ( i = 0; i < 2; i++ )
            fprintf( pFile, "%d", !Abc_ObjFaninC(pNode,i) );
        fprintf( pFile, " 1\n" );
        // write the choice node if present
        if ( fMark ) 
        {
            // count the number of fanins of the choice node and write the names line
            nFanins = 1;
            fprintf( pFile, ".names %sc", Abc_ObjName(pNode) );
            for ( pTemp = pNode->pData; pTemp; pTemp = pTemp->pData, nFanins++ )
                fprintf( pFile, " %s", Abc_ObjName(pTemp) );
            fprintf( pFile, " %s\n", Abc_ObjName(pNode) );
            // write the cubes for each of the fanins
            for ( i = 0, pTemp = pNode; pTemp; pTemp = pTemp->pData, i++ )
            {
                for ( k = 0; k < nFanins; k++ )
                    if ( k == i )
                        fprintf( pFile, "%d", (int)(pNode->fPhase == pTemp->fPhase) );
                    else 
                        fprintf( pFile, "-" );
                fprintf( pFile, " 1\n" );
            }
        }
    }
    else
    {
        assert( 0 );
    }
}

/**Function*************************************************************

  Synopsis    [Writes the primary input list.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_LogicWriteNodeFanins( FILE * pFile, Abc_Obj_t * pNode, int fMark )
{
    Abc_Obj_t * pFanin;
    int LineLength;
    int AddedLength;
    int NameCounter;
    char * pName;
    int i;

    LineLength  = 6;
    NameCounter = 0;
    Abc_ObjForEachFanin( pNode, pFanin, i )
    {
        // get the fanin name
        pName = Abc_ObjName(pFanin);
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
    pName = Abc_ObjName(pNode);
    // get the line length after the output name is written
    AddedLength = strlen(pName) + 1;
    if ( NameCounter && LineLength + AddedLength > 75 )
    { // write the line extender
        fprintf( pFile, " \\\n" );
        // reset the line length
        LineLength  = 0;
        NameCounter = 0;
    }
    fprintf( pFile, " %s%s", pName, fMark? "c" : "" );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


