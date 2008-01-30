/**CFile****************************************************************

  FileName    [ioWriteEqn.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Procedures to write equation representation of the network.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ioWriteEqn.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "io.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void Io_NtkWriteEqnOne( FILE * pFile, Abc_Ntk_t * pNtk );
static void Io_NtkWriteEqnPis( FILE * pFile, Abc_Ntk_t * pNtk );
static void Io_NtkWriteEqnPos( FILE * pFile, Abc_Ntk_t * pNtk );
static void Io_NtkWriteEqnNode( FILE * pFile, Abc_Obj_t * pNode );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Writes the logic network in the equation format.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_WriteEqn( Abc_Ntk_t * pNtk, char * pFileName )
{
    FILE * pFile;

    assert( Abc_NtkIsSopNetlist(pNtk) );
    if ( Abc_NtkLatchNum(pNtk) > 0 )
        printf( "Warning: only combinational portion is being written.\n" );

    // start the output stream
    pFile = fopen( pFileName, "w" );
    if ( pFile == NULL )
    {
        fprintf( stdout, "Io_WriteEqn(): Cannot open the output file \"%s\".\n", pFileName );
        return;
    }
    fprintf( pFile, "# Equations for \"%s\" written by ABC on %s\n", pNtk->pName, Extra_TimeStamp() );

    // write the equations for the network
    Io_NtkWriteEqnOne( pFile, pNtk );
    fprintf( pFile, "\n" );
    fclose( pFile );
}

/**Function*************************************************************

  Synopsis    [Write one network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_NtkWriteEqnOne( FILE * pFile, Abc_Ntk_t * pNtk )
{
    ProgressBar * pProgress;
    Abc_Obj_t * pNode;
    int i;

    // write the PIs
    fprintf( pFile, "INORDER =" );
    Io_NtkWriteEqnPis( pFile, pNtk );
    fprintf( pFile, ";\n" );

    // write the POs
    fprintf( pFile, "OUTORDER =" );
    Io_NtkWriteEqnPos( pFile, pNtk );
    fprintf( pFile, ";\n" );

    // write each internal node
    pProgress = Extra_ProgressBarStart( stdout, Abc_NtkObjNumMax(pNtk) );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        Io_NtkWriteEqnNode( pFile, pNode );
    }
    Extra_ProgressBarStop( pProgress );
}


/**Function*************************************************************

  Synopsis    [Writes the primary input list.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_NtkWriteEqnPis( FILE * pFile, Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pTerm, * pNet;
    int LineLength;
    int AddedLength;
    int NameCounter;
    int i;

    LineLength  = 9;
    NameCounter = 0;

    Abc_NtkForEachCi( pNtk, pTerm, i )
    {
        pNet = Abc_ObjFanout0(pTerm);
        // get the line length after this name is written
        AddedLength = strlen(Abc_ObjName(pNet)) + 1;
        if ( NameCounter && LineLength + AddedLength + 3 > IO_WRITE_LINE_LENGTH )
        { // write the line extender
            fprintf( pFile, " \n" );
            // reset the line length
            LineLength  = 0;
            NameCounter = 0;
        }
        fprintf( pFile, " %s", Abc_ObjName(pNet) );
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
void Io_NtkWriteEqnPos( FILE * pFile, Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pTerm, * pNet;
    int LineLength;
    int AddedLength;
    int NameCounter;
    int i;

    LineLength  = 10;
    NameCounter = 0;

    Abc_NtkForEachCo( pNtk, pTerm, i )
    {
        pNet = Abc_ObjFanin0(pTerm);
        // get the line length after this name is written
        AddedLength = strlen(Abc_ObjName(pNet)) + 1;
        if ( NameCounter && LineLength + AddedLength + 3 > IO_WRITE_LINE_LENGTH )
        { // write the line extender
            fprintf( pFile, " \n" );
            // reset the line length
            LineLength  = 0;
            NameCounter = 0;
        }
        fprintf( pFile, " %s", Abc_ObjName(pNet) );
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
void Io_NtkWriteEqnNode( FILE * pFile, Abc_Obj_t * pNode )
{
    Abc_Obj_t * pNet;
    int LineLength;
    int AddedLength;
    int NameCounter;
    char * pCube;
    int Value, fFirstLit, i;

    fprintf( pFile, "%s = ", Abc_ObjName(pNode) );

    if ( Abc_SopIsConst0(pNode->pData) )
    {
        fprintf( pFile, "0;\n" );
        return;
    }
    if ( Abc_SopIsConst1(pNode->pData) )
    {
        fprintf( pFile, "1;\n" );
        return;
    }

    NameCounter = 0;
    LineLength  = strlen(Abc_ObjName(pNode)) + 3;
    Abc_SopForEachCube( pNode->pData, Abc_ObjFaninNum(pNode), pCube )
    {
        if ( pCube != pNode->pData )
        {
            fprintf( pFile, " + " );
            LineLength += 3;
        }

        // add the cube
        fFirstLit = 1;
        Abc_CubeForEachVar( pCube, Value, i )
        {
            if ( Value == '-' )
                continue;
            pNet = Abc_ObjFanin( pNode, i );
            // get the line length after this name is written
            AddedLength = !fFirstLit + (Value == '0') + strlen(Abc_ObjName(pNet));
            if ( NameCounter && LineLength + AddedLength + 6 > IO_WRITE_LINE_LENGTH )
            { // write the line extender
                fprintf( pFile, " \n " );
                // reset the line length
                LineLength  = 0;
                NameCounter = 0;
            }
            fprintf( pFile, "%s%s%s", (fFirstLit? "": "*"), ((Value == '0')? "!":""), Abc_ObjName(pNet) );
            LineLength += AddedLength;
            NameCounter++;
            fFirstLit = 0;
        }
    }
    fprintf( pFile, ";\n" );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


