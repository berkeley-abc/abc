/**CFile****************************************************************

  FileName    [ioWriteVerilog.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Procedures to output a special subset of Verilog.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ioWriteVerilog.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "io.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void Io_WriteVerilogAuxInt( FILE * pFile, Abc_Ntk_t * pNtk );
static void Io_WriteVerilogAuxPis( FILE * pFile, Abc_Ntk_t * pNtk, int Start );
static void Io_WriteVerilogAuxPos( FILE * pFile, Abc_Ntk_t * pNtk, int Start );
static void Io_WriteVerilogAuxWires( FILE * pFile, Abc_Ntk_t * pNtk, int Start );
static void Io_WriteVerilogAuxNodes( FILE * pFile, Abc_Ntk_t * pNtk );
static void Io_WriteVerilogAuxArgs( FILE * pFile, Abc_Obj_t * pObj, int nInMax, int fPadZeros );
static int Io_WriteVerilogAuxCheckNtk( Abc_Ntk_t * pNtk );
static char * Io_WriteVerilogAuxGetName( Abc_Obj_t * pObj );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Write verilog.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_WriteVerilogAux( Abc_Ntk_t * pNtk, char * pFileName )
{
    FILE * pFile;

    if ( !Abc_NtkIsSopNetlist(pNtk) || !Io_WriteVerilogAuxCheckNtk(pNtk) )
    {
        printf( "Io_WriteVerilogAux(): Can write Verilog for a very special subset of logic networks.\n" );
        printf( "The current network is not in the subset; writing Verilog is not performed.\n" );
        return;
    }

    if ( Abc_NtkLatchNum(pNtk) > 0 )
        printf( "Io_WriteVerilogAux(): Warning: only combinational portion is being written.\n" );

    // start the output stream
    pFile = fopen( pFileName, "w" );
    if ( pFile == NULL )
    {
        fprintf( stdout, "Io_WriteVerilogAux(): Cannot open the output file \"%s\".\n", pFileName );
        return;
    }

    // write the equations for the network
    Io_WriteVerilogAuxInt( pFile, pNtk );
    fprintf( pFile, "\n" );
    fclose( pFile );
}

/**Function*************************************************************

  Synopsis    [Writes verilog.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_WriteVerilogAuxInt( FILE * pFile, Abc_Ntk_t * pNtk )
{
    // write inputs and outputs
    fprintf( pFile, "// Benchmark \"%s\" written by ABC on %s\n", pNtk->pName, Extra_TimeStamp() );
    fprintf( pFile, "module %s (\n   ", Abc_NtkName(pNtk) );
    Io_WriteVerilogAuxPis( pFile, pNtk, 3 );
    fprintf( pFile, ",\n   " );
    Io_WriteVerilogAuxPos( pFile, pNtk, 3 );
    fprintf( pFile, "  );\n" );
    // write inputs, outputs and wires
    fprintf( pFile, "  input" );
    Io_WriteVerilogAuxPis( pFile, pNtk, 5 );
    fprintf( pFile, ";\n" );
    fprintf( pFile, "  output" );
    Io_WriteVerilogAuxPos( pFile, pNtk, 5 );
    fprintf( pFile, ";\n" );
    fprintf( pFile, "  wire" );
    Io_WriteVerilogAuxWires( pFile, pNtk, 4 );
    fprintf( pFile, ";\n" );
    // write the nodes
    Io_WriteVerilogAuxNodes( pFile, pNtk );
    // finalize the file
    fprintf( pFile, "endmodule\n\n" );
    fclose( pFile );
} 

/**Function*************************************************************

  Synopsis    [Writes the primary inputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_WriteVerilogAuxPis( FILE * pFile, Abc_Ntk_t * pNtk, int Start )
{
    Abc_Obj_t * pTerm, * pNet;
    int LineLength;
    int AddedLength;
    int NameCounter;
    int i;

    LineLength  = Start;
    NameCounter = 0;
    Abc_NtkForEachCi( pNtk, pTerm, i )
    {
        pNet = Abc_ObjFanout0(pTerm);
        // get the line length after this name is written
        AddedLength = strlen(Abc_ObjName(pNet)) + 2;
        if ( NameCounter && LineLength + AddedLength + 3 > IO_WRITE_LINE_LENGTH )
        { // write the line extender
            fprintf( pFile, "\n   " );
            // reset the line length
            LineLength  = 3;
            NameCounter = 0;
        }
        fprintf( pFile, " %s%s", Abc_ObjName(pNet), (i==Abc_NtkCiNum(pNtk)-1)? "" : "," );
        LineLength += AddedLength;
        NameCounter++;
    }
}

/**Function*************************************************************

  Synopsis    [Writes the primary outputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_WriteVerilogAuxPos( FILE * pFile, Abc_Ntk_t * pNtk, int Start )
{
    Abc_Obj_t * pTerm, * pNet;
    int LineLength;
    int AddedLength;
    int NameCounter;
    int i;

    LineLength  = Start;
    NameCounter = 0;
    Abc_NtkForEachCo( pNtk, pTerm, i )
    {
        pNet = Abc_ObjFanin0(pTerm);
        // get the line length after this name is written
        AddedLength = strlen(Abc_ObjName(pNet)) + 2;
        if ( NameCounter && LineLength + AddedLength + 3 > IO_WRITE_LINE_LENGTH )
        { // write the line extender
            fprintf( pFile, "\n   " );
            // reset the line length
            LineLength  = 3;
            NameCounter = 0;
        }
        fprintf( pFile, " %s%s", Abc_ObjName(pNet), (i==Abc_NtkCoNum(pNtk)-1)? "" : "," );
        LineLength += AddedLength;
        NameCounter++;
    }
}

/**Function*************************************************************

  Synopsis    [Writes the wires.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_WriteVerilogAuxWires( FILE * pFile, Abc_Ntk_t * pNtk, int Start )
{
    Abc_Obj_t * pTerm, * pNet;
    int LineLength;
    int AddedLength;
    int NameCounter;
    int i, Counter, nNodes;

    // count the number of wires
    nNodes = 0;
    Abc_NtkForEachNode( pNtk, pTerm, i )
    {
        if ( i == 0 ) 
            continue;
        pNet = Abc_ObjFanout0(pTerm);
        if ( Abc_ObjIsCo(Abc_ObjFanout0(pNet)) )
            continue;
        nNodes++;
    }

    // write the wires
    Counter = 0;
    LineLength  = Start;
    NameCounter = 0;
    Abc_NtkForEachNode( pNtk, pTerm, i )
    {
        if ( i == 0 ) 
            continue;
        pNet = Abc_ObjFanout0(pTerm);
        if ( Abc_ObjIsCo(Abc_ObjFanout0(pNet)) )
            continue;
        Counter++;
        // get the line length after this name is written
        AddedLength = strlen(Abc_ObjName(pNet)) + 2;
        if ( NameCounter && LineLength + AddedLength + 3 > IO_WRITE_LINE_LENGTH )
        { // write the line extender
            fprintf( pFile, "\n   " );
            // reset the line length
            LineLength  = 3;
            NameCounter = 0;
        }
        fprintf( pFile, " %s%s", Io_WriteVerilogAuxGetName(pNet), (Counter==nNodes)? "" : "," );
        LineLength += AddedLength;
        NameCounter++;
    }
}

/**Function*************************************************************

  Synopsis    [Writes the wires.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_WriteVerilogAuxNodes( FILE * pFile, Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    int i, nCubes, nFanins, Counter, nDigits, fPadZeros;
    char * pName;
    extern int Abc_SopIsExorType( char * pSop );

    nDigits = Extra_Base10Log( Abc_NtkNodeNum(pNtk) );
    Counter = 1;
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        nFanins = Abc_ObjFaninNum(pObj);
        nCubes = Abc_SopGetCubeNum(pObj->pData);
        if ( Abc_SopIsAndType(pObj->pData) )
            pName = "ts_and", fPadZeros = 1;
        else if ( Abc_SopIsExorType(pObj->pData) )
            pName = "ts_xor", fPadZeros = 1;
        else // if ( Abc_SopIsOrType(pObj->pData) )
            pName = "ts_or",  fPadZeros = 0;

        assert( nCubes < 2 );
        if ( nCubes == 0 )
        {
            fprintf( pFile, "  ts_gnd g%0*d ", nDigits, Counter++ );
            Io_WriteVerilogAuxArgs( pFile, pObj, 0, fPadZeros );
        }
        else if ( nCubes == 1 && nFanins == 0 )
        {
            fprintf( pFile, "  ts_vdd g%0*d ", nDigits, Counter++ );
            Io_WriteVerilogAuxArgs( pFile, pObj, 0, fPadZeros );
        }
        else if ( nFanins == 1 && Abc_SopIsInv(pObj->pData) )
        {
            fprintf( pFile, "  ts_inv g%0*d ", nDigits, Counter++ );
            Io_WriteVerilogAuxArgs( pFile, pObj, 1, fPadZeros );
        }
        else if ( nFanins == 1 )
        {
            fprintf( pFile, "  ts_buf g%0*d ", nDigits, Counter++ );
            Io_WriteVerilogAuxArgs( pFile, pObj, 1, fPadZeros );
        }
        else if ( nFanins <= 4 )
        {
            fprintf( pFile, "  %s%d g%0*d ", pName, 4, nDigits, Counter++ );
            Io_WriteVerilogAuxArgs( pFile, pObj, 4, fPadZeros );
        }
        else if ( nFanins <= 6 )
        {
            fprintf( pFile, "  %s%d g%0*d ", pName, 6, nDigits, Counter++ );
            Io_WriteVerilogAuxArgs( pFile, pObj, 6, fPadZeros );
        }
        else if ( nFanins == 7 )
        {
            fprintf( pFile, "  %s%d g%0*d ", pName, 7, nDigits, Counter++ );
            Io_WriteVerilogAuxArgs( pFile, pObj, 7, fPadZeros );
        }
        else if ( nFanins == 8 )
        {
            fprintf( pFile, "  %s%d g%0*d ", pName, 8, nDigits, Counter++ );
            Io_WriteVerilogAuxArgs( pFile, pObj, 8, fPadZeros );
        }
        else if ( nFanins <= 16 )
        {
            fprintf( pFile, "  %s%d g%0*d ", pName, 16, nDigits, Counter++ );
            Io_WriteVerilogAuxArgs( pFile, pObj, 16, fPadZeros );
        }
        else if ( nFanins <= 32 )
        {
            fprintf( pFile, "  %s%d g%0*d ", pName, 32, nDigits, Counter++ );
            Io_WriteVerilogAuxArgs( pFile, pObj, 32, fPadZeros );
        }
        else if ( nFanins <= 64 )
        {
            fprintf( pFile, "  %s%d g%0*d ", pName, 64, nDigits, Counter++ );
            Io_WriteVerilogAuxArgs( pFile, pObj, 64, fPadZeros );
        }
        else if ( nFanins <= 128 )
        {
            fprintf( pFile, "  %s%d g%0*d ", pName, 128, nDigits, Counter++ );
            Io_WriteVerilogAuxArgs( pFile, pObj, 128, fPadZeros );
        }
    }
}

/**Function*************************************************************

  Synopsis    [Writes the inputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_WriteVerilogAuxArgs( FILE * pFile, Abc_Obj_t * pObj, int nInMax, int fPadZeros )
{
    Abc_Obj_t * pFanin;
    int i, Counter = 2;
    fprintf( pFile, "(.z (%s)", Io_WriteVerilogAuxGetName(Abc_ObjFanout0(pObj)) );
    Abc_ObjForEachFanin( pObj, pFanin, i )
    {
        if ( Counter++ % 4 == 0 )
            fprintf( pFile, "\n   " );
        fprintf( pFile, " .i%d (%s)", i+1, Io_WriteVerilogAuxGetName(Abc_ObjFanin(pObj,i)) );
    }
    for ( ; i < nInMax; i++ )
    {
        if ( Counter++ % 4 == 0 )
            fprintf( pFile, "\n   " );
        fprintf( pFile, " .i%d (%s)", i+1, fPadZeros? "1\'b0" : "1\'b1" );
    }
    fprintf( pFile, ");\n" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Io_WriteVerilogAuxCheckNtk( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    char * pSop;
    int i, k, nFanins;
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        if ( Abc_SopGetCubeNum(pObj->pData) > 1 )
        {
            printf( "Node %s contains a cover with more than one cube.\n", Abc_ObjName(pObj) );
            return 0;
        }
        nFanins = Abc_ObjFaninNum(pObj);
        if ( nFanins < 2 )
            continue;
        pSop = pObj->pData;
        for ( k = 0; k < nFanins; k++ )
            if ( pSop[k] != '1' )
            {
                printf( "Node %s contains a cover with non-positive literals.\n", Abc_ObjName(pObj) );
                return 0;
            }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Prepares the name for writing the Verilog file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Io_WriteVerilogAuxGetName( Abc_Obj_t * pObj )
{
    static char Buffer[20];
    char * pName;
    pName = Abc_ObjName(pObj);
    if ( pName[0] != '[' )
        return pName;
    // replace opening bracket by the escape sign and closing bracket by space
    // as a result of this transformation, the length of the name does not change
    strcpy( Buffer, pName );
    Buffer[0] = '\\';
    Buffer[strlen(Buffer)-1] = ' ';
    return Buffer;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


