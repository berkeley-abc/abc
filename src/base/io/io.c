/**CFile****************************************************************

  FileName    [io.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Command file.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: io.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "io.h"
#include "mainInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int IoCommandRead        ( Abc_Frame_t * pAbc, int argc, char **argv );
static int IoCommandReadBlif    ( Abc_Frame_t * pAbc, int argc, char **argv );
static int IoCommandReadBench   ( Abc_Frame_t * pAbc, int argc, char **argv );
static int IoCommandReadEdif    ( Abc_Frame_t * pAbc, int argc, char **argv );
static int IoCommandReadEqn     ( Abc_Frame_t * pAbc, int argc, char **argv );
static int IoCommandReadVerilog ( Abc_Frame_t * pAbc, int argc, char **argv );
static int IoCommandReadPla     ( Abc_Frame_t * pAbc, int argc, char **argv );

static int IoCommandWriteBlif   ( Abc_Frame_t * pAbc, int argc, char **argv );
static int IoCommandWriteBench  ( Abc_Frame_t * pAbc, int argc, char **argv );
static int IoCommandWriteCnf    ( Abc_Frame_t * pAbc, int argc, char **argv );
static int IoCommandWriteDot    ( Abc_Frame_t * pAbc, int argc, char **argv );
static int IoCommandWriteEqn    ( Abc_Frame_t * pAbc, int argc, char **argv );
static int IoCommandWriteGml    ( Abc_Frame_t * pAbc, int argc, char **argv );
static int IoCommandWritePla    ( Abc_Frame_t * pAbc, int argc, char **argv );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_Init( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "I/O", "read",          IoCommandRead,         1 );
    Cmd_CommandAdd( pAbc, "I/O", "read_blif",     IoCommandReadBlif,     1 );
    Cmd_CommandAdd( pAbc, "I/O", "read_bench",    IoCommandReadBench,    1 );
    Cmd_CommandAdd( pAbc, "I/O", "read_edif",     IoCommandReadEdif,     1 );
    Cmd_CommandAdd( pAbc, "I/O", "read_eqn",      IoCommandReadEqn,      1 );
    Cmd_CommandAdd( pAbc, "I/O", "read_verilog",  IoCommandReadVerilog,  1 );
    Cmd_CommandAdd( pAbc, "I/O", "read_pla",      IoCommandReadPla,      1 );

    Cmd_CommandAdd( pAbc, "I/O", "write_blif",    IoCommandWriteBlif,    0 );
    Cmd_CommandAdd( pAbc, "I/O", "write_bench",   IoCommandWriteBench,   0 );
    Cmd_CommandAdd( pAbc, "I/O", "write_cnf",     IoCommandWriteCnf,     0 );
    Cmd_CommandAdd( pAbc, "I/O", "write_dot",     IoCommandWriteDot,     0 );
    Cmd_CommandAdd( pAbc, "I/O", "write_eqn",     IoCommandWriteEqn,     0 );
    Cmd_CommandAdd( pAbc, "I/O", "write_gml",     IoCommandWriteGml,     0 );
    Cmd_CommandAdd( pAbc, "I/O", "write_pla",     IoCommandWritePla,     0 );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_End()
{
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int IoCommandRead( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk;
    char * FileName;
    FILE * pFile;
    int fCheck;
    int c;

    fCheck = 1;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "ch" ) ) != EOF )
    {
        switch ( c )
        {
            case 'c':
                fCheck ^= 1;
                break;
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }

    if ( argc != util_optind + 1 )
    {
        goto usage;
    }

    // get the input file name
    FileName = argv[util_optind];
    if ( (pFile = fopen( FileName, "r" )) == NULL )
    {
        fprintf( pAbc->Err, "Cannot open input file \"%s\". ", FileName );
        if ( FileName = Extra_FileGetSimilarName( FileName, ".mv", ".blif", ".pla", ".eqn", ".bench" ) )
            fprintf( pAbc->Err, "Did you mean \"%s\"?", FileName );
        fprintf( pAbc->Err, "\n" );
        return 1;
    }
    fclose( pFile );
 
    // set the new network
    pNtk = Io_Read( FileName, fCheck );
    if ( pNtk == NULL )
    {
        fprintf( pAbc->Err, "Reading network from file has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtk );
    return 0;

usage:
    fprintf( pAbc->Err, "usage: read [-ch] <file>\n" );
    fprintf( pAbc->Err, "\t         read the network from file in Verilog/BLIF/BENCH format\n" );
    fprintf( pAbc->Err, "\t-c     : toggle network check after reading [default = %s]\n", fCheck? "yes":"no" );
    fprintf( pAbc->Err, "\t-h     : prints the command summary\n" );
    fprintf( pAbc->Err, "\tfile   : the name of a file to read\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int IoCommandReadBlif( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pTemp;
    char * FileName;
    FILE * pFile;
    int fCheck;
    int c;

    fCheck = 1;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "ch" ) ) != EOF )
    {
        switch ( c )
        {
            case 'c':
                fCheck ^= 1;
                break;
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }

    if ( argc != util_optind + 1 )
    {
        goto usage;
    }

    // get the input file name
    FileName = argv[util_optind];
    if ( (pFile = fopen( FileName, "r" )) == NULL )
    {
        fprintf( pAbc->Err, "Cannot open input file \"%s\". ", FileName );
        if ( FileName = Extra_FileGetSimilarName( FileName, ".mv", ".blif", ".pla", ".eqn", ".bench" ) )
            fprintf( pAbc->Err, "Did you mean \"%s\"?", FileName );
        fprintf( pAbc->Err, "\n" );
        return 1;
    }
    fclose( pFile );
 
    // set the new network
    pNtk = Io_ReadBlif( FileName, fCheck );
    if ( pNtk == NULL )
    {
        fprintf( pAbc->Err, "Reading network from BLIF file has failed.\n" );
        return 1;
    }

    pNtk = Abc_NtkNetlistToLogic( pTemp = pNtk );
    Abc_NtkDelete( pTemp );
    if ( pNtk == NULL )
    {
        fprintf( pAbc->Err, "Converting to logic network after reading has failed.\n" );
        return 1;
    }

    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtk );
    return 0;

usage:
    fprintf( pAbc->Err, "usage: read_blif [-ch] <file>\n" );
    fprintf( pAbc->Err, "\t         read the network in binary BLIF format\n" );
    fprintf( pAbc->Err, "\t-c     : toggle network check after reading [default = %s]\n", fCheck? "yes":"no" );
    fprintf( pAbc->Err, "\t-h     : prints the command summary\n" );
    fprintf( pAbc->Err, "\tfile   : the name of a file to read\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int IoCommandReadBench( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pTemp;
    char * FileName;
    FILE * pFile;
    int fCheck;
    int c;

    fCheck = 1;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "ch" ) ) != EOF )
    {
        switch ( c )
        {
            case 'c':
                fCheck ^= 1;
                break;
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }

    if ( argc != util_optind + 1 )
    {
        goto usage;
    }

    // get the input file name
    FileName = argv[util_optind];
    if ( (pFile = fopen( FileName, "r" )) == NULL )
    {
        fprintf( pAbc->Err, "Cannot open input file \"%s\". ", FileName );
        if ( FileName = Extra_FileGetSimilarName( FileName, ".mv", ".blif", ".pla", ".eqn", ".bench" ) )
            fprintf( pAbc->Err, "Did you mean \"%s\"?", FileName );
        fprintf( pAbc->Err, "\n" );
        return 1;
    }
    fclose( pFile );

    // set the new network
    pNtk = Io_ReadBench( FileName, fCheck );
    if ( pNtk == NULL )
    {
        fprintf( pAbc->Err, "Reading network from BENCH file has failed.\n" );
        return 1;
    }

    pNtk = Abc_NtkNetlistToLogic( pTemp = pNtk );
    Abc_NtkDelete( pTemp );
    if ( pNtk == NULL )
    {
        fprintf( pAbc->Err, "Converting to logic network after reading has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtk );
    return 0;

usage:
    fprintf( pAbc->Err, "usage: read_bench [-ch] <file>\n" );
    fprintf( pAbc->Err, "\t         read the network in BENCH format\n" );
    fprintf( pAbc->Err, "\t-c     : toggle network check after reading [default = %s]\n", fCheck? "yes":"no" );
    fprintf( pAbc->Err, "\t-h     : prints the command summary\n" );
    fprintf( pAbc->Err, "\tfile   : the name of a file to read\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int IoCommandReadEdif( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pTemp;
    char * FileName;
    FILE * pFile;
    int fCheck;
    int c;

    fCheck = 1;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "ch" ) ) != EOF )
    {
        switch ( c )
        {
            case 'c':
                fCheck ^= 1;
                break;
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }

    if ( argc != util_optind + 1 )
    {
        goto usage;
    }

    // get the input file name
    FileName = argv[util_optind];
    if ( (pFile = fopen( FileName, "r" )) == NULL )
    {
        fprintf( pAbc->Err, "Cannot open input file \"%s\". ", FileName );
        if ( FileName = Extra_FileGetSimilarName( FileName, ".mv", ".blif", ".pla", ".eqn", ".bench" ) )
            fprintf( pAbc->Err, "Did you mean \"%s\"?", FileName );
        fprintf( pAbc->Err, "\n" );
        return 1;
    }
    fclose( pFile );

    // set the new network
    pNtk = Io_ReadEdif( FileName, fCheck );
    if ( pNtk == NULL )
    {
        fprintf( pAbc->Err, "Reading network from EDIF file has failed.\n" );
        return 1;
    }

    pNtk = Abc_NtkNetlistToLogic( pTemp = pNtk );
    Abc_NtkDelete( pTemp );
    if ( pNtk == NULL )
    {
        fprintf( pAbc->Err, "Converting to logic network after reading has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtk );
    return 0;

usage:
    fprintf( pAbc->Err, "usage: read_edif [-ch] <file>\n" );
    fprintf( pAbc->Err, "\t         read the network in EDIF (works only for ISCAS benchmarks)\n" );
    fprintf( pAbc->Err, "\t-c     : toggle network check after reading [default = %s]\n", fCheck? "yes":"no" );
    fprintf( pAbc->Err, "\t-h     : prints the command summary\n" );
    fprintf( pAbc->Err, "\tfile   : the name of a file to read\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int IoCommandReadEqn( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pTemp;
    char * FileName;
    FILE * pFile;
    int fCheck;
    int c;

    fCheck = 1;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "ch" ) ) != EOF )
    {
        switch ( c )
        {
            case 'c':
                fCheck ^= 1;
                break;
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }

    if ( argc != util_optind + 1 )
    {
        goto usage;
    }

    // get the input file name
    FileName = argv[util_optind];
    if ( (pFile = fopen( FileName, "r" )) == NULL )
    {
        fprintf( pAbc->Err, "Cannot open input file \"%s\". ", FileName );
        if ( FileName = Extra_FileGetSimilarName( FileName, ".mv", ".blif", ".pla", ".eqn", ".bench" ) )
            fprintf( pAbc->Err, "Did you mean \"%s\"?", FileName );
        fprintf( pAbc->Err, "\n" );
        return 1;
    }
    fclose( pFile );

    // set the new network
    pNtk = Io_ReadEqn( FileName, fCheck );
    if ( pNtk == NULL )
    {
        fprintf( pAbc->Err, "Reading network from the equation file has failed.\n" );
        return 1;
    }

    pNtk = Abc_NtkNetlistToLogic( pTemp = pNtk );
    Abc_NtkDelete( pTemp );
    if ( pNtk == NULL )
    {
        fprintf( pAbc->Err, "Converting to logic network after reading has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtk );
    return 0;

usage:
    fprintf( pAbc->Err, "usage: read_eqn [-ch] <file>\n" );
    fprintf( pAbc->Err, "\t         read the network in equation format\n" );
    fprintf( pAbc->Err, "\t-c     : toggle network check after reading [default = %s]\n", fCheck? "yes":"no" );
    fprintf( pAbc->Err, "\t-h     : prints the command summary\n" );
    fprintf( pAbc->Err, "\tfile   : the name of a file to read\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int IoCommandReadVerilog( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pTemp;
    char * FileName;
    FILE * pFile;
    int fCheck;
    int c;

    fCheck = 1;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "ch" ) ) != EOF )
    {
        switch ( c )
        {
            case 'c':
                fCheck ^= 1;
                break;
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }

    if ( argc != util_optind + 1 )
    {
        goto usage;
    }

    // get the input file name
    FileName = argv[util_optind];
    if ( (pFile = fopen( FileName, "r" )) == NULL )
    {
        fprintf( pAbc->Err, "Cannot open input file \"%s\". ", FileName );
        if ( FileName = Extra_FileGetSimilarName( FileName, ".mv", ".blif", ".pla", ".eqn", ".bench" ) )
            fprintf( pAbc->Err, "Did you mean \"%s\"?", FileName );
        fprintf( pAbc->Err, "\n" );
        return 1;
    }
    fclose( pFile );

    // set the new network
    pNtk = Io_ReadVerilog( FileName, fCheck );
    if ( pNtk == NULL )
    {
        fprintf( pAbc->Err, "Reading network from the verilog file has failed.\n" );
        return 1;
    }

    pNtk = Abc_NtkNetlistToLogic( pTemp = pNtk );
    Abc_NtkDelete( pTemp );
    if ( pNtk == NULL )
    {
        fprintf( pAbc->Err, "Converting to logic network after reading has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtk );
    return 0;

usage:
    fprintf( pAbc->Err, "usage: read_verilog [-ch] <file>\n" );
    fprintf( pAbc->Err, "\t         read the network in Verilog (IWLS 2005 subset)\n" );
    fprintf( pAbc->Err, "\t-c     : toggle network check after reading [default = %s]\n", fCheck? "yes":"no" );
    fprintf( pAbc->Err, "\t-h     : prints the command summary\n" );
    fprintf( pAbc->Err, "\tfile   : the name of a file to read\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int IoCommandReadPla( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pTemp;
    char * FileName;
    FILE * pFile;
    int fCheck;
    int c;

    fCheck = 1;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "ch" ) ) != EOF )
    {
        switch ( c )
        {
            case 'c':
                fCheck ^= 1;
                break;
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }

    if ( argc != util_optind + 1 )
    {
        goto usage;
    }

    // get the input file name
    FileName = argv[util_optind];
    if ( (pFile = fopen( FileName, "r" )) == NULL )
    {
        fprintf( pAbc->Err, "Cannot open input file \"%s\". ", FileName );
        if ( FileName = Extra_FileGetSimilarName( FileName, ".mv", ".blif", ".pla", ".eqn", ".bench" ) )
            fprintf( pAbc->Err, "Did you mean \"%s\"?", FileName );
        fprintf( pAbc->Err, "\n" );
        return 1;
    }
    fclose( pFile );

    // set the new network
    pNtk = Io_ReadPla( FileName, fCheck );
    if ( pNtk == NULL )
    {
        fprintf( pAbc->Err, "Reading network from PLA file has failed.\n" );
        return 1;
    }

    pNtk = Abc_NtkNetlistToLogic( pTemp = pNtk );
    Abc_NtkDelete( pTemp );
    if ( pNtk == NULL )
    {
        fprintf( pAbc->Err, "Converting to logic network after reading has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtk );
    return 0;

usage:
    fprintf( pAbc->Err, "usage: read_pla [-ch] <file>\n" );
    fprintf( pAbc->Err, "\t         read the network in PLA\n" );
    fprintf( pAbc->Err, "\t-c     : toggle network check after reading [default = %s]\n", fCheck? "yes":"no" );
    fprintf( pAbc->Err, "\t-h     : prints the command summary\n" );
    fprintf( pAbc->Err, "\tfile   : the name of a file to read\n" );
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int IoCommandWriteBlif( Abc_Frame_t * pAbc, int argc, char **argv )
{
    Abc_Ntk_t * pNtk;
    char * FileName;
    int fWriteLatches;
    int c;

    fWriteLatches = 1;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "lh" ) ) != EOF )
    {
        switch ( c )
        {
            case 'l':
                fWriteLatches ^= 1;
                break;
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }

    pNtk = pAbc->pNtkCur;
    if ( pNtk == NULL )
    {
        fprintf( pAbc->Out, "Empty network.\n" );
        return 0;
    }

    if ( argc != util_optind + 1 )
    {
        goto usage;
    }
    FileName = argv[util_optind];

    // check the network type
    if ( !Abc_NtkIsLogic(pNtk) && !Abc_NtkIsStrash(pNtk) && !Abc_NtkIsSeq(pNtk) )
    {
        fprintf( pAbc->Out, "Currently can only write logic networks, AIGs, and seq AIGs.\n" );
        return 0;
    }
    Io_WriteBlifLogic( pNtk, FileName, fWriteLatches );
//    Io_WriteBlif( pNtk, FileName, fWriteLatches );
    return 0;

usage:
    fprintf( pAbc->Err, "usage: write_blif [-lh] <file>\n" );
    fprintf( pAbc->Err, "\t         write the network into a BLIF file\n" );
    fprintf( pAbc->Err, "\t-l     : toggle writing latches [default = %s]\n", fWriteLatches? "yes":"no" );
    fprintf( pAbc->Err, "\t-h     : print the help massage\n" );
    fprintf( pAbc->Err, "\tfile   : the name of the file to write\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int IoCommandWriteBench( Abc_Frame_t * pAbc, int argc, char **argv )
{
    Abc_Ntk_t * pNtk, * pNtkTemp;
    char * FileName;
    int fWriteLatches;
    int c;

    fWriteLatches = 1;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "lh" ) ) != EOF )
    {
        switch ( c )
        {
            case 'l':
                fWriteLatches ^= 1;
                break;
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }

    pNtk = pAbc->pNtkCur;
    if ( pNtk == NULL )
    {
        fprintf( pAbc->Out, "Empty network.\n" );
        return 0;
    }

    if ( argc != util_optind + 1 )
    {
        goto usage;
    }
    // get the input file name
    FileName = argv[util_optind];

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pAbc->Out, "The network should be an AIG.\n" );
        return 0;
    }

    // derive the netlist
    pNtkTemp = Abc_NtkLogicToNetlistBench(pNtk);
    if ( pNtkTemp == NULL )
    {
        fprintf( pAbc->Out, "Writing BENCH has failed.\n" );
        return 0;
    }
    Io_WriteBench( pNtkTemp, FileName );
    Abc_NtkDelete( pNtkTemp );
    return 0;

usage:
    fprintf( pAbc->Err, "usage: write_bench [-h] <file>\n" );
    fprintf( pAbc->Err, "\t         write the network in BENCH format\n" );
//    fprintf( pAbc->Err, "\t-l     : toggle writing latches [default = %s]\n", fWriteLatches? "yes":"no" );
    fprintf( pAbc->Err, "\t-h     : print the help massage\n" );
    fprintf( pAbc->Err, "\tfile   : the name of the file to write\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int IoCommandWriteCnf( Abc_Frame_t * pAbc, int argc, char **argv )
{
    char * FileName;
    int c;

    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }

    if ( pAbc->pNtkCur == NULL )
    {
        fprintf( pAbc->Out, "Empty network.\n" );
        return 0;
    }

    if ( argc != util_optind + 1 )
    {
        goto usage;
    }

    // get the input file name
    FileName = argv[util_optind];
    // write the file
    if ( !Io_WriteCnf( pAbc->pNtkCur, FileName ) )
    {
        printf( "Writing CNF has failed.\n" );
        return 1;
    }
    return 0;

usage:
    fprintf( pAbc->Err, "usage: write_cnf [-h] <file>\n" );
    fprintf( pAbc->Err, "\t         write the miter cone into a CNF file\n" );
    fprintf( pAbc->Err, "\t-h     : print the help massage\n" );
    fprintf( pAbc->Err, "\tfile   : the name of the file to write\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int IoCommandWriteDot( Abc_Frame_t * pAbc, int argc, char **argv )
{
    char * FileName;
    Vec_Ptr_t * vNodes;
    int c;

    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }

    if ( pAbc->pNtkCur == NULL )
    {
        fprintf( pAbc->Out, "Empty network.\n" );
        return 0;
    }

    if ( !Abc_NtkIsStrash(pAbc->pNtkCur) )
    {
        fprintf( stdout, "IoCommandWriteDot(): Currently can only process logic networks with BDDs.\n" );
        return 0;
    }

    if ( argc != util_optind + 1 )
    {
        goto usage;
    }

    // get the input file name
    FileName = argv[util_optind];
    // write the file
    vNodes = Abc_NtkCollectObjects( pAbc->pNtkCur );
    Io_WriteDot( pAbc->pNtkCur, vNodes, NULL, FileName );
    Vec_PtrFree( vNodes );
    return 0;

usage:
    fprintf( pAbc->Err, "usage: write_dot [-h] <file>\n" );
    fprintf( pAbc->Err, "\t         write the AIG into a DOT file\n" );
    fprintf( pAbc->Err, "\t-h     : print the help massage\n" );
    fprintf( pAbc->Err, "\tfile   : the name of the file to write\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int IoCommandWriteEqn( Abc_Frame_t * pAbc, int argc, char **argv )
{
    Abc_Ntk_t * pNtk, * pNtkTemp;
    char * FileName;
    int c;

    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }

    pNtk = pAbc->pNtkCur;
    if ( pNtk == NULL )
    {
        fprintf( pAbc->Out, "Empty network.\n" );
        return 0;
    }

    if ( argc != util_optind + 1 )
    {
        goto usage;
    }

    if ( !Abc_NtkIsLogic(pNtk) && !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( stdout, "IoCommandWriteGml(): Currently can only process logic networks with BDDs.\n" );
        return 0;
    }

    // get the input file name
    FileName = argv[util_optind];
    // write the file
    // get rid of complemented covers if present
    if ( Abc_NtkIsSopLogic(pNtk) )
        Abc_NtkLogicMakeDirectSops(pNtk);
    // derive the netlist
    pNtkTemp = Abc_NtkLogicToNetlist(pNtk);
    if ( pNtkTemp == NULL )
    {
        fprintf( pAbc->Out, "Writing BENCH has failed.\n" );
        return 0;
    }
    Io_WriteEqn( pNtkTemp, FileName );
    Abc_NtkDelete( pNtkTemp );
    return 0;

usage:
    fprintf( pAbc->Err, "usage: write_eqn [-h] <file>\n" );
    fprintf( pAbc->Err, "\t         write the current network in the equation format\n" );
    fprintf( pAbc->Err, "\t-h     : print the help massage\n" );
    fprintf( pAbc->Err, "\tfile   : the name of the file to write\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int IoCommandWriteGml( Abc_Frame_t * pAbc, int argc, char **argv )
{
    char * FileName;
    int c;

    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }

    if ( pAbc->pNtkCur == NULL )
    {
        fprintf( pAbc->Out, "Empty network.\n" );
        return 0;
    }

    if ( !Abc_NtkIsLogic(pAbc->pNtkCur) && !Abc_NtkIsStrash(pAbc->pNtkCur) )
    {
        fprintf( stdout, "IoCommandWriteGml(): Currently can only process logic networks with BDDs.\n" );
        return 0;
    }

    if ( argc != util_optind + 1 )
    {
        goto usage;
    }

    // get the input file name
    FileName = argv[util_optind];
    // write the file
    Io_WriteGml( pAbc->pNtkCur, FileName );
    return 0;

usage:
    fprintf( pAbc->Err, "usage: write_gml [-h] <file>\n" );
    fprintf( pAbc->Err, "\t         write network using graph representation formal GML\n" );
    fprintf( pAbc->Err, "\t-h     : print the help massage\n" );
    fprintf( pAbc->Err, "\tfile   : the name of the file to write\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int IoCommandWritePla( Abc_Frame_t * pAbc, int argc, char **argv )
{
    Abc_Ntk_t * pNtk, * pNtkTemp;
    char * FileName;
    int c;

    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }

    pNtk = pAbc->pNtkCur;
    if ( pNtk == NULL )
    {
        fprintf( pAbc->Out, "Empty network.\n" );
        return 0;
    }

    if ( Abc_NtkGetLevelNum(pNtk) > 1 )
    {
        fprintf( pAbc->Out, "PLA writing is available for collapsed networks.\n" );
        return 0;
    }

    if ( Abc_NtkLatchNum(pNtk) > 0 )
    {
        fprintf( pAbc->Out, "Latches are writed at PI/PO pairs in the PLA file.\n" );
        return 0;
    }

    if ( argc != util_optind + 1 )
    {
        goto usage;
    }
    // get the input file name
    FileName = argv[util_optind];

    // derive the netlist
    pNtkTemp = Abc_NtkLogicToNetlist(pNtk);
    if ( pNtkTemp == NULL )
    {
        fprintf( pAbc->Out, "Writing PLA has failed.\n" );
        return 0;
    }
    Io_WritePla( pNtkTemp, FileName );
    Abc_NtkDelete( pNtkTemp );
    return 0;

usage:
    fprintf( pAbc->Err, "usage: write_pla [-h] <file>\n" );
    fprintf( pAbc->Err, "\t         write the collapsed network into a PLA file\n" );
    fprintf( pAbc->Err, "\t-h     : print the help massage\n" );
    fprintf( pAbc->Err, "\tfile   : the name of the file to write\n" );
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


