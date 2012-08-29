/**CFile****************************************************************

  FileName    [scl.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  Synopsis    [Standard-cell library representation.]

  Author      [Alan Mishchenko, Niklas Een]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 24, 2012.]

  Revision    [$Id: scl.c,v 1.0 2012/08/24 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sclInt.h"
#include "scl.h"
#include "base/main/mainInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int Scl_CommandRead  ( Abc_Frame_t * pAbc, int argc, char **argv );
static int Scl_CommandWrite ( Abc_Frame_t * pAbc, int argc, char **argv );
static int Scl_CommandPrint ( Abc_Frame_t * pAbc, int argc, char **argv );
static int Scl_CommandStime ( Abc_Frame_t * pAbc, int argc, char **argv );
static int Scl_CommandGsize ( Abc_Frame_t * pAbc, int argc, char **argv );
static int Scl_CommandBuffer( Abc_Frame_t * pAbc, int argc, char **argv );

extern int         Abc_SclCheckNtk( Abc_Ntk_t * p, int fVerbose );
extern Abc_Ntk_t * Abc_SclPerformBuffering( Abc_Ntk_t * p, int Degree, int fVerbose );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Scl_Init( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "SC mapping",  "read_scl",   Scl_CommandRead,   0 ); 
    Cmd_CommandAdd( pAbc, "SC mapping",  "write_scl",  Scl_CommandWrite,  0 ); 
    Cmd_CommandAdd( pAbc, "SC mapping",  "print_scl",  Scl_CommandPrint,  0 ); 
    Cmd_CommandAdd( pAbc, "SC mapping",  "stime",      Scl_CommandStime,  0 ); 
    Cmd_CommandAdd( pAbc, "SC mapping",  "gsize",      Scl_CommandGsize,  1 ); 
    Cmd_CommandAdd( pAbc, "SC mapping",  "buffer",     Scl_CommandBuffer, 1 ); 
}
void Scl_End( Abc_Frame_t * pAbc )
{
    Abc_SclLoad( NULL, (SC_Lib **)&pAbc->pLibScl );
}



/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Scl_CommandRead( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char * pFileName;
    FILE * pFile;
    int c;

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }
    if ( argc != globalUtilOptind + 1 )
        goto usage;

    // get the input file name
    pFileName = argv[globalUtilOptind];
    if ( (pFile = fopen( pFileName, "rb" )) == NULL )
    {
        fprintf( pAbc->Err, "Cannot open input file \"%s\". \n", pFileName );
        return 1;
    }
    fclose( pFile );

    // read new library
    Abc_SclLoad( pFileName, (SC_Lib **)&pAbc->pLibScl );
    Abc_SclWriteText( "sizing\\scl_out.txt", pAbc->pLibScl );
    return 0;

usage:
    fprintf( pAbc->Err, "usage: read_scl [-h] <file>\n" );
    fprintf( pAbc->Err, "\t         reads Liberty library from file\n" );
    fprintf( pAbc->Err, "\t-h     : prints the command summary\n" );
    fprintf( pAbc->Err, "\t<file> : the name of a file to read\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Scl_CommandWrite( Abc_Frame_t * pAbc, int argc, char **argv )
{
    FILE * pFile;
    char * pFileName;
    int c;

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }
    if ( argc != globalUtilOptind + 1 )
        goto usage;
    if ( pAbc->pLibScl == NULL )
    {
        fprintf( pAbc->Err, "There is no Liberty library available.\n" );
        return 1;
    }
    // get the input file name
    pFileName = argv[globalUtilOptind];
    if ( (pFile = fopen( pFileName, "wb" )) == NULL )
    {
        fprintf( pAbc->Err, "Cannot open output file \"%s\". \n", pFileName );
        return 1;
    }
    fclose( pFile );

    // save current library
    Abc_SclSave( pFileName, (SC_Lib *)pAbc->pLibScl );
    return 0;

usage:
    fprintf( pAbc->Err, "usage: write_scl [-h] <file>\n" );
    fprintf( pAbc->Err, "\t         write Liberty library into file\n" );
    fprintf( pAbc->Err, "\t-h     : print the help massage\n" );
    fprintf( pAbc->Err, "\t<file> : the name of the file to write\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Scl_CommandPrint( Abc_Frame_t * pAbc, int argc, char **argv )
{
    int c;

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }
    if ( pAbc->pLibScl == NULL )
    {
        fprintf( pAbc->Err, "There is no Liberty library available.\n" );
        return 1;
    }

    // save current library
    Abc_SclPrintCells( pAbc->pLibScl );
    return 0;

usage:
    fprintf( pAbc->Err, "usage: print_scl [-h]\n" );
    fprintf( pAbc->Err, "\t         prints statistics of Liberty library\n" );
    fprintf( pAbc->Err, "\t-h     : print the help massage\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Scl_CommandStime( Abc_Frame_t * pAbc, int argc, char **argv )
{
    int c;

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }

    if ( Abc_FrameReadNtk(pAbc) == NULL )
    {
        fprintf( pAbc->Err, "There is no current network.\n" );
        return 1;
    }
    if ( !Abc_NtkHasMapping(Abc_FrameReadNtk(pAbc)) )
    {
        fprintf( pAbc->Err, "The current network is not mapped.\n" );
        return 1;
    }
    if ( !Abc_SclCheckNtk(Abc_FrameReadNtk(pAbc), 0) )
    {
        fprintf( pAbc->Err, "The current networks is not in a topo order (run \"buffer -N 1000\").\n" );
        return 1;
    }
    if ( pAbc->pLibScl == NULL )
    {
        fprintf( pAbc->Err, "There is no Liberty library available.\n" );
        return 1;
    }

    Abc_SclTimePerform( pAbc->pLibScl, Abc_FrameReadNtk(pAbc) );
    return 0;

usage:
    fprintf( pAbc->Err, "usage: stime [-h]\n" );
    fprintf( pAbc->Err, "\t         performs STA using Liberty library\n" );
    fprintf( pAbc->Err, "\t-h     : print the help massage\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Scl_CommandGsize( Abc_Frame_t * pAbc, int argc, char **argv )
{
    int c;
    int nSteps = 100;

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Nh" ) ) != EOF )
    {
        switch ( c )
        {
            case 'N':
                if ( globalUtilOptind >= argc )
                {
                    Abc_Print( -1, "Command line switch \"-N\" should be followed by a positive integer.\n" );
                    goto usage;
                }
                nSteps = atoi(argv[globalUtilOptind]);
                globalUtilOptind++;
                if ( nSteps <= 0 ) 
                    goto usage;
                break;
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }

    if ( Abc_FrameReadNtk(pAbc) == NULL )
    {
        fprintf( pAbc->Err, "There is no current network.\n" );
        return 1;
    }
    if ( !Abc_NtkHasMapping(Abc_FrameReadNtk(pAbc)) )
    {
        fprintf( pAbc->Err, "The current network is not mapped.\n" );
        return 1;
    }
    if ( !Abc_SclCheckNtk(Abc_FrameReadNtk(pAbc), 0) )
    {
        fprintf( pAbc->Err, "The current networks is not in a topo order (run \"buffer -N 1000\").\n" );
        return 1;
    }
    if ( pAbc->pLibScl == NULL )
    {
        fprintf( pAbc->Err, "There is no Liberty library available.\n" );
        return 1;
    }

//    Abc_SclSizingPerform( pAbc->pLibScl, Abc_FrameReadNtk(pAbc), nSteps );
    return 0;

usage:
    fprintf( pAbc->Err, "usage: gsize [-N num] [-h]\n" );
    fprintf( pAbc->Err, "\t           performs gate sizing using Liberty library\n" );
    fprintf( pAbc->Err, "\t-N <num> : the number of refinement iterations [default = %d]\n", nSteps );
    fprintf( pAbc->Err, "\t-h       : print the help massage\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Scl_CommandBuffer( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Ntk_t * pNtkRes;
    int Degree;
    int c, fVerbose;
    Degree   = 3;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Nvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by a positive integer.\n" );
                goto usage;
            }
            Degree = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Degree < 0 ) 
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "This command can only be applied to a logic network.\n" );
        return 1;
    }

    // modify the current network
    pNtkRes = Abc_SclPerformBuffering( pNtk, Degree, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "The command has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    fprintf( pAbc->Err, "usage: buffer [-N num] [-vh]\n" );
    fprintf( pAbc->Err, "\t           performs buffering of the mapped network\n" );
    fprintf( pAbc->Err, "\t-N <num> : the number of refinement iterations [default = %d]\n", Degree );
    fprintf( pAbc->Err, "\t-v       : toggle printing optimization summary [default = %s]\n", fVerbose? "yes": "no" );
    fprintf( pAbc->Err, "\t-h       : print the command usage\n");
    return 1;
} 


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

