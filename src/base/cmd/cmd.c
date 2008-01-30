/**CFile****************************************************************

  FileName    [cmd.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Command file.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cmd.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#include "mainInt.h"
#include "cmdInt.h"
#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int CmdCommandTime          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int CmdCommandEcho          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int CmdCommandQuit          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int CmdCommandWhich         ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int CmdCommandHistory       ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int CmdCommandAlias         ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int CmdCommandUnalias       ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int CmdCommandHelp          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int CmdCommandSource        ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int CmdCommandSetVariable   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int CmdCommandUnsetVariable ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int CmdCommandUndo          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int CmdCommandRecall        ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int CmdCommandEmpty         ( Abc_Frame_t * pAbc, int argc, char ** argv );
#ifdef WIN32
static int CmdCommandLs            ( Abc_Frame_t * pAbc, int argc, char ** argv );
#endif
static int CmdCommandSis           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int CmdCommandMvsis         ( Abc_Frame_t * pAbc, int argc, char ** argv );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function********************************************************************

  Synopsis    [Initializes the command package.]

  SideEffects [Commands are added to the command table.]

  SeeAlso     [Cmd_End]

******************************************************************************/
void Cmd_Init( Abc_Frame_t * pAbc )
{
    pAbc->tCommands = st_init_table(strcmp, st_strhash);
    pAbc->tAliases  = st_init_table(strcmp, st_strhash);
    pAbc->tFlags    = st_init_table(strcmp, st_strhash);
    pAbc->aHistory  = Vec_PtrAlloc( 100 );

    Cmd_CommandAdd( pAbc, "Basic", "time",      CmdCommandTime,           0);
    Cmd_CommandAdd( pAbc, "Basic", "echo",      CmdCommandEcho,           0);
    Cmd_CommandAdd( pAbc, "Basic", "quit",      CmdCommandQuit,           0);
    Cmd_CommandAdd( pAbc, "Basic", "history",   CmdCommandHistory,        0);
    Cmd_CommandAdd( pAbc, "Basic", "alias",     CmdCommandAlias,          0);
    Cmd_CommandAdd( pAbc, "Basic", "unalias",   CmdCommandUnalias,        0);
    Cmd_CommandAdd( pAbc, "Basic", "help",      CmdCommandHelp,           0);
    Cmd_CommandAdd( pAbc, "Basic", "source",    CmdCommandSource,         0);
    Cmd_CommandAdd( pAbc, "Basic", "set",       CmdCommandSetVariable,    0);
    Cmd_CommandAdd( pAbc, "Basic", "unset",     CmdCommandUnsetVariable,  0);
    Cmd_CommandAdd( pAbc, "Basic", "undo",      CmdCommandUndo,           0); 
    Cmd_CommandAdd( pAbc, "Basic", "recall",    CmdCommandRecall,         0); 
    Cmd_CommandAdd( pAbc, "Basic", "empty",     CmdCommandEmpty,          0); 
#ifdef WIN32
    Cmd_CommandAdd( pAbc, "Basic", "ls",        CmdCommandLs,             0 );
#endif

    Cmd_CommandAdd( pAbc, "Various", "sis",     CmdCommandSis,            1); 
    Cmd_CommandAdd( pAbc, "Various", "mvsis",   CmdCommandMvsis,          1); 
}

/**Function********************************************************************

  Synopsis    [Ends the command package.]

  Description [Ends the command package. Tables are freed.]

  SideEffects []

  SeeAlso     []

******************************************************************************/
void Cmd_End( Abc_Frame_t * pAbc )
{
    st_generator * gen;
    char * pKey, * pValue;
    int i;

//    st_free_table( pAbc->tCommands, (void (*)()) 0, CmdCommandFree );
//    st_free_table( pAbc->tAliases,  (void (*)()) 0, CmdCommandAliasFree );
//    st_free_table( pAbc->tFlags,    free, free );

    st_foreach_item( pAbc->tCommands, gen, (char **)&pKey, (char **)&pValue )
        CmdCommandFree( (Abc_Command *)pValue );
    st_free_table( pAbc->tCommands );

    st_foreach_item( pAbc->tAliases, gen, (char **)&pKey, (char **)&pValue )
        CmdCommandAliasFree( (Abc_Alias *)pValue );
    st_free_table( pAbc->tAliases );

    st_foreach_item( pAbc->tFlags, gen, (char **)&pKey, (char **)&pValue )
        free( pKey ), free( pValue );
    st_free_table( pAbc->tFlags );

    for ( i = 0; i < pAbc->aHistory->nSize; i++ )
        free( pAbc->aHistory->pArray[i] );
    Vec_PtrFree( pAbc->aHistory );
}



/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int CmdCommandTime( Abc_Frame_t * pAbc, int argc, char **argv )
{
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

    if ( argc != util_optind )
    {
        goto usage;
    }

    pAbc->TimeTotal += pAbc->TimeCommand;
    fprintf( pAbc->Out, "elapse: %3.2f seconds, total: %3.2f seconds\n",
        (float)pAbc->TimeCommand / CLOCKS_PER_SEC, (float)pAbc->TimeTotal / CLOCKS_PER_SEC );
    pAbc->TimeCommand = 0;
    return 0;

  usage:
    fprintf( pAbc->Err, "usage: time [-h]\n" );
    fprintf( pAbc->Err, "   -h \t\tprint the command usage\n" );
    return 1;
}

/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int CmdCommandEcho( Abc_Frame_t * pAbc, int argc, char **argv )
{
    int i;
    int c;
    int n = 1;

    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "hn" ) ) != EOF )
    {
        switch ( c )
        {
        case 'n':
            n = 0;
            break;
        case 'h':
            goto usage;
            break;
        default:
            goto usage;
        }
    }

    for ( i = util_optind; i < argc; i++ )
        fprintf( pAbc->Out, "%s ", argv[i] );
    if ( n )
        fprintf( pAbc->Out, "\n" );
    else
        fflush ( pAbc->Out );
    return 0;

  usage:
    fprintf( pAbc->Err, "usage: echo [-h] string \n" );
    fprintf( pAbc->Err, "   -n \t\tsuppress newline at the end\n" );
    fprintf( pAbc->Err, "   -h \t\tprint the command usage\n" );
    return ( 1 );
}

/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int CmdCommandQuit( Abc_Frame_t * pAbc, int argc, char **argv )
{
    int c;

    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "hs" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
            break;
        case 's':
            return -2;
            break;
        default:
            goto usage;
        }
    }

    if ( argc != util_optind )
        goto usage;
    return -1;

  usage:
    fprintf( pAbc->Err, "usage: quit [-h] [-s]\n" );
    fprintf( pAbc->Err, "   -h  print the command usage\n" );
    fprintf( pAbc->Err,
                      "   -s  frees all the memory before quitting\n" );
    return 1;
}

/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int CmdCommandWhich( Abc_Frame_t * pAbc, int argc, char **argv )
{
    return 0;
}

/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int CmdCommandHistory( Abc_Frame_t * pAbc, int argc, char **argv )
{
    int i, c, num, size;

    num = 20;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
            case 'h':
                goto usage;
            default :
                goto usage;
        }
    }
    if ( argc > 2 )
        goto usage;

    // get the number of commands to print
    if ( argc == util_optind + 1 )
        num = atoi(argv[util_optind]);
    // print the commands
    size = pAbc->aHistory->nSize;
    num = ( num < size ) ? num : size;
    for ( i = size - num; i < size; i++ )
        fprintf( pAbc->Out, "%s", pAbc->aHistory->pArray[i] );
    return 0;

usage:
    fprintf( pAbc->Err, "usage: history [-h] <num>\n" );
    fprintf( pAbc->Err, "          prints the latest command entered on the command line\n" );
    fprintf( pAbc->Err, " -h     : print the command usage\n" );
    fprintf( pAbc->Err, "num     : print the last num commands\n" );
    return ( 1 );
}

/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int CmdCommandAlias( Abc_Frame_t * pAbc, int argc, char **argv )
{
    char *key, *value;
    int c;

    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
            break;
        default:
            goto usage;
        }
    }


    if ( argc == 1 )
    {
        CmdPrintTable( pAbc->tAliases, 1 );
        return 0;

    }
    else if ( argc == 2 )
    {
        if ( st_lookup( pAbc->tAliases, argv[1], &value ) )
            CmdCommandAliasPrint( pAbc, ( Abc_Alias * ) value );
        return 0;
    }

    // delete any existing alias 
    key = argv[1];
    if ( st_delete( pAbc->tAliases, &key, &value ) )
        CmdCommandAliasFree( ( Abc_Alias * ) value );
    CmdCommandAliasAdd( pAbc, argv[1], argc - 2, argv + 2 );
    return 0;

usage:
    fprintf( pAbc->Err, "usage: alias [-h] [command [string]]\n" );
    fprintf( pAbc->Err, "   -h \t\tprint the command usage\n" );
    return ( 1 );
}

/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int CmdCommandUnalias( Abc_Frame_t * pAbc, int argc, char **argv )
{
    int i;
    char *key, *value;
    int c;

    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
            break;
        default:
            goto usage;
        }
    }

    if ( argc < 2 )
    {
        goto usage;
    }

    for ( i = 1; i < argc; i++ )
    {
        key = argv[i];
        if ( st_delete( pAbc->tAliases, &key, &value ) )
        {
            CmdCommandAliasFree( ( Abc_Alias * ) value );
        }
    }
    return 0;

  usage:
    fprintf( pAbc->Err, "usage: unalias [-h] alias_names\n" );
    fprintf( pAbc->Err, "   -h \t\tprint the command usage\n" );
    return 1;
}

/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int CmdCommandHelp( Abc_Frame_t * pAbc, int argc, char **argv )
{
    bool fPrintAll;
    int c;

    fPrintAll = 0;
    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "ah" ) ) != EOF )
    {
        switch ( c )
        {
        case 'a':
            case 'v':
                fPrintAll ^= 1;
                break;
            break;
        case 'h':
            goto usage;
            break;
        default:
            goto usage;
        }
    }

    if ( argc != util_optind )
        goto usage;

    CmdCommandPrint( pAbc, fPrintAll );
    return 0;

usage:
    fprintf( pAbc->Err, "usage: help [-a] [-h]\n" );
    fprintf( pAbc->Err, "       prints the list of available commands by group\n" );
    fprintf( pAbc->Err, " -a       toggle printing hidden commands [default = %s]\n", fPrintAll? "yes": "no" );
    fprintf( pAbc->Err, " -h       print the command usage\n" );
    return 1;
}

/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int CmdCommandSource( Abc_Frame_t * pAbc, int argc, char **argv )
{
    int c, echo, prompt, silent, interactive, quit_count, lp_count;
    int status = 0;             /* initialize so that lint doesn't complain */
    int lp_file_index, did_subst;
    char *prompt_string, *real_filename, line[MAX_STR], *command;
    FILE *fp;

    interactive = silent = prompt = echo = 0;

    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "hipsx" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
            break;
        case 'i':               /* a hack to distinguish EOF from stdin */
            interactive = 1;
            break;
        case 'p':
            prompt = 1;
            break;
        case 's':
            silent = 1;
            break;
        case 'x':
            echo ^= 1;
            break;
        default:
            goto usage;
        }
    }

    /* added to avoid core-dumping when no script file is specified */
    if ( argc == util_optind )
    {
        goto usage;
    }

    lp_file_index = util_optind;
    lp_count = 0;

    /*
     * FIX (Tom, 5/7/95):  I'm not sure what the purpose of this outer do loop
     * is. In particular, lp_file_index is never modified in the loop, so it
     * looks it would just read the same file over again.  Also, SIS had
     * lp_count initialized to -1, and hence, any file sourced by SIS (if -l or
     * -t options on "source" were used in SIS) would actually be executed
     * twice.
     */
    do
    {
        lp_count++;             /* increment the loop counter */

        fp = CmdFileOpen( pAbc, argv[lp_file_index], "r", &real_filename, silent );
        if ( fp == NULL )
        {
            FREE( real_filename );
            return !silent;     /* error return if not silent */
        }

        quit_count = 0;
        do
        {
            if ( prompt )
            {
                prompt_string = Cmd_FlagReadByName( pAbc, "prompt" );
                if ( prompt_string == NULL )
                    prompt_string = "abc> ";

            }
            else
            {
                prompt_string = NIL( char );
            }

            /* clear errors -- e.g., EOF reached from stdin */
            clearerr( fp );

            /* read another command line */
//      if (CmdFgetsFilec(line, MAX_STR, fp, prompt_string) == NULL) {
//      Abc_UtilsPrintPrompt(prompt_string);
//      fflush(stdout);
            if ( fgets( line, MAX_STR, fp ) == NULL )
            {
                if ( interactive )
                {
                    if ( quit_count++ < 5 )
                    {
                        fprintf( pAbc->Err, "\nUse \"quit\" to leave ABC.\n" );
                        continue;
                    }
                    status = -1;    /* fake a 'quit' */
                }
                else
                {
                    status = 0; /* successful end of 'source' ; loop? */
                }
                break;
            }
            quit_count = 0;

            if ( echo )
            {
                fprintf( pAbc->Out, "abc - > %s", line );
            }
            command = CmdHistorySubstitution( pAbc, line, &did_subst );
            if ( command == NIL( char ) )
            {
                status = 1;
                break;
            }
            if ( did_subst )
            {
                if ( interactive )
                {
                    fprintf( pAbc->Out, "%s\n", command );
                }
            }
            if ( command != line )
            {
                ( void ) strcpy( line, command );
            }
            if ( interactive && *line != '\0' )
            {
                Cmd_HistoryAddCommand( pAbc, util_strsav(line) );
                if ( pAbc->Hst != NIL( FILE ) )
                {
                    fprintf( pAbc->Hst, "%s\n", line );
                    ( void ) fflush( pAbc->Hst );
                }
            }

            status = Cmd_CommandExecute( pAbc, line );
        }
        while ( status == 0 );

        if ( fp != stdin )
        {
            if ( status > 0 )
            {
                fprintf( pAbc->Err,
                                  "** cmd error: aborting 'source %s'\n",
                                  real_filename );
            }
            ( void ) fclose( fp );
        }
        FREE( real_filename );

    }
    while ( ( status == 0 ) && ( lp_count <= 0 ) );

    return status;

  usage:
    fprintf( pAbc->Err, "usage: source [-h] [-p] [-s] [-x] file_name\n" );
    fprintf( pAbc->Err, "\t-h     print the command usage\n" );
    fprintf( pAbc->Err, "\t-p     supply prompt before reading each line\n" );
    fprintf( pAbc->Err, "\t-s     silently ignore nonexistant file\n" );
    fprintf( pAbc->Err, "\t-x     echo each line as it is executed\n" );
    return 1;
}

/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int CmdCommandSetVariable( Abc_Frame_t * pAbc, int argc, char **argv )
{
    char *flag_value, *key, *value;
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
    if ( argc == 0 || argc > 3 )
    {
        goto usage;
    }
    else if ( argc == 1 )
    {
        CmdPrintTable( pAbc->tFlags, 0 );
        return 0;
    }
    else
    {
        key = argv[1];
        if ( st_delete( pAbc->tFlags, &key, &value ) )
        {
            FREE( key );
            FREE( value );
        }

        flag_value = argc == 2 ? util_strsav( "" ) : util_strsav( argv[2] );
//        flag_value = argc == 2 ? NULL : util_strsav(argv[2]);
        st_insert( pAbc->tFlags, util_strsav(argv[1]), flag_value );

        if ( strcmp( argv[1], "abcout" ) == 0 )
        {
            if ( pAbc->Out != stdout )
                fclose( pAbc->Out );
            if ( strcmp( flag_value, "" ) == 0 )
                flag_value = "-";
            pAbc->Out = CmdFileOpen( pAbc, flag_value, "w", NIL( char * ), 0 );
            if ( pAbc->Out == NULL )
                pAbc->Out = stdout;
#if HAVE_SETVBUF
            setvbuf( pAbc->Out, ( char * ) NULL, _IOLBF, 0 );
#endif
        }
        if ( strcmp( argv[1], "abcerr" ) == 0 )
        {
            if ( pAbc->Err != stderr )
                fclose( pAbc->Err );
            if ( strcmp( flag_value, "" ) == 0 )
                flag_value = "-";
            pAbc->Err = CmdFileOpen( pAbc, flag_value, "w", NIL( char * ), 0 );
            if ( pAbc->Err == NULL )
                pAbc->Err = stderr;
#if HAVE_SETVBUF
            setvbuf( pAbc->Err, ( char * ) NULL, _IOLBF, 0 );
#endif
        }
        if ( strcmp( argv[1], "history" ) == 0 )
        {
            if ( pAbc->Hst != NIL( FILE ) )
                fclose( pAbc->Hst );
            if ( strcmp( flag_value, "" ) == 0 )
                pAbc->Hst = NIL( FILE );
            else
            {
                pAbc->Hst = CmdFileOpen( pAbc, flag_value, "w", NIL( char * ), 0 );
                if ( pAbc->Hst == NULL )
                    pAbc->Hst = NIL( FILE );
            }
        }
        return 0;
    }

  usage:
    fprintf( pAbc->Err, "usage: set [-h] <name> <value>\n" );
    fprintf( pAbc->Err, "\t        sets the value of parameter <name>\n" );
    fprintf( pAbc->Err, "\t-h    : print the command usage\n" );
    return 1;

}

/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int CmdCommandUnsetVariable( Abc_Frame_t * pAbc, int argc, char **argv )
{
    int i;
    char *key, *value;
    int c;

    util_getopt_reset();
    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
            break;
        default:
            goto usage;
        }
    }

    if ( argc < 2 )
    {
        goto usage;
    }

    for ( i = 1; i < argc; i++ )
    {
        key = argv[i];
        if ( st_delete( pAbc->tFlags, &key, &value ) )
        {
            FREE( key );
            FREE( value );
        }
    }
    return 0;


  usage:
    fprintf( pAbc->Err, "usage: unset [-h] <name> \n" );
    fprintf( pAbc->Err, "\t        removes the value of parameter <name>\n" );
    fprintf( pAbc->Err, "\t-h    : print the command usage\n" );
    return 1;
}

/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int CmdCommandUndo( Abc_Frame_t * pAbc, int argc, char **argv )
{
    if ( pAbc->pNtkCur == NULL )
    {
        fprintf( pAbc->Out, "Empty network.\n" );
        return 0;
    }

    // if there are no arguments on the command line
    // set the current network to be the network from the previous step
    if ( argc == 1 ) 
        return CmdCommandRecall( pAbc, argc, argv );

    fprintf( pAbc->Err, "usage: undo\n" );
    fprintf( pAbc->Err, "         sets the current network to be the previously saved network\n" );
    return 1;

}

/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int CmdCommandRecall( Abc_Frame_t * pAbc, int argc, char **argv )
{
    Abc_Ntk_t * pNtk;
    int iStep, iStepFound;
    int nNetsToSave, c;
    char * pValue;
    int iStepStart, iStepStop;

    if ( pAbc->pNtkCur == NULL )
    {
        fprintf( pAbc->Out, "Empty network.\n" );
        return 0;
    }

    
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
 
    // get the number of networks to save
    pValue = Cmd_FlagReadByName( pAbc, "savesteps" );
    // if the value of steps to save is not set, assume 1-level undo
    if ( pValue == NULL )
        nNetsToSave = 1;
    else 
        nNetsToSave = atoi(pValue);

    // if there are no arguments on the command line
    // set the current network to be the network from the previous step
    if ( argc == 1 ) 
    {
        // get the previously saved network
        pNtk = Abc_NtkBackup(pAbc->pNtkCur);
        if ( pNtk == NULL )
            fprintf( pAbc->Out, "There is no previously saved network.\n" );
        else // set the current network to be the copy of the previous one
            Abc_FrameSetCurrentNetwork( pAbc, Abc_NtkDup(pNtk) );
         return 0;
    }
    if ( argc == 2 ) // the second argument is the number of the step to return to
    {
        // read the number of the step to return to
        iStep = atoi(argv[1]);
        // check whether it is reasonable
        if ( iStep >= pAbc->nSteps )
        {
            iStepStart = pAbc->nSteps - nNetsToSave;
            if ( iStepStart <= 0 )
                iStepStart = 1;
            iStepStop  = pAbc->nSteps;
            if ( iStepStop <= 0 )
                iStepStop = 1;
            if ( iStepStart == iStepStop )
                fprintf( pAbc->Out, "Can only recall step %d.\n", iStepStop );
            else
                fprintf( pAbc->Out, "Can only recall steps %d-%d.\n", iStepStart, iStepStop );
        }
        else if ( iStep < 0 )
            fprintf( pAbc->Out, "Cannot recall step %d.\n", iStep );
        else if ( iStep == 0 )
            Abc_FrameDeleteAllNetworks( pAbc );
        else 
        {
            // scroll backward through the list of networks
            // to determine if such a network exist
            iStepFound = 0;
            for ( pNtk = pAbc->pNtkCur; pNtk; pNtk = Abc_NtkBackup(pNtk) )
                if ( (iStepFound = Abc_NtkStep(pNtk)) == iStep ) 
                    break;
            if ( pNtk == NULL )
            {
                iStepStart = iStepFound;
                if ( iStepStart <= 0 )
                    iStepStart = 1;
                iStepStop  = pAbc->nSteps;
                if ( iStepStop <= 0 )
                    iStepStop = 1;
                if ( iStepStart == iStepStop )
                    fprintf( pAbc->Out, "Can only recall step %d.\n", iStepStop );
                else
                    fprintf( pAbc->Out, "Can only recall steps %d-%d.\n", iStepStart, iStepStop );
            }
            else
                Abc_FrameSetCurrentNetwork( pAbc, Abc_NtkDup(pNtk) );
        }
        return 0;
    }

usage:

    fprintf( pAbc->Err, "usage: recall -h <num>\n" );
    fprintf( pAbc->Err, "         set the current network to be one of the previous networks\n" );
    fprintf( pAbc->Err, "<num> :  level to return to [default = previous]\n" );
    fprintf( pAbc->Err, "   -h :  print the command usage\n");
    return 1;
}


/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int CmdCommandEmpty( Abc_Frame_t * pAbc, int argc, char **argv )
{
    int c;

    if ( pAbc->pNtkCur == NULL )
    {
        fprintf( pAbc->Out, "Empty network.\n" );
        return 0;
    }

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
 
    Abc_FrameDeleteAllNetworks( pAbc );
    Abc_FrameRestart( pAbc );
    return 0;
usage:

    fprintf( pAbc->Err, "usage: empty [-h]\n" );
    fprintf( pAbc->Err, "         removes all the currently stored networks\n" );
    fprintf( pAbc->Err, "   -h :  print the command usage\n");
    return 1;
}


#if 0

/**Function********************************************************************

  Synopsis    [Donald's version.]

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int CmdCommandUndo( Abc_Frame_t * pAbc, int argc, char **argv )
{
    Abc_Ntk_t * pNtkTemp;
    int id, c;

    while ( ( c = util_getopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
            break;
        default:
            goto usage;
        }
    }
    if (util_optind <= argc) {
    pNtkTemp = pAbc->pNtk;
    pAbc->pNtk = pAbc->pNtkSaved;
    pAbc->pNtkSaved = pNtkTemp;
    }
    id = atoi(argv[util_optind]);
    pNtkTemp = Cmd_HistoryGetSnapshot(pAbc, id);
    if (!pNtkTemp) 
    fprintf( pAbc->Err, "Snapshot %d does not exist\n", id);
    else
    pAbc->pNtk = Abc_NtkDup(pNtkTemp, Abc_NtkMan(pNtkTemp));

    return 0;
usage:
    fprintf( pAbc->Err, "usage: undo\n" );
    fprintf( pAbc->Err, "       swaps the current network and the backup network\n" );
    return 1;
}

#endif


#ifdef WIN32
/**Function*************************************************************

  Synopsis    [Command to print the contents of the current directory (Windows).]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
#include <io.h>

// these structures are defined in <io.h> but are for some reason invisible
typedef unsigned long _fsize_t; // Could be 64 bits for Win32

struct _finddata_t {
    unsigned    attrib;
    time_t      time_create;    // -1 for FAT file systems 
    time_t      time_access;    // -1 for FAT file systems 
    time_t      time_write;
    _fsize_t    size;
    char        name[260];
};

extern long _findfirst( char *filespec, struct _finddata_t *fileinfo );
extern int  _findnext( long handle, struct _finddata_t *fileinfo );
extern int  _findclose( long handle );

int CmdCommandLs( Abc_Frame_t * pAbc, int argc, char **argv )
{
    struct _finddata_t c_file;
    long   hFile;
    int    fLong = 0;
    int    fOnlyBLIF = 0;
    char   Buffer[25];
    int    Counter = 0;
    int    fPrintedNewLine;
    char   c;

    util_getopt_reset();
    while ( (c = util_getopt(argc, argv, "lb") ) != EOF )
    {
        switch (c)
        {
            case 'l':
              fLong = 1;
              break;
            case 'b':
              fOnlyBLIF = 1;
              break;
            default:
              goto usage;
        }
    }

    // find first .mv file in current directory
    if( (hFile = _findfirst( ((fOnlyBLIF)? "*.mv": "*.*"), &c_file )) == -1L )
    {
        if ( fOnlyBLIF )
            fprintf( pAbc->Out, "No *.mv files in the current directory.\n" );
        else
            fprintf( pAbc->Out, "No files in the current directory.\n" );
    }
    else
    {
        if ( fLong )
        {
            fprintf( pAbc->Out, " File              Date           Size |  File             Date           Size \n" );
            fprintf( pAbc->Out, " ----------------------------------------------------------------------------- \n" );
            do
            {
                strcpy( Buffer, ctime( &(c_file.time_write) ) );
                Buffer[16] = 0;
                fprintf( pAbc->Out, " %-17s %.24s%7ld", c_file.name, Buffer+4, c_file.size );
                if ( ++Counter % 2 == 0 )
                {
                    fprintf( pAbc->Out, "\n" );
                    fPrintedNewLine = 1;
                }
                else
                {
                    fprintf( pAbc->Out, " |" );
                    fPrintedNewLine = 0;
                }
            }
            while( _findnext( hFile, &c_file ) == 0 );
        }
        else
        {
            do
            {
                fprintf( pAbc->Out, " %-18s", c_file.name );
                if ( ++Counter % 4 == 0 )
                {
                    fprintf( pAbc->Out, "\n" );
                    fPrintedNewLine = 1;
                }
                else
                {
                    fprintf( pAbc->Out, " " );
                    fPrintedNewLine = 0;
                }
            }
            while( _findnext( hFile, &c_file ) == 0 );
        }
        if ( !fPrintedNewLine )
            fprintf( pAbc->Out, "\n" );
        _findclose( hFile );
    }
    return 0;

usage:
    fprintf( pAbc->Err, "Usage: ls [-l] [-b]\n" );
    fprintf( pAbc->Err, "       print the file names in the current directory\n" );
    fprintf( pAbc->Err, "        -l : print in the long format [default = short]\n" );
    fprintf( pAbc->Err, "        -b : print only .mv files [default = all]\n" );
    return 1; 
}
#endif



#ifdef WIN32
#define unlink _unlink
#endif

/**Function********************************************************************

  Synopsis    [Calls SIS internally.]

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int CmdCommandSis( Abc_Frame_t * pAbc, int argc, char **argv )
{
    FILE * pFile;
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkNew, * pNetlist;
    char * pNameWin = "sis.exe";
    char * pNameUnix = "sis";
    char Command[1000], Buffer[100];
    char * pSisName;
    int i;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    if ( pNtk == NULL )
    {
        fprintf( pErr, "Empty network.\n" );
        goto usage;
    }

    if ( strcmp( argv[0], "sis" ) != 0 )
    {
        fprintf( pErr, "Wrong command: \"%s\".\n", argv[0] );
        goto usage;
    }

    if ( argc == 1 )
        goto usage;
    if ( strcmp( argv[1], "-h" ) == 0 )
        goto usage;
    if ( strcmp( argv[1], "-?" ) == 0 )
        goto usage;

    // get the names from the resource file
    if ( Cmd_FlagReadByName(pAbc, "siswin") )
        pNameWin = Cmd_FlagReadByName(pAbc, "siswin");
    if ( Cmd_FlagReadByName(pAbc, "sisunix") )
        pNameUnix = Cmd_FlagReadByName(pAbc, "sisunix");

    // check if SIS is available
    if ( (pFile = fopen( pNameWin, "r" )) )
        pSisName = pNameWin;
    else if ( (pFile = fopen( pNameUnix, "r" )) )
        pSisName = pNameUnix;
    else if ( pFile == NULL )
    {
        fprintf( pErr, "Cannot find \"%s\" or \"%s\" in the current directory.\n", pNameWin, pNameUnix );
        goto usage;
    }
    fclose( pFile );

    // write out the current network
    pNetlist = Abc_NtkLogicToNetlist(pNtk);
    Io_WriteBlif( pNetlist, "_sis_in.blif", 1 );
    Abc_NtkDelete( pNetlist );

    // create the file for sis
    sprintf( Command, "%s -x -c ", pSisName );
    strcat ( Command, "\"" );
    strcat ( Command, "read_blif _sis_in.blif" );
    strcat ( Command, "; " );
    for ( i = 1; i < argc; i++ )
    {
        sprintf( Buffer, " %s", argv[i] );
        strcat( Command, Buffer );
    }
    strcat( Command, "; " );
    strcat( Command, "write_blif _sis_out.blif" );
    strcat( Command, "\"" );

    // call SIS
    if ( system( Command ) )
    {
        fprintf( pErr, "The following command has returned non-zero exit status:\n" );
        fprintf( pErr, "\"%s\"\n", Command );
        unlink( "_sis_in.blif" );
        goto usage;
    }

    // read in the SIS output
    if ( (pFile = fopen( "_sis_out.blif", "r" )) == NULL )
    {
        fprintf( pErr, "Cannot open SIS output file \"%s\".\n", "_sis_out.blif" );
        unlink( "_sis_in.blif" );
        goto usage;
    }
    fclose( pFile );

    // set the new network
    pNtkNew = Io_Read( "_sis_out.blif", 1 );
    // set the original spec of the new network
    if ( pNtk->pSpec )
    {
        FREE( pNtkNew->pSpec );
        pNtkNew->pSpec = util_strsav( pNtk->pSpec );
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkNew );

    // remove temporary networks
    unlink( "_sis_in.blif" );
    unlink( "_sis_out.blif" );
    return 0;

usage:
    fprintf( pErr, "\n" );
    fprintf( pErr, "Usage: sis [-h] <com>\n");
    fprintf( pErr, "         invokes SIS command for the current ABC network\n" );
    fprintf( pErr, "         (the executable of SIS should be in the same directory)\n" );
    fprintf( pErr, "   -h  : print the command usage\n" );
    fprintf( pErr, " <com> : a SIS command (or a semicolon-separated list of commands in quotes)\n" );
    fprintf( pErr, "         Example 1: sis eliminate 0\n" );
    fprintf( pErr, "         Example 2: sis \"ps; rd; fx; ps\"\n" );
    fprintf( pErr, "         Example 3: sis source script.rugged\n" );
    return 1;                    // error exit 
}


/**Function********************************************************************

  Synopsis    [Calls SIS internally.]

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int CmdCommandMvsis( Abc_Frame_t * pAbc, int argc, char **argv )
{
    FILE * pFile;
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkNew, * pNetlist;
    char Command[1000], Buffer[100];
    char * pNameWin = "mvsis.exe";
    char * pNameUnix = "mvsis";
    char * pMvsisName;
    int i;

    pNtk = Abc_FrameReadNet(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    if ( pNtk == NULL )
    {
        fprintf( pErr, "Empty network.\n" );
        goto usage;
    }

    if ( strcmp( argv[0], "mvsis" ) != 0 )
    {
        fprintf( pErr, "Wrong command: \"%s\".\n", argv[0] );
        goto usage;
    }

    if ( argc == 1 )
        goto usage;
    if ( strcmp( argv[1], "-h" ) == 0 )
        goto usage;
    if ( strcmp( argv[1], "-?" ) == 0 )
        goto usage;

    // get the names from the resource file
    if ( Cmd_FlagReadByName(pAbc, "mvsiswin") )
        pNameWin = Cmd_FlagReadByName(pAbc, "mvsiswin");
    if ( Cmd_FlagReadByName(pAbc, "mvsisunix") )
        pNameUnix = Cmd_FlagReadByName(pAbc, "mvsisunix");

    // check if MVSIS is available
    if ( (pFile = fopen( pNameWin, "r" )) )
        pMvsisName = pNameWin;
    else if ( (pFile = fopen( pNameUnix, "r" )) )
        pMvsisName = pNameUnix;
    else if ( pFile == NULL )
    {
        fprintf( pErr, "Cannot find \"%s\" or \"%s\" in the current directory.\n", pNameWin, pNameUnix );
        goto usage;
    }
    fclose( pFile );


    // write out the current network
    pNetlist = Abc_NtkLogicToNetlist(pNtk);
    Io_WriteBlif( pNetlist, "_mvsis_in.blif", 1 );
    Abc_NtkDelete( pNetlist );

    // create the file for MVSIS
    sprintf( Command, "%s -x -c ", pMvsisName );
    strcat ( Command, "\"" );
    strcat ( Command, "read_blif _mvsis_in.blif" );
    strcat ( Command, "; " );
    for ( i = 1; i < argc; i++ )
    {
        sprintf( Buffer, " %s", argv[i] );
        strcat( Command, Buffer );
    }
    strcat( Command, "; " );
    strcat( Command, "write_blif _mvsis_out.blif" );
    strcat( Command, "\"" );

    // call MVSIS
    if ( system( Command ) )
    {
        fprintf( pErr, "The following command has returned non-zero exit status:\n" );
        fprintf( pErr, "\"%s\"\n", Command );
        unlink( "_mvsis_in.blif" );
        goto usage;
    }

    // read in the MVSIS output
    if ( (pFile = fopen( "_mvsis_out.blif", "r" )) == NULL )
    {
        fprintf( pErr, "Cannot open MVSIS output file \"%s\".\n", "_mvsis_out.blif" );
        unlink( "_mvsis_in.blif" );
        goto usage;
    }
    fclose( pFile );

    // set the new network
    pNtkNew = Io_Read( "_mvsis_out.blif", 1 );
    // set the original spec of the new network
    if ( pNtk->pSpec )
    {
        FREE( pNtkNew->pSpec );
        pNtkNew->pSpec = util_strsav( pNtk->pSpec );
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkNew );

    // remove temporary networks
    unlink( "_mvsis_in.blif" );
    unlink( "_mvsis_out.blif" );
    return 0;

usage:
    fprintf( pErr, "\n" );
    fprintf( pErr, "Usage: mvsis [-h] <com>\n");
    fprintf( pErr, "         invokes MVSIS command for the current ABC network\n" );
    fprintf( pErr, "         (the executable of MVSIS should be in the same directory)\n" );
    fprintf( pErr, "   -h  : print the command usage\n" );
    fprintf( pErr, " <com> : a MVSIS command (or a semicolon-separated list of commands in quotes)\n" );
    fprintf( pErr, "         Example 1: mvsis fraig_sweep\n" );
    fprintf( pErr, "         Example 2: mvsis \"ps; fxu; ps\"\n" );
    fprintf( pErr, "         Example 3: mvsis source mvsis.rugged\n" );
    return 1;                    // error exit 
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


