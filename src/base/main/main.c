/**CFile****************************************************************

  FileName    [main.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [The main package.]

  Synopsis    [Here everything starts.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: main.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "mainInt.h"

// this line should be included in the library project
//#define ABC_LIB

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int TypeCheck( Abc_Frame_t * pAbc, char * s);

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

#ifndef ABC_LIB

/**Function*************************************************************

  Synopsis    [The main() procedure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int main( int argc, char * argv[] )
{
    Abc_Frame_t * pAbc;
    char sCommandUsr[500], sCommandTmp[100], sReadCmd[20], sWriteCmd[20], c;
    char * sCommand, * sOutFile, * sInFile;
    int  fStatus = 0;
    bool fBatch, fInitSource, fInitRead, fFinalWrite;

    // added to detect memory leaks:
#if defined(_DEBUG) && defined(_MSC_VER) 
    _CrtSetDbgFlag( _CRTDBG_ALLOC_MEM_DF | _CRTDBG_LEAK_CHECK_DF );
#endif
    
//    Npn_Experiment();
//    Npn_Generate();

    // get global frame (singleton pattern)
    // will be initialized on first call
    pAbc = Abc_FrameGetGlobalFrame();

    // default options
    fBatch = 0;
    fInitSource = 1;
    fInitRead   = 0;
    fFinalWrite = 0;
    sInFile = sOutFile = NULL;
    sprintf( sReadCmd,  "read"  );
    sprintf( sWriteCmd, "write" );
    
    Extra_UtilGetoptReset();
    while ((c = Extra_UtilGetopt(argc, argv, "c:hf:F:o:st:T:x")) != EOF) {
        switch(c) {
            case 'c':
                strcpy( sCommandUsr, globalUtilOptarg );
                fBatch = 1;
                break;
                
            case 'f':
                sprintf(sCommandUsr, "source %s", globalUtilOptarg);
                fBatch = 1;
                break;

            case 'F':
                sprintf(sCommandUsr, "source -x %s", globalUtilOptarg);
                fBatch = 1;
                break;
                
            case 'h':
                goto usage;
                break;
                
            case 'o':
                sOutFile = globalUtilOptarg;
                fFinalWrite = 1;
                break;
                
            case 's':
                fInitSource = 0;
                break;
                
            case 't':
                if ( TypeCheck( pAbc, globalUtilOptarg ) )
                {
                    if ( !strcmp(globalUtilOptarg, "none") == 0 )
                    {
                        fInitRead = 1;
                        sprintf( sReadCmd, "read_%s", globalUtilOptarg );
                    }
                }
                else {
                    goto usage;
                }
                fBatch = 1;
                break;
                
            case 'T':
                if ( TypeCheck( pAbc, globalUtilOptarg ) )
                {
                    if (!strcmp(globalUtilOptarg, "none") == 0)
                    {
                        fFinalWrite = 1;
                        sprintf( sWriteCmd, "write_%s", globalUtilOptarg);
                    }
                }
                else {
                    goto usage;
                }
                fBatch = 1;
                break;
                
            case 'x':
                fFinalWrite = 0;
                fInitRead   = 0;
                fBatch = 1;
                break;
                
            default:
                goto usage;
        }
    }
    
    if ( fBatch )
    {
        pAbc->fBatchMode = 1;

        if (argc - globalUtilOptind == 0)
        {
            sInFile = NULL;
        }
        else if (argc - globalUtilOptind == 1)
        {
            fInitRead = 1;
            sInFile = argv[globalUtilOptind];
        }
        else
        {
            Abc_UtilsPrintUsage( pAbc, argv[0] );
        }
        
        // source the resource file
        if ( fInitSource )
        {
            Abc_UtilsSource( pAbc );
        }
        
        fStatus = 0;
        if ( fInitRead && sInFile )
        {
            sprintf( sCommandTmp, "%s %s", sReadCmd, sInFile );
            fStatus = Cmd_CommandExecute( pAbc, sCommandTmp );
        }
        
        if ( fStatus == 0 )
        {
            /* cmd line contains `source <file>' */
            fStatus = Cmd_CommandExecute( pAbc, sCommandUsr );
            if ( (fStatus == 0 || fStatus == -1) && fFinalWrite && sOutFile )
            {
                sprintf( sCommandTmp, "%s %s", sWriteCmd, sOutFile );
                fStatus = Cmd_CommandExecute( pAbc, sCommandTmp );
            }
        }
        
    }
    else 
    {
        // start interactive mode
        // print the hello line
        Abc_UtilsPrintHello( pAbc );
        
        // source the resource file
        if ( fInitSource )
        {
            Abc_UtilsSource( pAbc );
        }
                
        // execute commands given by the user
        while ( !feof(stdin) )
        {
            // print command line prompt and
            // get the command from the user
            sCommand = Abc_UtilsGetUsersInput( pAbc );
            
            // execute the user's command
            fStatus = Cmd_CommandExecute( pAbc, sCommand );
            
            // stop if the user quitted or an error occurred
            if ( fStatus == -1 || fStatus == -2 )
                break;
        }
    } 
     
    // if the memory should be freed, quit packages
    if ( fStatus < 0 ) 
    {
        Abc_Stop(); 
    }    
    return 0;  

usage:
    Abc_UtilsPrintHello( pAbc );
    Abc_UtilsPrintUsage( pAbc, argv[0] );
    return 1;
}

#endif

/**Function*************************************************************

  Synopsis    [Initialization procedure for the library project.]

  Description [Note that when Abc_Start() is run in a static library
  project, it does not load the resource file by default. As a result, 
  ABC is not set up the same way, as when it is run on a command line. 
  For example, some error messages while parsing files will not be 
  produced, and intermediate networks will not be checked for consistancy. 
  One possibility is to load the resource file after Abc_Start() as follows:
  Abc_UtilsSource(  Abc_FrameGetGlobalFrame() );]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_Start()
{
    Abc_Frame_t * pAbc;
    // added to detect memory leaks:
#if defined(_DEBUG) && defined(_MSC_VER) 
    _CrtSetDbgFlag( _CRTDBG_ALLOC_MEM_DF | _CRTDBG_LEAK_CHECK_DF );
#endif
    // start the glocal frame
    pAbc = Abc_FrameGetGlobalFrame();
    // source the resource file
//    Abc_UtilsSource( pAbc );
}

/**Function*************************************************************

  Synopsis    [Deallocation procedure for the library project.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_Stop()
{
    Abc_Frame_t * pAbc;
    pAbc = Abc_FrameGetGlobalFrame();
    // perform uninitializations
    Abc_FrameEnd( pAbc );
    // stop the framework
    Abc_FrameDeallocate( pAbc );
}

/**Function********************************************************************

  Synopsis    [Returns 1 if s is a file type recognized, else returns 0.]

  Description [Returns 1 if s is a file type recognized by ABC, else returns 0. 
  Recognized types are "blif", "bench", "pla", and "none".]

  SideEffects []

******************************************************************************/
static int TypeCheck( Abc_Frame_t * pAbc, char * s )
{
    if (strcmp(s, "blif") == 0)
        return 1;
    else if (strcmp(s, "bench") == 0)
        return 1;
    else if (strcmp(s, "pla") == 0)
        return 1;
    else if (strcmp(s, "none") == 0)
        return 1;
    else {
        fprintf( pAbc->Err, "unknown type %s\n", s );
        return 0;
    }
}




/**Function*************************************************************

  Synopsis    [Find the file name.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_MainFileName( char * pFileName )
{
    static char Buffer[200];
    char * pExtension;
    assert( strlen(pFileName) < 190 );
    pExtension = Extra_FileNameExtension( pFileName );
    if ( pExtension == NULL )
        sprintf( Buffer, "%s.opt", pFileName );
    else
    {
        strncpy( Buffer, pFileName, pExtension-pFileName-1 );
        sprintf( Buffer+(pExtension-pFileName-1), ".opt.%s", pExtension );
    }
    return Buffer;
}

/**Function*************************************************************

  Synopsis    [The main() procedure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int main_( int argc, char * argv[] )
{
    extern void Nwk_ManPrintStatsUpdate( void * p, void * pAig, void * pNtk,
         int nRegInit, int nLutInit, int nLevInit, int Time );
    char * pComs[20] = 
    {
/*00*/  "*r -am ",
/*01*/  "*w -abc 1.aig",
/*02*/  "*lcorr -nc",//; *ps",
/*03*/  "*scorr -nc",//; *ps",
/*04*/  "*dch; *if -K 4 -C 16 -F 3 -A 2; *sw -m",//; *ps",
/*05*/  "*dch; *if -K 4 -C 16 -F 3 -A 2; *sw -m",//; *ps", 
/*06*/  "*w ",
/*07*/  "*w -abc 2.aig",
/*08*/  "miter -mc 1.aig 2.aig; sim -F 4 -W 4 -mv"
    };
    char Command[1000];
    int i, nComs;
    Abc_Frame_t * pAbc;
    FILE * pFile;
    int nRegInit, nLutInit, nLevInit;
    int clkStart = clock();

    // added to detect memory leaks:
#if defined(_DEBUG) && defined(_MSC_VER) 
    _CrtSetDbgFlag( _CRTDBG_ALLOC_MEM_DF | _CRTDBG_LEAK_CHECK_DF );
#endif

    // check that the file is present
    if ( argc != 2 )
    {
        printf( "Expecting one command argument (file name).\n" );
        return 0;
    }
    pFile = fopen( argv[1], "r" );
    if ( pFile == NULL )
    {
        printf( "Cannot open file \"%s\".\n", argv[1] );
        return 0;
    }
    fclose( pFile );

    // count the number of commands
    for ( nComs = 0; nComs < 20; nComs++ )
        if ( pComs[nComs] == NULL )
            break;
    // perform the commands
    printf( "Reading design \"%s\"...\n", argv[1] );
    pAbc = Abc_FrameGetGlobalFrame();
    for ( i = 0; i < nComs; i++ )
    {

        if ( i == 0 )
            sprintf( Command, "%s%s", pComs[i], argv[1] );
        else if ( i == 6 )
            sprintf( Command, "%s%s", pComs[i], Abc_MainFileName(argv[1]) );
        else 
            sprintf( Command, "%s", pComs[i] );
        if ( Cmd_CommandExecute( pAbc, Command ) )
        {
            printf( "Internal command %d failed.\n", i );
            return 0;
        }
        if ( i == 0 )
        {
            extern int Nwk_ManStatsRegs( void * p );
            extern int Nwk_ManStatsLuts( void * pNtk );
            extern int Nwk_ManStatsLevs( void * pNtk );
            nRegInit = Nwk_ManStatsRegs( pAbc->pAbc8Ntl );
            nLutInit = Nwk_ManStatsLuts( pAbc->pAbc8Nwk );
            nLevInit = Nwk_ManStatsLevs( pAbc->pAbc8Nwk );
        }
        if ( i >= 1 && i <= 5 )
        Nwk_ManPrintStatsUpdate( pAbc->pAbc8Ntl, pAbc->pAbc8Aig, pAbc->pAbc8Nwk, 
            nRegInit, nLutInit, nLevInit, clkStart );
    }
    Abc_Stop(); 
    printf( "Writing optimized design \"%s\"...\n", Abc_MainFileName(argv[1]) );
    ABC_PRT( "Total time", clock() - clkStart );
    printf( "\n" );
    return 0;  
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


