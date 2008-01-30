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

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int TypeCheck( Abc_Frame_t * pAbc, char * s);

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

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
#ifdef _DEBUG
    _CrtSetDbgFlag( _CRTDBG_ALLOC_MEM_DF | _CRTDBG_LEAK_CHECK_DF );
#endif

    // get global frame (singleton pattern)
    // will be initialized on first call
    pAbc = Abc_FrameGetGlobalFrame();

    // default options
    fBatch = 0;
    fInitSource = 1;
    fInitRead   = 0;
    fFinalWrite = 0;
    sInFile = sOutFile = NULL;
    sprintf( sReadCmd,  "read_blif_mv"  );
    sprintf( sWriteCmd, "write_blif_mv" );
    
    util_getopt_reset();
    while ((c = util_getopt(argc, argv, "c:hf:F:o:st:T:x")) != EOF) {
        switch(c) {
            case 'c':
                strcpy( sCommandUsr, util_optarg );
                fBatch = 1;
                break;
                
            case 'f':
                sprintf(sCommandUsr, "source %s", util_optarg);
                fBatch = 1;
                break;

            case 'F':
                sprintf(sCommandUsr, "source -x %s", util_optarg);
                fBatch = 1;
                break;
                
            case 'h':
                goto usage;
                break;
                
            case 'o':
                sOutFile = util_optarg;
                fFinalWrite = 1;
                break;
                
            case 's':
                fInitSource = 0;
                break;
                
            case 't':
                if ( TypeCheck( pAbc, util_optarg ) )
                {
                    if ( !strcmp(util_optarg, "none") == 0 )
                    {
                        fInitRead = 1;
                        sprintf( sReadCmd, "read_%s", util_optarg );
                    }
                }
                else {
                    goto usage;
                }
                fBatch = 1;
                break;
                
            case 'T':
                if ( TypeCheck( pAbc, util_optarg ) )
                {
                    if (!strcmp(util_optarg, "none") == 0)
                    {
                        fFinalWrite = 1;
                        sprintf( sWriteCmd, "write_%s", util_optarg);
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

        if (argc - util_optind == 0)
        {
            sInFile = NULL;
        }
        else if (argc - util_optind == 1)
        {
            fInitRead = 1;
            sInFile = argv[util_optind];
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
    if ( fStatus == -2 ) 
    {
        // perform uninitializations
        Abc_FrameEnd( pAbc );
        // stop the framework
        Abc_FrameDeallocate( pAbc );
    }
    return 0;

usage:
    Abc_UtilsPrintHello( pAbc );
    Abc_UtilsPrintUsage( pAbc, argv[0] );
    return 1;
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

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


