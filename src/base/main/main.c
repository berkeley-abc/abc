/*////////////////////////////////////////////////////////////////////////////

ABC: System for Sequential Synthesis and Verification

http://www.eecs.berkeley.edu/~alanmi/abc/

Copyright (c) The Regents of the University of California. All rights reserved.

Permission is hereby granted, without written agreement and without license or
royalty fees, to use, copy, modify, and distribute this software and its
documentation for any purpose, provided that the above copyright notice and
the following two paragraphs appear in all copies of this software.

IN NO EVENT SHALL THE UNIVERSITY OF CALIFORNIA BE LIABLE TO ANY PARTY FOR
DIRECT, INDIRECT, SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES ARISING OUT OF
THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN IF THE UNIVERSITY OF
CALIFORNIA HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

THE UNIVERSITY OF CALIFORNIA SPECIFICALLY DISCLAIMS ANY WARRANTIES, INCLUDING,
BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE. THE SOFTWARE PROVIDED HEREUNDER IS ON AN "AS IS" BASIS,
AND THE UNIVERSITY OF CALIFORNIA HAS NO OBLIGATION TO PROVIDE MAINTENANCE,
SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONS.

////////////////////////////////////////////////////////////////////////////*/

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


#ifdef ABC_PYTHON_EMBED
#include <Python.h>
#endif /* ABC_PYTHON_EMBED */

#include "base/abc/abc.h"
#include "mainInt.h"

ABC_NAMESPACE_IMPL_START

// this line should be included in the library project
//#define ABC_LIB

//#define ABC_USE_BINARY 1

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int TypeCheck( Abc_Frame_t * pAbc, const char * s);

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
int Abc_RealMain( int argc, char * argv[] )
{
    Abc_Frame_t * pAbc;
    char sCommandUsr[500] = {0}, sCommandTmp[100], sReadCmd[20], sWriteCmd[20];
    const char * sOutFile, * sInFile;
    char * sCommand;
    int  fStatus = 0;
    int c, fBatch, fInitSource, fInitRead, fFinalWrite;

    // added to detect memory leaks
    // watch for {,,msvcrtd.dll}*__p__crtBreakAlloc()
    // (http://support.microsoft.com/kb/151585)
#if defined(_DEBUG) && defined(_MSC_VER)
    _CrtSetDbgFlag( _CRTDBG_ALLOC_MEM_DF | _CRTDBG_LEAK_CHECK_DF );
#endif

//    Npn_Experiment();
//    Npn_Generate();

    // get global frame (singleton pattern)
    // will be initialized on first call
    pAbc = Abc_FrameGetGlobalFrame();

#ifdef ABC_PYTHON_EMBED
    {
        PyObject* pModule;
        void init_pyabc(void);

        Py_SetProgramName(argv[0]);
        Py_NoSiteFlag = 1;
        Py_Initialize();

        init_pyabc();

        pModule = PyImport_ImportModule("pyabc");
        if (pModule)
        {
            Py_DECREF(pModule);
        }
        else
        {
            fprintf( pAbc->Err, "error: pyabc.py not found. PYTHONPATH may not be set properly.\n");
        }
    }
#endif /* ABC_PYTHON_EMBED */

    // default options
    fBatch      = 0;
    fInitSource = 1;
    fInitRead   = 0;
    fFinalWrite = 0;
    sInFile = sOutFile = NULL;
    sprintf( sReadCmd,  "read"  );
    sprintf( sWriteCmd, "write" );

    Extra_UtilGetoptReset();
    while ((c = Extra_UtilGetopt(argc, argv, "c:C:hf:F:o:st:T:xb")) != EOF) {
        switch(c) {
            case 'c':
                strcpy( sCommandUsr, globalUtilOptarg );
                fBatch = 1;
                break;

            case 'C':
                strcpy( sCommandUsr, globalUtilOptarg );
                fBatch = 2;
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

            case 'b':
                Abc_FrameSetBridgeMode();
                break;

            default:
                goto usage;
        }
    }

    if ( Abc_FrameIsBridgeMode() )
    {
        extern Gia_Man_t * Gia_ManFromBridge( FILE * pFile, Vec_Int_t ** pvInit );
        pAbc->pGia = Gia_ManFromBridge( stdin, NULL );
    }
    else if ( fBatch && sCommandUsr[0] )
        Abc_Print( 1, "ABC command line: \"%s\".\n\n", sCommandUsr );

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

        if (fBatch == 2){
            fBatch = 0;
            pAbc->fBatchMode = 0;
        }

    }

    if ( !fBatch )
    {
        // start interactive mode

        // print the hello line
        Abc_UtilsPrintHello( pAbc );
        // print history of the recent commands
        Cmd_HistoryPrint( pAbc, 10 );

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

#ifdef ABC_PYTHON_EMBED
    {
        Py_Finalize();
    }
#endif /* ABC_PYTHON_EMBED */

    // if the memory should be freed, quit packages
//    if ( fStatus < 0 ) 
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

/**Function********************************************************************

  Synopsis    [Returns 1 if s is a file type recognized, else returns 0.]

  Description [Returns 1 if s is a file type recognized by ABC, else returns 0. 
  Recognized types are "blif", "bench", "pla", and "none".]

  SideEffects []

******************************************************************************/
static int TypeCheck( Abc_Frame_t * pAbc, const char * s )
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


ABC_NAMESPACE_IMPL_END

#if defined(ABC_USE_BINARY)
int main_( int argc, char * argv[] )
#else
int main( int argc, char * argv[] )
#endif
{
  return ABC_NAMESPACE_PREFIX Abc_RealMain(argc, argv);
}
