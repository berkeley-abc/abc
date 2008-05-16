/**CFile****************************************************************

  FileName    [mainInt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [The main package.]

  Synopsis    [Internal declarations of the main package.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: mainInt.h,v 1.1 2008/05/14 22:13:13 wudenni Exp $]

***********************************************************************/

#ifndef __MAIN_INT_H__
#define __MAIN_INT_H__
 
////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "main.h"
#include "port_type.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

// the current version
#define ABC_VERSION "UC Berkeley, ABC 1.01"

// the maximum length of an input line 
#define MAX_STR     32768

////////////////////////////////////////////////////////////////////////
///                    STRUCTURE DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

struct Abc_Frame_t_
{
    // general info
    char *          sVersion;    // the name of the current version
    // commands, aliases, etc
    st_table *      tCommands;   // the command table
    st_table *      tAliases;    // the alias table
    st_table *      tFlags;      // the flag table
    Vec_Ptr_t *     aHistory;    // the command history
    // the functionality
    Abc_Ntk_t *     pNtkCur;     // the current network
    int             nSteps;      // the counter of different network processed
    int             fAutoexac;   // marks the autoexec mode
    int                fBatchMode;     // are we invoked in batch mode?
    // output streams
    FILE *          Out;
    FILE *          Err;
    FILE *          Hst;
    // used for runtime measurement
    double          TimeCommand; // the runtime of the last command
    double          TimeTotal;   // the total runtime of all commands
    // temporary storage for structural choices
    Vec_Ptr_t *     vStore;      // networks to be used by choice
    // decomposition package
    void *          pManDec;     // decomposition manager
    DdManager *     dd;          // temporary BDD package
    // libraries for mapping
    void *          pLibLut;     // the current LUT library
    void *          pLibGen;     // the current genlib
    void *          pLibSuper;   // the current supergate library
    void *          pLibVer;     // the current Verilog library

    // new code
    void *          pAbc8Ntl;    // the current design
    void *          pAbc8Nwk;    // the current mapped network
    void *          pAbc8Aig;    // the current AIG
    void *          pAbc8Lib;    // the current LUT library
};

////////////////////////////////////////////////////////////////////////
///                       GLOBAL VARIABLES                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                       MACRO DEFINITIONS                          ///
////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////
#ifdef WIN32
#define DLLEXPORT __declspec(dllexport)
#define DLLIMPORT __declspec(dllimport)
#else  /* defined(WIN32) */
#define DLLIMPORT
#endif /* defined(WIN32) */

#ifndef ABC_DLL
#define ABC_DLL DLLIMPORT
#endif

/*=== mvMain.c ===========================================================*/
extern ABC_DLL int             main( int argc, char * argv[] );
/*=== mvInit.c ===================================================*/
extern ABC_DLL void            Abc_FrameInit( Abc_Frame_t * pAbc );
extern ABC_DLL void            Abc_FrameEnd( Abc_Frame_t * pAbc );
/*=== mvFrame.c =====================================================*/
extern ABC_DLL Abc_Frame_t *   Abc_FrameAllocate();
extern ABC_DLL void            Abc_FrameDeallocate( Abc_Frame_t * p );
/*=== mvUtils.c =====================================================*/
extern ABC_DLL char *          Abc_UtilsGetVersion( Abc_Frame_t * pAbc );
extern ABC_DLL char *          Abc_UtilsGetUsersInput( Abc_Frame_t * pAbc );
extern ABC_DLL void            Abc_UtilsPrintHello( Abc_Frame_t * pAbc );
extern ABC_DLL void            Abc_UtilsPrintUsage( Abc_Frame_t * pAbc, char * ProgName );
extern ABC_DLL void            Abc_UtilsSource( Abc_Frame_t * pAbc );

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
