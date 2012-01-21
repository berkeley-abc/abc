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

#ifndef ABC__base__main__mainInt_h
#define ABC__base__main__mainInt_h

 
////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "main.h"
#include "src/misc/tim/tim.h"
#include "src/map/if/if.h"
#include "src/aig/aig/aig.h"
#include "src/aig/gia/gia.h"
#include "src/proof/ssw/ssw.h"
#include "src/proof/fra/fra.h"
//#include "src/aig/nwk/nwkMerge.h"
//#include "src/aig/ntl/ntlnwk.h"
#include "src/misc/ext/ext.h"
#include "src/misc/extra/extraBdd.h"

ABC_NAMESPACE_HEADER_START

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
    Abc_Ntk_t *     pNtkCur;       // the current network
    Abc_Ntk_t *     pNtkBestDelay; // the current network
    Abc_Ntk_t *     pNtkBestArea;  // the current network
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
    void *          pLibGen2;    // the current genlib
    void *          pLibSuper;   // the current supergate library
    void *          pLibVer;     // the current Verilog library

    // new code
    Gia_Man_t *     pGia;
    Gia_Man_t *     pGia2;
    Abc_Cex_t *     pCex; 
    Vec_Ptr_t *     vCexVec;

    void *          pSave1; 
    void *          pSave2; 
    void *          pSave3; 
    void *          pSave4; 

    // related to LTL
    Vec_Ptr_t *     vLTLProperties_global;

    // the addition to keep the best Ntl that can be used to restore
    void *            pAbc8NtlBestDelay;    // the best delay, Ntl
    void *            pAbc8NtlBestArea;    // the best area
    int             Status;             // the status of verification problem (proved=1, disproved=0, undecided=-1)
    int             nFrames;            // the number of time frames completed by BMC

    Vec_Ptr_t *     vPlugInComBinPairs; // pairs of command and its binary name

    EXT_ABC_FRAME                // plugin for external functionality
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



ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
