/**CFile****************************************************************

  FileName    [main.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [The main package.]

  Synopsis    [External declarations of the main package.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: main.h,v 1.1 2008/05/14 22:13:13 wudenni Exp $]

***********************************************************************/

#ifndef __MAIN_H__
#define __MAIN_H__

#ifdef __cplusplus
extern "C" {
#endif

////////////////////////////////////////////////////////////////////////
///                         TYPEDEFS                                 ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    STRUCTURE DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

// the framework containing all data
typedef struct Abc_Frame_t_      Abc_Frame_t;   

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

// data structure packages
#include "extra.h"
#include "vec.h"
#include "st.h"

// core packages
#include "abc.h"
#include "cmd.h"
#include "ioAbc.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

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

/*=== main.c ===========================================================*/
extern ABC_DLL void            Abc_Start();
extern ABC_DLL void            Abc_Stop();

/*=== mainFrame.c ===========================================================*/
extern ABC_DLL Abc_Ntk_t *     Abc_FrameReadNtk( Abc_Frame_t * p );
extern ABC_DLL FILE *          Abc_FrameReadOut( Abc_Frame_t * p );
extern ABC_DLL FILE *          Abc_FrameReadErr( Abc_Frame_t * p );
extern ABC_DLL bool            Abc_FrameReadMode( Abc_Frame_t * p );
extern ABC_DLL bool            Abc_FrameSetMode( Abc_Frame_t * p, bool fNameMode );
extern ABC_DLL void            Abc_FrameRestart( Abc_Frame_t * p );
extern ABC_DLL bool            Abc_FrameShowProgress( Abc_Frame_t * p );

extern ABC_DLL void            Abc_FrameSetCurrentNetwork( Abc_Frame_t * p, Abc_Ntk_t * pNet );
extern ABC_DLL void            Abc_FrameSwapCurrentAndBackup( Abc_Frame_t * p );
extern ABC_DLL void            Abc_FrameReplaceCurrentNetwork( Abc_Frame_t * p, Abc_Ntk_t * pNet );
extern ABC_DLL void            Abc_FrameUnmapAllNetworks( Abc_Frame_t * p );
extern ABC_DLL void            Abc_FrameDeleteAllNetworks( Abc_Frame_t * p );

extern ABC_DLL void               Abc_FrameSetGlobalFrame( Abc_Frame_t * p );
extern ABC_DLL Abc_Frame_t *   Abc_FrameGetGlobalFrame();

extern ABC_DLL Vec_Ptr_t *     Abc_FrameReadStore();                  
extern ABC_DLL int             Abc_FrameReadStoreSize();              
extern ABC_DLL void *          Abc_FrameReadLibLut();                    
extern ABC_DLL void *          Abc_FrameReadLibGen();                    
extern ABC_DLL void *          Abc_FrameReadLibSuper();                  
extern ABC_DLL void *          Abc_FrameReadLibVer();                  
extern ABC_DLL void *          Abc_FrameReadManDd();                     
extern ABC_DLL void *          Abc_FrameReadManDec();                    
extern ABC_DLL char *          Abc_FrameReadFlag( char * pFlag ); 
extern ABC_DLL bool            Abc_FrameIsFlagEnabled( char * pFlag );

extern ABC_DLL void            Abc_FrameSetNtkStore( Abc_Ntk_t * pNtk ); 
extern ABC_DLL void            Abc_FrameSetNtkStoreSize( int nStored );  
extern ABC_DLL void            Abc_FrameSetLibLut( void * pLib );        
extern ABC_DLL void            Abc_FrameSetLibGen( void * pLib );        
extern ABC_DLL void            Abc_FrameSetLibSuper( void * pLib );      
extern ABC_DLL void            Abc_FrameSetLibVer( void * pLib );      
extern ABC_DLL void            Abc_FrameSetFlag( char * pFlag, char * pValue );

#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
