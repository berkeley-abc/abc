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

#ifndef ABC__base__main__main_h
#define ABC__base__main__main_h


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

// core packages
#include "base/abc/abc.h"
#include "aig/gia/gia.h"

// data structure packages
#include "misc/vec/vec.h"
#include "misc/st/st.h"

// the framework containing all data is defined here
#include "abcapis.h"

#include "base/cmd/cmd.h"
#include "base/io/ioAbc.h"

ABC_NAMESPACE_HEADER_START

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         TYPEDEFS                                 ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                       GLOBAL VARIABLES                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    STRUCTURE DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                       MACRO DEFINITIONS                          ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== main.c ===========================================================*/
ABC_DLL extern void            Abc_Start();
ABC_DLL extern void            Abc_Stop();

/*=== mainFrame.c ===========================================================*/
ABC_DLL extern Abc_Ntk_t *     Abc_FrameReadNtk( Abc_Frame_t * p );
ABC_DLL extern Gia_Man_t *     Abc_FrameReadGia( Abc_Frame_t * p );
ABC_DLL extern FILE *          Abc_FrameReadOut( Abc_Frame_t * p );
ABC_DLL extern FILE *          Abc_FrameReadErr( Abc_Frame_t * p );
ABC_DLL extern int             Abc_FrameReadMode( Abc_Frame_t * p );
ABC_DLL extern int             Abc_FrameSetMode( Abc_Frame_t * p, int fNameMode );
ABC_DLL extern void            Abc_FrameRestart( Abc_Frame_t * p );
ABC_DLL extern int             Abc_FrameShowProgress( Abc_Frame_t * p );
ABC_DLL extern void            Abc_FrameClearVerifStatus( Abc_Frame_t * p );
ABC_DLL extern void            Abc_FrameUpdateGia( Abc_Frame_t * p, Gia_Man_t * pNew );
ABC_DLL extern Gia_Man_t *     Abc_FrameGetGia( Abc_Frame_t * p );

ABC_DLL extern void            Abc_FrameSetCurrentNetwork( Abc_Frame_t * p, Abc_Ntk_t * pNet );
ABC_DLL extern void            Abc_FrameSwapCurrentAndBackup( Abc_Frame_t * p );
ABC_DLL extern void            Abc_FrameReplaceCurrentNetwork( Abc_Frame_t * p, Abc_Ntk_t * pNet );
ABC_DLL extern void            Abc_FrameUnmapAllNetworks( Abc_Frame_t * p );
ABC_DLL extern void            Abc_FrameDeleteAllNetworks( Abc_Frame_t * p );

ABC_DLL extern void            Abc_FrameSetGlobalFrame( Abc_Frame_t * p );
ABC_DLL extern Abc_Frame_t *   Abc_FrameGetGlobalFrame();
ABC_DLL extern Abc_Frame_t *   Abc_FrameReadGlobalFrame();

ABC_DLL extern Vec_Ptr_t *     Abc_FrameReadStore();
ABC_DLL extern int             Abc_FrameReadStoreSize();
ABC_DLL extern void *          Abc_FrameReadLibLut();
ABC_DLL extern void *          Abc_FrameReadLibBox();
ABC_DLL extern void *          Abc_FrameReadLibGen();
ABC_DLL extern void *          Abc_FrameReadLibGen2();
ABC_DLL extern void *          Abc_FrameReadLibSuper();
ABC_DLL extern void *          Abc_FrameReadLibScl();
ABC_DLL extern void *          Abc_FrameReadManDd();
ABC_DLL extern void *          Abc_FrameReadManDec();
ABC_DLL extern void *          Abc_FrameReadManDsd();
ABC_DLL extern void *          Abc_FrameReadManDsd2();
ABC_DLL extern Vec_Ptr_t *     Abc_FrameReadSignalNames();
ABC_DLL extern char *          Abc_FrameReadSpecName();

ABC_DLL extern char *          Abc_FrameReadFlag( char * pFlag );
ABC_DLL extern int             Abc_FrameIsFlagEnabled( char * pFlag );
ABC_DLL extern int             Abc_FrameIsBatchMode();
ABC_DLL extern void            Abc_FrameSetBatchMode( int Mode );
ABC_DLL extern int             Abc_FrameIsBridgeMode();
ABC_DLL extern void            Abc_FrameSetBridgeMode();

ABC_DLL extern int             Abc_FrameReadBmcFrames( Abc_Frame_t * p );
ABC_DLL extern int             Abc_FrameReadProbStatus( Abc_Frame_t * p );
ABC_DLL extern void *          Abc_FrameReadCex( Abc_Frame_t * p );
ABC_DLL extern Vec_Ptr_t *     Abc_FrameReadCexVec( Abc_Frame_t * p );
ABC_DLL extern Vec_Int_t *     Abc_FrameReadStatusVec( Abc_Frame_t * p );
ABC_DLL extern Vec_Ptr_t *     Abc_FrameReadPoEquivs( Abc_Frame_t * p );
ABC_DLL extern Vec_Int_t *     Abc_FrameReadPoStatuses( Abc_Frame_t * p );
ABC_DLL extern Vec_Int_t *     Abc_FrameReadObjIds( Abc_Frame_t * p );
ABC_DLL extern Abc_Nam_t *     Abc_FrameReadJsonStrs( Abc_Frame_t * p );
ABC_DLL extern Vec_Wec_t *     Abc_FrameReadJsonObjs( Abc_Frame_t * p );

ABC_DLL extern int             Abc_FrameReadCexPiNum( Abc_Frame_t * p );
ABC_DLL extern int             Abc_FrameReadCexRegNum( Abc_Frame_t * p );
ABC_DLL extern int             Abc_FrameReadCexPo( Abc_Frame_t * p );
ABC_DLL extern int             Abc_FrameReadCexFrame( Abc_Frame_t * p );

ABC_DLL extern void            Abc_FrameSetNtkStore( Abc_Ntk_t * pNtk );
ABC_DLL extern void            Abc_FrameSetNtkStoreSize( int nStored );
ABC_DLL extern void            Abc_FrameSetLibLut( void * pLib );
ABC_DLL extern void            Abc_FrameSetLibBox( void * pLib );
ABC_DLL extern void            Abc_FrameSetLibGen( void * pLib );
ABC_DLL extern void            Abc_FrameSetLibGen2( void * pLib );
ABC_DLL extern void            Abc_FrameSetLibSuper( void * pLib );
ABC_DLL extern void            Abc_FrameSetLibVer( void * pLib );
ABC_DLL extern void            Abc_FrameSetFlag( char * pFlag, char * pValue );
ABC_DLL extern void            Abc_FrameSetCex( Abc_Cex_t * pCex );
ABC_DLL extern void            Abc_FrameSetNFrames( int nFrames );
ABC_DLL extern void            Abc_FrameSetStatus( int Status );
ABC_DLL extern void            Abc_FrameSetManDsd( void * pMan );
ABC_DLL extern void            Abc_FrameSetManDsd2( void * pMan );
ABC_DLL extern void            Abc_FrameSetInv( Vec_Int_t * vInv );
ABC_DLL extern void            Abc_FrameSetCnf( Vec_Int_t * vInv );
ABC_DLL extern void            Abc_FrameSetStr( Vec_Str_t * vInv );
ABC_DLL extern void            Abc_FrameSetJsonStrs( Abc_Nam_t * pStrs );
ABC_DLL extern void            Abc_FrameSetJsonObjs( Vec_Wec_t * vObjs );
ABC_DLL extern void            Abc_FrameSetSignalNames( Vec_Ptr_t * vNames );
ABC_DLL extern void            Abc_FrameSetSpecName( char * pFileName );

ABC_DLL extern int             Abc_FrameCheckPoConst( Abc_Frame_t * p, int iPoNum );

ABC_DLL extern void            Abc_FrameReplaceCex( Abc_Frame_t * pAbc, Abc_Cex_t ** ppCex );
ABC_DLL extern void            Abc_FrameReplaceCexVec( Abc_Frame_t * pAbc, Vec_Ptr_t ** pvCexVec );
ABC_DLL extern void            Abc_FrameReplacePoEquivs( Abc_Frame_t * pAbc, Vec_Ptr_t ** pvPoEquivs );
ABC_DLL extern void            Abc_FrameReplacePoStatuses( Abc_Frame_t * pAbc, Vec_Int_t ** pvStatuses );

ABC_DLL extern char *          Abc_FrameReadDrivingCell();
ABC_DLL extern float           Abc_FrameReadMaxLoad();
ABC_DLL extern void            Abc_FrameSetDrivingCell( char * pName );
ABC_DLL extern void            Abc_FrameSetMaxLoad( float Load );

ABC_DLL extern void            Abc_FrameSetArrayMapping( int * p );
ABC_DLL extern void            Abc_FrameSetBoxes( int * p );

ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
