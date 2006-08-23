/**CFile****************************************************************

  FileName    [io.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: io.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef __IO_H__
#define __IO_H__

#ifdef __cplusplus
extern "C" {
#endif

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

#define  IO_WRITE_LINE_LENGTH    78    // the output line length

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== abcRead.c ==========================================================*/
extern Abc_Ntk_t *        Io_Read( char * pFileName, int fCheck );
/*=== abcReadBaf.c ==========================================================*/
extern Abc_Ntk_t *        Io_ReadBaf( char * pFileName, int fCheck );
/*=== abcReadBlif.c ==========================================================*/
extern Abc_Ntk_t *        Io_ReadBlif( char * pFileName, int fCheck );
/*=== abcReadBench.c ==========================================================*/
extern Abc_Ntk_t *        Io_ReadBench( char * pFileName, int fCheck );
/*=== abcReadEdif.c ==========================================================*/
extern Abc_Ntk_t *        Io_ReadEdif( char * pFileName, int fCheck );
/*=== abcReadEqn.c ==========================================================*/
extern Abc_Ntk_t *        Io_ReadEqn( char * pFileName, int fCheck );
/*=== abcReadVerilog.c ==========================================================*/
extern Abc_Ntk_t *        Io_ReadVerilog( char * pFileName, int fCheck );
/*=== abcReadPla.c ==========================================================*/
extern Abc_Ntk_t *        Io_ReadPla( char * pFileName, int fCheck );
/*=== abcUtil.c ==========================================================*/
extern Abc_Obj_t *        Io_ReadCreatePi( Abc_Ntk_t * pNtk, char * pName );
extern Abc_Obj_t *        Io_ReadCreatePo( Abc_Ntk_t * pNtk, char * pName );
extern Abc_Obj_t *        Io_ReadCreateAssert( Abc_Ntk_t * pNtk, char * pName );
extern Abc_Obj_t *        Io_ReadCreateLatch( Abc_Ntk_t * pNtk, char * pNetLI, char * pNetLO );
extern Abc_Obj_t *        Io_ReadCreateNode( Abc_Ntk_t * pNtk, char * pNameOut, char * pNamesIn[], int nInputs );
extern Abc_Obj_t *        Io_ReadCreateConst( Abc_Ntk_t * pNtk, char * pName, bool fConst1 );
extern Abc_Obj_t *        Io_ReadCreateInv( Abc_Ntk_t * pNtk, char * pNameIn, char * pNameOut );
extern Abc_Obj_t *        Io_ReadCreateBuf( Abc_Ntk_t * pNtk, char * pNameIn, char * pNameOut );
extern FILE *             Io_FileOpen( const char * FileName, const char * PathVar, const char * Mode, int fVerbose );
/*=== abcWriteBaf.c ==========================================================*/
extern void               Io_WriteBaf( Abc_Ntk_t * pNtk, char * pFileName );
/*=== abcWriteBlif.c ==========================================================*/
extern void               Io_WriteBlifLogic( Abc_Ntk_t * pNtk, char * pFileName, int fWriteLatches );
extern void               Io_WriteBlifNetlist( Abc_Ntk_t * pNtk, char * pFileName, int fWriteLatches );
extern void               Io_WriteTimingInfo( FILE * pFile, Abc_Ntk_t * pNtk );
/*=== abcWriteBench.c ==========================================================*/
extern int                Io_WriteBench( Abc_Ntk_t * pNtk, char * FileName );
/*=== abcWriteCnf.c ==========================================================*/
extern int                Io_WriteCnf( Abc_Ntk_t * pNtk, char * FileName );
/*=== abcWriteDot.c ==========================================================*/
extern void               Io_WriteDotAig( Abc_Ntk_t * pNtk, Vec_Ptr_t * vNodes, Vec_Ptr_t * vNodesShow, char * pFileName, int fMulti );
extern void               Io_WriteDotNtk( Abc_Ntk_t * pNtk, Vec_Ptr_t * vNodes, Vec_Ptr_t * vNodesShow, char * pFileName, int fGateNames );
/*=== abcWriteEqn.c ==========================================================*/
extern void               Io_WriteEqn( Abc_Ntk_t * pNtk, char * pFileName );
/*=== abcWriteGml.c ==========================================================*/
extern void               Io_WriteGml( Abc_Ntk_t * pNtk, char * pFileName );
/*=== abcWriteList.c ==========================================================*/
extern void               Io_WriteList( Abc_Ntk_t * pNtk, char * pFileName, int fUseHost );
/*=== abcWritePla.c ==========================================================*/
extern int                Io_WritePla( Abc_Ntk_t * pNtk, char * FileName );
/*=== abcWriteVerilog.c ==========================================================*/
extern void               Io_WriteVerilog( Abc_Ntk_t * pNtk, char * FileName, int fVerLibStyle );

#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

