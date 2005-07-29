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
///                      MACRO DEFITIONS                             ///
////////////////////////////////////////////////////////////////////////

#define  IO_WRITE_LINE_LENGTH    78    // the output line length

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== abcRead.c ==========================================================*/
extern Abc_Ntk_t *        Io_Read( char * pFileName, int fCheck );
/*=== abcReadBlif.c ==========================================================*/
extern Abc_Ntk_t *        Io_ReadBlif( char * pFileName, int fCheck );
/*=== abcReadBench.c ==========================================================*/
extern Abc_Ntk_t *        Io_ReadBench( char * pFileName, int fCheck );
/*=== abcReadVerilog.c ==========================================================*/
extern Abc_Ntk_t *        Io_ReadVerilog( char * pFileName, int fCheck );
extern void               Io_ReadSetNonDrivenNets( Abc_Ntk_t * pNet );
/*=== abcWriteBlif.c ==========================================================*/
extern void               Io_WriteBlif( Abc_Ntk_t * pNtk, char * pFileName );
extern void               Io_WriteTimingInfo( FILE * pFile, Abc_Ntk_t * pNtk );
/*=== abcWriteBlifLogic.c ==========================================================*/
extern void               Io_WriteBlifLogic( Abc_Ntk_t * pNtk, char * pFileName, int fWriteLatches );
/*=== abcWriteBench.c ==========================================================*/
extern int                Io_WriteBench( Abc_Ntk_t * pNtk, char * FileName );
/*=== abcWriteGate.c ==========================================================*/
extern int                Io_WriteGate( Abc_Ntk_t * pNtk, char * FileName );
/*=== abcWriteCnf.c ==========================================================*/
extern int                Io_WriteCnf( Abc_Ntk_t * pNtk, char * FileName );

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

#endif

