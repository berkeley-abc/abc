/**CFile****************************************************************

  FileName    [snRead.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [External HDL import without changing the current ABC workspace.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snRead.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
#ifndef ABC__base__sn__snRead_h
#define ABC__base__sn__snRead_h
#include "sn.h"
#include "misc/vec/vec.h"
ABC_NAMESPACE_HEADER_START
// Shared process-path utilities for the companion reader and partition mapper.
int Sn_TempPrefix( char * pBuffer, size_t nBuffer, const char * pStem );
int Sn_MapLutExecutable( char * pBuffer, size_t nBuffer );
typedef struct Sn_ReadOptions_t_
{
    const char * pTop;
    Vec_Ptr_t * vDefines;
    Vec_Ptr_t * vBlackboxes;
    int fVerbose;
    int fPreserveState;
    int fStrictModules; // Reject undeclared modules instead of dropping their instances.
} Sn_ReadOptions_t;

// Newly owned validated design; *pTop receives its selected root. Failure returns NULL and leaves the frame alone.
// On Windows, reports unsupported HDL loading and returns NULL without launching an external process.
sn_design_t * Sn_ReadHdl( int nFiles, char ** ppFiles, const Sn_ReadOptions_t * pOptions,
                         sn_module_id_t * pTop, FILE * pError );
int Sn_IsHdlFile( const char * pFileName );
// Common strict, state-preserving HDL front door for equivalence commands.
sn_design_t * Sn_ReadVerifyHdl( int nFiles, char ** ppFiles, const char * pTop,
                               Vec_Ptr_t * vDefines, sn_module_id_t * pTopId, FILE * pError );
ABC_NAMESPACE_HEADER_END
#endif
