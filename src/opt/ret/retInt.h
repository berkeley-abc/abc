/**CFile****************************************************************

  FileName    [retInt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Retiming package.]

  Synopsis    [Internal declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - Oct 31, 2006.]

  Revision    [$Id: retInt.h,v 1.00 2006/10/31 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __RET_INT_H__
#define __RET_INT_H__

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    STRUCTURE DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                       MACRO DEFINITIONS                          ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== retArea.c ========================================================*/
extern int         Abc_NtkRetimeMinArea( Abc_Ntk_t * pNtk, int fVerbose );
/*=== retBwd.c ========================================================*/
extern int         Abc_NtkRetimeBackward( Abc_Ntk_t * pNtk, int fVerbose );
/*=== retCore.c ========================================================*/
extern int         Abc_NtkRetime( Abc_Ntk_t * pNtk, int Mode, int fVerbose );
/*=== retDelay.c ========================================================*/
extern int         Abc_NtkRetimeMinDelay( Abc_Ntk_t * pNtk, int fVerbose );
/*=== retFlow.c ========================================================*/
extern void        Abc_NtkMaxFlowTest( Abc_Ntk_t * pNtk );
extern Vec_Ptr_t * Abc_NtkMaxFlow( Abc_Ntk_t * pNtk, int fForward, int fVerbose );
/*=== retFwd.c ========================================================*/
extern int         Abc_NtkRetimeForward( Abc_Ntk_t * pNtk, int fVerbose );
/*=== retInit.c ========================================================*/
extern void        Abc_NtkRetimeInitialValues( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkMiter, int fVerbose );

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


