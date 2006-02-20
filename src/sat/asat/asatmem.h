/**CFile****************************************************************

  FileName    [asatmem.h]

  PackageName [SAT solver.]

  Synopsis    [Memory management.]

  Author      [Alan Mishchenko <alanmi@eecs.berkeley.edu>]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - January 1, 2004.]

  Revision    [$Id: asatmem.h,v 1.0 2004/01/01 1:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __ASAT_MEM_H__
#define __ASAT_MEM_H__

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

//#include "leaks.h"       
#include <stdio.h>
#include <stdlib.h>

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    STRUCTURE DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

typedef struct Asat_MmFixed_t_ Asat_MmFixed_t;
typedef struct Asat_MmFlex_t_  Asat_MmFlex_t;
typedef struct Asat_MmStep_t_  Asat_MmStep_t;

////////////////////////////////////////////////////////////////////////
///                       GLOBAL VARIABLES                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                       MACRO DEFINITIONS                          ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DECLARATIONS                        ///
////////////////////////////////////////////////////////////////////////

// fixed-size-block memory manager
extern Asat_MmFixed_t *    Asat_MmFixedStart( int nEntrySize );
extern void                Asat_MmFixedStop( Asat_MmFixed_t * p, int fVerbose );
extern char *              Asat_MmFixedEntryFetch( Asat_MmFixed_t * p );
extern void                Asat_MmFixedEntryRecycle( Asat_MmFixed_t * p, char * pEntry );
extern void                Asat_MmFixedRestart( Asat_MmFixed_t * p );
extern int                 Asat_MmFixedReadMemUsage( Asat_MmFixed_t * p );
// flexible-size-block memory manager
extern Asat_MmFlex_t *     Asat_MmFlexStart();
extern void                Asat_MmFlexStop( Asat_MmFlex_t * p, int fVerbose );
extern char *              Asat_MmFlexEntryFetch( Asat_MmFlex_t * p, int nBytes );
extern int                 Asat_MmFlexReadMemUsage( Asat_MmFlex_t * p );
// hierarchical memory manager
extern Asat_MmStep_t *     Asat_MmStepStart( int nSteps );
extern void                Asat_MmStepStop( Asat_MmStep_t * p, int fVerbose );
extern char *              Asat_MmStepEntryFetch( Asat_MmStep_t * p, int nBytes );
extern void                Asat_MmStepEntryRecycle( Asat_MmStep_t * p, char * pEntry, int nBytes );
extern int                 Asat_MmStepReadMemUsage( Asat_MmStep_t * p );

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
#endif
