/**CFile****************************************************************

  FileName    [parterInt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Acyclic word-level partitioning.]

  Synopsis    [Checked storage and diagnostics shared by the kernel.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: parterInt.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
#ifndef ABC__base__parter__parterInt_h
#define ABC__base__parter__parterInt_h

#include "parter.h"
#include <float.h>
#include <math.h>
#include <stdarg.h>

ABC_NAMESPACE_HEADER_START

extern int Prt_Error( char * pError, unsigned nError, const char * pFormat, ... );
extern void * Prt_Alloc( size_t nItems, size_t ItemSize );

// Internal callers have already validated the immutable graph.
extern int Prt_GraphTopoChecked( const Prt_Graph_t * p, unsigned * pOrder, char * pError, unsigned nError );

ABC_NAMESPACE_HEADER_END
#endif
