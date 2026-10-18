/**CFile****************************************************************

  FileName    [drw.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Compact DAG-aware AIG rewriting.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: drw.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__opt__drw__drw_h
#define ABC__opt__drw__drw_h

#include "aig/gia/gia.h"

ABC_NAMESPACE_HEADER_START

extern Gia_Man_t * Drw_ManRewrite( Gia_Man_t * pGia, int fKeepLevel, int fVerbose );

ABC_NAMESPACE_HEADER_END

#endif
