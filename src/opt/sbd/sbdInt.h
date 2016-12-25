/**CFile****************************************************************

  FileName    [rsbInt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based optimization using internal don't-cares.]

  Synopsis    [Internal declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: rsbInt.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef ABC__opt_sbdInt__h
#define ABC__opt_sbdInt__h


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include "misc/vec/vec.h"
#include "sat/bsat/satSolver.h"
#include "misc/util/utilNam.h"
#include "misc/util/utilTruth.h"
#include "map/scl/sclLib.h"
#include "map/scl/sclCon.h"
#include "bool/kit/kit.h"
#include "misc/st/st.h"
#include "map/mio/mio.h"
#include "base/abc/abc.h"
#include "sbd.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_HEADER_START

#define SBD_SAT_UNDEC 0x1234567812345678
#define SBD_SAT_SAT   0x8765432187654321

#define SBD_LUTS_MAX  2
#define SBD_SIZE_MAX  4
#define SBD_DIV_MAX   7

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Sbd_Str_t_ Sbd_Str_t;
struct Sbd_Str_t_
{
    int               fLut;                 // LUT or SEL
    int               nVarIns;              // input count
    int               VarIns[SBD_DIV_MAX];  // input vars
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== sbdCnf.c ==========================================================*/

ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

