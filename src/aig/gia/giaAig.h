/**CFile****************************************************************

  FileName    [giaAig.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaAig.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __GIA_AIG_H__
#define __GIA_AIG_H__

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "aig.h"
#include "gia.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////
 
////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== giaAig.c =============================================================*/
extern Gia_Man_t *         Gia_ManFromAig( Aig_Man_t * p );
extern Gia_Man_t *         Gia_ManFromAigSimple( Aig_Man_t * p );
extern Gia_Man_t *         Gia_ManFromAigSwitch( Aig_Man_t * p );
extern Aig_Man_t *         Gia_ManToAig( Gia_Man_t * p, int fChoices );
extern Aig_Man_t *         Gia_ManToAigSkip( Gia_Man_t * p, int nOutDelta );
extern void                Gia_ManReprToAigRepr( Aig_Man_t * p, Gia_Man_t * pGia );
extern Gia_Man_t *         Gia_ManCompress2( Gia_Man_t * p );
 
#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

