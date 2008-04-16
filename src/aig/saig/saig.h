/**CFile****************************************************************

  FileName    [saig.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: saig.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __SAIG_H__
#define __SAIG_H__

#ifdef __cplusplus
extern "C" {
#endif

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

static inline int          Saig_ManPiNum( Aig_Man_t * p )          { return p->nTruePis;                     }
static inline int          Saig_ManPoNum( Aig_Man_t * p )          { return p->nTruePos;                     }
static inline int          Saig_ManRegNum( Aig_Man_t * p )         { return p->nRegs;                        }
static inline Aig_Obj_t *  Saig_ManLo( Aig_Man_t * p, int i )      { return (Aig_Obj_t *)Vec_PtrEntry(p->vPis, Saig_ManPiNum(p)+i);   }
static inline Aig_Obj_t *  Saig_ManLi( Aig_Man_t * p, int i )      { return (Aig_Obj_t *)Vec_PtrEntry(p->vPos, Saig_ManPoNum(p)+i);   }

// iterator over the primary inputs/outputs
#define Saig_ManForEachPi( p, pObj, i )                                           \
    Vec_PtrForEachEntryStop( p->vPis, pObj, i, Saig_ManPiNum(p) )
#define Saig_ManForEachPo( p, pObj, i )                                           \
    Vec_PtrForEachEntryStop( p->vPos, pObj, i, Saig_ManPoNum(p) )
// iterator over the latch inputs/outputs
#define Saig_ManForEachLo( p, pObj, i )                                           \
    for ( i = 0; (i < Saig_ManRegNum(p)) && (((pObj) = Vec_PtrEntry(p->vPis, i+Saig_ManPiNum(p))), 1); i++ )
#define Saig_ManForEachLi( p, pObj, i )                                           \
    for ( i = 0; (i < Saig_ManRegNum(p)) && (((pObj) = Vec_PtrEntry(p->vPos, i+Saig_ManPoNum(p))), 1); i++ )
// iterator over the latch input and outputs
#define Saig_ManForEachLiLo( p, pObjLi, pObjLo, i )                               \
    for ( i = 0; (i < Saig_ManRegNum(p)) && (((pObjLi) = Saig_ManLi(p, i)), 1)    \
        && (((pObjLo)=Saig_ManLo(p, i)), 1); i++ )

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== saigPhase.c ==========================================================*/
 
#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

