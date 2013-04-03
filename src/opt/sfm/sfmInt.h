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
 
#ifndef ABC__opt_sfmInt__h
#define ABC__opt_sfmInt__h


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include "misc/vec/vec.h"
#include "sfm.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_HEADER_START

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

struct Sfm_Ntk_t_
{
    // objects
    int *             pMem;   // memory for objects
    Vec_Int_t         vObjs;  // ObjId -> Offset
    Vec_Int_t         vPis;   // PiId -> ObjId
    Vec_Int_t         vPos;   // PoId -> ObjId
    // fanins/fanouts
    Vec_Int_t         vMem;   // memory for overflow fanin/fanouts
    // attributes
    Vec_Int_t         vLevels;
    Vec_Int_t         vTravIds;
    Vec_Int_t         vSatVars;
    Vec_Wrd_t         vTruths;
};

typedef struct Sfm_Obj_t_ Sfm_Obj_t;
struct Sfm_Obj_t_
{
    unsigned          Type   :  2;
    unsigned          Id     : 30;
    unsigned          fOpt   :  1;
    unsigned          fTfo   :  1;
    unsigned          nFanis :  4;
    unsigned          nFanos : 26;
    int               Fanio[0];
};

struct Sfm_Man_t_
{
    Sfm_Ntk_t *       pNtk;
    // window
    Sfm_Obj_t *       pNode;
    Vec_Int_t *       vLeaves;      // leaves 
    Vec_Int_t *       vRoots;       // roots
    Vec_Int_t *       vNodes;       // internal
    Vec_Int_t *       vTfo;         // TFO (including pNode)
    // SAT solving
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

static inline Sfm_Obj_t * Sfm_ManObj( Sfm_Ntk_t * p, int Id ) { return (Sfm_Obj_t *)Vec_IntEntryP( &p->vObjs, Id ); }

#define Sfm_ManForEachObj( p, pObj, i )                                \
    for ( i = 0; (i < Vec_IntSize(&p->vObjs) && ((pObj) = Sfm_ManObj(p, i))); i++ )
#define Sfm_ManForEachPi( p, pObj, i )                                 \
    for ( i = 0; (i < Vec_IntSize(&p->vPis) && ((pObj) = Sfm_ManObj(p, Vec_IntEntry(&p->vPis, i)))); i++ )
#define Sfm_ManForEachPo( p, pObj, i )                                 \
    for ( i = 0; (i < Vec_IntSize(&p->vPos) && ((pObj) = Sfm_ManObj(p, Vec_IntEntry(&p->vPos, i)))); i++ )

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== sfmCnf.c ==========================================================*/
extern int          Sfm_DeriveCnfs( Vec_Wrd_t * vTruths, Vec_Int_t * vFanins, Vec_Str_t ** pvCnfs, Vec_Int_t ** pvOffsets );
/*=== sfmCore.c ==========================================================*/
/*=== sfmMan.c ==========================================================*/
/*=== sfmNtk.c ==========================================================*/
/*=== sfmSat.c ==========================================================*/
extern int          Sfm_CreateSatWindow( Sfm_Ntk_t * p );

ABC_NAMESPACE_HEADER_END



#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

