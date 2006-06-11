/**CFile****************************************************************

  FileName    [player.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [PLA decomposition package.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: player.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef __XYZ_H__
#define __XYZ_H__

#ifdef __cplusplus
extern "C" {
#endif

#include "ivy.h"
#include "esop.h"
#include "vec.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Pla_Man_t_  Pla_Man_t;
typedef struct Pla_Obj_t_  Pla_Obj_t;

// storage for node information
struct Pla_Obj_t_
{
    unsigned          fFixed :  1;  // fixed node
    unsigned          Depth  :  7;  // the depth in terms of LUTs/PLAs
    unsigned          nRefs  : 24;  // the number of references
    Vec_Int_t         vSupp[2];     // supports in two frames
    Esop_Cube_t *     pCover[2];    // esops in two frames
};

// storage for additional information
struct Pla_Man_t_
{
    // general characteristics
    int               nLutMax;      // the number of vars
    int               nPlaMax;      // the number of vars
    int               nCubesMax;    // the limit on the number of cubes in the intermediate covers
    Ivy_Man_t *       pManAig;      // the AIG manager
    Pla_Obj_t *       pPlaStrs;     // memory for structures
    Esop_Man_t *      pManMin;      // the cube manager
    // arrays to map local variables
    Vec_Int_t *       vComTo0;      // mapping of common variables into first fanin
    Vec_Int_t *       vComTo1;      // mapping of common variables into second fanin
    Vec_Int_t *       vPairs0;      // the first var in each pair of common vars
    Vec_Int_t *       vPairs1;      // the second var in each pair of common vars
    Vec_Int_t *       vTriv0;       // trival support of the first node
    Vec_Int_t *       vTriv1;       // trival support of the second node
    // statistics
    int               nNodes;       // the number of nodes processed
    int               nNodesLut;    // the number of nodes processed
    int               nNodesPla;    // the number of nodes processed
    int               nNodesBoth;   // the number of nodes processed
    int               nNodesDeref;  // the number of nodes processed
};

#define PLAYER_FANIN_LIMIT  128

#define PLA_MIN(a,b)        (((a) < (b))? (a) : (b))
#define PLA_MAX(a,b)        (((a) > (b))? (a) : (b))

#define PLA_EMPTY           ((Esop_Cube_t *)1)

static inline Pla_Man_t *   Ivy_ObjPlaMan( Ivy_Obj_t * pObj )   { return (Pla_Man_t *)Ivy_ObjMan(pObj)->pData;       }
static inline Pla_Obj_t *   Ivy_ObjPlaStr( Ivy_Obj_t * pObj )   { return Ivy_ObjPlaMan(pObj)->pPlaStrs + pObj->Id;   }

static inline unsigned *    Ivy_ObjGetTruth( Ivy_Obj_t * pObj )  
{ 
    Ivy_Man_t * p = Ivy_ObjMan(pObj);
    int Offset = Vec_IntEntry( p->vTruths, pObj->Id );
    return Offset < 0 ? NULL : p->pMemory + Offset;
    
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== playerAbc.c ==============================================================*/
extern void *        Abc_NtkPlayer( void * pNtk, int nLutMax, int nFaninMax, int fVerbose );
/*=== playerBuild.c ============================================================*/
extern Ivy_Man_t *   Pla_ManToAig( Ivy_Man_t * p );
/*=== playerCore.c =============================================================*/
extern Ivy_Man_t *   Pla_ManDecompose( Ivy_Man_t * p, int nLutMax, int nPlaMax, int fVerbose );
/*=== playerMan.c ==============================================================*/
extern Pla_Man_t *   Pla_ManAlloc( Ivy_Man_t * p, int nLutMax, int nPlaMax );
extern void          Pla_ManFree( Pla_Man_t * p );
extern void          Pla_ManFreeStr( Pla_Man_t * p, Pla_Obj_t * pStr );
/*=== playerUtil.c =============================================================*/
extern int           Pla_ManMergeTwoSupports( Pla_Man_t * p, Vec_Int_t * vSupp0, Vec_Int_t * vSupp1, Vec_Int_t * vSupp );
extern Esop_Cube_t * Pla_ManAndTwoCovers( Pla_Man_t * p, Esop_Cube_t * pCover0, Esop_Cube_t * pCover1, int nSupp, int fStopAtLimit );
extern Esop_Cube_t * Pla_ManExorTwoCovers( Pla_Man_t * p, Esop_Cube_t * pCover0, Esop_Cube_t * pCover1, int nSupp, int fStopAtLimit );
extern void          Pla_ManComputeStats( Ivy_Man_t * pAig, Vec_Int_t * vNodes );

#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////



