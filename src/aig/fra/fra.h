/**CFile****************************************************************

  FileName    [fra.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [[New FRAIG package.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 30, 2007.]

  Revision    [$Id: fra.h,v 1.00 2007/06/30 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef __FRA_H__
#define __FRA_H__

#ifdef __cplusplus
extern "C" {
#endif 

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <time.h>

#include "vec.h"
#include "aig.h"
#include "dar.h"
#include "satSolver.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Fra_Par_t_   Fra_Par_t;
typedef struct Fra_Man_t_   Fra_Man_t;

// FRAIG parameters
struct Fra_Par_t_
{
    int              nSimWords;         // the number of words in the simulation info
    double           dSimSatur;         // the ratio of refined classes when saturation is reached
    int              fPatScores;        // enables simulation pattern scoring
    int              MaxScore;          // max score after which resimulation is used
    double           dActConeRatio;     // the ratio of cone to be bumped
    double           dActConeBumpMax;   // the largest bump in activity
    int              fSpeculate;        // use speculative reduction
    int              fProve;            // prove the miter outputs
    int              fVerbose;          // verbose output
    int              fDoSparse;         // skip sparse functions
    int              nBTLimitNode;      // conflict limit at a node
    int              nBTLimitMiter;     // conflict limit at an output
};

// FRAIG manager
struct Fra_Man_t_
{
    // high-level data    
    Fra_Par_t *      pPars;             // parameters governing fraiging
    // AIG managers
    Aig_Man_t *      pManAig;           // the starting AIG manager
    Aig_Man_t *      pManFraig;         // the final AIG manager
    // simulation info
    unsigned *       pSimWords;         // memory for simulation information
    int              nSimWords;         // the number of simulation words
    // counter example storage
    int              nPatWords;         // the number of words in the counter example
    unsigned *       pPatWords;         // the counter example
    int *            pPatScores;        // the scores of each pattern
    // equivalence classes 
    Vec_Ptr_t *      vClasses;          // equivalence classes
    Vec_Ptr_t *      vClasses1;         // equivalence class of Const1 node
    Vec_Ptr_t *      vClassesTemp;      // temporary storage for new classes
    Aig_Obj_t **     pMemClasses;       // memory allocated for equivalence classes
    Aig_Obj_t **     pMemClassesFree;   // memory allocated for equivalence classes to be used
    Vec_Ptr_t *      vClassOld;         // old equivalence class after splitting
    Vec_Ptr_t *      vClassNew;         // new equivalence class(es) after splitting
    int              nPairs;            // the number of pairs of nodes
    // equivalence checking
    sat_solver *     pSat;              // SAT solver
    int              nSatVars;          // the number of variables currently used
    Vec_Ptr_t *      vPiVars;           // the PIs of the cone used 
    sint64           nBTLimitGlobal;    // resource limit
    sint64           nInsLimitGlobal;   // resource limit
    // various data members
    Aig_Obj_t **     pMemFraig;         // memory allocated for points to the fraig nodes
    Aig_Obj_t **     pMemRepr;          // memory allocated for points to the node representatives
    Vec_Ptr_t **     pMemFanins;        // the arrays of fanins
    int *            pMemSatNums;       // the array of SAT numbers
    int              nSizeAlloc;        // allocated size of the arrays
    // statistics
    int              nSimRounds;
    int              nNodesMiter;
    int              nClassesZero;
    int              nClassesBeg;
    int              nClassesEnd;
    int              nPairsBeg;
    int              nPairsEnd;
    int              nSatCalls;
    int              nSatCallsSat;
    int              nSatCallsUnsat;
    int              nSatProof;
    int              nSatFails;
    int              nSatFailsReal;
    int              nSpeculs;         
    // runtime
    int              timeSim;
    int              timeTrav;
    int              timeSat;
    int              timeSatUnsat;
    int              timeSatSat;
    int              timeSatFail;
    int              timeRef;
    int              timeTotal;
    int              time1;
    int              time2;
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

static inline unsigned *   Fra_ObjSim( Aig_Obj_t * pObj )   { return ((Fra_Man_t *)pObj->pData)->pSimWords + ((Fra_Man_t *)pObj->pData)->nSimWords * pObj->Id;  }
static inline unsigned     Fra_ObjRandomSim()               { return (rand() << 24) ^ (rand() << 12) ^ rand(); }

static inline Aig_Obj_t *  Fra_ObjFraig( Aig_Obj_t * pObj )                              { return ((Fra_Man_t *)pObj->pData)->pMemFraig[pObj->Id];       }
static inline Aig_Obj_t *  Fra_ObjRepr( Aig_Obj_t * pObj )                               { return ((Fra_Man_t *)pObj->pData)->pMemRepr[pObj->Id];        }
static inline Vec_Ptr_t *  Fra_ObjFaninVec( Aig_Obj_t * pObj )                           { return ((Fra_Man_t *)pObj->pData)->pMemFanins[pObj->Id];      }
static inline int          Fra_ObjSatNum( Aig_Obj_t * pObj )                             { return ((Fra_Man_t *)pObj->pData)->pMemSatNums[pObj->Id];     }

static inline void         Fra_ObjSetFraig( Aig_Obj_t * pObj, Aig_Obj_t * pNode )        { ((Fra_Man_t *)pObj->pData)->pMemFraig[pObj->Id]   = pNode;    }
static inline void         Fra_ObjSetRepr( Aig_Obj_t * pObj, Aig_Obj_t * pNode )         { ((Fra_Man_t *)pObj->pData)->pMemRepr[pObj->Id]    = pNode;    }
static inline void         Fra_ObjSetFaninVec( Aig_Obj_t * pObj, Vec_Ptr_t * vFanins )   { ((Fra_Man_t *)pObj->pData)->pMemFanins[pObj->Id]  = vFanins;  }
static inline void         Fra_ObjSetSatNum( Aig_Obj_t * pObj, int Num )                 { ((Fra_Man_t *)pObj->pData)->pMemSatNums[pObj->Id] = Num;      }

static inline Aig_Obj_t *  Fra_ObjChild0Fra( Aig_Obj_t * pObj ) { assert( !Aig_IsComplement(pObj) ); return Aig_ObjFanin0(pObj)? Aig_NotCond(Fra_ObjFraig(Aig_ObjFanin0(pObj)), Aig_ObjFaninC0(pObj)) : NULL;  }
static inline Aig_Obj_t *  Fra_ObjChild1Fra( Aig_Obj_t * pObj ) { assert( !Aig_IsComplement(pObj) ); return Aig_ObjFanin1(pObj)? Aig_NotCond(Fra_ObjFraig(Aig_ObjFanin1(pObj)), Aig_ObjFaninC1(pObj)) : NULL;  }

////////////////////////////////////////////////////////////////////////
///                         ITERATORS                                ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== fraAnd.c ========================================================*/
extern void                Fra_Sweep( Fra_Man_t * p );
/*=== fraClass.c ========================================================*/
extern void                Fra_PrintClasses( Fra_Man_t * p );
extern void                Fra_CreateClasses( Fra_Man_t * p );
extern int                 Fra_RefineClasses( Fra_Man_t * p );
extern int                 Fra_RefineClasses1( Fra_Man_t * p );
/*=== fraCnf.c ========================================================*/
extern void                Fra_NodeAddToSolver( Fra_Man_t * p, Aig_Obj_t * pOld, Aig_Obj_t * pNew );
/*=== fraCore.c ========================================================*/
extern Aig_Man_t *         Fra_Perform( Aig_Man_t * pManAig, Fra_Par_t * pParams );
/*=== fraMan.c ========================================================*/
extern void                Fra_ParamsDefault( Fra_Par_t * pParams );
extern Fra_Man_t *         Fra_ManStart( Aig_Man_t * pManAig, Fra_Par_t * pParams );
extern void                Fra_ManPrepare( Fra_Man_t * p );
extern void                Fra_ManStop( Fra_Man_t * p );
extern void                Fra_ManPrint( Fra_Man_t * p );
/*=== fraSat.c ========================================================*/
extern int                 Fra_NodesAreEquiv( Fra_Man_t * p, Aig_Obj_t * pOld, Aig_Obj_t * pNew );
extern int                 Fra_NodeIsConst( Fra_Man_t * p, Aig_Obj_t * pNew );
/*=== fraSim.c ========================================================*/
extern int                 Fra_NodeHasZeroSim( Fra_Man_t * p, Aig_Obj_t * pObj );
extern int                 Fra_NodeCompareSims( Fra_Man_t * p, Aig_Obj_t * pObj0, Aig_Obj_t * pObj1 );
extern void                Fra_SavePattern( Fra_Man_t * p );
extern void                Fra_Simulate( Fra_Man_t * p );
extern void                Fra_Resimulate( Fra_Man_t * p );
extern int                 Fra_CheckOutputSims( Fra_Man_t * p );

#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

