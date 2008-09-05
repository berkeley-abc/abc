/**CFile****************************************************************

  FileName    [sswInt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Inductive prover with constraints.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 1, 2008.]

  Revision    [$Id: sswInt.h,v 1.00 2008/09/01 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __SSW_INT_H__
#define __SSW_INT_H__

#ifdef __cplusplus
extern "C" {
#endif

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "saig.h"
#include "satSolver.h"
#include "ssw.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

// equivalence classes
typedef struct Ssw_Cla_t_ Ssw_Cla_t;

// manager
typedef struct Ssw_Man_t_ Ssw_Man_t;
struct Ssw_Man_t_
{
    // parameters
    Ssw_Pars_t *     pPars;          // parameters
    int              nFrames;        // for quick lookup
    // AIGs used in the package
    Aig_Man_t *      pAig;           // user-given AIG
    Aig_Man_t *      pFrames;        // final AIG
    Aig_Obj_t **     pNodeToFraig;   // mapping of AIG nodes into FRAIG nodes
    // equivalence classes
    Ssw_Cla_t *      ppClasses;      // equivalence classes of nodes
//    Aig_Obj_t **     pReprsProved;   // equivalences proved
    int              fRefined;       // is set to 1 when refinement happens
    // SAT solving
    sat_solver *     pSat;           // recyclable SAT solver
    int              nSatVars;       // the counter of SAT variables
    int *            pSatVars;       // mapping of each node into its SAT var
    Vec_Ptr_t *      vFanins;        // fanins of the CNF node
    Vec_Ptr_t *      vSimRoots;      // the roots of cand const 1 nodes to simulate
    Vec_Ptr_t *      vSimClasses;    // the roots of cand equiv classes to simulate
    // constraints
    int              nConstrTotal;   // the number of total constraints
    int              nConstrReduced; // the number of reduced constraints
    int              nStragers;
    // SAT calls statistics
    int              nSatCalls;      // the number of SAT calls
    int              nSatProof;      // the number of proofs
    int              nSatFailsReal;  // the number of timeouts
    int              nSatCallsUnsat; // the number of unsat SAT calls
    int              nSatCallsSat;   // the number of sat SAT calls
    // runtime stats
    int              timeBmc;        // bounded model checking
    int              timeReduce;     // speculative reduction
    int              timeSimSat;     // simulation of the counter-examples
    int              timeSat;        // solving SAT
    int              timeSatSat;     // sat
    int              timeSatUnsat;   // unsat
    int              timeSatUndec;   // undecided
    int              timeOther;      // other runtime
    int              timeTotal;      // total runtime
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

static inline int  Ssw_ObjSatNum( Ssw_Man_t * p, Aig_Obj_t * pObj )             { return p->pSatVars[pObj->Id]; }
static inline void Ssw_ObjSetSatNum( Ssw_Man_t * p, Aig_Obj_t * pObj, int Num ) { p->pSatVars[pObj->Id] = Num;  }

static inline int  Ssw_ObjIsConst1Cand( Aig_Man_t * pAig, Aig_Obj_t * pObj ) 
{
    return Aig_ObjRepr(pAig, pObj) == Aig_ManConst1(pAig);
}
static inline void Ssw_ObjSetConst1Cand( Aig_Man_t * pAig, Aig_Obj_t * pObj ) 
{
    assert( !Ssw_ObjIsConst1Cand( pAig, pObj ) );
    Aig_ObjSetRepr( pAig, pObj, Aig_ManConst1(pAig) );
}

static inline Aig_Obj_t * Ssw_ObjFraig( Ssw_Man_t * p, Aig_Obj_t * pObj, int i )                       { return p->pNodeToFraig[p->nFrames*pObj->Id + i];  }
static inline void        Ssw_ObjSetFraig( Ssw_Man_t * p, Aig_Obj_t * pObj, int i, Aig_Obj_t * pNode ) { p->pNodeToFraig[p->nFrames*pObj->Id + i] = pNode; }

static inline Aig_Obj_t * Ssw_ObjChild0Fra( Ssw_Man_t * p, Aig_Obj_t * pObj, int i ) { assert( !Aig_IsComplement(pObj) ); return Aig_ObjFanin0(pObj)? Aig_NotCond(Ssw_ObjFraig(p, Aig_ObjFanin0(pObj), i), Aig_ObjFaninC0(pObj)) : NULL;  }
static inline Aig_Obj_t * Ssw_ObjChild1Fra( Ssw_Man_t * p, Aig_Obj_t * pObj, int i ) { assert( !Aig_IsComplement(pObj) ); return Aig_ObjFanin1(pObj)? Aig_NotCond(Ssw_ObjFraig(p, Aig_ObjFanin1(pObj), i), Aig_ObjFaninC1(pObj)) : NULL;  }

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== sswAig.c ===================================================*/
extern Aig_Man_t *   Ssw_FramesWithClasses( Ssw_Man_t * p );
/*=== sswClass.c =================================================*/
extern Ssw_Cla_t *   Ssw_ClassesStart( Aig_Man_t * pAig );
extern void          Ssw_ClassesSetData( Ssw_Cla_t * p, void * pManData,
                         unsigned (*pFuncNodeHash)(void *,Aig_Obj_t *),
                         int (*pFuncNodeIsConst)(void *,Aig_Obj_t *),
                         int (*pFuncNodesAreEqual)(void *,Aig_Obj_t *, Aig_Obj_t *) );
extern void          Ssw_ClassesStop( Ssw_Cla_t * p );
extern int           Ssw_ClassesCand1Num( Ssw_Cla_t * p );
extern int           Ssw_ClassesClassNum( Ssw_Cla_t * p );
extern int           Ssw_ClassesLitNum( Ssw_Cla_t * p );
extern Aig_Obj_t **  Ssw_ClassesReadClass( Ssw_Cla_t * p, Aig_Obj_t * pRepr, int * pnSize );
extern void          Ssw_ClassesCheck( Ssw_Cla_t * p );
extern void          Ssw_ClassesPrint( Ssw_Cla_t * p, int fVeryVerbose );
extern void          Ssw_ClassesRemoveNode( Ssw_Cla_t * p, Aig_Obj_t * pObj );
extern void          Ssw_ClassesPrepare( Ssw_Cla_t * p, int fLatchCorr, int nMaxLevs );
extern Ssw_Cla_t *   Ssw_ClassesPrepareSimple( Aig_Man_t * pAig, int fLatchCorr, int nMaxLevs );
extern int           Ssw_ClassesRefine( Ssw_Cla_t * p );
extern int           Ssw_ClassesRefineOneClass( Ssw_Cla_t * p, Aig_Obj_t * pRepr, int fRecursive );
extern int           Ssw_ClassesRefineConst1Group( Ssw_Cla_t * p, Vec_Ptr_t * vRoots, int fRecursive );
extern int           Ssw_ClassesRefineConst1( Ssw_Cla_t * p, int fRecursive );
/*=== sswCnf.c ===================================================*/
extern void          Ssw_CnfNodeAddToSolver( Ssw_Man_t * p, Aig_Obj_t * pObj );
/*=== sswMan.c ===================================================*/
extern Ssw_Man_t *   Ssw_ManCreate( Aig_Man_t * pAig, Ssw_Pars_t * pPars );
extern void          Ssw_ManCleanup( Ssw_Man_t * p );
extern void          Ssw_ManStop( Ssw_Man_t * p );
extern void          Ssw_ManStartSolver( Ssw_Man_t * p );
/*=== sswSat.c ===================================================*/
extern int           Ssw_NodesAreEquiv( Ssw_Man_t * p, Aig_Obj_t * pOld, Aig_Obj_t * pNew );
extern int           Ssw_NodesAreConstrained( Ssw_Man_t * p, Aig_Obj_t * pOld, Aig_Obj_t * pNew );
/*=== sswSimSat.c ===================================================*/
extern void          Ssw_ManResimulateCex( Ssw_Man_t * p, Aig_Obj_t * pObj, Aig_Obj_t * pRepr, int f );
extern void          Ssw_ManResimulateCexTotal( Ssw_Man_t * p, Aig_Obj_t * pObj, Aig_Obj_t * pRepr, int f );
/*=== sswSweep.c ===================================================*/
extern int           Ssw_ManSweepBmc( Ssw_Man_t * p );
extern int           Ssw_ManSweep( Ssw_Man_t * p );

#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

