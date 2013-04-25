/**CFile****************************************************************

  FileName    [sscInt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Choice computation for tech-mapping.]

  Synopsis    [Internal declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 29, 2008.]

  Revision    [$Id: sscInt.h,v 1.00 2008/07/29 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef ABC__aig__ssc__sscInt_h
#define ABC__aig__ssc__sscInt_h


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "aig/gia/gia.h"
#include "sat/bsat/satSolver.h"
#include "ssc.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////



ABC_NAMESPACE_HEADER_START


////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

// choicing manager
typedef struct Ssc_Man_t_ Ssc_Man_t;
struct Ssc_Man_t_
{
    // parameters
    Ssc_Pars_t *     pPars;          // choicing parameters
    Gia_Man_t *      pAig;           // subject AIG
    Gia_Man_t *      pCare;          // care set AIG
    Gia_Man_t *      pFraig;         // resulting AIG
    Vec_Int_t *      vPivot;         // one SAT pattern
    // SAT solving
    sat_solver *     pSat;           // recyclable SAT solver
    Vec_Int_t *      vSatVars;       // mapping of each node into its SAT var
    Vec_Int_t *      vUsedNodes;     // nodes whose SAT vars are assigned
    int              nRecycles;      // the number of times SAT solver was recycled
    int              nCallsSince;    // the number of calls since the last recycle
    Vec_Int_t *      vFanins;        // fanins of the CNF node
    // SAT calls statistics
    int              nSatCalls;      // the number of SAT calls
    int              nSatProof;      // the number of proofs
    int              nSatFailsReal;  // the number of timeouts
    int              nSatCallsUnsat; // the number of unsat SAT calls
    int              nSatCallsSat;   // the number of sat SAT calls
    // runtime stats
    clock_t          timeSimInit;    // simulation and class computation
    clock_t          timeSimSat;     // simulation of the counter-examples
    clock_t          timeSat;        // solving SAT
    clock_t          timeSatSat;     // sat
    clock_t          timeSatUnsat;   // unsat
    clock_t          timeSatUndec;   // undecided
    clock_t          timeChoice;     // choice computation
    clock_t          timeOther;      // other runtime
    clock_t          timeTotal;      // total runtime
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

static inline int  Ssc_ObjSatNum( Ssc_Man_t * p, Gia_Obj_t * pObj )             { return Vec_IntEntry(p->vSatVars, Gia_ObjId(p->pFraig, pObj));     }
static inline void Ssc_ObjSetSatNum( Ssc_Man_t * p, Gia_Obj_t * pObj, int Num ) { Vec_IntWriteEntry(p->vSatVars, Gia_ObjId(p->pFraig, pObj), Num);  }

static inline int  Ssc_ObjFraig( Ssc_Man_t * p, Gia_Obj_t * pObj )              { return pObj->Value;           }
static inline void Ssc_ObjSetFraig( Gia_Obj_t * pObj, int iNode )               { pObj->Value = iNode;          }

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== sscClass.c =================================================*/
extern int           Ssc_GiaClassesRefine( Gia_Man_t * p );
/*=== sscCnf.c ===================================================*/
extern void          Ssc_CnfNodeAddToSolver( Ssc_Man_t * p, Gia_Obj_t * pObj );
/*=== sscCore.c ==================================================*/
/*=== sscSat.c ===================================================*/
extern int           Ssc_NodesAreEquiv( Ssc_Man_t * p, Gia_Obj_t * pObj1, Gia_Obj_t * pObj2 );
extern void          Ssc_ManSatSolverRecycle( Ssc_Man_t * p );
extern void          Ssc_ManStartSolver( Ssc_Man_t * p );
extern Vec_Int_t *   Ssc_ManFindPivotSat( Ssc_Man_t * p );
/*=== sscSim.c ===================================================*/
extern void          Ssc_GiaRandomPiPattern( Gia_Man_t * p, int nWords, Vec_Int_t * vPivot );
extern void          Ssc_GiaSimRound( Gia_Man_t * p );
extern Vec_Int_t *   Ssc_GiaFindPivotSim( Gia_Man_t * p );
/*=== sscUtil.c ===================================================*/
extern Gia_Man_t *   Ssc_GenerateOneHot( int nVars );


ABC_NAMESPACE_HEADER_END



#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

