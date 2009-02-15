/**CFile****************************************************************

  FileName    [cecInt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinatinoal equivalence checking.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cecInt.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __CEC_INT_H__
#define __CEC_INT_H__

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "aig.h"
#include "satSolver.h"
#include "bar.h"
#include "cec.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

#ifdef __cplusplus
extern "C" {
#endif

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Cec_ManSat_t_ Cec_ManSat_t;
struct Cec_ManSat_t_
{
    // parameters
    Cec_ParSat_t *   pPars;          
    // AIGs used in the package
    Aig_Man_t *      pAig;           // the AIG whose outputs are considered
    Vec_Int_t *      vStatus;        // status for each output
    // SAT solving
    sat_solver *     pSat;           // recyclable SAT solver
    int              nSatVars;       // the counter of SAT variables
    int *            pSatVars;       // mapping of each node into its SAT var
    Vec_Ptr_t *      vUsedNodes;     // nodes whose SAT vars are assigned
    int              nRecycles;      // the number of times SAT solver was recycled
    int              nCallsSince;    // the number of calls since the last recycle
    Vec_Ptr_t *      vFanins;        // fanins of the CNF node
    // SAT calls statistics
    int              nSatUnsat;      // the number of proofs
    int              nSatSat;        // the number of failure
    int              nSatUndec;      // the number of timeouts
    // runtime stats
    int              timeSatUnsat;   // unsat
    int              timeSatSat;     // sat
    int              timeSatUndec;   // undecided
    int              timeTotal;      // total runtime
};

typedef struct Cec_ManCec_t_ Cec_ManCec_t;
struct Cec_ManCec_t_
{
    // parameters
    Cec_ParCec_t *   pPars;          
    // AIGs used in the package
    Aig_Man_t *      pAig;           // the miter for equivalence checking
    // mapping of PI/PO nodes

    // counter-example
    int *            pCex;           // counter-example
    int              iOutput;        // the output for this counter-example

    // statistics

};

typedef struct Cec_MtrStatus_t_ Cec_MtrStatus_t;
struct Cec_MtrStatus_t_
{
    int         nInputs;  // the total number of inputs
    int         nNodes;   // the total number of nodes
    int         nOutputs; // the total number of outputs
    int         nUnsat;   // the number of UNSAT outputs
    int         nSat;     // the number of SAT outputs
    int         nUndec;   // the number of undecided outputs
    int         iOut;     // the satisfied output
};

// combinational simulation manager
typedef struct Caig_Man_t_ Caig_Man_t;
struct Caig_Man_t_
{
    // parameters
    Aig_Man_t *     pAig;         // the AIG to be used for simulation
    int             nWords;       // the number of simulation words
    // AIG representation
    int             nPis;         // the number of primary inputs
    int             nPos;         // the number of primary outputs
    int             nNodes;       // the number of internal nodes
    int             nObjs;        // nPis + nNodes + nPos + 1
    int *           pFans0;       // fanin0 for all objects
    int *           pFans1;       // fanin1 for all objects
    // simulation info
    int *           pRefs;        // reference counter for each node
    unsigned *      pSims;        // simlulation information for each node
    // recycable memory
    unsigned *      pMems;        // allocated simulaton memory
    int             nWordsAlloc;  // the number of allocated entries
    int             nMems;        // the number of used entries  
    int             nMemsMax;     // the max number of used entries 
    int             MemFree;      // next ABC_FREE entry
    // equivalence class representation
    int *           pReprs;       // representatives of each node
    int *           pNexts;       // nexts for each node
    // temporaries
    Vec_Ptr_t *     vSims;        // pointers to sim info
    Vec_Int_t *     vClassOld;    // old class numbers
    Vec_Int_t *     vClassNew;    // new class numbers
    Vec_Int_t *     vRefinedC;    // refined const reprs
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

static inline int  Cec_Var2Lit( int Var, int fCompl )  { return Var + Var + fCompl; }
static inline int  Cec_Lit2Var( int Lit )              { return Lit >> 1;           }
static inline int  Cec_LitIsCompl( int Lit )           { return Lit & 1;            }
static inline int  Cec_LitNot( int Lit )               { return Lit ^ 1;            }
static inline int  Cec_LitNotCond( int Lit, int c )    { return Lit ^ (int)(c > 0); }
static inline int  Cec_LitRegular( int Lit )           { return Lit & ~01;          }

static inline int  Cec_ObjSatNum( Cec_ManSat_t * p, Aig_Obj_t * pObj )             { return p->pSatVars[pObj->Id]; }
static inline void Cec_ObjSetSatNum( Cec_ManSat_t * p, Aig_Obj_t * pObj, int Num ) { p->pSatVars[pObj->Id] = Num;  }

static inline Aig_Obj_t * Cec_ObjFraig( Aig_Obj_t * pObj )                       { return pObj->pData;  }
static inline void        Cec_ObjSetFraig( Aig_Obj_t * pObj, Aig_Obj_t * pNode ) { pObj->pData = pNode; }

static inline int  Cec_ObjIsConst1Cand( Aig_Man_t * pAig, Aig_Obj_t * pObj ) 
{
    return Aig_ObjRepr(pAig, pObj) == Aig_ManConst1(pAig);
}
static inline void Cec_ObjSetConst1Cand( Aig_Man_t * pAig, Aig_Obj_t * pObj ) 
{
    assert( !Cec_ObjIsConst1Cand( pAig, pObj ) );
    Aig_ObjSetRepr( pAig, pObj, Aig_ManConst1(pAig) );
}

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== cecAig.c ==========================================================*/
extern Aig_Man_t *     Cec_Duplicate( Aig_Man_t * p );
extern Aig_Man_t *     Cec_DeriveMiter( Aig_Man_t * p0, Aig_Man_t * p1 );
/*=== cecClass.c ==========================================================*/
extern Aig_Man_t *     Caig_ManSpecReduce( Caig_Man_t * p, int nLevels );
extern int             Caig_ManCompareEqual( unsigned * p0, unsigned * p1, int nWords );
extern int             Caig_ManCompareConst( unsigned * p, int nWords );
extern void            Caig_ManCollectSimsNormal( Caig_Man_t * p, int i );
extern int             Caig_ManClassRefineOne( Caig_Man_t * p, int i, Vec_Ptr_t * vSims );
extern void            Caig_ManProcessRefined( Caig_Man_t * p, Vec_Int_t * vRefined );
extern void            Caig_ManPrintClasses( Caig_Man_t * p, int fVerbose );
extern Caig_Man_t *    Caig_ManClassesPrepare( Aig_Man_t * pAig, int nWords, int nIters );
/*=== cecCnf.c ==========================================================*/
extern void            Cec_CnfNodeAddToSolver( Cec_ManSat_t * p, Aig_Obj_t * pObj );
/*=== cecSat.c ==========================================================*/
extern Cec_MtrStatus_t Cec_SatSolveOutputs( Aig_Man_t * pAig, Cec_ParSat_t * pPars );
/*=== cecSim.c ==========================================================*/
extern Caig_Man_t *    Caig_ManCreate( Aig_Man_t * pAig );
extern void            Caig_ManDelete( Caig_Man_t * p );
extern void            Caig_ManSimMemRelink( Caig_Man_t * p );
extern unsigned *      Caig_ManSimRead( Caig_Man_t * p, int i );
extern unsigned *      Caig_ManSimRef( Caig_Man_t * p, int i );
extern unsigned *      Caig_ManSimDeref( Caig_Man_t * p, int i );
extern void            Caig_ManSimulateRound( Caig_Man_t * p, Vec_Ptr_t * vInfoCis, Vec_Ptr_t * vInfoCos );
extern int             Cec_ManSimulate( Aig_Man_t * pAig, int nWords, int nIters, int TimeLimit, int fMiter, int fVerbose );
/*=== cecStatus.c ==========================================================*/
extern int             Cec_OutputStatus( Aig_Man_t * p, Aig_Obj_t * pObj );
extern Cec_MtrStatus_t Cec_MiterStatus( Aig_Man_t * p );
extern Cec_MtrStatus_t Cec_MiterStatusTrivial( Aig_Man_t * p );
extern void            Cec_MiterStatusPrint( Cec_MtrStatus_t S, char * pString, int Time );
/*=== cecSweep.c ==========================================================*/
extern void            Cec_ManSatSweepInt( Caig_Man_t * pMan, Cec_ParCsw_t * pPars );
extern Aig_Man_t *     Cec_ManSatSweep( Aig_Man_t * pAig, Cec_ParCsw_t * pPars );

#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

