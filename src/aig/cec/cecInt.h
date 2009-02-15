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

#include "satSolver.h"
#include "bar.h"
#include "gia.h"
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

// simulation pattern manager
typedef struct Cec_ManPat_t_ Cec_ManPat_t;
struct Cec_ManPat_t_
{
    Vec_Int_t *      vPattern1;      // pattern in terms of primary inputs
    Vec_Int_t *      vPattern2;      // pattern in terms of primary inputs
    Vec_Str_t *      vStorage;       // storage for compressed patterns
    int              iStart;         // position in the array where recent patterns begin
    int              nPats;          // total number of recent patterns
    int              nPatsAll;       // total number of all patterns
    int              nPatLits;       // total number of literals in recent patterns
    int              nPatLitsAll;    // total number of literals in all patterns
    int              nPatLitsMin;    // total number of literals in minimized recent patterns
    int              nPatLitsMinAll; // total number of literals in minimized all patterns
    int              nSeries;        // simulation series
    int              fVerbose;       // verbose stats
    // runtime statistics
    int              timeFind;       // detecting the pattern  
    int              timeShrink;     // minimizing the pattern
    int              timeVerify;     // verifying the result of minimisation
    int              timeSort;       // sorting literals 
    int              timePack;       // packing into sim info structures 
    int              timeTotal;      // total runtime  
};

// SAT solving manager
typedef struct Cec_ManSat_t_ Cec_ManSat_t;
struct Cec_ManSat_t_
{
    // parameters
    Cec_ParSat_t *   pPars;          
    // AIGs used in the package
    Gia_Man_t *      pAig;           // the AIG whose outputs are considered
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
    int              nSatTotal;      // the number of calls
    // conflicts
    int              nConfUnsat;
    int              nConfSat;
    int              nConfUndec;
    // runtime stats
    int              timeSatUnsat;   // unsat
    int              timeSatSat;     // sat
    int              timeSatUndec;   // undecided
    int              timeTotal;      // total runtime
};

// combinational sweeping object
typedef struct Cec_ObjCsw_t_ Cec_ObjCsw_t;
struct Cec_ObjCsw_t_
{
    int              iRepr;          // representative node
    unsigned         iNext   : 30;   // next node in the class
    unsigned         iProved :  1;   // this node is proved
    unsigned         iFailed :  1;   // this node is failed
    unsigned         SimNum;         // simulation info number
};

// combinational simulation manager
typedef struct Cec_ManCsw_t_ Cec_ManCsw_t;
struct Cec_ManCsw_t_
{
    // parameters
    Gia_Man_t *      pAig;           // the AIG to be used for simulation
    Cec_ParCsw_t *   pPars;          // SAT sweeping parameters 
    int              nWords;         // the number of simulation words
    // equivalence classes
    Cec_ObjCsw_t *   pObjs;          // objects used for SAT sweeping
    // recycable memory
    unsigned *       pMems;          // allocated simulaton memory
    int              nWordsAlloc;    // the number of allocated entries
    int              nMems;          // the number of used entries  
    int              nMemsMax;       // the max number of used entries 
    int              MemFree;        // next free entry
    // temporaries
    Vec_Int_t *      vClassOld;      // old class numbers
    Vec_Int_t *      vClassNew;      // new class numbers
    Vec_Int_t *      vClassTemp;     // temporary storage
    Vec_Int_t *      vRefinedC;      // refined const reprs
    // simulation patterns
    Vec_Int_t *      vXorNodes;      // nodes used in speculative reduction
    int              nAllProved;     // total number of proved nodes
    int              nAllDisproved;  // total number of disproved nodes
    int              nAllFailed;     // total number of failed nodes
    // runtime stats
    int              timeSim;        // unsat
    int              timeSat;        // sat
    int              timeTotal;      // total runtime
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== cecCore.c ============================================================*/
/*=== cecClass.c ============================================================*/
extern int                  Cec_ManCswCountLitsAll( Cec_ManCsw_t * p );
extern int *                Cec_ManCswDeriveReprs( Cec_ManCsw_t * p );
extern Gia_Man_t *          Cec_ManCswSpecReduction( Cec_ManCsw_t * p );
extern Gia_Man_t *          Cec_ManCswSpecReductionProved( Cec_ManCsw_t * p );
extern Gia_Man_t *          Cec_ManCswDupWithClasses( Cec_ManCsw_t * p );
extern int                  Cec_ManCswClassesPrepare( Cec_ManCsw_t * p );
extern int                  Cec_ManCswClassesUpdate( Cec_ManCsw_t * p, Cec_ManPat_t * pPat, Gia_Man_t * pNew );
/*=== cecMan.c ============================================================*/
extern Cec_ManCsw_t *       Cec_ManCswStart( Gia_Man_t * pAig, Cec_ParCsw_t *  pPars );  
extern void                 Cec_ManCswStop( Cec_ManCsw_t * p );
extern Cec_ManPat_t *       Cec_ManPatStart();
extern void                 Cec_ManPatPrintStats( Cec_ManPat_t * p );
extern void                 Cec_ManPatStop( Cec_ManPat_t * p );
extern Cec_ManSat_t *       Cec_ManSatCreate( Gia_Man_t * pAig, Cec_ParSat_t * pPars );
extern void                 Cec_ManSatPrintStats( Cec_ManSat_t * p );
extern void                 Cec_ManSatStop( Cec_ManSat_t * p );
/*=== cecPat.c ============================================================*/
extern void                 Cec_ManPatSavePattern( Cec_ManPat_t *  pPat, Cec_ManSat_t *  p, Gia_Obj_t * pObj );
extern Vec_Ptr_t *          Cec_ManPatCollectPatterns( Cec_ManPat_t *  pMan, int nInputs, int nWords );
/*=== cecSolve.c ============================================================*/
extern int                  Cec_ObjSatVarValue( Cec_ManSat_t * p, Gia_Obj_t * pObj );
extern void                 Cec_ManSatSolve( Cec_ManPat_t * pPat, Gia_Man_t * pAig, Cec_ParSat_t * pPars );
/*=== cecUtil.c ============================================================*/

#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

