/**CFile****************************************************************

  FileName    [pdrInt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Property driven reachability.]

  Synopsis    [Internal declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 20, 2010.]

  Revision    [$Id: pdrInt.h,v 1.00 2010/11/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef ABC__sat__pdr__pdrInt_h
#define ABC__sat__pdr__pdrInt_h

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "src/aig/saig/saig.h"
#include "src/sat/cnf/cnf.h"
#include "src/sat/bsat/satSolver.h"
#include "pdr.h" 

ABC_NAMESPACE_HEADER_START

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////
             
////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Pdr_Set_t_ Pdr_Set_t;
struct Pdr_Set_t_
{
    word        Sign;      // signature
    int         nRefs;     // ref counter
    int         nTotal;    // total literals
    int         nLits;     // num flop literals
    int         Lits[0];
};

typedef struct Pdr_Obl_t_ Pdr_Obl_t;
struct Pdr_Obl_t_
{
    int         iFrame;    // time frame
    int         prio;      // priority
    int         nRefs;     // reference counter
    Pdr_Set_t * pState;    // state cube
    Pdr_Obl_t * pNext;     // next one
    Pdr_Obl_t * pLink;     // queue link
};

typedef struct Pdr_Man_t_ Pdr_Man_t;
struct Pdr_Man_t_
{
    // input problem
    Pdr_Par_t * pPars;     // parameters
    Aig_Man_t * pAig;      // user's AIG
    // static CNF representation
    Cnf_Dat_t * pCnf1;     // CNF for this AIG
    Vec_Int_t * vVar2Reg;  // mapping of SAT var into registers
    // dynamic CNF representation
    Cnf_Dat_t * pCnf2;     // CNF for this AIG
    Vec_Int_t** pvId2Vars; // for each used ObjId, maps frame into SAT var
    Vec_Ptr_t * vVar2Ids;  // for each used frame, maps SAT var into ObjId
    // data representation
    Vec_Ptr_t * vSolvers;  // SAT solvers
    Vec_Vec_t * vClauses;  // clauses by timeframe
    Pdr_Obl_t * pQueue;    // proof obligations
    int *       pOrder;    // ordering of the lits
    Vec_Int_t * vActVars;  // the counter of activation variables
    // internal use
    Vec_Int_t * vPrio;     // priority flops
    Vec_Int_t * vLits;     // array of literals
    Vec_Int_t * vCiObjs;   // cone leaves
    Vec_Int_t * vCoObjs;   // cone roots
    Vec_Int_t * vCiVals;   // cone leaf values
    Vec_Int_t * vCoVals;   // cone root values
    Vec_Int_t * vNodes;    // cone nodes
    Vec_Int_t * vUndo;     // cone undos
    Vec_Int_t * vVisits;   // intermediate
    Vec_Int_t * vCi2Rem;   // CIs to be removed
    Vec_Int_t * vRes;      // final result
    Vec_Int_t * vSuppLits; // support literals
    Pdr_Set_t * pCubeJust; // justification
    // statistics
    int         nBlocks;   // the number of times blockState was called
    int         nObligs;   // the number of proof obligations derived
    int         nCubes;    // the number of cubes derived
    int         nCalls;    // the number of SAT calls
    int         nCallsS;   // the number of SAT calls (sat)
    int         nCallsU;   // the number of SAT calls (unsat)
    int         nStarts;   // the number of SAT solver restarts
    int         nFrames;   // frames explored
    int         nCasesSS;
    int         nCasesSU;
    int         nCasesUS;
    int         nCasesUU;
    // runtime
    int         timeStart;
    int         timeToStop;
    // time stats
    int         tSat;
    int         tSatSat;
    int         tSatUnsat;
    int         tGeneral;
    int         tPush;
    int         tTsim;
    int         tContain;
    int         tCnf;
    int         tTotal;
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

static inline sat_solver * Pdr_ManSolver( Pdr_Man_t * p, int k )  { return (sat_solver *)Vec_PtrEntry(p->vSolvers, k); }

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== pdrCex.c ==========================================================*/
extern Abc_Cex_t *     Pdr_ManDeriveCex( Pdr_Man_t * p );
/*=== pdrCnf.c ==========================================================*/
extern int             Pdr_ObjSatVar( Pdr_Man_t * p, int k, Aig_Obj_t * pObj );
extern int             Pdr_ObjRegNum( Pdr_Man_t * p, int k, int iSatVar );
extern int             Pdr_ManFreeVar( Pdr_Man_t * p, int k );
extern sat_solver *    Pdr_ManNewSolver( sat_solver * pSat, Pdr_Man_t * p, int k, int fInit );
/*=== pdrCore.c ==========================================================*/
extern int             Pdr_ManCheckContainment( Pdr_Man_t * p, int k, Pdr_Set_t * pSet );
/*=== pdrInv.c ==========================================================*/
extern void            Pdr_ManPrintProgress( Pdr_Man_t * p, int fClose, int Time );
extern void            Pdr_ManPrintClauses( Pdr_Man_t * p, int kStart );
extern void            Pdr_ManDumpClauses( Pdr_Man_t * p, char * pFileName, int fProved );
extern void            Pdr_ManReportInvariant( Pdr_Man_t * p );
extern void            Pdr_ManVerifyInvariant( Pdr_Man_t * p );
/*=== pdrMan.c ==========================================================*/
extern Pdr_Man_t *     Pdr_ManStart( Aig_Man_t * pAig, Pdr_Par_t * pPars, Vec_Int_t * vPrioInit );
extern void            Pdr_ManStop( Pdr_Man_t * p );
extern Abc_Cex_t *     Pdr_ManDeriveCex( Pdr_Man_t * p );
/*=== pdrSat.c ==========================================================*/
extern sat_solver *    Pdr_ManCreateSolver( Pdr_Man_t * p, int k );
extern sat_solver *    Pdr_ManFetchSolver( Pdr_Man_t * p, int k );
extern void            Pdr_ManSetPropertyOutput( Pdr_Man_t * p, int k );
extern Vec_Int_t *     Pdr_ManCubeToLits( Pdr_Man_t * p, int k, Pdr_Set_t * pCube, int fCompl, int fNext );
extern Vec_Int_t *     Pdr_ManLitsToCube( Pdr_Man_t * p, int k, int * pArray, int nArray );
extern void            Pdr_ManSolverAddClause( Pdr_Man_t * p, int k, Pdr_Set_t * pCube );
extern void            Pdr_ManCollectValues( Pdr_Man_t * p, int k, Vec_Int_t * vObjIds, Vec_Int_t * vValues );
extern int             Pdr_ManCheckCubeCs( Pdr_Man_t * p, int k, Pdr_Set_t * pCube );
extern int             Pdr_ManCheckCube( Pdr_Man_t * p, int k, Pdr_Set_t * pCube, Pdr_Set_t ** ppPred, int nConfLimit );
/*=== pdrTsim.c ==========================================================*/
extern Pdr_Set_t *     Pdr_ManTernarySim( Pdr_Man_t * p, int k, Pdr_Set_t * pCube );
/*=== pdrUtil.c ==========================================================*/
extern Pdr_Set_t *     Pdr_SetAlloc( int nSize );
extern Pdr_Set_t *     Pdr_SetCreate( Vec_Int_t * vLits, Vec_Int_t * vPiLits );
extern Pdr_Set_t *     Pdr_SetCreateFrom( Pdr_Set_t * pSet, int iRemove );
extern Pdr_Set_t *     Pdr_SetCreateSubset( Pdr_Set_t * pSet, int * pLits, int nLits );
extern Pdr_Set_t *     Pdr_SetDup( Pdr_Set_t * pSet );
extern Pdr_Set_t *     Pdr_SetRef( Pdr_Set_t * p );
extern void            Pdr_SetDeref( Pdr_Set_t * p );
extern int             Pdr_SetContains( Pdr_Set_t * pOld, Pdr_Set_t * pNew );
extern int             Pdr_SetContainsSimple( Pdr_Set_t * pOld, Pdr_Set_t * pNew );
extern int             Pdr_SetIsInit( Pdr_Set_t * p, int iRemove );
extern void            Pdr_SetPrint( FILE * pFile, Pdr_Set_t * p, int nRegs, Vec_Int_t * vFlopCounts );
extern int             Pdr_SetCompare( Pdr_Set_t ** pp1, Pdr_Set_t ** pp2 );
extern Pdr_Obl_t *     Pdr_OblStart( int k, int prio, Pdr_Set_t * pState, Pdr_Obl_t * pNext );
extern Pdr_Obl_t *     Pdr_OblRef( Pdr_Obl_t * p );
extern void            Pdr_OblDeref( Pdr_Obl_t * p );
extern int             Pdr_QueueIsEmpty( Pdr_Man_t * p );
extern Pdr_Obl_t *     Pdr_QueueHead( Pdr_Man_t * p );
extern Pdr_Obl_t *     Pdr_QueuePop( Pdr_Man_t * p );
extern void            Pdr_QueuePush( Pdr_Man_t * p, Pdr_Obl_t * pObl );
extern void            Pdr_QueuePrint( Pdr_Man_t * p );
extern void            Pdr_QueueStop( Pdr_Man_t * p );
extern int             Pdr_ManCubeJust( Pdr_Man_t * p, int k, Pdr_Set_t * pCube );

ABC_NAMESPACE_HEADER_END


#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

