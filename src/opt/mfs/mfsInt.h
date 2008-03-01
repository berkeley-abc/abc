/**CFile****************************************************************

  FileName    [mfsInt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [The good old minimization with complete don't-cares.]

  Synopsis    [Internal declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: mfsInt.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __MFS_INT_H__
#define __MFS_INT_H__

#ifdef __cplusplus
extern "C" {
#endif

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "abc.h"
#include "mfs.h"
#include "aig.h"
#include "cnf.h"
#include "satSolver.h"
#include "satStore.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

#define MFS_FANIN_MAX   10

typedef struct Mfs_Man_t_ Mfs_Man_t;
struct Mfs_Man_t_
{
    // input data
    Mfs_Par_t *         pPars;
    Abc_Ntk_t *         pNtk;
    Aig_Man_t *         pCare;
    Vec_Ptr_t *         vSuppsInv;
    int                 nFaninMax;
    // intermeditate data for the node
    Vec_Ptr_t *         vRoots;    // the roots of the window
    Vec_Ptr_t *         vSupp;     // the support of the window
    Vec_Ptr_t *         vNodes;    // the internal nodes of the window
    Vec_Ptr_t *         vDivs;     // the divisors of the node
    Vec_Int_t *         vDivLits;  // the SAT literals of divisor nodes
    Vec_Int_t *         vProjVars; // the projection variables
    // intermediate simulation data
    Vec_Ptr_t *         vDivCexes; // the counter-example for dividors
    int                 nDivWords; // the number of words
    int                 nCexes;    // the numbe rof current counter-examples
    int                 nSatCalls; 
    int                 nSatCexes;
    // solving data
    Aig_Man_t *         pAigWin;   // window AIG with constraints
    Cnf_Dat_t *         pCnf;      // the CNF for the window
    sat_solver *        pSat;      // the SAT solver used 
    Int_Man_t *         pMan;      // interpolation manager;
    Vec_Int_t *         vMem;      // memory for intermediate SOPs
    Vec_Vec_t *         vLevels;   // levelized structure for updating
    Vec_Ptr_t *         vFanins;   // the new set of fanins
    // the result of solving
    int                 nFanins;   // the number of fanins
    int                 nWords;    // the number of words
    int                 nCares;    // the number of care minterms
    unsigned            uCare[(MFS_FANIN_MAX<=5)?1:1<<(MFS_FANIN_MAX-5)];  // the computed care-set
    // performance statistics
    int                 nNodesTried;
    int                 nNodesResub;
    int                 nMintsCare;
    int                 nMintsTotal;
    int                 nNodesBad;
    int                 nTotalDivs;
    int                 nTimeOuts;
    // node/edge stats
    int                 nTotalNodesBeg;
    int                 nTotalNodesEnd;
    int                 nTotalEdgesBeg;
    int                 nTotalEdgesEnd;
    // statistics
    int                 timeWin;
    int                 timeDiv;
    int                 timeAig;
    int                 timeCnf;
    int                 timeSat;
    int                 timeInt;
    int                 timeTotal;
};

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== mfsDiv.c ==========================================================*/
extern Vec_Ptr_t *      Abc_MfsComputeDivisors( Mfs_Man_t * p, Abc_Obj_t * pNode, int nLevDivMax );
/*=== mfsInter.c ==========================================================*/
extern sat_solver *     Abc_MfsCreateSolverResub( Mfs_Man_t * p, int * pCands, int nCands );
extern Hop_Obj_t *      Abc_NtkMfsInterplate( Mfs_Man_t * p, int * pCands, int nCands );
/*=== mfsMan.c ==========================================================*/
extern Mfs_Man_t *      Mfs_ManAlloc( Mfs_Par_t * pPars );
extern void             Mfs_ManStop( Mfs_Man_t * p );
extern void             Mfs_ManClean( Mfs_Man_t * p );
/*=== mfsResub.c ==========================================================*/
extern void             Abc_NtkMfsPrintResubStats( Mfs_Man_t * p );
extern int              Abc_NtkMfsEdgeSwapEval( Mfs_Man_t * p, Abc_Obj_t * pNode );
extern int              Abc_NtkMfsResubNode( Mfs_Man_t * p, Abc_Obj_t * pNode );
extern int              Abc_NtkMfsResubNode2( Mfs_Man_t * p, Abc_Obj_t * pNode );
/*=== mfsSat.c ==========================================================*/
extern void             Abc_NtkMfsSolveSat( Mfs_Man_t * p, Abc_Obj_t * pNode );
/*=== mfsStrash.c ==========================================================*/
extern Aig_Man_t *      Abc_NtkConstructAig( Mfs_Man_t * p, Abc_Obj_t * pNode );
/*=== mfsWin.c ==========================================================*/
extern Vec_Ptr_t *      Abc_MfsComputeRoots( Abc_Obj_t * pNode, int nWinTfoMax, int nFanoutLimit );


#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

