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
    // intermeditate data for the node
    Vec_Ptr_t *         vRoots;    // the roots of the window
    Vec_Ptr_t *         vSupp;     // the support of the window
    Vec_Ptr_t *         vNodes;    // the internal nodes of the window
    Vec_Int_t *         vProjVars; // the projection variables
    // solving data
    Aig_Man_t *         pAigWin;   // window AIG with constraints
    Cnf_Dat_t *         pCnf;      // the CNF for the window
    sat_solver *        pSat;      // the SAT solver used 
    // the result of solving
    int                 nFanins;   // the number of fanins
    int                 nWords;    // the number of words
    int                 nCares;    // the number of care minterms
    unsigned            uCare[(MFS_FANIN_MAX<=5)?1:1<<(MFS_FANIN_MAX-5)];  // the computed care-set
    // performance statistics
    int                 nNodesTried;
    int                 nNodesBad;
    int                 nMintsCare;
    int                 nMintsTotal;
    // statistics
    int                 timeWin;
    int                 timeAig;
    int                 timeCnf;
    int                 timeSat;
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

/*=== mfsMan.c ==========================================================*/
extern Mfs_Man_t *      Mfs_ManAlloc();
extern void             Mfs_ManStop( Mfs_Man_t * p );
extern void             Mfs_ManClean( Mfs_Man_t * p );
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

