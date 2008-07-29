/**CFile****************************************************************

  FileName    [dchInt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Choice computation for tech-mapping.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 29, 2008.]

  Revision    [$Id: dchInt.h,v 1.00 2008/07/29 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __DCH_INT_H__
#define __DCH_INT_H__

#ifdef __cplusplus
extern "C" {
#endif

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "aig.h"
#include "satSolver.h"
#include "dch.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

// equivalence classes
typedef struct Dch_Cla_t_ Dch_Cla_t;
struct Dch_Cla_t_
{
    int              nNodes;       // the number of nodes in the class
    int              pNodes[0];    // the nodes of the class
};

// choicing manager
typedef struct Dch_Man_t_ Dch_Man_t;
struct Dch_Man_t_
{
    // parameters
    Dch_Pars_t *     pPars;
    // AIGs used in the package
    Vec_Ptr_t *      vAigs;        // user-given AIGs
    Aig_Man_t *      pAigTotal;    // intermediate AIG
    Aig_Man_t *      pAigFraig;    // final AIG
    // equivalence classes
    Dch_Cla_t **     ppClasses;    // classes for representative nodes
    // SAT solving
    sat_solver *     pSat;         // recyclable SAT solver
    Vec_Int_t **     ppSatVars;    // SAT variables for used nodes
    Vec_Ptr_t *      vUsedNodes;   // nodes whose SAT vars are assigned
    // runtime stats
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== dchAig.c =====================================================*/
extern Aig_Man_t *     Dch_DeriveTotalAig( Vec_Ptr_t * vAigs );
extern Aig_Man_t *     Dch_DeriveChoiceAig( Aig_Man_t * pAig );

/*=== dchMan.c =====================================================*/
extern Dch_Man_t *     Dch_ManCreate( Vec_Ptr_t * vAigs, Dch_Pars_t * pPars );
extern void            Dch_ManStop( Dch_Man_t * p );

/*=== dchSat.c =====================================================*/
 
/*=== dchSim.c =====================================================*/
extern Dch_Cla_t **    Dch_CreateCandEquivClasses( Aig_Man_t * pAig, int nWords, int fVerbose );


#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

