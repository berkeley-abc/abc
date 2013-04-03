/**CFile****************************************************************

  FileName    [sfm.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based optimization using internal don't-cares.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: sfm.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef ABC__opt_sfm__h
#define ABC__opt_sfm__h


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_HEADER_START

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Sfm_Man_t_ Sfm_Man_t;
typedef struct Sfm_Ntk_t_ Sfm_Ntk_t;
typedef struct Sfm_Par_t_ Sfm_Par_t;
struct Sfm_Par_t_
{
    int           nWinTfoLevs;   // the maximum fanout levels
    int           nFanoutsMax;   // the maximum number of fanouts
    int           nDepthMax;     // the maximum number of logic levels
    int           nDivMax;       // the maximum number of divisors
    int           nWinSizeMax;   // the maximum size of the window
    int           nGrowthLevel;  // the maximum allowed growth in level
    int           nBTLimit;      // the maximum number of conflicts in one SAT run
    int           fResub;        // performs resubstitution
    int           fArea;         // performs optimization for area
    int           fMoreEffort;   // performs high-affort minimization
    int           fSwapEdge;     // performs edge swapping
    int           fOneHotness;   // adds one-hotness conditions
    int           fDelay;        // performs optimization for delay
    int           fPower;        // performs power-aware optimization
    int           fGiaSat;       // use new SAT solver
    int           fVerbose;      // enable basic stats
    int           fVeryVerbose;  // enable detailed stats
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== sfmCnf.c ==========================================================*/
/*=== sfmCore.c ==========================================================*/
extern int          Sfm_ManPerform( Sfm_Ntk_t * p, Sfm_Par_t * pPars );
/*=== sfmMan.c ==========================================================*/
extern Sfm_Man_t *  Sfm_ManAlloc( Sfm_Ntk_t * p );
extern void         Sfm_ManFree( Sfm_Man_t * p );
/*=== sfmNtk.c ==========================================================*/
extern Sfm_Ntk_t *  Sfm_NtkAlloc( int nPis, int nPos, int nNodes, Vec_Int_t * vFanins, Vec_Int_t * vFanouts, Vec_Int_t * vEdges, Vec_Int_t * vOpts );
extern void         Sfm_NtkFree( Sfm_Ntk_t * p );
/*=== sfmSat.c ==========================================================*/


ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

