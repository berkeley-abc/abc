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

#include "misc/vec/vecWec.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_HEADER_START

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Sfm_Ntk_t_ Sfm_Ntk_t;
typedef struct Sfm_Par_t_ Sfm_Par_t;
struct Sfm_Par_t_
{
    int             nTfoLevMax;    // the maximum fanout levels
    int             nFanoutMax;    // the maximum number of fanouts
    int             nDepthMax;     // the maximum depth to try
    int             nWinSizeMax;   // the maximum window size
    int             nGrowthLevel;  // the maximum allowed growth in level
    int             nBTLimit;      // the maximum number of conflicts in one SAT run
    int             nFirstFixed;   // the number of first nodes to be treated as fixed
    int             fRrOnly;       // perform redundance removal
    int             fArea;         // performs optimization for area
    int             fMoreEffort;   // performs high-affort minimization
    int             fVerbose;      // enable basic stats
    int             fVeryVerbose;  // enable detailed stats
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== sfmCnf.c ==========================================================*/
/*=== sfmCore.c ==========================================================*/
extern void         Sfm_ParSetDefault( Sfm_Par_t * pPars );
extern int          Sfm_NtkPerform( Sfm_Ntk_t * p, Sfm_Par_t * pPars );
/*=== sfmNtk.c ==========================================================*/
extern Sfm_Ntk_t *  Sfm_NtkConstruct( Vec_Wec_t * vFanins, int nPis, int nPos, Vec_Str_t * vFixed, Vec_Wrd_t * vTruths );
extern void         Sfm_NtkFree( Sfm_Ntk_t * p );
extern Vec_Int_t *  Sfm_NodeReadFanins( Sfm_Ntk_t * p, int i );
extern word *       Sfm_NodeReadTruth( Sfm_Ntk_t * p, int i );
extern int          Sfm_NodeReadFixed( Sfm_Ntk_t * p, int i );
extern int          Sfm_NodeReadUsed( Sfm_Ntk_t * p, int i );
/*=== sfmSat.c ==========================================================*/


ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

