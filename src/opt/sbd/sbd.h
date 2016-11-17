/**CFile****************************************************************

  FileName    [sbd.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based optimization using internal don't-cares.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: sbd.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef ABC__opt_sbd__h
#define ABC__opt_sbd__h

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

typedef struct Sbd_Ntk_t_ Sbd_Ntk_t;
typedef struct Sbd_Par_t_ Sbd_Par_t;
struct Sbd_Par_t_
{
    int             nTfoLevMax;    // the maximum fanout levels
    int             nTfiLevMax;    // the maximum fanin levels
    int             nFanoutMax;    // the maximum number of fanouts
    int             nDepthMax;     // the maximum depth to try
    int             nVarMax;       // the maximum variable count
    int             nMffcMin;      // the minimum MFFC size
    int             nMffcMax;      // the maximum MFFC size
    int             nDecMax;       // the maximum number of decompositions
    int             nWinSizeMax;   // the maximum window size
    int             nGrowthLevel;  // the maximum allowed growth in level
    int             nBTLimit;      // the maximum number of conflicts in one SAT run
    int             nNodesMax;     // the maximum number of nodes to try
    int             iNodeOne;      // one particular node to try
    int             nFirstFixed;   // the number of first nodes to be treated as fixed
    int             nTimeWin;      // the size of timing window in percents
    int             DeltaCrit;     // delay delta in picoseconds
    int             DelAreaRatio;  // delay/area tradeoff (how many ps we trade for a unit of area)
    int             fRrOnly;       // perform redundance removal
    int             fArea;         // performs optimization for area
    int             fAreaRev;      // performs optimization for area in reverse order
    int             fMoreEffort;   // performs high-affort minimization
    int             fUseAndOr;     // enable internal detection of AND/OR gates
    int             fZeroCost;     // enable zero-cost replacement
    int             fUseSim;       // enable simulation
    int             fPrintDecs;    // enable printing decompositions
    int             fAllBoxes;     // enable preserving all boxes
    int             fLibVerbose;   // enable library stats
    int             fDelayVerbose; // enable delay stats
    int             fVerbose;      // enable basic stats
    int             fVeryVerbose;  // enable detailed stats
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== sbdCnf.c ==========================================================*/
/*=== sbdCore.c ==========================================================*/
extern void         Sbd_ParSetDefault( Sbd_Par_t * pPars );
extern int          Sbd_NtkPerform( Sbd_Ntk_t * p, Sbd_Par_t * pPars );
/*=== sbdNtk.c ==========================================================*/
extern Sbd_Ntk_t *  Sbd_NtkConstruct( Vec_Wec_t * vFanins, int nPis, int nPos, Vec_Str_t * vFixed, Vec_Str_t * vEmpty, Vec_Wrd_t * vTruths );
extern void         Sbd_NtkFree( Sbd_Ntk_t * p );
extern Vec_Int_t *  Sbd_NodeReadFanins( Sbd_Ntk_t * p, int i );
extern word *       Sbd_NodeReadTruth( Sbd_Ntk_t * p, int i );
extern int          Sbd_NodeReadFixed( Sbd_Ntk_t * p, int i );
extern int          Sbd_NodeReadUsed( Sbd_Ntk_t * p, int i );
/*=== sbdWin.c ==========================================================*/
extern Vec_Int_t *  Sbd_NtkDfs( Sbd_Ntk_t * p, Vec_Wec_t * vGroups, Vec_Int_t * vGroupMap, Vec_Int_t * vBoxesLeft, int fAllBoxes );


ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

