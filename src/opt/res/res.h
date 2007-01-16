/**CFile****************************************************************

  FileName    [res.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Resynthesis package.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - January 15, 2007.]

  Revision    [$Id: res.h,v 1.00 2007/01/15 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __RES_H__
#define __RES_H__

#ifdef __cplusplus
extern "C" {
#endif

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Res_Win_t_ Res_Win_t;
struct Res_Win_t_
{
    // the general data
    int              nWinTfiMax; // the fanin levels
    int              nWinTfoMax; // the fanout levels
    int              nLevLeaves; // the level where leaves begin
    int              nLevDivMax; // the maximum divisor level
    Abc_Obj_t *      pNode;      // the node in the center
    // the window data
    Vec_Vec_t *      vLevels;    // nodes by level
    Vec_Ptr_t *      vLeaves;    // leaves of the window
    Vec_Ptr_t *      vRoots;     // roots of the window
    Vec_Ptr_t *      vDivs;      // the candidate divisors of the node
};

typedef struct Res_Sim_t_ Res_Sim_t;
struct Res_Sim_t_
{
    Abc_Ntk_t *      pAig;       // AIG for simulation
    // simulation parameters
    int              nWords;     // the number of simulation words
    int              nPats;      // the number of patterns
    int              nWordsOut;  // the number of simulation words in the output patterns
    int              nPatsOut;   // the number of patterns in the output patterns 
    // simulation info
    Vec_Ptr_t *      vPats;      // input simulation patterns
    Vec_Ptr_t *      vPats0;     // input simulation patterns
    Vec_Ptr_t *      vPats1;     // input simulation patterns
    Vec_Ptr_t *      vOuts;      // output simulation info
    int              nPats0;     // the number of 0-patterns accumulated
    int              nPats1;     // the number of 1-patterns accumulated
    // resub candidates
    Vec_Vec_t *      vCands;     // resubstitution candidates
};

// adds one node to the window
static inline void Res_WinAddNode( Res_Win_t * p, Abc_Obj_t * pObj )
{
    assert( !pObj->fMarkA );
    pObj->fMarkA = 1;
    Vec_VecPush( p->vLevels, pObj->Level, pObj );
}

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== resDivs.c ==========================================================*/
extern void          Res_WinDivisors( Res_Win_t * p, int nLevDivMax );
extern int           Res_WinVisitMffc( Res_Win_t * p );
/*=== resFilter.c ==========================================================*/
extern Vec_Ptr_t *   Res_FilterCandidates( Res_Win_t * pWin, Res_Sim_t * pSim );
/*=== resSat.c ==========================================================*/
extern Hop_Obj_t *   Res_SatFindFunction( Hop_Man_t * pMan, Res_Win_t * pWin, Vec_Ptr_t * vFanins, Abc_Ntk_t * pAig );
/*=== resSim.c ==========================================================*/
extern Res_Sim_t *   Res_SimAlloc( int nWords );
extern void          Res_SimFree( Res_Sim_t * p );
extern int           Res_SimPrepare( Res_Sim_t * p, Abc_Ntk_t * pAig );
/*=== resStrash.c ==========================================================*/
extern Abc_Ntk_t *   Res_WndStrash( Res_Win_t * p );
/*=== resWnd.c ==========================================================*/
extern void          Res_UpdateNetwork( Abc_Obj_t * pObj, Vec_Ptr_t * vFanins, Hop_Obj_t * pFunc, Vec_Vec_t * vLevels );
/*=== resWnd.c ==========================================================*/
extern Res_Win_t *   Res_WinAlloc();
extern void          Res_WinFree( Res_Win_t * p );
extern int           Res_WinCompute( Abc_Obj_t * pNode, int nWinTfiMax, int nWinTfoMax, Res_Win_t * p );
extern void          Res_WinVisitNodeTfo( Res_Win_t * p );


#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

