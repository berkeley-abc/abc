/**CFile****************************************************************

  FileName    [pdr.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Property driven reachability.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 20, 2010.]

  Revision    [$Id: pdr.h,v 1.00 2010/11/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef ABC__sat__pdr__pdr_h
#define ABC__sat__pdr__pdr_h


ABC_NAMESPACE_HEADER_START


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Pdr_Par_t_ Pdr_Par_t;
struct Pdr_Par_t_
{
    int iOutput;      // zero-based number of primary output to solve
    int nRecycle;     // limit on vars for recycling
    int nFrameMax;    // limit on frame count
    int nConfLimit;   // limit on SAT solver conflicts
    int nTimeOut;     // timeout in seconds
    int fTwoRounds;   // use two rounds for generalization
    int fMonoCnf;     // monolythic CNF
    int fDumpInv;     // dump inductive invariant
    int fShortest;    // forces bug traces to be shortest
    int fSkipGeneral; // skips expensive generalization step
    int fVerbose;     // verbose output
    int fVeryVerbose; // very verbose output
    int iFrame;       // explored up to this frame
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== pdrCore.c ==========================================================*/
extern void            Pdr_ManSetDefaultParams( Pdr_Par_t * pPars );
extern int             Pdr_ManSolve( Aig_Man_t * p, Pdr_Par_t * pPars, Abc_Cex_t ** ppCex );


ABC_NAMESPACE_HEADER_END


#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

