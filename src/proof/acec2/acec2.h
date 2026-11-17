/**CFile****************************************************************

  FileName    [acec2.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Arithmetic analysis and equivalence checking.]

  Synopsis    [Public, instance-owned arithmetic analysis interface.]

  Description [Based on A. Mishchenko, B. Sterin, and R. Brayton,
    "Structural reverse engineering of arithmetic circuits",
    UC Berkeley, Tech. Report, 2017.
    https://people.eecs.berkeley.edu/~alanmi/publications/2017/tech17_arith.pdf]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 11, 2026.]

  Revision    [$Id$]

***********************************************************************/

#ifndef ABC__proof__acec2__acec2_h
#define ABC__proof__acec2__acec2_h

#include "aig/gia/gia.h"

ABC_NAMESPACE_HEADER_START

typedef struct Acec2_Par_t_ Acec2_Par_t;
typedef struct Acec2_Man_t_ Acec2_Man_t;

struct Acec2_Par_t_
{
    int nCuts;                  // retained nontrivial cuts per node (1..64)
    int nTimeLimit;             // shared runtime limit in seconds; 0 is unlimited
    int nBTLimit;               // initial conflicts per SAT query; 0 is unlimited
    int nMaxWidth;              // maximum polynomial word / normalized prefix width
    int fAlgebra;               // bounded exact weighted polynomial proof
    int fNormalize;             // use checked arithmetic identities
    int fPaired;                // replace roots shared by both normalized designs
    int fSweep;                 // use the established CEC sweeping engine
    int fVerbose;               // detailed reporting
    int RunId;                 // caller's cancellation identifier
    int (*pFuncStop)(int);      // optional cooperative cancellation
    int * pCancelled;          // optional instance-owned cancellation latch
    unsigned nCecOptions;      // internal CEC scheduling policies; ignored by standalone profiling
    int nCecPolyLimit;          // active deterministic proof tier; zero uses the ordinary limit
    int nAnalysisLevel;         // 0: regions; 1: words; 2: products; 3: expressions
};

// Analysis never changes the input GIA, including its scratch fields.
// The caller retains the GIA until the analysis manager is freed.
extern void          Acec2_SetDefaultParams( Acec2_Par_t * p );
extern Acec2_Man_t *  Acec2_Analyze( Gia_Man_t * pGia, Acec2_Par_t * pPars );
extern void          Acec2_ProfilePolynomial( Acec2_Man_t * p );
extern void          Acec2_Free( Acec2_Man_t * p );
extern void          Acec2_Print( Acec2_Man_t * p, FILE * pFile, int fVerbose );
extern int           Acec2_WriteJson( Acec2_Man_t * p, FILE * pFile );

// Combinational comparison at all CI/CO boundaries, including register pins.
// Returns 1/0/-1 for equivalent/inequivalent/unknown.  Does not change inputs.
// On inequivalence, the caller owns *ppCex (CI ordering, failing CO index).
extern int           Acec2_Solve( Gia_Man_t * pGia0, Gia_Man_t * pGia1,
                                 Acec2_Par_t * pPars, Abc_Cex_t ** ppCex );
extern int           Acec2_SolveMiter( Gia_Man_t * pGia, Acec2_Par_t * pPars, Abc_Cex_t ** ppCex );

ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
