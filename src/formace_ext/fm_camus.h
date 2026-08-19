/**CFile****************************************************************

  FileName    [fm_camus.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ForMACE CaDiCaL-backed CAMUS-style MUS support.]

  Synopsis    [In-process CaDiCaL-backed guarded constraint-group API.]

***********************************************************************/

#ifndef ABC__formace_ext__fm_camus_h
#define ABC__formace_ext__fm_camus_h

#include "misc/util/abc_global.h"
#include "misc/vec/vec.h"

ABC_NAMESPACE_HEADER_START

typedef struct Fm_CamusMan_t_ Fm_CamusMan_t;

/** Experimental controls.  Defaults reproduce the production algorithm. */
typedef struct Fm_CamusOptions_t_
{
    int fUseCoreShrink;
    int fUseMusSeed;
    int fMinimizeSeed;
    int fUseModelAbsorb;
    int fGrowMcs;
    int fBinaryMapBounds;
    /** Master switch retained for the original all-default CaDiCaL ablation. */
    int fUseCadicalTuning;
    /** Independent production tuning switches for solver-level ablations. */
    int fUseCadicalPlain;
    int fUseCadicalIlb;
    int fUseCadicalStableOnly;
} Fm_CamusOptions_t;

/** Per-call measurements for Fm_CamusFindMinimumMus(). */
typedef struct Fm_CamusStats_t_
{
    ABC_INT64_T nSeedSolves;
    ABC_INT64_T nMapSolves;
    ABC_INT64_T nMapSat;
    ABC_INT64_T nMapUnsat;
    ABC_INT64_T nValidationSolves;
    ABC_INT64_T nGrowthSolves;
    ABC_INT64_T nRefinements;
    ABC_INT64_T nCorrectionSets;
    ABC_INT64_T nCoreShrinks;
    ABC_INT64_T nCoreGroupsRemoved;
    ABC_INT64_T nModelGroupsAdded;
    ABC_INT64_T nExplicitGroupsTried;
    ABC_INT64_T nSolverConstructions;
    abctime     timeTotal;
    abctime     timeSeed;
    abctime     timeMap;
    abctime     timeValidation;
    abctime     timeGrowth;
    int         nSeedInput;
    int         nSeedResult;
    int         nResult;
} Fm_CamusStats_t;

/**Function*************************************************************

  Synopsis    [Starts a guarded-group SAT problem.]

  Description [nVars is the number of caller-owned SAT variables.  The
  manager allocates one private selector variable for each group.]

***********************************************************************/
extern Fm_CamusMan_t * Fm_CamusStart( int nVars, int nGroups );
extern Fm_CamusMan_t * Fm_CamusStartWithOptions( int nVars, int nGroups, const Fm_CamusOptions_t * pOptions );
extern void            Fm_CamusStop( Fm_CamusMan_t * p );
extern void            Fm_CamusOptionsDefault( Fm_CamusOptions_t * pOptions );
extern void            Fm_CamusGetStats( Fm_CamusMan_t * p, Fm_CamusStats_t * pStats );
/** Returns the linked CaDiCaL signature, for example "cadical-2.2.0". */
extern const char *    Fm_CamusBackendName( void );
extern void            Fm_CamusSetLimits( Fm_CamusMan_t * p, ABC_INT64_T nConfLimit, abctime nTimeOut );

/**Function*************************************************************

  Synopsis    [Adds permanent or selector-guarded clauses.]

  Description [Literals use ABC's internal SAT literal encoding.  Group
  clauses are enabled only when their group index is supplied to Solve.]

***********************************************************************/
extern int             Fm_CamusAddBackground( Fm_CamusMan_t * p, int * pLits, int nLits );
extern int             Fm_CamusAddGroup( Fm_CamusMan_t * p, int iGroup, int * pLits, int nLits );

/**Function*************************************************************

  Synopsis    [Solves with precisely the requested groups enabled.]

  Description [Returns l_True, l_False, or l_Undef.  The vector contains
  group indexes, not SAT variables.]

***********************************************************************/
extern int             Fm_CamusSolve( Fm_CamusMan_t * p, Vec_Int_t * vEnabled );

/**Function*************************************************************

  Synopsis    [Computes one subset-minimal UNSAT group set.]

  Description [The supplied group set must be UNSAT.  The result is a newly
  allocated sorted vector, or NULL for SAT, unknown, or invalid input. An
  empty vector is a valid MUS when the background itself is UNSAT.]

***********************************************************************/
extern Vec_Int_t *     Fm_CamusFindMus( Fm_CamusMan_t * p, Vec_Int_t * vEnabled );

/**Function*************************************************************

  Synopsis    [Computes one minimum-cardinality UNSAT group set.]

  Description [Uses implicit MCS discovery and minimum hitting sets.  The
  result is a newly allocated sorted vector, or NULL for SAT, unknown, or
  invalid input. An empty vector is a valid minimum when the background
  itself is UNSAT.]

***********************************************************************/
extern Vec_Int_t *     Fm_CamusFindMinimumMus( Fm_CamusMan_t * p, Vec_Int_t * vEnabled );

ABC_NAMESPACE_HEADER_END

#endif
