/**CFile****************************************************************

  FileName    [snAigCost.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Shared-master AIG area and local output-level characterization.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snAigCost.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
#ifndef ABC__base__sn__snAigCost_h
#define ABC__base__sn__snAigCost_h

#include "sn.h"

ABC_NAMESPACE_HEADER_START

#define SN_AIG_COST_LEVEL_NONE ((unsigned)~0U)

typedef struct Sn_AigCostModule_t_
{
    unsigned nObjects, Levels;
    int Known, fSelected;
    uint64_t Ands, FlopBits, SramBits, Occurrences;
    double LocalArea;
    double * pObjectAreas;
    unsigned * pObjectLevels;
    char UnknownReason[192];
} Sn_AigCostModule_t;

typedef struct Sn_AigCost_t_
{
    unsigned nModules, Top, nCharacterized, nOpaque, MaxLevels;
    Sn_AigCostModule_t * pModules;
    uint64_t Ands, FlopBits, SramBits, Occurrences;
    uint64_t ExpandedAnds, ExpandedFlopBits, ExpandedSramBits;
    double LocalArea, ExpandedArea;
} Sn_AigCost_t;

// Each selected master is blasted independently with child, state, memory,
// and explicit loop boundaries, structurally hashed, and cleaned. Levels
// are local boundary-to-boundary levels; MaxLevels is not hierarchy depth.
// Object areas count each surviving AND once plus the supplied storage costs;
// they are assigned weights, not raw per-object AND counts. Output levels are
// independent of this ownership: aliases and duplicate logic can own zero ANDs
// and still have a nonzero level. Each pObjectLevels entry is the maximum level
// of the object's observed output literals that survive structural hashing and
// cleanup, including all outputs of mapped gates and child instances. Separate
// FAN objects retain their own output levels and also contribute to the owner's
// maximum, including owners of opaque mapped sequential cells.
// If only some bits survive,
// only those bits contribute. SN_AIG_COST_LEVEL_NONE means that no observed
// output survives, or the object was not evaluated or has no signal output.
// Observed constants and input boundaries have level zero. Boundaries include
// child outputs, native and mapped state outputs, memory reads, and loop cuts;
// their CIs remain valid even when unused. Unobserved dead logic is not blasted
// merely to report levels. These local structural levels are not timing slack.
// Opaque technology primitives and unsupported functions have Known zero,
// a nonempty UnknownReason, and neither object array. Consumers must handle
// unknown costs explicitly rather than interpreting them as zero weights.
// nOpaque counts all unknown selected masters. Totals include known costs only
// and therefore are partial when nOpaque is nonzero. Expanded totals cover Top,
// even when fAll is set. Malformed designs, allocation failures, and overflow
// still fail the whole characterization.
// Top == SN_INVALID_ID selects the last definition. The result is caller-owned;
// failure sets *ppResult to NULL and never changes the SN graph.
extern int Sn_AigCostCompute( const sn_design_t * pDesign, unsigned Top, int fAll,
    double FlopArea, double SramArea, Sn_AigCost_t ** ppResult, char * pError, unsigned nError );
extern void Sn_AigCostFree( Sn_AigCost_t * p );

// Characterize exactly one explicitly named master, treating its children as
// boundaries without characterizing their contents. Validation and unknown
// reasons are the same as above. Occurrences is one; no hierarchy totals are
// computed. The returned record and its arrays are caller-owned and must be
// released with Sn_AigCostModuleFree. Failure sets *ppResult to NULL.
extern int Sn_AigCostComputeModule( const sn_design_t * pDesign, unsigned Module,
    double FlopArea, double SramArea, Sn_AigCostModule_t ** ppResult, char * pError, unsigned nError );
extern void Sn_AigCostModuleFree( Sn_AigCostModule_t * p );

// Batch callers may use this only within a validated, privately owned design.
// It checks the named module, assuming the design tables and child contracts
// are unchanged or were checked after mutation. The public single-master API
// above continues to check the full design for independent callers.
extern int Sn_AigCostComputeModuleLocal( const sn_design_t * pDesign, unsigned Module,
    double FlopArea, double SramArea, Sn_AigCostModule_t ** ppResult, char * pError, unsigned nError );

ABC_NAMESPACE_HEADER_END
#endif
