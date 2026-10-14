/**CFile****************************************************************

  FileName    [parter.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Acyclic word-level partitioning.]

  Synopsis    [Indexed immutable hypergraphs and partitioning interfaces.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: parter.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
// Inspired by Fiduccia-Mattheyses bipartitioning (DAC 1982) and UMpack's
// FMPart/MLPart work by Andrew E. Caldwell, Andrew B. Kahng, and Igor L. Markov,
// with subsequent contributors credited in readme.md. Acyclic partitioning
// references include Herrmann et al. (2019) and Moreira, Popp, and Schulz
// (2017). See readme.md for full references and source credits.
// ABC uses indexed arrays and directed move constraints; these references
// are algorithmic inspiration and introduce no external runtime dependency.

#ifndef ABC__base__parter__parter_h
#define ABC__base__parter__parter_h

#include "misc/util/abc_global.h"

ABC_NAMESPACE_HEADER_START

#define PRT_NONE ((unsigned)~0U)

typedef struct Prt_Graph_t_
{
    unsigned nObjs, nNets, nPins;
    unsigned * pInStart, * pInNets;
    unsigned * pOutStart, * pOutNets;
    unsigned * pDriver, * pSinkStart, * pSinks;
    double * pObjWeight, * pNetWeight;
} Prt_Graph_t;

// Nets retain their original IDs, including empty slots. PRT_NONE denotes
// an external driver. Consumers are sorted and deduplicated; internal self
// dependencies are removed. Object and net weights are finite and nonnegative.
// NULL weight arrays request unit weights. Connectivity is caller-owned on
// input and copied. An empty graph is valid. Every failing constructor sets
// its result to NULL and leaves its inputs untouched.
extern int Prt_GraphCreate( unsigned nObjs, unsigned nNets,
    const unsigned * pDriver, const unsigned * pSinkStart, const unsigned * pSinks,
    const double * pObjWeight, const double * pNetWeight,
    Prt_Graph_t ** ppGraph, char * pError, unsigned nError );
extern void Prt_GraphFree( Prt_Graph_t * p );
extern int Prt_GraphCheck( const Prt_Graph_t * p, char * pError, unsigned nError );

// The caller supplies nObjs output slots. Topological order is deterministic;
// failure includes cycles. SCC labels are dense, ordered by their minimum
// original object ID; nComponents is zero for an empty graph. Both operations
// publish their output arrays only on success.
extern int Prt_GraphTopo( const Prt_Graph_t * p, unsigned * pOrder,
    char * pError, unsigned nError );
extern int Prt_GraphScc( const Prt_Graph_t * p, unsigned * pComponents,
    unsigned * pnComponents, char * pError, unsigned nError );

// Every new object must have at least one member. Contraction sums object
// weights, preserves net IDs/weights, and remaps drivers and consumers.
extern int Prt_GraphContract( const Prt_Graph_t * p, unsigned nObjs,
    const unsigned * pMap, Prt_Graph_t ** ppGraph, char * pError, unsigned nError );

typedef struct Prt_Options_t_
{
    double BalanceTolerance;
    unsigned nPasses, Seed;
    int fHardBalance;
    int (*pCancel)( void * pUser );
    void * pUser;
} Prt_Options_t;

typedef struct Prt_Stats_t_
{
    double InitialCut, FinalCut, Weight[2];
    unsigned nMoves, nPasses;
    int fBalanced;
} Prt_Stats_t;

// BalanceTolerance is the relative deviation from half of the total weight,
// in [0,1]. Zero passes returns the seeded topological-prefix initialization.
// A relaxed run permits its initial imbalance but never worsens that bound.
// A hard-balance run fails if its result does not meet the requested bound.
// Both parts must be nonempty. Zero-weight objects remain ordinary vertices.
// Cut weight counts each net once when its driver and consumers span parts;
// an external-source net uses only its consumers. Cancellation, invalid input,
// or failure leaves caller labels and statistics unchanged.
extern void Prt_OptionsDefault( Prt_Options_t * p );
extern int Prt_Bisect( const Prt_Graph_t * p, const Prt_Options_t * pOptions,
    unsigned * pParts, Prt_Stats_t * pStats, char * pError, unsigned nError );
extern int Prt_Refine( const Prt_Graph_t * p, const Prt_Options_t * pOptions,
    unsigned * pParts, Prt_Stats_t * pStats, char * pError, unsigned nError );
extern double Prt_CutWeight( const Prt_Graph_t * p, const unsigned * pParts );

// Optional multilevel candidate with at most 16 contraction levels. Every
// coarse quotient is checked as a DAG. Uncoarsening uses the same FM kernel.
// A flat FM run remains the baseline; the candidate is retained only when
// its balance excess is no worse and its cut is strictly smaller. Zero levels
// is exactly Prt_Bisect. Statistics include work spent on both candidates.
extern int Prt_BisectMulti( const Prt_Graph_t * p, const Prt_Options_t * pOptions,
    unsigned nLevels, unsigned * pParts, Prt_Stats_t * pStats, char * pError, unsigned nError );

ABC_NAMESPACE_HEADER_END
#endif
