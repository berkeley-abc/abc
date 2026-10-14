/**CFile****************************************************************

  FileName    [parterRun.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Acyclic word-level partitioning.]

  Synopsis    [Transactional size-cap partitioning of SN hierarchies.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: parterRun.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
#ifndef ABC__base__parter__parterRun_h
#define ABC__base__parter__parterRun_h
#include "parterSn.h"
ABC_NAMESPACE_HEADER_START

typedef struct Prt_RunOptions_t_
{
    unsigned Top;
    int fAll;
    double MaxArea, FlopArea, SramArea;
    unsigned nMaxSplits, nCoarseLevels;
    Prt_Options_t Partition;
    FILE * pLog;
} Prt_RunOptions_t;

typedef struct Prt_RunStats_t_
{
    unsigned nSplits, nParts, nUnknown, nRelaxed, nIndivisible;
    double InitialArea, FinalArea;
    uint64_t InputBits, OutputBits;
} Prt_RunStats_t;

// Characterize selected masters, split oversized local workloads, and
// recharacterize every generated part before accepting the cap. Unknown
// and indivisible over-cap masters are retained and counted separately. The
// cap is verified for all other selected known masters. An exhausted split
// budget, cancellation, or validation failure discards all work.
// The source and caller stats remain unchanged on failure. Success returns
// an owned design, including when no split is needed. Original master IDs
// and the explicit Top survive; appended parts change the last-module default.
// pLog is optional progress output. Cancellation uses Partition.pCancel.
extern void Prt_RunOptionsDefault( Prt_RunOptions_t * p );
extern int Prt_SnPartition( const sn_design_t * pDesign, const Prt_RunOptions_t * pOptions,
    sn_design_t ** ppResult, Prt_RunStats_t * pStats, char * pError, unsigned nError );

ABC_NAMESPACE_HEADER_END
#endif
