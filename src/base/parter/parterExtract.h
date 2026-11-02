/**CFile****************************************************************

  FileName    [parterExtract.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Acyclic word-level partitioning.]

  Synopsis    [Transactional extraction of assigned SN partitions.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: parterExtract.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__base__parter__parterExtract_h
#define ABC__base__parter__parterExtract_h
#include "base/sn/sn.h"
ABC_NAMESPACE_HEADER_START

typedef struct Prt_ExtractStats_t_
{
    unsigned nParts, nInputPorts, nOutputPorts, nDummyOutputs;
    uint64_t InputBits, OutputBits;
} Prt_ExtractStats_t;

typedef struct Prt_ExtractMap_t_
{
    unsigned nObjects;
    unsigned * pModule;
    unsigned * pObject;
} Prt_ExtractMap_t;

// Every non-port, non-constant object has a label in [0,nParts). Ports and
// constants use SN_INVALID_ID. Each part is nonempty. Mandatory groups stay
// together, and all crossing dependencies must induce an acyclic quotient.
// The caller owns the returned design. The original master ID and ordered
// interface survive, including every repeated occurrence. Constants are
// replicated locally. Outputless parts receive one unused constant output
// because SN instances require at least one output. Stats includes this port.
// Failure leaves the source and stats untouched and sets *ppResult to NULL.
int Prt_SnExtract( const sn_design_t * pDesign, unsigned Master,
    const unsigned * pPartByObject, unsigned nParts, sn_design_t ** ppResult,
    Prt_ExtractStats_t * pStats, char * pError, unsigned nError );

// Optional correspondence for semantic checks across reordered state boundaries.
// Non-constant objects have their exact destination module/object. Constants
// use SN_INVALID_ID because they may be copied into several parts. The map is
// caller-owned. No source object or path is used to guess state equivalence.
int Prt_SnExtractMapped( const sn_design_t * pDesign, unsigned Master,
    const unsigned * pPartByObject, unsigned nParts, sn_design_t ** ppResult,
    Prt_ExtractStats_t * pStats, Prt_ExtractMap_t ** ppMap, char * pError, unsigned nError );
// Internal batch operation: the design must already pass the full SN check.
// Mutates only the named master and newly appended parts, checking these locally.
// Success aliases the input in *ppResult. On failure the caller must destroy the
// entire private design; it is not safe to publish or continue using it.
int Prt_SnExtractPrivateMapped( sn_design_t * pDesign, unsigned Master,
    const unsigned * pPartByObject, unsigned nParts, sn_design_t ** ppResult,
    Prt_ExtractStats_t * pStats, Prt_ExtractMap_t ** ppMap, char * pError, unsigned nError );
void Prt_ExtractMapFree( Prt_ExtractMap_t * pMap );

ABC_NAMESPACE_HEADER_END
#endif
