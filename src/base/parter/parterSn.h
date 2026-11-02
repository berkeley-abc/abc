/**CFile****************************************************************

  FileName    [parterSn.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Acyclic word-level partitioning.]

  Synopsis    [SN correspondence and indivisible-group characterization.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: parterSn.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
#ifndef ABC__base__parter__parterSn_h
#define ABC__base__parter__parterSn_h

#include "parter.h"
#include "base/sn/snAigCost.h"

ABC_NAMESPACE_HEADER_START

typedef struct Prt_SnModel_t_
{
    Prt_Graph_t * pGraph;
    unsigned nObjects, nMovable, nGroups, nScc;
    unsigned * pObjToGroup, * pObjToVertex, * pVertexObject;
    double MaxGroupWeight, MaxSccWeight;
    unsigned MaxGroupObject, MaxSccObject;
} Prt_SnModel_t;

// Build from a checked SN module and its known local characterization. The
// caller retains both inputs; no design, cost, or derived SN cache is changed.
// PI, PO, and constant objects map to PRT_NONE. Mandatory groups include all
// owner/FAN objects, state pairs, and memories with every read/write port.
// SCCs are computed after these contractions, including every control fanin.
// Net IDs are original SN object IDs. Constants have no cut cost and their
// uses are omitted because extraction reproduces them locally. PI nets keep
// their distinct identities and have an external driver. A PO does not add
// a partition vertex; extraction preserves the parent's original interface.
// pVertexObject supplies the smallest original object ID in each final SCC.
// No-new-loop extraction cannot divide an SCC. Unknown cost is an error here;
// a multi-master caller may instead report and skip an unknown master.
extern int Prt_SnBuild( const sn_module_t * pModule, const Sn_AigCostModule_t * pCosts,
    Prt_SnModel_t ** ppModel, char * pError, unsigned nError );
extern void Prt_SnFree( Prt_SnModel_t * p );

ABC_NAMESPACE_HEADER_END
#endif
