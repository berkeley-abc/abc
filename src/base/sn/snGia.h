/**CFile****************************************************************

  FileName    [snGia.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Frame-independent SN to GIA conversion.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snGia.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
#ifndef ABC__base__sn__snGia_h
#define ABC__base__sn__snGia_h
#include "snBlast.h"
#include "aig/gia/gia.h"
ABC_NAMESPACE_HEADER_START

// The caller owns the returned GIA. Boundary must be initialized and empty; it remains caller-owned.
// No ABC frame, current network, or saved extraction is changed, including on failure.
typedef struct Sn_GiaResult_t_
{
    sn_blast_hier_stats_t Stats;
    abctime BlastTime, ImportTime;
    int MiniAnds;
} Sn_GiaResult_t;

typedef struct Sn_GiaOptions_t_
{
    sn_blast_options_t Blast;
    Vec_Ptr_t * vModules;
    Vec_Ptr_t * vInstances;
    int fMemory, fMultiply;
} Sn_GiaOptions_t;

// Verification extraction: preserved state polarity, explicit cuts, positional interfaces. The descriptor vector
// is caller-owned and contains no names. Failure never installs a GIA or changes the design.
Gia_Man_t * Sn_DesignExtractGia( const sn_design_t * pDesign, sn_module_id_t Top,
    const Sn_GiaOptions_t * pOptions, Vec_Int_t * vDescriptor, FILE * pError );

Gia_Man_t * Sn_DesignToGia( const sn_design_t * pDesign, sn_module_id_t Top,
    const sn_blast_options_t * pOptions, sn_blast_boundary_t * pBoundary, Sn_GiaResult_t * pResult );
void Sn_GiaSetNames( Gia_Man_t * pGia, const sn_design_t * pDesign, sn_module_id_t Top,
    const sn_blast_boundary_t * pBoundary, int fOmitLoops, int * pNonCanonical, int * pDuplicates );

ABC_NAMESPACE_HEADER_END
#endif
