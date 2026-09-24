/**CFile****************************************************************

  FileName    [snSec.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Checked sequential extraction and non-mutating SEC adapters.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snSec.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
#ifndef ABC__base__sn__snSec_h
#define ABC__base__sn__snSec_h
#include "snGia.h"
ABC_NAMESPACE_HEADER_START

typedef struct Sn_SecModel_t_
{
    Gia_Man_t * pGia; // raw-polarity state; port names are for reporting only
    Vec_Str_t * vInit;
    Vec_Int_t * vInputWidths, * vOutputWidths;
    int ClockInput, ClockEdge, Unknown;
    Vec_Int_t * vResetValues; // original non-clock PI positions: -1 free, 0/1 asserted level
    int ResetCycles; // zero means no startup-reset contract
    Vec_Ptr_t * vStateKeys;
    Vec_Ptr_t * vStateNames; // source/physical bit labels for traces; not pairing keys
    Vec_Int_t * vAssumedZero; // raw state bit positions assumed zero only at frame zero
    Vec_Int_t * vChoicePis; // raw state bit -> actual normalized choice PI, -1 for known bits
    int PairState, AllowUnmatched, Paired, PairedWords, Unmatched;
    int IsZeroReference; // reporting only: synthetic stateless side of supplied-miter checking
} Sn_SecModel_t;

typedef struct Sn_SecExtractOptions_t_
{
    int fAssumeZero;
    int fTraceState; // collect display labels only when a trace was requested
    Vec_Ptr_t * vResets; // optional borrowed strings pin=0 or pin=1; scalar top-level inputs
    int nResetCycles;
    int fPairState, fAllowUnmatched;
} Sn_SecExtractOptions_t;

// Caller owns the model. Extraction never changes the live ABC workspaces.
Sn_SecModel_t * Sn_DesignExtractSeqGia( const sn_design_t * pDesign, sn_module_id_t Top,
    int fAssumeZero, FILE * pError );
Sn_SecModel_t * Sn_DesignExtractSeqGiaOptions( const sn_design_t * pDesign, sn_module_id_t Top,
    const Sn_SecExtractOptions_t * pOptions, FILE * pError );
void Sn_SecModelFree( Sn_SecModel_t * p );
// Replay has interleaved left/right POs, then a comparison-enable PO in reset
// mode, followed by next state. Choice PIs follow free environmental PIs in
// left-then-right raw state order, omitting paired right-hand choices. vChoicePis
// records the resulting indices. Reset PIs are replaced by a shared controller.
// The replay owns its
// state independently of the inputs; proof is its XOR-output projection. For a
// zero-state side, remove an unused positional clock port if its peer has one.
Gia_Man_t * Sn_GiaSecBuildMiter( Sn_SecModel_t * pLeft, Sn_SecModel_t * pRight,
    Gia_Man_t ** ppReplay, FILE * pError );
// 1 proved, 0 failed with validated owned witness, -1 unknown, -2 internal error.
// fVerbose enables solver diagnostics (command -w), independently of RTL trace verbosity (-v).
int Sn_GiaSecProveMiter( Gia_Man_t * pMiter, int nSeconds, int fVerbose,
    Abc_Cex_t ** ppCex, int * pnFrames );

ABC_NAMESPACE_HEADER_END
#endif
