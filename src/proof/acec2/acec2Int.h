/**CFile****************************************************************

  FileName    [acec2Int.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Arithmetic analysis and equivalence checking.]

  Synopsis    [Internal arithmetic identities and analysis ownership.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 11, 2026.]

  Revision    [$Id$]

***********************************************************************/

#ifndef ABC__proof__acec2__acec2Int_h
#define ABC__proof__acec2__acec2Int_h

#include "acec2.h"
#include "misc/vec/vecHsh.h"

ABC_NAMESPACE_HEADER_START

enum {
    ACEC2_SOURCE_QUEUES = 5
};

enum {
    ACEC2_CEC_SINGLE_USE = 2,
    ACEC2_CEC_DEFER = 8,
    ACEC2_CEC_RECORDS_ONLY = 64 // internal measurement: records and ordinary CEC
};

enum { ACEC2_OUTPUT_POLICIES = 5 };

enum {
    ACEC2_BOUNDARY_CONSTANT,
    ACEC2_BOUNDARY_INPUT,
    ACEC2_BOUNDARY_ALTERNATIVE,
    ACEC2_BOUNDARY_PARITY,
    ACEC2_BOUNDARY_LOGIC,
    ACEC2_BOUNDARY_SHARED_POLICY,
    ACEC2_BOUNDARY_CONFLICT,
    ACEC2_BOUNDARY_REUSE,
    ACEC2_BOUNDARY_OUTPUT,
    ACEC2_BOUNDARY_NO_CONSUMER,
    ACEC2_BOUNDARY_OPEN_CONSUMER,
    ACEC2_BOUNDARY_TAP,
    ACEC2_BOUNDARY_BIT_PRODUCT,
    ACEC2_BOUNDARY_COUNT
};

typedef struct Acec2_WordSim_t_ Acec2_WordSim_t;
typedef struct Acec2_TruthCache_t_ Acec2_TruthCache_t;
typedef struct Acec2_CountCtx_t_ Acec2_CountCtx_t;
typedef struct Acec2_ParityCtx_t_ Acec2_ParityCtx_t;
typedef struct Acec2_CarryCtx_t_ Acec2_CarryCtx_t;
struct Acec2_WordSim_t_
{
    Gia_Man_t * g;
    Acec2_Man_t * pMan; // borrowed arithmetic cover for boundary proposals
    Vec_Int_t * vStop, * vEval, * vBoundary;
    Vec_Wrd_t * vSim;
    Vec_Wec_t * vCandidates;
    Acec2_WordSim_t * pDomain; // borrowed immutable domain retained by the analysis
    int nUsers;
};

typedef struct Acec2_Cell_t_ Acec2_Cell_t;
struct Acec2_Cell_t_
{
    int In[3];                 // literals; unused third input is -1
    int Out[2];                // sum and carry literals
    int nIns;                  // exact identity: sum + 2*carry = sum(inputs)
    int Tree, Rank, Phase;     // relative column and orientation in the region
    int Depth;                 // cell depth in the selected cover
    int Ext[2];                // output fanout edges outside this cell
    int Proof;                 // zero: independent cut; otherwise proof index + 1
};

typedef struct Acec2_Proof_t_ Acec2_Proof_t;
struct Acec2_Proof_t_
{
    int Kind, Domain;          // truth / SAT cell / weighted source; free cut / source-constrained
    int fExhaustive;           // weighted source proof enumerated its complete active support
    int fBoundary;             // proposal inputs reconnect observed arithmetic interfaces
    Vec_Int_t * vCut;          // source IDs; NULL denotes the source primary inputs
    Vec_Int_t * vRoots;        // proof support is the fanin closure to vCut
    Vec_Int_t * vIdentity;     // immutable weighted, parity-cell or masked identity
    Vec_Int_t * vChain;        // optional two checked HAs: input literals, sum, carry
    int ChainProof[2];        // earlier source certificates; zero means an independent carry cut
    Vec_Wec_t * vMonomials;    // completed source-output polynomial, source IDs
    Vec_Wrd_t * vCoefficients; // immutable modular coefficients for that proof
};

typedef struct Acec2_Word_t_ Acec2_Word_t;
typedef struct Acec2_Product_t_ Acec2_Product_t;
struct Acec2_Word_t_
{
    int Tree, Width, nRolled, Record;
    int fIndependent;          // complete SAT proof of the explicit linear cut reference
    int fPolynomial;           // exact source proof of the parent record polynomial
    int fSource;               // linear identity proved on the source, not a free cut
    Vec_Int_t * vTerms;         // independent cut literals and their weights
    Vec_Int_t * vConstants;     // constant columns from reversed boundary cells
    Vec_Int_t * vBits;          // proved result literals, least significant first
    Vec_Int_t * vRollback;      // checked cell parts moving a parent boundary backwards
    Vec_Int_t * vSumProducts;   // source record, shift, negation of full product words
    Vec_Int_t * vSourceCut;     // optional free cut below the weighted reference terms
    Acec2_Product_t * pProduct; // optional independently certified product reference
};

struct Acec2_Product_t_
{
    Vec_Int_t * vOperands[2];   // ordered literals; zero literals fill bit gaps
    int fSigned[2], fNeg, Shift; // negation follows shifting; -1 drops the low bit
};

typedef struct Acec2_Expr_t_ Acec2_Expr_t;
struct Acec2_Expr_t_
{
    int Tree, Width;
    Vec_Ptr_t * vProducts;      // owned, exact factors of weighted partial products
    Vec_Int_t * vAddends;       // original literal/weight pairs not factored
    Vec_Int_t * vConstant;      // constant bits modulo 2^Width
};

typedef struct Acec2_Counter_t_ Acec2_Counter_t;
struct Acec2_Counter_t_
{
    int Width;
    Vec_Int_t * vInputs;       // independent source literal/rank pairs, up to six inputs
    Vec_Int_t * vOutputs;      // weighted binary or carry-save output literals
    Vec_Int_t * vGates;        // exact implementation cone to the independent cut
};

typedef struct Acec2_Record_t_ Acec2_Record_t;
struct Acec2_Record_t_
{
    int Tree, Word, Counter, Expression, Width, Prefix, Domain, Extend, LowLit, Compose;
    int Discovery;             // proposing region + 1; diagnostic, not proof ownership
    int Proof;                 // weighted source proof index + 1, or zero
    int fPolynomial;           // 1: output substitution; 2: checked sum of grids
    Vec_Int_t * vOutputs;      // source literal/rank pairs; roots need not be binary
    Vec_Int_t * vOutputMasks;  // optional source XOR literal for each output occurrence
    Vec_Int_t * vTerms;        // certified weighted reference before gate expansion
    Vec_Int_t * vConstants;    // constant powers of two in the certified reference
    Acec2_Product_t * pProductReference; // optional checked source product certificate
    Vec_Int_t * vCut;          // source literals of polynomial variables
    Vec_Wec_t * vMonomials;    // square-free source IDs; empty denotes one
    Vec_Wrd_t * vCoefficients; // little-endian limbs modulo 2^Width per monomial
    Vec_Int_t * vCovered;      // recognized implementation, not the proof support
    Vec_Int_t * vSupport;      // proof support is the source fanin closure of these IDs
    Vec_Int_t * vDependencies; // earlier checked record IDs
    Vec_Int_t * vBitStatus;    // weighted root=0, binary word=1, binary prefix=2
    Vec_Int_t * vParts;        // kind, index, rank, phase; kind three references an earlier record
    Vec_Int_t * vComposition;  // product index, port, exact integer-adder region
    int FactorWidth;
    Vec_Ptr_t * vFactors;      // exact product terms over source cut literals
    Vec_Wec_t * vResidual;
    Vec_Wrd_t * vResidualCoefs;
};

typedef struct Acec2_Part_t_ Acec2_Part_t;
struct Acec2_Part_t_
{
    int Kind, Id, nIns, nOuts;
    int In[12], Out[8];        // literal/rank pairs of an exact integer identity
    Vec_Int_t * vGates;        // borrowed implementation footprint
};

struct Acec2_Man_t_
{
    Vec_Bit_t * vFocus;        // optional owned fanin-closed source analysis cone
    Gia_Man_t * pGia;
    Acec2_Par_t Pars;
    int fFast, fSingleUse;       // CEC analysis policy; standalone profiling retains joined regions
    abctime Deadline, Time;
    abctime TimeDetect, TimeCounters, TimeTrees, TimeWords, TimeExpressions, TimeRecords;
    Acec2_TruthCache_t * pTruthCache;
    Vec_Ptr_t * vCells;         // owned cells with unique output ownership
    Vec_Ptr_t * vAlternatives;  // owned, checked cells excluded only by cover overlap
    Vec_Int_t * vDisjoint;      // (cell kind, index) of an independent interior-disjoint cover
    Vec_Ptr_t * vProofs;        // checked identities; support is separate from footprint
    Vec_Wec_t * vCellGates;     // conservative covered gate IDs for selected cells
    Vec_Wec_t * vAltGates;      // footprints of the retained alternatives
    Vec_Int_t * vXors;          // records: nInputs, input IDs[3], output literal
    Vec_Int_t * vXorFirst;      // object ID -> first parity-cut record, or -1
    Vec_Int_t * vXorNext;       // parity-cut record -> next alternative for this node
    Vec_Int_t * vXorBest;       // object ID -> selected parity-cut offset, or -1
    Vec_Int_t * vXorGroup;      // object ID -> parity network, or -1
    Vec_Wec_t * vXorNetworks;   // parity-node IDs in each connected equation network
    Vec_Wec_t * vXorLeaves;     // independent boundary IDs of the selected equations
    Vec_Wec_t * vXorSinks;      // node IDs without another selected parity consumer
    Vec_Int_t * vXorDepths;     // maximum selected-equation depth in each network
    Acec2_ParityCtx_t * pParity; // exact per-node phased symmetric-difference forms
    int nParityForms, nParityPairs, nParitySetLimits, nParityPairLimits;
    Vec_Int_t * vMaskCandidates; // shared parity-boundary leaves, ordered once per design
    int iMaskCandidate, nMaskAttempts, nMaskRecords, nMaskLimits;
    int iSourceRequest;        // round-robin region, mask, counter, carry and polynomial requests
    int nSourceWork[ACEC2_SOURCE_QUEUES]; // consumed work units for those queues
    Acec2_CarryCtx_t * pCarry; // incremental source carry proofs, private solver and simulation
    int nCarryRequests, nCarryWork, nCarryRecords, fCarryComplete;
    Vec_Int_t * vConstants;     // (object ID, constant value), exact cut proofs
    Vec_Int_t * vVanish;        // private parity relations: two inputs, sum, carry, proof
    Vec_Int_t * vCarries;       // AND/majority cuts: size, leaf IDs, node, truth
    Vec_Int_t * vExtraRules;    // checked completion cuts in the same format
    Vec_Int_t * vOwner;         // object ID -> 2*cell + output, or -1
    Vec_Int_t * vNodeCell;      // object ID -> selected implementation cell
    Vec_Int_t * vRefs;          // private structural fanout-edge counts
    Vec_Int_t * vEdges;         // cell input -> producer output, or -1
    Vec_Wec_t * vTrees;         // selected cell IDs in each region
    Vec_Wec_t * vLeaves;        // (literal, relative weight) pairs
    Vec_Wec_t * vRoots;         // (literal, relative weight) pairs
    Vec_Wec_t * vBias;          // columns with a constant 1 from reversed HAs
    Vec_Wec_t * vTaps;          // (literal, weight, outside fanout count) triples
    Vec_Wec_t * vBoundaries;    // direction, literal, rank, reason, cell; diagnostic only
    int nBoundaries[ACEC2_BOUNDARY_COUNT];
    Vec_Int_t * vWidths;
    Vec_Int_t * vNormal;        // at most one boundary root at each weight
    Vec_Int_t * vPrefix;        // usable low-column normalization width
    Vec_Ptr_t * vWords;         // owned, independently certified region words
    Vec_Int_t * vTreeWord;      // region -> word record, or -1
    int nWordAttempts, nWordLimits, nWordConflicts;
    int nWordPolyAttempts, nWordPolyProved, nWordPolyLimits, nWordPolyHits;
    int nWordBoundaryAttempts, nWordBoundaryProved, nWordBoundaryPrefixes;
    int nWordCecAttempts, nWordCecProved;
    int nWordConflictStart;     // cumulative conflicts at this region's first query
    Hsh_VecMan_t * hFailedProofs; // exact extracted-cone keys for completed effort failures
    Vec_Int_t * vFailedProofs;   // four integers per exact problem: result and attempted effort
    int nFailedProofWords, nFailedProofHits, nRecordLimits;
    int nBddAttempts, nBddLimits, nBddHits;
    Hsh_VecMan_t * hCertificates; // exact independent product-certificate problems
    Vec_Int_t * vCertificates;   // four integers per exact problem: result and attempted effort
    int nCertificateWords, nCertificateHits, nCertificateAttempts;
    int nCertificateRecords, nCertificateContext;
    Vec_Ptr_t * vWordDomains;  // bounded immutable simulation domains keyed by source stops
    int nWordDomainHits, iWordDomain;
    Vec_Wec_t * vWordSiblings; // carry-sibling index over append-only checked cells
    int nWordSiblingCells[2];   // selected and alternative cells already indexed
    Hsh_Int1Man_t * hWordMap;  // destination node -> source-alias list
    Vec_Int_t * vWordMap, * vWordHeads, * vWordNext;
    Vec_Ptr_t * vCounters;      // exact general counter alternatives, separate from the cell cover
    Acec2_CountCtx_t * pCounterCtx; // resumable private parity-cut analysis
    int nCounterCuts, nCounterSteps, nCounterLimits, nCounterCutLimit, nCounterStepLimit;
    int nCounterBridgeChecks, nCounterBridges;
    int nCounterRequests, nCounterWork, nCounterRecords, fCounterComplete;
    Hsh_VecMan_t * hCounterRegions; // completed immutable counter/alternative-region identities
    int iRegionCache;          // records already indexed by canonical integer parts
    Vec_Ptr_t * vRecords;       // owned component certificates shared by analysis and CEC
    int nRecordStage;           // zero: unbuilt; then regions, words, products, expressions
    Vec_Int_t * vWordProgress;  // per-record tier, next mode, proved prefix, conflicts used
    Vec_Int_t * vRegionRequests; // highest requested recognition level per region
    Vec_Int_t * vRegionStage;   // next word/product/composition/sum action
    Vec_Int_t * vRegionClasses; // recognition groups connected by checked integer records
    int iRegionClassRecord;     // append-only records already included in those groups
    Vec_Int_t * vRegionWord;    // word/gap queue cursors and next action per region
    Vec_Wec_t * vRegionWordQueues; // fixed record batches for each region and action
    Vec_Int_t * vRecordWork;    // source-wide word/gap requests spent on each record
    Vec_Int_t * vLinearProgress; // per-region proof tier, known prefix and absent candidate
    Vec_Int_t * vExtended;      // per-record low-bit extension: untried, absent, or record ID + 1
    Vec_Int_t * vComposeTried;  // completed composition recipe over immutable source regions
    int nStageActions[4], nStageQueries[4]; // bounded work units, including source proposal scans
    int nWeightedAttempts, nWeightedProved, nWeightedLimits;
    int nWeightedTruthChecks, nWeightedTruthProved, nWeightedTruthDisproved, nWeightedTruthLimits;
    int fWeightedTruth;        // method of the most recent successful weighted source query
    Vec_Ptr_t * vGapQueues;     // owned proposal queues indexed by immutable source record
    Vec_Wrd_t * vGapSim;        // private source simulation; proposals only
    Hsh_VecMan_t * hGapProducts; // source AND pairs, indexed once for grid proposals
    Vec_Int_t * vGapProducts;    // corresponding positive literals, or -1 if absent
    int nGapGroups, nGapProposals, nGapClosed, nGapLimits;
    int nGridAttempts, nGridProved, nGridPrefixes, nGridLimits;
    Hsh_VecMan_t * hGridProofs;  // exact source obligations, independent of proposing records
    Vec_Int_t * vGridProofs;     // result, rule-generation counts and proof method
    int nGridProofWords, nGridProofHits, nGridProofCacheLimits;
    int nGridLowAttempts, nGridLowProved, nGridLowLimits;
    int nGridLocalChecks, nGridLocalProved, nGridLocalLimits;
    int nGridPartitionAttempts, nGridPartitionParts, nGridPartitionProved, nGridPartitionLimits;
    ABC_INT64_T nGridPartitionWork;
    ABC_INT64_T nGapSteps;
    int nStageRequests[4], nStageRecords[4];
    int iRegionRequest;         // fair cursor over currently unmatched regions
    Vec_Int_t * vTreeRecord;    // region -> preferred binary/prefix certificate
    Vec_Ptr_t * vExpressions;   // owned weighted sums of certified product terms
    Vec_Int_t * vTreeExpression; // region -> expression; -1 untried, -2 absent
    int nProducts, nExprLimits, nProductLeafLimits;
    int nProductWords, nProductAttempts, nProductLimits;
    int nSumWords, nSumAttempts, nSumLimits;
    Vec_Int_t * vProductProgress; // per-region effort tier and next independent proposal
    Hsh_VecMan_t * hSourceProducts; // exact source operand descriptions
    Vec_Ptr_t * vSourceProducts; // owned product proposals, stable across record enrichment
    Vec_Wec_t * vSourceProductIds; // append-only proposal queue for each region
    int nCuts, nCutLimits, nPairLimits, nCandidates, nCovered;
    ABC_INT64_T nDuplicates, nDominated, nTruths;
    int nXor2, nXor3, nXorGroups, nXorDepth;
    int nFadds, nHadds, nRejected, nNormal, fStopped, fCancelled;
    int nPolyStatus, nPolyTerms, nPolyPeak, nPolyCarries, nPolyProbes;
    int nPolyTermLimit;         // zero: whole-word default; local callers set deterministic effort
    int fPolyEffortLimit;       // completed deterministic effort exhaustion, not time
    Vec_Int_t * vOperands[2];  // proved full-product operands, CI indices in bit order
    int fPolySigned[2];
    int nPolyWidth, nPolyRecords; // certified product width and retained source polynomials
    int nOutputPolyAttempts, nOutputPolyLimits, nOutputPolySkipped;
    int nOutputPolyGeneration[5], nOutputPolyTried[ACEC2_OUTPUT_POLICIES]; // deterministic attempts on unchanged source rules
    int iOutputPolyPolicy, fOutputPolyComplete;
    int fPolyProfiled;         // explicit full-output profiling is attempted once
    int nCarryFiltered, nParityOnly, nPrefix, nNormalCells, nPrefixCells;
    int nLargest, nLargestNormal, nMulti, nTaps, fStorageLimit;
    int nRecoveredCuts, nRecoveryLimits;
    int nFunctionalCells, nFunctionalProbes, nFunctionalLimits, nParityCells, nParityProbes, nParityLimits;
    int nCarryProbeLimit, nCarryConflictLimit;
    int nGridChainAttempts, nGridChainProved, nGridChainSteps, nGridChainLimits;
    ABC_INT64_T nGridChainWork;
    ABC_INT64_T nRecoverySteps;
    int nXorExpanded, nXorExpansionLimits;
    ABC_INT64_T nCutChecks, nCutCorrections, nUnconfirmedCuts;
};

// Local deadlines limit an attempt. Only caller cancellation is shared and
// latched across attempts, copied parameter structs, and Boolean solvers.
static inline int Acec2_Cancelled( Acec2_Par_t * p )
{
    if ( p->pCancelled && *p->pCancelled ) return 1;
    if ( !p->pFuncStop || !p->pFuncStop(p->RunId) ) return 0;
    if ( p->pCancelled ) *p->pCancelled = 1;
    return 1;
}
static inline int Acec2_Stop( Acec2_Par_t * p, abctime Deadline )
{
    return Acec2_Cancelled(p) || (Deadline && Abc_Clock() >= Deadline);
}
static inline word Acec2_Random( word * pState )
{
    *pState ^= *pState << 13; *pState ^= *pState >> 7; *pState ^= *pState << 17;
    return *pState;
}
static inline int Acec2_Stopped( Acec2_Man_t * p )
{
    if ( p->fStopped )
        return 1;
    if ( Acec2_Stop(&p->Pars, p->Deadline) )
        p->fStopped = 1;
    return p->fStopped;
}
static inline Acec2_Cell_t * Acec2_Cell( Acec2_Man_t * p, int i )
{
    return (Acec2_Cell_t *)Vec_PtrEntry( p->vCells, i );
}
static inline Acec2_Word_t * Acec2_Word( Acec2_Man_t * p, int Tree )
{
    int i = Vec_IntEntry(p->vTreeWord, Tree);
    return i < 0 ? NULL : (Acec2_Word_t *)Vec_PtrEntry(p->vWords, i);
}
static inline Acec2_Expr_t * Acec2_Expression( Acec2_Man_t * p, int Tree )
{
    int i = Vec_IntEntry(p->vTreeExpression, Tree);
    return i < 0 ? NULL : (Acec2_Expr_t *)Vec_PtrEntry(p->vExpressions, i);
}
// Unsigned masks also make bit 31 well-defined under UBSan and on MSVC.
static inline void Acec2_BitWrite( Vec_Bit_t * p, int i, int Value )
{
    unsigned * pWords = (unsigned *)p->pArray;
    assert( i >= 0 && i < p->nSize && (Value == 0 || Value == 1) );
    if ( Value ) Abc_InfoSetBit(pWords, i);
    else pWords[i >> 5] &= ~(1u << (i & 31));
}

/**Function*************************************************************

  Synopsis    [Evaluates one gate in a private bit-parallel simulation array.]

  Description [Stride and Lane support several words per node. Native XORs,
  muxes and complemented edges use the same semantics in every caller.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline word Acec2_SimGate( Gia_Man_t * g, int id, Vec_Wrd_t * values, int Stride, int Lane )
{
    Gia_Obj_t * o = Gia_ManObj(g, id);
    word a = Vec_WrdEntry(values, Stride*Gia_ObjFaninId0(o, id)+Lane);
    word b = Vec_WrdEntry(values, Stride*Gia_ObjFaninId1(o, id)+Lane);
    if ( Gia_ObjFaninC0(o) ) a = ~a;
    if ( Gia_ObjFaninC1(o) ) b = ~b;
    if ( Gia_ObjIsMux(g, o) )
    {
        word c = Vec_WrdEntry(values, Stride*Gia_ObjFaninId2(g, id)+Lane);
        if ( Gia_ObjFaninC2(g, o) ) c = ~c;
        return (c & b) | (~c & a);
    }
    return Gia_ObjIsXor(o) ? a ^ b : a & b;
}

extern int          Acec2_UnionFind( int * Parent, int * Delta, int * Flip, int x, int fLiteral );
extern int          Acec2_CopyGate( Gia_Man_t * src, Gia_Man_t * dst, Vec_Int_t * map, int id );
extern int          Acec2_CopyCone( Gia_Man_t * src, Gia_Man_t * dst, Vec_Int_t * map, Vec_Int_t * roots, Vec_Int_t * order,
                                    Acec2_Par_t * pars, abctime deadline );
extern void         Acec2_WriteList( FILE * f, Vec_Int_t * values, int Step, int Limit );

static inline int Acec2_LitFind( Vec_Int_t * parents, int lit )
{
    return Acec2_UnionFind(Vec_IntArray(parents), NULL, NULL, lit >> 1, 1) ^ (lit & 1);
}

static inline int Acec2_WeightFind( int * Parent, int * Delta, int * Flip, int x )
{
    return Acec2_UnionFind(Parent, Delta, Flip, x, 0);
}

/**Function*************************************************************

  Synopsis    [Reads a completed proof independently of its search budget.]

  Description [Returns zero for a new obligation, one for a proof, two for
  a completed rejection, and minus one for a previously exhausted effort.
  Effort results apply only to the same recipe with no larger limits.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Acec2_ProofCacheRead( Vec_Int_t * v, int Id, int Limit, Acec2_Par_t * p )
{
    int status, savedLimit, savedTier;
    if ( Id < 0 ) return 0;
    status = Vec_IntEntry(v, 4*Id);
    if ( status != 3 ) return status;
    savedLimit = Vec_IntEntry(v, 4*Id+1); savedTier = Vec_IntEntry(v, 4*Id+2);
    if ( Vec_IntEntry(v, 4*Id+3) != (int)(p->nCecOptions & ACEC2_CEC_DEFER) ) return 0;
    if ( (savedLimit && (!Limit || Limit > savedLimit)) ||
         (savedTier && (!p->nCecPolyLimit || p->nCecPolyLimit > savedTier)) ) return 0;
    return -1;
}

/**Function*************************************************************

  Synopsis    [Stores exact outcomes separately from deterministic exhaustion.]

  Description [The caller excludes deadline and cancellation results.
  Only completed proofs or rejections survive increases in search effort.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Acec2_ProofCacheWrite( Vec_Int_t * v, int Id, int Limit,
                                        Acec2_Par_t * p, int Result, int fEffort )
{
    int old;
    if ( Id < 0 || (Result < 0 && !fEffort) ) return;
    old = Vec_IntEntry(v, 4*Id); if ( old == 1 || old == 2 ) return;
    Vec_IntWriteEntry(v, 4*Id, Result == 1 ? 1 : Result == 0 ? 2 : 3);
    Vec_IntWriteEntry(v, 4*Id+1, Limit); Vec_IntWriteEntry(v, 4*Id+2, p->nCecPolyLimit);
    Vec_IntWriteEntry(v, 4*Id+3, (int)(p->nCecOptions & ACEC2_CEC_DEFER));
}

extern int          Acec2_IndexLookup( Hsh_Int1Man_t * p, int Key );
extern void         Acec2_BuildParity( Acec2_Man_t * p );
extern void         Acec2_PairParities( Acec2_Man_t * p, Vec_Ptr_t * vCandidates );
extern int          Acec2_ParityBuild( Acec2_Man_t * p, Gia_Man_t * g, Vec_Int_t * vMap, int Lit, int Mask );
extern int          Acec2_CheckParityCell( Acec2_Man_t * p, Acec2_Cell_t * c );
extern int          Acec2_ParityHasLeaf( Acec2_Man_t * p, int Lit, int Leaf );
extern int          Acec2_ParityCarryRefs( Acec2_Man_t * m, Acec2_Cell_t * c, Vec_Int_t * seen, int Stamp, Vec_Int_t * stack );
extern void         Acec2_ParityFree( Acec2_ParityCtx_t * p );
extern int          Acec2_EnrichMasked( Acec2_Man_t * p, Vec_Bit_t * vLive, int * pnQueries );
extern int          Acec2_RecordImportMasked( Acec2_Man_t * p, Acec2_Man_t * pChild, Acec2_Record_t * r,
                                            Vec_Int_t * vBack, Vec_Int_t * vMasks );
extern int          Acec2_IndexAdd( Hsh_Int1Man_t * p, int Key );
extern int          Acec2_WordCarryPatterns( Acec2_Word_t * p, Hsh_Int1Man_t * hCuts, Vec_Wrd_t * vValues, int Round );
extern Acec2_WordSim_t * Acec2_WordSimStart( Gia_Man_t * g, Vec_Int_t * vStop, int Width );
extern Acec2_WordSim_t * Acec2_WordSimCached( Acec2_Man_t * m, Vec_Int_t * vMap, Hsh_Int1Man_t * hCuts, int Width );
extern void         Acec2_WordSimStop( Acec2_WordSim_t * p );
extern void         Acec2_WordPrioritize( Acec2_WordSim_t * p, Acec2_Man_t * m );
extern void         Acec2_OperandPatterns( Vec_Int_t ** vOps, Hsh_Int1Man_t * hCuts, Vec_Wrd_t * vValues, int Round, word * pState );
extern void         Acec2_ProductPatterns( Vec_Int_t ** vOps, Hsh_Int1Man_t * hCuts, Vec_Wrd_t * vValues, Vec_Wrd_t * vExpected, int Width );
extern void         Acec2_ModelPatterns( Vec_Int_t ** vOps, Hsh_Int1Man_t * hCuts, Vec_Wrd_t * vValues,
                                        Vec_Wrd_t * vExpected, int Width, Gia_Man_t * pModel );
extern void         Acec2_WordSimulate( Acec2_WordSim_t * p, Vec_Wrd_t * vValues, Vec_Wrd_t * vExpected, int Round );
extern Vec_Int_t *  Acec2_ProductReference( Gia_Man_t * g, Vec_Int_t ** vOps, Hsh_Int1Man_t * hCuts, int Mode, int Width );
extern Gia_Man_t *  Acec2_ExtractWord( Acec2_WordSim_t * p, int Mode, int Width, int Prefix, int nInputs,
                                     Vec_Int_t ** pvRoots, Vec_Int_t ** vOps, Hsh_Int1Man_t * hCuts, int Strategy, Gia_Man_t * pModel );

extern int          Acec2_PolyCompare( Acec2_Man_t * p0, Acec2_Man_t * p1, abctime Deadline, Abc_Cex_t ** ppCex );
extern int          Acec2_CheckCut( Acec2_Man_t * p, int * pCut, Vec_Int_t * vTruth,
                                    Vec_Int_t * vStack, Vec_Int_t * vTouched );
extern void         Acec2_RefreshCounterRecords( Acec2_Man_t * m );
extern int          Acec2_RecordFullProductWidth( Acec2_Record_t * r );
extern int          Acec2_ProveGridExpression( Acec2_Man_t * m, int Record, Vec_Ptr_t * products, Vec_Int_t * outputs,
                                             int Width, int Offset, int * pPrefix );
extern void         Acec2_PairRecovered( Acec2_Man_t * m, Vec_Ptr_t * candidates, int First );
extern int          Acec2_PolyComparePrefix( Acec2_Man_t * p0, Acec2_Man_t * p1, int Width, abctime Deadline );
extern int          Acec2_PolyCompareQuiet( Acec2_Man_t * p0, Acec2_Man_t * p1, abctime Deadline );
extern int          Acec2_PolyWordBoundaryPrefix( Acec2_Man_t * p, Acec2_Record_t * r, Vec_Int_t * vBits );
extern int          Acec2_PolyLinearPrefix( Acec2_Man_t * p, Acec2_Word_t * w, Vec_Int_t * vBits );
extern int          Acec2_PolyCheckProduct( Acec2_Man_t * p, Vec_Int_t ** vOps, int Mode,
                                          int Width, int nTermLimit, abctime Deadline );
extern int          Acec2_PolyCompareCex( Acec2_Man_t * p0, Acec2_Man_t * p1, abctime Deadline, Abc_Cex_t ** ppCex );
extern int          Acec2_CexOutput( Gia_Man_t * p, Abc_Cex_t * pCex, int iOut );
extern int          Acec2_ProveBddLimit( Gia_Man_t ** g, Vec_Int_t * vOrder, Acec2_Par_t * pPars, abctime Deadline,
                                       Abc_Cex_t ** ppCex, int nLimit, int * pfLimited );
extern Gia_Man_t *  Acec2_CompleteWord( Acec2_Man_t * m, Vec_Int_t * vObserved, abctime Deadline, Vec_Int_t ** pvRules );
extern int          Acec2_MapNode( Gia_Man_t * pGia, Gia_Man_t * pNew, Vec_Int_t * vMap, Gia_Obj_t * o, int Id );
extern int          Acec2_AliasUpdate( Gia_Man_t * pNew, Vec_Int_t ** vMaps, Vec_Int_t ** vReplaces,
                                     Acec2_Par_t * pPars, abctime Deadline );
extern int          Acec2_AliasApply( Gia_Man_t * pNew, Vec_Int_t ** vMaps, Vec_Int_t ** vReplaces,
                                     Vec_Int_t * vOutputs, Vec_Int_t * vPairs, Acec2_Par_t * pPars, abctime Deadline );
typedef struct Acec2_Templ_t_ Acec2_Templ_t;
extern Acec2_Templ_t * Acec2_TemplateStart( void );
extern void         Acec2_TemplateStop( Acec2_Templ_t * p );
extern void         Acec2_TemplateNewProofs( Acec2_Templ_t * p );
extern void         Acec2_TemplateSetPending( Acec2_Templ_t * p );
extern int          Acec2_TemplatePending( Acec2_Templ_t * p, int fClear );
extern Vec_Int_t *  Acec2_ProductBits( Gia_Man_t * g, Vec_Int_t ** vOps, int Mode, int Width );
extern int          Acec2_TemplateMatch( Gia_Man_t * pNew, Vec_Int_t ** vMaps, Vec_Int_t ** vOriginals, Vec_Int_t ** vReplaces,
                                         Vec_Int_t ** vOps, int Width, Acec2_Par_t * pPars, abctime Deadline, int * pnWords, Acec2_Templ_t * pTemplates );
extern int          Acec2_TemplateShifted( Gia_Man_t * pNew, Vec_Int_t ** vMaps, Vec_Int_t ** vOriginals, Vec_Int_t ** vReplaces,
                                         Vec_Int_t ** vOps, int Width, Acec2_Par_t * pPars, abctime Deadline, int * pnWords, Acec2_Templ_t * pTemplates );
typedef enum { ACEC2_MATCH_INITIAL = -1, ACEC2_MATCH_ALL = 0, ACEC2_MATCH_PENDING = 2,
               ACEC2_MATCH_CHEAP = 3, ACEC2_MATCH_BOUNDARY = 4 } Acec2_MatchMode_t;
extern int          Acec2_MatchProducts( Gia_Man_t * pNew, Acec2_Man_t ** m, Vec_Int_t ** vMaps, Vec_Int_t ** vOriginals, Vec_Int_t ** vReplaces,
                                        Acec2_Par_t * pPars, abctime Deadline, Acec2_MatchMode_t Mode, int * pnWords, Acec2_Templ_t * pTemplates );
extern int          Acec2_MatchTruth( Gia_Man_t * pNew, Acec2_Man_t ** pMans, Vec_Int_t ** vMaps, Vec_Int_t ** vReplaces,
                                     Vec_Int_t * vFrontier, Acec2_Par_t * pPars, abctime Deadline );
extern int          Acec2_CertifyProducts( Gia_Man_t * pNew, Acec2_Man_t ** pMans, Vec_Int_t ** vMaps,
                                         Vec_Int_t ** vReplaces, Vec_Int_t ** vOps, int Width,
                                         Acec2_Par_t * pPars, abctime Deadline, int * pnWords, int * pPrefix );
extern Acec2_Word_t * Acec2_CertifyProductWord( Acec2_Man_t * m, Acec2_Product_t * pProduct, int Prefix );
extern void         Acec2_WordFree( Acec2_Word_t * p );
typedef struct Acec2_PolyCtx_t_ Acec2_PolyCtx_t;
extern Acec2_PolyCtx_t * Acec2_PolyRegionStart( Acec2_Man_t * p, Vec_Int_t * vMap, Vec_Int_t * vFrontier );
extern int          Acec2_PolyRegionUpdate( Acec2_PolyCtx_t * p, Vec_Int_t * vMap, Vec_Int_t * vFrontier );
extern void         Acec2_PolyRegionReuse( Acec2_PolyCtx_t * p, int * pHits, int * pLimits );
extern void         Acec2_PolyRegionStop( Acec2_PolyCtx_t * p );
extern int          Acec2_PolyRegion( Acec2_PolyCtx_t * p, int Tree, Vec_Int_t * vRoots, Gia_Man_t * pNew,
                                     Vec_Wec_t * vCols, Vec_Int_t * vConst, abctime Deadline,
                                     int nMaxObjs, int * pFlip );
extern void         Acec2_Detect( Acec2_Man_t * p );
extern Vec_Int_t *  Acec2_RecordCover( Acec2_Man_t * p );
extern Acec2_Cell_t * Acec2_MatchCut( int * pSum, int * pCarry );
extern void         Acec2_RecoverCarries( Acec2_Man_t * p, Vec_Ptr_t * vCandidates );
extern int          Acec2_AdvanceCarries( Acec2_Man_t * p, Vec_Bit_t * vLive, int * pnWork );
extern void         Acec2_CarryStop( Acec2_Man_t * p );
extern int          Acec2_EnrichCarries( Acec2_Man_t * p, Vec_Bit_t * vLive, int * pnWork );
extern int          Acec2_ImportCells( Acec2_Man_t * p, Vec_Ptr_t * vCandidates );
extern void         Acec2_RecoverParityCells( Acec2_Man_t * m, Vec_Ptr_t * vCandidates );
extern void         Acec2_BuildXors( Acec2_Man_t * p );
extern int          Acec2_WeightUnion( int * Parent, int * Delta, int * Flip, int * Size, int a, int b, int d, int f );
extern int          Acec2_GetPart( Acec2_Man_t * p, int Kind, int Id, Acec2_Part_t * b );
extern void         Acec2_BuildCounterRegions( Acec2_Man_t * p );
extern void         Acec2_BuildCellRegions( Acec2_Man_t * p );
extern void         Acec2_BuildClosureRegions( Acec2_Man_t * p );
extern Acec2_Record_t * Acec2_RecordAlloc( int Width );
extern int          Acec2_RecordPopulate( Acec2_Man_t * p, Acec2_Record_t * r );
extern Acec2_Product_t * Acec2_RecordProduct( Acec2_Man_t * p, Acec2_Record_t * r );
extern int          Acec2_CertifyLinearWord( Acec2_Man_t * p, Acec2_Word_t * w, int Minimum );
extern int          Acec2_WordOperandPatterns( Acec2_Man_t * p, Acec2_Word_t * w, Hsh_Int1Man_t * h, Vec_Wrd_t * vValues, int Round );
extern void         Acec2_CloseWords( Acec2_Man_t * p );
extern int          Acec2_CloseRecordWord( Acec2_Man_t * p, int Record, int * pnQueries );
extern void         Acec2_CloseRecordWords( Acec2_Man_t * p );
extern void         Acec2_DiscoverLinearWords( Acec2_Man_t * p );
extern int          Acec2_DiscoverLinearRegion( Acec2_Man_t * p, int Tree, int * pnQueries );
extern Acec2_Record_t * Acec2_RecordWord( Acec2_Man_t * p, int Word, int Parent );
extern int          Acec2_RecordAddProductWord( Acec2_Man_t * p, Acec2_Word_t * pWord, int Tree );
extern int          Acec2_RecordOutputPolynomial( Acec2_Man_t * p, int Width, Hsh_VecMan_t * hMonomials, Vec_Wrd_t * vCoefficients );
extern void         Acec2_FindCounters( Acec2_Man_t * p );
extern int          Acec2_AdvanceCounters( Acec2_Man_t * p, Vec_Bit_t * vLive, int * pnWork );
extern void         Acec2_CounterStop( Acec2_Man_t * p );
extern int          Acec2_CounterCheck( Acec2_Man_t * p, Acec2_Counter_t * c, Vec_Int_t * vGates );
extern int          Acec2_CounterTruth( Acec2_Man_t * p, Acec2_Counter_t * c, word * pTruth );
extern void         Acec2_CountersWriteJson( Acec2_Man_t * p, FILE * f );
extern void         Acec2_BuildRecords( Acec2_Man_t * p );
extern void         Acec2_BuildRecordsBasic( Acec2_Man_t * p );
extern void         Acec2_RecordTreeWord( Acec2_Man_t * p, int Tree );
extern int          Acec2_EnrichRegion( Acec2_Man_t * p, int Tree, int Level, int * pnQueries );
extern int          Acec2_EnrichCounters( Acec2_Man_t * p, Vec_Bit_t * vLive, int * pnWork );
extern int          Acec2_EnrichPolynomial( Acec2_Man_t * p, int * pnWork );
extern int          Acec2_ProveWeighted( Acec2_Man_t * p, Vec_Int_t * vOutputs, Vec_Int_t * vTerms, Vec_Int_t * vConstants, int Width );
extern int          Acec2_ProveWeightedProducts( Acec2_Man_t * p, Vec_Int_t * vOutputs, Vec_Int_t * vTerms, Vec_Int_t * vConstants, Vec_Int_t * vProducts, int Width );
extern int          Acec2_ProveWeightedCut( Acec2_Man_t * p, Vec_Int_t * vOutputs, Vec_Int_t * vTerms, Vec_Int_t * vConstants, Vec_Int_t * vProducts, Vec_Int_t * vCut, int Width );
extern int          Acec2_PolyWeighted( Acec2_Man_t * p, Vec_Int_t * vOutputs, Vec_Int_t * vTerms, Vec_Int_t * vConstants, Vec_Int_t * vProducts, int Width );
extern int          Acec2_PolyWeightedQuick( Acec2_Man_t * p, Vec_Int_t * vOutputs, Vec_Int_t * vTerms, Vec_Int_t * vConstants, Vec_Int_t * vProducts, int Width );
extern int          Acec2_RecordWeighted( Acec2_Man_t * p, Vec_Int_t * vOutputs, Vec_Int_t * vTerms, Vec_Int_t * vConstants, int Width );
extern int          Acec2_ProveProductGridPrefix( Acec2_Man_t * p, int Record, Acec2_Product_t * product, Vec_Int_t * vOutputs, int * pPrefix );
extern int          Acec2_RecordGridProduct( Acec2_Man_t * p, int Record, Acec2_Product_t * product, Vec_Int_t * vOutputs );
extern int          Acec2_RecordGridExpression( Acec2_Man_t * p, int Record, Vec_Ptr_t * products, Vec_Int_t * vOutputs, int Width, int Offset );
extern int          Acec2_RecordLiftParts( Acec2_Man_t * p, int Parent, int Width );
extern int          Acec2_RecordCompose( Acec2_Man_t * p, int First, int Second, int Width );
extern int          Acec2_CloseRecordGaps( Acec2_Man_t * p, int Record, int * pnQueries );
extern void         Acec2_CloseGaps( Acec2_Man_t * p );
extern int          Acec2_GapRecord( Acec2_Man_t * p, int Record );
extern void         Acec2_PrintGapProducts( Acec2_Man_t * p, FILE * f, int fJson );
extern void         Acec2_GapStop( Acec2_Man_t * p );
extern void         Acec2_RecordWriteJson( Acec2_Man_t * p, FILE * f );
extern void         Acec2_RecordFree( Acec2_Record_t * p );
extern int          Acec2_RecordCheck( Acec2_Man_t * p, Acec2_Record_t * r );
extern int          Acec2_CheckRegion( Acec2_Man_t * m, int Tree, int Width );
extern Vec_Int_t *  Acec2_ExprOperand( Acec2_Man_t * m, Vec_Int_t * vBits, int fSigned, int * pLifted, abctime Deadline );
extern int          Acec2_WeightedWidth( Vec_Int_t * vTerms, int Limit );
extern int          Acec2_RecordColumns( Acec2_Record_t * r, Gia_Man_t * g, Vec_Int_t * vMap,
                                        Vec_Int_t * vFrontier, Vec_Wec_t * vCols, Vec_Int_t * vConst,
                                        Acec2_Par_t * pPars, abctime Deadline, int nMaxObjs );
typedef struct Acec2_RecordMatch_t_ Acec2_RecordMatch_t;
extern Acec2_RecordMatch_t * Acec2_RecordMatchStart();
extern void         Acec2_RecordMatchStop( Acec2_RecordMatch_t * p );
extern int          Acec2_MatchRecordsStep( Acec2_Man_t ** m, Vec_Int_t ** vMaps, Vec_Int_t ** vReplaces,
                                           Vec_Int_t * vFrontier, Acec2_Par_t * pPars, abctime Deadline,
                                           int * pnWords, Acec2_RecordMatch_t * p );
extern void         Acec2_FindExpressions( Acec2_Man_t * p );
extern void         Acec2_FindExpression( Acec2_Man_t * p, int Tree );
extern Vec_Ptr_t *   Acec2_RecordFactors( Acec2_Man_t * m, Acec2_Record_t * r, Vec_Int_t * vMap, int * pWidth );
extern Vec_Ptr_t *   Acec2_RecordProductProposals( Acec2_Man_t * m, Acec2_Record_t * r, Vec_Int_t * vMap );
extern Vec_Ptr_t *   Acec2_RegionProductProposals( Acec2_Man_t * m, int Tree );
extern Vec_Ptr_t *   Acec2_RecordProductGrid( Acec2_Man_t * m, Acec2_Record_t * r );
extern Vec_Int_t *   Acec2_ProductLeaves( Acec2_Man_t * m, int Tree );
extern void         Acec2_TruthCacheStop( Acec2_TruthCache_t * p );
extern void         Acec2_ExprFree( Acec2_Expr_t * p );
extern int          Acec2_ExprColumns( Acec2_Man_t * m, Acec2_Expr_t * e, Gia_Man_t * g, Vec_Int_t * vMap,
                                     Vec_Wec_t * vCols, Vec_Int_t * vConst, int nMaxObjs, abctime Deadline );
extern int          Acec2_CompressColumn( Gia_Man_t * g, Vec_Wec_t * vCols, Vec_Int_t * vConst, Vec_Int_t * vNext,
                                        int Rank, Acec2_Par_t * pPars, abctime Deadline, int nMaxObjs );
extern Acec2_Man_t * Acec2_AnalyzeLimit( Gia_Man_t * pGia, Acec2_Par_t * pPars, abctime Deadline );
extern Acec2_Man_t * Acec2_AnalyzeFocused( Gia_Man_t * pGia, Acec2_Par_t * pPars, abctime Deadline, Vec_Bit_t * vFocus );
extern Acec2_Man_t * Acec2_AnalyzeCec( Gia_Man_t * pGia, Acec2_Par_t * pPars, abctime Deadline );
extern Acec2_Man_t * Acec2_AnalyzeSourceCells( Gia_Man_t * pGia, Acec2_Par_t * pPars, abctime Deadline );
extern Acec2_Man_t * Acec2_AnalyzeCells( Gia_Man_t * pGia, Acec2_Par_t * pPars, abctime Deadline );
extern int          Acec2_ProveBounded( Gia_Man_t * pMiter, Acec2_Par_t * pPars, abctime Deadline, int nIters );
extern int          Acec2_ProveContext( Gia_Man_t * pMiter, Acec2_Par_t * pPars, abctime Deadline );
extern int          Acec2_ProveConcreteEx( Gia_Man_t * pMiter, Acec2_Par_t * pPars, abctime Deadline, Vec_Int_t * vPairs, int fWide );
extern int          Acec2_CheckSimulation( Gia_Man_t * p0, Gia_Man_t * p1, Gia_Man_t * pMiter,
                                          Acec2_Par_t * pPars, abctime Deadline, Abc_Cex_t ** ppCex );
typedef struct Acec2_NormStats_t_ Acec2_NormStats_t;
struct Acec2_NormStats_t_
{
    int nRegions, nSkipped, nBefore, nAfter;
    int nRoots[2], nMatched[2], nNew[2], nSelected[2];
    int nPolyTried[2], nPolyDone[2];
    int nExpressions[2];
    int nPolyReused[2], nPolyLimits[2];
    int nMacroWords, nMacroBits, nTruthBits;
    int nRecordWords, nRecordBits;
    int nProfileRecords[2], fProfileLimited[2];
    int nProfileBits, nProfileWords, fProfileTried, nProfileAnds[2];
    abctime TimeProfile[2];
    abctime TimeSetup, TimeRecords, TimeLocal, TimeMatch, TimeRebuild, TimeCec, TimeTotal;
    int iPendingStep;          // setup, records, local normalization, matching, rebuild, CEC, profile
    int nEffortTier, nEffortEscalations;
    int nPasses, fPassLimit;    // bounded arithmetic loop; distinct from a fixed point
    int fArithmeticBudget;    // arithmetic time share exhausted before ordinary CEC
    int iLastStage;             // boundary recovery=1, arithmetic proof=2, surrounding CEC=3
    int fContextProved;         // exact context proof of the returned miter
};
extern Gia_Man_t *  Acec2_BuildMiterBudget( Gia_Man_t * pGia0, Gia_Man_t * pGia1,
                                         Acec2_Man_t * p0, Acec2_Man_t * p1,
                                         Acec2_Par_t * pPars, abctime Deadline,
                                         abctime CecTime, Acec2_NormStats_t * pStats );
extern Gia_Man_t *  Acec2_BuildMiterEx( Gia_Man_t * pGia0, Gia_Man_t * pGia1,
                                     Acec2_Man_t * p0, Acec2_Man_t * p1,
                                     Acec2_Par_t * pPars, abctime Deadline, Acec2_NormStats_t * pStats );

ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
