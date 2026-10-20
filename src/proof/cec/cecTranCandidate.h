// Transaction candidates, recipes, and canonicalization.
// Private implementation fragment included only by cecTrans.c.

// The check is exact over the current signature batch (not hash-based), so a
// duplicate cannot consume one of the expensive formal-proof slots.  Signature
// equality may merge different functions only on unsampled patterns, which
// can lose a search opportunity but can never compromise correctness.
// Convert an old-network literal into its literal in the network currently
// being duplicated.  All candidate divisors precede the target, so their
// copies are available when the target is rebuilt.
static inline int Cec_TranCopyLit( Gia_Man_t * p, int iLit )
{
    Gia_Obj_t * pObj = Gia_ManObj( p, Abc_Lit2Var(iLit) );
    assert( ~pObj->Value );
    return Abc_LitNotCond( pObj->Value, Abc_LitIsCompl(iLit) );
}

// Root-only transduction optimizes the AND network while preserving the
// sequential interface.  Generic sequential cleanup is allowed to delete
// latches that become unobservable after a constant replacement, which makes
// AND-only gain accounting inconsistent and changes the register boundary.
// The final root bundle therefore performs combinational cleanup only.
static inline int Cec_TranMapLitByValue( Gia_Man_t * p, int iLit )
{
    int iMapped = Gia_ManObj(p, Abc_Lit2Var(iLit))->Value;
    return iMapped == ~0 ? -1 :
        Abc_LitNotCond( iMapped, Abc_LitIsCompl(iLit) );
}

// Gia_ManDup() deliberately copies only the Boolean/sequential graph and does
// not copy the AIGER property partition.  Transduction product graphs must keep
// the last nConstrs POs typed as constraints; proof-only miters must not inherit
// this metadata.  Keep the operation local and explicit at product boundaries.
static inline void Cec_TranAssertTypedInterface( Gia_Man_t * p,
    Gia_Man_t * pNew )
{
    assert( Gia_ManPiNum(pNew) == Gia_ManPiNum(p) );
    assert( Gia_ManPoNum(pNew) == Gia_ManPoNum(p) );
    assert( Gia_ManRegNum(pNew) == Gia_ManRegNum(p) );
    assert( Gia_ManConstrNum(p) >= 0 &&
            Gia_ManConstrNum(p) <= Gia_ManPoNum(p) );
    assert( Gia_ManConstrNum(pNew) == Gia_ManConstrNum(p) );
}

static inline Gia_Man_t * Cec_TranDupProduct( Gia_Man_t * p )
{
    Gia_Man_t * pNew = Gia_ManDup( p );
    pNew->nConstrs = p->nConstrs;
    Cec_TranAssertTypedInterface( p, pNew );
    return pNew;
}

// Return the exact input-object -> normalized-output literal map when asked.
// This is the proof-history bridge across a commit: object IDs are disposable,
// but a proved relation can be reused after both cleanup renumberings if every
// endpoint and recipe leaf has a surviving mapped literal.
static Gia_Man_t * Cec_TranCleanupKeepRegs( Gia_Man_t * p,
    Vec_Int_t ** pvMap )
{
    Gia_Man_t * pNew, * pTemp;
    Vec_Int_t * vMap = pvMap ? Vec_IntStartFull(Gia_ManObjNum(p)) : NULL;
    Gia_Obj_t * pObj;
    int i, iLit;
    pNew = Gia_ManCleanup( pTemp = Cec_TranDupProduct(p) );
    if ( vMap )
        Gia_ManForEachObj( p, pObj, i )
        {
            iLit = Cec_TranMapLitByValue( p, Abc_Var2Lit(i, 0) );
            if ( iLit >= 0 )
                iLit = Cec_TranMapLitByValue( pTemp, iLit );
            Vec_IntWriteEntry( vMap, i, iLit );
        }
    Gia_ManStop( pTemp );
    pNew = Gia_ManDupNormalize( pTemp = pNew, 0 );
    if ( vMap )
        Vec_IntForEachEntry( vMap, iLit, i )
            if ( iLit >= 0 )
                Vec_IntWriteEntry( vMap, i,
                    Cec_TranMapLitByValue(pTemp, iLit) );
    Gia_ManStop( pTemp );
    Cec_TranAssertTypedInterface( p, pNew );
    if ( pvMap )
        *pvMap = vMap;
    return pNew;
}

static int Cec_TranGain( Gia_Man_t * p, Gia_Man_t * pCand )
{
    return Gia_ManAndNum(p) + Gia_ManRegNum(p)
         - Gia_ManAndNum(pCand) - Gia_ManRegNum(pCand);
}

static int Cec_TranAllPosAreZero( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i;
    Gia_ManForEachPo( p, pObj, i )
        if ( Gia_ObjFaninId0p(p, pObj) != 0 || Gia_ObjFaninC0(pObj) )
            return 0;
    return 1;
}

static inline int Cec_TranHashGate( Gia_Man_t * pNew, Gia_Obj_t * pObj, int iLit0, int iLit1 )
{
    return Gia_ObjIsXor(pObj) ? Gia_ManHashXor(pNew, iLit0, iLit1) :
        Gia_ManHashAnd(pNew, iLit0, iLit1);
}

// Mark the complete combinational TFO of the edited target, including the
// PO/RI boundaries.  A marked RI is emitted as a difference PO by the local
// miter; its corresponding RO is then related inductively by the common
// source-state machine built below.
// Compute the sampled care used by the bounded-window proof.  Unlike output
// scope, the window obligation observes the exact TFO cut as well as every
// PO/RI reached before the cut.  Re-simulating the marked cone with the root
// flipped therefore makes a harvested window CEX a real new dependency
// constraint instead of relying only on the tried-recipe history to avoid
// proposing the same invalid function again.
// Construct a single-state sequential difference machine.  It shares the
// original transition relation, duplicates only the target's combinational
// TFO for the edited variant, and emits differences at all affected PO/RI
// boundaries.  Equality of the affected RIs, together with unchanged
// unmarked RIs, inductively establishes a common state trajectory.  Thus this
// is an exact COI reduction for these pure combinational edits, not a bounded
// window approximation.
// This is intentionally the same sequential proof engine used by &scorr:
// bounded reset-reachable BMC followed by its inductive correspondence
// refinement.  The difference is the query: &stran proves a proposed
// transduction transaction, rather than asking scorr to merge an equivalence
// class in the original network.
static int Cec_TranProveWhole( Gia_Man_t * p, Gia_Man_t * pCand,
    Cec_ParTran_t * pPars, Cec_TranProf_t * pProf )
{
    Cec_ParCor_t Cor;
    Gia_Man_t * pMiter, * pReduced;
    int fProved;
    pMiter = Gia_ManMiter( p, pCand, 0, 0, 1, 0, 0 );
    if ( pMiter == NULL )
        return 0;
    Cec_ManCorSetDefaultParams( &Cor );
    Cor.nFrames   = pPars->nFrames;
    Cor.nBTLimit  = pPars->nBTLimit;
    Cor.nConfTotal = pPars->nHardConfTotal;
    Cor.nStepsMax = pPars->nStepsMax;
    Cor.fVerbose  = 0;
    Cor.pProfile  = (pPars->fProfile || pPars->fVerbose) ? &pProf->Corr : NULL;
    pReduced = Cec_ManLSCorrespondence( pMiter, &Cor );
    // A total-budget stop leaves unrefined speculative classes in pReduced.
    // They must never be interpreted as a discharged transaction.
    fProved = !Cor.fConfStop && Cec_TranAllPosAreZero( pReduced );
    Gia_ManStop( pReduced );
    Gia_ManStop( pMiter );
    return fProved;
}

// Recover a concrete bounded counterexample only after the complete local
// proof has rejected a transaction.  The main &scorr oracle remains the
// acceptance proof; this BMC is solely a witness extractor for CEGIS.  A
// timeout/UNKNOWN cannot refine the pattern bank and is kept conservative.
// The candidate has already passed the exact structural-gain test.  This
// routine is the transactional boundary: no speculative wiring reaches p
// unless the sequential miter is discharged by scorr's proof infrastructure.
#define CEC_TRAN_RECIPE_NODES_MAX 100

// Recipe fanins use ordinary non-negative GIA literals for external signals.
// A negative value encodes a literal of an already-created recipe gate.  This
// keeps a candidate self-contained after the temporary divisor pool is freed
// and makes remapping across committed snapshots straightforward.
static inline int Cec_TranRecipeGateCode( int iGate, int fCompl )
{
    return -2 - Abc_Var2Lit( iGate, fCompl );
}
static inline int Cec_TranRecipeCodeIsGate( int Code )
{
    return Code < -1;
}
static inline int Cec_TranRecipeGateLit( int Code )
{
    assert( Cec_TranRecipeCodeIsGate(Code) );
    return -Code - 2;
}

typedef struct Cec_TranCand_t_ Cec_TranCand_t;
typedef struct Cec_TranRecipe_t_ Cec_TranRecipe_t;
struct Cec_TranRecipe_t_
{
    int nRefs;
    int Data[1];
};
struct Cec_TranCand_t_
{
    int iTarget;
    int iDiv0;                  // display/compatibility: first external literal
    int iDiv1;                  // display/compatibility: second external literal
    int nMffc;
    int Gain;                   // local structural gain for scheduling
    int nGates;                 // dependency AIG nodes in Recipe[]
    int iOut;                   // external or recipe-gate literal code
    int * Recipe;               // shared, immutable, exactly 2*nGates ints
    unsigned fStrict   : 1;
    unsigned nKind     : 2;
    // nProofStage is the certificate strength currently safe to reuse.  A
    // commit may downgrade it to sequential.  The three origin fields never
    // change and keep reporting stable across remap/canonicalization.
    unsigned nProofStage : 2;   // 0=unproved, 1=combinational, 2=sequential
    unsigned nProofLane  : 2;   // original proof engine: 1=CBS, 2=scorr
    unsigned nProofPhase : 1;   // original algorithm phase: 0=COMB, 1=SEQ
    unsigned nProofKind  : 2;   // candidate kind when originally proved
    unsigned nStatus    : 3;    // candidate/stale/tried_seq/proved_comb/proved_seq/selected
    unsigned fExactTemplate : 1;// finite exact resub template (before greedy diversity)
    unsigned fDivRescue : 1;
    unsigned fDivGlobal : 1;
    unsigned fPrimaryFrontier : 1;
    unsigned fKitPortfolio : 1;
    unsigned fBdcPortfolio : 1;
    unsigned nResubStage : 3;    // iterator stage: 1/3/4 exact, 5 greedy
    int      nResubRank;         // 0=non-resub, otherwise raw recipe rank
    int      nCiOverlap;         // CI support overlap with root; ordering only
    int      nDivRankMax;        // worst (largest) ranked-divisor position used
    int      nDivRankSum;        // sum of ranked-divisor positions used
    int      nWave;              // zero-based root CEGAR wave
    int      nGreedyPathIndex;   // 1=primary; 2..4=experimental depth-2 path
};

static int Cec_TranBuildMffcBin( int Mffc )
{
    return Mffc <= 1 ? 0 : Mffc == 2 ? 1 : Mffc <= 4 ? 2 :
        Mffc <= 8 ? 3 : Mffc <= 16 ? 4 : 5;
}

static void Cec_TranProfilePivotAttempts( Cec_TranProf_t * pProf,
    long long const * pInfo )
{
    pProf->nRootGreedyPivotAttempts += pInfo[CEC_TRAN_PIVOT_ATTEMPT_TOTAL];
}

// Candidate vectors copy scheduling metadata by value, but all copies of a
// constructed candidate refer to one immutable, reference-counted recipe.
// Literal/constant candidates allocate no recipe at all.  Keeping the recipe
// out of Cec_TranCand_t is important because the root lane can contain every
// exact earlier literal and may therefore hold millions of zero-gate entries.
static int * Cec_TranRecipeAlloc( int nSize )
{
    Cec_TranRecipe_t * p;
    assert( nSize > 0 && nSize <= 2 * CEC_TRAN_RECIPE_NODES_MAX );
    p = (Cec_TranRecipe_t *)ABC_ALLOC( char,
        sizeof(Cec_TranRecipe_t) + sizeof(int) * (nSize - 1) );
    p->nRefs = 1;
    return p->Data;
}

static Cec_TranRecipe_t * Cec_TranRecipeHead( int const * pData )
{
    return (Cec_TranRecipe_t *)((char *)pData -
        offsetof(Cec_TranRecipe_t, Data));
}

static void Cec_TranCandRecipeRetain( Cec_TranCand_t const * pCand )
{
    if ( pCand->Recipe )
        Cec_TranRecipeHead(pCand->Recipe)->nRefs++;
}

static void Cec_TranCandRecipeRelease( Cec_TranCand_t * pCand )
{
    Cec_TranRecipe_t * pRecipe;
    if ( pCand->Recipe == NULL )
        return;
    pRecipe = Cec_TranRecipeHead( pCand->Recipe );
    assert( pRecipe->nRefs > 0 );
    if ( --pRecipe->nRefs == 0 )
        ABC_FREE( pRecipe );
    pCand->Recipe = NULL;
}

static inline int Cec_TranRecipeNotCode( int Code )
{
    int iLit;
    if ( !Cec_TranRecipeCodeIsGate(Code) )
        return Abc_LitNot( Code );
    iLit = Cec_TranRecipeGateLit( Code );
    return Cec_TranRecipeGateCode( Abc_Lit2Var(iLit),
        !Abc_LitIsCompl(iLit) );
}

static inline int Cec_TranRecipeMapCode( int Code, int const * pMap,
    int nMapped )
{
    int iLit, iGate;
    if ( !Cec_TranRecipeCodeIsGate(Code) )
        return Code;
    iLit = Cec_TranRecipeGateLit( Code );
    iGate = Abc_Lit2Var( iLit );
    assert( iGate < nMapped );
    return Abc_LitIsCompl(iLit) ?
        Cec_TranRecipeNotCode(pMap[iGate]) : pMap[iGate];
}

static void Cec_TranRecipeMarkUsed_rec( int Code, int const * pRecipe,
    int nGates, char * pUsed )
{
    int iGate;
    if ( !Cec_TranRecipeCodeIsGate(Code) )
        return;
    iGate = Abc_Lit2Var( Cec_TranRecipeGateLit(Code) );
    assert( iGate < nGates );
    if ( pUsed[iGate] )
        return;
    pUsed[iGate] = 1;
    Cec_TranRecipeMarkUsed_rec( pRecipe[2*iGate], pRecipe, nGates, pUsed );
    Cec_TranRecipeMarkUsed_rec( pRecipe[2*iGate+1], pRecipe, nGates, pUsed );
}

// Canonicalize the small recipe AIG before it enters a candidate set.  These
// are structural identities only: commutative fanins, constants, duplicate
// inputs, complementary inputs, one-level absorption, hash-identical gates,
// and dead gates.  Sampled dominance is deliberately not a pruning rule.
static void Cec_TranCandCanonicalizeRecipe( Cec_TranCand_t * pCand )
{
    int Work[2 * CEC_TRAN_RECIPE_NODES_MAX] = {0};
    int OldMap[CEC_TRAN_RECIPE_NODES_MAX] = {0};
    int CompactMap[CEC_TRAN_RECIPE_NODES_MAX];
    int Compact[2 * CEC_TRAN_RECIPE_NODES_MAX];
    char Used[CEC_TRAN_RECIPE_NODES_MAX] = {0};
    int i, k, a, b, Result, nWork = 0, nCompact = 0, iOut;
    if ( pCand->nGates == 0 )
        return;
    assert( pCand->nGates <= CEC_TRAN_RECIPE_NODES_MAX );
    for ( i = 0; i < pCand->nGates; i++ )
    {
        a = Cec_TranRecipeMapCode( pCand->Recipe[2*i], OldMap, i );
        b = Cec_TranRecipeMapCode( pCand->Recipe[2*i+1], OldMap, i );
        if ( a == 0 || b == 0 || a == Cec_TranRecipeNotCode(b) )
            Result = 0;
        else if ( a == 1 )
            Result = b;
        else if ( b == 1 || a == b )
            Result = a;
        else
        {
            Result = -1;
            if ( Cec_TranRecipeCodeIsGate(a) &&
                 !Abc_LitIsCompl(Cec_TranRecipeGateLit(a)) )
            {
                k = Abc_Lit2Var( Cec_TranRecipeGateLit(a) );
                if ( Work[2*k] == b || Work[2*k+1] == b )
                    Result = a;
            }
            if ( Result == -1 && Cec_TranRecipeCodeIsGate(b) &&
                 !Abc_LitIsCompl(Cec_TranRecipeGateLit(b)) )
            {
                k = Abc_Lit2Var( Cec_TranRecipeGateLit(b) );
                if ( Work[2*k] == a || Work[2*k+1] == a )
                    Result = b;
            }
            if ( Result == -1 )
            {
                if ( a > b ) { int t = a; a = b; b = t; }
                for ( k = 0; k < nWork; k++ )
                    if ( Work[2*k] == a && Work[2*k+1] == b )
                        break;
                if ( k < nWork )
                    Result = Cec_TranRecipeGateCode( k, 0 );
                else
                {
                    Work[2*nWork] = a;
                    Work[2*nWork+1] = b;
                    Result = Cec_TranRecipeGateCode( nWork++, 0 );
                }
            }
        }
        OldMap[i] = Result;
    }
    iOut = Cec_TranRecipeMapCode( pCand->iOut, OldMap, pCand->nGates );
    Cec_TranRecipeMarkUsed_rec( iOut, Work, nWork, Used );
    for ( i = 0; i < nWork; i++ )
    {
        CompactMap[i] = -1;
        if ( !Used[i] )
            continue;
        a = Cec_TranRecipeMapCode( Work[2*i], CompactMap, i );
        b = Cec_TranRecipeMapCode( Work[2*i+1], CompactMap, i );
        Compact[2*nCompact] = a;
        Compact[2*nCompact+1] = b;
        CompactMap[i] = Cec_TranRecipeGateCode( nCompact++, 0 );
    }
    iOut = Cec_TranRecipeMapCode( iOut, CompactMap, nWork );
    Cec_TranCandRecipeRelease( pCand );
    pCand->nGates = nCompact;
    pCand->iOut = iOut;
    if ( nCompact )
    {
        pCand->Recipe = Cec_TranRecipeAlloc( 2 * nCompact );
        memcpy( pCand->Recipe, Compact, sizeof(int) * 2 * nCompact );
    }
    pCand->nKind = nCompact ? CEC_TRAN_CAND_CONSTR :
        (Abc_Lit2Var(iOut) == 0 ? CEC_TRAN_CAND_CONST :
            CEC_TRAN_CAND_EXIST);
}

static inline int Cec_TranRecipeCopyCode( Gia_Man_t * p, int Code,
    int const * pGates, int nBuilt )
{
    int iLit, iGate;
    if ( !Cec_TranRecipeCodeIsGate(Code) )
        return Cec_TranCopyLit( p, Code );
    iLit = Cec_TranRecipeGateLit( Code );
    iGate = Abc_Lit2Var( iLit );
    assert( iGate < nBuilt );
    return Abc_LitNotCond( pGates[iGate], Abc_LitIsCompl(iLit) );
}

static int Cec_TranRecipeBuildMapped( Gia_Man_t * p, Gia_Man_t * pNew,
    Cec_TranCand_t const * pCand, int * pGates )
{
    int i, iLit0, iLit1;
    assert( pCand->nGates <= CEC_TRAN_RECIPE_NODES_MAX );
    for ( i = 0; i < pCand->nGates; i++ )
    {
        iLit0 = Cec_TranRecipeCopyCode( p, pCand->Recipe[2*i], pGates, i );
        iLit1 = Cec_TranRecipeCopyCode( p, pCand->Recipe[2*i+1], pGates, i );
        pGates[i] = Gia_ManHashAnd( pNew, iLit0, iLit1 );
    }
    return Cec_TranRecipeCopyCode( p, pCand->iOut, pGates, pCand->nGates );
}

static int Cec_TranRecipeBuild( Gia_Man_t * p, Gia_Man_t * pNew,
    Cec_TranCand_t const * pCand )
{
    int Gates[CEC_TRAN_RECIPE_NODES_MAX];
    return Cec_TranRecipeBuildMapped( p, pNew, pCand, Gates );
}

// Frozen structural hashing used by commit-wave gain evaluation.  DATE's
// DryReplace accounts for replacement nodes which are already present in the
// DAG.  Candidate nGates is only an upper bound on that cost.  Build one
// strashed copy per wave, then simulate each small recipe against this copy
// without appending anything to either network.
typedef struct Cec_TranFrozenHash_t_ Cec_TranFrozenHash_t;
struct Cec_TranFrozenHash_t_
{
    Gia_Man_t * pHash;
    Vec_Int_t * vOldToHash;
    Vec_Int_t * vHashToOld;      // earliest old object represented by a hash node
    int         nFrozenObjs;
};

static void Cec_TranFrozenHashStart( Gia_Man_t * p,
    Cec_TranFrozenHash_t * pHash )
{
    Gia_Obj_t * pObj;
    int i, iLit, iLit0, iLit1, iVar;
    memset( pHash, 0, sizeof(Cec_TranFrozenHash_t) );
    pHash->pHash = Gia_ManStart( Gia_ManObjNum(p) );
    Gia_ManHashAlloc( pHash->pHash );
    pHash->vOldToHash = Vec_IntStartFull( Gia_ManObjNum(p) );
    pHash->vHashToOld = Vec_IntAlloc( Gia_ManObjNum(p) );
    Vec_IntWriteEntry( pHash->vOldToHash, 0, 0 );
    Vec_IntFillExtra( pHash->vHashToOld, 1, 0 );
    Gia_ManForEachCi( p, pObj, i )
    {
        int iOld = Gia_ObjId( p, pObj );
        iLit = Gia_ManAppendCi( pHash->pHash );
        Vec_IntWriteEntry( pHash->vOldToHash, iOld, iLit );
        Vec_IntFillExtra( pHash->vHashToOld,
            Gia_ManObjNum(pHash->pHash), -1 );
        Vec_IntWriteEntry( pHash->vHashToOld,
            Abc_Lit2Var(iLit), iOld );
    }
    Gia_ManForEachAnd( p, pObj, i )
    {
        iLit0 = Vec_IntEntry( pHash->vOldToHash,
            Gia_ObjFaninId0p(p, pObj) );
        iLit1 = Vec_IntEntry( pHash->vOldToHash,
            Gia_ObjFaninId1p(p, pObj) );
        iLit0 = Abc_LitNotCond( iLit0, Gia_ObjFaninC0(pObj) );
        iLit1 = Abc_LitNotCond( iLit1, Gia_ObjFaninC1(pObj) );
        iLit = Cec_TranHashGate( pHash->pHash, pObj, iLit0, iLit1 );
        Vec_IntWriteEntry( pHash->vOldToHash, i, iLit );
        Vec_IntFillExtra( pHash->vHashToOld,
            Gia_ManObjNum(pHash->pHash), -1 );
        iVar = Abc_Lit2Var( iLit );
        if ( Vec_IntEntry(pHash->vHashToOld, iVar) < 0 )
            Vec_IntWriteEntry( pHash->vHashToOld, iVar, i );
    }
    pHash->nFrozenObjs = Gia_ManObjNum( pHash->pHash );
}

static void Cec_TranFrozenHashStop( Cec_TranFrozenHash_t * pHash )
{
    if ( pHash->pHash )
    {
        Gia_ManHashStop( pHash->pHash );
        Gia_ManStop( pHash->pHash );
    }
    Vec_IntFreeP( &pHash->vOldToHash );
    Vec_IntFreeP( &pHash->vHashToOld );
    memset( pHash, 0, sizeof(Cec_TranFrozenHash_t) );
}

static inline int Cec_TranFrozenRecipeCode(
    Cec_TranFrozenHash_t const * pHash, int Code,
    int const * pGates, int nBuilt )
{
    int iLit, iGate;
    if ( !Cec_TranRecipeCodeIsGate(Code) )
    {
        iLit = Vec_IntEntry( pHash->vOldToHash, Abc_Lit2Var(Code) );
        return Abc_LitNotCond( iLit, Abc_LitIsCompl(Code) );
    }
    iLit = Cec_TranRecipeGateLit( Code );
    iGate = Abc_Lit2Var( iLit );
    assert( iGate < nBuilt );
    return Abc_LitNotCond( pGates[iGate], Abc_LitIsCompl(iLit) );
}

static int Cec_TranFrozenHashAnd( Cec_TranFrozenHash_t const * pHash,
    int iTarget, char const * pCovered, int iLit0, int iLit1,
    int * pNew0, int * pNew1, int * pnNew )
{
    int i, iLit, iOld;
    if ( iLit0 < 2 )
        return iLit0 ? iLit1 : 0;
    if ( iLit1 < 2 )
        return iLit1 ? iLit0 : 0;
    if ( iLit0 == iLit1 )
        return iLit1;
    if ( iLit0 == Abc_LitNot(iLit1) )
        return 0;
    if ( iLit0 > iLit1 )
        ABC_SWAP( int, iLit0, iLit1 );
    if ( Abc_Lit2Var(iLit0) < pHash->nFrozenObjs &&
         Abc_Lit2Var(iLit1) < pHash->nFrozenObjs )
    {
        iLit = Gia_ManHashAndTry( pHash->pHash, iLit0, iLit1 );
        if ( iLit >= 0 )
        {
            iOld = Vec_IntEntry( pHash->vHashToOld, Abc_Lit2Var(iLit) );
            // The topological bundle has only copied nodes preceding the
            // target.  A hit at the target or in its TFO is not reusable.
            if ( iOld >= 0 && iOld < iTarget &&
                 (!pCovered || !pCovered[iOld]) )
                return iLit;
        }
    }
    for ( i = 0; i < *pnNew; i++ )
        if ( pNew0[i] == iLit0 && pNew1[i] == iLit1 )
            return Abc_Var2Lit( pHash->nFrozenObjs + i, 0 );
    assert( *pnNew < CEC_TRAN_RECIPE_NODES_MAX );
    pNew0[*pnNew] = iLit0;
    pNew1[*pnNew] = iLit1;
    return Abc_Var2Lit( pHash->nFrozenObjs + (*pnNew)++, 0 );
}

static int Cec_TranFrozenRecipeReach_rec(
    Cec_TranFrozenHash_t const * pHash, Gia_Man_t * p, int iLit,
    int const * pNew0, int const * pNew1, char * pSeen,
    Vec_Int_t * vBoundary )
{
    int iVar = Abc_Lit2Var( iLit );
    int iNew, iOld, Count;
    if ( iVar < pHash->nFrozenObjs )
    {
        iOld = Vec_IntEntry( pHash->vHashToOld, iVar );
        if ( iOld > 0 && Gia_ObjIsAnd(Gia_ManObj(p, iOld)) &&
             Vec_IntFind(vBoundary, iOld) < 0 )
            Vec_IntPush( vBoundary, iOld );
        return 0;
    }
    iNew = iVar - pHash->nFrozenObjs;
    if ( pSeen[iNew] )
        return 0;
    pSeen[iNew] = 1;
    Count = 1;
    Count += Cec_TranFrozenRecipeReach_rec( pHash, p, pNew0[iNew],
        pNew0, pNew1, pSeen, vBoundary );
    Count += Cec_TranFrozenRecipeReach_rec( pHash, p, pNew1[iNew],
        pNew0, pNew1, pSeen, vBoundary );
    return Count;
}

static int Cec_TranFrozenRecipeCost( Gia_Man_t * p,
    Cec_TranFrozenHash_t const * pHash, Cec_TranCand_t const * pCand,
    char const * pCovered, Vec_Int_t * vBoundary )
{
    int Gates[CEC_TRAN_RECIPE_NODES_MAX];
    int New0[CEC_TRAN_RECIPE_NODES_MAX];
    int New1[CEC_TRAN_RECIPE_NODES_MAX];
    char Seen[CEC_TRAN_RECIPE_NODES_MAX] = {0};
    int i, iLit0, iLit1, iOut, nNew = 0;
    for ( i = 0; i < pCand->nGates; i++ )
    {
        iLit0 = Cec_TranFrozenRecipeCode( pHash, pCand->Recipe[2*i],
            Gates, i );
        iLit1 = Cec_TranFrozenRecipeCode( pHash, pCand->Recipe[2*i+1],
            Gates, i );
        Gates[i] = Cec_TranFrozenHashAnd( pHash, pCand->iTarget,
            pCovered, iLit0, iLit1, New0, New1, &nNew );
    }
    iOut = Cec_TranFrozenRecipeCode( pHash, pCand->iOut,
        Gates, pCand->nGates );
    return Cec_TranFrozenRecipeReach_rec( pHash, p, iOut,
        New0, New1, Seen, vBoundary );
}

// Flatten only positive-polarity ANDs created by this recipe.  External
// divisors remain atomic even when they happen to be AND nodes in the source
// graph; recursively opening those cones would make a supposedly cheap CBS
// query proportional to the original TFI.  A complemented recipe gate is
// also atomic because De Morgan expansion would turn one cube family into an
// exponential cover.  Repeated positive recipe gates are idempotent in an
// AND cone and are traversed once.
static int Cec_TranRecipeCollectAndLeaves_rec( Cec_TranCand_t const * pCand,
    int Code, char * pSeen, int * pLeaves, int nLeaves )
{
    int iLit, iGate;
    if ( !Cec_TranRecipeCodeIsGate(Code) )
    {
        pLeaves[nLeaves++] = Code;
        return nLeaves;
    }
    iLit = Cec_TranRecipeGateLit( Code );
    iGate = Abc_Lit2Var( iLit );
    assert( iGate < pCand->nGates );
    if ( Abc_LitIsCompl(iLit) )
    {
        pLeaves[nLeaves++] = Code;
        return nLeaves;
    }
    if ( pSeen[iGate] )
        return nLeaves;
    pSeen[iGate] = 1;
    nLeaves = Cec_TranRecipeCollectAndLeaves_rec( pCand,
        pCand->Recipe[2*iGate], pSeen, pLeaves, nLeaves );
    return Cec_TranRecipeCollectAndLeaves_rec( pCand,
        pCand->Recipe[2*iGate+1], pSeen, pLeaves, nLeaves );
}

static int Cec_TranRecipeCollectAndLeaves( Cec_TranCand_t const * pCand,
    int * pLeaves )
{
    char Seen[CEC_TRAN_RECIPE_NODES_MAX] = {0};
    int iOutLit, iOutGate;
    if ( !Cec_TranRecipeCodeIsGate(pCand->iOut) )
        return 0;
    iOutLit = Cec_TranRecipeGateLit( pCand->iOut );
    iOutGate = Abc_Lit2Var( iOutLit );
    assert( iOutGate < pCand->nGates );
    return Cec_TranRecipeCollectAndLeaves_rec( pCand,
        Cec_TranRecipeGateCode(iOutGate, 0), Seen, pLeaves, 0 );
}

static inline word Cec_TranRecipeSimCode( Cec_TranSim_t * pSim, int Code,
    word const * pGates, int nBuilt, int iSlot )
{
    int iLit, iGate;
    if ( !Cec_TranRecipeCodeIsGate(Code) )
        return Cec_TranSimLit( pSim, Code, iSlot );
    iLit = Cec_TranRecipeGateLit( Code );
    iGate = Abc_Lit2Var( iLit );
    assert( iGate < nBuilt );
    return pGates[iGate] ^ (Abc_LitIsCompl(iLit) ? ~(word)0 : 0);
}

static int Cec_TranRecipeMatchesRoot( Cec_TranSim_t * pSim,
    Cec_TranCand_t const * pCand, word * pCare )
{
    word Gates[CEC_TRAN_RECIPE_NODES_MAX];
    word Value, v0, v1;
    int i, s;
    for ( s = 0; s < pSim->nSlots; s++ )
    {
        for ( i = 0; i < pCand->nGates; i++ )
        {
            v0 = Cec_TranRecipeSimCode( pSim, pCand->Recipe[2*i], Gates, i, s );
            v1 = Cec_TranRecipeSimCode( pSim, pCand->Recipe[2*i+1], Gates, i, s );
            Gates[i] = v0 & v1;
        }
        Value = Cec_TranRecipeSimCode( pSim, pCand->iOut,
            Gates, pCand->nGates, s );
        if ( (Value ^ Cec_TranSimLit(pSim,
                Abc_Var2Lit(pCand->iTarget, 0), s)) &
             (pCare ? pCare[s] : ~(word)0) )
            return 0;
    }
    return 1;
}

static int Cec_TranRecipeStructurallyValid( Cec_TranSim_t * pSim,
    Cec_TranCand_t const * pCand )
{
    int i, k, Code;
    if ( pCand->nGates < 0 ||
         pCand->nGates > CEC_TRAN_RECIPE_NODES_MAX )
        return 0;
    for ( i = -1; i < 2 * pCand->nGates; i++ )
    {
        Code = i < 0 ? pCand->iOut : pCand->Recipe[i];
        if ( Cec_TranRecipeCodeIsGate(Code) )
        {
            k = Abc_Lit2Var( Cec_TranRecipeGateLit(Code) );
            if ( k >= (i < 0 ? pCand->nGates : i / 2) )
                return 0;
        }
        else if ( Code < 0 || Abc_Lit2Var(Code) >= Gia_ManObjNum(pSim->pGia) )
            return 0;
    }
    return 1;
}

// Direct resubstitution replaces the root itself, rather than one of the
// root's supergate leaves.  Formal proof remains the sole commit criterion.
static int Cec_TranSigMatchesRoot( Cec_TranSim_t * pSim, int iTarget,
    int iDiv, word * pCare )
{
    int s;
    word h;
    for ( s = 0; s < pSim->nSlots; s++ )
    {
        h = Cec_TranSimLit( pSim, iDiv, s );
        if ( (h ^ Cec_TranSimLit(pSim, Abc_Var2Lit(iTarget, 0), s)) &
             (pCare ? pCare[s] : ~(word)0) )
            return 0;
    }
    return 1;
}

typedef struct Cec_TranRoot_t_ Cec_TranRoot_t;
struct Cec_TranRoot_t_
{
    int iObj;
    int nMffc;
};

typedef struct Cec_TranDivRank_t_ Cec_TranDivRank_t;
typedef struct Cec_TranRootCursor_t_ Cec_TranRootCursor_t;
typedef struct Cec_TranSourceMacro_t_ Cec_TranSourceMacro_t;
static void Cec_TranSourceMacroStop( Cec_TranSourceMacro_t * s );
struct Cec_TranRootCursor_t_
{
    int State[6];               // Stage/n/i/k/Stage-5 slot + classified frontier
    Cec_TranSourceMacro_t * pSourceMacro;
    int nSourceMacroOwner;      // one immutable root-pass lifetime, not an ID hash
    void * pBuildCache;         // root-local exact residual memo across pages
    Cec_TranTeachCache_t * pTeachCache; // frozen columns/signature across waves
    Vec_Int_t * vBuildPool;     // immutable ordered divisor IDs across pages
    Cec_TranDivRank_t * pBuildRanks; // rank metadata aligned with vBuildPool
    Cec_TranSim_t * pRankSource; // immutable score owner, same snapshot only
    word * pRankSims;
    int nRankSlots, iRankRoot;
    int nDiagRaw, nDiagNext, nDiagPositive, nDiagCollapsed, nDiagInvalid;
    long long nDiagPivots;
    abctime timeDiagEnum;
    int nBuildYield;
    int nBuildAccepted;         // unique positive-gain Build candidates emitted on this snapshot
    int nPages;
    int fExhausted;
    int fExpConflict;
    abctime timeExpBuild, timeExpRank;
};

static void Cec_TranRootCursorCacheStop( Cec_TranRootCursor_t * pCursor )
{
    if ( pCursor->pBuildCache == NULL )
        return;
    Abc_ResubRootCacheStop( pCursor->pBuildCache );
    pCursor->pBuildCache = NULL;
}

// A canonical Build has at least one gate, while acceptance requires
// MFFC-gates > 0.  A zero-gate canonical result belongs to Constant/Existing,
// so MFFC=1 can never yield a positive-gain Build candidate.
static int Cec_TranRootBuildEligible( Cec_TranRoot_t const * pRoot )
{
    return pRoot->nMffc > 1;
}

// With proof micro-batching disabled, q retains its historical meaning: one
// discovery wave pulls q Build candidates (or drains the iterator for q=0)
// and a positive proof is immediately eligible for selection.  With -j, q is
// instead the per-snapshot commit horizon and -j is the per-proof-call slice.
// Returning zero means either "legacy unlimited" (q=0, -j=0) or "horizon
// reached" (-j>0); callers distinguish these cases through nRootProofBatch.
static int Cec_TranRootBuildBudget( Cec_ParTran_t const * pPars,
    Cec_TranRootCursor_t const * pCursor )
{
    int nRemain;
    if ( pCursor->fExhausted )
        return 0;
    if ( pPars->nRootProofBatch <= 0 )
        return pPars->nRootConstrTop;
    if ( pPars->nRootConstrTop == 0 )
        return pPars->nRootProofBatch;
    nRemain = pPars->nRootConstrTop - pCursor->nBuildAccepted;
    return nRemain <= 0 ? 0 :
        Abc_MinInt( pPars->nRootProofBatch, nRemain );
}

static int Cec_TranRootBuildHorizonReached( Cec_ParTran_t const * pPars,
    Cec_TranRootCursor_t const * pCursor )
{
    assert( pPars->nRootProofBatch > 0 );
    return pCursor->fExhausted ||
        (pPars->nRootConstrTop > 0 &&
         pCursor->nBuildAccepted >= pPars->nRootConstrTop);
}

// Direct is discovered only on page zero.  Later immutable proof pages have
// nothing left to discover for a root with no positive-gain Build universe.
// Keep this separate from iterator exhaustion: no iterator was run here.
static int Cec_TranRootDiscoveryFinished( Cec_ParTran_t const * pPars,
    Cec_TranRoot_t const * pRoot, Cec_TranRootCursor_t const * pCursor,
    int iPage )
{
    if ( pPars->nRootProofBatch <= 0 )
        return 0;
    if ( iPage > 0 &&
         (!pPars->fUseConstr || !Cec_TranRootBuildEligible(pRoot)) )
        return 1;
    return pPars->fUseConstr &&
        Cec_TranRootBuildHorizonReached(pPars, pCursor);
}

typedef struct Cec_TranCandVec_t_ Cec_TranCandVec_t;
struct Cec_TranCandVec_t_
{
    Cec_TranCand_t * pArray;
    int * pHash;                // open-addressed candidate index (entry + 1)
    int nSize;
    int nCap;
    int nHash;
    int iHead;
};

static unsigned Cec_TranCandHash( Cec_TranCand_t const * pCand )
{
    unsigned Hash = 2166136261u;
    int i;
#define CEC_TRAN_CAND_HASH_ADD(Value) \
    Hash = (Hash ^ (unsigned)(Value)) * 16777619u
    CEC_TRAN_CAND_HASH_ADD( pCand->iTarget );
    CEC_TRAN_CAND_HASH_ADD( pCand->fStrict );
    CEC_TRAN_CAND_HASH_ADD( pCand->nGates );
    CEC_TRAN_CAND_HASH_ADD( pCand->iOut );
    for ( i = 0; i < 2 * pCand->nGates; i++ )
        CEC_TRAN_CAND_HASH_ADD( pCand->Recipe[i] );
#undef CEC_TRAN_CAND_HASH_ADD
    return Hash;
}

static void Cec_TranCandVecHashResize( Cec_TranCandVec_t * p, int nHashNew )
{
    int * pHashNew = ABC_CALLOC( int, nHashNew );
    int i, k;
    assert( nHashNew > 0 && !(nHashNew & (nHashNew - 1)) );
    for ( i = 0; i < p->nSize; i++ )
    {
        k = (int)(Cec_TranCandHash(p->pArray + i) & (unsigned)(nHashNew - 1));
        while ( pHashNew[k] )
            k = (k + 1) & (nHashNew - 1);
        pHashNew[k] = i + 1;
    }
    ABC_FREE( p->pHash );
    p->pHash = pHashNew;
    p->nHash = nHashNew;
}

static void Cec_TranCandVecPush( Cec_TranCandVec_t * p, Cec_TranCand_t Cand )
{
    int k;
    if ( p->nSize == p->nCap )
    {
        p->nCap = p->nCap ? 2 * p->nCap : 64;
        p->pArray = ABC_REALLOC( Cec_TranCand_t, p->pArray, p->nCap );
    }
    if ( p->nHash == 0 || 2 * (p->nSize + 1) >= p->nHash )
        Cec_TranCandVecHashResize( p, p->nHash ? 2 * p->nHash : 128 );
    Cec_TranCandRecipeRetain( &Cand );
    p->pArray[p->nSize] = Cand;
    k = (int)(Cec_TranCandHash(&Cand) & (unsigned)(p->nHash - 1));
    while ( p->pHash[k] )
        k = (k + 1) & (p->nHash - 1);
    p->pHash[k] = ++p->nSize;
}

static void Cec_TranCandVecClear( Cec_TranCandVec_t * p )
{
    int i;
    for ( i = 0; i < p->nSize; i++ )
        Cec_TranCandRecipeRelease( p->pArray + i );
    p->nSize = p->iHead = 0;
    if ( p->pHash )
        memset( p->pHash, 0, sizeof(int) * p->nHash );
}

static void Cec_TranCandVecStop( Cec_TranCandVec_t * p )
{
    Cec_TranCandVecClear( p );
    ABC_FREE( p->pArray );
    ABC_FREE( p->pHash );
    memset( p, 0, sizeof(Cec_TranCandVec_t) );
}

static int Cec_TranCandEqual( Cec_TranCand_t const * p0, Cec_TranCand_t const * p1 )
{
    return p0->iTarget == p1->iTarget && p0->fStrict == p1->fStrict &&
        p0->nGates == p1->nGates && p0->iOut == p1->iOut &&
        (p0->nGates == 0 || !memcmp( p0->Recipe, p1->Recipe,
            sizeof(int) * 2 * p0->nGates ));
}

static int Cec_TranCandVecContains( Cec_TranCandVec_t const * p, Cec_TranCand_t const * pCand )
{
    int k;
    if ( p->nHash == 0 )
        return 0;
    k = (int)(Cec_TranCandHash(pCand) & (unsigned)(p->nHash - 1));
    while ( p->pHash[k] )
    {
        if ( Cec_TranCandEqual(p->pArray + p->pHash[k] - 1, pCand) )
            return 1;
        k = (k + 1) & (p->nHash - 1);
    }
    return 0;
}

static int Cec_TranCandVecFind( Cec_TranCandVec_t const * p,
    Cec_TranCand_t const * pCand )
{
    int k;
    if ( p->nHash == 0 )
        return -1;
    k = (int)(Cec_TranCandHash(pCand) & (unsigned)(p->nHash - 1));
    while ( p->pHash[k] )
    {
        int i = p->pHash[k] - 1;
        if ( Cec_TranCandEqual(p->pArray + i, pCand) )
            return i;
        k = (k + 1) & (p->nHash - 1);
    }
    return -1;
}

static int Cec_TranProofHistoryCodeMap( int Code, Vec_Int_t * vMap,
    int * pfValid )
{
    int iMapped;
    if ( Cec_TranRecipeCodeIsGate(Code) )
        return Code;
    if ( Code < 0 || Abc_Lit2Var(Code) >= Vec_IntSize(vMap) )
    {
        *pfValid = 0;
        return 0;
    }
    iMapped = Vec_IntEntry( vMap, Abc_Lit2Var(Code) );
    if ( iMapped < 0 )
    {
        *pfValid = 0;
        return 0;
    }
    return Abc_LitNotCond( iMapped, Abc_LitIsCompl(Code) );
}

static int Cec_TranProofHistoryTopoValid( Gia_Man_t * p,
    Cec_TranCand_t const * pCand )
{
    int i, Code, iObj;
    if ( pCand->iTarget <= 0 || pCand->iTarget >= Gia_ManObjNum(p) ||
         !Gia_ObjIsAnd(Gia_ManObj(p, pCand->iTarget)) )
        return 0;
    for ( i = -1; i < 2 * pCand->nGates; i++ )
    {
        Code = i < 0 ? pCand->iOut : pCand->Recipe[i];
        if ( Cec_TranRecipeCodeIsGate(Code) )
        {
            iObj = Abc_Lit2Var( Cec_TranRecipeGateLit(Code) );
            if ( iObj >= (i < 0 ? pCand->nGates : i / 2) )
                return 0;
            continue;
        }
        iObj = Abc_Lit2Var( Code );
        if ( Code < 0 || iObj >= Gia_ManObjNum(p) ||
             (iObj != 0 && iObj >= pCand->iTarget) )
            return 0;
    }
    return 1;
}

// Carry only formally proved relations across a commit.  UNKNOWN/split
// obligations are deliberately not cached; they can only reappear through
// natural discovery on a genuinely rebuilt graph.  A carried relation is
// downgraded to a sequential certificate because a sequentially proved commit
// need not preserve arbitrary-state internal identities.  Proof origin
// metadata is preserved so phase/kind/lane statistics do not move when a
// recipe canonicalizes or its reusable certificate strength is downgraded.
static void Cec_TranRemapProofHistory( Gia_Man_t * pNew,
    Vec_Int_t * vOldToNew, Cec_TranCandVec_t const * pCarry,
    Cec_TranCandVec_t * pHistory, Cec_TranProf_t * pProf )
{
    Cec_TranCand_t Cand;
    int i, k, Code, iTargetLit, fValid;
    Cec_TranCandVecClear( pHistory );
    for ( i = 0; i < pCarry->nSize; i++ )
    {
        Cec_TranCand_t const * pOld = pCarry->pArray + i;
        if ( pOld->iTarget < 0 || pOld->iTarget >= Vec_IntSize(vOldToNew) )
        {
            pProf->nHistoryTriedInvalidated++;
            continue;
        }
        iTargetLit = Vec_IntEntry( vOldToNew, pOld->iTarget );
        if ( iTargetLit < 0 )
        {
            pProf->nHistoryTriedInvalidated++;
            continue;
        }
        Cand = *pOld;
        Cand.Recipe = NULL;
        Cand.iTarget = Abc_Lit2Var( iTargetLit );
        Cand.nMffc = 0;
        Cand.Gain = -1;
        Cand.nProofStage = 2;
        Cand.nStatus = CEC_TRAN_STATE_PROVED_SEQ;
        fValid = 1;
        if ( Cand.nGates )
            Cand.Recipe = Cec_TranRecipeAlloc( 2 * Cand.nGates );
        for ( k = 0; k < 2 * Cand.nGates; k++ )
            Cand.Recipe[k] = Cec_TranProofHistoryCodeMap(
                pOld->Recipe[k], vOldToNew, &fValid );
        Cand.iOut = Cec_TranProofHistoryCodeMap(
            pOld->iOut, vOldToNew, &fValid );
        if ( fValid && Abc_LitIsCompl(iTargetLit) )
            Cand.iOut = Cec_TranRecipeNotCode( Cand.iOut );
        if ( fValid )
            Cec_TranCandCanonicalizeRecipe( &Cand );
        if ( !fValid || !Cec_TranProofHistoryTopoValid(pNew, &Cand) )
        {
            Cec_TranCandRecipeRelease( &Cand );
            pProf->nHistoryTriedInvalidated++;
            continue;
        }
        Cand.iDiv0 = Cand.iDiv1 = -1;
        for ( k = -1; k < 2 * Cand.nGates; k++ )
        {
            Code = k < 0 ? Cand.iOut : Cand.Recipe[k];
            if ( Cec_TranRecipeCodeIsGate(Code) || Abc_Lit2Var(Code) == 0 )
                continue;
            if ( Cand.iDiv0 == -1 )
                Cand.iDiv0 = Code;
            else if ( Abc_Lit2Var(Cand.iDiv0) != Abc_Lit2Var(Code) )
            {
                Cand.iDiv1 = Code;
                break;
            }
        }
        if ( !Cec_TranCandVecContains(pHistory, &Cand) )
        {
            Cec_TranCandVecPush( pHistory, Cand );
            pProf->nHistoryTriedRemapped++;
        }
        Cec_TranCandRecipeRelease( &Cand );
    }
}

static Cec_TranCand_t Cec_TranCandCreateLiteral( int iTarget, int iDiv,
    int nMffc, int nKind, int fStrict )
{
    Cec_TranCand_t Cand;
    memset( &Cand, 0, sizeof(Cand) );
    Cand.iTarget = iTarget;
    Cand.iDiv0 = iDiv;
    Cand.iDiv1 = -1;
    Cand.nMffc = nMffc;
    Cand.Gain = -1;
    Cand.nKind = nKind;
    Cand.fStrict = fStrict;
    Cand.nGates = 0;
    Cand.iOut = iDiv;
    return Cand;
}
