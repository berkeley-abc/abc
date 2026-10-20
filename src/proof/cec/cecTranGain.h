// Exact gain, MFFC, and support profiling.
// Private implementation fragment included only by cecTrans.c.

// Among candidates that already passed signature/care matching and structural
// legality, root-only order is deterministic: constants first, then existing
// literals, then constructed recipes by increasing gate count.  Kind priority
// never admits an unmatched relation.  Gain/coverage and the canonical recipe
// key break ties without changing that kind order.
static int Cec_TranCandHeuristicCompare( const void * p0, const void * p1 )
{
    Cec_TranCand_t const * pC0 = (Cec_TranCand_t const *)p0;
    Cec_TranCand_t const * pC1 = (Cec_TranCand_t const *)p1;
    if ( pC0->nKind != pC1->nKind )
        return pC0->nKind - pC1->nKind;
    if ( pC0->nGates != pC1->nGates )
        return pC0->nGates - pC1->nGates;
    if ( pC0->fExactTemplate != pC1->fExactTemplate )
        return pC1->fExactTemplate - pC0->fExactTemplate;
    // The resub engine yields exact covers in decreasing sampled coverage /
    // residual-reduction order.  CI overlap is the next safe tie-break; it is
    // never used as a semantic filter.
    if ( pC0->nResubRank != pC1->nResubRank )
        return pC0->nResubRank - pC1->nResubRank;
    if ( pC0->nCiOverlap != pC1->nCiOverlap )
        return pC1->nCiOverlap - pC0->nCiOverlap;
    if ( pC0->fDivRescue != pC1->fDivRescue )
        return pC0->fDivRescue - pC1->fDivRescue;
    if ( pC0->Gain != pC1->Gain )
        return pC1->Gain - pC0->Gain;
    if ( pC0->iOut != pC1->iOut )
        return pC0->iOut - pC1->iOut;
    return pC0->nGates ? memcmp( pC0->Recipe, pC1->Recipe,
        sizeof(int) * 2 * pC0->nGates ) : 0;
}

// Group candidates by MFFC-ranked target and sort each root's alternatives by
// local gain.  Every layer is proved even after another alternative succeeds;
// the exact-cost portfolio at commit time then compares this order's winner
// with the q=1-primary winner and prevents a globally worse replacement.
// qStrictAll is grouped by target and gain-sorted within each group.  Store
// each [begin,end) range and the maximum direct/normal/rescue widths.  Layer
// lookup scans the small per-root range, exposing the cheap direct lane first,
// then legacy constructed candidates, then diverse-rescue candidates.  The
// metadata remains O(number of roots).
static int Cec_TranCandVecEvalSortTail( Gia_Man_t * p,
    Cec_TranCandVec_t * pVec, int iStart, Cec_TranProf_t * pProf )
{
    int i, nEvals = 0;
    for ( i = iStart; i < pVec->nSize; i++ )
        if ( pVec->pArray[i].Gain < 0 )
        {
            pVec->pArray[i].Gain = Cec_TranRootCandidateGainEval(
                p, pVec->pArray + i, pProf );
            nEvals++;
        }
    if ( pVec->nSize - iStart > 1 )
        qsort( pVec->pArray + iStart, pVec->nSize - iStart,
            sizeof(Cec_TranCand_t), Cec_TranCandGainCompare );
    return nEvals;
}

// Apply one proved replacement per target in one topological duplication.
// Replacements only use earlier literals, so if an earlier selected target is
// itself rewritten, every later recipe automatically sees its equivalent new
// representative.  This is the root-scope analogue of reducing all proved
// signal-correspondence classes at once.
static Gia_Man_t * Cec_TranDupRootBundle( Gia_Man_t * p,
    Cec_TranCand_t const * pCands, Vec_Int_t * vSelected )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int * pSelect = ABC_FALLOC( int, Gia_ManObjNum(p) );
    int i, k, iCand, iLit0, iLit1, iRep;
    Vec_IntForEachEntry( vSelected, iCand, k )
        pSelect[pCands[iCand].iTarget] = iCand;
    Gia_ManFillValue( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) + 4 * Vec_IntSize(vSelected) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    pNew->nConstrs = p->nConstrs;
    Gia_ManHashAlloc( pNew );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachAnd( p, pObj, i )
    {
        iLit0 = Gia_ObjFanin0Copy( pObj );
        iLit1 = Gia_ObjFanin1Copy( pObj );
        iCand = pSelect[i];
        if ( iCand < 0 )
        {
            pObj->Value = Cec_TranHashGate( pNew, pObj, iLit0, iLit1 );
            continue;
        }
        iRep = Cec_TranRecipeBuild( p, pNew, pCands + iCand );
        pObj->Value = iRep;
    }
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    pNew->nConstrs = p->nConstrs;
    Cec_TranAssertTypedInterface( p, pNew );
    ABC_FREE( pSelect );
    return pNew;
}

// Exact all-Build attribution on the selected set, without reselecting it.
// Apply only the selected Direct edits, then compare their cleaned graph with
// the actual committed graph. The signed Build marginal includes interactions
// with those Direct edits and includes every original Build proof lane, even
// if remapping changed the recipe's current kind or certificate strength.
static void Cec_TranBuildReductionProfile( Gia_Man_t * p,
    Cec_TranCandVec_t const * pSelected, Gia_Man_t * pFinal,
    char const * Scope )
{
    Vec_Int_t * vDirect = Vec_IntAlloc( pSelected->nSize );
    Gia_Man_t * pDup, * pClean;
    int i, nWithoutBuild, nBuild = 0;
    for ( i = 0; i < pSelected->nSize; i++ )
        if ( pSelected->pArray[i].nProofKind == CEC_TRAN_CAND_CONSTR )
            nBuild++;
        else
            Vec_IntPush( vDirect, i );
    if ( nBuild )
    {
        pDup = Cec_TranDupRootBundle( p, pSelected->pArray, vDirect );
        pClean = Cec_TranCleanupKeepRegs( pDup, NULL );
        nWithoutBuild = Gia_ManAndNum( pClean );
        Gia_ManStop( pClean );
        Gia_ManStop( pDup );
    }
    else
        nWithoutBuild = Gia_ManAndNum( pFinal );
    Abc_Print( 1, "sresub build reduction: scope=%s selected=%d and-before=%d and-without-build=%d and-after=%d ordered-and-gain=%d\n",
        Scope, nBuild, Gia_ManAndNum(p), nWithoutBuild,
        Gia_ManAndNum(pFinal), nWithoutBuild - Gia_ManAndNum(pFinal) );
    Vec_IntFree( vDirect );
}

// The exact q=1 frontier is a conservative portfolio member.  It includes
// ordinary non-resub candidates and candidates explicitly generated by the
// legacy/direct/boundary q=1 path, but never admits a root which exists only
// because q>1 explored additional choices.  Comparing its cleanup cost with
// the full gain portfolio gives large q a strict q=1 bundle fallback.
// Exact dry-run size for one proof-stage subset, using the same winner
// selection and cleanup as the unified commit.  In particular, evaluate both
// the local-gain portfolio and the q=1-primary fallback, because the real
// commit may choose either one after exact cleanup.
// Counterfactual size profiles use the same per-target winner selection and
// cleanup as the real commit.  With only three candidate kinds, the six
// proper nonempty subsets are enough to recover exact Shapley contributions;
// the empty size is the input and the full size is the actual committed
// result.  Additional subsets expose the marginal utility of raw resub ranks
// above one, CEGAR waves after wave one, and the two sources currently folded
// into the existing kind (global lookup versus zero-gate resub recipes).
// Split the exact cleanup gain by both proof stage and candidate kind.  The
// combinational characteristic function starts from the input network.  The
// sequential characteristic function starts from the full combinational
// bundle, so its Shapley values add up to the incremental temporal reduction
// instead of double-counting reductions already certified combinationally.
// Select the best proved recipe for each target, then commit all selected
// targets together.  Different proved alternatives of one target form one
// equivalence class, so only the highest exact-gain representative is needed.
static int Cec_TranRootCompare( const void * p0, const void * p1 )
{
    Cec_TranRoot_t const * pR0 = (Cec_TranRoot_t const *)p0;
    Cec_TranRoot_t const * pR1 = (Cec_TranRoot_t const *)p1;
    if ( pR0->nMffc != pR1->nMffc )
        return pR1->nMffc - pR0->nMffc;
    return pR1->iObj - pR0->iObj;
}

static void Cec_TranMffcScratchClear( char * pMark, Vec_Int_t * vMarked )
{
    int i, iObj;
    Vec_IntForEachEntry( vMarked, iObj, i )
        pMark[iObj] = 0;
    Vec_IntClear( vMarked );
}

static inline int Cec_TranMffcIsBoundary( int iObj, int iRoot,
    char const * pCovered, char const * pUsed,
    Vec_Int_t const * vBoundary )
{
    return iObj != iRoot &&
        ((pCovered && pCovered[iObj]) || (pUsed && pUsed[iObj]) ||
         (vBoundary && Vec_IntFind((Vec_Int_t *)vBoundary, iObj) >= 0));
}

// Dereference and restore one root using scratch reference counts.  Testing a
// fanin's original ref count in isolation is incorrect for reconvergent MFFCs:
// removing an earlier parent can make a later shared fanin reach zero.  The
// paired traversals below reproduce Gia_NodeDeref_rec/Gia_NodeRef_rec while
// honoring virtual-selection and candidate-support cutpoints.
static int Cec_TranMffcDeref_rec( Gia_Man_t * p, int iObj, int iRoot,
    char const * pCovered, char const * pUsed,
    Vec_Int_t const * vBoundary, int * pRefs,
    char * pMark, Vec_Int_t * vMarked )
{
    Gia_Obj_t * pObj = Gia_ManObj( p, iObj );
    int iFan, Count = 1;
    assert( Gia_ObjIsAnd(pObj) );
    assert( !pMark[iObj] );
    pMark[iObj] = 1;
    Vec_IntPush( vMarked, iObj );
    iFan = Gia_ObjFaninId0p( p, pObj );
    if ( Gia_ObjIsAnd(Gia_ManObj(p, iFan)) &&
         !Cec_TranMffcIsBoundary(iFan, iRoot, pCovered, pUsed, vBoundary) )
    {
        assert( pRefs[iFan] > 0 );
        if ( --pRefs[iFan] == 0 )
            Count += Cec_TranMffcDeref_rec( p, iFan, iRoot, pCovered,
                pUsed, vBoundary, pRefs, pMark, vMarked );
    }
    iFan = Gia_ObjFaninId1p( p, pObj );
    if ( Gia_ObjIsAnd(Gia_ManObj(p, iFan)) &&
         !Cec_TranMffcIsBoundary(iFan, iRoot, pCovered, pUsed, vBoundary) )
    {
        assert( pRefs[iFan] > 0 );
        if ( --pRefs[iFan] == 0 )
            Count += Cec_TranMffcDeref_rec( p, iFan, iRoot, pCovered,
                pUsed, vBoundary, pRefs, pMark, vMarked );
    }
    return Count;
}

static int Cec_TranMffcRef_rec( Gia_Man_t * p, int iObj, int iRoot,
    char const * pCovered, char const * pUsed,
    Vec_Int_t const * vBoundary, int * pRefs )
{
    Gia_Obj_t * pObj = Gia_ManObj( p, iObj );
    int iFan, Count = 1;
    assert( Gia_ObjIsAnd(pObj) );
    iFan = Gia_ObjFaninId0p( p, pObj );
    if ( Gia_ObjIsAnd(Gia_ManObj(p, iFan)) &&
         !Cec_TranMffcIsBoundary(iFan, iRoot, pCovered, pUsed, vBoundary) &&
         pRefs[iFan]++ == 0 )
        Count += Cec_TranMffcRef_rec( p, iFan, iRoot, pCovered, pUsed,
            vBoundary, pRefs );
    iFan = Gia_ObjFaninId1p( p, pObj );
    if ( Gia_ObjIsAnd(Gia_ManObj(p, iFan)) &&
         !Cec_TranMffcIsBoundary(iFan, iRoot, pCovered, pUsed, vBoundary) &&
         pRefs[iFan]++ == 0 )
        Count += Cec_TranMffcRef_rec( p, iFan, iRoot, pCovered, pUsed,
            vBoundary, pRefs );
    return Count;
}

static void Cec_TranMarkDynamicMffcWithRefs( Gia_Man_t * p, int iRoot,
    char const * pCovered, char const * pUsed,
    Vec_Int_t const * vBoundary, int * pRefs,
    char * pMark, Vec_Int_t * vMarked )
{
    int nDeref, nRef;
    assert( pRefs != NULL );
    assert( Gia_ObjIsAnd(Gia_ManObj(p, iRoot)) );
    Cec_TranMffcScratchClear( pMark, vMarked );
    nDeref = Cec_TranMffcDeref_rec( p, iRoot, iRoot, pCovered, pUsed,
        vBoundary, pRefs, pMark, vMarked );
    nRef = Cec_TranMffcRef_rec( p, iRoot, iRoot, pCovered, pUsed,
        vBoundary, pRefs );
    assert( nDeref == nRef && nDeref == Vec_IntSize(vMarked) );
}

// Private reference snapshot.  Callers may reuse it while the graph and
// covered set are unchanged: each paired MFFC traversal restores its refs.
static int * Cec_TranMffcRefsStart( Gia_Man_t * p, char const * pCovered )
{
    Gia_Obj_t * pObj;
    int * pRefs;
    int i, iFan;
    assert( p->pRefs != NULL );
    pRefs = ABC_ALLOC( int, Gia_ManObjNum(p) );
    memcpy( pRefs, p->pRefs, sizeof(int) * Gia_ManObjNum(p) );
    // Covered objects have already been removed by earlier virtual choices.
    // Remove their structural fanin references from this scratch snapshot so
    // later roots see the true marginal MFFC.
    if ( pCovered )
    {
        Gia_ManForEachAnd( p, pObj, i )
            if ( pCovered[i] )
            {
                iFan = Gia_ObjFaninId0p( p, pObj );
                assert( pRefs[iFan] > 0 );
                pRefs[iFan]--;
                iFan = Gia_ObjFaninId1p( p, pObj );
                assert( pRefs[iFan] > 0 );
                pRefs[iFan]--;
            }
    }
    return pRefs;
}

static void Cec_TranMarkDynamicMffc( Gia_Man_t * p, int iRoot,
    char const * pCovered, char const * pUsed,
    Vec_Int_t const * vBoundary, char * pMark, Vec_Int_t * vMarked )
{
    int * pRefs = Cec_TranMffcRefsStart( p, pCovered );
    Cec_TranMarkDynamicMffcWithRefs( p, iRoot, pCovered, pUsed,
        vBoundary, pRefs, pMark, vMarked );
    ABC_FREE( pRefs );
}

static void Cec_TranCandCollectSupport( Cec_TranCand_t const * pCand,
    Vec_Int_t * vSupport )
{
    int i, Code, iObj;
    Vec_IntClear( vSupport );
    for ( i = -1; i < 2 * pCand->nGates; i++ )
    {
        Code = i < 0 ? pCand->iOut : pCand->Recipe[i];
        if ( Cec_TranRecipeCodeIsGate(Code) )
            continue;
        iObj = Abc_Lit2Var( Code );
        if ( iObj && Vec_IntFind(vSupport, iObj) < 0 )
            Vec_IntPush( vSupport, iObj );
    }
}
