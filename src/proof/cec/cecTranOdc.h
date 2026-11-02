#include "cecTranConstHelper.h"

// ODC proof, composition, and serial orchestration.
// Private implementation fragment included only by cecTrans.c.

static int Cec_TranOdcCandidateCompare( const void * p0, const void * p1 )
{
    Cec_TranCand_t const * pC0 = (Cec_TranCand_t const *)p0;
    Cec_TranCand_t const * pC1 = (Cec_TranCand_t const *)p1;
    if ( pC0->Gain != pC1->Gain )
        return pC1->Gain - pC0->Gain;
    if ( pC0->nMffc != pC1->nMffc )
        return pC1->nMffc - pC0->nMffc;
    if ( pC0->nGates != pC1->nGates )
        return pC0->nGates - pC1->nGates;
    if ( pC0->iTarget != pC1->iTarget )
        return pC1->iTarget - pC0->iTarget;
    return Cec_TranCandGainCompare( p0, p1 );
}

// A serial ODC commit contains one edit, so its exact Build marginal is the
// whole commit gain for Build and zero for Direct.
static void Cec_TranPrintOdcCommitProfile( int iRound, int nBefore,
    int nAfter, int fBuild, int fProfile, int fVerbose )
{
    CEC_TRAN_VERBOSE( fVerbose, "sresub ODC commit: round=%d AND=%d->%d.\n",
        iRound + 1, nBefore, nAfter );
    if ( fProfile )
        Abc_Print( 1, "sresub build reduction: scope=odc selected=%d and-before=%d and-without-build=%d and-after=%d ordered-and-gain=%d\n",
            fBuild, nBefore, fBuild ? nBefore : nAfter, nAfter,
            fBuild ? nBefore - nAfter : 0 );
}

// Auxiliary endpoints belong only to the proof graph.  For ordinary fanouts
// of r, prove the actual source gate g = lit(r)&s equal to lit(h)&s.  Seeding
// r=h would incorrectly assume the very equality which ODC relaxes.  The
// original transition relation is retained by Cec_TranBuildRootBatch, so the
// returned class equalities have both reset base and inductive closure.
// Unsupported incidence, direct PO/RI and full-care control use strict r=h.
static int Cec_TranOdcFanoutObligations( Gia_Man_t * p,
    Cec_TranCand_t const * pCand, int fFullCare,
    Cec_TranCandVec_t * pObligations )
{
    Gia_Obj_t * pFan;
    int f, iFan, iFan0, iFan1, nBefore = pObligations->nSize;
    int fFull = fFullCare || pCand->nGates == CEC_TRAN_RECIPE_NODES_MAX;
    assert( p->vFanoutNums && p->vFanout );
    Gia_ObjForEachFanoutStaticId( p, pCand->iTarget, iFan, f )
    {
        pFan = Gia_ManObj( p, iFan );
        if ( !Gia_ObjIsAnd(pFan) || Gia_ObjIsXor(pFan) ||
             Gia_ObjIsBuf(pFan) || Gia_ObjIsMux(p, pFan) )
        {
            fFull = 1;
            break;
        }
        iFan0 = Gia_ObjFaninId0p( p, pFan );
        iFan1 = Gia_ObjFaninId1p( p, pFan );
        if ( (iFan0 == pCand->iTarget) == (iFan1 == pCand->iTarget) )
        {
            fFull = 1;
            break;
        }
    }
    if ( fFull )
        Cec_TranCandVecPush( pObligations, *pCand );
    else Gia_ObjForEachFanoutStaticId( p, pCand->iTarget, iFan, f )
    {
        Cec_TranCand_t Obl = *pCand;
        int iSide, fCompl;
        pFan = Gia_ManObj( p, iFan );
        iFan0 = Gia_ObjFaninId0p( p, pFan );
        iSide = iFan0 == pCand->iTarget ?
            Gia_ObjFaninLit1p(p, pFan) : Gia_ObjFaninLit0p(p, pFan);
        fCompl = iFan0 == pCand->iTarget ?
            Gia_ObjFaninC0(pFan) : Gia_ObjFaninC1(pFan);
        Obl.iTarget = iFan;
        Obl.nGates++;
        Obl.Recipe = Cec_TranRecipeAlloc( 2 * Obl.nGates );
        if ( pCand->nGates )
            memcpy( Obl.Recipe, pCand->Recipe,
                sizeof(int) * 2 * pCand->nGates );
        Obl.Recipe[2 * pCand->nGates] = fCompl ?
            Cec_TranRecipeNotCode(pCand->iOut) : pCand->iOut;
        Obl.Recipe[2 * pCand->nGates + 1] = iSide;
        Obl.iOut = Cec_TranRecipeGateCode( pCand->nGates, 0 );
        Obl.fStrict = 1;
        Cec_TranCandVecPush( pObligations, Obl );
        Cec_TranCandRecipeRelease( &Obl );
    }
    // A dangling root needs no ODC obligation; conservatively require strict
    // equality anyway, avoiding a vacuous candidate-PASS implementation path.
    if ( pObligations->nSize == nBefore )
        Cec_TranCandVecPush( pObligations, *pCand );
    return fFull;
}

// Reconstruct the entire affected cone with the candidate substituted once.
// Reconvergent paths share the same changed node, rather than treating an
// affected side input as an independent frozen value. Prove all exits.
static int Cec_TranWindowObligations( Gia_Man_t * p,
    Cec_TranCand_t const * pCand, Cec_ParTran_t * pPars,
    Cec_TranCandVec_t * pObligations )
{
    Vec_Int_t * vNodes = Vec_IntAlloc(32), * vEnds = Vec_IntAlloc(16);
    int overflow, i, n, k, j, a, work[2*CEC_TRAN_RECIPE_NODES_MAX];
    int codes[CEC_TRAN_RECIPE_NODES_MAX+1], ng = pCand->nGates;
    Cec_TranWindowCollect(p,pCand->iTarget,Cec_TranWindowDepth(pPars),
        CEC_TRAN_RECIPE_NODES_MAX - pPars->nDepNodesMax,vNodes,vEnds,&overflow);
    if ( pPars->fOdcStrict || (pPars->nExplore & 16384) ||
         ng + Vec_IntSize(vNodes)-1 > CEC_TRAN_RECIPE_NODES_MAX )
    {
        Cec_TranCandVecPush(pObligations,*pCand);
        Vec_IntFree(vNodes); Vec_IntFree(vEnds); return 1;
    }
    if ( ng ) memcpy(work,pCand->Recipe,2*ng*sizeof(int));
    codes[0] = pCand->iOut;
    for ( i = 1; i < Vec_IntSize(vNodes); i++ )
    {
        Gia_Obj_t * pObj = Gia_ManObj(p,Vec_IntEntry(vNodes,i));
        for ( j = 0; j < 2; j++ )
        {
            a = j ? Gia_ObjFaninLit1p(p,pObj) : Gia_ObjFaninLit0p(p,pObj);
            k = Vec_IntFind(vNodes,Abc_Lit2Var(a)); assert(k < i);
            work[2*ng+j] = k < 0 ? a : Abc_LitIsCompl(a) ?
                Cec_TranRecipeNotCode(codes[k]) : codes[k];
        }
        codes[i] = Cec_TranRecipeGateCode(ng++,0);
    }
    Vec_IntForEachEntry(vEnds,n,i)
    {
        Cec_TranCand_t Obl = *pCand;
        Obl.iTarget = n; Obl.nGates = ng; Obl.fStrict = 1;
        Obl.iOut = codes[Vec_IntFind(vNodes,n)];
        Obl.Recipe = ng ? Cec_TranRecipeAlloc(2*ng) : NULL;
        if ( ng ) memcpy(Obl.Recipe,work,2*ng*sizeof(int));
        Cec_TranCandVecPush(pObligations,Obl);
        Cec_TranCandRecipeRelease(&Obl);
    }
    overflow = Vec_IntFind(vEnds,pCand->iTarget) >= 0;
    Vec_IntFree(vNodes); Vec_IntFree(vEnds); return overflow;
}
#include "cecTranWindowFactor.h"

// Conservative composability: regions cannot overlap, and no region may
// modify another region's frozen side inputs or candidate support. This
// makes every subset safe. The depth-one control uses the same rule.
static int Cec_TranWindowPoolAdd( Gia_Man_t * p, Cec_TranCand_t const * pCand,
    Cec_ParTran_t * pPars, char * pTargets, char * pReads, Vec_Int_t * vSupport )
{
    Vec_Int_t * vNodes = Vec_IntAlloc(32), * vEnds = Vec_IntAlloc(16);
    int overflow, n, i, j, a, pass = 0;
    if ( !Cec_TranProofHistoryTopoValid(p,pCand) ) goto done;
    Cec_TranWindowCollect(p,pCand->iTarget,Cec_TranWindowDepth(pPars),
        CEC_TRAN_RECIPE_NODES_MAX - pPars->nDepNodesMax,vNodes,vEnds,&overflow);
    Cec_TranCandCollectSupport(pCand,vSupport);
    // Candidate support must be earlier than its root (checked above), so
    // it cannot name any node in its own forward window.
    for ( i = 1; i < Vec_IntSize(vNodes); i++ )
    {
        Gia_Obj_t * pObj = Gia_ManObj(p,Vec_IntEntry(vNodes,i));
        for ( j = 0; j < 2; j++ )
        {
            a = j ? Gia_ObjFaninId1p(p,pObj) : Gia_ObjFaninId0p(p,pObj);
            if ( Vec_IntFind(vNodes,a) < 0 ) Vec_IntPushUnique(vSupport,a);
        }
    }
    Vec_IntForEachEntry(vNodes,n,i)
        if ( pTargets[n] || pReads[n] ) goto done;
    Vec_IntForEachEntry(vSupport,n,i)
        if ( pTargets[n] ) goto done;
    Vec_IntForEachEntry(vNodes,n,i) pTargets[n] = 1;
    Vec_IntForEachEntry(vSupport,n,i) pReads[n] = 1;
    pass = 1;
done:
    Vec_IntFree(vNodes); Vec_IntFree(vEnds); return pass;
}

// Conditions are hereditary: every subset of this pool is safe.  Existing
// MFFC/support conflict selection may therefore choose any subset afterward.
// Recipe external reads cannot be selected roots (in either insertion order),
// and no source AND can have two selected roots as fanins.  This is stronger
// than necessary for candidates proved in full care, deliberately so.
static int Cec_TranOdcFanoutPoolAdd( Gia_Man_t * p,
    Cec_TranCand_t const * pCand, char * pTargets, char * pReads,
    Vec_Int_t * vSupport )
{
    Gia_Obj_t * pFan;
    int f, i, iObj, iFan, iFan0, iFan1;
    if ( pTargets[pCand->iTarget] || pReads[pCand->iTarget] ||
         !Cec_TranProofHistoryTopoValid(p, pCand) )
        return 0;
    Cec_TranCandCollectSupport( pCand, vSupport );
    Vec_IntForEachEntry( vSupport, iObj, i )
        if ( pTargets[iObj] || iObj == pCand->iTarget )
            return 0;
    Gia_ObjForEachFanoutStaticId( p, pCand->iTarget, iFan, f )
    {
        pFan = Gia_ManObj( p, iFan );
        if ( !Gia_ObjIsAnd(pFan) || Gia_ObjIsBuf(pFan) )
            continue;
        iFan0 = Gia_ObjFaninId0p( p, pFan );
        iFan1 = Gia_ObjFaninId1p( p, pFan );
        if ( pTargets[iFan0] || pTargets[iFan1] )
            return 0;
    }
    pTargets[pCand->iTarget] = 1;
    Vec_IntForEachEntry( vSupport, iObj, i )
        pReads[iObj] = 1;
    return 1;
}

// Every subset of the composable selected set is safe.  Attribute exact AND
// reduction in Constant -> Existing -> Build order on that SAME set, without
// reselection or changing the commit.  In particular, new Direct reductions
// and their cleanup effects are never reported as Ordered Seq Build gain.
static void Cec_TranOdcKindGains( Gia_Man_t * p,
    Cec_TranCandVec_t const * pSelected, Gia_Man_t * pFinal,
    int * pKindSelected, int * pKindGain )
{
    Vec_Int_t * vSubset = Vec_IntAlloc(pSelected->nSize);
    int i, k, nPrev = Gia_ManAndNum(p), nNext;
    memset(pKindSelected, 0, sizeof(int) * 3);
    memset(pKindGain, 0, sizeof(int) * 3);
    for ( i = 0; i < pSelected->nSize; i++ )
        pKindSelected[pSelected->pArray[i].nKind]++;
    for ( k = 0; k < 3; k++ )
    {
        for ( i = 0; i < pSelected->nSize; i++ )
            if ( pSelected->pArray[i].nKind == k )
                Vec_IntPush(vSubset, i);
        if ( !pKindSelected[k] )
            continue;
        if ( Vec_IntSize(vSubset) == pSelected->nSize )
            nNext = Gia_ManAndNum(pFinal);
        else
        {
            Gia_Man_t * pDup = Cec_TranDupRootBundle(p, pSelected->pArray, vSubset);
            Gia_Man_t * pClean = Cec_TranCleanupKeepRegs(pDup, NULL);
            nNext = Gia_ManAndNum(pClean);
            assert(Gia_ManRegNum(pClean) == Gia_ManRegNum(p));
            Gia_ManStop(pClean);
            Gia_ManStop(pDup);
        }
        pKindGain[k] = nPrev - nNext;
        nPrev = nNext;
    }
    assert(pKindGain[0] + pKindGain[1] + pKindGain[2] ==
        Gia_ManAndNum(p) - Gia_ManAndNum(pFinal));
    Vec_IntFree(vSubset);
}

// Composition proof: fix a state reachable in frozen N and the current PIs.
// Topological induction preserves every nonselected source node.  A selected
// root evaluates h on earlier nonselected external reads, hence to its frozen
// h value.  A nonselected AND has either zero changed inputs or one selected
// root; the latter case is exactly its discharged fanout obligation.  Special
// gates and COs can read selected roots only with strict equality proved.
// Preserved RIs and the unchanged register interface then preserve reachability
// frame by frame.  Helpers may participate in correspondence closure without
// being physical edits.  Never carry these ODC certificates across a commit.
static int Cec_TranOdcExitProofLane( Vec_Int_t * vStatus, Vec_Str_t * vStage,
    int Begin, int End )
{
    int k, Lane = 1;
    assert(Begin >= 0 && End >= Begin);
    for ( k = Begin; k < End; ++k )
    {
        if ( !Vec_IntEntry(vStatus,k) ) return 0;
        assert(Vec_StrEntry(vStage,k) == 1 || Vec_StrEntry(vStage,k) == 2);
        if ( Vec_StrEntry(vStage,k) == 2 ) Lane = 2;
    }
    return Lane; // an unobserved target needs no temporal obligation
}

static Gia_Man_t * Cec_TranOdcFanoutRound( Gia_Man_t * p,
    Cec_TranCandVec_t * pFrontier,
    Cec_TranCand_t const * pHelpers, int nHelpers, Cec_ParTran_t * pPars,
    Cec_TranProf_t * pProf, int iRound, int * pnTried, int * pnSelected,
    long long * pnObligations, long long * pnProved, long long * pnBatches,
    abctime * pTimeProof, int * pKindSelected, int * pKindGain )
{
    Cec_TranCandVec_t Obligations = {0}, SafePool = {0}, Selected = {0};
    Vec_Int_t * vBeg = Vec_IntAlloc( pFrontier->nSize + 1 );
    Vec_Int_t * vStatus = NULL, * vSupport = Vec_IntAlloc( 32 );
    Vec_Int_t * vMffc = Vec_IntAlloc( 128 ), * vSelected = Vec_IntAlloc( 16 );
    Vec_Str_t * vStage = NULL;
    char * pTargets = ABC_CALLOC( char, Gia_ManObjNum(p) );
    char * pReads = ABC_CALLOC( char, Gia_ManObjNum(p) );
    char * pCovered = ABC_CALLOC( char, Gia_ManObjNum(p) );
    char * pUsed = ABC_CALLOC( char, Gia_ManObjNum(p) );
    char * pSolved = ABC_CALLOC( char, Gia_ManObjNum(p) );
    char * pMffc = ABC_CALLOC( char, Gia_ManObjNum(p) );
    Gia_Man_t * pDup, * pClean = NULL;
    int i, k, nProved = 0, nFull = 0, nConflicts = 0, nProofs = 0;
    int KindSubmitted[3] = {0}, KindProved[3] = {0};
    int fCombBoundaryOnly = (pPars->nExplore & 4096) != 0;
    int nLimit = pPars->nOdcProofMax ?
        Abc_MinInt(pFrontier->nSize, pPars->nOdcProofMax) : pFrontier->nSize;
    abctime clk = Abc_Clock();
    Gia_ManStaticFanoutStart( p );
    Vec_IntPush( vBeg, 0 );
    for ( i = 0; i < nLimit; i++ )
    {
        KindSubmitted[pFrontier->pArray[i].nKind]++;
        if ( pPars->fWindowFactor )
            Cec_TranCandVecPush(&Obligations,pFrontier->pArray[i]);
        else nFull += (pPars->nExplore & 134217728) ?
            Cec_TranWindowObligations(p,pFrontier->pArray+i,pPars,&Obligations) :
            Cec_TranOdcFanoutObligations( p, pFrontier->pArray + i,
                pPars->fOdcStrict || (pPars->nExplore & 16384), &Obligations );
        Vec_IntPush( vBeg, Obligations.nSize );
    }
    if ( Obligations.nSize )
    {
        if ( pPars->fWindowFactor )
            vStatus = Cec_TranProveWindowFactorBatch(p,pHelpers,nHelpers,Obligations.pArray,
                Obligations.nSize,pPars,pProf,fCombBoundaryOnly,&vStage,&nFull);
        else vStatus = Cec_TranProveRootBatch( p, pHelpers, nHelpers,
            Obligations.pArray, Obligations.nSize, pPars, pProf,
            fCombBoundaryOnly, &vStage );
        (*pnBatches)++;
    }
    *pTimeProof = Abc_Clock() - clk;
    for ( i = 0; i < nLimit; i++ )
    {
        Cec_TranCand_t Cand = pFrontier->pArray[i];
        int Lane = Cec_TranOdcExitProofLane(vStatus,vStage,
            Vec_IntEntry(vBeg,i),Vec_IntEntry(vBeg,i+1));
        int fProved = Lane != 0;
        for ( k = Vec_IntEntry(vBeg, i); k < Vec_IntEntry(vBeg, i+1); k++ )
        {
            fProved &= Vec_IntEntry( vStatus, k );
            nProofs += Vec_IntEntry( vStatus, k );
        }
        if(getenv("ABC_CEX_DETAIL")) Abc_Print(1,"cex-proof round=%d root=%d hash=%u proved=%d gain=%d\n",iRound+1,Cand.iTarget,Cec_TranCandHash(&Cand),fProved,Cand.Gain);
        if ( !fProved )
            continue;
        nProved++;
        KindProved[Cand.nKind]++;
        if ( !( (pPars->nExplore & 134217728) ?
            Cec_TranWindowPoolAdd(p,&Cand,pPars,pTargets,pReads,vSupport) :
            Cec_TranOdcFanoutPoolAdd(p,&Cand,pTargets,pReads,vSupport) ) )
        {
            nConflicts++;
            continue;
        }
        // This status is consumed ONLY by structural selection below.  It is
        // not a strict r=h certificate and never enters strict proof history.
        Cand.nStatus = Lane == 1 ? CEC_TRAN_STATE_PROVED_COMB :
            CEC_TRAN_STATE_PROVED_SEQ;
        Cand.nProofStage = Cand.nProofLane = Lane;
        Cand.nProofPhase = 1;
        Cand.nProofKind = Cand.nKind;
        Cec_TranCandVecPush( &SafePool, Cand );
    }
    Gia_ManStaticFanoutStop( p );
    *pnTried = nLimit;
    *pnObligations += Obligations.nSize;
    *pnProved += nProved;
    if ( SafePool.nSize )
        Cec_TranRootConsumeProved( p, &SafePool, pCovered, pUsed, pSolved,
            pMffc, vMffc, vSupport, &Selected, pProf );
    *pnSelected = Selected.nSize;
    if(getenv("ABC_CEX_DETAIL")) for(i=0;i<Selected.nSize;++i)
        Abc_Print(1,"cex-selected round=%d root=%d hash=%u gain=%d\n",iRound+1,Selected.pArray[i].iTarget,Cec_TranCandHash(Selected.pArray+i),Selected.pArray[i].Gain);

    if ( Selected.nSize )
    {
        for ( i = 0; i < Selected.nSize; i++ )
            Vec_IntPush( vSelected, i );
        pDup = Cec_TranDupRootBundle( p, Selected.pArray, vSelected );
        pClean = Cec_TranCleanupKeepRegs( pDup, NULL );
        assert( Gia_ManRegNum(pClean) == Gia_ManRegNum(p) );
        assert( Cec_TranGain(p, pClean) > 0 );
        Cec_TranOdcKindGains(p, &Selected, pClean, pKindSelected, pKindGain);
        Gia_ManStop( pDup );
    }
    if ( pPars->fProfile )
        Cec_TranBuildReductionProfile(p,&Selected,pClean ? pClean : p,"odc");
    if ( fCombBoundaryOnly )
        CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root ODC boundary engine: schema=1 mode=comb-only candidates=%d proved=%d selected=%d.\n",
            nLimit, nProved, *pnSelected);
    if ( pPars->nExplore & 512 )
        for ( k = 0; k < 3; k++ )
            CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root ODC kind profile: schema=1 round=%d kind=%s submitted=%d proved=%d selected=%d ordered-and-gain=%d.\n",
                iRound + 1, k == 0 ? "constant" : k == 1 ? "existing" : "build",
                KindSubmitted[k], KindProved[k], pKindSelected[k], pKindGain[k]);
    CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root ODC fanout round: schema=1 round=%d candidates=%d obligations=%d full-care=%d proved-obligations=%d proved-candidates=%d composition-conflicts=%d selected=%d proof-batches=%d comb-unknown=%lld seq-incomplete=%d bmc-unknown=%lld ind-unknown=%lld proof-sec=%.6f.\n",
        iRound + 1, nLimit, Obligations.nSize, nFull, nProofs, nProved,
        nConflicts, *pnSelected, Obligations.nSize != 0,
        (long long)pProf->nCombUnknown, pProf->nSeqUnknown,
        (long long)pProf->Corr.nBmcUnknown, (long long)pProf->Corr.nIndUnknown,
        Cec_TranTimeSec(*pTimeProof) );
    Cec_TranCandVecStop( &Obligations );
    Cec_TranCandVecStop( &SafePool );
    Cec_TranCandVecStop( &Selected );
    Vec_IntFree( vBeg );
    Vec_IntFreeP( &vStatus );
    Vec_StrFreeP( &vStage );
    Vec_IntFree( vSupport );
    Vec_IntFree( vMffc );
    Vec_IntFree( vSelected );
    ABC_FREE( pTargets );
    ABC_FREE( pReads );
    ABC_FREE( pCovered );
    ABC_FREE( pUsed );
    ABC_FREE( pSolved );
    ABC_FREE( pMffc );
    return pClean;
}

// Quality-first ODC reference implementation.  Strict COMB/SEQ processing has
// already reached its configured fixed point before this routine is called.
// On each current snapshot, Build is reconstructed using the immediate-fanout
// care mask, candidates are ordered by current structural gain, and whole-
// machine sequential miters are tried one by one.  The first proof is committed
// alone; all remaining candidates and masks are discarded and rediscovered on
// the new graph.  Consequently no ODC certificate is ever reused across a
// state change and no pair of interacting ODC replacements shares a proof.
static Gia_Man_t * Cec_TranRunOdcSerial( Gia_Man_t * p,
    Cec_ParTran_t * pPars, Cec_TranPatDb_t * pSharedDb )
{
    Cec_ParTran_t OdcPars = *pPars;
    long long nGenerated = 0, nPositive = 0, nSampleStrict = 0;
    long long nAttempts = 0, nRejected = 0, nCommits = 0;
    long long nGain = 0, nLimitHits = 0;
    long long nObligations = 0, nProved = 0, nBatches = 0;
    int nInitial = Gia_ManAndNum( p );
    int fUseCare = !OdcPars.fOdcStrict;
    int fCut = OdcPars.fRoute3 && fUseCare &&
        Cec_TranStrictCexOption("ABC_SRESUB_ODC_CUT",1,1);
    int fOdcDirect = OdcPars.fOdcFanout && (OdcPars.nExplore & 512);
    int CarePairTruth = OdcPars.fOdcFanout && fUseCare ?
        Cec_TranStrictCexOption("ABC_ODC_CARE_PAIR_TRUTH",Cec_TranReviewedOdc(&OdcPars),1) : 0;
    int SavedCarePairTruth = Abc_ResubSetCarePairTruth(CarePairTruth);
    int SavedPackDefault = s_CexPackDefault;
    int iRound, fConstHelpers;
    abctime TimeAll = Abc_Clock(), TimeProofAll = 0;

    // This owned stage-local copy is the only pipeline entry that activates
    // the relational lane. The global fanout option also occurs in Strict.
    OdcPars.fOdcProofScope = OdcPars.fOdcFanout;
    s_CexPackDefault = Cec_TranReviewedOdc(&OdcPars) ? 2 : 0;
    fConstHelpers = Cec_TranConstHelpersEnabled(&OdcPars);
    CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root ODC CONST-helper policy: schema=1 enabled=%d scope=odc-relational source=original-reset-signatures proof-only=1 q-slots=0 commit=0.\n",fConstHelpers);
    CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root ODC pair-truth policy: schema=1 enabled=%d scope=odc fixed-material-pool=1.\n",CarePairTruth);

    // ODC is an additional Build portfolio, not a second Direct/scorr pass.
    // One page retrieves the same q-prefix without changing the strict proof
    // micro-batch policy.  Pool-conflict pruning is a strict-function test and
    // is therefore disabled only inside this care-aware phase.
    OdcPars.fBuildOnly = !fOdcDirect;
    // Quality-study overrides apply only after the frozen strict prefix.
    if ( OdcPars.nExplore & 32768 ) OdcPars.nBTLimit = 10000;
    if ( OdcPars.nExplore & 65536 ) OdcPars.nFrames = 2;
    if ( OdcPars.nExplore & 131072 ) OdcPars.nRootConstrTop = 80;
    if ( OdcPars.nExplore & 262144 ) OdcPars.nFrames = 4;
    if ( OdcPars.nExplore & 524288 ) OdcPars.nRootConstrTop = 320;
    if ( OdcPars.nExplore & 1048576 ) OdcPars.nDepNodesMax = 40;
    if ( OdcPars.nExplore & 2097152 ) OdcPars.nConstrMax = 0;
    if ( OdcPars.nExplore & 4194304 ) OdcPars.nConstrBaseMax = 64;
    if ( OdcPars.nExplore & 8388608 ) OdcPars.nConstrBaseMax = 128;
    // Route3's Strict stage intentionally keeps the frozen W64 N100/K0
    // search.  Restore the reviewed route1 ODC construction bounds only in
    // this owned stage-local copy, after Strict has produced its real graph.
    if ( OdcPars.fRoute3 )
    {
        OdcPars.nDepNodesMax = 20;
        OdcPars.nConstrMax = 8;
        OdcPars.nSimWords = 4;
        OdcPars.nSimFrames = 8;
        OdcPars.fResetNested = 0;
    }
    // Explicit stage-local options take precedence over legacy -E presets.
    if ( OdcPars.nWindowFrames >= 0 ) OdcPars.nFrames = OdcPars.nWindowFrames;
    if ( OdcPars.nWindowConflicts >= 0 ) OdcPars.nBTLimit = OdcPars.nWindowConflicts;
    if ( OdcPars.nWindowDivs >= 0 ) OdcPars.nConstrBaseMax = OdcPars.nWindowDivs;
    if ( OdcPars.nWindowCandidates >= 0 ) OdcPars.nRootConstrTop = OdcPars.nWindowCandidates;
    if ( OdcPars.nWindowSteps >= -1 ) OdcPars.nStepsMax = OdcPars.nWindowSteps;
    assert(!OdcPars.fWindowFactor || (OdcPars.fOdcFanout && (OdcPars.nExplore & 134217728)));
    if ( OdcPars.fWindowCache ) Abc_ResubProblemCacheStart(OdcPars.nWindowCacheMiB);
    CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-window options: S=%d cache=%d factor=%d.\n",
        OdcPars.nStepsMax,OdcPars.fWindowCache,OdcPars.fWindowFactor);
    CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root ODC quality config: F=%d C=%d q=%d B=%d N=%d K=%d Q=%d W=%d nested=%d care-kit=%d strict-root=%d.\n",
        OdcPars.nFrames, OdcPars.nBTLimit, OdcPars.nRootConstrTop,
        OdcPars.nConstrBaseMax, OdcPars.nDepNodesMax, OdcPars.nConstrMax,
        OdcPars.nSimWords, OdcPars.nSimFrames, OdcPars.fResetNested,
        !!(OdcPars.nExplore & 8192), !!(OdcPars.nExplore & 16384));
    CEC_TRAN_VERBOSE( pPars->fVerbose, "sresub ODC cut config: schema=1 enabled=%d leaves=%d algorithm=%s depth=%d proof=unchanged\n",
        fCut,fCut ? 4 : 0,fCut ? "original-drw4" : "none",OdcPars.nConstrMax);
    if ( OdcPars.nExplore & 134217728 )
        CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root ODC spatial window config: depth=%d max-extra-ands=%d F=%d C=%d.\n",
            Cec_TranWindowDepth(&OdcPars),100-OdcPars.nDepNodesMax,OdcPars.nFrames,OdcPars.nBTLimit);
    if ( OdcPars.nExplore & 16777216 ) OdcPars.nStage5Paths = 4;
    assert( !OdcPars.nSignatureGuide || (OdcPars.fOdcFanout && fUseCare &&
        OdcPars.fUseConstr && (OdcPars.nExplore & 134217728) &&
        Cec_TranStrictCexOption("ABC_CEX_MODE",Cec_TranReviewedOdc(&OdcPars) ? 2 : 0,3) == 2 &&
        Cec_TranStrictCexOption("ABC_CEX_COMPRESS",Cec_TranReviewedOdc(&OdcPars) ? 4 : 0,6) == 4) );
    OdcPars.nRootProofBatch = 0;
    OdcPars.nExplore &= ~6;
    // A uniform round cap bounds repeated rediscovery, independently of the
    // frontier size.  It changes only -J and never admits an unproved edit.
    for ( iRound = 0; !OdcPars.fOdcFanout || !OdcPars.nOdcFanoutRounds ||
          iRound < OdcPars.nOdcFanoutRounds; iRound++ )
    {
        Cec_TranProf_t Prof = {0};
        Cec_TranCandVec_t Known = {0}, RootCands = {0};
        Cec_TranCandVec_t Candidates = {0}, Frontier = {0}, ConstHelpers = {0};
        Cec_TranRoot_t * pRoots;
        Cec_TranRootCursor_t * pCursors;
        Cec_TranDepScratch_t Dep;
        Cec_TranPatDb_t * pDb;
        Cec_TranSim_t * pSource, * pSim;
        Cec_TranSigGuide_t * pSigGuide;
        Gia_Man_t * pDup = NULL, * pClean = NULL;
        Gia_Obj_t * pObj;
        Vec_Int_t * vMffc = Vec_IntAlloc( 128 );
        Vec_Int_t * vSupport = Vec_IntAlloc( 32 );
        Vec_Int_t * vOne = Vec_IntAlloc( 1 );
        char * pMffc = ABC_CALLOC( char, Gia_ManObjNum(p) );
        char * pSolved = ABC_CALLOC( char, Gia_ManObjNum(p) );
        char * pCovered = ABC_CALLOC( char, Gia_ManObjNum(p) );
        char * pUsed = ABC_CALLOC( char, Gia_ManObjNum(p) );
        char * pSampleStrict = NULL;
        int fOwnDb = pSharedDb == NULL;
        int fRootBatch, fCommitted = 0, fCommittedBuild = 0;
        int nRoots = 0, r, i, nTfoMax = OdcPars.nConstrBaseMax;
        int nBefore = Gia_ManAndNum( p ), nTried = 0, nSelected = 0;
        int nGeneratedRound = 0, nPositiveRound = 0;
        int KindSelected[3] = {0}, KindGain[3] = {0};
        int nMffcOneRoots = 0, nMffcOneCandidates = 0;
        abctime TimeProof = 0;

        // This is a post-strict sequential phase.  Preserve the latest SEQ
        // Kit/BDC portfolio gate instead of silently falling back to native
        // Build only when the ODC-local profile object is initialized.
        Prof.fVerbose = OdcPars.fVerbose;
        Prof.DiagPhase = 1;
        pDb = fOwnDb ? Cec_TranPatDbStart( p, 0 ) : pSharedDb;
        Gia_ManCreateRefs( p );
        if ( fCut )
        {
            abctime clkCut = Abc_Clock();
            Prof.OdcCutSize = 4;
            Prof.pOdcCutCache = Cec_TranCutCacheStartMode(p,4,1,0);
            Prof.timeCutSetup = Abc_Clock() - clkCut;
        }
        Gia_ManStaticFanoutStart( p );
        Gia_ManForEachAnd( p, pObj, i )
            nRoots++;
        pRoots = ABC_ALLOC( Cec_TranRoot_t, nRoots );
        nRoots = 0;
        Gia_ManForEachAnd( p, pObj, i )
            pRoots[nRoots].iObj = i,
            pRoots[nRoots].nMffc = Gia_NodeMffcSize( p, pObj ),
            nRoots++;
        qsort( pRoots, nRoots, sizeof(Cec_TranRoot_t), Cec_TranRootCompare );
        pCursors = ABC_CALLOC( Cec_TranRootCursor_t, Gia_ManObjNum(p) );
        pSource = Cec_TranSimStart( p, &OdcPars, pDb );
        if ( fConstHelpers )
            Cec_TranConstHelperNominate(p,pSource,&ConstHelpers,&Prof);
        fRootBatch = Vec_PtrSize(pDb->vCexes) > 64 * OdcPars.nSimWords;
        pSim = fRootBatch ? Cec_TranSimStartRootBatch( p,
            OdcPars.nSimWords, OdcPars.nSimFrames ) : pSource;
        Abc_ResubPrepareManager( pSim->nSlots );
        Cec_TranDepScratchStart( &Dep, pSim->nSlots,
            OdcPars.nConstrBaseMax ? OdcPars.nConstrBaseMax : 64, 1 );
        s_CexMode = Cec_TranStrictCexOption("ABC_CEX_MODE",Cec_TranReviewedOdc(&OdcPars) ? 2 : 0,3);
        assert(s_CexMode >= 0 && s_CexMode <= 3);
        s_CexRound=iRound+1;
        s_CexRoots=s_CexTriggered=s_CexPoints=s_CexAdded=0; s_CexTime=0;
        s_CexCoreConflicts=s_CexRefinedLabels=0;
        s_CexCompress=Cec_TranStrictCexOption("ABC_CEX_COMPRESS",Cec_TranReviewedOdc(&OdcPars) ? 4 : 0,6);
        assert(s_CexCompress>=0 && s_CexCompress<=6);
        s_CexRawRows=s_CexUniqueRows=s_CexTables=s_CexPoolConflict=0;
        s_CexNarrowing=0; s_CexNarrowRoots=s_CexNarrowDivsBefore=s_CexNarrowDivsAfter=0;
        s_CexPackTime=s_CexSelectTime=s_CexConstructTime=s_CexNativeTime=s_CexDiscoveryTime=0;
        s_CexProjectAll=getenv("ABC_CEX_PROJECT_ALL") ? atoi(getenv("ABC_CEX_PROJECT_ALL")) : 0;
        assert(s_CexProjectAll==0 || s_CexProjectAll==1);
        if (s_CexMode) {
            Cec_ParTran_t LongPars=OdcPars;
            Cec_TranPatDb_t * empty=Cec_TranPatDbStart(p,0);
            abctime cx=Abc_Clock();
            assert(!fRootBatch && fUseCare && (OdcPars.nExplore & 134217728));
            LongPars.nSimWords=1; LongPars.nSimFrames=256;
            s_CexLong=Cec_TranSimStart(p,&LongPars,empty);
            s_CexAug=Cec_TranSimStartRootBatch(p,pSim->nSlots+1,1);
            if(s_CexCompress) s_CexPacked=Cec_TranSimStartRootBatch(p,pSim->nSlots+s_CexLong->nSlots,1);
            Cec_TranPatDbStop(empty);
            s_CexTime+=Abc_Clock()-cx;
            if (getenv("ABC_CEX_DETAIL")) {
                int ci, f;
                Abc_Print(1,"cex-snapshot round=%d objects=%d regs=%d\n",s_CexRound,Gia_ManObjNum(p),Gia_ManRegNum(p));
                Gia_ManForEachCi(p,pObj,ci) Abc_Print(1,"cex-ci index=%d id=%d\n",ci,Gia_ObjId(p,pObj));
                Gia_ManForEachAnd(p,pObj,ci) Abc_Print(1,"cex-gate id=%d a=%d b=%d xor=%d\n",ci,Gia_ObjFaninLit0p(p,pObj),Gia_ObjFaninLit1p(p,pObj),Gia_ObjIsXor(pObj));
                Gia_ManForEachCo(p,pObj,ci) Abc_Print(1,"cex-co index=%d lit=%d\n",ci,Gia_ObjFaninLit0p(p,pObj));
                Gia_ManForEachCi(p,pObj,ci) {
                    Abc_Print(1,"cex-old-ci id=%d words=",Gia_ObjId(p,pObj));
                    for(f=0;f<pSim->nSlots;++f) Abc_Print(1,"%s%llx",f?",":"",(unsigned long long)Cec_TranSimObj(pSim,Gia_ObjId(p,pObj))[f]);
                    Abc_Print(1,"\n");
                }
                for(f=0;f<s_CexLong->nSlots;++f) {
                    Abc_Print(1,"cex-pis frame=%d words=",f);
                    Gia_ManForEachPi(p,pObj,ci) Abc_Print(1,"%s%llx",ci?",":"",(unsigned long long)Cec_TranSimObj(s_CexLong,Gia_ObjId(p,pObj))[f]);
                    Abc_Print(1,"\n");
                }
            }
        }
        pSigGuide = Cec_TranSigGuideStart( p, OdcPars.nSignatureGuide );
        { abctime cd=Abc_Clock();
        for ( r = 0; r < nRoots; r++ )
        {
            if ( pRoots[r].nMffc <= 0 || (!fOdcDirect && pRoots[r].nMffc <= 1) )
                continue;
            if ( pRoots[r].nMffc == 1 )
            {
                Cec_TranOdcDirectMffcOne( p, pSource, &OdcPars, pRoots + r,
                    fUseCare, &Known, &RootCands, &Prof );
                nMffcOneRoots++;
                nMffcOneCandidates += RootCands.nSize;
            }
            else Cec_TranRootDiscoverOne( p, pSim, pSource, pDb, fRootBatch,
                &OdcPars, pRoots + r, pCursors + pRoots[r].iObj, 0,
                OdcPars.fUseTfoDivs, nTfoMax, fUseCare, &Known, pSolved,
                pCovered, pUsed, pMffc, vMffc, &Dep, &Prof,
                &RootCands, pSigGuide );
            for ( i = 0; i < RootCands.nSize; i++ )
            {
                Cec_TranCandVecPush( &Known, RootCands.pArray[i] );
                Cec_TranCandVecPush( &Candidates, RootCands.pArray[i] );
            }
        }
        s_CexDiscoveryTime=Abc_Clock()-cd; }
        // Rebuild from the next graph after every commit. Never retain a cut
        // manager, divisor pool or care mask across ODC snapshots.
        Cec_TranCutCacheStop((Cec_TranCutCache_t *)Prof.pOdcCutCache);
        Prof.pOdcCutCache = NULL;
        if ( fOdcDirect )
        {
            int KindGenerated[3] = {0};
            for ( i = 0; i < Candidates.nSize; i++ )
                KindGenerated[Candidates.pArray[i].nKind]++;
            CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root ODC direct discovery: schema=1 round=%d mffc-one-roots=%d mffc-one-generated=%d constant-generated=%d existing-generated=%d build-generated=%d.\n",
                iRound + 1, nMffcOneRoots, nMffcOneCandidates,
                KindGenerated[0], KindGenerated[1], KindGenerated[2]);
        }
        Cec_TranRootPrepareSeqFrontier( p, pRoots, nRoots, &Candidates,
            pCovered, pUsed, pMffc, vMffc, vSupport, 0, &Frontier, &Prof );
        if ( Frontier.nSize > 1 )
            qsort( Frontier.pArray, Frontier.nSize,
                sizeof(Cec_TranCand_t), Cec_TranOdcCandidateCompare );
        pSampleStrict = ABC_CALLOC( char, Frontier.nSize );
        for ( i = 0; i < Frontier.nSize; i++ )
        {
            pSampleStrict[i] = Cec_TranRecipeMatchesRoot(
                pSource, Frontier.pArray + i, NULL );
            nSampleStrict += pSampleStrict[i];
        }
        CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root ODC enumeration: round=%d roots=%d iter-init=%d iter-next=%d iter-exhausted=%d iter-capped=%d pivot-attempts=%lld accepted=%lld generated=%d positive=%d core-variants=%lld care-pool-changed=%lld.\n",
            iRound + 1, nRoots, Prof.nRootResubIterInit,
            Prof.nRootResubIterNext, Prof.nRootResubIterExhausted,
            Prof.nRootResubIterCapped, Prof.nRootGreedyPivotAttempts,
            (long long)Prof.nRootBuildAccepted, Candidates.nSize, Frontier.nSize,
            Prof.nOdcCoreVariants, Prof.nOdcCarePoolChanged );
        if ( OdcPars.nExplore & 134217728 )
            CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root ODC window discovery: round=%d roots=%lld nodes=%lld exits=%lld capacity-cuts=%lld care-bits=%lld total-bits=%lld.\n",
                iRound+1,Prof.nOdcWindowRoots,Prof.nOdcWindowNodes,Prof.nOdcWindowEnds,
                Prof.nOdcWindowOverflow,Prof.nOdcWindowCareBits,Prof.nOdcWindowBits);
        if(s_CexMode || getenv("ABC_CEX_PROFILE"))
            CEC_TRAN_VERBOSE( pPars->fVerbose || getenv("ABC_CEX_PROFILE"), "cex-build-time round=%d discovery-sec=%.6f native-sec=%.6f\n",s_CexRound,Cec_TranTimeSec(s_CexDiscoveryTime),Cec_TranTimeSec(s_CexNativeTime));
        if(s_CexMode) {
            CEC_TRAN_VERBOSE( pPars->fVerbose || getenv("ABC_CEX_PROFILE"), "cex-summary round=%d mode=%d roots=%lld triggered=%lld points=%lld added=%lld seconds=%.6f\n",s_CexRound,s_CexMode,s_CexRoots,s_CexTriggered,s_CexPoints,s_CexAdded,Cec_TranTimeSec(s_CexTime));
            if(s_CexProjectAll) CEC_TRAN_VERBOSE( pPars->fVerbose || getenv("ABC_CEX_PROFILE"), "cex-isf-refine round=%d conflicting-cores=%lld refined-labels=%lld\n",s_CexRound,s_CexCoreConflicts,s_CexRefinedLabels);
            if(s_CexCompress>=5) CEC_TRAN_VERBOSE( pPars->fVerbose || getenv("ABC_CEX_PROFILE"), "cex-core-guide round=%d roots=%lld divs-before=%lld divs-after=%lld\n",s_CexRound,s_CexNarrowRoots,s_CexNarrowDivsBefore,s_CexNarrowDivsAfter);
            if(s_CexCompress) {
                CEC_TRAN_VERBOSE( pPars->fVerbose || getenv("ABC_CEX_PROFILE"), "cex-compression round=%d mode=%d tables=%lld raw=%lld unique=%lld pool-conflict=%lld pack-sec=%.6f select-sec=%.6f construct-sec=%.6f\n",s_CexRound,s_CexCompress,s_CexTables,s_CexRawRows,s_CexUniqueRows,s_CexPoolConflict,Cec_TranTimeSec(s_CexPackTime),Cec_TranTimeSec(s_CexSelectTime),Cec_TranTimeSec(s_CexConstructTime));
                Cec_TranSimStop(s_CexPacked); s_CexPacked=NULL;
                ABC_FREE(s_CexWeights);
            }
            Cec_TranSimStop(s_CexLong); Cec_TranSimStop(s_CexAug);
            s_CexLong=s_CexAug=NULL; s_CexMode=0;
        }
        nGenerated += Candidates.nSize;
        nPositive += Frontier.nSize;
        nGeneratedRound = Candidates.nSize;
        nPositiveRound = Frontier.nSize;

        for ( i = 0; i < Gia_ManObjNum(p); i++ )
            Cec_TranRootCursorStop( pCursors + i );
        Cec_TranDepScratchStop( &Dep );
        Abc_ResubPrepareManager( 0 );
        if ( fRootBatch )
            Cec_TranSimStop( pSim );
        Cec_TranSimStop( pSource );
        Gia_ManStaticFanoutStop( p );
        if ( fOwnDb )
            Cec_TranPatDbStop( pDb );

        if ( OdcPars.fOdcFanout )
        {
            pClean = Cec_TranOdcFanoutRound( p, &Frontier, ConstHelpers.pArray,
                ConstHelpers.nSize, &OdcPars, &Prof,
                iRound, &nTried, &nSelected, &nObligations, &nProved,
                &nBatches, &TimeProof, KindSelected, KindGain );
            fCommitted = pClean != NULL;
            nAttempts += nTried;
            if ( fCommitted )
                nGain += Cec_TranGain(p, pClean), nCommits += nSelected;
        }
        else
        for ( i = 0; i < Frontier.nSize &&
              (!OdcPars.nOdcProofMax || nTried < OdcPars.nOdcProofMax); i++ )
        {
            int Gain;
            abctime clk;
            Vec_IntClear( vOne );
            Vec_IntPush( vOne, 0 );
            pDup = Cec_TranDupRootBundle( p, Frontier.pArray + i, vOne );
            pClean = Cec_TranCleanupKeepRegs( pDup, NULL );
            Gain = Cec_TranGain( p, pClean );
            if ( Gain <= 0 )
            {
                Gia_ManStop( pDup );
                Gia_ManStop( pClean );
                pDup = pClean = NULL;
                continue;
            }
            nTried++;
            nAttempts++;
            clk = Abc_Clock();
            fCommitted = Cec_TranProveWhole( p, pDup, &OdcPars, &Prof );
            TimeProof += Abc_Clock() - clk;
            if ( !fCommitted )
            {
                nRejected++;
                Gia_ManStop( pDup );
                Gia_ManStop( pClean );
                pDup = pClean = NULL;
                continue;
            }
            fCommittedBuild = Frontier.pArray[i].nProofKind == CEC_TRAN_CAND_CONSTR;
            nGain += Gain;
            nCommits++;
            break;
        }
        nLimitHits += !fCommitted && OdcPars.nOdcProofMax &&
            nTried >= OdcPars.nOdcProofMax && nTried < Frontier.nSize;
        TimeProofAll += TimeProof;
        Cec_TranSigGuideStop( pSigGuide, iRound + 1, OdcPars.fVerbose );

        Cec_TranCandVecStop( &Known );
        Cec_TranCandVecStop( &RootCands );
        Cec_TranCandVecStop( &Candidates );
        Cec_TranCandVecStop( &Frontier );
        if ( fConstHelpers ) Cec_TranConstHelperPrint(&Prof,iRound);
        Cec_TranCandVecStop( &ConstHelpers );
        Vec_IntFree( vMffc );
        Vec_IntFree( vSupport );
        Vec_IntFree( vOne );
        ABC_FREE( pMffc );
        ABC_FREE( pSolved );
        ABC_FREE( pCovered );
        ABC_FREE( pUsed );
        ABC_FREE( pSampleStrict );
        ABC_FREE( pRoots );
        ABC_FREE( pCursors );
        if ( !fCommitted )
        {
            ABC_FREE( p->pRefs );
            CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root ODC %s round: schema=1 round=%d generated=%d positive=%d attempted=%d result=no-commit limit-hit=%s.\n",
                OdcPars.fOdcFanout ? "fanout" : "serial", iRound + 1, nGeneratedRound, nPositiveRound, nTried,
                OdcPars.nOdcProofMax && nTried >= OdcPars.nOdcProofMax ?
                    "yes" : "no" );
            break;
        }
        if ( pDup )
            Gia_ManStop( pDup );
        Gia_ManStop( p );
        p = pClean;
        if ( !OdcPars.fOdcFanout )
            Cec_TranPrintOdcCommitProfile( iRound, nBefore, Gia_ManAndNum(p),
                fCommittedBuild,
                OdcPars.fProfile, OdcPars.fVerbose );
    }
    if ( OdcPars.fOdcFanout )
        CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root ODC fanout summary: schema=1 care=%s round-cap=%d round-cap-hit=%s generated=%lld positive=%lld attempted=%lld obligations=%lld proved-candidates=%lld selected=%lld batches=%lld gain=%lld AND=%d->%d proof-sec=%.6f total-sec=%.6f.\n",
            fUseCare ? "first-level" : "full-control", OdcPars.nOdcFanoutRounds,
            OdcPars.nOdcFanoutRounds && iRound == OdcPars.nOdcFanoutRounds ? "yes" : "no",
            nGenerated, nPositive, nAttempts, nObligations, nProved, nCommits,
            nBatches, nGain, nInitial, Gia_ManAndNum(p),
            Cec_TranTimeSec(TimeProofAll), Cec_TranTimeSec(Abc_Clock() - TimeAll) );
    else CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root ODC serial summary: schema=1 policy=single-current-machine-reprove care=%s generated=%lld positive=%lld sampled-strict-compatible=%lld attempted=%lld rejected-or-unknown=%lld commits=%lld gain=%lld proof-limit-hits=%lld AND=%d->%d proof-sec=%.6f total-sec=%.6f.\n",
        fUseCare ? "first-level-immediate-fanout" : "full-control",
        nGenerated, nPositive, nSampleStrict, nAttempts, nRejected,
        nCommits, nGain, nLimitHits, nInitial, Gia_ManAndNum(p),
        Cec_TranTimeSec(TimeProofAll), Cec_TranTimeSec(Abc_Clock() - TimeAll) );
    if ( OdcPars.fWindowCache ) Abc_ResubProblemCacheStop(pPars->fVerbose);
    Abc_ResubSetCarePairTruth(SavedCarePairTruth);
    s_CexPackDefault = SavedPackDefault;
    return p;
}
