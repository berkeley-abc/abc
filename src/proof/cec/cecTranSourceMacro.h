// Experimental single source-macro supplier.  Included after cecTranTfo.h.
// A macro is a <=2-AND source cone cut at the immutable physical Build pool.
// Its endpoint never becomes a physical divisor: emitted recipes inline it.
// Collection order, then macro/outer-gate/leaf/phase order is deterministic.
// This supplier is reached only after the unchanged native iterator exhausts.

struct Cec_TranSourceMacro_t_
{
    Gia_Man_t * pSource;
    int iRoot, nSlots, fPrepared, fNativeExhausted, fDone;
    int nNativeYield, nNativeAccepted;
    abctime timeNativeBuild;
    int fReleased, nAtomsTotal;
    long long nReservoirBytes, nSignatureBytes;
    Cec_TranProf_t * pProfile;   // owner outlives all cursors in this RootPass
    Vec_Int_t * vReservoir, * vPool, * vEndpoints;
    Cec_TranCandVec_t Atoms;
    word * pColumns;             // root, then ordered B32; current Teach domain
    word * pAtomSims;            // derived only from those physical columns
    char * pOuterUnate;          // physical then macro, input phase/output phase
    int iAtom;
    int iPairCached, iPairFirst, iPairSecond;
    long long iTemplate;
    long long nTemplates, nWords, nOuterReject, nMatches;
    long long nSetupWords;       // AND/comparison word operations, not memory reads
};

static int Cec_TranSourceMacroNewOwner()
{
    static int nOwner = 0;
    return ++nOwner;
}

static int Cec_TranSourceMacroEnabled()
{
    char const * p = getenv("ABC_STRAN_SOURCE_MACRO");
    assert( !p || !strcmp(p, "0") || !strcmp(p, "1") );
    return p && !strcmp(p, "1");
}

static int Cec_TranSourceMacroTraceEnabled()
{
    char const * p = getenv("ABC_STRAN_SOURCE_MACRO_TRACE");
    assert( !p || !strcmp(p, "0") || !strcmp(p, "1") );
    return p && !strcmp(p, "1");
}

// Experimental compatibility path; absent/zero retains the original capture
// position and the public rank+macro rejection. It does not widen the lane.
static int Cec_TranSourceMacroPreboundEnabled()
{
    char const * p = getenv("ABC_STRAN_SOURCE_MACRO_PREBOUND");
    assert( !p || !strcmp(p, "0") || !strcmp(p, "1") );
    return p && !strcmp(p, "1");
}

static int Cec_TranSourceMacroPreboundScope( Cec_ParTran_t const * pPars,
    int fOdc )
{
    return pPars->fRoute3 && pPars->fUseConstr &&
        pPars->nConstrBaseMax == 32 && !fOdc && !pPars->fOdcProofScope;
}

// TRACE-only exact observations, separate from the historical macro stream.
// Emit in both prebound modes so a new mode-zero run is an exact reference.
// Hex strings retain all 64 bits when JSON is read by a JavaScript consumer.
static void Cec_TranSourceMacroTraceReservoir( Cec_TranSourceMacro_t const * s,
    int Owner, int Phase, Vec_Int_t * vRankSurvivors, int fBoundActive )
{
    int i, iObj;
    printf("stran-source-macro-prebound {\"schema\":1,\"event\":\"reservoir\",\"source_owner\":%d,\"phase\":%d,\"root\":%d,\"reservoir\":[",
        Owner, Phase, s->iRoot);
    Vec_IntForEachEntry(s->vReservoir, iObj, i) printf("%s%d", i ? "," : "", iObj);
    // This is before top-B/rescue selection. R minus these IDs identifies
    // actual bound pruning, not merely nodes outside the final physical P.
    printf("],\"bound_active\":%d,\"rank_survivors\":[", fBoundActive);
    Vec_IntForEachEntry(vRankSurvivors, iObj, i) printf("%s%d", i ? "," : "", iObj);
    printf("]}\n");
}

static void Cec_TranSourceMacroTraceBinding( Cec_TranSourceMacro_t const * s,
    int Owner, int Phase )
{
    int i, k, iObj;
    size_t j, nColumns = (size_t)(Vec_IntSize(s->vPool) + 1) * s->nSlots;
    assert( s->fPrepared );
    printf("stran-source-macro-prebound {\"schema\":1,\"event\":\"binding\",\"source_owner\":%d,\"phase\":%d,\"root\":%d,\"slots\":%d,\"pool\":[",
        Owner, Phase, s->iRoot, s->nSlots);
    Vec_IntForEachEntry(s->vPool, iObj, i) printf("%s%d", i ? "," : "", iObj);
    printf("],\"atoms\":[");
    for ( i = 0; i < s->Atoms.nSize; i++ )
    {
        Cec_TranCand_t const * c = s->Atoms.pArray + i;
        printf("%s[%d,%d,[", i ? "," : "", Vec_IntEntry(s->vEndpoints, i), c->iOut);
        for ( k = 0; k < 2 * c->nGates; k++ ) printf("%s%d", k ? "," : "", c->Recipe[k]);
        printf("]]");
    }
    printf("],\"columns\":[");
    for ( j = 0; j < nColumns; j++ )
        printf("%s\"%016llx\"", j ? "," : "", (unsigned long long)s->pColumns[j]);
    printf("]}\n");
}

// Only the first traced source is serialized. This is the exact GIA1 object
// convention used by the frozen source observer, so the external verifier can
// reconstruct its bytes and compare the archived SHA256 without a hash library
// or a new capture pipeline in ABC. Later sources retain only their owner ID.
static void Cec_TranSourceMacroTraceGraph( Gia_Man_t * p, int Owner )
{
    Gia_Obj_t * pObj;
    int i, Type, a, b;
    assert( Owner == 1 && !Gia_ManXorNum(p) && !Gia_ManMuxNum(p) );
    printf("stran-source-macro {\"event\":\"source_graph\",\"source_owner\":%d,\"gia_header\":[%d,%d,%d,%d,%d],\"gia_objects\":[",
        Owner, Gia_ManObjNum(p), Gia_ManCiNum(p), Gia_ManCoNum(p),
        Gia_ManRegNum(p), p->nConstrs);
    Gia_ManForEachObj1(p, pObj, i)
    {
        Type = Gia_ObjIsCi(pObj) ? 1 : Gia_ObjIsCo(pObj) ? 3 : Gia_ObjIsBuf(pObj) ? 4 : 2;
        assert( Type != 2 || Gia_ObjIsAnd(pObj) );
        a = Type == 1 ? -1 : Gia_ObjFaninLit0p(p, pObj);
        b = Type == 2 ? Gia_ObjFaninLit1p(p, pObj) : -1;
        printf("%s[%d,%d,%d,%d]", i == 1 ? "" : ",", i, Type, a, b);
    }
    printf("]}\n");
}

static Cec_TranSourceMacro_t * Cec_TranSourceMacroCreate(
    Gia_Man_t * p, int iRoot, Vec_Int_t * vReservoir )
{
    Cec_TranSourceMacro_t * s = ABC_CALLOC(Cec_TranSourceMacro_t, 1);
    int i, iObj;
    s->pSource = p;
    s->iRoot = iRoot;
    s->iPairCached = -1;
    s->vReservoir = Vec_IntDup(vReservoir);
    s->nReservoirBytes = (long long)sizeof(int) * Vec_IntSize(vReservoir);
    s->vEndpoints = Vec_IntAlloc(16);
    Vec_IntForEachEntry(vReservoir, iObj, i)
        assert( iObj > 0 && iObj < iRoot &&
            (Gia_ObjIsCi(Gia_ManObj(p, iObj)) ||
             Gia_ObjIsAnd(Gia_ManObj(p, iObj))) );
    return s;
}

// These are explicit payload sizes, not allocator capacity or process RSS.
static void Cec_TranSourceMacroTrack( Cec_TranSourceMacro_t * s, Cec_TranProf_t * pProf )
{
    if ( s->pProfile ) { assert( s->pProfile == pProf ); return; }
    s->pProfile = pProf;
    pProf->nSourceMacroReservoirIds += s->nReservoirBytes / sizeof(int);
    pProf->nSourceMacroReservoirLive += s->nReservoirBytes;
    if ( pProf->nSourceMacroReservoirPeak < pProf->nSourceMacroReservoirLive )
        pProf->nSourceMacroReservoirPeak = pProf->nSourceMacroReservoirLive;
    pProf->nSourceMacroSignatureBytes += s->nSignatureBytes;
    pProf->nSourceMacroSignatureLive += s->nSignatureBytes;
    if ( pProf->nSourceMacroSignaturePeak < pProf->nSourceMacroSignatureLive )
        pProf->nSourceMacroSignaturePeak = pProf->nSourceMacroSignatureLive;
}

// Terminal-only release keeps native diagnostics and scalar cursor/cost fields.
// A legacy q-limited page is not terminal: it may continue on a later wave.
static void Cec_TranSourceMacroReleasePayload( Cec_TranSourceMacro_t * s )
{
    if ( !s || s->fReleased ) return;
    if ( s->pProfile )
    {
        s->pProfile->nSourceMacroReservoirLive -= s->nReservoirBytes;
        s->pProfile->nSourceMacroSignatureLive -= s->nSignatureBytes;
        assert( s->pProfile->nSourceMacroReservoirLive >= 0 &&
            s->pProfile->nSourceMacroSignatureLive >= 0 );
    }
    s->nReservoirBytes = s->nSignatureBytes = 0;
    Vec_IntFreeP(&s->vReservoir);
    Vec_IntFreeP(&s->vPool);
    Vec_IntFreeP(&s->vEndpoints);
    Cec_TranCandVecStop(&s->Atoms);
    ABC_FREE(s->pColumns);
    ABC_FREE(s->pAtomSims);
    ABC_FREE(s->pOuterUnate);
    s->fReleased = 1;
}

static void Cec_TranSourceMacroStop( Cec_TranSourceMacro_t * s )
{
    if ( !s ) return;
    Cec_TranSourceMacroReleasePayload(s);
    ABC_FREE(s);
}

// -1 is the invalid sentinel (never a recipe literal). Count before recursing
// so an uncovered/deep cone is bounded work; shared completed gates count once.
// BUF cones are outside this first prototype's declared plain-AND grammar.
static int Cec_TranSourceMacroExpand( Cec_TranSourceMacro_t * s,
    int iObj, int * pSeen, int * pNodes, int * pRecipe, int * pnGates )
{
    Gia_Obj_t * pObj;
    int i, a, b;
    if ( !iObj || Vec_IntFind(s->vPool, iObj) >= 0 )
        return Abc_Var2Lit(iObj, 0);
    assert( iObj > 0 && iObj < s->iRoot );
    for ( i = 0; i < *pnGates; i++ )
        if ( pNodes[i] == iObj ) return Cec_TranRecipeGateCode(i, 0);
    pObj = Gia_ManObj(s->pSource, iObj);
    if ( !Gia_ObjIsAnd(pObj) || Gia_ObjIsBuf(pObj) || Gia_ObjIsXor(pObj) ||
         Gia_ObjIsMuxId(s->pSource, iObj) || ++*pSeen > 2 )
        return -1;
    a = Cec_TranSourceMacroExpand(s, Gia_ObjFaninId0p(s->pSource, pObj),
        pSeen, pNodes, pRecipe, pnGates);
    if ( a == -1 ) return -1;
    b = Cec_TranSourceMacroExpand(s, Gia_ObjFaninId1p(s->pSource, pObj),
        pSeen, pNodes, pRecipe, pnGates);
    if ( b == -1 ) return -1;
    if ( Gia_ObjFaninC0(pObj) ) a = Cec_TranRecipeNotCode(a);
    if ( Gia_ObjFaninC1(pObj) ) b = Cec_TranRecipeNotCode(b);
    assert( *pnGates < 2 );
    pNodes[*pnGates] = iObj;
    pRecipe[2 * *pnGates] = a;
    pRecipe[2 * *pnGates + 1] = b;
    return Cec_TranRecipeGateCode((*pnGates)++, 0);
}

static word Cec_TranSourceMacroWord( Cec_TranSourceMacro_t * s,
    int Code, word * pGates, int Slot )
{
    int i;
    word Value;
    if ( Cec_TranRecipeCodeIsGate(Code) )
    {
        i = Cec_TranRecipeGateLit(Code);
        Value = pGates[Abc_Lit2Var(i)];
        return Abc_LitIsCompl(i) ? ~Value : Value;
    }
    if ( Abc_Lit2Var(Code) == 0 ) return Code ? ~(word)0 : 0;
    i = Vec_IntFind(s->vPool, Abc_Lit2Var(Code));
    assert( i >= 0 );
    Value = s->pColumns[(size_t)(i + 1) * s->nSlots + Slot];
    return Abc_LitIsCompl(Code) ? ~Value : Value;
}

static void Cec_TranSourceMacroPrepare( Cec_TranSourceMacro_t * s,
    Cec_TranSim_t * pSim, Vec_Int_t * vPool )
{
    Cec_TranCand_t Cand;
    int i, j, k, iObj, Seen, Nodes[2], Recipe[4], nGates, Out, Phase, OutPhase;
    word Gates[2], Value, Target;
    assert( !s->fReleased );
    assert( pSim->pGia == s->pSource && pSim->nSlots > 0 && Vec_IntSize(vPool) <= 32 );
    if ( s->fPrepared )
    {
        assert( s->nSlots == pSim->nSlots &&
            Vec_IntSize(vPool) == Vec_IntSize(s->vPool) );
        for ( i = -1; i < Vec_IntSize(vPool); i++ )
        {
            iObj = i < 0 ? s->iRoot : Vec_IntEntry(vPool, i);
            assert( i < 0 || iObj == Vec_IntEntry(s->vPool, i) );
            assert( !memcmp(s->pColumns + (size_t)(i + 1) * s->nSlots,
                Cec_TranSimObj(pSim, iObj), sizeof(word) * s->nSlots) );
        }
        return;
    }
    s->vPool = Vec_IntDup(vPool);
    s->nSlots = pSim->nSlots;
    s->pColumns = ABC_ALLOC(word, (size_t)(Vec_IntSize(vPool) + 1) * s->nSlots);
    for ( i = -1; i < Vec_IntSize(vPool); i++ )
    {
        iObj = i < 0 ? s->iRoot : Vec_IntEntry(vPool, i);
        assert( i < 0 || (iObj > 0 && iObj < s->iRoot &&
            Vec_IntFind(s->vReservoir, iObj) >= 0) );
        memcpy(s->pColumns + (size_t)(i + 1) * s->nSlots,
            Cec_TranSimObj(pSim, iObj), sizeof(word) * s->nSlots);
    }
    Vec_IntForEachEntry(s->vReservoir, iObj, i)
    {
        if ( Vec_IntFind(vPool, iObj) >= 0 ) continue;
        Seen = nGates = 0;
        Out = Cec_TranSourceMacroExpand(s, iObj, &Seen, Nodes, Recipe, &nGates);
        if ( Out == -1 || !nGates ) continue;
        memset(&Cand, 0, sizeof(Cand));
        Cand.iTarget = s->iRoot;
        Cand.nKind = CEC_TRAN_CAND_CONSTR;
        Cand.fStrict = 1;
        Cand.nGates = nGates;
        Cand.Recipe = Cec_TranRecipeAlloc(2 * nGates);
        memcpy(Cand.Recipe, Recipe, sizeof(int) * 2 * nGates);
        Cand.iOut = Out;
        Cec_TranCandCanonicalizeRecipe(&Cand);
        if ( Cand.nGates )
        {
            // Both phases are enumerated, so store one representative modulo
            // output complement. This is structural equality, not a signature.
            if ( (Cec_TranRecipeGateLit(Cand.iOut) & 1) )
                Cand.iOut = Cec_TranRecipeNotCode(Cand.iOut);
            if ( !Cec_TranCandVecContains(&s->Atoms, &Cand) )
            {
                Vec_IntPush(s->vEndpoints, iObj);
                Cec_TranCandVecPush(&s->Atoms, Cand);
            }
        }
        Cec_TranCandRecipeRelease(&Cand);
    }
    s->pAtomSims = ABC_ALLOC(word, (size_t)s->Atoms.nSize * s->nSlots);
    s->nAtomsTotal = s->Atoms.nSize;
    for ( i = 0; i < s->Atoms.nSize; i++ )
        for ( j = 0; j < s->nSlots; j++ )
        {
            Cec_TranCand_t const * a = s->Atoms.pArray + i;
            for ( k = 0; k < a->nGates; k++ )
            {
                Value = Cec_TranSourceMacroWord(s, a->Recipe[2*k], Gates, j);
                Gates[k] = Value & Cec_TranSourceMacroWord(s, a->Recipe[2*k+1], Gates, j);
                s->nSetupWords++;
            }
            s->pAtomSims[(size_t)i * s->nSlots + j] =
                Cec_TranSourceMacroWord(s, a->iOut, Gates, j);
        }
    // Full-column necessary conditions are computed once, not per template.
    // For (inner & outer)^OutPhase == root, root^OutPhase implies outer.
    s->pOuterUnate = ABC_CALLOC(char, 4 * (Vec_IntSize(vPool) + s->Atoms.nSize));
    for ( i = 0; i < Vec_IntSize(vPool) + s->Atoms.nSize; i++ )
        for ( Phase = 0; Phase < 2; Phase++ )
            for ( OutPhase = 0; OutPhase < 2; OutPhase++ )
            {
                for ( j = 0; j < s->nSlots; j++ )
                {
                    Value = i < Vec_IntSize(vPool) ?
                        s->pColumns[(size_t)(i + 1) * s->nSlots + j] :
                        s->pAtomSims[(size_t)(i - Vec_IntSize(vPool)) * s->nSlots + j];
                    if ( Phase ) Value = ~Value;
                    Target = OutPhase ? ~s->pColumns[j] : s->pColumns[j];
                    s->nSetupWords++;
                    if ( Target & ~Value ) break;
                }
                s->pOuterUnate[4*i + 2*Phase + OutPhase] = j == s->nSlots;
            }
    s->nSignatureBytes = (long long)sizeof(word) * s->nSlots *
        (1 + Vec_IntSize(vPool) + s->Atoms.nSize) + 4LL * (Vec_IntSize(vPool) + s->Atoms.nSize);
    if ( s->pProfile )
    {
        s->pProfile->nSourceMacroSignatureBytes += s->nSignatureBytes;
        s->pProfile->nSourceMacroSignatureLive += s->nSignatureBytes;
        if ( s->pProfile->nSourceMacroSignaturePeak < s->pProfile->nSourceMacroSignatureLive )
            s->pProfile->nSourceMacroSignaturePeak = s->pProfile->nSourceMacroSignatureLive;
    }
    s->fPrepared = 1;
}

// Exactly one macro occurrence, with zero, one, or two distinct physical
// leaves. AIG phases cover AND/OR trees without duplicate operator encodings:
// 2 + 8*B + 96*C(B,2) templates per atom. No template is materialized ahead.
static int Cec_TranSourceMacroNext( Cec_TranSourceMacro_t * s,
    Cec_TranSim_t * pSim, Cec_TranRoot_t const * pRoot, Cec_TranCand_t * pCand )
{
    int B, nOuter, a, b, Pair, Phase, InnerNot, OutNot;
    int Codes[3], Inner0, Inner1, Outer, Slot, i, nGates, Recipe[8], Out, OuterIndex;
    long long nPerAtom, Index;
    word Values[3], Result;
    Cec_TranCand_t const * Atom;
    assert( !s->fReleased );
    B = Vec_IntSize(s->vPool);
    nPerAtom = 2 + 8 * B + 48LL * B * (B - 1);
    assert( s->fPrepared && pRoot->iObj == s->iRoot && pSim->pGia == s->pSource );
    while ( s->iAtom < s->Atoms.nSize )
    {
        if ( s->iTemplate == nPerAtom )
        {
            s->iTemplate = 0;
            s->iAtom++;
            continue;
        }
        Index = s->iTemplate++;
        s->nTemplates++;
        a = b = Pair = InnerNot = OutNot = 0;
        if ( Index < 2 ) { nOuter = 0; Phase = (int)Index; }
        else if ( (Index -= 2) < 8 * B )
        {
            nOuter = 1; a = (int)(Index / 8);
            Phase = (int)Index & 3; OutNot = ((int)Index >> 2) & 1;
        }
        else
        {
            nOuter = 2; Index -= 8 * B;
            Phase = (int)Index & 7; InnerNot = ((int)Index >> 3) & 1;
            OutNot = ((int)Index >> 4) & 1; Index /= 32;
            Pair = (int)(Index % 3); Index /= 3;
            if ( s->iPairCached != (int)Index )
            {
                s->iPairCached = (int)Index;
                for ( a = 0; Index >= B - a - 1; a++ ) Index -= B - a - 1;
                s->iPairFirst = a;
                s->iPairSecond = a + 1 + (int)Index;
            }
            a = s->iPairFirst; b = s->iPairSecond;
            assert( a < b && b < B );
        }
        // Pair chooses the outer input. Pair 0 puts the macro outside; 1/2
        // put one physical leaf outside. Necessary unateness rejects early.
        Outer = nOuter == 2 ? Pair : 1;
        Inner0 = Outer == 0 ? 1 : 0;
        Inner1 = Outer == 2 ? 1 : 2;
        OuterIndex = Outer == 0 ? B + s->iAtom : Outer == 1 ? a : b;
        if ( nOuter && !s->pOuterUnate[4*OuterIndex + 2*((Phase >> Outer) & 1) + OutNot] )
        {
            s->nOuterReject++;
            continue;
        }
        for ( Slot = 0; Slot < s->nSlots; Slot++ )
        {
            s->nWords++;
            Values[0] = s->pAtomSims[(size_t)s->iAtom * s->nSlots + Slot];
            if ( Phase & 1 ) Values[0] = ~Values[0];
            if ( !nOuter ) Result = Values[0];
            else
            {
                Values[1] = s->pColumns[(size_t)(a + 1) * s->nSlots + Slot];
                if ( Phase & 2 ) Values[1] = ~Values[1];
                if ( nOuter == 2 )
                {
                    Values[2] = s->pColumns[(size_t)(b + 1) * s->nSlots + Slot];
                    if ( Phase & 4 ) Values[2] = ~Values[2];
                }
                if ( nOuter == 1 ) Result = Values[0] & Values[1];
                else
                {
                    Result = Values[Inner0] & Values[Inner1];
                    if ( InnerNot ) Result = ~Result;
                    Result &= Values[Outer];
                }
                if ( OutNot ) Result = ~Result;
            }
            if ( Result != s->pColumns[Slot] ) break;
        }
        if ( Slot < s->nSlots ) continue;
        s->nMatches++;
        Atom = s->Atoms.pArray + s->iAtom;
        nGates = Atom->nGates;
        memcpy(Recipe, Atom->Recipe, sizeof(int) * 2 * nGates);
        Codes[0] = Phase & 1 ? Cec_TranRecipeNotCode(Atom->iOut) : Atom->iOut;
        if ( nOuter ) Codes[1] = Abc_Var2Lit(Vec_IntEntry(s->vPool, a), (Phase >> 1) & 1);
        if ( nOuter == 2 ) Codes[2] = Abc_Var2Lit(Vec_IntEntry(s->vPool, b), (Phase >> 2) & 1);
        Out = Codes[0];
        if ( nOuter )
        {
            Recipe[2*nGates] = nOuter == 1 ? Codes[0] : Codes[Inner0];
            Recipe[2*nGates+1] = nOuter == 1 ? Codes[1] : Codes[Inner1];
            Out = Cec_TranRecipeGateCode(nGates++, nOuter == 2 ? InnerNot : 0);
            if ( nOuter == 2 )
            {
                Recipe[2*nGates] = Out;
                Recipe[2*nGates+1] = Codes[Outer];
                Out = Cec_TranRecipeGateCode(nGates++, 0);
            }
            if ( OutNot ) Out = Cec_TranRecipeNotCode(Out);
        }
        memset(pCand, 0, sizeof(*pCand));
        pCand->iTarget = s->iRoot;
        pCand->nMffc = pRoot->nMffc;
        pCand->fStrict = pCand->fExactTemplate = 1;
        pCand->nKind = CEC_TRAN_CAND_CONSTR;
        pCand->nGates = nGates;
        pCand->iOut = Out;
        pCand->Recipe = Cec_TranRecipeAlloc(2 * nGates);
        memcpy(pCand->Recipe, Recipe, sizeof(int) * 2 * nGates);
        Cec_TranCandCanonicalizeRecipe(pCand);
        assert( Cec_TranRecipeStructurallyValid(pSim, pCand) &&
            Cec_TranRecipeMatchesRoot(pSim, pCand, NULL) );
        pCand->iDiv0 = pCand->iDiv1 = -1;
        for ( i = -1; i < 2 * pCand->nGates; i++ )
        {
            int Code = i < 0 ? pCand->iOut : pCand->Recipe[i];
            if ( Cec_TranRecipeCodeIsGate(Code) || Abc_Lit2Var(Code) == 0 ) continue;
            if ( pCand->iDiv0 == -1 ) pCand->iDiv0 = Code;
            else if ( Abc_Lit2Var(pCand->iDiv0) != Abc_Lit2Var(Code) )
            { pCand->iDiv1 = Code; break; }
        }
        return 1;
    }
    s->fDone = 1;
    return 0;
}
