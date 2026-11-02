// Shared combinational and sequential candidate proof.
// Private implementation fragment included only by cecTrans.c.

// The correspondence SRM can place constants, ROs, and internal ANDs into
// speculative classes, but a free PI cannot be a class node: unlike an RO it
// has no frame-to-frame definition for Gia_ManCorrSpecReal().  Preserve useful
// root=PI candidates by representing each PI literal with one unstrashed
// ordinary AND proxy (x&1=x) in this temporary proof network.  Sharing by PI
// phase avoids duplicate wrappers.  Endpoint keepalive COs retain these
// proxies in correspondence modes; a query-only miter need not retain them.
static int Cec_TranRootClassEndpoint( Gia_Man_t * pNew, int iLit,
    int nPis, int * pPiProxies )
{
    Gia_Obj_t * pObj = Gia_ManObj( pNew, Abc_Lit2Var(iLit) );
    int iIndex;
    // Raw x&1 proxies are deliberately not structural-hash entries.  All
    // hash-built source, recipe and query nodes must precede this phase.
    assert( Vec_IntSize(&pNew->vHTable) == 0 );
    if ( !Gia_ObjIsCi(pObj) || Gia_ObjCioId(pObj) >= nPis )
        return iLit;
    iIndex = 2 * Gia_ObjCioId(pObj) + Abc_LitIsCompl(iLit);
    if ( pPiProxies[iIndex] == -1 )
        pPiProxies[iIndex] = Gia_ManAppendAnd( pNew, iLit, 1 );
    return pPiProxies[iIndex];
}

// CO offsets and indices share GIA's 29-bit representation.  Check this local
// proof-graph boundary before AppendCo can truncate a difference or index.
static void Cec_TranRootAppendCo( Gia_Man_t * p, int iLit )
{
    int iObj = Gia_ManObjNum(p), iDriver = Abc_Lit2Var(iLit);
    assert( iLit >= 0 && iDriver < iObj );
    assert( iObj <= INT_MAX / 2 );
    assert( (unsigned)(iObj - iDriver) < GIA_NONE );
    assert( (unsigned)Gia_ManCoNum(p) < GIA_NONE );
    Gia_ManAppendCo( p, iLit );
}

// Build one signal-correspondence instance for a group of strict Direct
// candidates.  The source transition relation is copied only once.  Candidate
// endpoint pairs seed speculative equivalence classes.  Root-XOR-replacement
// POs are built only by the separate bounded reachable-CEX harvesting miter;
// correspondence status itself is read directly from the refined classes.
typedef struct Cec_TranRootBatchSize_t_ {
    int CopyObjs, CopyAnds, HelperBuild, TargetBuild;
    int HelperAnds, BuildAnds, DirectAnds, QueryAnds, ProxyAnds;
    int RawObjs, RawAnds;
} Cec_TranRootBatchSize_t;

// Optional accounting measures actual appended hash nodes, not recipe length.
// Cleanup can discard copied source cones, so raw additions and final graph
// size are separate quantities and must not be subtracted from one another.
static Gia_Man_t * Cec_TranBuildRootBatchMeasured( Gia_Man_t * p,
    Cec_TranCand_t const * pHelpers, int nHelpers,
    Cec_TranCand_t const * pCands, int nCands,
    int fCreateQueries,
    Vec_Int_t ** pvPairs, Vec_Int_t ** pvCombPairs, Vec_Int_t ** pvQueries,
    Vec_Int_t ** pvAndLeaves, Vec_Str_t ** pvAndCounts,
    Cec_TranRootBatchSize_t * pSize )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    int nRelations;
    Vec_Int_t * vPairs, * vCombPairs, * vQueries, * vAndLeaves;
    Vec_Str_t * vAndCounts;
    Vec_Bit_t * vKept;
    int nPis = Gia_ManPiNum(p);
    int * pPiProxies;
    int Gates[CEC_TRAN_RECIPE_NODES_MAX];
    int Leaves[2 * CEC_TRAN_RECIPE_NODES_MAX + 1];
    int i, k, nLeaves, iLit0, iLit1, iRoot, iRep, iQuery;
    if ( pSize ) memset( pSize, 0, sizeof(*pSize) );
    assert( nHelpers >= 0 && nCands > 0 );
    assert( (int64_t)nHelpers + nCands <= INT_MAX / 2 );
    assert( nPis <= INT_MAX / 2 );
    assert( fCreateQueries >= 0 && fCreateQueries <= 2 );
    assert( (pvAndLeaves != NULL) == (pvAndCounts != NULL) );
    nRelations = nHelpers + nCands;
    vPairs = Vec_IntAlloc( 2 * nRelations );
    vCombPairs = Vec_IntAlloc( 2 * nCands );
    vQueries = Vec_IntAlloc( nCands );
    vAndLeaves = pvAndLeaves ? Vec_IntAlloc( 2 * nCands ) : NULL;
    vAndCounts = pvAndCounts ? Vec_StrAlloc( nCands ) : NULL;
    pPiProxies = nPis ? ABC_FALLOC( int, 2 * nPis ) : NULL;
    Gia_ManFillValue( p );
    // Relations can share every physical recipe/endpoint.  Their count is
    // not a graph-capacity estimate; let normal GIA growth handle new nodes.
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( "stran_direct_root_batch" );
    Gia_ManHashAlloc( pNew );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachAnd( p, pObj, i )
    {
        iLit0 = Gia_ObjFanin0Copy( pObj );
        iLit1 = Gia_ObjFanin1Copy( pObj );
        pObj->Value = Cec_TranHashGate( pNew, pObj, iLit0, iLit1 );
    }
    if ( pSize )
        pSize->CopyObjs = Gia_ManObjNum(pNew),
        pSize->CopyAnds = Gia_ManAndNum(pNew);
    for ( i = 0; i < nRelations; i++ )
    {
        Cec_TranCand_t const * pCand = i < nHelpers ?
            pHelpers + i : pCands + i - nHelpers;
        int fObligation = i >= nHelpers;
        int nAndsBefore = pSize ? Gia_ManAndNum(pNew) : 0;
        iRoot = Cec_TranCopyLit( p, Abc_Var2Lit(pCand->iTarget, 0) );
        iRep = Cec_TranRecipeBuildMapped( p, pNew, pCand, Gates );
        if ( pSize )
        {
            int nAdded = Gia_ManAndNum(pNew) - nAndsBefore;
            if ( !fObligation )
                pSize->HelperAnds += nAdded,
                pSize->HelperBuild += pCand->nKind == CEC_TRAN_CAND_CONSTR;
            else if ( pCand->nKind == CEC_TRAN_CAND_CONSTR )
                pSize->BuildAnds += nAdded, pSize->TargetBuild++;
            else
                pSize->DirectAnds += nAdded;
        }
        if ( fObligation )
            Vec_IntPushTwo( vCombPairs, iRoot, iRep );
        if ( fObligation && vAndCounts )
        {
            nLeaves = Cec_TranRecipeCollectAndLeaves( pCand, Leaves );
            assert( nLeaves <= 2 * CEC_TRAN_RECIPE_NODES_MAX + 1 );
            for ( k = 0; k < nLeaves; k++ )
                Vec_IntPush( vAndLeaves, Cec_TranRecipeCopyCode(
                    p, Leaves[k], Gates, pCand->nGates) );
            Vec_StrPush( vAndCounts, (char)nLeaves );
        }
        // Build ordinary CBS/BMC queries from the real recipe endpoint.  A PI
        // proxy is only a correspondence-class representation; exposing its
        // unstrashed x&1 gate to CBS would make the solver visit constant
        // fanins, which are not CBS candidate variables.
        if ( fObligation && fCreateQueries )
        {
            nAndsBefore = pSize ? Gia_ManAndNum(pNew) : 0;
            iQuery = Gia_ManHashXor( pNew, iRoot, iRep );
            if ( pSize ) pSize->QueryAnds += Gia_ManAndNum(pNew) - nAndsBefore;
            Vec_IntPush( vQueries, iQuery );
        }
        Vec_IntPushTwo( vPairs, iRoot, iRep );
    }
    // Finish the complete hashed graph before appending raw PI proxies.
    // Otherwise a later unique recipe can resize the structural hash, whose
    // AND count includes those unregistered proxies.  Comb pairs, query
    // literals and recipe leaves retain their original physical endpoints.
    Gia_ManHashStop( pNew );
    if ( pSize ) pSize->ProxyAnds = Gia_ManAndNum(pNew);
    for ( i = 1; i < Vec_IntSize(vPairs); i += 2 )
        Vec_IntWriteEntry( vPairs, i, Cec_TranRootClassEndpoint( pNew,
            Vec_IntEntry(vPairs, i), nPis, pPiProxies ) );
    if ( pSize ) pSize->ProxyAnds = Gia_ManAndNum(pNew) - pSize->ProxyAnds;
    Vec_IntForEachEntry( vQueries, iQuery, i )
        Cec_TranRootAppendCo( pNew, iQuery );
    // Endpoint COs only keep seeded class members alive through cleanup.  A
    // normal correspondence closure reads status from representatives and
    // needs no XOR property at all; the separate reachable-CEX miter requests
    // XOR queries and retains candidate endpoints through those queries.
    // Mode 2 is the ordinary-CBS A/B path: keep the class endpoints as well
    // as the XOR queries because the same graph continues into scorr.  Mode 1
    // is the standalone reachable-CEX miter and must expose only query POs.
    // A CO retains its physical driver in either phase.  Preserve the first
    // occurrence of each driver, without changing any relation or query.
    // Phase-specific PI proxies remain distinct physical drivers.
    vKept = fCreateQueries != 1 ? Vec_BitStart(Gia_ManObjNum(pNew)) : NULL;
    for ( i = 0; fCreateQueries != 1 && i < Vec_IntSize(vPairs); i++ )
    {
        int iLit = Vec_IntEntry(vPairs, i), iDriver = Abc_Lit2Var(iLit);
        if ( Vec_BitEntry(vKept, iDriver) )
            continue;
        Vec_BitWriteEntry( vKept, iDriver, 1 );
        Cec_TranRootAppendCo( pNew, iLit );
    }
    Vec_BitFreeP( &vKept );
    Gia_ManForEachRi( p, pObj, i )
        Cec_TranRootAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    if ( pSize )
        pSize->RawObjs = Gia_ManObjNum(pNew),
        pSize->RawAnds = Gia_ManAndNum(pNew);
    // Original POs are intentionally omitted, so remove their now-dangling
    // cones before Cec's reference-counted simulator is started.  Query POs
    // and every RI remain roots; remap the saved query literals through the
    // cleanup copy left in pTemp->Value.
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManDupRemapLiterals( vPairs, pTemp );
    Gia_ManDupRemapLiterals( vCombPairs, pTemp );
    Gia_ManDupRemapLiterals( vQueries, pTemp );
    if ( vAndLeaves )
        Gia_ManDupRemapLiterals( vAndLeaves, pTemp );
    Gia_ManStop( pTemp );
    ABC_FREE( pPiProxies );

    *pvPairs = vPairs;
    *pvCombPairs = vCombPairs;
    *pvQueries = vQueries;
    if ( pvAndLeaves )
        *pvAndLeaves = vAndLeaves;
    if ( pvAndCounts )
        *pvAndCounts = vAndCounts;
    return pNew;
}

static int Cec_TranRootLitPhase( Gia_Man_t * p, int iLit )
{
    return Gia_ObjPhase(Gia_ManObj(p, Abc_Lit2Var(iLit))) ^
        Abc_LitIsCompl(iLit);
}

static int Cec_TranRootUfFind( int * pParent, int iObj )
{
    int iRoot = iObj;
    while ( pParent[iRoot] != iRoot )
        iRoot = pParent[iRoot];
    while ( pParent[iObj] != iObj )
    {
        int iNext = pParent[iObj];
        pParent[iObj] = iRoot;
        iObj = iNext;
    }
    return iRoot;
}

// Seed the transitive closure of candidate endpoint relations.  For example,
// a=b and a=c enter correspondence as one speculative class {a,b,c}; a CEX
// can split c without discarding a=b.  The smallest object ID is the class
// head, as required by Gia representatives.
static void Cec_TranSeedRootClasses( Gia_Man_t * p, Vec_Int_t * vPairs )
{
    int * pParent = ABC_ALLOC( int, Gia_ManObjNum(p) );
    int i, iLit0, iLit1, iObj0, iObj1, iRoot0, iRoot1;
    for ( i = 0; i < Gia_ManObjNum(p); i++ )
        pParent[i] = i;
    for ( i = 0; i < Vec_IntSize(vPairs); i += 2 )
    {
        iLit0 = Vec_IntEntry( vPairs, i );
        iLit1 = Vec_IntEntry( vPairs, i + 1 );
        if ( Cec_TranRootLitPhase(p, iLit0) !=
             Cec_TranRootLitPhase(p, iLit1) )
            continue;
        iObj0 = Abc_Lit2Var( iLit0 );
        iObj1 = Abc_Lit2Var( iLit1 );
        iRoot0 = Cec_TranRootUfFind( pParent, iObj0 );
        iRoot1 = Cec_TranRootUfFind( pParent, iObj1 );
        if ( iRoot0 == iRoot1 )
            continue;
        if ( iRoot0 < iRoot1 )
            pParent[iRoot1] = iRoot0;
        else
            pParent[iRoot0] = iRoot1;
    }
    for ( i = 1; i < Gia_ManObjNum(p); i++ )
    {
        iRoot0 = Cec_TranRootUfFind( pParent, i );
        if ( iRoot0 != i )
            Gia_ObjSetRepr( p, i, iRoot0 );
    }
    ABC_FREE( pParent );
}

static int Cec_TranRootBatchPairProved( Gia_Man_t * p,
    int iLit0, int iLit1 )
{
    int iObj0 = Abc_Lit2Var( iLit0 );
    int iObj1 = Abc_Lit2Var( iLit1 );
    int iHead0, iHead1;
    if ( Cec_TranRootLitPhase(p, iLit0) != Cec_TranRootLitPhase(p, iLit1) )
        return 0;
    iHead0 = Gia_ObjRepr(p, iObj0) == GIA_VOID ?
        iObj0 : Gia_ObjRepr(p, iObj0);
    iHead1 = Gia_ObjRepr(p, iObj1) == GIA_VOID ?
        iObj1 : Gia_ObjRepr(p, iObj1);
    return iHead0 == iHead1;
}

// Solve one counterexample cube directly on the shared candidate graph.  CBS
// returns 1 for UNSAT, 0 for SAT, and -1 for UNKNOWN.
static int Cec_TranCombSolveCube( Cbs_Man_t * pCbs, int const * pLits,
    int nLits, int fSaveModel, Cec_TranProf_t * pProf )
{
    int Status = fSaveModel ?
        Cbs_ManSolveLits( pCbs, pLits, nLits ) :
        Cbs_ManSolveLitsNoModel( pCbs, pLits, nLits );
    pProf->nCombNoModelCalls += !fSaveModel;
    pProf->nCombConfUsed += Cbs_ManReadConflicts( pCbs );
    return Status;
}

// Correspondence represents a PI endpoint with an unstrashed x&1 proxy.
// Remove that proof-only wrapper before passing a literal to CBS.
static int Cec_TranCombUnwrapPiProxy( Gia_Man_t * pBatch, int iLit )
{
    Gia_Obj_t * pObj = Gia_ManObj( pBatch, Abc_Lit2Var(iLit) );
    int iLit0, iLit1, iReal = -1;
    if ( !Gia_ObjIsAnd(pObj) )
        return iLit;
    iLit0 = Gia_ObjFaninLit0p( pBatch, pObj );
    iLit1 = Gia_ObjFaninLit1p( pBatch, pObj );
    if ( iLit0 == 1 )
        iReal = iLit1;
    else if ( iLit1 == 1 )
        iReal = iLit0;
    return iReal == -1 ? iLit :
        Abc_LitNotCond( iReal, Abc_LitIsCompl(iLit) );
}

// Solve one explicitly constructed XOR query through CBS's ordinary
// single-root interface.  This path exists as an A/B baseline for the direct
// multi-literal interface above; both share the same manager and conflict cap.
static int Cec_TranCombSolveQuery( Cbs_Man_t * pCbs, Gia_Man_t * pBatch,
    int iQuery, int fSaveModel, Cec_TranProf_t * pProf )
{
    int Status = fSaveModel ?
        Cbs_ManSolve( pCbs, Gia_ObjFromLit(pBatch, iQuery) ) :
        Cbs_ManSolveNoModel( pCbs, Gia_ObjFromLit(pBatch, iQuery) );
    pProf->nCombNoModelCalls += !fSaveModel;
    pProf->nCombConfUsed += Cbs_ManReadConflicts( pCbs );
    return Status;
}

// Candidate-directed combinational equivalence.  Registers are treated as
// independent CIs, so every UNSAT result is valid in all states.  A generic
// a=h relation is two implication counterexample cubes.  If h is a recipe
// AND/NAND cone, flatten only that recipe cone into one short cube per leaf
// plus one long cube; the first SAT cube terminates the candidate immediately.
static Vec_Str_t * Cec_TranProveCombBatch( Gia_Man_t * pBatch,
    Cec_TranCand_t const * pCands, int nCands, Vec_Int_t * vPairs,
    Vec_Int_t * vQueries, Vec_Int_t * vAndLeaves, Vec_Str_t * vAndCounts,
    Cec_ParTran_t * pPars, Cec_TranProf_t * pProf,
    int fStopAtFirstProof, int * pnAttempted )
{
    Cbs_Man_t * pCbs = Cbs_ManAlloc( pBatch );
    Cec_TranFreeSim_t * pFree = NULL;
    Vec_Str_t * vStage = Vec_StrStart( nCands );
    int Cube[2 * CEC_TRAN_RECIPE_NODES_MAX + 2];
    int i, k, iBeg = 0, iEnd = 0, nLeaves, a, h, t;
    int Status, fSat, fUnknown, fSaveModel, FreeMismatch;
    long long nConfStart = pProf->nCombConfUsed;
    abctime clk = Abc_Clock(), timeSolve = 0, clkSolve;
    Cec_TranPreproofEvent( pProf, pBatch, "cbs", 0, nCands, 0 );
    if ( pPars->fUseFreeSim && (pPars->nFreeWords || pPars->nFreeCexMax) )
        pFree = Cec_TranFreeSimStart( pBatch, pPars->nFreeWords,
            pPars->nFreeCexMax );
    Cbs_ManSetConflictNum( pCbs, pPars->nCombBTLimit );
    assert( pPars->fUseCbsMultiLit || Vec_IntSize(vQueries) == nCands );
    if ( pnAttempted )
        *pnAttempted = 0;
    for ( i = 0; i < nCands; i++ )
    {
        if ( pnAttempted )
            (*pnAttempted)++;
        nLeaves = pPars->fUseCbsMultiLit ?
            (unsigned char)Vec_StrEntry(vAndCounts, i) : 0;
        iBeg = iEnd;
        iEnd += nLeaves;
        a = Vec_IntEntry( vPairs, 2*i );
        h = Vec_IntEntry( vPairs, 2*i + 1 );
        h = Cec_TranCombUnwrapPiProxy( pBatch, h );
        if ( a == h )
        {
            Vec_StrWriteEntry( vStage, i, 1 );
            pProf->nCombProved++;
            if ( fStopAtFirstProof )
                break;
            continue;
        }
        if ( pFree )
        {
            FreeMismatch = Cec_TranFreeSimMismatch( pFree, a, h );
            if ( FreeMismatch )
                continue;
        }
        // Model extraction is useful only while the batch CEGIS bank still
        // has room.  Once full, use the cheaper solve entry point for every
        // remaining cube/query instead of repeatedly collecting unused CIs.
        fSaveModel = pFree != NULL && pFree->nCexes < pFree->nCexMax;
        fSat = fUnknown = 0;
        if ( !pPars->fUseCbsMultiLit )
        {
            clkSolve = Abc_Clock();
            Status = Cec_TranCombSolveQuery( pCbs, pBatch,
                Vec_IntEntry(vQueries, i), fSaveModel, pProf );
            timeSolve += Abc_Clock() - clkSolve;
            if ( Status == 0 )
            {
                pProf->nCombDisproved++;
                if ( fSaveModel && pFree->nCexes < pFree->nCexMax )
                {
                    abctime clkFree = Abc_Clock();
                    if ( Cec_TranFreeSimAddModel(pFree, Cbs_ReadModel(pCbs), a, h) )
                        pProf->nCombFreeCexStored++;
                    else
                        pProf->nCombFreeCexInvalid++;
                    pProf->timeFreeCexSim += Abc_Clock() - clkFree;
                }
            }
            else if ( Status < 0 )
                pProf->nCombUnknown++;
            else
            {
                Vec_StrWriteEntry( vStage, i, 1 );
                pProf->nCombProved++;
                if ( fStopAtFirstProof )
                    break;
            }
            continue;
        }
        if ( nLeaves )
        {
            int iOutLit = Cec_TranRecipeGateLit( pCands[i].iOut );
            // If h = AND(leaves), a != h is covered by one short cube
            // a & !leaf[k] per leaf, plus one long cube !a & all(leaves).
            // For a complemented recipe output, replacing a by !a gives the
            // same cover.  Only recipe ANDs were flattened when the shared
            // proof graph was built; original divisor cones stay atomic.
            t = Abc_LitNotCond( a, Abc_LitIsCompl(iOutLit) );
            for ( k = iBeg; k < iEnd; k++ )
            {
                Cube[0] = t;
                Cube[1] = Abc_LitNot( Vec_IntEntry(vAndLeaves, k) );
                clkSolve = Abc_Clock();
                Status = Cec_TranCombSolveCube( pCbs, Cube, 2,
                    fSaveModel, pProf );
                timeSolve += Abc_Clock() - clkSolve;
                if ( Status == 0 ) { fSat = 1; break; }
                if ( Status < 0 )
                {
                    fUnknown = 1;
                    pProf->nCombUnknownEarly++;
                    pProf->nCombCubesSkippedUnknown += iEnd - k;
                    break;
                }
            }
            if ( !fSat && !fUnknown )
            {
                Cube[0] = Abc_LitNot( t );
                for ( k = 0; k < nLeaves; k++ )
                    Cube[k+1] = Vec_IntEntry( vAndLeaves, iBeg + k );
                clkSolve = Abc_Clock();
                Status = Cec_TranCombSolveCube( pCbs, Cube, nLeaves + 1,
                    fSaveModel, pProf );
                timeSolve += Abc_Clock() - clkSolve;
                if ( Status == 0 )
                    fSat = 1;
                else
                {
                    fUnknown = Status < 0;
                    pProf->nCombUnknownEarly += Status < 0;
                }
            }
        }
        else
        {
            Cube[0] = a;             Cube[1] = Abc_LitNot(h);
            clkSolve = Abc_Clock();
            Status = Cec_TranCombSolveCube( pCbs, Cube, 2,
                fSaveModel, pProf );
            timeSolve += Abc_Clock() - clkSolve;
            if ( Status == 0 )
                fSat = 1;
            else
            {
                fUnknown = Status < 0;
                if ( fUnknown )
                {
                    pProf->nCombUnknownEarly++;
                    pProf->nCombCubesSkippedUnknown++;
                }
            }
            if ( !fSat && !fUnknown )
            {
                Cube[0] = Abc_LitNot(a); Cube[1] = h;
                clkSolve = Abc_Clock();
                Status = Cec_TranCombSolveCube( pCbs, Cube, 2,
                    fSaveModel, pProf );
                timeSolve += Abc_Clock() - clkSolve;
                if ( Status == 0 )
                    fSat = 1;
                else
                {
                    fUnknown = Status < 0;
                    pProf->nCombUnknownEarly += Status < 0;
                }
            }
        }
        if ( fSat )
        {
            pProf->nCombDisproved++;
            if ( fSaveModel && pFree->nCexes < pFree->nCexMax )
            {
                abctime clkFree = Abc_Clock();
                if ( Cec_TranFreeSimAddModel(pFree, Cbs_ReadModel(pCbs), a, h) )
                    pProf->nCombFreeCexStored++;
                else
                    pProf->nCombFreeCexInvalid++;
                pProf->timeFreeCexSim += Abc_Clock() - clkFree;
            }
        }
        else if ( fUnknown )
            pProf->nCombUnknown++;
        else
        {
            Vec_StrWriteEntry( vStage, i, 1 );
            pProf->nCombProved++;
            if ( fStopAtFirstProof )
                break;
        }
    }
    pProf->timeCombSolve += timeSolve;
    pProf->timeRootCbsScreen += Abc_Clock() - clk - timeSolve;
    Cec_TranFreeSimStop( pFree );
    Cbs_ManStop( pCbs );
    Cec_TranPreproofEvent( pProf, pBatch, "cbs", 1, nCands, pProf->nCombConfUsed - nConfStart );
    return vStage;
}

#include "cecTranSeqBudget.h"
#include "cecTranRelational.h"
#include "cecTranRelationalChunks.h"

// Return one status bit per candidate.  Seed candidate endpoints as ordinary
// equivalence classes and run one shared correspondence closure over exactly
// these relations.  This retains &scorr's standard BMC, SRM, CEX resimulation,
// class refinement, and induction fixed point without unrelated class search.
static Vec_Int_t * Cec_TranProveRootBatchPrepared( Gia_Man_t * pBatch,
    Cec_TranCand_t const * pCands, int nCands, int nHelpers,
    Cec_ParTran_t * pPars, Cec_TranProf_t * pProf, int fCombOnly,
    Vec_Str_t ** pvStage, Vec_Int_t * vPairs, Vec_Int_t * vCombPairs,
    Vec_Int_t * vQueries, Vec_Int_t * vAndLeaves, Vec_Str_t * vAndCounts )
{
    Cec_ParCor_t Cor;
    Gia_Obj_t * pObj;
    Vec_Int_t * vSeqPairs = NULL, * vRelStatus = NULL;
    Vec_Int_t * vStatus = Vec_IntStart( nCands );
    Vec_Str_t * vStage;
    Cec_ProfCor_t CorrBefore;
    int i, RetValue = 1, nSeq = 0;
    int RelMode = (pPars->fOdcProofScope || pPars->fRoute3) ?
        Cec_TranRelationalMode(pPars) : 0;
    int RelRounds = 0;
    int RelChunkMode = Cec_TranRelChunkMode(pPars);
    int nSeqSplit = 0, nSeqUnknown = 0, nSeqRoots = 0;
    abctime clk, timeSeq = 0;
    memset( &Cor, 0, sizeof(Cor) );
    assert( !pPars->fOdcProofScope || pPars->fOdcFanout );
    assert(!pPars->fRoute1 || pPars->fOdcProofScope || !fCombOnly);
    assert(nHelpers >= 0 && Vec_IntSize(vPairs) == 2*(nHelpers+nCands));
    assert(Vec_IntSize(vCombPairs) == 2*nCands);
    assert(!vAndCounts || Vec_StrSize(vAndCounts) == nCands);
    assert(pPars->fUseCbsMultiLit ? Vec_IntSize(vQueries) == 0 :
        Vec_IntSize(vQueries) == nCands);
    // Strict's existing certificate helpers retain their own legacy scope.
    // Speculative ODC CONST helpers must use relational withdrawal closure.
    assert(!pPars->fOdcProofScope || !nHelpers || RelMode == 1);
    if ( pPars->fOdcProofScope ) pProf->nOdcConstInjected += nHelpers;
    pProf->nRootSrmNodesMax = Abc_MaxInt(
        pProf->nRootSrmNodesMax, Gia_ManObjNum(pBatch) );
    // A universal root equality is already a complete CBS certificate.
    // Only unresolved candidates require reset BMC and the full SRM fixed
    // point; all original relations remain available as induction helpers.
    vStage = Cec_TranProveCombBatch( pBatch, pCands, nCands,
            vCombPairs, vQueries, vAndLeaves, vAndCounts, pPars, pProf,
            0, NULL );
    if ( !fCombOnly )
        for ( i = 0; i < nCands; i++ )
            if ( Vec_StrEntry(vStage, i) == 0 )
                nSeq++;
    pProf->nSeqCands += nSeq;
    if ( nSeq && RelMode )
    {
        Cec_TranRelObserve_t * previousObserve=Cec_TranRelObserveCurrent;
        Cec_TranRelClosed_t * previousClosed=Cec_TranRelClosedCurrent;
        Cec_TranRelObserveCurrent=(Cec_TranRelObserve_t *)pProf->pRelObserve;
        Cec_TranRelClosedCurrent=(Cec_TranRelClosed_t *)pProf->pRelClosed;
        clk = Abc_Clock();
        if ( Cec_TranSeqBudgetBegin() )
            vRelStatus = RelChunkMode ?
                Cec_TranRelChunksProve(pBatch,vPairs,pCands,nCands,nHelpers,vStage,pPars,
                    &RelRounds,RelChunkMode == 2 ? CEC_TRAN_REL_CHUNK_SIZE : 0) :
                Cec_TranRelationalProve(pBatch,vPairs,pPars,&RelRounds);
        else
            vRelStatus = Cec_TranSeqBudgetUnproved(nHelpers+nCands);
        Cec_TranSeqBudgetEnd(vRelStatus);
        Cec_TranRelObserveCurrent=previousObserve;
        Cec_TranRelClosedCurrent=previousClosed;
        Cec_TranRelObserveClosed((Cec_TranRelObserve_t *)pProf->pRelObserve,vRelStatus,RelRounds);
        Cec_TranRelClosedRecord((Cec_TranRelClosed_t *)pProf->pRelClosed,vRelStatus);
        assert(Vec_IntSize(vRelStatus) == nHelpers+nCands);
        if ( pPars->fOdcProofScope && nHelpers )
        {
            pProf->nOdcConstChecked += nHelpers;
            for ( i = 0; i < nHelpers; i++ )
            {
                int Status = Vec_IntEntry(vRelStatus,i);
                assert(Status >= -1 && Status <= 1);
                pProf->nOdcConstSurvived += Status == 1;
                pProf->nOdcConstWithdrawn += Status == 0;
                pProf->nOdcConstUnknown += Status == -1;
            }
            assert(pProf->nOdcConstChecked == pProf->nOdcConstSurvived +
                pProf->nOdcConstWithdrawn + pProf->nOdcConstUnknown);
        }
        pProf->timeRootScorrOther += Abc_Clock() - clk;
        if ( RelMode == 1 )
        {
            Cor.fCompleted = 1;
            pProf->nSeqSeeded += nHelpers + nCands;
            pProf->nSeqFixedRounds += RelRounds;
        }
    }
    if ( nSeq )
    {
        int iPrevTarget = -1, nClass = 0;
        for ( i = 0; i < nCands; i++ )
            {
                if ( pCands[i].iTarget != iPrevTarget )
                {
                    if ( nClass )
                    {
                        pProf->nSeqClassSum += nClass + 1;
                        pProf->nSeqClassMax = Abc_MaxInt(
                            pProf->nSeqClassMax, nClass + 1 );
                    }
                    nSeqRoots++;
                    iPrevTarget = pCands[i].iTarget;
                    nClass = 0;
                }
                nClass++;
            }
        if ( nClass )
        {
            pProf->nSeqClassSum += nClass + 1;
            pProf->nSeqClassMax = Abc_MaxInt(
                pProf->nSeqClassMax, nClass + 1 );
        }
        pProf->nSeqRoots += nSeqRoots;
    }
    if ( nSeq && RelMode != 1 )
    {
        Gia_ManSetPhase( pBatch );
        pBatch->pReprs = ABC_CALLOC( Gia_Rpr_t, Gia_ManObjNum(pBatch) );
        Gia_ManForEachObj( pBatch, pObj, i )
            Gia_ObjSetRepr( pBatch, i, GIA_VOID );
        Gia_ManCreateValueRefs( pBatch );
        // Universally proved combinational relations remain in the same
        // hypothesis as induction helpers.  They are not sequential proof
        // obligations, but removing them can break a shared invariant.
        vSeqPairs = Vec_IntAlloc( 2 * (nHelpers + nCands) );
        for ( i = 0; i < nHelpers + nCands; i++ )
            Vec_IntPushTwo( vSeqPairs, Vec_IntEntry(vPairs, 2*i),
                Vec_IntEntry(vPairs, 2*i + 1) );
        Cec_TranSeedRootClasses( pBatch, vSeqPairs );
        pProf->nSeqSeeded += Vec_IntSize(vSeqPairs) / 2;
        pBatch->pNexts = Gia_ManDeriveNexts( pBatch );
        Cec_ManCorSetDefaultParams( &Cor );
        Cor.nFrames   = pPars->nFrames;
        Cor.nBTLimit  = pPars->nBTLimit;
        // Root scorr intentionally has no shared conflict cap.  -C is the
        // per-output limit; an UNKNOWN output is removed from only its own
        // speculative class by ordinary scorr refinement.  A shared cap would
        // make solve order turn one hard relation into a global early stop.
        Cor.nConfTotal = 0;
        Cor.nStepsMax = pPars->nStepsMax;
        Cor.fVerbose  = 0;
        Cor.pProfile  = (pPars->fProfile || pPars->fVerbose) ? &pProf->Corr : NULL;
        if ( pProf->pStrictCex )
        {
            assert( !fCombOnly && pProf->DiagPhase == 1 );
            Cor.pCexFunc = Cec_TranStrictCexObserve;
            Cor.pCexData = pProf->pStrictCex;
        }
        CorrBefore = pProf->Corr;
        clk = Abc_Clock();
        RetValue = Cec_ManLSCorrespondenceClasses( pBatch, &Cor );
        timeSeq = Abc_Clock() - clk;
        // Detailed correspondence counters use nanosecond ticks.  Attribute
        // the complete base phase, inductive SAT, and resimulation separately;
        // the remaining wall time is class management and fixed-point control.
        {
            abctime TimeSrm = 0, TimeBmc = 0, TimeIndSat = 0;
            abctime TimeResim = 0, Remain = timeSeq, Use;
            if ( pPars->fProfile )
            {
                double BmcHr = pProf->Corr.timeBmc - CorrBefore.timeBmc;
                double BmcSrmHr = pProf->Corr.timeBmcSrm - CorrBefore.timeBmcSrm;
                double BmcSimHr = pProf->Corr.timeBmcSim - CorrBefore.timeBmcSim;
                double IndSrmHr = pProf->Corr.timeIndSrm - CorrBefore.timeIndSrm;
                double IndSatHr = pProf->Corr.timeIndSat - CorrBefore.timeIndSat;
                double IndSimHr = pProf->Corr.timeIndSim - CorrBefore.timeIndSim;
                double BmcOtherHr = BmcHr - BmcSrmHr - BmcSimHr;
                if ( BmcOtherHr < 0 )
                    BmcOtherHr = 0;
                TimeSrm = (abctime)(1.0e-9 * (BmcSrmHr + IndSrmHr) * CLOCKS_PER_SEC);
                TimeBmc = (abctime)(1.0e-9 * BmcOtherHr * CLOCKS_PER_SEC);
                TimeIndSat = (abctime)(1.0e-9 * IndSatHr * CLOCKS_PER_SEC);
                TimeResim = (abctime)(1.0e-9 * (BmcSimHr + IndSimHr) * CLOCKS_PER_SEC);
                Use = TimeSrm < Remain ? TimeSrm : Remain;
                pProf->timeRootScorrGraph += Use; Remain -= Use;
                Use = TimeBmc < Remain ? TimeBmc : Remain;
                pProf->timeRootScorrBmc += Use; Remain -= Use;
                Use = TimeIndSat < Remain ? TimeIndSat : Remain;
                pProf->timeRootScorrIndSat += Use; Remain -= Use;
                Use = TimeResim < Remain ? TimeResim : Remain;
                pProf->timeRootScorrResim += Use; Remain -= Use;
                pProf->timeRootScorrOther += Remain;
            }
            else
                pProf->timeRootScorrOther += timeSeq;
        }
        if ( Cor.fCompleted )
            pProf->nSeqFixedRounds += Cor.nRoundsDone;
    }
    for ( i = 0; i < nCands; i++ )
    {
        int fProved = Vec_StrEntry(vStage, i) == 1;
        int fBatchComplete = 0;
        if ( !fProved && nSeq )
        {
            int fSameClass = RelMode == 1 ? Vec_IntEntry(vRelStatus,nHelpers+i) == 1 :
                Cec_TranRootBatchPairProved( pBatch,
                Vec_IntEntry(vPairs, 2*(nHelpers+i)),
                Vec_IntEntry(vPairs, 2*(nHelpers+i)+1) );
            fBatchComplete = RetValue && Cor.fCompleted;
            // fConfStop can only accompany an incomplete correspondence run;
            // it is not the per-output UNKNOWN indication.  Keep the invariant
            // explicit so callers cannot accidentally reintroduce batch-wide
            // poisoning for ordinary solver UNKNOWNs.
            assert( !Cor.fConfStop || !Cor.fCompleted );
            fProved = fBatchComplete && fSameClass;
            if ( !fProved )
            {
                // As in ordinary &scorr, SAT counterexamples split only the
                // affected speculative class.  A global early stop is UNKNOWN;
                // a completed fixed point classifies each relation by whether
                // its endpoints survived in the same refined class.
                nSeqSplit += fBatchComplete && !fSameClass &&
                    (RelMode != 1 || Vec_IntEntry(vRelStatus,nHelpers+i) == 0);
                nSeqUnknown += !fBatchComplete ||
                    (RelMode == 1 && Vec_IntEntry(vRelStatus,nHelpers+i) < 0);
            }
        }
        if ( fProved && Vec_StrEntry(vStage, i) == 0 )
        {
            Vec_StrWriteEntry( vStage, i, 2 );
            pProf->nSeqProved++;
        }
        Vec_IntWriteEntry( vStatus, i, fProved );
        assert(!fProved || Vec_StrEntry(vStage, i) == 1 ||
            Vec_StrEntry(vStage, i) == 2);
    }
    if ( pPars->fVerbose )
    {
        int Counts[2][3] = {{0}}; // Direct/Build x unproved/CBS/SEQ
        int HelperProved = 0, HelperUnproved = 0, HelperUnknown = 0;
        int HelperObserved = RelMode == 1 && vRelStatus != NULL;
        for ( i = 0; i < nCands; ++i )
            ++Counts[pCands[i].nKind == CEC_TRAN_CAND_CONSTR][(int)Vec_StrEntry(vStage,i)];
        for ( i = 0; HelperObserved && i < nHelpers; ++i )
        {
            int Status = Vec_IntEntry(vRelStatus,i);
            HelperProved += Status == 1;
            HelperUnproved += Status == 0;
            HelperUnknown += Status < 0;
        }
        // A pure CBS batch performs no sequential helper check. Report that
        // absence explicitly rather than inventing zero helper-proof work.
        Abc_Print(1,"stran-root batch-certificates: schema=1 round=%d wave=%d batch=%d helpers-enabled=%d helpers=%d helper-proof-observed=%d helper-proved=%d helper-unproved-zero=%d helper-unknown=%d target-direct-cbs=%d target-direct-seq=%d target-direct-unproved=%d target-build-cbs=%d target-build-seq=%d target-build-unproved=%d closure-rounds=%d proof-mode=%d\n",
            pProf->PreproofRound,pProf->PreproofWave,pProf->nRootBatchCalls+1,
            pPars->fUseHelpers,nHelpers,HelperObserved,
            HelperObserved ? HelperProved : -1,HelperObserved ? HelperUnproved : -1,
            HelperObserved ? HelperUnknown : -1,Counts[0][1],Counts[0][2],Counts[0][0],
            Counts[1][1],Counts[1][2],Counts[1][0],RelRounds,RelChunkMode);
    }
    if ( RelMode == 2 && nSeq )
    {
        int both=0, legacyOnly=0, relationalOnly=0, neither=0;
        for ( i=0; i<nCands; i++ )
        {
            int a=Vec_IntEntry(vStatus,i), b=Vec_StrEntry(vStage,i)==1 ||
                Vec_IntEntry(vRelStatus,nHelpers+i)==1;
            both += a && b; legacyOnly += a && !b;
            relationalOnly += !a && b; neither += !a && !b;
        }
        Abc_Print(1,"stran-root relational-comparison: schema=1 candidates=%d both=%d legacy-only=%d relational-only=%d neither=%d consume=legacy\n",
            nCands,both,legacyOnly,relationalOnly,neither);
    }
    Vec_IntFreeP(&vRelStatus);
    pProf->nRootBatchCalls++;
    pProf->nRootBatchMax = Abc_MaxInt( pProf->nRootBatchMax,
        nHelpers + nCands );
    pProf->nSeqSplit += nSeqSplit;
    pProf->nSeqUnknown += nSeqUnknown;
    Vec_IntFree( vPairs );
    Vec_IntFree( vCombPairs );
    Vec_IntFree( vQueries );
    Vec_IntFreeP( &vSeqPairs );
    Vec_IntFreeP( &vAndLeaves );
    Vec_StrFreeP( &vAndCounts );
    Gia_ManStop( pBatch );
    *pvStage = vStage;
    return vStatus;
}

static Vec_Int_t * Cec_TranProveRootBatch( Gia_Man_t * p,
    Cec_TranCand_t const * pHelpers, int nHelpers,
    Cec_TranCand_t const * pCands, int nCands, Cec_ParTran_t * pPars,
    Cec_TranProf_t * pProf, int fCombOnly, Vec_Str_t ** pvStage )
{
    Vec_Int_t * vPairs, * vCombPairs, * vQueries;
    Vec_Int_t * vAndLeaves = NULL;
    Vec_Str_t * vAndCounts = NULL;
    Cec_TranCandVec_t expanded={0};
    Cec_TranRootBatchSize_t Size;
    Vec_Int_t * result;
    int nRequestedHelpers = nHelpers;
    abctime clk = Abc_Clock();
    Gia_Man_t * pBatch;
    if(pProf->pRelClosed)
    {
        Cec_TranRelClosedPrepare((Cec_TranRelClosed_t *)pProf->pRelClosed,p,
            pHelpers,nHelpers,pCands,nCands,pPars->nFrames,&expanded);
        pHelpers=expanded.pArray;nHelpers=expanded.nSize;
    }
    if(pProf->pRelObserve)
    {
        Cec_TranRelObserveBegin((Cec_TranRelObserve_t *)pProf->pRelObserve,p,
            pHelpers,nHelpers,pCands,nCands,pPars->nFrames);
        Cec_TranRelObservePrint((Cec_TranRelObserve_t *)pProf->pRelObserve,"batch-enter",0);
    }
    Cec_TranPreproofEvent( pProf, p, "batch-copy", 0, nHelpers + nCands, 0 );
    pBatch = Cec_TranBuildRootBatchMeasured( p, pHelpers, nHelpers,
        pCands, nCands, !pPars->fUseCbsMultiLit ? 2 : 0,
        &vPairs, &vCombPairs, &vQueries,
        pPars->fUseCbsMultiLit ? &vAndLeaves : NULL,
        pPars->fUseCbsMultiLit ? &vAndCounts : NULL,
        pPars->fVerbose ? &Size : NULL );
    if ( pPars->fVerbose )
        Abc_Print(1,"stran-root batch-materialization: schema=1 round=%d wave=%d batch=%d source-objs=%d source-ands=%d source-copy-objs=%d source-copy-ands=%d requested-helpers=%d helpers=%d helper-build=%d helper-direct=%d targets=%d target-build=%d target-direct=%d closed-known=%d recipe-helper-ands=%d recipe-build-ands=%d recipe-direct-ands=%d query-ands=%d proxy-ands=%d raw-objs=%d raw-ands=%d batch-objs=%d batch-ands=%d batch-regs=%d\n",
            pProf->PreproofRound,pProf->PreproofWave,pProf->nRootBatchCalls+1,
            Gia_ManObjNum(p),Gia_ManAndNum(p),Size.CopyObjs,Size.CopyAnds,
            nRequestedHelpers,nHelpers,Size.HelperBuild,nHelpers-Size.HelperBuild,
            nCands,Size.TargetBuild,nCands-Size.TargetBuild,
            pProf->pRelClosed ? ((Cec_TranRelClosed_t *)pProf->pRelClosed)->nKnown : 0,
            Size.HelperAnds,Size.BuildAnds,Size.DirectAnds,Size.QueryAnds,Size.ProxyAnds,
            Size.RawObjs,Size.RawAnds,Gia_ManObjNum(pBatch),Gia_ManAndNum(pBatch),Gia_ManRegNum(pBatch));
    // Legacy profile label: this is shared immutable batch preparation,
    // including Route1's temporal-only path, not evidence of a CBS SAT call.
    pProf->timeRootCbsGraph += Abc_Clock() - clk;
    Cec_TranPreproofEvent( pProf, pBatch, "batch-copy", 1, nHelpers + nCands, Gia_ManObjNum(pBatch) );
    result=Cec_TranProveRootBatchPrepared(pBatch,pCands,nCands,nHelpers,
        pPars,pProf,fCombOnly,pvStage,vPairs,vCombPairs,vQueries,
        vAndLeaves,vAndCounts);
    Cec_TranCandVecStop(&expanded);
    return result;
}

// A correspondence counterexample produced during induction is a local SRM
// assignment and need not be reachable from reset.  Between construct waves,
// therefore, ask one bounded reset-reachable question over all failed
// constructed recipes.  One real trace is enough to rebuild every signature
// and dependency problem in the next wave.
static int Cec_TranRootCandidateGainEval( Gia_Man_t * p,
    Cec_TranCand_t const * pCand, Cec_TranProf_t * pProf )
{
    Gia_Obj_t * pRoot = Gia_ManObj( p, pCand->iTarget );
    int Used[2 * CEC_TRAN_RECIPE_NODES_MAX + 1];
    int Gain, i, k, Code, iObj, nUsed = 0, fSeen;
    abctime clk = Abc_Clock();

    // Root scheduling needs the local structural gain, not a rebuilt copy of
    // the complete sequential network.  Temporarily add the replacement's
    // fanin references, dereference the target MFFC, and restore the original
    // reference counts.  This is O(affected MFFC), changes no graph objects,
    // and correctly keeps a divisor that lies inside the removed cone alive.
    // The recipe costs at most nGates new AIG nodes; structural hashing can
    // only improve the final gain.  Strict-root candidates cache the simpler
    // MFFC-nGates bound at discovery, so this affected-MFFC walk is only a
    // fallback for lanes whose divisors are not guaranteed outside the MFFC.
    // The one real bundle commit below still performs cleanup and checks the
    // exact combined AND+register gain.
    assert( p->pRefs != NULL );
    assert( Gia_ObjIsAnd(pRoot) );
    for ( i = -1; i < 2 * pCand->nGates; i++ )
    {
        Code = i < 0 ? pCand->iOut : pCand->Recipe[i];
        if ( Cec_TranRecipeCodeIsGate(Code) )
            continue;
        iObj = Abc_Lit2Var( Code );
        if ( iObj == 0 || !Gia_ObjIsAnd(Gia_ManObj(p, iObj)) )
            continue;
        fSeen = 0;
        for ( k = 0; k < nUsed; k++ )
            fSeen |= Used[k] == iObj;
        if ( fSeen )
            continue;
        Used[nUsed++] = iObj;
        Gia_ObjRefIncId( p, iObj );
    }
    Gain = Gia_NodeMffcSize( p, pRoot );
    for ( i = 0; i < nUsed; i++ )
        Gia_ObjRefDecId( p, Used[i] );
    Gain -= pCand->nGates;
    pProf->timeGain += Abc_Clock() - clk;
    pProf->nGainCalls++;
    return Gain;
}

static int Cec_TranCandGainCompare( const void * p0, const void * p1 )
{
    Cec_TranCand_t const * pC0 = (Cec_TranCand_t const *)p0;
    Cec_TranCand_t const * pC1 = (Cec_TranCand_t const *)p1;
    if ( pC0->Gain != pC1->Gain )
        return pC1->Gain - pC0->Gain;
    if ( pC0->nKind != pC1->nKind )
        return pC0->nKind - pC1->nKind;
    if ( pC0->nGates != pC1->nGates )
        return pC0->nGates - pC1->nGates;
    if ( pC0->iOut != pC1->iOut )
        return pC0->iOut - pC1->iOut;
    return memcmp( pC0->Recipe, pC1->Recipe,
        sizeof(int) * 2 * pC0->nGates );
}
