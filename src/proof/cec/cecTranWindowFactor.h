// Proof-only Boolean-difference factorization. Included by cecTranOdc.h.
// For each exit e(r,s), Shannon expansion gives
//   e(r,s) XOR e(h,s) = (r XOR h) AND (e(0,s) XOR e(1,s)).
// Thus ALL frozen-window exits are preserved iff (r XOR h) AND D == 0,
// where D is the OR of their Boolean differences. D depends on the window,
// not the replacement. Reconvergence is preserved by shared cofactors.
// The masked-pair representation (r AND D) = (h AND D) is equivalent and
// avoids building a per-candidate XOR for correspondence/multi-literal CBS.
// No simulation care mask or previously proved certificate is reused here.

static int Cec_TranWindowFactorCare( Gia_Man_t * p, Gia_Man_t * pNew,
    int Root, Cec_ParTran_t * pPars, int * pnNodes, int * pnEnds,
    int * pfFull )
{
    Vec_Int_t * vNodes = Vec_IntAlloc(32), * vEnds = Vec_IntAlloc(16);
    int Cof[2][CEC_TRAN_RECIPE_NODES_MAX+1];
    int overflow, i, j, k, a, side, ends, Care = 0;
    Cec_TranWindowCollect(p,Root,Cec_TranWindowDepth(pPars),
        CEC_TRAN_RECIPE_NODES_MAX-pPars->nDepNodesMax,vNodes,vEnds,&overflow);
    *pnNodes = Vec_IntSize(vNodes);
    *pnEnds = Vec_IntSize(vEnds);
    *pfFull = pPars->fOdcStrict || (pPars->nExplore & 16384) ||
        Vec_IntFind(vEnds,Root) >= 0;
    assert(*pnEnds > 0 && *pnNodes <= CEC_TRAN_RECIPE_NODES_MAX+1);
    if ( *pfFull )
        Care = 1;
    else
    {
        for ( side = 0; side < 2; side++ )
        {
            Cof[side][0] = side;
            for ( i = 1; i < Vec_IntSize(vNodes); i++ )
            {
                Gia_Obj_t * pObj = Gia_ManObj(p,Vec_IntEntry(vNodes,i));
                int Lits[2];
                assert(Gia_ObjIsAnd(pObj) && !Gia_ObjIsXor(pObj) &&
                    !Gia_ObjIsMux(p,pObj) && !Gia_ObjIsBuf(pObj));
                for ( j = 0; j < 2; j++ )
                {
                    a = j ? Gia_ObjFaninLit1p(p,pObj) : Gia_ObjFaninLit0p(p,pObj);
                    k = Vec_IntFind(vNodes,Abc_Lit2Var(a));
                    assert(k < i);
                    Lits[j] = k < 0 ? Cec_TranCopyLit(p,a) :
                        Abc_LitNotCond(Cof[side][k],Abc_LitIsCompl(a));
                }
                Cof[side][i] = Gia_ManHashAnd(pNew,Lits[0],Lits[1]);
            }
        }
        Vec_IntForEachEntry(vEnds,ends,i)
        {
            k = Vec_IntFind(vNodes,ends);
            assert(k >= 0);
            a = Gia_ManHashXor(pNew,Cof[0][k],Cof[1][k]);
            Care = Gia_ManHashOr(pNew,Care,a);
        }
    }
    Vec_IntFree(vNodes); Vec_IntFree(vEnds);
    return Care;
}

static Gia_Man_t * Cec_TranBuildWindowFactorBatch( Gia_Man_t * p,
    Cec_TranCand_t const * pHelpers, int nHelpers,
    Cec_TranCand_t const * pCands, int nCands, Cec_ParTran_t * pPars,
    Vec_Int_t ** pvPairs, Vec_Int_t ** pvCombPairs, Vec_Int_t ** pvQueries,
    Vec_Int_t ** pvAndLeaves, Vec_Str_t ** pvAndCounts, int * pnFull )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    Vec_Int_t * vPairs = Vec_IntAlloc(2*(nHelpers+nCands));
    Vec_Int_t * vCombPairs = Vec_IntAlloc(2*nCands);
    Vec_Int_t * vQueries = Vec_IntAlloc(nCands);
    Vec_Int_t * vAndLeaves = pPars->fUseCbsMultiLit ? Vec_IntAlloc(2*nCands) : NULL;
    Vec_Str_t * vAndCounts = pPars->fUseCbsMultiLit ? Vec_StrAlloc(nCands) : NULL;
    int * pCare = ABC_FALLOC(int,Gia_ManObjNum(p));
    int * pNodes = ABC_CALLOC(int,Gia_ManObjNum(p));
    int * pEnds = ABC_CALLOC(int,Gia_ManObjNum(p));
    int * pFull = ABC_CALLOC(int,Gia_ManObjNum(p));
    int * pPiProxies = Gia_ManPiNum(p) ? ABC_FALLOC(int,2*Gia_ManPiNum(p)) : NULL;
    int Gates[CEC_TRAN_RECIPE_NODES_MAX];
    int Leaves[2*CEC_TRAN_RECIPE_NODES_MAX+1];
    int i, k, r, Root, Rep, Bad, Care, nRoots = 0, nBefore, nAfterCopy, nLeaves;
    long long nCofactorNodes = 0, nOriginalExits = 0, nUnfactoredWindowNodes = 0;
    assert(nCands > 0 && nHelpers >= 0 && (!nHelpers || pHelpers));
    *pnFull = 0;
    Gia_ManFillValue(p);
    pNew = Gia_ManStart(Gia_ManObjNum(p)+4*nCands+16);
    pNew->pName = Abc_UtilStrsav("stran_window_boolean_difference");
    Gia_ManHashAlloc(pNew);
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi(p,pObj,i) pObj->Value = Gia_ManAppendCi(pNew);
    Gia_ManForEachAnd(p,pObj,i)
        pObj->Value = Cec_TranHashGate(pNew,pObj,
            Gia_ObjFanin0Copy(pObj),Gia_ObjFanin1Copy(pObj));
    nAfterCopy = Gia_ManAndNum(pNew);
    // Helpers are original-graph predicates.  They are never care-masked and
    // never enter candidate-only CBS queries, leaf arrays, or returned status.
    for ( i = 0; i < nHelpers; i++ )
    {
        assert(pHelpers[i].nKind == CEC_TRAN_CAND_CONST &&
            pHelpers[i].nGates == 0 && pHelpers[i].Recipe == NULL &&
            pHelpers[i].iOut >= 0 && pHelpers[i].iOut <= 1);
        Root = Cec_TranCopyLit(p,Abc_Var2Lit(pHelpers[i].iTarget,0));
        Rep = pHelpers[i].iOut;
        Vec_IntPushTwo(vPairs,Root,Rep);
    }
    for ( i = 0; i < nCands; i++ )
    {
        r = pCands[i].iTarget;
        if ( pCare[r] == -1 )
        {
            nBefore = Gia_ManAndNum(pNew);
            pCare[r] = Cec_TranWindowFactorCare(p,pNew,r,pPars,
                pNodes+r,pEnds+r,pFull+r);
            nCofactorNodes += Gia_ManAndNum(pNew)-nBefore;
            nRoots++;
        }
        Care = pCare[r];
        // Match the original strict fallback exactly for oversized recipes.
        if ( pCands[i].nGates+pNodes[r]-1 > CEC_TRAN_RECIPE_NODES_MAX )
            Care = 1;
        *pnFull += pFull[r] ||
            pCands[i].nGates+pNodes[r]-1 > CEC_TRAN_RECIPE_NODES_MAX;
        nOriginalExits += (pPars->fOdcStrict || (pPars->nExplore & 16384) ||
            pCands[i].nGates+pNodes[r]-1 > CEC_TRAN_RECIPE_NODES_MAX) ? 1 : pEnds[r];
        nUnfactoredWindowNodes += pNodes[r]-1;
        Root = Cec_TranCopyLit(p,Abc_Var2Lit(r,0));
        Rep = Cec_TranRecipeBuildMapped(p,pNew,pCands+i,Gates);
        Root = Gia_ManHashAnd(pNew,Root,Care);
        Rep = Gia_ManHashAnd(pNew,Rep,Care);
        Vec_IntPushTwo(vCombPairs,Root,Rep);
        if ( !pPars->fUseCbsMultiLit )
            Vec_IntPush(vQueries,Gia_ManHashXor(pNew,Root,Rep));
        if ( vAndCounts )
        {
            // With D=1, a masked pair is exactly the original strict-root
            // relation. Its recipe leaf decomposition remains valid. Other
            // masked predicates must use generic equality CBS.
            nLeaves = Care == 1 ?
                Cec_TranRecipeCollectAndLeaves(pCands+i,Leaves) : 0;
            for ( k = 0; k < nLeaves; k++ )
                Vec_IntPush(vAndLeaves,Cec_TranRecipeCopyCode(p,
                    Leaves[k],Gates,pCands[i].nGates));
            Vec_StrPush(vAndCounts,(char)nLeaves);
        }
        Vec_IntPushTwo(vPairs,Root,Rep);
    }
    assert(Vec_IntSize(vPairs) == 2*(nHelpers+nCands));
    assert(Vec_IntSize(vCombPairs) == 2*nCands);
    assert(!vAndCounts || Vec_StrSize(vAndCounts) == nCands);
    // This builder shares the same raw PI-class proxies as the root batch.
    // Complete all source/cofactor/recipe/query hashing before creating them;
    // candidate CBS endpoints and all-exit predicates remain unchanged.
    Gia_ManHashStop(pNew);
    for ( i = 0; i < Vec_IntSize(vPairs); ++i )
        Vec_IntWriteEntry(vPairs,i,Cec_TranRootClassEndpoint(pNew,
            Vec_IntEntry(vPairs,i),Gia_ManPiNum(p),pPiProxies));
    Vec_IntForEachEntry(vQueries,Bad,i) Gia_ManAppendCo(pNew,Bad);
    Vec_IntForEachEntry(vPairs,Bad,i) Gia_ManAppendCo(pNew,Bad);
    Gia_ManForEachRi(p,pObj,i) Gia_ManAppendCo(pNew,Gia_ObjFanin0Copy(pObj));
    Gia_ManSetRegNum(pNew,Gia_ManRegNum(p));
    nBefore = Gia_ManAndNum(pNew);
    pNew = Gia_ManCleanup(pTemp=pNew);
    Gia_ManDupRemapLiterals(vPairs,pTemp);
    Gia_ManDupRemapLiterals(vCombPairs,pTemp);
    Gia_ManDupRemapLiterals(vQueries,pTemp);
    if ( vAndLeaves ) Gia_ManDupRemapLiterals(vAndLeaves,pTemp);
    Gia_ManStop(pTemp);
    if ( pPars->fVerbose )
        Abc_Print(1,"window-factor graph: encoding=%s candidates=%d roots=%d original-exits=%lld factored-obligations=%d unshared-window-node-visits=%lld cofactor-new-ands=%lld source-copy-ands=%d before-cleanup-ands=%d proof-ands=%d\n",
            "masked-pair",nCands,nRoots,nOriginalExits,nCands,nUnfactoredWindowNodes,
            nCofactorNodes,nAfterCopy,nBefore,Gia_ManAndNum(pNew));
    ABC_FREE(pCare); ABC_FREE(pNodes); ABC_FREE(pEnds); ABC_FREE(pFull); ABC_FREE(pPiProxies);
    *pvPairs=vPairs; *pvCombPairs=vCombPairs; *pvQueries=vQueries;
    *pvAndLeaves = vAndLeaves;
    *pvAndCounts = vAndCounts;
    return pNew;
}

static Vec_Int_t * Cec_TranProveWindowFactorBatch( Gia_Man_t * p,
    Cec_TranCand_t const * pHelpers, int nHelpers,
    Cec_TranCand_t const * pCands, int nCands, Cec_ParTran_t * pPars,
    Cec_TranProf_t * pProf, int fCombOnly, Vec_Str_t ** pvStage, int * pnFull )
{
    Vec_Int_t * vPairs, * vCombPairs, * vQueries, * vAndLeaves;
    Vec_Str_t * vAndCounts;
    abctime clk = Abc_Clock();
    Gia_Man_t * pBatch = Cec_TranBuildWindowFactorBatch(p,pHelpers,nHelpers,pCands,nCands,pPars,
        &vPairs,&vCombPairs,&vQueries,&vAndLeaves,&vAndCounts,pnFull);
    pProf->timeRootCbsGraph += Abc_Clock()-clk;
    return Cec_TranProveRootBatchPrepared(pBatch,pCands,nCands,nHelpers,
        pPars,pProf,fCombOnly,pvStage,vPairs,vCombPairs,vQueries,vAndLeaves,vAndCounts);
}

// Exhaustive truth-table oracle over the independently built original and
// factored proof graphs. This catches care polarity, reconvergence and omitted
// exits even if the two SAT call paths happen to return the same status.
