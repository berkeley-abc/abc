// Frozen ODC core engine imported from 517615384; selected only by explicit
// stage-aware ODC override in cecTranRelational.h. No native-XOR/lazy changes.
// Same immutable transition and simultaneous Houdini operator as Separate.
// An UNSAT assumption core certifies a target under a subset of the frozen H.
// That certificate survives weakening H only while every dependency survives.
// This state is owned by this one call; it never crosses a proof page or commit.
typedef struct Cec_TranRelCoreStat_t_ {
    long long nSkipped, nInvalidated, nCoreEdges, nCoreChecks;
    long long nAssumptionLits, nHypothesisDuplicates, nUnconditional;
    long long nHypothesisPushes, nQueryPushes, nPrefixRounds, nPrefixPops;
} Cec_TranRelCoreStat_t;

static Vec_Int_t * Cec_TranRelationalProveCore( Gia_Man_t * p,
    Vec_Int_t * vPairs, Cec_ParTran_t * pPars, int * pnRounds,
    Cec_TranRelCoreStat_t * pStat, int fPrefix )
{
    int n = Vec_IntSize(vPairs)/2, k = pPars->nFrames;
    Vec_Int_t * vStatus = Vec_IntStartFull(n), * vFrozen = Vec_IntStart(n);
    Vec_Int_t * vAssumptions = Vec_IntAlloc(n*k+1);
    Vec_Int_t ** pDeps = ABC_CALLOC(Vec_Int_t *,n);
    Cec_TranRelUnroll_t base, ind;
    Cec_TranRelCoreStat_t Stat = {0};
    int * pLitOwner;
    int i, j, f, q, status, changed=1, rounds=0, alive=0, incomplete=0;
    int baseSat=0, baseUnknown=0, indSat=0, indUnknown=0, nLits;
    long long baseQueries=0, indQueries=0;
    int ModelPrune = Cec_TranStrictCexOption("ABC_REL_MODEL_PRUNE",0,1);
    long long ModelScanned=0, BaseModelRemoved=0, IndModelRemoved=0;
    abctime TimeModel=0;
    abctime clk = Abc_Clock();
    assert(k > 0);
    base = Cec_TranRelUnroll(p,vPairs,k,1);
    Vec_IntFill(vStatus,n,1);
    for ( i=0; i<n; i++ )
    {
        if ( Vec_IntEntry(vStatus,i)!=1 ) continue;
        for ( f=0; f<k; f++ )
        {
            q = Vec_IntEntry(base.vQueries,f*n+i);
            baseQueries++;
            status = sat_solver_solve(base.pSat,&q,&q+1,pPars->nBTLimit,0,0,0);
            if ( status == l_False ) continue;
            baseSat += status==l_True; baseUnknown += status==l_Undef;
            if ( status == l_True && ModelPrune )
            {
                abctime clkModel=Abc_Clock();
                int Removed;
                assert(Cec_TranRelModelLit(base.pSat,q)==1);
                Removed=Cec_TranRelModelWithdraw(&base,vStatus,0,k,&ModelScanned);
                assert(Removed>0 && Vec_IntEntry(vStatus,i)==0);
                BaseModelRemoved+=Removed;
                TimeModel+=Abc_Clock()-clkModel;
            }
            else Vec_IntWriteEntry(vStatus,i,status==l_True ? 0 : -1);
            break;
        }
    }
    for ( i=0; i<n; ++i ) alive += Vec_IntEntry(vStatus,i)==1;
    Cec_TranRelUnrollStop(&base);
    ind = Cec_TranRelUnroll(p,vPairs,k+1,0);
    nLits = 2*Gia_ManObjNum(ind.p);
    pLitOwner = ABC_ALLOC(int,nLits);
    while ( pPars->nStepsMax < 0 || rounds < pPars->nStepsMax )
    {
        int nHypotheses;
        changed=0; rounds++;
        memcpy(Vec_IntArray(vFrozen),Vec_IntArray(vStatus),sizeof(int)*n);
        Vec_IntClear(vAssumptions);
        for ( i=0; i<nLits; i++ ) pLitOwner[i]=-1;
        for ( f=0; f<k; f++ ) for ( i=0; i<n; i++ )
            if ( Vec_IntEntry(vFrozen,i)==1 )
            {
                q = Vec_IntEntry(ind.vQueries,f*n+i);
                assert(q >= 0 && q < nLits);
                if ( pLitOwner[q]>=0 )
                {
                    Stat.nHypothesisDuplicates++;
                    continue;
                }
                pLitOwner[q]=i;
                Vec_IntPush(vAssumptions,q^1);
            }
        nHypotheses=Vec_IntSize(vAssumptions);
        if ( fPrefix )
        {
            assert(ind.pSat->root_level==0 && veci_size(&ind.pSat->trail_lim)==0);
            for ( j=0; j<nHypotheses; j++ )
            {
                int ok=sat_solver_push(ind.pSat,Vec_IntEntry(vAssumptions,j));
                // Every frozen predicate passed all reset base frames. Their
                // conjunction has a reset-prefix witness in this original T.
                // A contradiction here violates a prover invariant.
                assert(ok);
                if ( !ok ) abort();
            }
            assert(ind.pSat->root_level==nHypotheses);
            Stat.nPrefixRounds++;
            Stat.nHypothesisPushes+=nHypotheses;
            Stat.nAssumptionLits+=nHypotheses;
        }
        for ( i=0; i<n; i++ )
        {
            int valid = pDeps[i]!=NULL;
            int * pCore, nCore;
            if ( Vec_IntEntry(vStatus,i)!=1 ) continue;
            if ( valid )
                Vec_IntForEachEntry(pDeps[i],j,f)
                {
                    Stat.nCoreChecks++;
                    if ( Vec_IntEntry(vFrozen,j)!=1 ) { valid=0; break; }
                }
            if ( valid ) { Stat.nSkipped++; continue; }
            if ( pDeps[i] ) Stat.nInvalidated++;
            q = Vec_IntEntry(ind.vQueries,k*n+i);
            indQueries++;
            Stat.nQueryPushes++;
            if ( fPrefix )
            {
                assert(ind.pSat->root_level==nHypotheses);
                sat_solver_set_resource_limits(ind.pSat,pPars->nBTLimit,0,0,0);
                Stat.nAssumptionLits++;
                status=sat_solver_push(ind.pSat,q) ?
                    sat_solver_solve_internal(ind.pSat) : l_False;
                assert(ind.pSat->root_level==nHypotheses+1 &&
                    veci_size(&ind.pSat->trail_lim)==nHypotheses+1);
            }
            else
            {
                Vec_IntPush(vAssumptions,q);
                Stat.nAssumptionLits+=Vec_IntSize(vAssumptions);
                Stat.nHypothesisPushes+=nHypotheses;
                status=sat_solver_solve(ind.pSat,Vec_IntArray(vAssumptions),
                    Vec_IntArray(vAssumptions)+Vec_IntSize(vAssumptions),
                    pPars->nBTLimit,0,0,0);
                Vec_IntPop(vAssumptions);
            }
            if ( status==l_False )
            {
                if ( !pDeps[i] ) pDeps[i]=Vec_IntAlloc(4);
                else Vec_IntClear(pDeps[i]);
                nCore = sat_solver_final(ind.pSat,&pCore);
                for ( f=0; f<nCore; f++ )
                {
                    int lit = pCore[f];
                    // BSAT returns the negations of assumptions. The target
                    // assumption is not a hypothesis dependency, even when a
                    // prior-frame assumption happens to duplicate its literal.
                    if ( lit==(q^1) ) continue;
                    assert(lit >= 0 && lit < nLits && pLitOwner[lit]>=0);
                    j=pLitOwner[lit];
                    assert(Vec_IntEntry(vFrozen,j)==1);
                    Vec_IntPushUnique(pDeps[i],j);
                }
                Stat.nCoreEdges += Vec_IntSize(pDeps[i]);
                Stat.nUnconditional += Vec_IntSize(pDeps[i])==0;
                if ( fPrefix )
                {
                    sat_solver_pop(ind.pSat); Stat.nPrefixPops++;
                    assert(ind.pSat->root_level==nHypotheses);
                }
                continue;
            }
            indSat += status==l_True; indUnknown += status==l_Undef;
            if ( status == l_True && ModelPrune )
            {
                abctime clkModel=Abc_Clock();
                int Removed;
                // The SAT model satisfies this round's frozen H, even if
                // earlier queries have already withdrawn some status entries.
                assert(Cec_TranRelModelLit(ind.pSat,q)==1);
                Removed=Cec_TranRelModelWithdraw(&ind,vStatus,k,1,&ModelScanned);
                assert(Removed>0 && Vec_IntEntry(vStatus,i)==0);
                IndModelRemoved+=Removed;
                alive-=Removed;
                TimeModel+=Abc_Clock()-clkModel;
            }
            else
            {
                Vec_IntWriteEntry(vStatus,i,status==l_True ? 0 : -1);
                alive--;
            }
            if ( fPrefix )
            {
                sat_solver_pop(ind.pSat); Stat.nPrefixPops++;
                assert(ind.pSat->root_level==nHypotheses);
            }
            changed=1;
        }
        if ( fPrefix )
        {
            for ( j=0; j<nHypotheses; j++ )
            {
                sat_solver_pop(ind.pSat); Stat.nPrefixPops++;
            }
            assert(ind.pSat->root_level==0 && veci_size(&ind.pSat->trail_lim)==0);
        }
        if ( !changed || !alive ) break;
    }
    if ( changed && alive )
    {
        incomplete=alive;
        for ( i=0; i<n; i++ ) if ( Vec_IntEntry(vStatus,i)==1 )
            Vec_IntWriteEntry(vStatus,i,-1);
        alive=0;
    }
    assert(rounds <= n+1);
    for ( i=0; i<n; i++ )
    {
        if ( Vec_IntEntry(vStatus,i)==1 )
        {
            assert(pDeps[i]!=NULL);
            Vec_IntForEachEntry(pDeps[i],j,f)
                assert(Vec_IntEntry(vStatus,j)==1);
        }
        Vec_IntFreeP(pDeps+i);
    }
    CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root relational-proof: schema=1 depth=%d relations=%d proved=%d rounds=%d base-queries=%lld base-sat=%d base-unknown=%d ind-queries=%lld ind-sat=%d ind-unknown=%d incomplete=%d seconds=%.6f\n",
        k,n,alive,rounds,baseQueries,baseSat,baseUnknown,indQueries,indSat,
        indUnknown,incomplete,(double)(Abc_Clock()-clk)/CLOCKS_PER_SEC);
    CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root relational-core: schema=1 skipped=%lld invalidated=%lld core-edges=%lld core-checks=%lld assumption-lits=%lld hypothesis-duplicates=%lld unconditional=%lld engine=%d hypothesis-pushes=%lld query-pushes=%lld prefix-rounds=%lld prefix-pops=%lld\n",
        Stat.nSkipped,Stat.nInvalidated,Stat.nCoreEdges,Stat.nCoreChecks,
        Stat.nAssumptionLits,Stat.nHypothesisDuplicates,Stat.nUnconditional,
        fPrefix ? 2 : 1,Stat.nHypothesisPushes,Stat.nQueryPushes,
        Stat.nPrefixRounds,Stat.nPrefixPops);
    CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root relational-model-prune: schema=1 enabled=%d base-model-removed=%lld ind-model-removed=%lld scanned-literals=%lld seconds=%.6f\n",
        ModelPrune,BaseModelRemoved,IndModelRemoved,ModelScanned,
        (double)TimeModel/CLOCKS_PER_SEC);
    ABC_FREE(pLitOwner); ABC_FREE(pDeps);
    Vec_IntFree(vAssumptions); Vec_IntFree(vFrozen);
    Cec_TranRelUnrollStop(&ind);
    *pnRounds=rounds;
    if ( pStat ) *pStat=Stat;
    return vStatus;
}
