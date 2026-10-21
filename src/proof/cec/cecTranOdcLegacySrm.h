// Historical CEC SRM comparison on one complete prepared ODC relation batch.
// Prepared owns this fresh plain-AIG graph and frees the seeded/refined classes.
// Its PI proxies, exit/care predicates, helper pairs and original RIs are used
// verbatim. This adapter does not accept a second proof call on the same graph.
#define CEC_ODC_LEGACY_REQUIRE(C) do { if (!(C)) { \
    Abc_Print(-1,"Assertion legacy ODC SRM invariant failed at %s:%d: %s\n",__FILE__,__LINE__,#C); \
    abort(); } } while (0)

static Vec_Int_t * Cec_TranOdcLegacySrmProve( Gia_Man_t * p,
    Vec_Int_t * pairs, Cec_ParTran_t const * pars, int * pnRounds )
{
    Cec_ParCor_t cor; Gia_Obj_t * o;
    Vec_Int_t * status=Vec_IntStartFull(Vec_IntSize(pairs)/2);
    int i,lit,ret,completed,proved=0;
    abctime started=Abc_Clock(),setup;
    CEC_ODC_LEGACY_REQUIRE(pars->fRoute3 && pars->fOdcProofScope && !(Vec_IntSize(pairs)&1));
    CEC_ODC_LEGACY_REQUIRE(!Cec_TranRelClosedCurrent && !Cec_TranRelObserveCurrent && !Cec_TranSeqBudgetCurrent);
    CEC_ODC_LEGACY_REQUIRE(!p->pReprs && !p->pNexts);
    // CEC's original speculative unroller handles plain ANDs and ROs.
    // BuildRootBatch already lowers typed gates and wraps PI endpoints.
    Gia_ManForEachAnd(p,o,i)
        CEC_ODC_LEGACY_REQUIRE(!Gia_ObjIsXor(o) && !Gia_ObjIsBuf(o) && !Gia_ObjIsMux(p,o));
    Vec_IntForEachEntry(pairs,lit,i)
    {
        CEC_ODC_LEGACY_REQUIRE(lit>=0 && Abc_Lit2Var(lit)<Gia_ManObjNum(p));
        o=Gia_ManObj(p,Abc_Lit2Var(lit));
        CEC_ODC_LEGACY_REQUIRE(!Gia_ObjIsCo(o) &&
            (!Gia_ObjIsCi(o) || Gia_ObjCioId(o)>=Gia_ManPiNum(p)));
    }
    Gia_ManSetPhase(p);
    p->pReprs=ABC_CALLOC(Gia_Rpr_t,Gia_ManObjNum(p));
    Gia_ManForEachObj(p,o,i)Gia_ObjSetRepr(p,i,GIA_VOID);
    Gia_ManCreateValueRefs(p);
    Cec_TranSeedRootClasses(p,pairs);
    p->pNexts=Gia_ManDeriveNexts(p);
    Cec_ManCorSetDefaultParams(&cor);
    cor.nFrames=pars->nFrames; cor.nBTLimit=pars->nBTLimit;
    cor.nStepsMax=pars->nStepsMax; cor.nConfTotal=0;
    setup=Abc_Clock()-started;
    ret=Cec_ManLSCorrespondenceClasses(p,&cor);
    completed=ret && cor.fCompleted;
    *pnRounds=cor.nRoundsDone;
    if(completed)for(i=0;i<Vec_IntSize(status);++i)
        if(Cec_TranRootBatchPairProved(p,Vec_IntEntry(pairs,2*i),Vec_IntEntry(pairs,2*i+1)))
        {Vec_IntWriteEntry(status,i,1);++proved;}
    // A removed class may come from SAT or per-output budget UNKNOWN, even
    // after convergence. Keep every unproved relation at -1 rather than
    // inventing a SAT-refutation status for Prepared's helper accounting.
    if(pars->fVerbose)
    {
        Abc_Print(1,"stran-root odc-legacy-srm: schema=1 relations=%d proved=%d unproved=%d completed=%d rounds=%d seconds=%.6f setup-sec=%.6f backend=legacy-srm sat-refutations=unavailable unknown-splits=unavailable\n",
            Vec_IntSize(status),proved,Vec_IntSize(status)-proved,completed,*pnRounds,
            (double)(Abc_Clock()-started)/CLOCKS_PER_SEC,(double)setup/CLOCKS_PER_SEC);
        fflush(stdout);
    }
    return status;
}
#undef CEC_ODC_LEGACY_REQUIRE
