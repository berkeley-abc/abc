// Strict Route3 defaults to local TFI and legal one-hop TFO divisors.
// An explicit 0 retains the exact old pool/order and only enables accounting.
static int Cec_TranLocalDomainParse( char const * pText )
{
    if ( pText == NULL ) return 2;
    if ( !strcmp(pText, "0") ) return 0;
    if ( !strcmp(pText, "1") ) return 1;
    if ( !strcmp(pText, "2") ) return 2;
    return -1;
}

static int Cec_TranLocalDomainRead()
{
    int Mode = Cec_TranLocalDomainParse(getenv("ABC_SRESUB_LOCAL_DOMAIN"));
    // The Route3 public entry rejects invalid input before graph copy/search.
    // Internal callers must obey the same contract rather than fall back.
    assert( Mode >= 0 );
    return Mode;
}

static char const * Cec_TranLocalDomainName( int Mode )
{
    assert( Mode >= 0 && Mode <= 2 );
    return Mode == 0 ? "global-earlier" : Mode == 1 ?
        "local-TFI" : "local-TFI+complete-fanin-TFO";
}

static void Cec_TranLocalDomainConfig( Cec_ParTran_t * pPars,
    Cec_TranProf_t * pProf, int fTfo, int nTfoMax )
{
    int Mode = pProf->StrictLocalDomainMode;
    int Reservoir = pPars->nConstrBaseMax ? Abc_MaxInt(
        4 * pPars->nConstrBaseMax, pPars->nConstrBaseMax + 32) : 0;
    int TfoLimit = !fTfo || Abc_ResubQualityNoTruncation() ? 0 :
        (nTfoMax ? nTfoMax : (Reservoir ? Reservoir : 256));
    Abc_Print(1, "sresub local-domain config: schema=1 mode=%d source=%s scope=Strict global-earlier=%d no-routing=%d tfo=%d K=%d B=%d reservoir-cap=%d tfo-cap=%d tfo-request=%d rank-tie=support-cardinality cursor=freeze-ordered-pool invalidation=per-snapshot proof=unchanged\n",
        Mode, Cec_TranLocalDomainName(Mode), !Mode, !Mode, fTfo,
        pPars->nConstrMax, pPars->nConstrBaseMax, Reservoir, TfoLimit, nTfoMax);
    fflush(stdout);
    Abc_Print(1,"sresub cut-domain config: schema=1 leaves=%d scope=Strict algorithm=%s membership=leaves+internal tfo=one-hop-shell proof=unchanged\n",
        pProf->StrictCutSize, pProf->StrictCutSize == 4 &&
        (!getenv("ABC_SRESUB_CUT_SELECTOR") || !strcmp(getenv("ABC_SRESUB_CUT_SELECTOR"),"drw4")) ?
        "original-drw4" : "resub-reconv-level-one");
}

// Counts describe actual work, including repeated collection/ranking on a
// continuation page.  Bound is the cursor-restored pool consumed by discovery;
// post-B is the fresh selection or, when PAGE skips selection, the frozen pool.
// Ranked counts scored reservoir items after RankBound pruning; PAGE scores zero.
static void Cec_TranLocalDomainRecord( Cec_TranProf_t * pProf, int Root,
    int Wave, Cec_TranTfoStats_t const * pStats, int Collected,
    int RankInput, int PostB, int Bound, int fCursorRestored, int Ranked )
{
    if ( !pProf->StrictLocalDomainProfile ) return;
    assert( Collected == pStats->nTfi + pStats->nAdded + pStats->nGlobal );
    assert( RankInput <= Collected && PostB <= RankInput );
    pProf->nLocalDomainCalls++;
    pProf->nLocalDomainFirst += Wave == 0;
    pProf->nLocalDomainCont += Wave != 0;
    pProf->nLocalDomainTfi += pStats->nTfi;
    pProf->nLocalDomainTfo += pStats->nAdded;
    pProf->nLocalDomainGlobal += pStats->nGlobal;
    pProf->nLocalDomainCollected += Collected;
    pProf->nLocalDomainRankInput += RankInput;
    pProf->nLocalDomainRanked += Ranked;
    pProf->nLocalDomainPostB += PostB;
    pProf->nLocalDomainBound += Bound;
    if ( pProf->PreproofTrace )
    {
        Abc_Print(1, "sresub local-domain pool: schema=1 mode=%d source=%s scope=Strict round=%d wave=%d root=%d tfi=%lld tfo=%lld global=%lld collected=%d rank-input=%d ranked=%d post-B=%d bound=%d cursor-restored=%d\n",
            pProf->StrictLocalDomainMode, Cec_TranLocalDomainName(pProf->StrictLocalDomainMode),
            pProf->PreproofRound, Wave, Root, pStats->nTfi, pStats->nAdded,
            pStats->nGlobal, Collected, RankInput, Ranked, PostB, Bound, fCursorRestored);
        fflush(stdout);
    }
}
