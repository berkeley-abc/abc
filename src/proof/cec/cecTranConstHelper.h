/** Proof-only CONST nominations from the owned original reset simulation. */
static int Cec_TranConstHelperPolicyAllowed( Cec_ParTran_t const * pPars,
    int RelMode )
{
    return pPars->fOdcProofScope && pPars->fOdcFanout && RelMode == 1 &&
        !(pPars->nExplore & 4096);
}

static int Cec_TranConstHelpersEnabled( Cec_ParTran_t * pPars )
{
    char const * Text = getenv("ABC_ODC_CONST_HELPERS");
    int Enabled;
    if ( Text && strcmp(Text,"0") && strcmp(Text,"1") )
    {
        Abc_Print(-1,"ABC_ODC_CONST_HELPERS must be 0 or 1.\n");
        exit(2);
    }
    Enabled = Text ? !strcmp(Text,"1") : Cec_TranReviewedOdc(pPars);
    if ( Enabled && !Cec_TranConstHelperPolicyAllowed(pPars,
        pPars->fOdcProofScope ? Cec_TranRelationalMode(pPars) : 0) )
    {
        Abc_Print(-1,"ABC_ODC_CONST_HELPERS=1 requires the actual ODC fanout stage, ABC_ODC_RELATIONAL_PROOF=1, and sequential proof (not CBS-only).\n");
        exit(2);
    }
    return Enabled;
}

static void Cec_TranConstHelperNominate( Gia_Man_t * p,
    Cec_TranSim_t * pSource, Cec_TranCandVec_t * pHelpers,
    Cec_TranProf_t * pProf )
{
    Gia_Obj_t * pObj;
    int i, k;
    assert(pSource->pGia == p && pSource->nSlots > 0 && !pHelpers->nSize);
    Gia_ManForEachAnd(p,pObj,i)
    {
        word const * pWords = Cec_TranSimObj(pSource,i);
        int Zero = 1, One = 1;
        Cec_TranCand_t Helper;
        pProf->nOdcConstScanned++;
        for ( k = 0; k < pSource->nSlots && (Zero || One); k++ )
        {
            Zero &= pWords[k] == 0;
            One &= pWords[k] == ~(word)0;
        }
        if ( !Zero && !One ) continue;
        assert(Zero != One);
        // Owned literal metadata has no simulation pointer, recipe or gain.
        // MFFC, profitability, candidate kind, and q do not filter this pool.
        Helper = Cec_TranCandCreateLiteral(i,One,0,CEC_TRAN_CAND_CONST,1);
        Helper.Gain = 0;
        assert(Helper.nGates == 0 && Helper.Recipe == NULL);
        Cec_TranCandVecPush(pHelpers,Helper);
        pProf->nOdcConstZero += Zero;
        pProf->nOdcConstOne += One;
    }
    assert(pProf->nOdcConstScanned == Gia_ManAndNum(p));
    assert(pHelpers->nSize == pProf->nOdcConstZero+pProf->nOdcConstOne);
    assert(pHelpers->nSize <= Gia_ManAndNum(p));
}

static void Cec_TranConstHelperPrint( Cec_TranProf_t const * pProf, int iRound )
{
    assert(pProf->nOdcConstChecked <= pProf->nOdcConstInjected);
    assert(pProf->nOdcConstChecked == pProf->nOdcConstSurvived +
        pProf->nOdcConstWithdrawn + pProf->nOdcConstUnknown);
    CEC_TRAN_VERBOSE( pProf->fVerbose || getenv("ABC_ODC_CONST_HELPERS"), "stran-root ODC CONST-helper round: schema=1 round=%d scanned=%d nominated=%d zero=%d one=%d injected=%d checked=%d survived=%d withdrawn=%d unknown=%d unconsumed=%d q-slots=0 committed=0 gain=0.\n",
        iRound+1,pProf->nOdcConstScanned,pProf->nOdcConstZero+pProf->nOdcConstOne,
        pProf->nOdcConstZero,pProf->nOdcConstOne,pProf->nOdcConstInjected,
        pProf->nOdcConstChecked,pProf->nOdcConstSurvived,pProf->nOdcConstWithdrawn,
        pProf->nOdcConstUnknown,pProf->nOdcConstInjected-pProf->nOdcConstChecked);
}
