// Commit draining and stable profile emission.
// Private implementation fragment included only by cecTrans.c.

// Drain the proved pool to a commit fixed point without rediscovering or
// re-proving candidates.  Each iteration is one commit wave: validate every
// deferred certificate on the current graph, evaluate frozen DAG-aware gain,
// select one conflict-free batch, commit it, and remap the remainder.  Thus an
// overlap only delays a candidate to the next wave; it never discards it.
static Gia_Man_t * Cec_TranDrainProvedCommits( Gia_Man_t * p,
    Cec_ParTran_t * pPars, Cec_TranCandVec_t * pHistory,
    int iEpoch, int iPhase, int * pnBatches )
{
    static char const * pPhase[2] = { "comb", "seq" };
    int nBatches = 0, nInvalidTotal = 0;
    assert( iPhase == 0 || iPhase == 1 );
    while ( pHistory->nSize )
    {
        abctime clkTotal = Abc_Clock(), clk;
        Cec_TranProf_t Prof = {0};
        Cec_TranCandVec_t HistoryLive = {0}, Proved = {0};
        Cec_TranCandVec_t Selected = {0}, Carry = {0};
        Cec_TranPatDb_t * pDb;
        Cec_TranSim_t * pSim;
        Gia_Man_t * pNext;
        Vec_Int_t * vMffc = Vec_IntAlloc( 128 );
        Vec_Int_t * vSupport = Vec_IntAlloc( 32 );
        char * pMffc = ABC_CALLOC( char, Gia_ManObjNum(p) );
        char * pSolved = ABC_CALLOC( char, Gia_ManObjNum(p) );
        char * pCovered = ABC_CALLOC( char, Gia_ManObjNum(p) );
        char * pUsed = ABC_CALLOC( char, Gia_ManObjNum(p) );
        int i, nSelected = 0, nBefore = Gia_ManAndNum( p );

        // The simulation is only a structural/signature guard for certificates
        // remapped through cleanup.  This loop performs no candidate discovery
        // and makes no proof calls.
        Prof.fVerbose = pPars->fVerbose;
        clk = Abc_Clock();
        pDb = Cec_TranPatDbStart( p, 0 );
        Gia_ManCreateRefs( p );
        pSim = iPhase == 0 && pPars->fCombFreeDiscovery ?
            Cec_TranSimStartFreeCiDiscovery( p, pPars ) :
            Cec_TranSimStart( p, pPars, pDb );
        assert( iPhase != 0 || !pPars->fCombFreeDiscovery ||
                pSim->pState == NULL );
        if ( iPhase == 0 && pPars->fCombFreeDiscovery && pPars->fVerbose )
            CEC_TRAN_VERBOSE( pPars->fVerbose, "resub-comb closure-signature: source=independent-PI/RO history=%d slots=%d.\n",
                pHistory->nSize, pSim->nSlots );
        Prof.timeRootSimSig += Abc_Clock() - clk;
        clk = Abc_Clock();
        for ( i = 0; i < pHistory->nSize; i++ )
        {
            Cec_TranCand_t Cand = pHistory->pArray[i];
            assert(Cand.nProofStage == 1 || Cand.nProofStage == 2);
            if ( !Cec_TranProofHistoryTopoValid(p, &Cand) ||
                 !Cec_TranRecipeStructurallyValid(pSim, &Cand) ||
                 !Cec_TranRecipeMatchesRoot(pSim, &Cand, NULL) )
            {
                Prof.nHistoryTriedInvalidated++;
                continue;
            }
            Cand.nStatus = Cand.nProofStage == 1 ?
                CEC_TRAN_STATE_PROVED_COMB : CEC_TRAN_STATE_PROVED_SEQ;
            if ( !Cec_TranCandVecContains(&HistoryLive, &Cand) )
                Cec_TranCandVecPush( &HistoryLive, Cand );
            if ( !Cec_TranCandVecContains(&Proved, &Cand) )
                Cec_TranCandVecPush( &Proved, Cand );
        }
        Prof.timeRootRefresh += Abc_Clock() - clk;
        clk = Abc_Clock();
        if ( Proved.nSize )
            nSelected = Cec_TranRootConsumeProved( p, &Proved,
                pCovered, pUsed, pSolved, pMffc, vMffc, vSupport,
                &Selected, &Prof );
        Prof.timeRootPostSelect += Abc_Clock() - clk;
        for ( i = 0; i < HistoryLive.nSize; i++ )
            if ( !Cec_TranCandVecContains(&Selected,
                    HistoryLive.pArray + i) )
                Cec_TranCandVecPush( &Carry, HistoryLive.pArray[i] );

        // Commit may stop p, so all snapshot-owned guards are released first.
        Cec_TranSimStop( pSim );
        Cec_TranPatDbStop( pDb );
        pNext = Cec_TranCommitSelectedRootOnly( p, &Selected, pPars,
            &Prof, &Carry, pHistory );
        p = pNext;
        ABC_FREE( p->pRefs );
        nInvalidTotal += Prof.nHistoryTriedInvalidated;
        if ( nSelected )
        {
            nBatches++;
            CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root commit closure: epoch=%d phase=%s wave=%d selected=%d AND=%d->%d gain=%d deferred=%d.\n",
                iEpoch + 1, pPhase[iPhase], nBatches, nSelected,
                nBefore, Gia_ManAndNum(p), nBefore - Gia_ManAndNum(p),
                pHistory->nSize );
        }

        Cec_TranCandVecStop( &HistoryLive );
        Cec_TranCandVecStop( &Proved );
        Cec_TranCandVecStop( &Selected );
        Cec_TranCandVecStop( &Carry );
        Vec_IntFree( vMffc );
        Vec_IntFree( vSupport );
        ABC_FREE( pMffc );
        ABC_FREE( pSolved );
        ABC_FREE( pCovered );
        ABC_FREE( pUsed );
        Prof.timeTotal = Abc_Clock() - clkTotal;
        if ( !nSelected )
            break;
    }
    *pnBatches = nBatches;
    CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root commit closure fixed point: epoch=%d phase=%s batches=%d deferred=%d invalidated=%d.\n",
        iEpoch + 1, pPhase[iPhase], nBatches, pHistory->nSize,
        nInvalidTotal );
    return p;
}
