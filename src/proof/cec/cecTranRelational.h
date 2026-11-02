// ODC candidate relations as explicit k-inductive predicates.
// The scalar reference below unrolls the original transition at every frame.
// Route3 defaults to the signed-basis/Frozen-H engine selected later in this
// file: it materializes a substituted SRM with every residual equality kept.
// The scalar reference removes only its queried relation. The signed basis
// can remove other predicates
// only after complete scalar model replay, never from sampled classes.
// This is the standard conjunctive invariant (Houdini) fixed point, not a
// bounded-model-checking proof and not a retry of a failed correspondence run.

static int Cec_TranRelationalMode( Cec_ParTran_t const * pPars )
{
    char const * s = getenv("ABC_ODC_RELATIONAL_PROOF");
    // &sresub is the explicit relational-Strict contract.  Do not let a
    // stale ODC diagnostic environment variable silently change its proof
    // engine in either Strict or the reviewed ODC continuation.
    if ( pPars->fRoute3 ) return 1;
    if ( !s ) return pPars->fRoute1 || pPars->fStran2Guide;
    if ( !strcmp(s, "0") ) return 0;
    if ( !strcmp(s, "1") ) return 1;
    if ( !strcmp(s, "2") ) return 2; // observe both, consume legacy status
    Abc_Print( -1, "stran-quality-invalid-option: ABC_ODC_RELATIONAL_PROOF must be 0, 1 or 2\n" );
    exit( 2 );
    return 0;
}

// Induction uses one additional frame. Check before k+1 and before any
// frame-major int-sized map is allocated; prepared batches can be larger
// than the command's input graph.
static int Cec_TranRelFramesSupported( Gia_Man_t * p, int nFrames )
{
    return nFrames > 0 && nFrames < INT_MAX &&
        Gia_ManObjNum(p) <= INT_MAX / (nFrames + 1);
}

typedef struct Cec_TranRelUnroll_t_ {
    Gia_Man_t * p;
    Vec_Int_t * vQueries; // frame-major XOR(root, recipe)
    sat_solver * pSat;
    int nRelations;
    int nFrames;
    abctime timeUnroll;
    abctime timeCnf;
} Cec_TranRelUnroll_t;

static void Cec_TranRelClause( sat_solver * pSat, int * pLits, int nLits )
{
    // Do not put the insertion inside assert: NDEBUG must preserve semantics.
    int ok = sat_solver_addclause( pSat, pLits, pLits + nLits );
    assert( ok );
    if ( !ok ) abort(); // only acyclic gate definitions are added
}

static Cec_TranRelUnroll_t Cec_TranRelUnroll( Gia_Man_t * p,
    Vec_Int_t * vPairs, int nFrames, int fReset )
{
    Cec_TranRelUnroll_t u;
    Gia_Obj_t * o;
    int * old = ABC_CALLOC( int, Gia_ManObjNum(p) );
    int * cur = ABC_CALLOC( int, Gia_ManObjNum(p) );
    int f, i, a, b, q, z, clause[3], x, y;
    int NativeXor = Cec_TranStrictCexOption("ABC_REL_NATIVE_XOR",0,1);
    abctime clk = Abc_Clock();
    assert( nFrames > 0 && !(Vec_IntSize(vPairs) & 1) );
    memset( &u, 0, sizeof(u) );
    u.nRelations = Vec_IntSize(vPairs) / 2;
    u.nFrames = nFrames;
    u.vQueries = Vec_IntAlloc( 0 );
    u.p = Gia_ManStart( Gia_ManObjNum(p) );
    if ( NativeXor ) u.p->pMuxes=ABC_CALLOC(unsigned,u.p->nObjsAlloc);
    Gia_ManHashStart( u.p );
    for ( f = 0; f < nFrames; f++ )
    {
        int * tmp;
        cur[0] = 0;
        Gia_ManForEachPi( p, o, i )
            cur[Gia_ObjId(p,o)] = Gia_ManAppendCi( u.p );
        Gia_ManForEachRo( p, o, i )
            cur[Gia_ObjId(p,o)] = f ? old[Gia_ObjId(p,Gia_ManRi(p,i))] :
                fReset ? 0 : Gia_ManAppendCi( u.p );
        Gia_ManForEachObj1( p, o, i )
        {
            if ( Gia_ObjIsCi(o) ) continue;
            a = Abc_LitNotCond( cur[Gia_ObjFaninId0p(p,o)], Gia_ObjFaninC0(o) );
            if ( Gia_ObjIsCo(o) || Gia_ObjIsBuf(o) ) cur[i] = a;
            else
            {
                b = Abc_LitNotCond( cur[Gia_ObjFaninId1p(p,o)], Gia_ObjFaninC1(o) );
                cur[i] = Cec_TranHashGate( u.p, o, a, b );
            }
        }
        for ( i = 0; i < u.nRelations; i++ )
        {
            a = Vec_IntEntry(vPairs,2*i); b = Vec_IntEntry(vPairs,2*i+1);
            a = Abc_LitNotCond(cur[Abc_Lit2Var(a)], Abc_LitIsCompl(a));
            b = Abc_LitNotCond(cur[Abc_Lit2Var(b)], Abc_LitIsCompl(b));
            // Exact query only: one XOR variable/four clauses instead of
            // three AND gates. Original T and every obligation are unchanged.
            q = NativeXor ? Gia_ManHashXorReal(u.p,a,b) : Gia_ManHashXor(u.p,a,b);
            Vec_IntPush(u.vQueries,q);
        }
        tmp = old; old = cur; cur = tmp;
    }
    ABC_FREE(old); ABC_FREE(cur);
    Gia_ManHashStop(u.p);
    u.timeUnroll = Abc_Clock() - clk;
    clk = Abc_Clock();
    u.pSat = sat_solver_new();
    sat_solver_setnvars(u.pSat,Gia_ManObjNum(u.p));
    clause[0] = 1; Cec_TranRelClause(u.pSat,clause,1); // false constant
    Gia_ManForEachAnd(u.p,o,i)
    {
        a=Gia_ObjFaninLit0p(u.p,o); b=Gia_ObjFaninLit1p(u.p,o);
        z=Abc_Var2Lit(i,0);
        if ( Gia_ObjIsXor(o) )
            for ( x=0; x<2; x++ ) for ( y=0; y<2; y++ )
            {
                clause[0]=a^x; clause[1]=b^y; clause[2]=z^(1^x^y);
                Cec_TranRelClause(u.pSat,clause,3);
            }
        else
        {
            clause[0]=z^1; clause[1]=a; Cec_TranRelClause(u.pSat,clause,2);
            clause[0]=z^1; clause[1]=b; Cec_TranRelClause(u.pSat,clause,2);
            clause[0]=z; clause[1]=a^1; clause[2]=b^1;
            Cec_TranRelClause(u.pSat,clause,3);
        }
    }
    u.timeCnf = Abc_Clock() - clk;
    return u;
}

static void Cec_TranRelUnrollStop( Cec_TranRelUnroll_t * u )
{
    sat_solver_delete(u->pSat);
    Vec_IntFree(u->vQueries);
    Gia_ManStop(u->p);
}

// Result: 1 proved, 0 refuted by base/induction, -1 solver budget unknown.
// Induction SAT is NOT a reachable counterexample and is never fed to Guide.
static Vec_Int_t * Cec_TranRelationalSeparateProve( Gia_Man_t * p,
    Vec_Int_t * vPairs, Cec_ParTran_t * pPars, int * pnRounds )
{
    int n = Vec_IntSize(vPairs)/2, k = pPars->nFrames;
    Vec_Int_t * vStatus = Vec_IntStartFull(n);
    Cec_TranRelUnroll_t base, ind;
    int i, f, q, status, changed=1, rounds=0, alive=0, incomplete=0;
    int baseSat=0, baseUnknown=0, indSat=0, indUnknown=0;
    long long baseQueries=0, indQueries=0;
    long long guardClauses=0;
    int baseVars, baseClauses, indVars, indClauses, baseConflicts, indConflicts;
    abctime timeBaseSolve=0, timeIndSolve=0, timeGuards=0, timeStop=0, clkPhase;
    abctime clk = Abc_Clock();
    assert(k > 0);
    base = Cec_TranRelUnroll(p,vPairs,k,1);
    if ( pPars->fVerbose )
        CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root relational-setup: schema=1 phase=base frames=%d relations=%d vars=%d clauses=%d unroll-sec=%.6f cnf-sec=%.6f\n",
            k,n,sat_solver_nvars(base.pSat),sat_solver_nclauses(base.pSat),
            (double)base.timeUnroll/CLOCKS_PER_SEC,(double)base.timeCnf/CLOCKS_PER_SEC);
    for ( i=0; i<n; i++ )
    {
        Vec_IntWriteEntry(vStatus,i,1);
        for ( f=0; f<k; f++ )
        {
            q = Vec_IntEntry(base.vQueries,f*n+i);
            baseQueries++;
            clkPhase = pPars->fVerbose ? Abc_Clock() : 0;
            status = sat_solver_solve(base.pSat,&q,&q+1,pPars->nBTLimit,0,0,0);
            if ( pPars->fVerbose ) timeBaseSolve += Abc_Clock() - clkPhase;
            if ( status == l_False ) continue;
            Vec_IntWriteEntry(vStatus,i,status==l_True ? 0 : -1);
            baseSat += status==l_True; baseUnknown += status==l_Undef;
            break;
        }
        alive += Vec_IntEntry(vStatus,i)==1;
    }
    baseVars = sat_solver_nvars(base.pSat);
    baseClauses = sat_solver_nclauses(base.pSat);
    baseConflicts = sat_solver_nconflicts(base.pSat);
    clkPhase = Abc_Clock();
    Cec_TranRelUnrollStop(&base);
    timeStop += Abc_Clock() - clkPhase;
    ind = Cec_TranRelUnroll(p,vPairs,k+1,0);
    indVars = sat_solver_nvars(ind.pSat);
    indClauses = sat_solver_nclauses(ind.pSat);
    if ( pPars->fVerbose )
        CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root relational-setup: schema=1 phase=ind frames=%d relations=%d vars=%d clauses=%d unroll-sec=%.6f cnf-sec=%.6f\n",
            k+1,n,indVars,indClauses,(double)ind.timeUnroll/CLOCKS_PER_SEC,
            (double)ind.timeCnf/CLOCKS_PER_SEC);
    // A removed hypothesis invalidates earlier UNSAT answers in that round.
    // Recheck every surviving obligation until a complete unchanged round.
    // Assumptions, not permanent clauses, allow hypotheses to be withdrawn.
    while ( pPars->nStepsMax < 0 || rounds < pPars->nStepsMax )
    {
        int guard, clause[2];
        clkPhase = Abc_Clock();
        changed=0; rounds++;
        guard = Abc_Var2Lit(sat_solver_nvars(ind.pSat),0);
        sat_solver_setnvars(ind.pSat,sat_solver_nvars(ind.pSat)+1);
        // One fresh round activation represents the entire current conjunction.
        // Old activations are unassumed and can be false.  No removed predicate
        // remains a permanent hypothesis, and each SAT query has two literals.
        for ( f=0; f<k; f++ ) for ( i=0; i<n; i++ )
            if ( Vec_IntEntry(vStatus,i)==1 )
            {
                clause[0]=guard^1;
                clause[1]=Abc_LitNot(Vec_IntEntry(ind.vQueries,f*n+i));
                Cec_TranRelClause(ind.pSat,clause,2);
                guardClauses++;
            }
        timeGuards += Abc_Clock() - clkPhase;
        for ( i=0; i<n; i++ )
        {
            int assumptions[2];
            if ( Vec_IntEntry(vStatus,i)!=1 ) continue;
            assumptions[0]=guard;
            assumptions[1]=Vec_IntEntry(ind.vQueries,k*n+i);
            indQueries++;
            clkPhase = pPars->fVerbose ? Abc_Clock() : 0;
            status = sat_solver_solve(ind.pSat,assumptions,assumptions+2,
                pPars->nBTLimit,0,0,0);
            if ( pPars->fVerbose ) timeIndSolve += Abc_Clock() - clkPhase;
            if ( status==l_False ) continue;
            Vec_IntWriteEntry(vStatus,i,status==l_True ? 0 : -1);
            indSat += status==l_True; indUnknown += status==l_Undef;
            changed=1; alive--;
        }
        if ( !changed || !alive ) break;
    }
    // A base certificate or a partial induction round is never a proof.
    // Preserve the caller's explicit step budget even in the research lane.
    if ( changed && alive )
    {
        incomplete=alive;
        for(i=0;i<n;i++) if(Vec_IntEntry(vStatus,i)==1)
            Vec_IntWriteEntry(vStatus,i,-1);
        alive=0;
    }
    assert(rounds <= n+1);
    CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root relational-proof: schema=1 depth=%d relations=%d proved=%d rounds=%d base-queries=%lld base-sat=%d base-unknown=%d ind-queries=%lld ind-sat=%d ind-unknown=%d incomplete=%d seconds=%.6f\n",
        k,n,alive,rounds,baseQueries,baseSat,baseUnknown,indQueries,indSat,indUnknown,incomplete,
        (double)(Abc_Clock()-clk)/CLOCKS_PER_SEC);
    indConflicts = sat_solver_nconflicts(ind.pSat);
    clkPhase = Abc_Clock();
    Cec_TranRelUnrollStop(&ind);
    timeStop += Abc_Clock() - clkPhase;
    if ( pPars->fVerbose )
        CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root relational-cost: schema=1 depth=%d relations=%d base-vars=%d base-clauses=%d ind-vars=%d ind-clauses=%d guards=%d guard-clauses=%lld base-conflicts=%d ind-conflicts=%d base-unroll-sec=%.6f ind-unroll-sec=%.6f base-cnf-sec=%.6f ind-cnf-sec=%.6f base-sat-sec=%.6f ind-sat-sec=%.6f guard-sec=%.6f stop-sec=%.6f\n",
            k,n,baseVars,baseClauses,indVars,indClauses,rounds,guardClauses,
            baseConflicts,indConflicts,(double)base.timeUnroll/CLOCKS_PER_SEC,
            (double)ind.timeUnroll/CLOCKS_PER_SEC,(double)base.timeCnf/CLOCKS_PER_SEC,
            (double)ind.timeCnf/CLOCKS_PER_SEC,(double)timeBaseSolve/CLOCKS_PER_SEC,
            (double)timeIndSolve/CLOCKS_PER_SEC,(double)timeGuards/CLOCKS_PER_SEC,
            (double)timeStop/CLOCKS_PER_SEC);
    *pnRounds=rounds;
    return vStatus;
}

#include "cecTranRelationalBasis.h"
#include "cecTranRelationalModel.h"
#include "cecTranRelationalCore.h"
#include "cecTranOdcLegacySrm.h"

// An explicit ODC override does not change Strict's signed-basis selection.
// Route3 Strict defaults to lazy basis for SRM; explicit BASIS is preserved.
// ODC keeps its existing core selection independently of Strict's default.
// Explicit zero selects the original scalar ODC engine as a paired control.
static int Cec_TranRelationalBackend( Cec_ParTran_t const * pPars )
{
    char const * s=getenv("ABC_STRAN_ODC_CORE");
    int basis=Cec_TranRelationalBasisMode();
    if ( pPars->fRoute3 && !pPars->fOdcProofScope && !getenv("ABC_STRAN_RELATIONAL_BASIS") )
        basis=2;
    if ( pPars->fRoute3 && pPars->fOdcProofScope && Cec_TranFrozenOdcSolverOption() )
        return Cec_TranFrozenOdcSolverOption()==1 ? 6 : 5;
    if ( !s ) return basis;
    if ( strcmp(s,"0") && strcmp(s,"1") && strcmp(s,"2") )
    {
        Abc_Print(-1,"ABC_STRAN_ODC_CORE must be 0, 1 or 2\n");
        exit(2);
    }
    if ( !pPars->fOdcProofScope ) return basis;
    return !strcmp(s,"0") ? 0 : !strcmp(s,"1") ? 3 : 4;
}

static Vec_Int_t * Cec_TranRelationalProve( Gia_Man_t * p,
    Vec_Int_t * vPairs, Cec_ParTran_t * pPars, int * pnRounds )
{
    int backend=Cec_TranRelationalBackend(pPars);
    if ( !Cec_TranRelFramesSupported(p, pPars->nFrames) )
    {
        Abc_Print(-1, "sresub proof skipped: induction depth exceeds the supported prepared-graph unrolling size.\n");
        *pnRounds = 0;
        // Retain existing complete certificates only; every new obligation
        // is UNKNOWN. The caller still owns and releases the prepared graph.
        return Cec_TranSeqBudgetUnproved(Vec_IntSize(vPairs) / 2);
    }
    if ( pPars->fVerbose )
        CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root relational-dispatch: schema=1 scope=%s backend=%d depth=%d relations=%d\n",
            pPars->fOdcProofScope ? "odc" : "strict",backend,pPars->nFrames,Vec_IntSize(vPairs)/2);
    if ( backend==6 )
        return Cec_TranOdcLegacySrmProve(p,vPairs,pPars,pnRounds);
    if ( backend==5 )
    {
        // Pairs are materialized exit predicates (including factored care
        // masks) and separately withdrawn helpers, never an invented root
        // equality. The original RI functions and caller's
        // all-exits/compatible-window commit checks remain authoritative.
        assert(pPars->fRoute3 && pPars->fOdcProofScope &&
            Cec_TranRelClosedCurrent==NULL && Cec_TranRelObserveCurrent==NULL);
        return Cec_TranRelationalLazyBasisEngine(p,vPairs,pPars,pnRounds,3);
    }
    if ( backend>=3 )
    {
        assert(pPars->fOdcProofScope && Cec_TranRelClosedCurrent==NULL &&
            Cec_TranRelObserveCurrent==NULL);
        return Cec_TranRelationalProveCore(p,vPairs,pPars,pnRounds,NULL,backend==4);
    }
    if(backend==2)
        return Cec_TranRelationalLazyBasisProve(p,vPairs,pPars,pnRounds);
    return backend==1 ?
        Cec_TranRelationalBasisProve(p,vPairs,pPars,pnRounds) :
        Cec_TranRelationalSeparateProve(p,vPairs,pPars,pnRounds);
}
