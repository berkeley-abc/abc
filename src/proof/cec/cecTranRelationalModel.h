// Exact eager-query SAT model withdrawal, frozen from 517615384.
// Only a definite literal value from the just-returned SAT model may refute
// another relation. In particular, an unassigned complemented literal is not
// evidence of a true query. No SAT model is retained across solves or batches.
static int Cec_TranRelModelLit( sat_solver * pSat, int Lit )
{
    int Value;
    assert(Abc_Lit2Var(Lit) < sat_solver_nvars(pSat));
    Value = pSat->model[Abc_Lit2Var(Lit)];
    if ( Value != l_True && Value != l_False ) return -1;
    return (Value == l_True) ^ Abc_LitIsCompl(Lit);
}

// A model satisfying the current entire hypothesis and violating R also
// violates R under every smaller hypothesis. Withdraw all such predicates,
// but still reprove every survivor in a complete unchanged induction round.
// In reset base, any violated checked frame is already a reachable witness.
static int Cec_TranRelModelWithdraw( Cec_TranRelUnroll_t * u,
    Vec_Int_t * vStatus, int FirstFrame, int nFrames, long long * pnScanned )
{
    int i, f, Removed = 0;
    for ( i = 0; i < u->nRelations; ++i )
    {
        if ( Vec_IntEntry(vStatus,i) != 1 ) continue;
        for ( f = FirstFrame; f < FirstFrame+nFrames; ++f )
        {
            int Query = Vec_IntEntry(u->vQueries,f*u->nRelations+i);
            ++*pnScanned;
            if ( Cec_TranRelModelLit(u->pSat,Query) != 1 ) continue;
            Vec_IntWriteEntry(vStatus,i,0);
            ++Removed;
            break;
        }
    }
    return Removed;
}
