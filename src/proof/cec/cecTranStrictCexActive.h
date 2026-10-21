// Query a missing target value inside the existing W-frame reset horizon.
// SAT chooses PI samples only; no recipe, proof status, or gain comes from it.
enum { CEC_TRAN_STRICT_CEX_QUERIES = 64, CEC_TRAN_STRICT_CEX_UNROLL_CAP = 500000 };

static void Cec_TranStrictCexClause( sat_solver * Sat, int * Clause, int n )
{
    int Added=sat_solver_addclause(Sat,Clause,Clause+n);
    assert(Added); // Acyclic gate equations are satisfiable for every PI vector.
    (void)Added;
}

static sat_solver * Cec_TranStrictCexCnf( Gia_Man_t * p )
{
    sat_solver * Sat=sat_solver_new();
    Gia_Obj_t * o;
    int i, a, v, z, Clause[3], x, y;
    sat_solver_setnvars(Sat,Gia_ManObjNum(p));
    Clause[0]=1; Cec_TranStrictCexClause(Sat,Clause,1); // node zero = false
    Gia_ManForEachAnd(p,o,i)
    {
        a=Gia_ObjFaninLit0p(p,o); v=Gia_ObjFaninLit1p(p,o); z=Abc_Var2Lit(i,0);
        if ( Gia_ObjIsXor(o) )
            for ( x=0; x<2; ++x ) for ( y=0; y<2; ++y )
            {
                Clause[0]=a^x; Clause[1]=v^y; Clause[2]=z^(1^x^y);
                Cec_TranStrictCexClause(Sat,Clause,3);
            }
        else
        {
            Clause[0]=z^1; Clause[1]=a; Cec_TranStrictCexClause(Sat,Clause,2);
            Clause[0]=z^1; Clause[1]=v; Cec_TranStrictCexClause(Sat,Clause,2);
            Clause[0]=z; Clause[1]=a^1; Clause[2]=v^1; Cec_TranStrictCexClause(Sat,Clause,3);
        }
    }
    return Sat;
}

static int Cec_TranStrictCexActive( Cec_TranStrictCex_t * b, Gia_Man_t * p,
    Cec_TranSim_t * Sim, Cec_TranRoot_t * Roots, int nRoots )
{
    int Ids[64], Wanted[64], Queries[64];
    int nQueries=0, nObj=Gia_ManObjNum(p), nFrames=Sim->nFrames;
    int i, j, f, r, a, v, Lit, Status, Before=Vec_PtrSize(b->vPrefixes);
    int * Map;
    Gia_Man_t * Unroll;
    Gia_Obj_t * o;
    Cbs_Man_t * Sat;
    sat_solver * Cdcl;
    abctime Start=Abc_Clock();
    if ( Before >= 64 ) return 0;
    // Existing structural root order; no circuit names or result labels.
    for ( r=0; r<nRoots; ++r )
    {
        word * Values=Cec_TranSimObj(Sim,Roots[r].iObj);
        if ( Roots[r].nMffc < 2 || (Values[0] != 0 && Values[0] != ~(word)0) ) continue;
        for ( j=1; j<Sim->nSlots; ++j ) if ( Values[j] != Values[0] ) break;
        if ( j != Sim->nSlots ) continue;
        b->ActiveLow++;
        if ( nQueries == CEC_TRAN_STRICT_CEX_QUERIES ) continue;
        Ids[nQueries]=Roots[r].iObj; Wanted[nQueries++]=Values[0] == 0;
    }
    if ( !nQueries ) return 0;
    if ( (size_t)nObj*nFrames > CEC_TRAN_STRICT_CEX_UNROLL_CAP )
    { b->ActiveSizeSkip++; return 0; }
    Unroll=Gia_ManStart(nObj*nFrames);
    Gia_ManHashStart(Unroll);
    Map=ABC_CALLOC(int,(size_t)nObj*nFrames);
    for ( f=0; f<nFrames; ++f )
    {
        int * Frame=Map+(size_t)f*nObj;
        Gia_ManForEachPi(p,o,i) Frame[Gia_ObjId(p,o)]=Gia_ManAppendCi(Unroll);
        Gia_ManForEachRo(p,o,i)
            Frame[Gia_ObjId(p,o)]=f ? Map[(size_t)(f-1)*nObj+Gia_ObjId(p,Gia_ManRi(p,i))] : 0;
        Gia_ManForEachObj1(p,o,i)
        {
            if ( Gia_ObjIsCi(o) ) continue;
            a=Abc_LitNotCond(Frame[Gia_ObjFaninId0p(p,o)],Gia_ObjFaninC0(o));
            if ( Gia_ObjIsCo(o) || Gia_ObjIsBuf(o) ) Frame[i]=a;
            else
            {
                v=Abc_LitNotCond(Frame[Gia_ObjFaninId1p(p,o)],Gia_ObjFaninC1(o));
                Frame[i]=Gia_ObjIsXor(o) ? Gia_ManHashXor(Unroll,a,v) : Gia_ManHashAnd(Unroll,a,v);
            }
        }
    }
    for ( r=0; r<nQueries; ++r )
    {
        Lit=0;
        for ( f=0; f<nFrames; ++f )
        {
            a=Abc_LitNotCond(Map[(size_t)f*nObj+Ids[r]],!Wanted[r]);
            Lit=Abc_LitNot(Gia_ManHashAnd(Unroll,Abc_LitNot(Lit),Abc_LitNot(a)));
        }
        Queries[r]=Lit;
        Gia_ManAppendCo(Unroll,Lit);
    }
    Gia_ManHashStop(Unroll);
    ABC_FREE(Map);
    Sat=b->Solver ? NULL : Cbs_ManAlloc(Unroll);
    Cdcl=b->Solver ? Cec_TranStrictCexCnf(Unroll) : NULL;
    if ( Sat ) Cbs_ManSetConflictNum(Sat,100);
    for ( r=0; r<nQueries && Vec_PtrSize(b->vPrefixes)<64; ++r )
    {
        Abc_Cex_t * c, * Old;
        Lit=Queries[r]; b->ActiveQueries++;
        if ( Lit < 2 ) Status=!Lit;
        else if ( Cdcl )
        {
            int Conflicts=sat_solver_nconflicts(Cdcl);
            int Answer=sat_solver_solve(Cdcl,&Lit,&Lit+1,100,0,0,0);
            Status=Answer==l_True ? 0 : Answer==l_False ? 1 : -1;
            b->ActiveConflicts += sat_solver_nconflicts(Cdcl)-Conflicts;
        }
        else
        {
            Status=Cbs_ManSolveLits(Sat,&Lit,1);
            b->ActiveConflicts += Cbs_ManReadConflicts(Sat);
            b->ActiveQueueCut += Status<0 && Cbs_ManReadConflicts(Sat)<=100;
        }
        if ( Status != 0 )
        {
            b->ActiveUnsat += Status == 1; b->ActiveUnknown += Status < 0;
            continue;
        }
        b->ActiveSat++;
        c=Abc_CexAlloc(0,b->nPis,nFrames); c->iFrame=nFrames-1; c->iPo=-1;
        if ( Lit >= 2 && Cdcl )
        {
            Gia_ManForEachPi(Unroll,o,i)
                if ( sat_solver_var_value(Cdcl,Gia_ObjId(Unroll,o)) ) Abc_InfoSetBit(c->pData,i);
        }
        else if ( Lit >= 2 )
        {
            Vec_Int_t * Model=Cbs_ReadModel(Sat);
            Vec_IntForEachEntry(Model,v,i)
            {
                assert(Abc_Lit2Var(v)<b->nPis*nFrames);
                if ( !Abc_LitIsCompl(v) ) Abc_InfoSetBit(c->pData,Abc_Lit2Var(v));
            }
        }
        if ( !Cec_TranStrictCexReplayTarget(p,c,Ids[r],Wanted[r]) )
        {
            b->ActiveInvalid++; Abc_CexFree(c);
            // A replay mismatch is an implementation error, never a sample.
            assert(0); continue;
        }
        b->ActiveSplit++;
        Vec_PtrForEachEntry(Abc_Cex_t *,b->vPrefixes,Old,j)
            if ( Cec_TranPatDbCexEqual(Old,c) ) break;
        if ( j<Vec_PtrSize(b->vPrefixes) ) { b->Duplicate++; Abc_CexFree(c); continue; }
        Vec_PtrPush(b->vPrefixes,c); b->Added++;
    }
    if ( Sat ) Cbs_ManStop(Sat);
    if ( Cdcl ) sat_solver_delete(Cdcl);
    Gia_ManStop(Unroll);
    b->ActiveTime += Abc_Clock()-Start;
    return Vec_PtrSize(b->vPrefixes)>Before;
}
