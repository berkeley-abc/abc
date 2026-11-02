// ODC care and spatial-window observation.
// Private implementation fragment included only by cecTrans.c.

// First-level ODC observes the target only through its immediate fanouts.  For
// an ordinary AIG AND, toggling one input can change the output exactly when
// the other (possibly complemented) input is one, so the care set is the OR of
// these side-input values over all fanouts.  A direct PO/RI, XOR, buffer, or a
// recognized mux is kept fully observable.  The latter is a conservative
// over-approximation: it may lose an ODC opportunity, but cannot create one.
// This mask guides construction only.  Every committed ODC edit is separately
// proved against the complete current sequential machine.
static word * Cec_TranFirstLevelCare( Cec_TranSim_t * pSim, int iTarget,
    long long * pnCareBits )
{
    Gia_Man_t * p = pSim->pGia;
    word * pCare = ABC_CALLOC( word, pSim->nSlots );
    Gia_Obj_t * pFan;
    int f, s, iFan, iFan0, iFan1, iSideLit;
    int fFull = 0;
    assert( p->vFanoutNums && p->vFanout );
    Gia_ObjForEachFanoutStaticId( p, iTarget, iFan, f )
    {
        pFan = Gia_ManObj( p, iFan );
        if ( Gia_ObjIsCo(pFan) || !Gia_ObjIsAnd(pFan) ||
             Gia_ObjIsXor(pFan) || Gia_ObjIsBuf(pFan) ||
             Gia_ObjIsMux(p, pFan) )
        {
            fFull = 1;
            break;
        }
        iFan0 = Gia_ObjFaninId0p( p, pFan );
        iFan1 = Gia_ObjFaninId1p( p, pFan );
        if ( (iFan0 == iTarget) == (iFan1 == iTarget) )
        {
            // Duplicate/non-direct incidence is rare after hashing.  Treat it
            // as fully observable rather than relying on a special identity.
            fFull = 1;
            break;
        }
        iSideLit = iFan0 == iTarget ?
            Gia_ObjFaninLit1p(p, pFan) : Gia_ObjFaninLit0p(p, pFan);
        for ( s = 0; s < pSim->nSlots; s++ )
            pCare[s] |= Cec_TranSimLit( pSim, iSideLit, s );
    }
    if ( fFull )
        for ( s = 0; s < pSim->nSlots; s++ )
            pCare[s] = ~(word)0;
    if ( pnCareBits )
    {
        *pnCareBits = 0;
        for ( s = 0; s < pSim->nSlots; s++ )
            *pnCareBits += Abc_TtCountOnes( pCare[s] );
    }
    return pCare;
}

// Spatial TFO windows terminate at depth, every PO/RI and unsupported gate.
// vNodes includes the root; every edge leaving this region starts in vEnds.
// At the recipe encoding capacity, preserve the current node as an exit;
// never drop an outgoing path or silently truncate the proof boundary.
static int Cec_TranWindowDepth( Cec_ParTran_t * pPars )
{
    int d = (pPars->nExplore >> 28) & 3;
    return 1 << d;
}
static void Cec_TranWindowCollect( Gia_Man_t * p, int iRoot, int Depth,
    int MaxAnds, Vec_Int_t * vNodes, Vec_Int_t * vEnds, int * pOverflow )
{
    Vec_Int_t * vDepth = Vec_IntAlloc(16);
    int i, j, n, d, f, fan;
    Gia_Obj_t * pFan;
    Vec_IntClear(vNodes); Vec_IntClear(vEnds);
    Vec_IntPush(vNodes, iRoot); Vec_IntPush(vDepth, 0);
    *pOverflow = MaxAnds < 0;
    for ( i = 0; i < Vec_IntSize(vNodes); i++ )
    {
        n = Vec_IntEntry(vNodes, i); d = Vec_IntEntry(vDepth, i);
        if ( d == Depth ) { Vec_IntPushUnique(vEnds, n); continue; }
        Gia_ObjForEachFanoutStaticId(p, n, fan, f)
        {
            pFan = Gia_ManObj(p, fan);
            if ( !Gia_ObjIsAnd(pFan) || Gia_ObjIsXor(pFan) ||
                 Gia_ObjIsBuf(pFan) || Gia_ObjIsMux(p, pFan) )
            { Vec_IntPushUnique(vEnds, n); continue; }
            j = Vec_IntFind(vNodes, fan);
            if ( j >= 0 ) continue;
            if ( Vec_IntSize(vNodes) - 1 >= MaxAnds )
            { *pOverflow = 1; Vec_IntPushUnique(vEnds,n); continue; }
            Vec_IntPush(vNodes, fan); Vec_IntPush(vDepth, d+1);
        }
    }
    if ( Vec_IntSize(vEnds) == 0 )
    {
        Vec_IntClear(vNodes); Vec_IntPush(vNodes, iRoot);
        Vec_IntClear(vEnds); Vec_IntPush(vEnds, iRoot);
    }
    Vec_IntSort(vNodes, 0); Vec_IntSort(vEnds, 0);
    assert(Vec_IntEntry(vNodes, 0) == iRoot);
    Vec_IntFree(vDepth);
}
static word * Cec_TranWindowCare( Cec_TranSim_t * pSim, int iRoot,
    Cec_ParTran_t * pPars, Cec_TranProf_t * pProf )
{
    Gia_Man_t * p = pSim->pGia;
    Vec_Int_t * vNodes = Vec_IntAlloc(32), * vEnds = Vec_IntAlloc(16);
    int overflow, i, n, k0, k1, s, a, b;
    word * pValues, * pCare = ABC_CALLOC(word, pSim->nSlots);
    Cec_TranWindowCollect(p, iRoot, Cec_TranWindowDepth(pPars),
        100 - pPars->nDepNodesMax, vNodes, vEnds, &overflow);
    pValues = ABC_ALLOC(word, Vec_IntSize(vNodes) * pSim->nSlots);
    Vec_IntForEachEntry(vNodes, n, i)
    {
        Gia_Obj_t * pObj = Gia_ManObj(p, n);
        if ( n == iRoot )
        {
            for ( s = 0; s < pSim->nSlots; s++ )
                pValues[i*pSim->nSlots+s] = ~Cec_TranSimObj(pSim,n)[s];
            continue;
        }
        a = Gia_ObjFaninLit0p(p,pObj); b = Gia_ObjFaninLit1p(p,pObj);
        k0 = Vec_IntFind(vNodes, Abc_Lit2Var(a));
        k1 = Vec_IntFind(vNodes, Abc_Lit2Var(b));
        assert(k0 < i && k1 < i);
        for ( s = 0; s < pSim->nSlots; s++ )
        {
            word x = k0 < 0 ? Cec_TranSimObj(pSim,Abc_Lit2Var(a))[s] : pValues[k0*pSim->nSlots+s];
            word y = k1 < 0 ? Cec_TranSimObj(pSim,Abc_Lit2Var(b))[s] : pValues[k1*pSim->nSlots+s];
            pValues[i*pSim->nSlots+s] = (x ^ (Abc_LitIsCompl(a) ? ~(word)0 : 0)) &
                (y ^ (Abc_LitIsCompl(b) ? ~(word)0 : 0));
        }
    }
    Vec_IntForEachEntry(vEnds, n, i)
    {
        int k = Vec_IntFind(vNodes,n); assert(k >= 0);
        for ( s = 0; s < pSim->nSlots; s++ )
            pCare[s] |= pValues[k*pSim->nSlots+s] ^ Cec_TranSimObj(pSim,n)[s];
    }
    if ( pProf )
    {
        pProf->nOdcWindowRoots++;
        pProf->nOdcWindowNodes += Vec_IntSize(vNodes);
        pProf->nOdcWindowEnds += Vec_IntSize(vEnds);
        pProf->nOdcWindowOverflow += overflow;
        pProf->nOdcWindowBits += 64 * pSim->nSlots;
        for ( s = 0; s < pSim->nSlots; s++ )
            pProf->nOdcWindowCareBits += Abc_TtCountOnes(pCare[s]);
    }
    ABC_FREE(pValues); Vec_IntFree(vNodes); Vec_IntFree(vEnds);
    return pCare;
}
