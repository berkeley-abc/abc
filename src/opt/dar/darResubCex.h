/* Exact high-coordinate columns, learned only from real predicate failures.
   All state belongs to one immutable pair-pool build; physical ordinals stay
   unchanged. The original full predicate and COST still accept candidates. */
struct Dar_ResubCex_t_
{
    unsigned Seen[2][32], Words[2];
    word * Cover[2];
    long long Builds, Queries, Columns, PairVisits, ApplicabilityWords, IntersectionWords;
    long long Predicates, Rejected, Exact, PredicateWords, QueryAudits, RefineAudits, Invalid;
};

static void Dar_ResubCexStart( Dar_Resub_t * p )
{
    p->fCexColumns = Dar_ResubReuseOption("ABC_DRW_CEX_COLUMNS",
        p->nLeavesMax == 10 && p->fIndex &&
        p->pPars && p->pPars->fUpdateLevel);
    p->fCexCheck = Dar_ResubReuseEnabled("ABC_DRW_CEX_COLUMNS_CHECK");
    if ( !p->fCexColumns || !p->fIndex || p->nWords <= 2 ) return;
    p->pCex = ABC_CALLOC(Dar_ResubCex_t, 1);
    /* Uninitialized columns are never read: publish Seen only after filling
       all active ordinal words. Rebuild clears Seen, not the whole storage. */
    p->pCex->Cover[0] = ABC_ALLOC(word, (32*p->nWords-64)*DAR_RS_INDEX_WORDS);
    p->pCex->Cover[1] = ABC_ALLOC(word, (32*p->nWords-64)*DAR_RS_INDEX_WORDS);
}

static void Dar_ResubCexStop( Dar_Resub_t * p )
{
    Dar_ResubCex_t zero = {0}, * s = p->pCex ? p->pCex : &zero;
    if ( p->fProfile && p->fCexColumns )
        printf("DAR_CEX_COLUMNS enabled=1 active=%d check=%d cut=%d words32=%d builds=%lld queries=%lld columns=%lld pool_pair_visits=%lld applicability_words=%lld intersection_words=%lld full_predicates=%lld full_rejected=%lld full_exact=%lld predicate_words32=%lld query_audits=%lld refine_audits=%lld invalid=%lld\n",
            p->pCex != NULL, p->fCexCheck, p->nLeavesMax, p->nWords,
            s->Builds, s->Queries, s->Columns, s->PairVisits, s->ApplicabilityWords, s->IntersectionWords,
            s->Predicates, s->Rejected, s->Exact, s->PredicateWords, s->QueryAudits, s->RefineAudits, s->Invalid);
    if ( !p->pCex ) return;
    ABC_FREE(p->pCex->Cover[0]); ABC_FREE(p->pCex->Cover[1]); ABC_FREE(p->pCex);
}

static void Dar_ResubCexBuild( Dar_Resub_t * p, int fUP )
{
    memset(p->pCex->Seen[!fUP], 0, sizeof(p->pCex->Seen[!fUP]));
    p->pCex->Words[!fUP] = 0;
    p->pCex->Builds++;
}

/* NULL second operand denotes one signed literal. Two signed operands use
   FIRST's pair encoding, including the special double-complement OR code. */
static unsigned Dar_ResubCexOuter( Aig_Obj_t * a, Aig_Obj_t * b, int w )
{
    unsigned value;
    if ( b ) return Dar_ResubPairWord(a,b,w);
    value = ((unsigned *)Aig_Regular(a)->pData)[w];
    return Aig_IsComplement(a) ? ~value : value;
}

static unsigned Dar_ResubCexPair( Dar_Resub_t * p, int fUP, int i, int w )
{
    Vec_Ptr_t * v0 = fUP ? p->vDivs2UP0 : p->vDivs2UN0;
    Vec_Ptr_t * v1 = fUP ? p->vDivs2UP1 : p->vDivs2UN1;
    return Dar_ResubPairWord((Aig_Obj_t *)Vec_PtrEntry(v0,i), (Aig_Obj_t *)Vec_PtrEntry(v1,i), w);
}

/* CHECK uses the original complete predicate, independent of learned masks
   and columns. Matching ordinal bitsets imply identical ascending streams. */
static void Dar_ResubCexCheck( Dar_Resub_t * p, int fUP, Aig_Obj_t * a, Aig_Obj_t * b,
    word * before, word * after )
{
    Dar_ResubPairIndex_t * idx = &p->Index[!fUP];
    int j, i, w;
    for ( j = 0; j < idx->nWords; j++ )
    {
        word bits = before[j], expected = 0, actual = 0;
        if ( after[j] & ~before[j] ) goto fail;
        while ( bits )
        {
            word bit = bits & (~bits+1);
            i = 64*j + Abc_TtFindFirstBit(&bits,1); bits &= bits-1;
            if ( i >= idx->nPairs ) goto fail;
            for ( w = 0; w < p->nWords; w++ )
            {
                unsigned outer = Dar_ResubCexOuter(a,b,w), pair = Dar_ResubCexPair(p,fUP,i,w);
                if ( ((fUP ? outer | pair : outer & pair) ^ ((unsigned *)p->pRoot->pData)[w]) & p->pCareSet[w] ) break;
            }
            if ( w == p->nWords ) expected |= bit, actual |= after[j] & bit;
        }
        if ( expected != actual ) goto fail;
    }
    return;
fail:
    fprintf(stderr,"DAR_CEX_COLUMNS_FAIL root=%d pool=%d\n",p->pRoot->Id,!fUP);
    abort();
}

static void Dar_ResubCexQuery( Dar_Resub_t * p, int fUP, Aig_Obj_t * a, Aig_Obj_t * b, word * matches )
{
    Dar_ResubCex_t * s = p->pCex;
    Dar_ResubPairIndex_t * idx = &p->Index[!fUP];
    word before[DAR_RS_INDEX_WORDS], any = 0;
    unsigned words = s->Words[!fUP];
    int w, c, j;
    s->Queries++;
    if ( p->fCexCheck ) memcpy(before,matches,sizeof(word)*idx->nWords);
    if ( !words ) goto done;
    for ( j = 0; j < idx->nWords; j++ ) any |= matches[j];
    if ( !any ) goto done;
    while ( words )
    {
        word wide = words;
        unsigned root, outer, needed;
        w = Abc_TtFindFirstBit(&wide,1); words &= words-1;
        root = ((unsigned *)p->pRoot->pData)[w]; outer = Dar_ResubCexOuter(a,b,w);
        needed = (fUP ? root & ~outer : ~root & outer) & p->pCareSet[w] & s->Seen[!fUP][w];
        s->ApplicabilityWords++;
        while ( needed )
        {
            word * column;
            wide = needed; c = 32*w + Abc_TtFindFirstBit(&wide,1); needed &= needed-1;
            column = s->Cover[!fUP] + (c-64)*DAR_RS_INDEX_WORDS;
            any = 0;
            for ( j = 0; j < idx->nWords; j++ ) any |= (matches[j] &= column[j]);
            s->IntersectionWords += idx->nWords;
            if ( !any ) goto done;
        }
    }
done:
    if ( p->fCexCheck ) Dar_ResubCexCheck(p,fUP,a,b,before,matches), s->QueryAudits++;
}

static void Dar_ResubCexRecord( Dar_Resub_t * p, int fUP, Aig_Obj_t * a, Aig_Obj_t * b,
    int ordinal, int w, word * matches )
{
    Dar_ResubCex_t * s = p->pCex;
    Dar_ResubPairIndex_t * idx = &p->Index[!fUP];
    unsigned root, outer, pair, mismatch, bit, needed;
    word before[DAR_RS_INDEX_WORDS], wide, * column;
    int c, i, j;
    s->Predicates++; s->PredicateWords += w + (w != p->nWords);
    if ( w == p->nWords ) { s->Exact++; return; }
    s->Rejected++;
    root = ((unsigned *)p->pRoot->pData)[w]; outer = Dar_ResubCexOuter(a,b,w);
    pair = Dar_ResubCexPair(p,fUP,ordinal,w);
    mismatch = ((fUP ? outer | pair : outer & pair) ^ root) & p->pCareSet[w];
    bit = mismatch & (0u-mismatch);
    needed = (fUP ? root & ~outer : ~root & outer) & p->pCareSet[w];
    /* A defensive no-op preserves the original predicate on an unexpected
       low coordinate, invalid unate pool, or repeated learned counterexample. */
    if ( w < 2 || !bit || !(needed & bit) || (s->Seen[!fUP][w] & bit) )
    {
        s->Invalid++;
        if ( p->fCexCheck ) { fprintf(stderr,"DAR_CEX_COLUMNS_FAIL invalid counterexample\n"); abort(); }
        return;
    }
    wide = bit; c = 32*w + Abc_TtFindFirstBit(&wide,1);
    column = s->Cover[!fUP] + (c-64)*DAR_RS_INDEX_WORDS;
    memset(column,0,sizeof(word)*idx->nWords);
    for ( i = 0; i < idx->nPairs; i++ )
    {
        unsigned value = Dar_ResubCexPair(p,fUP,i,w);
        if ( (fUP ? value : ~value) & bit ) column[i>>6] |= (word)1 << (i&63);
    }
    s->Seen[!fUP][w] |= bit; s->Words[!fUP] |= 1u << w;
    s->Columns++; s->PairVisits += idx->nPairs;
    if ( p->fCexCheck ) memcpy(before,matches,sizeof(word)*idx->nWords);
    for ( j = 0; j < idx->nWords; j++ ) matches[j] &= column[j];
    s->IntersectionWords += idx->nWords;
    if ( p->fCexCheck ) Dar_ResubCexCheck(p,fUP,a,b,before,matches), s->RefineAudits++;
}
