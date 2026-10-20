/* Bounded strict-SEQ teaching from the existing proof oracle.
 * PI prefixes only: no old node IDs, register values, care, or certificates.
 * Consume at the next ordinary epoch; never restart an iterator or add epochs.
 */
struct Cec_TranStrictCex_t_
{
    Vec_Ptr_t * vPrefixes;
    int Mode, nPis, nFramesMax, Solver;
    long long Seen, Added, Duplicate, InvalidReset, InvalidSplit, TooLong;
    long long Overflow, IgnoredInd, Injected, SplitPairs;
    long long ActiveLow, ActiveQueries, ActiveSat, ActiveUnsat, ActiveUnknown;
    long long ActiveSplit, ActiveInvalid, ActiveSizeSkip;
    long long ActiveConflicts, ActiveQueueCut;
    abctime ActiveTime;
    abctime Time;
};

static int Cec_TranStrictCexOption( char const * Name, int Default, int Max )
{
    char * End, * Text = getenv(Name);
    long Value;
    if ( !Text ) return Default;
    Value = strtol(Text, &End, 10);
    if ( !*Text || *End || Value < 0 || Value > Max )
    {
        Abc_Print(-1, "%s must be an integer in [0,%d].\n", Name, Max);
        return Default;
    }
    return (int)Value;
}

static Cec_TranStrictCex_t * Cec_TranStrictCexStart( Gia_Man_t * p, Cec_ParTran_t * Pars )
{
    Cec_TranStrictCex_t * b;
    int Mode = Cec_TranStrictCexOption("ABC_STRICT_CEX_MODE", (Pars->fRoute1 || Pars->fStran2Guide) ? 4 : 0, 6);
    if ( !Mode ) return NULL;
    b = ABC_CALLOC(Cec_TranStrictCex_t, 1);
    b->Mode = Mode;
    b->Solver = Cec_TranStrictCexOption("ABC_STRICT_CEX_SOLVER", Pars->fRoute1 || Pars->fStran2Guide, 1);
    b->nPis = Gia_ManPiNum(p);
    b->nFramesMax = Pars->nSimFrames;
    b->vPrefixes = Vec_PtrAlloc(64);
    return b;
}

static void Cec_TranStrictCexStop( Cec_TranStrictCex_t * b )
{
    Abc_Cex_t * c;
    int i;
    if ( !b ) return;
    Vec_PtrForEachEntry(Abc_Cex_t *, b->vPrefixes, c, i) Abc_CexFree(c);
    Vec_PtrFree(b->vPrefixes);
    ABC_FREE(b);
}

// Independently replay the unreduced proof graph from reset. A packed SAT
// cube is retained only if its completed PI lane splits a current relation.
static int Cec_TranStrictCexReplayTarget( Gia_Man_t * p, Abc_Cex_t * c,
    int Root, int Wanted )
{
    unsigned char * Values = ABC_CALLOC(unsigned char, Gia_ManObjNum(p));
    unsigned char * State = ABC_CALLOC(unsigned char, Gia_ManRegNum(p));
    Gia_Obj_t * o;
    int f, i, r, a, v, Repr, Splits = 0;
    assert(c->nRegs == 0 && c->nPis == Gia_ManPiNum(p));
    assert(Root >= 0 || p->pReprs);
    for ( f = 0; f <= c->iFrame; ++f )
    {
        Gia_ManForEachPi(p, o, i)
            Values[Gia_ObjId(p,o)] = Abc_InfoHasBit(c->pData, f*c->nPis+i);
        Gia_ManForEachRo(p, o, r) Values[Gia_ObjId(p,o)] = State[r];
        Gia_ManForEachObj1(p, o, i)
        {
            if ( Gia_ObjIsCi(o) ) continue;
            a = Values[Gia_ObjFaninId0p(p,o)] ^ Gia_ObjFaninC0(o);
            if ( Gia_ObjIsCo(o) || Gia_ObjIsBuf(o) ) Values[i] = a;
            else
            {
                v = Values[Gia_ObjFaninId1p(p,o)] ^ Gia_ObjFaninC1(o);
                Values[i] = Gia_ObjIsXor(o) ? a ^ v : a & v;
            }
        }
        if ( Root >= 0 ) Splits += Values[Root] == Wanted;
        else Gia_ManForEachObj(p, o, i)
        {
            Repr = Gia_ObjRepr(p,i);
            if ( Repr != GIA_VOID &&
                (Values[i] ^ Gia_ObjPhase(o)) !=
                (Values[Repr] ^ Gia_ObjPhase(Gia_ManObj(p,Repr))) ) Splits++;
        }
        Gia_ManForEachRi(p, o, r) State[r] = Values[Gia_ObjId(p,o)];
    }
    ABC_FREE(Values); ABC_FREE(State);
    return Splits;
}

static int Cec_TranStrictCexReplay( Gia_Man_t * p, Abc_Cex_t * c )
{
    return Cec_TranStrictCexReplayTarget(p,c,-1,0);
}

static void Cec_TranStrictCexObserve( void * Data, Gia_Man_t * p,
    Vec_Ptr_t * Info, Vec_Int_t * OutBits, int nFrames, int Induction )
{
    Cec_TranStrictCex_t * b = (Cec_TranStrictCex_t *)Data;
    Abc_Cex_t * c, * Old;
    int i, j, r, f, pi, Bit, Splits;
    int nBits = 32 * Vec_PtrReadWordsSimInfo(Info);
    char * Used;
    abctime Start = Abc_Clock();
    if ( Induction ) { b->IgnoredInd += Vec_IntSize(OutBits)/2; return; }
    assert(b->nPis == Gia_ManPiNum(p));
    assert(Vec_PtrSize(Info) >= Gia_ManRegNum(p) + nFrames*b->nPis);
    Used = ABC_CALLOC(char, nBits);
    for ( i = 0; i+1 < Vec_IntSize(OutBits); i += 2 )
    {
        Bit = Vec_IntEntry(OutBits,i+1);
        assert(Bit >= 0 && Bit < nBits);
        if ( Used[Bit] ) continue;
        Used[Bit] = 1; b->Seen++;
        if ( nFrames <= 0 || nFrames > b->nFramesMax ) { b->TooLong++; continue; }
        for ( r = 0; r < Gia_ManRegNum(p); ++r )
            if ( Abc_InfoHasBit((unsigned *)Vec_PtrEntry(Info,r),Bit) ) break;
        if ( r != Gia_ManRegNum(p) ) { b->InvalidReset++; continue; }
        c = Abc_CexAlloc(0,b->nPis,nFrames);
        c->iFrame = nFrames-1; c->iPo = -1;
        for ( f = 0; f < nFrames; ++f ) for ( pi = 0; pi < b->nPis; ++pi )
            if ( Abc_InfoHasBit((unsigned *)Vec_PtrEntry(Info,Gia_ManRegNum(p)+f*b->nPis+pi),Bit) )
                Abc_InfoSetBit(c->pData,f*b->nPis+pi);
        Vec_PtrForEachEntry(Abc_Cex_t *, b->vPrefixes, Old, j)
            if ( Cec_TranPatDbCexEqual(Old,c) ) break;
        if ( j < Vec_PtrSize(b->vPrefixes) ) { b->Duplicate++; Abc_CexFree(c); continue; }
        if ( Vec_PtrSize(b->vPrefixes) >= 64 ) { b->Overflow++; Abc_CexFree(c); continue; }
        Splits = Cec_TranStrictCexReplay(p,c);
        if ( !Splits ) { b->InvalidSplit++; Abc_CexFree(c); continue; }
        Vec_PtrPush(b->vPrefixes,c);
        b->Added++; b->SplitPairs += Splits;
    }
    ABC_FREE(Used); b->Time += Abc_Clock()-Start;
}

// Keep every initial observation and add at most 64 feedback traces. Q and W
// consumed by Build remain fixed; overflow uses the existing root lane selector.
// Recreate reset ROs for this graph, so cleanup/register removal needs no stale
// register mapping. The bank itself owns PI prefixes only.
static Cec_TranPatDb_t * Cec_TranStrictCexTeach( Cec_TranStrictCex_t * b,
    Gia_Man_t * p, Cec_TranPatDb_t * Initial )
{
    Cec_TranPatDb_t * db;
    Abc_Cex_t * c, * d;
    unsigned Random = 0x9e3779b9u;
    int Group, i, k, r, Value;
    if ( !b || b->Mode < 2 || b->Mode == 5 || !Vec_PtrSize(b->vPrefixes) ) return NULL;
    assert(b->nPis == Gia_ManPiNum(p));
    db = Cec_TranPatDbStart(p, 64 + (Initial ? Vec_PtrSize(Initial->vCexes) : 0));
    for ( Group = 0; Group < 2; ++Group )
    {
        Vec_Ptr_t * Source = Group ? b->vPrefixes : Initial ? Initial->vCexes : NULL;
        if ( !Source ) continue;
        Vec_PtrForEachEntry(Abc_Cex_t *, Source, c, i)
        {
            // Initial scorr is reset based too. Do not silently project a
            // free-state model into a supposedly reachable teaching trace.
            for ( r = 0; r < c->nRegs; ++r ) assert(!Abc_InfoHasBit(c->pData,r));
            d = Abc_CexAlloc(db->nRegs,db->nPis,c->iFrame+1);
            d->iFrame = c->iFrame; d->iPo = -1;
            for ( k = 0; k < (c->iFrame+1)*c->nPis; ++k )
            {
                Value = Abc_InfoHasBit(c->pData,c->nRegs+k);
                if ( Group && (b->Mode == 3 || b->Mode == 6) )
                {
                    Random ^= Random << 13; Random ^= Random >> 17; Random ^= Random << 5;
                    Value = Random & 1;
                }
                if ( Value ) Abc_InfoSetBit(d->pData,d->nRegs+k);
            }
            if ( Cec_TranPatDbAppend(db,d) && Group ) b->Injected++;
        }
    }
    Cec_TranPatDbSeal(db);
    return db;
}

static void Cec_TranStrictCexPrint( Cec_TranStrictCex_t * b, int Epoch )
{
    if ( !b ) return;
    Abc_Print(1,"strict-cex epoch=%d mode=%d bank=%d seen=%lld added=%lld duplicate=%lld invalid-reset=%lld invalid-split=%lld too-long=%lld overflow=%lld ignored-ind=%lld injected=%lld split-pairs=%lld seconds=%.6f active-low=%lld active-queries=%lld active-sat=%lld active-unsat=%lld active-unknown=%lld active-split=%lld active-invalid=%lld active-size-skip=%lld active-seconds=%.6f solver=%d active-conflicts=%lld active-queue-cut=%lld\n",
        Epoch,b->Mode,Vec_PtrSize(b->vPrefixes),b->Seen,b->Added,b->Duplicate,
        b->InvalidReset,b->InvalidSplit,b->TooLong,b->Overflow,b->IgnoredInd,
        b->Injected,b->SplitPairs,(double)b->Time/CLOCKS_PER_SEC,
        b->ActiveLow,b->ActiveQueries,b->ActiveSat,b->ActiveUnsat,b->ActiveUnknown,
        b->ActiveSplit,b->ActiveInvalid,b->ActiveSizeSkip,(double)b->ActiveTime/CLOCKS_PER_SEC,
        b->Solver,b->ActiveConflicts,b->ActiveQueueCut);
}
