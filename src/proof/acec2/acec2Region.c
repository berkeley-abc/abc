/**CFile****************************************************************

  FileName    [acec2Region.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Arithmetic analysis and equivalence checking.]

  Synopsis    [Weighted composition of checked cells and general counters.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 14, 2026.]

  Revision    [$Id$]

***********************************************************************/

#include "acec2Int.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

enum { ACEC2_COVER_PRIMARY, ACEC2_COVER_PARITY, ACEC2_COVER_DISJOINT, ACEC2_COVER_JOINED, ACEC2_COVER_CLOSURE };

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Reads a checked integer identity and its separate footprint.]

  Description [Kinds zero and one denote selected and alternative cells.
  Kind two denotes a general counter. A counter whose modular identity
  could overflow is not lifted into a wider integer composition.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_GetPart( Acec2_Man_t * m, int Kind, int Id, Acec2_Part_t * b )
{
    Acec2_Cell_t * c; Acec2_Counter_t * counter;
    Vec_Ptr_t * v; int i, side, bound, rank;
    memset(b, 0, sizeof(Acec2_Part_t)); b->Kind = Kind; b->Id = Id;
    if ( Kind < 0 || Kind > 2 || Id < 0 ) return 0;
    if ( Kind < 2 )
    {
        v = Kind ? m->vAlternatives : m->vCells;
        if ( Id >= Vec_PtrSize(v) ) return 0;
        c = (Acec2_Cell_t *)Vec_PtrEntry(v, Id); b->nIns = c->nIns; b->nOuts = 2;
        for ( i = 0; i < c->nIns; i++ ) { b->In[2*i] = c->In[i]; b->In[2*i+1] = 0; }
        for ( i = 0; i < 2; i++ ) { b->Out[2*i] = c->Out[i]; b->Out[2*i+1] = i; }
        b->vGates = Vec_WecEntry(Kind ? m->vAltGates : m->vCellGates, Id); return 1;
    }
    if ( Id >= Vec_PtrSize(m->vCounters) ) return 0;
    counter = (Acec2_Counter_t *)Vec_PtrEntry(m->vCounters, Id);
    b->nIns = Vec_IntSize(counter->vInputs)/2; b->nOuts = Vec_IntSize(counter->vOutputs)/2;
    if ( b->nIns > 6 || b->nOuts > 4 || counter->Width < 1 || counter->Width > 8 ) return 0;
    for ( side = 0; side < 2; side++ )
    {
        Vec_Int_t * terms = side ? counter->vOutputs : counter->vInputs;
        bound = 0;
        for ( i = 0; i < Vec_IntSize(terms); i += 2 )
        {
            rank = Vec_IntEntry(terms, i+1);
            if ( rank < 0 || rank >= counter->Width ) return 0;
            bound += 1 << rank;
        }
        if ( bound >= (1 << counter->Width) ) return 0;
    }
    memcpy(b->In, Vec_IntArray(counter->vInputs), (size_t)2*b->nIns*sizeof(int));
    memcpy(b->Out, Vec_IntArray(counter->vOutputs), (size_t)2*b->nOuts*sizeof(int));
    b->vGates = counter->vGates; return 1;
}

/**Function*************************************************************

  Synopsis    [Selects output ownership while retaining all source alternatives.]

  Description [Larger counters are tried first. Overlapping interiors are
  allowed, but a wholly covered decomposition does not add another stage.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_PartSelect( Acec2_Man_t * m, Acec2_Part_t * parts, Vec_Int_t * vOwner )
{
    Vec_Bit_t * vCovered = Vec_BitStart(Gia_ManObjNum(m->pGia));
    Vec_Wrd_t * vOrder = Vec_WrdAlloc(Vec_PtrSize(m->vCounters));
    Acec2_Part_t b; Acec2_Counter_t * c; word key;
    int kind, i, j, id, count, n = 0, fresh, valid;
    Vec_PtrForEachEntry(Acec2_Counter_t *, m->vCounters, c, i)
        Vec_WrdPush(vOrder, ((word)(unsigned)Vec_IntSize(c->vGates) << 32) | (0xFFFFFFFFu-(unsigned)i));
    if ( Vec_WrdSize(vOrder) > 1 ) Vec_WrdSort(vOrder, 1);
    for ( kind = 2; kind >= 0; kind-- )
    {
        // Selected cells precede alternative decompositions after counters.
        int actual = kind == 2 ? 2 : 1-kind;
        count = actual == 2 ? Vec_WrdSize(vOrder) : Vec_PtrSize(actual ? m->vAlternatives : m->vCells);
        for ( i = 0; i < count && !Acec2_Stopped(m); i++ )
        {
            id = i;
            if ( actual == 2 ) { key = Vec_WrdEntry(vOrder, i); id = (int)(0xFFFFFFFFu-(unsigned)key); }
            if ( !Acec2_GetPart(m, actual, id, &b) ) continue;
            valid = 1; fresh = 0;
            for ( j = 0; j < b.nOuts; j++ )
                if ( Vec_IntEntry(vOwner, b.Out[2*j] >> 1) >= 0 ) { valid = 0; break; }
            if ( !valid ) continue;
            Vec_IntForEachEntry(b.vGates, id, j) if ( !Vec_BitEntry(vCovered, id) ) { fresh = 1; break; }
            if ( !fresh ) continue;
            parts[n] = b;
            for ( j = 0; j < b.nOuts; j++ ) Vec_IntWriteEntry(vOwner, b.Out[2*j] >> 1, 4*n+j);
            Vec_IntForEachEntry(b.vGates, id, j) Acec2_BitWrite(vCovered, id, 1);
            n++;
        }
    }
    Vec_BitFree(vCovered); Vec_WrdFree(vOrder); return n;
}

/**Function*************************************************************

  Synopsis    [Orders exact integer-part descriptors without changing them.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_PartCompare( const void * p0, const void * p1 )
{
    const int * a = (const int *)p0, * b = (const int *)p1; int i;
    for ( i = 0; i < 4; i++ ) if ( a[i] != b[i] ) return a[i] < b[i] ? -1 : 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Names a composed identity independently of enumeration order.]

  Description [Part IDs, weights, phases and all boundary occurrences remain
  explicit. Sorting preserves multiplicity and does not combine different
  decompositions that happen to agree only at the stored modulus.]

  SideEffects [Returns an owned key; leaves the record intact.]

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Acec2_PartKey( Acec2_Record_t * r )
{
    Vec_Int_t * key = Vec_IntAlloc(100), * parts = Vec_IntDup(r->vParts), * terms;
    Vec_Wrd_t * order = Vec_WrdAlloc(100); word entry;
    int side, i, stride;
    Vec_IntPushThree(key, r->Width, r->Prefix, Vec_IntSize(parts));
    if ( Vec_IntSize(parts) > 4 ) qsort(Vec_IntArray(parts), Vec_IntSize(parts)/4, 4*sizeof(int), Acec2_PartCompare);
    Vec_IntAppend(key, parts); Vec_IntFree(parts);
    for ( side = 0; side < 3; side++ )
    {
        terms = side == 2 ? r->vConstants : side ? r->vTerms : r->vOutputs; stride = side == 2 ? 1 : 2;
        Vec_IntPush(key, Vec_IntSize(terms)); Vec_WrdClear(order);
        for ( i = 0; i < Vec_IntSize(terms); i += stride )
            Vec_WrdPush(order, ((word)(unsigned)Vec_IntEntry(terms, i+stride-1) << 32) | (unsigned)(stride == 1 ? 1 : Vec_IntEntry(terms, i)));
        if ( Vec_WrdSize(order) > 1 ) Vec_WrdSort(order, 0);
        Vec_WrdForEachEntry(order, entry, i) Vec_IntPushTwo(key, (int)(unsigned)entry, (int)(entry >> 32));
    }
    Vec_WrdFree(order); return key;
}

/**Function*************************************************************

  Synopsis    [Indexes earlier checked integer partitions before adding a view.]

  Description [Existing records are immutable and IDs never move. Modular
  dependencies and word certificates are not integer-part cache entries.]

  SideEffects [Advances the per-analysis record cursor.]

  SeeAlso     []

***********************************************************************/
static void Acec2_PartCache( Acec2_Man_t * m )
{
    Acec2_Record_t * r; Vec_Int_t * key; int id;
    if ( !m->hCounterRegions )
    { m->hCounterRegions = Hsh_VecManStart(100); m->hCounterRegions->vValue = Vec_IntAlloc(100); }
    for ( ; m->iRegionCache < Vec_PtrSize(m->vRecords) && !Acec2_Stopped(m); m->iRegionCache++ )
    {
        r = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, m->iRegionCache);
        if ( !r->vParts || r->Word >= 0 || r->Proof || r->Compose || r->Extend || Vec_IntSize(r->vDependencies) ) continue;
        key = Acec2_PartKey(r); id = Hsh_VecManAdd(m->hCounterRegions, key); Vec_IntFree(key);
        Vec_IntFillExtra(m->hCounterRegions->vValue, id+1, 0);
        if ( !Vec_IntEntry(m->hCounterRegions->vValue, id) ) Vec_IntWriteEntry(m->hCounterRegions->vValue, id, m->iRegionCache+1);
    }
}

/**Function*************************************************************

  Synopsis    [Stores one checked composed boundary with explicit modulus.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_PartRecord( Acec2_Man_t * m, Acec2_Part_t * parts, Vec_Int_t * vMembers,
                              int * Delta, int * Flip, Vec_Int_t * vEdges, Vec_Bit_t * vUsed, int fCounters, int fCache )
{
    Acec2_Record_t * r; Acec2_Part_t * b;
    Vec_Int_t * vCounts; Vec_Int_t * vBias, * key;
    int i, j, id, rank, min = 0, width = 0, balance = 0, phase, hasCounter = 0, kept, cache = -1;
    Vec_IntForEachEntry(vMembers, id, i)
    {
        b = parts+id; min = Abc_MinInt(min, Delta[id]); hasCounter |= b->Kind == 2;
        for ( j = 0; j < b->nIns; j++ )
            if ( Vec_IntEntry(vEdges, 6*id+j) < 0 ) balance += ((b->In[2*j] ^ Flip[id]) & 1) ? -1 : 1;
    }
    if ( (fCounters && !hasCounter) || Vec_IntSize(vMembers) < 2 ) return;
    if ( !fCounters )
    {
        Acec2_Part_t * first = parts+Vec_IntEntry(vMembers, 0);
        int tree = first->Kind == 0 ? Acec2_Cell(m, first->Id)->Tree : -1, same = tree >= 0;
        // The main region already stores an identical complete partition.
        Vec_IntForEachEntry(vMembers, id, i)
            if ( parts[id].Kind != 0 || Acec2_Cell(m, parts[id].Id)->Tree != tree ) { same = 0; break; }
        if ( same && Vec_IntSize(vMembers) == Vec_IntSize(Vec_WecEntry(m->vTrees, tree)) ) return;
    }
    Vec_IntForEachEntry(vMembers, id, i)
    {
        b = parts+id;
        for ( j = 0; j < b->nOuts; j++ )
            if ( !Vec_BitEntry(vUsed, 4*id+j) ) width = Abc_MaxInt(width, Delta[id]-min+b->Out[2*j+1]+1);
    }
    width = Abc_MinInt(width, m->Pars.nMaxWidth); if ( width < 1 ) return;
    r = Acec2_RecordAlloc(width); r->vParts = Vec_IntAlloc(4*Vec_IntSize(vMembers));
    vBias = Vec_IntStart(width); vCounts = Vec_IntStart(width);
    Vec_IntForEachEntry(vMembers, id, i)
    {
        b = parts+id; rank = Delta[id]-min; phase = Flip[id] ^ (balance < 0);
        // Parts entirely above the explicit modulus make no contribution.
        if ( rank >= width ) continue;
        Vec_IntPushTwo(r->vParts, b->Kind, b->Id); Vec_IntPushTwo(r->vParts, rank, phase);
        Vec_IntAppend(r->vCovered, b->vGates);
        for ( j = 0; j < b->nIns; j++ )
        {
            int k = rank+b->In[2*j+1];
            Vec_IntPush(r->vSupport, b->In[2*j] >> 1);
            if ( k >= width ) continue;
            if ( phase ) Vec_IntAddToEntry(vBias, k, -1);
            if ( Vec_IntEntry(vEdges, 6*id+j) < 0 ) Vec_IntPushTwo(r->vTerms, b->In[2*j] ^ phase, k);
        }
        for ( j = 0; j < b->nOuts; j++ )
        {
            int k = rank+b->Out[2*j+1];
            Vec_IntPush(r->vSupport, b->Out[2*j] >> 1);
            if ( k >= width ) continue;
            if ( phase ) Vec_IntAddToEntry(vBias, k, 1);
            if ( !Vec_BitEntry(vUsed, 4*id+j) ) { Vec_IntPushTwo(r->vOutputs, b->Out[2*j] ^ phase, k); Vec_IntAddToEntry(vCounts, k, 1); }
        }
    }
    for ( i = 0; i < width; i++ )
    {
        int value = Vec_IntEntry(vBias, i), bit = (unsigned)value & 1;
        if ( bit ) Vec_IntPush(r->vConstants, i);
        if ( i+1 < width ) Vec_IntAddToEntry(vBias, i+1, (value-bit)/2);
    }
    while ( r->Prefix < width && Vec_IntEntry(vCounts, r->Prefix) <= 1 ) r->Prefix++;
    kept = 0;
    for ( i = 0; i < r->Prefix; i++ ) kept += Vec_IntEntry(vCounts, i);
    if ( !kept ) r->Prefix = 0;
    Vec_IntFill(r->vBitStatus, Vec_IntSize(r->vOutputs)/2, 0);
    Vec_IntUniqify(r->vCovered); Vec_IntUniqify(r->vSupport);
    if ( ((ABC_INT64_T)2*Vec_IntSize(r->vTerms)+Vec_IntSize(r->vConstants)+1)*((width+63)/64) > 1000000 )
    { m->nRecordLimits++; Acec2_RecordFree(r); }
    else
    {
        if ( fCache )
        {
            Acec2_PartCache(m);
            if ( Acec2_Stopped(m) ) { Acec2_RecordFree(r); goto finish; }
            key = Acec2_PartKey(r);
            cache = Hsh_VecManAdd(m->hCounterRegions, key); Vec_IntFree(key);
            Vec_IntFillExtra(m->hCounterRegions->vValue, cache+1, 0);
            if ( Vec_IntEntry(m->hCounterRegions->vValue, cache) ) { Acec2_RecordFree(r); goto finish; }
        }
        if ( Acec2_RecordPopulate(m, r) )
        {
            Vec_PtrPush(m->vRecords, r);
            if ( cache >= 0 ) Vec_IntWriteEntry(m->hCounterRegions->vValue, cache, Vec_PtrSize(m->vRecords));
        }
        else
        {
            if ( !Acec2_Stopped(m) ) Abc_Print(-1, "&atree2: internal integer-region certificate error.\n");
            Acec2_RecordFree(r);
        }
    }
finish:
    Vec_IntFree(vBias); Vec_IntFree(vCounts);
}

/**Function*************************************************************

  Synopsis    [Connects general counters to compatible surrounding cells.]

  Description [Single-consumer edges establish columns first. A shared
  output joins only if every consumer admits consistent relative weights
  and phases. One use cancels the producer; extra uses remain on the cut.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_BuildPartRegions( Acec2_Man_t * m, int fCounters, int Cover )
{
    int nMax, n, i, j, e, k, root, producer, target, diff, phase, valid;
    int * Parent, * Delta, * Flip, * Size;
    Acec2_Part_t * parts, * b, * a;
    Vec_Int_t * vOwner, * vEdges, * vStamp, * vDelta, * vFlip, * v, * choices;
    Vec_Wec_t * vConsumers, * vGroups;
    Vec_Bit_t * vUsed;
    if ( (fCounters && !Vec_PtrSize(m->vCounters)) || Acec2_Stopped(m) ) return;
    if ( (ABC_INT64_T)Vec_PtrSize(m->vCells)+Vec_PtrSize(m->vAlternatives)+Vec_PtrSize(m->vCounters) > 10000000 )
    { m->nRecordLimits++; return; }
    nMax = Vec_PtrSize(m->vCells)+(fCounters || Cover != ACEC2_COVER_PRIMARY ? Vec_PtrSize(m->vAlternatives) : 0)+
        (fCounters ? Vec_PtrSize(m->vCounters) : 0);
    if ( nMax <= 0 ) return;
    parts = ABC_ALLOC(Acec2_Part_t, nMax); vOwner = Vec_IntStartFull(Gia_ManObjNum(m->pGia));
    if ( fCounters ) n = Acec2_PartSelect(m, parts, vOwner);
    else if ( Cover == ACEC2_COVER_DISJOINT || Cover == ACEC2_COVER_CLOSURE )
    {
        choices = Cover == ACEC2_COVER_CLOSURE ? Acec2_RecordCover(m) : m->vDisjoint;
        n = Vec_IntSize(choices)/2;
        if ( Cover == ACEC2_COVER_CLOSURE && n == Vec_PtrSize(m->vCells) )
        {
            for ( i = 0; i < n && Vec_IntEntry(choices, 2*i) == 0; i++ ) {}
            // Primary and joined views already contain this exact cell set.
            if ( i == n ) n = 0;
        }
        for ( i = 0; i < n; i++ )
        {
            valid = Acec2_GetPart(m, Vec_IntEntry(choices, 2*i), Vec_IntEntry(choices, 2*i+1), parts+i); assert(valid);
            for ( j = 0; j < parts[i].nOuts; j++ ) Vec_IntWriteEntry(vOwner, parts[i].Out[2*j] >> 1, 4*i+j);
        }
        if ( Cover == ACEC2_COVER_CLOSURE ) Vec_IntFree(choices);
    }
    else
    {
        n = Vec_PtrSize(m->vCells);
        for ( i = 0; i < n; i++ )
        {
            valid = Acec2_GetPart(m, 0, i, parts+i); assert(valid);
            for ( j = 0; j < parts[i].nOuts; j++ ) Vec_IntWriteEntry(vOwner, parts[i].Out[2*j] >> 1, 4*i+j);
        }
        if ( Cover == ACEC2_COVER_PARITY )
        {
            Acec2_Cell_t * cell; Acec2_Proof_t * proof; int added = 0;
            Vec_PtrForEachEntry(Acec2_Cell_t *, m->vAlternatives, cell, i)
            {
                if ( !cell->Proof ) continue;
                proof = (Acec2_Proof_t *)Vec_PtrEntry(m->vProofs, cell->Proof-1);
                if ( (proof->Kind != 4 && (proof->Kind != 2 || !proof->fBoundary)) ||
                     Vec_IntEntry(vOwner, cell->Out[0] >> 1) >= 0 || Vec_IntEntry(vOwner, cell->Out[1] >> 1) >= 0 ) continue;
                valid = Acec2_GetPart(m, 1, i, parts+n); assert(valid);
                for ( j = 0; j < parts[n].nOuts; j++ ) Vec_IntWriteEntry(vOwner, parts[n].Out[2*j] >> 1, 4*n+j);
                n++; added++;
            }
            if ( !added ) { ABC_FREE(parts); Vec_IntFree(vOwner); return; }
        }
    }
    if ( n <= 0 || n > nMax ) { ABC_FREE(parts); Vec_IntFree(vOwner); return; }
    Parent = ABC_ALLOC(int, n); Delta = ABC_CALLOC(int, n); Flip = ABC_CALLOC(int, n); Size = ABC_ALLOC(int, n);
    vEdges = Vec_IntStartFull(6*n); vUsed = Vec_BitStart(4*n); vConsumers = Vec_WecStart(4*n); vGroups = Vec_WecStart(n);
    vStamp = Vec_IntStartFull(n); vDelta = Vec_IntStart(n); vFlip = Vec_IntStart(n);
    for ( i = 0; i < n; i++ )
    {
        Parent[i] = i; Size[i] = 1; b = parts+i;
        for ( j = 0; j < b->nIns; j++ )
        {
            e = Vec_IntEntry(vOwner, b->In[2*j] >> 1);
            if ( e >= 0 ) Vec_WecPush(vConsumers, e, 6*i+j);
        }
    }
    // Join unique consumers before considering whole shared-output stars.
    for ( k = 0; k < 1+(fCounters || Cover == ACEC2_COVER_PARITY || Cover == ACEC2_COVER_JOINED || Cover == ACEC2_COVER_CLOSURE); k++ )
        Vec_WecForEachLevel(vConsumers, v, e)
        {
            if ( !Vec_IntSize(v) || (Vec_IntSize(v) == 1) != (k == 0) ) continue;
            producer = e/4; a = parts+producer;
            root = Acec2_WeightFind(Parent, Delta, Flip, producer);
            Vec_IntWriteEntry(vStamp, root, e); Vec_IntWriteEntry(vDelta, root, 0); Vec_IntWriteEntry(vFlip, root, 0);
            valid = 1;
            Vec_IntForEachEntry(v, target, j)
            {
                i = target/6; b = parts+i; root = Acec2_WeightFind(Parent, Delta, Flip, i);
                diff = a->Out[2*(e%4)+1]-b->In[2*(target%6)+1]+Delta[producer]-Delta[i];
                phase = ((a->Out[2*(e%4)] ^ b->In[2*(target%6)]) & 1) ^ Flip[producer] ^ Flip[i];
                if ( Vec_IntEntry(vStamp, root) == e &&
                     (Vec_IntEntry(vDelta, root) != diff || Vec_IntEntry(vFlip, root) != phase) ) { valid = 0; break; }
                Vec_IntWriteEntry(vStamp, root, e); Vec_IntWriteEntry(vDelta, root, diff); Vec_IntWriteEntry(vFlip, root, phase);
            }
            if ( !valid ) continue;
            Vec_IntForEachEntry(v, target, j)
            {
                i = target/6; b = parts+i;
                diff = a->Out[2*(e%4)+1]-b->In[2*(target%6)+1];
                phase = (a->Out[2*(e%4)] ^ b->In[2*(target%6)]) & 1;
                valid = Acec2_WeightUnion(Parent, Delta, Flip, Size, producer, i, diff, phase); assert(valid);
                if ( !Vec_BitEntry(vUsed, e) ) { Vec_IntWriteEntry(vEdges, target, e); Acec2_BitWrite(vUsed, e, 1); }
            }
        }
    for ( i = 0; i < n; i++ ) Vec_WecPush(vGroups, Acec2_WeightFind(Parent, Delta, Flip, i), i);
    Vec_WecForEachLevel(vGroups, v, i)
        if ( Vec_IntSize(v) && !Acec2_Stopped(m) )
            Acec2_PartRecord(m, parts, v, Delta, Flip, vEdges, vUsed, fCounters, fCounters || Cover == ACEC2_COVER_CLOSURE);
    ABC_FREE(parts); ABC_FREE(Parent); ABC_FREE(Delta); ABC_FREE(Flip); ABC_FREE(Size);
    Vec_IntFree(vOwner); Vec_IntFree(vEdges); Vec_IntFree(vStamp); Vec_IntFree(vDelta); Vec_IntFree(vFlip);
    Vec_WecFree(vConsumers); Vec_WecFree(vGroups); Vec_BitFree(vUsed);
}

/**Function*************************************************************

  Synopsis    [Retains component boundaries before joining shared consumers.]

  Description [A valid shared arithmetic region can hide a useful binary
  word inside it. Preserve the single-consumer partitions as independently
  checked records, alongside the larger region and every source alternative.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_BuildCellRegions( Acec2_Man_t * m )
{
    Acec2_BuildPartRegions(m, 0, ACEC2_COVER_PRIMARY);
    if ( m->fSingleUse ) Acec2_BuildPartRegions(m, 0, ACEC2_COVER_JOINED);
    Acec2_BuildPartRegions(m, 0, ACEC2_COVER_DISJOINT);
    if ( m->nParityCells || m->nParityPairs ) Acec2_BuildPartRegions(m, 0, ACEC2_COVER_PARITY);
    Acec2_BuildClosureRegions(m);
}

/**Function*************************************************************

  Synopsis    [Adds closure-oriented records beside a reconstruction partition.]

  Description [Only source alternatives can change this view. Repeated
  requests reuse exact part lists and boundaries in the region-record cache.]

  SideEffects [Appends checked records without changing primary regions.]

  SeeAlso     []

***********************************************************************/
void Acec2_BuildClosureRegions( Acec2_Man_t * m )
{
    if ( m->fFast && (m->nParityPairs || m->nParityCells || m->nFunctionalCells) )
        Acec2_BuildPartRegions(m, 0, ACEC2_COVER_CLOSURE);
}

/**Function*************************************************************

  Synopsis    [Builds checked regions containing larger general counters.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_BuildCounterRegions( Acec2_Man_t * m )
{
    Acec2_BuildPartRegions(m, 1, ACEC2_COVER_PRIMARY);
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
