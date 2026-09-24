/**CFile****************************************************************

  FileName    [snSec.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [HDL sequential equivalence with explicit initialization contracts.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snSec.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
#include "snSec.h"
#include "snRead.h"
#include "snClock.h"
#include "base/main/mainInt.h"
#include "aig/gia/giaAig.h"
#include "aig/saig/saig.h"
#include "proof/fra/fra.h"
#include "proof/cec/cec.h"
#include "proof/pdr/pdr.h"
#include "sat/bmc/bmc.h"
#include "misc/st/st.h"
#include <errno.h>
#include <limits.h>
#include <sys/stat.h>
#include <ctype.h>

ABC_NAMESPACE_IMPL_START

void Sn_SecModelFree( Sn_SecModel_t * p )
{
    if (!p) return;
    if (p->pGia) Gia_ManStop(p->pGia);
    Vec_StrFree(p->vInit);
    Vec_IntFree(p->vInputWidths);
    Vec_IntFree(p->vOutputWidths);
    Vec_IntFreeP(&p->vResetValues);
    if (p->vStateKeys) { for (int i = 0; i < Vec_PtrSize(p->vStateKeys); i++) ABC_FREE(Vec_PtrArray(p->vStateKeys)[i]); Vec_PtrFree(p->vStateKeys); }
    if (p->vStateNames) { for (int i = 0; i < Vec_PtrSize(p->vStateNames); i++) ABC_FREE(Vec_PtrArray(p->vStateNames)[i]); Vec_PtrFree(p->vStateNames); }
    Vec_IntFreeP(&p->vAssumedZero);
    Vec_IntFreeP(&p->vChoicePis);
    ABC_FREE(p);
}

Sn_SecModel_t * Sn_DesignExtractSeqGiaOptions( const sn_design_t * pDesign, sn_module_id_t Top,
    const Sn_SecExtractOptions_t * settings, FILE * pError )
{
    Sn_SecModel_t * p = ABC_CALLOC(Sn_SecModel_t, 1);
    const sn_module_t * m = sn_design_get_module_const(pDesign, Top);
    const char * reason = NULL;
    sn_clock_options_t options = {0};
    int i, offset = 0;
    p->vInit = Vec_StrAlloc(100);
    p->vInputWidths = Vec_IntAlloc(16);
    p->vOutputWidths = Vec_IntAlloc(16);
    p->PairState = settings->fPairState;
    p->AllowUnmatched = settings->fAllowUnmatched;
    // Source layout is useful for VCD display even without -p. It remains
    // strictly separate from the optional initial-state pairing contract.
    if (p->PairState || settings->fTraceState)
        options.sec_state_keys = p->vStateKeys = Vec_PtrAlloc(100);
    if (settings->fTraceState) options.sec_display_names = p->vStateNames = Vec_PtrAlloc(100);
    if (settings->fTraceState && settings->fAssumeZero) p->vAssumedZero = Vec_IntAlloc(16);
    options.sec_raw = true;
    options.assume_zero = settings->fAssumeZero != 0;
    options.sec_free_init = settings->vResets && Vec_PtrSize(settings->vResets) != 0;
    if ((options.sec_free_init && (settings->fAssumeZero || settings->nResetCycles <= 0)) ||
        (!options.sec_free_init && (settings->nResetCycles || settings->fPairState)) ||
        (settings->fAllowUnmatched && !settings->fPairState))
    { fprintf(pError, "SEC invalid initialization/reset options.\n"); Sn_SecModelFree(p); return NULL; }
    p->ResetCycles = options.sec_free_init ? settings->nResetCycles : 0;
    options.init_bits = p->vInit;
    options.clock_input = &p->ClockInput;
    options.clock_edge = &p->ClockEdge;
    p->pGia = sn_design_clock_abstract(pDesign, Top, options, NULL, &reason);
    if (!p->pGia)
    {
        fprintf(pError, "SEC extraction refused in module %s: %s.\n",
            sn_name_get(&pDesign->names, m->name), reason ? reason : "extraction failed");
        Sn_SecModelFree(p);
        return NULL;
    }
    if (p->vStateNames && Vec_PtrSize(p->vStateNames) != Vec_StrSize(p->vInit))
    { fprintf(pError, "SEC state display metadata does not match raw state.\n"); Sn_SecModelFree(p); return NULL; }
    // Pairing keys survive @write and @collapse even when physical _sn_ names
    // change. Prefer their source path for display, but never use display names
    // as a fallback pairing relation.
    if (p->vStateKeys && p->vStateNames)
        for (i = 0; i < Vec_PtrSize(p->vStateKeys); i++)
        {
            const char * key = (const char *)Vec_PtrEntry(p->vStateKeys, i);
            const char * layout = key ? strchr(key, '|') : NULL;
            const char * bit = layout ? strrchr(layout, '[') : NULL;
            if (bit)
            {
                size_t prefix = (size_t)(layout - key), suffix = strlen(bit);
                char * name = ABC_ALLOC(char, prefix + suffix + 1);
                memcpy(name, key, prefix);
                memcpy(name + prefix, bit, suffix + 1);
                ABC_FREE(Vec_PtrArray(p->vStateNames)[i]);
                Vec_PtrWriteEntry(p->vStateNames, i, name);
            }
        }
    for (i = 0; i < Vec_StrSize(p->vInit); i++)
        if (Vec_StrEntry(p->vInit, i) == 'x')
        {
            p->Unknown++;
            if (!options.sec_free_init)
            {
                if (p->vAssumedZero) Vec_IntPush(p->vAssumedZero, i);
                Vec_StrWriteEntry(p->vInit, i, '0');
            }
        }
    for (size_t k = 0; k < m->type_objects[SN_PI].size; k++)
    {
        sn_obj_id_t obj = sn_vec_at(sn_obj_id_t, &m->type_objects[SN_PI], k);
        int width = (int)sn_obj_width(m, obj);
        if (p->ClockInput >= offset && p->ClockInput < offset + width)
        {
            if (width != 1)
            {
                fprintf(pError, "SEC clock must be a scalar top-level port.\n");
                Sn_SecModelFree(p);
                return NULL;
            }
        }
        else Vec_IntPush(p->vInputWidths, width);
        offset += width;
    }
    for (size_t k = 0; k < m->type_objects[SN_PO].size; k++)
        Vec_IntPush(p->vOutputWidths, (int)sn_obj_width(m, sn_vec_at(sn_obj_id_t, &m->type_objects[SN_PO], k)));
    if (p->ResetCycles)
    {
        p->vResetValues = Vec_IntStartFull(Gia_ManPiNum(p->pGia));
        for (i = 0; i < Vec_PtrSize(settings->vResets); i++)
        {
            const char * spec = (const char *)Vec_PtrEntry(settings->vResets, i);
            const char * equal = strrchr(spec, '=');
            int found = 0, original = 0, retained = 0;
            if (!equal || equal == spec || (equal[1] != '0' && equal[1] != '1') || equal[2])
            { fprintf(pError, "SEC -R requires a scalar input assignment pin=0 or pin=1.\n"); goto reset_error; }
            for (size_t k = 0; k < m->type_objects[SN_PI].size; k++)
            {
                sn_obj_id_t obj = sn_vec_at(sn_obj_id_t, &m->type_objects[SN_PI], k);
                const char * name = sn_obj_name(m, obj);
                int width = (int)sn_obj_width(m, obj), isClock = original == p->ClockInput;
                if (name && strlen(name) == (size_t)(equal - spec) && !strncmp(name, spec, equal - spec))
                {
                    int old;
                    if (width != 1 || isClock)
                    { fprintf(pError, "SEC reset %.*s must be a scalar non-clock input.\n", (int)(equal-spec), spec); goto reset_error; }
                    old = Vec_IntEntry(p->vResetValues, retained);
                    if (old >= 0 && old != equal[1] - '0')
                    { fprintf(pError, "SEC conflicting reset assignments for %s.\n", name); goto reset_error; }
                    Vec_IntWriteEntry(p->vResetValues, retained, equal[1] - '0');
                    found++;
                }
                original += width;
                if (!isClock) retained += width;
            }
            if (found != 1)
            { fprintf(pError, "SEC reset selector %s does not identify one top-level input.\n", spec); goto reset_error; }
        }
    }
    return p;
reset_error:
    Sn_SecModelFree(p);
    return NULL;
}

Sn_SecModel_t * Sn_DesignExtractSeqGia( const sn_design_t * pDesign, sn_module_id_t Top,
    int fAssumeZero, FILE * pError )
{
    Sn_SecExtractOptions_t options = {0};
    options.fAssumeZero = fAssumeZero;
    return Sn_DesignExtractSeqGiaOptions(pDesign, Top, &options, pError);
}

// An inert register enables the sequential miter builder and ABC's existing
// sequential replay for zero-state operands. It is never a displayed RTL bit.
static void Sn_SecDummy( Gia_Man_t * p )
{
    assert(!Gia_ManRegNum(p));
    Gia_ManAppendCi(p);
    Gia_ManAppendCo(p, 0);
    Gia_ManSetRegNum(p, 1);
}

static int Sn_SecAlignClock( Sn_SecModel_t * p, const Sn_SecModel_t * peer, FILE * error )
{
    Gia_Man_t * next;
    Gia_Obj_t * obj;
    Vec_Int_t * roots, * aliases;
    unsigned char * depends;
    const char * reason = NULL;
    int i, port, offset = 0, ci = peer->ClockInput, cycle = -1;
    if (Gia_ManRegNum(p->pGia) || p->ClockInput >= 0 || ci < 0 ||
        Gia_ManPiNum(p->pGia) != Gia_ManPiNum(peer->pGia) + 1) return 1;
    for (port = 0; port < Vec_IntSize(p->vInputWidths) && offset < ci; port++)
        offset += Vec_IntEntry(p->vInputWidths, port);
    if (offset != ci || port == Vec_IntSize(p->vInputWidths) || Vec_IntEntry(p->vInputWidths, port) != 1)
        return 1; // ordinary interface check below explains the mismatch
    depends = ABC_CALLOC(unsigned char, Gia_ManObjNum(p->pGia));
    depends[Gia_ObjId(p->pGia, Gia_ManPi(p->pGia, ci))] = 1;
    Gia_ManForEachAnd(p->pGia, obj, i)
        depends[i] = depends[Gia_ObjFaninId0p(p->pGia, obj)] || depends[Gia_ObjFaninId1p(p->pGia, obj)];
    Gia_ManForEachPo(p->pGia, obj, i)
        if (depends[Gia_ObjFaninId0p(p->pGia, obj)]) break;
    ABC_FREE(depends);
    if (i != Gia_ManPoNum(p->pGia))
    { fprintf(error, "SEC clock is used as data on the zero-state side.\n"); return 0; }
    aliases = Vec_IntStartFull(Gia_ManCiNum(p->pGia));
    roots = Vec_IntAlloc(Gia_ManPoNum(p->pGia));
    Vec_IntWriteEntry(aliases, ci, 0);
    for (i = 0; i < Gia_ManPoNum(p->pGia); i++) Vec_IntPush(roots, sn_clock_co(p->pGia, i));
    next = sn_gia_substitute_cis(p->pGia, Vec_IntArray(aliases), Vec_IntArray(roots),
        Vec_IntSize(roots), &reason, &cycle);
    Vec_IntFree(aliases);
    Vec_IntFree(roots);
    if (!next)
    {
        fprintf(error, "SEC cannot align zero-state clock: %s.\n",
            reason ? reason : cycle >= 0 ? "combinational cycle" : "CI substitution failed");
        return 0;
    }
    next->vNamesIn = Vec_PtrAlloc(Gia_ManPiNum(next));
    for (i = 0; i < Gia_ManPiNum(p->pGia); i++)
        if (i != ci) Vec_PtrPush(next->vNamesIn, Abc_UtilStrsav((char *)Vec_PtrEntry(p->pGia->vNamesIn, i)));
    next->vNamesOut = Vec_PtrDupStr(p->pGia->vNamesOut);
    Gia_ManStop(p->pGia);
    p->pGia = next;
    p->ClockInput = ci;
    Vec_IntDrop(p->vInputWidths, port);
    if (p->vResetValues) Vec_IntDrop(p->vResetValues, ci);
    return 1;
}

// Add one shared saturating startup counter to the raw paired model. Drop the
// constrained reset PIs, but retain an extra diagnostic PO for comparison-enable.
// All other PIs remain free during the prefix as well as during normal operation.
static Gia_Man_t * Sn_SecResetPrefix( Gia_Man_t * raw, const Sn_SecModel_t * model,
    Vec_Str_t * init, FILE * error )
{
    Gia_Man_t * result;
    Vec_Int_t * roots = Vec_IntAlloc(Gia_ManCoNum(raw) + 33);
    Vec_Int_t * aliases;
    int bits = 0, states[31], next[31], done = 1, carry = 1;
    int i, pos = Gia_ManPoNum(raw), regs = Gia_ManRegNum(raw), cycle = -1;
    unsigned n = (unsigned)model->ResetCycles;
    const char * reason = NULL;
    for (unsigned value = n; value; value >>= 1) bits++;
    for (i = 0; i < bits; i++) states[i] = Gia_ManAppendCi(raw);
    Gia_ManHashAlloc(raw);
    for (i = 0; i < bits; i++)
        done = Gia_ManHashAnd(raw, done, states[i] ^ (1 ^ ((n >> i) & 1)));
    for (i = 0; i < bits; i++)
    {
        int sum = Gia_ManHashXor(raw, states[i], carry);
        carry = Gia_ManHashAnd(raw, carry, states[i]);
        next[i] = Gia_ManHashMux(raw, done, states[i], sum);
        Vec_StrPush(init, '0');
    }
    Gia_ManHashStop(raw);
    aliases = Vec_IntStartFull(Gia_ManCiNum(raw));
    for (i = 0; i < Vec_IntSize(model->vResetValues); i++)
        if (Vec_IntEntry(model->vResetValues, i) >= 0)
            Vec_IntWriteEntry(aliases, i, done ^ Vec_IntEntry(model->vResetValues, i));
    for (i = 0; i < pos; i++) Vec_IntPush(roots, sn_clock_co(raw, i));
    Vec_IntPush(roots, done);
    for (i = pos; i < Gia_ManCoNum(raw); i++) Vec_IntPush(roots, sn_clock_co(raw, i));
    for (i = 0; i < bits; i++) Vec_IntPush(roots, next[i]);
    raw->nRegs = 0;
    result = sn_gia_substitute_cis(raw, Vec_IntArray(aliases), Vec_IntArray(roots),
        Vec_IntSize(roots), &reason, &cycle);
    if (result) Gia_ManSetRegNum(result, regs + bits);
    else fprintf(error, "SEC reset controller construction failed: %s.\n", reason);
    Vec_IntFree(roots);
    Vec_IntFree(aliases);
    return result;
}

typedef struct Sn_SecKey_t_ { const char * key; int bit; } Sn_SecKey_t;
static int Sn_SecKeyCompare( const void * x, const void * y )
{ return strcmp(((const Sn_SecKey_t *)x)->key, ((const Sn_SecKey_t *)y)->key); }

// Match exact source paths AND layouts. Sorting avoids quadratic scans on large state vectors.
static Vec_Int_t * Sn_SecPairKeys( Sn_SecModel_t * a, Sn_SecModel_t * b, FILE * error )
{
    Sn_SecModel_t * models[2] = {a, b};
    Sn_SecKey_t * keys[2] = {NULL, NULL};
    int sizes[2] = {0, 0}, ok = 0;
    Vec_Int_t * pairs = Vec_IntStartFull(Vec_StrSize(b->vInit));
    a->Paired = b->Paired = a->PairedWords = b->PairedWords = a->Unmatched = b->Unmatched = 0;
    if (!a->PairState) return pairs;
    for (int side = 0; side < 2; side++)
    {
        Sn_SecModel_t * m = models[side];
        if (m->vStateKeys && Vec_PtrSize(m->vStateKeys) != Vec_StrSize(m->vInit))
        { fprintf(error, "SEC state identity vector does not match raw state.\n"); goto done; }
        keys[side] = ABC_ALLOC(Sn_SecKey_t, Vec_StrSize(m->vInit));
        for (int i = 0; i < Vec_StrSize(m->vInit); i++)
        {
            const char * key = m->vStateKeys ? (const char *)Vec_PtrEntry(m->vStateKeys, i) : NULL;
            if (!key)
            {
                if (Vec_StrEntry(m->vInit, i) != 'x') continue;
                fprintf(error, "SEC state correspondence refused: %s bit %d lacks supported source identity/layout.\n", side ? "right" : "left", i);
                goto done;
            }
            for (const char * c = key; *c; c++)
                if (!(isalnum((unsigned char)*c) || strchr("_$.[]:|-", *c)))
                { fprintf(error, "SEC unsupported state identity: %s.\n", key); goto done; }
            if (!strchr(key, '|') || !strrchr(key, '[') || strrchr(key, '[') < strchr(key, '|'))
            { fprintf(error, "SEC malformed state layout: %s.\n", key); goto done; }
            keys[side][sizes[side]].key = key;
            keys[side][sizes[side]++].bit = i;
        }
        qsort(keys[side], sizes[side], sizeof(Sn_SecKey_t), Sn_SecKeyCompare);
        for (int i = 1; i < sizes[side]; i++)
            if (!strcmp(keys[side][i-1].key, keys[side][i].key))
            { fprintf(error, "SEC duplicate state identity: %s.\n", keys[side][i].key); goto done; }
    }
    for (int side = 0; side < 2; side++)
    {
        const char * lastWord = NULL;
        size_t lastLength = 0;
        for (int i = 0; i < sizes[side]; i++)
        {
            Sn_SecKey_t * key = &keys[side][i];
            Sn_SecKey_t * peer;
            if (Vec_StrEntry(models[side]->vInit, key->bit) != 'x') continue;
            peer = (Sn_SecKey_t *)bsearch(key, keys[!side], sizes[!side], sizeof(Sn_SecKey_t), Sn_SecKeyCompare);
            if (peer && Vec_StrEntry(models[!side]->vInit, peer->bit) == 'x')
            {
                models[side]->Paired++;
                size_t length = (size_t)(strrchr(key->key, '[') - key->key);
                if (!lastWord || lastLength != length || strncmp(lastWord, key->key, length))
                    models[side]->PairedWords++;
                lastWord = key->key; lastLength = length;
                if (side) Vec_IntWriteEntry(pairs, key->bit, peer->bit);
            }
            else
            {
                models[side]->Unmatched++;
                fprintf(error, "SEC unmatched %s state: %s (missing/incompatible layout or known peer).\n", side ? "right" : "left", key->key);
                if (!a->AllowUnmatched) goto done;
            }
        }
    }
    ok = 1;
done:
    ABC_FREE(keys[0]); ABC_FREE(keys[1]);
    if (!ok) Vec_IntFreeP(&pairs);
    return pairs;
}

static Gia_Man_t * Sn_SecMergeChoices( Gia_Man_t * replay, Sn_SecModel_t * a, Sn_SecModel_t * b,
    Vec_Int_t * pairs, FILE * error )
{
    Sn_SecModel_t * models[2] = {a, b};
    Vec_Int_t * aliases = Vec_IntStartFull(Gia_ManCiNum(replay));
    Vec_Int_t * roots = Vec_IntAlloc(Gia_ManCoNum(replay));
    const char * reason = NULL;
    int cycle = -1, regs = Gia_ManRegNum(replay);
    int old = Gia_ManPiNum(replay) - a->Unknown - b->Unknown, next = old;
    for (int side = 0; side < 2; side++)
    {
        Sn_SecModel_t * m = models[side];
        Vec_IntFreeP(&m->vChoicePis);
        m->vChoicePis = Vec_IntStartFull(Vec_StrSize(m->vInit));
        for (int bit = 0; bit < Vec_StrSize(m->vInit); bit++)
            if (Vec_StrEntry(m->vInit, bit) == 'x')
            {
                int peer = side ? Vec_IntEntry(pairs, bit) : -1;
                if (peer >= 0)
                {
                    int pi = Vec_IntEntry(a->vChoicePis, peer);
                    Vec_IntWriteEntry(aliases, old, Gia_Obj2Lit(replay, Gia_ManPi(replay, pi)));
                    Vec_IntWriteEntry(m->vChoicePis, bit, pi);
                }
                else Vec_IntWriteEntry(m->vChoicePis, bit, next++);
                old++;
            }
    }
    for (int i = 0; i < Gia_ManCoNum(replay); i++) Vec_IntPush(roots, sn_clock_co(replay, i));
    replay->nRegs = 0;
    Gia_Man_t * result = sn_gia_substitute_cis(replay, Vec_IntArray(aliases), Vec_IntArray(roots), Vec_IntSize(roots), &reason, &cycle);
    Gia_ManStop(replay);
    Vec_IntFree(aliases); Vec_IntFree(roots);
    if (result) Gia_ManSetRegNum(result, regs);
    else fprintf(error, "SEC choice merging failed: %s.\n", reason);
    return result;
}

Gia_Man_t * Sn_GiaSecBuildMiter( Sn_SecModel_t * a, Sn_SecModel_t * b,
    Gia_Man_t ** ppReplay, FILE * pError )
{
    Gia_Man_t * left, * right, * raw, * replay, * proof;
    Vec_Str_t * init;
    Vec_Int_t * roots, * aliases;
    Vec_Int_t * pairs;
    const char * reason = NULL;
    int i, cycle = -1, regs;
    *ppReplay = NULL;
    if (a->PairState != b->PairState || a->AllowUnmatched != b->AllowUnmatched)
    { fprintf(pError, "SEC inconsistent state correspondence options.\n"); return NULL; }
    if (!Sn_SecAlignClock(a, b, pError) || !Sn_SecAlignClock(b, a, pError)) return NULL;
    if (Gia_ManPiNum(a->pGia) != Gia_ManPiNum(b->pGia) || Gia_ManPoNum(a->pGia) != Gia_ManPoNum(b->pGia))
    {
        fprintf(pError, "SEC interface mismatch: PI %d/%d, PO %d/%d (left/right).\n",
            Gia_ManPiNum(a->pGia), Gia_ManPiNum(b->pGia), Gia_ManPoNum(a->pGia), Gia_ManPoNum(b->pGia));
        return NULL;
    }
    if (!Vec_IntEqual(a->vInputWidths, b->vInputWidths) ||
        !Vec_IntEqual(a->vOutputWidths, b->vOutputWidths) ||
        (a->ClockInput >= 0 && b->ClockInput >= 0 && a->ClockInput != b->ClockInput))
    {
        fprintf(pError, "SEC interface mismatch: port widths or clock positions differ.\n");
        return NULL;
    }
    if (a->ResetCycles != b->ResetCycles || (a->ResetCycles &&
        !Vec_IntEqual(a->vResetValues, b->vResetValues)))
    { fprintf(pError, "SEC reset positions, asserted levels, or prefix lengths differ.\n"); return NULL; }
    pairs = Sn_SecPairKeys(a, b, pError);
    if (!pairs) return NULL;
    left = Gia_ManDup(a->pGia);
    right = Gia_ManDup(b->pGia);
    init = Vec_StrDup(a->vInit);
    if (!Gia_ManRegNum(left)) { Sn_SecDummy(left); Vec_StrPush(init, '0'); }
    for (i = 0; i < Vec_StrSize(b->vInit); i++) Vec_StrPush(init, Vec_StrEntry(b->vInit, i));
    if (!Gia_ManRegNum(right)) { Sn_SecDummy(right); Vec_StrPush(init, '0'); }
    raw = Gia_ManMiter(left, right, 0, 1, 1, 0, 0);
    Gia_ManStop(left);
    Gia_ManStop(right);
    if (!raw) { Vec_StrFree(init); Vec_IntFree(pairs); return NULL; }
    if (a->ResetCycles)
    {
        Gia_Man_t * withReset = Sn_SecResetPrefix(raw, a, init, pError);
        Gia_ManStop(raw);
        raw = withReset;
        if (!raw) { Vec_StrFree(init); Vec_IntFree(pairs); return NULL; }
    }
    Vec_StrPush(init, '\0');
    replay = Gia_ManDupZeroUndc(raw, Vec_StrArray(init), 0, 0, 0);
    Vec_StrFree(init);
    Gia_ManStop(raw);
    if (a->ResetCycles) replay = Sn_SecMergeChoices(replay, a, b, pairs, pError);
    Vec_IntFree(pairs);
    if (!replay) return NULL;
    regs = Gia_ManRegNum(replay);
    roots = Vec_IntAlloc(Gia_ManCoNum(replay));
    aliases = Vec_IntStartFull(Gia_ManCiNum(replay));
    Gia_ManHashAlloc(replay);
    for (i = 0; i < 2 * Gia_ManPoNum(a->pGia); i += 2)
    {
        int bad = Gia_ManHashXor(replay, sn_clock_co(replay, i), sn_clock_co(replay, i + 1));
        if (a->ResetCycles) bad = Gia_ManHashAnd(replay, bad, sn_clock_co(replay, 2 * Gia_ManPoNum(a->pGia)));
        Vec_IntPush(roots, bad);
    }
    for (i = Gia_ManPoNum(replay); i < Gia_ManCoNum(replay); i++)
        Vec_IntPush(roots, sn_clock_co(replay, i));
    Gia_ManHashStop(replay);
    replay->nRegs = 0;
    proof = sn_gia_substitute_cis(replay, Vec_IntArray(aliases), Vec_IntArray(roots),
        Vec_IntSize(roots), &reason, &cycle);
    Gia_ManSetRegNum(replay, regs);
    Vec_IntFree(roots);
    Vec_IntFree(aliases);
    if (!proof)
    {
        fprintf(pError, "SEC miter construction failed: %s.\n", reason);
        Gia_ManStop(replay);
        return NULL;
    }
    Gia_ManSetRegNum(proof, regs);
    *ppReplay = replay;
    return proof;
}

static int Sn_SecRemaining( int seconds, abctime start )
{
    if (!seconds) return 0;
    // Round a positive fractional remainder up: zero means unlimited to ABC's
    // engines. Check elapsed time between phases instead of restarting -T.
    return seconds - (int)((Abc_Clock() - start) / CLOCKS_PER_SEC);
}

// Proving the bad outputs zero for arbitrary state is sufficient for SEC.
// A combinational counterexample is useful only if replay validates it at the
// actual initial state. This also handles purely combinational operands.
static int Sn_SecCombTry( Gia_Man_t * p, int seconds, int verbose, Abc_Cex_t ** ppCex, FILE * error )
{
    Vec_Int_t * roots = Vec_IntAlloc(2 * Gia_ManPoNum(p));
    Vec_Int_t * aliases = Vec_IntStartFull(Gia_ManCiNum(p));
    Gia_Man_t * comb;
    Cec_ParCec_t pars;
    const char * reason = NULL;
    int i, cycle = -1, regs = Gia_ManRegNum(p), status;
    for (i = 0; i < Gia_ManPoNum(p); i++)
    {
        Vec_IntPush(roots, sn_clock_co(p, i));
        Vec_IntPush(roots, 0);
    }
    p->nRegs = 0;
    comb = sn_gia_substitute_cis(p, Vec_IntArray(aliases), Vec_IntArray(roots),
        Vec_IntSize(roots), &reason, &cycle);
    Gia_ManSetRegNum(p, regs);
    Vec_IntFree(roots);
    Vec_IntFree(aliases);
    if (!comb)
    {
        fprintf(error, "SEC combinational precheck failed: %s.\n",
            reason ? reason : cycle >= 0 ? "combinational cycle" : "CI substitution failed");
        return -2;
    }
    Cec_ManCecSetDefaultParams(&pars);
    pars.TimeLimit = seconds;
    pars.fVerbose = verbose;
    pars.fSilent = !verbose;
    status = Cec_ManVerify(comb, &pars);
    if (status == 0)
    {
        Abc_Cex_t * cex = comb->pCexComb;
        if (cex)
        {
            *ppCex = Abc_CexAlloc(regs, Gia_ManPiNum(p), 1);
            (*ppCex)->iPo = cex->iPo;
            for (i = 0; i < Gia_ManPiNum(p); i++)
                if (Abc_InfoHasBit(cex->pData, i)) Abc_InfoSetBit((*ppCex)->pData, regs + i);
            if (!Gia_ManVerifyCex(p, *ppCex, 0)) ABC_FREE(*ppCex);
        }
        if (!*ppCex) status = -1;
    }
    Gia_ManStop(comb);
    return status;
}

static int Sn_GiaSecProveMiterOnStream( Gia_Man_t * p, int seconds, int verbose,
    Abc_Cex_t ** ppCex, int * pnFrames, FILE * error )
{
    Aig_Man_t * aig;
    Abc_Frame_t * scratch;
    void * saved_aig;
    Vec_Int_t * saved_inv;
    Fra_Sec_t pars;
    int status = -1, remaining;
    abctime start = Abc_Clock();
    *ppCex = NULL;
    *pnFrames = 0;
    if (!Gia_ManPoNum(p)) return 1;
    if (verbose) printf("SEC solver phase: combinational check.\n");
    status = Sn_SecCombTry(p, seconds ? Abc_MinInt(seconds, 1) : 1, verbose, ppCex, error);
    if (status != -1) return status;
    // The existing engines export invariants/unfinished miters through global
    // scratch slots. Isolate those side effects, including library-only calls
    // where the ABC frame has not yet been initialized. No live network is used.
    scratch = Abc_FrameGetGlobalFrame();
    saved_aig = scratch->pSave1;
    saved_inv = scratch->pAbcWlcInv;
    scratch->pSave1 = NULL;
    scratch->pAbcWlcInv = NULL;
    if (!Gia_ManPiNum(p))
    {
        // Some legacy sequential simulation engines require at least one PI.
        // Supply an unused one only in their private model; strip it from the
        // returned witness before validating against the caller's miter.
        char * init = ABC_ALLOC(char, Gia_ManRegNum(p) + 1);
        Gia_Man_t * padded;
        memset(init, '0', Gia_ManRegNum(p));
        init[Gia_ManRegNum(p)] = 0;
        padded = Gia_ManDupZeroUndc(p, init, 1, 0, 0);
        ABC_FREE(init);
        aig = Gia_ManToAig(padded, 0);
        Gia_ManStop(padded);
    }
    else aig = Gia_ManToAig(p, 0);
    // Same sequential engines as dprove, using only temporary managers. BMC
    // quickly supplies shallow witnesses; SEC handles the remaining proof.
    remaining = Sn_SecRemaining(seconds, start);
    if (!seconds || remaining > 0)
    {
        if (verbose) printf("SEC solver phase: bounded checking (up to 16 frames).\n");
        status = Saig_BmcPerform(aig, 0, 16, 2000, remaining, 100000, 0, verbose, 0, pnFrames, !verbose, 0);
    }
    remaining = Sn_SecRemaining(seconds, start);
    if (status == -1 && (!seconds || remaining > 0))
    {
        if (seconds)
        {
            // Fra_FraigSec does not forward its timeout to latch correlation.
            // For a bounded run, invoke its PDR engine directly with the
            // remaining budget instead of entering unbounded preprocessing.
            Pdr_Par_t pdr;
            Pdr_ManSetDefaultParams(&pdr);
            pdr.nTimeOut = remaining;
            pdr.fVerbose = verbose;
            pdr.fSilent = !verbose;
            if (verbose) printf("SEC solver phase: PDR (remaining budget %d seconds).\n", remaining);
            status = Pdr_ManSolve(aig, &pdr);
            *pnFrames = Abc_MaxInt(*pnFrames, pdr.iFrame);
        }
        else
        {
            Fra_SecSetDefaultParams(&pars);
            pars.fVerbose = verbose;
            pars.fSilent = !verbose;
            if (verbose) printf("SEC solver phase: sequential equivalence engine.\n");
            status = Fra_FraigSec(aig, &pars, NULL);
        }
    }
    if (status == 0)
    {
        *ppCex = aig->pSeqModel;
        aig->pSeqModel = NULL;
        if (*ppCex && !Gia_ManPiNum(p))
        {
            Abc_Cex_t * original = *ppCex;
            *ppCex = Abc_CexAlloc(Gia_ManRegNum(p), 0, original->iFrame + 1);
            (*ppCex)->iFrame = original->iFrame;
            (*ppCex)->iPo = original->iPo;
            ABC_FREE(original);
        }
        if (!*ppCex || !Gia_ManVerifyCex(p, *ppCex, 0))
        {
            ABC_FREE(*ppCex);
            status = -2;
        }
        else *pnFrames = (*ppCex)->iFrame;
    }
    Aig_ManStop(aig);
    if (scratch->pSave1) Aig_ManStop((Aig_Man_t *)scratch->pSave1);
    Vec_IntFreeP(&scratch->pAbcWlcInv);
    scratch->pSave1 = saved_aig;
    scratch->pAbcWlcInv = saved_inv;
    return status;
}

int Sn_GiaSecProveMiter( Gia_Man_t * p, int seconds, int verbose, Abc_Cex_t ** ppCex, int * pnFrames )
{
    return Sn_GiaSecProveMiterOnStream(p, seconds, verbose, ppCex, pnFrames, stderr);
}

// Binary words are printed MSB-first; the interface and witness remain LSB-first.
static void Sn_SecPrintWords( FILE * out, Gia_Man_t * replay, Gia_Man_t * model,
    Vec_Int_t * widths, int frame, int side, int input, int limit, const Sn_SecModel_t * source )
{
    int offset = 0, retained = 0, width, i, bit;
    Vec_IntForEachEntry(widths, width, i)
    {
        if (i < limit)
        {
            const char * name = (const char *)Vec_PtrEntry(input ? model->vNamesIn : model->vNamesOut, offset);
            const char * label = name, * end;
            if (!strncmp(label, "pi:", 3) || !strncmp(label, "po:", 3)) label += 3;
            end = strrchr(label, '[');
            if (end)
            {
                const char * digit = end + 1;
                if (*digit == '-') digit++;
                while (*digit >= '0' && *digit <= '9') digit++;
                if (digit == end + 1 || *digit != ']' || digit[1]) end = NULL;
            }
            fprintf(out, " %.*s=", end ? (int)(end - label) : (int)strlen(label), label);
            for (bit = width - 1; bit >= 0; bit--)
            {
                int reset = input && source->vResetValues ? Vec_IntEntry(source->vResetValues, offset + bit) : -1;
                if (reset >= 0) fprintf(out, "%d", reset ^ (frame >= source->ResetCycles));
                else
                {
                    Gia_Obj_t * obj = input ? Gia_ManPi(replay, retained + bit) :
                        Gia_ManPo(replay, 2 * (offset + bit) + side);
                    fprintf(out, "%d", Gia_ManCounterExampleValueLookup(replay, Gia_ObjId(replay, obj), frame));
                }
            }
        }
        if (!input || !source->vResetValues || Vec_IntEntry(source->vResetValues, offset) < 0) retained += width;
        offset += width;
    }
    if (Vec_IntSize(widths) > limit) fprintf(out, " ... (%d words omitted)", Vec_IntSize(widths) - limit);
}

static void Sn_SecPrintFrame( FILE * out, int frame, int resetCycles )
{
    fprintf(out, "frame %d", frame);
    if (resetCycles)
    {
        if (frame < resetCycles) fprintf(out, " (startup)");
        else fprintf(out, " (post-reset %d)", frame - resetCycles);
    }
}

// The first raw latch group belongs to the left model, followed by the right
// group. Gia_ManDupZeroUndc preserves their order, complementing 1-initialized
// latches and using a choice PI on frame zero for each X-initialized latch.
// Dummy, reset-controller, and undc-startup latches are never RTL state.
static int Sn_SecStateBit( Gia_Man_t * replay, const Sn_SecModel_t * left,
    const Sn_SecModel_t * model, int side, int bit, int frame )
{
    int base = side ? Abc_MaxInt(1, Gia_ManRegNum(left->pGia)) : 0;
    char init = Vec_StrEntry(model->vInit, bit);
    if (init == 'x' && frame == 0)
    {
        int choice = Vec_IntEntry(model->vChoicePis, bit);
        return Gia_ManCounterExampleValueLookup(replay,
            Gia_ObjId(replay, Gia_ManPi(replay, choice)), frame);
    }
    return Gia_ManCounterExampleValueLookup(replay,
        Gia_ObjId(replay, Gia_ManRo(replay, base + bit)), frame) ^ (init == '1');
}

static int Sn_SecStateGroup( const Sn_SecModel_t * model, int bit, int limit )
{
    const char * name = model->vStateNames && bit < Vec_PtrSize(model->vStateNames) ?
        (const char *)Vec_PtrEntry(model->vStateNames, bit) : NULL;
    const char * suffix = name ? strrchr(name, '[') : NULL;
    int next;
    if (!suffix || strcmp(suffix, "[0]")) return 1;
    for (next = bit + 1; next < Vec_StrSize(model->vInit) && next < limit; next++)
    {
        const char * peer = (const char *)Vec_PtrEntry(model->vStateNames, next);
        char expected[32];
        snprintf(expected, sizeof(expected), "[%d]", next - bit);
        if (!peer || strncmp(name, peer, (size_t)(suffix - name)) ||
            strcmp(peer + (suffix - name), expected)) break;
    }
    return next - bit;
}

static int Sn_SecSourceStateRange( const Sn_SecModel_t * model, int bit, int width,
    int * left, int * right );

static void Sn_SecPrintState( FILE * out, Gia_Man_t * replay,
    const Sn_SecModel_t * left, const Sn_SecModel_t * model,
    int side, int frame, int limit )
{
    int count = Vec_StrSize(model->vInit);
    for (int bit = 0; bit < count && bit < limit;)
    {
        const char * name = model->vStateNames && bit < Vec_PtrSize(model->vStateNames) ?
            (const char *)Vec_PtrEntry(model->vStateNames, bit) : NULL;
        const char * suffix = name ? strrchr(name, '[') : NULL;
        int group = Sn_SecStateGroup(model, bit, limit);
        int rangeLeft = 0, rangeRight = 0;
        int sourceRange = Sn_SecSourceStateRange(model, bit, group, &rangeLeft, &rangeRight);
        if (group > 1)
        {
            fprintf(out, " %.*s", (int)(suffix - name), name);
            if (sourceRange && (rangeLeft != group - 1 || rangeRight != 0))
                fprintf(out, "[%d:%d]", rangeLeft, rangeRight);
            fputc('=', out);
            for (int j = group - 1; j >= 0; j--)
                fprintf(out, "%d", Sn_SecStateBit(replay, left, model, side, bit + j, frame));
        }
        else if (sourceRange && name && suffix)
        {
            fprintf(out, " %.*s", (int)(suffix - name), name);
            if (rangeLeft) fprintf(out, "[%d]", rangeLeft);
            fprintf(out, "=%d", Sn_SecStateBit(replay, left, model, side, bit, frame));
        }
        else if (name) fprintf(out, " %s=%d", name, Sn_SecStateBit(replay, left, model, side, bit, frame));
        else fprintf(out, " state[%d]=%d", bit, Sn_SecStateBit(replay, left, model, side, bit, frame));
        bit += group;
    }
    if (count > limit) fprintf(out, " ... (%d bits omitted)", count - limit);
    if (!count) fprintf(out, " (none)");
}

static FILE * Sn_SecOpenTrace( const char * name, FILE * error );

// Return 1 with replay values active, -1 for a validated witness too large
// for indexed replay, or 0 for an invalid witness. The caller owns ValueStop.
static int Sn_SecReplayStart( Gia_Man_t * replay, Abc_Cex_t * cex )
{
    Abc_Cex_t * copy = Abc_CexDup(cex, cex->nRegs);
    // At least one side of a failing XOR is one. Select it for ABC replay's
    // asserted-output check; both original output values remain available.
    copy->iPo = 2 * cex->iPo;
    if (!Gia_ManVerifyCex(replay, copy, 0)) copy->iPo++;
    if (!Gia_ManVerifyCex(replay, copy, 0)) { ABC_FREE(copy); return 0; }
    if ((uint64_t)Gia_ManObjNum(replay) * ((uint64_t)cex->iFrame + 1) > INT_MAX)
    { ABC_FREE(copy); return -1; }
    Gia_ManCounterExampleValueStart(replay, copy);
    ABC_FREE(copy);
    return 1;
}

static int Sn_SecTrace( Gia_Man_t * replay, const Sn_SecModel_t * a, const Sn_SecModel_t * b,
    Abc_Cex_t * cex, FILE * out, FILE ** pTrace, const char * traceName,
    FILE * error, int verbose, int replayStatus )
{
    int f, i, first = -1, output = -1, va = 0, vb = 0;
    FILE * trace = NULL;
    const char * qualifier = a->PairState ?
        (a->Unmatched || b->Unmatched ? " under named correspondence and independent unmatched choices" : " under named initial-state correspondence") :
        a->ResetCycles && (a->Unknown || b->Unknown) ? " under independent initial choices" : "";
    if (replayStatus < 0)
    {
        fprintf(out, "SEC NOT EQUIVALENT%s: validated failure at output %d, ", qualifier, cex->iPo);
        Sn_SecPrintFrame(out, cex->iFrame, a->ResetCycles);
        fprintf(out, ".\nDetailed replay exceeds ABC's indexed simulation limit.\n");
        return -1;
    }
    for (f = a->ResetCycles; f <= cex->iFrame && first < 0; f++)
        for (i = 0; i < Gia_ManPoNum(a->pGia); i++)
        {
            va = Gia_ManCounterExampleValueLookup(replay, Gia_ObjId(replay, Gia_ManPo(replay, 2*i)), f);
            vb = Gia_ManCounterExampleValueLookup(replay, Gia_ObjId(replay, Gia_ManPo(replay, 2*i+1)), f);
            if (va != vb) { first = f; output = i; break; }
        }
    if (first >= 0)
    {
        if (traceName) trace = *pTrace = Sn_SecOpenTrace(traceName, error);
        if (b->IsZeroReference)
            fprintf(out, "SEC NOT EQUIVALENT%s: miter output %s, ", qualifier,
                (char *)Vec_PtrEntry(a->pGia->vNamesOut, output));
        else
            fprintf(out, "SEC NOT EQUIVALENT%s: %s / %s, ", qualifier,
                (char *)Vec_PtrEntry(a->pGia->vNamesOut, output),
                (char *)Vec_PtrEntry(b->pGia->vNamesOut, output));
        Sn_SecPrintFrame(out, first, a->ResetCycles);
        fprintf(out, b->IsZeroReference ? ", value=%d expected=%d.\n" : ", left=%d right=%d.\n", va, vb);
        for (i = 0; i < 2; i++)
        {
            int omitted = 0;
            FILE * dest = i ? trace : verbose ? out : NULL;
            if (!dest) continue;
            fprintf(dest, "Frame 0 is the initial state; each sample precedes its next transition.\n");
            if (a->ResetCycles)
            {
                fprintf(dest, "Contract: %d startup reset edges, then reset held deasserted; %s initial choices left=%d right=%d.\n",
                    a->ResetCycles, a->PairState ? "named correspondence for" : "independent", a->Unknown, b->Unknown);
                for (int side = 0; side < 2; side++)
                {
                    const Sn_SecModel_t * model = side ? b : a;
                    int shown = 0;
                    for (int bit = 0; bit < Vec_StrSize(model->vInit); bit++)
                        if (Vec_StrEntry(model->vInit, bit) == 'x')
                        {
                            int choice = Vec_IntEntry(model->vChoicePis, bit);
                            if (i || shown++ < 16)
                            {
                                fprintf(dest, "initial-choice %s state-bit %d=%d\n", side ? "right" : "left", bit,
                                    Gia_ManCounterExampleValueLookup(replay, Gia_ObjId(replay, Gia_ManPi(replay, choice)), 0));
                                if (a->PairState) fprintf(dest, "  source=%s choice-pi=%d\n", (char *)Vec_PtrEntry(model->vStateKeys, bit), choice);
                            }
                        }
                    if (!i && model->Unknown > 16) fprintf(dest, "%d more initial choices omitted.\n", model->Unknown - 16);
                }
            }
            else fprintf(dest, "Contract: known init retained; assumed-zero bits left=%d right=%d; reset inputs are free.\n", a->Unknown, b->Unknown);
            for (f = 0; f <= first; f++)
            {
                if (!i && f >= 16 && f != first && f != a->ResetCycles) { omitted++; continue; }
                Sn_SecPrintFrame(dest, f, a->ResetCycles);
                fprintf(dest, " inputs:");
                Sn_SecPrintWords(dest, replay, a->pGia, a->vInputWidths, f, 0, 1, i ? INT_MAX : 12, a);
                if (a->ResetCycles) fprintf(dest, " [comparison %s]", f < a->ResetCycles ? "disabled" : "enabled");
                fprintf(dest, b->IsZeroReference ? "\n  miter:" : "\n  left:");
                Sn_SecPrintWords(dest, replay, a->pGia, a->vOutputWidths, f, 0, 0, i ? INT_MAX : 12, a);
                fprintf(dest, b->IsZeroReference ? "\n  zero reference:" : "\n  right:");
                Sn_SecPrintWords(dest, replay, b->pGia, b->vOutputWidths, f, 1, 0, i ? INT_MAX : 12, b);
                fprintf(dest, "%s\n", f == first ? " <-- mismatch" : "");
                fprintf(dest, b->IsZeroReference ? "  miter state:" : "  left state:");
                Sn_SecPrintState(dest, replay, a, a, 0, f, i ? INT_MAX : 12);
                fprintf(dest, "\n");
                if (!b->IsZeroReference)
                {
                    fprintf(dest, "  right state:");
                    Sn_SecPrintState(dest, replay, a, b, 1, f, i ? INT_MAX : 12);
                    fprintf(dest, "\n");
                }
            }
            if (omitted) fprintf(dest, "%d intermediate frames omitted.\n", omitted);
        }
    }
    return first >= 0;
}

typedef struct Sn_SecVcdSignal_t_
{
    char kind; // input, choice, output, state, mismatch, or comparison enable
    int side, offset, width, id;
    int rangeLeft, rangeRight, hasSourceRange;
    const char * name; // borrowed from the model, except fixed marker names
    char * vcdName; // owned plain identifier, unique within its VCD scope
    char * vcdKey; // owned collision key, including a per-bit range when present
    int nameCollision;
} Sn_SecVcdSignal_t;

static void Sn_SecVcdCode( int id, char * code )
{
    int pos = 0;
    do { code[pos++] = (char)('!' + id % 94); id /= 94; } while (id);
    code[pos] = 0;
}

// sn_sec_identity stores the original packed [left:right] and width. Its
// trailing [bit] is the LSB-first bit offset, not a declared source index.
// Refuse malformed or mismatched metadata and fall back to normalized ranges.
static int Sn_SecVcdParseStateKey( const char * key, const char ** layout,
    int * left, int * right, int * width, int * index )
{
    const char * cursor;
    char * end;
    long values[4];
    *layout = key ? strrchr(key, '|') : NULL;
    if (!*layout) return 0;
    cursor = *layout + 1;
    for (int i = 0; i < 4; i++)
    {
        errno = 0;
        values[i] = strtol(cursor, &end, 10);
        if (errno || end == cursor || values[i] < INT_MIN || values[i] > INT_MAX) return 0;
        if (i < 2 ? *end != ':' : i == 2 ? *end != '[' : *end != ']') return 0;
        cursor = end + 1;
    }
    if (*cursor || values[2] <= 0 ||
        ((int64_t)values[0] >= values[1] ? (int64_t)values[0] - values[1] + 1 :
                                        (int64_t)values[1] - values[0] + 1) != values[2]) return 0;
    *left = (int)values[0];
    *right = (int)values[1];
    *width = (int)values[2];
    *index = (int)values[3];
    return 1;
}

static int Sn_SecSourceStateRange( const Sn_SecModel_t * model, int bit, int width,
    int * left, int * right )
{
    const char * key, * layout, * peer, * peerLayout;
    int declaredWidth, index, peerLeft, peerRight, peerWidth, peerIndex;
    if (!model->vStateKeys || width <= 0 || bit < 0 ||
        bit > Vec_PtrSize(model->vStateKeys) || width > Vec_PtrSize(model->vStateKeys) - bit) return 0;
    key = (const char *)Vec_PtrEntry(model->vStateKeys, bit);
    if (!Sn_SecVcdParseStateKey(key, &layout, left, right, &declaredWidth, &index) ||
        declaredWidth != width || index != 0) return 0;
    for (int j = 1; j < width; j++)
    {
        peer = (const char *)Vec_PtrEntry(model->vStateKeys, bit + j);
        if (!Sn_SecVcdParseStateKey(peer, &peerLayout, &peerLeft, &peerRight,
                                    &peerWidth, &peerIndex) ||
            peerLayout - peer != layout - key || strncmp(peer, key, (size_t)(layout - key)) ||
            peerLeft != *left || peerRight != *right || peerWidth != width || peerIndex != j)
            return 0;
    }
    return 1;
}

static void Sn_SecVcdAdd( Vec_Ptr_t * signals, char kind, int side, int offset,
    int width, const char * name )
{
    Sn_SecVcdSignal_t * signal = ABC_CALLOC(Sn_SecVcdSignal_t, 1);
    signal->kind = kind;
    signal->side = side;
    signal->offset = offset;
    signal->width = width;
    signal->name = name;
    signal->id = Vec_PtrSize(signals);
    Vec_PtrPush(signals, signal);
}

static char * Sn_SecVcdBaseName( Sn_SecVcdSignal_t * signal )
{
    const char * name = signal->name ? signal->name : "state";
    const char * suffix;
    char * end;
    long index;
    size_t length, used = 0;
    char * result;
    if (!strncmp(name, "pi:", 3) || !strncmp(name, "po:", 3)) name += 3;
    length = strlen(name);
    suffix = strrchr(name, '[');
    if ((signal->kind == 'C' || signal->kind == 'M' || signal->kind == 'Z') && suffix)
    {
        errno = 0;
        index = strtol(suffix + 1, &end, 10);
        if (!errno && end != suffix + 1 && *end == ']' && !end[1] &&
            index >= INT_MIN && index <= INT_MAX)
        {
            signal->hasSourceRange = 1;
            signal->rangeLeft = signal->rangeRight = (int)index;
            length = (size_t)(suffix - name);
        }
    }
    if (suffix && !strcmp(suffix, "[0]") &&
        (signal->width > 1 ||
         ((signal->kind == 'I' || signal->kind == 'O') && signal->width == 1) ||
         (signal->kind == 'S' && signal->hasSourceRange)))
        length = (size_t)(suffix - name);
    result = ABC_ALLOC(char, length + 8);
    for (size_t i = 0; i < length; i++)
    {
        unsigned char c = (unsigned char)name[i];
        int valid = (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') ||
            (c >= '0' && c <= '9') || c == '_' || (i && c == '$');
        result[used++] = valid ? (char)c : '_';
    }
    if (!used) memcpy(result, "signal", used = 6);
    if (!((result[0] >= 'A' && result[0] <= 'Z') ||
          (result[0] >= 'a' && result[0] <= 'z') || result[0] == '_'))
    { memmove(result + 1, result, used); result[0] = '_'; used++; }
    result[used] = 0;
    return result;
}

static char * Sn_SecVcdCollisionKey( const Sn_SecVcdSignal_t * signal )
{
    size_t cap = strlen(signal->vcdName) + 40;
    char * key = ABC_ALLOC(char, cap);
    if ((signal->kind == 'C' || signal->kind == 'M' || signal->kind == 'Z') && signal->hasSourceRange)
        snprintf(key, cap, "%s[%d]", signal->vcdName, signal->rangeLeft);
    else strcpy(key, signal->vcdName);
    return key;
}

static void Sn_SecVcdDefinitions( FILE * out, Vec_Ptr_t * signals, int first, int last )
{
    st__table * firstByName = st__init_table(strcmp, st__strhash);
    st__table * usedNames = st__init_table(strcmp, st__strhash);
    for (int i = first; i < last; i++)
    {
        Sn_SecVcdSignal_t * signal = (Sn_SecVcdSignal_t *)Vec_PtrEntry(signals, i);
        int previous;
        signal->vcdName = Sn_SecVcdBaseName(signal);
        signal->vcdKey = Sn_SecVcdCollisionKey(signal);
        if (st__lookup_int(firstByName, signal->vcdKey, &previous))
        {
            signal->nameCollision = 1;
            ((Sn_SecVcdSignal_t *)Vec_PtrEntry(signals, previous))->nameCollision = 1;
        }
        else st__insert(firstByName, signal->vcdKey, (char *)Abc_Int2Ptr(i));
    }
    for (int i = first; i < last; i++)
    {
        Sn_SecVcdSignal_t * signal = (Sn_SecVcdSignal_t *)Vec_PtrEntry(signals, i);
        if (!signal->nameCollision) st__insert(usedNames, signal->vcdKey, NULL);
    }
    for (int i = first; i < last; i++)
    {
        Sn_SecVcdSignal_t * signal = (Sn_SecVcdSignal_t *)Vec_PtrEntry(signals, i);
        char code[32];
        if (signal->nameCollision)
        {
            size_t cap = strlen(signal->vcdName) + 32;
            char * candidate = ABC_ALLOC(char, cap);
            char * candidateKey;
            snprintf(candidate, cap, "%s_%d", signal->vcdName, signal->id);
            ABC_FREE(signal->vcdName);
            signal->vcdName = candidate;
            candidateKey = Sn_SecVcdCollisionKey(signal);
            while (st__is_member(usedNames, candidateKey))
            {
                size_t length = strlen(candidate);
                cap = length + 32;
                candidate = ABC_REALLOC(char, candidate, cap);
                snprintf(candidate + length, cap - length, "_%d", signal->id);
                signal->vcdName = candidate;
                ABC_FREE(candidateKey);
                candidateKey = Sn_SecVcdCollisionKey(signal);
            }
            ABC_FREE(signal->vcdKey);
            signal->vcdKey = candidateKey;
            st__insert(usedNames, signal->vcdKey, NULL);
        }
        Sn_SecVcdCode(signal->id, code);
        fprintf(out, "$var wire %d %s %s", signal->width, code, signal->vcdName);
        if (signal->hasSourceRange)
        {
            if (signal->width > 1) fprintf(out, " [%d:%d]", signal->rangeLeft, signal->rangeRight);
            else if (signal->rangeLeft || signal->kind == 'C' || signal->kind == 'M' || signal->kind == 'Z')
                fprintf(out, " [%d]", signal->rangeLeft);
        }
        else if (signal->width > 1) fprintf(out, " [%d:0]", signal->width - 1);
        fprintf(out, " $end\n");
    }
    st__free_table(firstByName);
    st__free_table(usedNames);
    for (int i = first; i < last; i++)
    {
        Sn_SecVcdSignal_t * signal = (Sn_SecVcdSignal_t *)Vec_PtrEntry(signals, i);
        ABC_FREE(signal->vcdKey);
    }
}

static int Sn_SecVcdValue( Gia_Man_t * replay, const Sn_SecModel_t * a,
    const Sn_SecModel_t * b, const Sn_SecVcdSignal_t * signal, int bit, int frame )
{
    int offset = signal->offset + bit;
    const Sn_SecModel_t * model = signal->side ? b : a;
    switch (signal->kind)
    {
    case 'I':
        if (a->vResetValues && Vec_IntEntry(a->vResetValues, offset) >= 0)
            return Vec_IntEntry(a->vResetValues, offset) ^ (frame >= a->ResetCycles);
        return Gia_ManCounterExampleValueLookup(replay,
            Gia_ObjId(replay, Gia_ManPi(replay, signal->side + bit)), frame);
    case 'C':
        if (frame) return 2; // an initial choice has no meaning after frame zero
        return Gia_ManCounterExampleValueLookup(replay,
            Gia_ObjId(replay, Gia_ManPi(replay, signal->offset)), frame);
    case 'Z': return frame ? 2 : 0; // explicit zero assumption at startup only
    case 'O':
        return Gia_ManCounterExampleValueLookup(replay,
            Gia_ObjId(replay, Gia_ManPo(replay, 2 * offset + signal->side)), frame);
    case 'S': return Sn_SecStateBit(replay, a, model, signal->side, offset, frame);
    case 'M':
        return Gia_ManCounterExampleValueLookup(replay,
            Gia_ObjId(replay, Gia_ManPo(replay, 2 * offset)), frame) ^
            Gia_ManCounterExampleValueLookup(replay,
            Gia_ObjId(replay, Gia_ManPo(replay, 2 * offset + 1)), frame);
    default: return frame >= a->ResetCycles;
    }
}

static void Sn_SecVcdSamples( FILE * out, Gia_Man_t * replay, const Sn_SecModel_t * a,
    const Sn_SecModel_t * b, Vec_Ptr_t * signals, int frame )
{
    fprintf(out, "#%lld\n", 10LL * frame);
    if (a->ResetCycles && frame == a->ResetCycles)
        fprintf(out, "$comment post-reset frame 0 begins here $end\n");
    for (int i = 0; i < Vec_PtrSize(signals); i++)
    {
        const Sn_SecVcdSignal_t * signal = (const Sn_SecVcdSignal_t *)Vec_PtrEntry(signals, i);
        char code[32];
        Sn_SecVcdCode(signal->id, code);
        if (signal->width == 1)
        {
            int value = Sn_SecVcdValue(replay, a, b, signal, 0, frame);
            fprintf(out, "%c%s\n", value == 2 ? 'x' : (char)('0' + value), code);
        }
        else
        {
            fputc('b', out);
            for (int bit = signal->width - 1; bit >= 0; bit--)
                fputc('0' + Sn_SecVcdValue(replay, a, b, signal, bit, frame), out);
            fprintf(out, " %s\n", code);
        }
    }
}

// The VCD and text trace query the same validated replay. Register ranges use
// source identity metadata when valid; ports and other state use the extracted
// LSB-first layout. Display labels never establish a pairing relation.
static int Sn_SecWriteVcd( FILE * out, Gia_Man_t * replay, const Sn_SecModel_t * a,
    const Sn_SecModel_t * b, Abc_Cex_t * cex )
{
    Vec_Ptr_t * signals = Vec_PtrAlloc(64);
    int first, last, offset = 0, retained = 0, width, i;
    fprintf(out, "$date generated by ABC &sec $end\n$version SN sequential replay $end\n"
        "$timescale 1ns $end\n$comment samples are edge-indexed transitions, 10ns apart; no physical clock is implied. "
        "Known initialization is preserved; assumed-zero bits left=%d right=%d; startup reset edges=%d. $end\n",
        a->ResetCycles ? 0 : a->Unknown, b->ResetCycles ? 0 : b->Unknown, a->ResetCycles);
    fprintf(out, "$scope module inputs $end\n");
    first = Vec_PtrSize(signals);
    Vec_IntForEachEntry(a->vInputWidths, width, i)
    {
        Sn_SecVcdAdd(signals, 'I', retained, offset, width,
            (const char *)Vec_PtrEntry(a->pGia->vNamesIn, offset));
        if (!a->vResetValues || Vec_IntEntry(a->vResetValues, offset) < 0) retained += width;
        offset += width;
    }
    last = Vec_PtrSize(signals); Sn_SecVcdDefinitions(out, signals, first, last);
    fprintf(out, "$upscope $end\n");
    fprintf(out, "$scope module assumed_zero_at_start $end\n");
    first = Vec_PtrSize(signals);
    for (int side = 0; side < 2; side++)
    {
        const Sn_SecModel_t * model = side ? b : a;
        if (!model->vAssumedZero) continue;
        for (int j = 0; j < Vec_IntSize(model->vAssumedZero); j++)
        {
            int bit = Vec_IntEntry(model->vAssumedZero, j);
            Sn_SecVcdAdd(signals, 'Z', side, bit, 1,
                model->vStateNames ? (const char *)Vec_PtrEntry(model->vStateNames, bit) : "state");
        }
    }
    last = Vec_PtrSize(signals); Sn_SecVcdDefinitions(out, signals, first, last);
    fprintf(out, "$upscope $end\n");
    fprintf(out, "$scope module initial_choices $end\n");
    for (int side = 0; side < 2; side++)
    {
        const Sn_SecModel_t * model = side ? b : a;
        if (side && b->IsZeroReference) continue;
        fprintf(out, "$scope module %s $end\n", side ? "right" : "left");
        first = Vec_PtrSize(signals);
        if (model->vChoicePis)
            for (int bit = 0; bit < Vec_StrSize(model->vInit); bit++)
                if (Vec_StrEntry(model->vInit, bit) == 'x')
                    Sn_SecVcdAdd(signals, 'C', side, Vec_IntEntry(model->vChoicePis, bit), 1,
                        model->vStateNames ? (const char *)Vec_PtrEntry(model->vStateNames, bit) : "choice");
        last = Vec_PtrSize(signals); Sn_SecVcdDefinitions(out, signals, first, last);
        fprintf(out, "$upscope $end\n");
    }
    fprintf(out, "$upscope $end\n");
    for (int side = 0; side < (b->IsZeroReference ? 1 : 2); side++)
    {
        const Sn_SecModel_t * model = side ? b : a;
        fprintf(out, "$scope module %s $end\n", b->IsZeroReference ? "design" : side ? "right" : "left");
        first = Vec_PtrSize(signals);
        offset = 0;
        Vec_IntForEachEntry(model->vOutputWidths, width, i)
        {
            Sn_SecVcdAdd(signals, 'O', side, offset, width,
                (const char *)Vec_PtrEntry(model->pGia->vNamesOut, offset));
            offset += width;
        }
        for (int bit = 0; bit < Vec_StrSize(model->vInit);)
        {
            const char * name = model->vStateNames ?
                (const char *)Vec_PtrEntry(model->vStateNames, bit) : NULL;
            int group = Sn_SecStateGroup(model, bit, Vec_StrSize(model->vInit));
            Sn_SecVcdAdd(signals, 'S', side, bit, group, name);
            {
                Sn_SecVcdSignal_t * signal = (Sn_SecVcdSignal_t *)Vec_PtrEntry(signals, Vec_PtrSize(signals) - 1);
                signal->hasSourceRange = Sn_SecSourceStateRange(model, bit, group,
                    &signal->rangeLeft, &signal->rangeRight);
            }
            bit += group;
        }
        last = Vec_PtrSize(signals); Sn_SecVcdDefinitions(out, signals, first, last);
        fprintf(out, "$upscope $end\n");
    }
    fprintf(out, "$scope module %s $end\n", b->IsZeroReference ? "bad" : "mismatch");
    first = Vec_PtrSize(signals);
    for (i = 0; i < Gia_ManPoNum(a->pGia); i++)
        Sn_SecVcdAdd(signals, 'M', 0, i, 1,
            (const char *)Vec_PtrEntry(a->pGia->vNamesOut, i));
    Sn_SecVcdAdd(signals, 'E', 0, 0, 1, "comparison_enabled");
    last = Vec_PtrSize(signals); Sn_SecVcdDefinitions(out, signals, first, last);
    fprintf(out, "$upscope $end\n$enddefinitions $end\n");
    for (i = 0; i <= cex->iFrame; i++) Sn_SecVcdSamples(out, replay, a, b, signals, i);
    for (i = 0; i < Vec_PtrSize(signals); i++)
    {
        Sn_SecVcdSignal_t * signal = (Sn_SecVcdSignal_t *)Vec_PtrEntry(signals, i);
        ABC_FREE(signal->vcdName);
        free(signal);
    }
    Vec_PtrFree(signals);
    return 1;
}

// Refuse existing output paths as well as exact input aliases. This also avoids
// overwriting an include/library source, hard link, or symbolic link to a source.
static FILE * Sn_SecOpenTrace( const char * name, FILE * error )
{
    struct stat st;
    FILE * out;
    if (!stat(name, &st))
    { fprintf(error, "SEC trace path already exists; choose a new filename: %s.\n", name); return NULL; }
    out = fopen(name, "w");
    if (!out) fprintf(error, "Cannot open SEC trace %s: %s.\n", name, strerror(errno));
    return out;
}

// Supplied-miter mode reuses the pair adapter with a stateless zero reference.
// It adds no unknown state/relation and retains the miter's positional ports.
static Sn_SecModel_t * Sn_SecZeroReference( const Sn_SecModel_t * a )
{
    Sn_SecModel_t * b = ABC_CALLOC(Sn_SecModel_t, 1);
    b->IsZeroReference = 1;
    b->pGia = Gia_ManStart(16);
    b->pGia->vNamesIn = Vec_PtrAlloc(Gia_ManPiNum(a->pGia));
    b->pGia->vNamesOut = Vec_PtrAlloc(Gia_ManPoNum(a->pGia));
    for (int i = 0; i < Gia_ManPiNum(a->pGia); i++)
    {
        Gia_ManAppendCi(b->pGia);
        Vec_PtrPush(b->pGia->vNamesIn, Abc_UtilStrsav((char *)Vec_PtrEntry(a->pGia->vNamesIn, i)));
    }
    for (int i = 0; i < Gia_ManPoNum(a->pGia); i++)
    {
        Gia_ManAppendCo(b->pGia, 0);
        Vec_PtrPush(b->pGia->vNamesOut, Abc_UtilStrsav((char *)Vec_PtrEntry(a->pGia->vNamesOut, i)));
    }
    b->vInit = Vec_StrAlloc(0);
    b->vInputWidths = Vec_IntDup(a->vInputWidths);
    b->vOutputWidths = Vec_IntDup(a->vOutputWidths);
    b->vResetValues = a->vResetValues ? Vec_IntDup(a->vResetValues) : NULL;
    b->ResetCycles = a->ResetCycles;
    b->ClockInput = a->ClockInput;
    b->ClockEdge = -1;
    return b;
}

// Convert two top-level result words into one word of bitwise mismatches.
// Compare whole SN ports, not merely two halves of an even bit-level PO list.
// The checked extraction has already removed loop-breaker boundaries, so its
// GIA PO list contains exactly the top-level output bits in port order.
static int Sn_SecPairOutputWords( Sn_SecModel_t * model, FILE * error )
{
    Gia_Man_t * original = model->pGia, * transformed;
    int width;
    if (Vec_IntSize(model->vOutputWidths) != 2 ||
        (width = Vec_IntEntry(model->vOutputWidths, 0)) <= 0 ||
        width > INT_MAX / 2 || width != Vec_IntEntry(model->vOutputWidths, 1) ||
        Gia_ManPoNum(original) != 2 * width)
    {
        fprintf(error, "SEC -m -x requires exactly two equal-width top-level output words.\n");
        return 0;
    }
    transformed = Gia_ManTransformMiter2(original);
    if (!transformed || Gia_ManPiNum(transformed) != Gia_ManPiNum(original) ||
        Gia_ManRegNum(transformed) != Gia_ManRegNum(original) || Gia_ManPoNum(transformed) != width)
    {
        fprintf(error, "SEC -m -x failed to construct the bitwise output comparison.\n");
        if (transformed) Gia_ManStop(transformed);
        return 0;
    }
    if (transformed->vNamesIn) Vec_PtrFreeFree(transformed->vNamesIn);
    if (transformed->vNamesOut) Vec_PtrFreeFree(transformed->vNamesOut);
    transformed->vNamesIn = Vec_PtrDupStr(original->vNamesIn);
    transformed->vNamesOut = Vec_PtrAlloc(width);
    for (int bit = 0; bit < width; bit++)
    {
        char label[48];
        snprintf(label, sizeof(label), "po:pair_diff[%d]", bit);
        Vec_PtrPush(transformed->vNamesOut, Abc_UtilStrsav(label));
    }
    model->pGia = transformed;
    Gia_ManStop(original);
    Vec_IntClear(model->vOutputWidths);
    Vec_IntPush(model->vOutputWidths, width);
    return 1;
}

int Sn_CommandSec( Abc_Frame_t * frame, int argc, char ** argv )
{
    Sn_SecExtractOptions_t extract = {0};
    Sn_SecModel_t * models[2] = {NULL, NULL};
    Gia_Man_t * miter = NULL, * replay = NULL;
    Abc_Cex_t * cex = NULL, * empty = NULL;
    Vec_Ptr_t * defines = Vec_PtrAlloc(4), * files = Vec_PtrAlloc(4);
    Vec_Ptr_t * resets = Vec_PtrAlloc(2);
    const char * extra = NULL, * trace_name = NULL, * vcd_name = NULL, * top_name = NULL;
    int c, seconds = 0, zero = 0, verbose = 0, status = -1, frames = 0, ret = 1;
    int supplied = 0, pairOutputs = 0, solverVerbose = 0;
    FILE * out = Abc_FrameReadOut(frame), * error = Abc_FrameReadErr(frame), * trace = NULL, * vcd = NULL;
    abctime start = Abc_Clock(), solve;
    extract.vResets = resets;
    Extra_UtilGetoptReset();
    while ((c = Extra_UtilGetopt(argc, argv, "M:D:F:T:O:W:zvwhR:N:pumx")) != EOF)
    {
        switch (c)
        {
        case 'M': top_name = globalUtilOptarg; break;
        case 'D': Vec_PtrPush(defines, (void *)globalUtilOptarg); break;
        case 'F': extra = globalUtilOptarg; break;
        case 'O': trace_name = globalUtilOptarg; break;
        case 'W': vcd_name = globalUtilOptarg; break;
        case 'R': Vec_PtrPush(resets, (void *)globalUtilOptarg); break;
        case 'T': case 'N':
        {
            char * end;
            long value;
            errno = 0;
            value = strtol(globalUtilOptarg, &end, 10);
            if (errno || !*globalUtilOptarg || *end || value <= 0 || value > INT_MAX)
            { fprintf(error, "SEC -%c requires positive whole %s.\n", c, c == 'T' ? "seconds" : "reset edges"); goto done; }
            if (c == 'T') seconds = (int)value;
            else extract.nResetCycles = (int)value;
            break;
        }
        case 'z': zero = 1; break;
        case 'v': verbose = 1; break;
        case 'w': solverVerbose = 1; break;
        case 'p': extract.fPairState = 1; break;
        case 'u': extract.fAllowUnmatched = 1; break;
        case 'm': supplied = 1; break;
        case 'x': pairOutputs = 1; break;
        default: goto usage;
        }
    }
    if (argc - globalUtilOptind != (supplied ? 1 : 2)) goto usage;
    if (pairOutputs && !supplied)
    { fprintf(error, "SEC -x requires supplied-miter mode (-m).\n"); goto done; }
    if ((extract.fPairState && (!Vec_PtrSize(resets) || supplied)) ||
        (extract.fAllowUnmatched && !extract.fPairState))
    { fprintf(error, "SEC -p requires -R in pair mode; -u requires -p.\n"); goto done; }
    if ((zero && Vec_PtrSize(resets)) || (extract.nResetCycles && !Vec_PtrSize(resets)))
    { fprintf(error, "SEC -R and -z are mutually exclusive; -N requires -R.\n"); goto done; }
    extract.fAssumeZero = zero;
    extract.fTraceState = verbose || trace_name || vcd_name;
    if (Vec_PtrSize(resets) && !extract.nResetCycles) extract.nResetCycles = 1;
    for (int i = 0; i < Vec_PtrSize(resets); i++)
    {
        const char * spec = (const char *)Vec_PtrEntry(resets, i), * equal = strchr(spec, '=');
        if (!equal || equal == spec || (equal[1] != '0' && equal[1] != '1') || equal[2] || strchr(spec, ','))
        { fprintf(error, "SEC -R requires one pin=0 or pin=1 assignment per option.\n"); goto done; }
    }
    if ((extra && !Sn_IsHdlFile(extra)) || !Sn_IsHdlFile(argv[globalUtilOptind]) ||
        (!supplied && !Sn_IsHdlFile(argv[globalUtilOptind+1])))
    { fprintf(error, "SEC accepts only two Verilog/SystemVerilog inputs (.v/.sv), or one with -m.\n"); goto done; }
    if (trace_name && vcd_name && !strcmp(trace_name, vcd_name))
    { fprintf(error, "SEC text and VCD trace paths must differ.\n"); goto done; }
    if (trace_name || vcd_name)
        for (int i = globalUtilOptind; i < argc; i++)
            if ((trace_name && !strcmp(trace_name, argv[i])) ||
                (vcd_name && !strcmp(vcd_name, argv[i])))
            { fprintf(error, "SEC trace must not overwrite an input.\n"); goto done; }
    frame->Status = -1;
    frame->nFrames = 0;
    Abc_FrameReplaceCex(frame, &empty);
    Vec_IntFreeP(&frame->vStatuses);
    for (int side = 0; side < (supplied ? 1 : 2); side++)
    {
        sn_module_id_t top;
        sn_design_t * design;
        Vec_PtrClear(files);
        Vec_PtrPush(files, argv[globalUtilOptind+side]);
        if (extra) Vec_PtrPush(files, (void *)extra);
        design = Sn_ReadVerifyHdl(Vec_PtrSize(files), (char **)Vec_PtrArray(files),
                                  top_name, defines, &top, error);
        if (!design) goto done;
        models[side] = Sn_DesignExtractSeqGiaOptions(design, top, &extract, error);
        sn_design_destroy(design);
        if (!models[side]) goto done;
    }
    if (pairOutputs)
    {
        if (!Sn_SecPairOutputWords(models[0], error)) goto done;
        fprintf(out, "SEC two-word miter: bitwise XOR of two %d-bit top-level outputs; each bit is a bad indicator.\n",
            Vec_IntEntry(models[0]->vOutputWidths, 0));
    }
    if (supplied) models[1] = Sn_SecZeroReference(models[0]);
    miter = Sn_GiaSecBuildMiter(models[0], models[1], &replay, error);
    if (!miter) goto done;
    if (supplied) fprintf(out, "SEC supplied HDL miter: every output is a bad indicator; compare against a synthetic zero reference.\n");
    for (int side = 0; side < 2; side++)
    {
        fprintf(out, "SEC %s: PI=%d PO=%d FF=%d clock=%s unknown-init=%d.\n", supplied ? (side ? "zero reference" : "miter") : (side ? "right" : "left"),
            Gia_ManPiNum(models[side]->pGia), Gia_ManPoNum(models[side]->pGia), Gia_ManRegNum(models[side]->pGia),
            models[side]->IsZeroReference ? "none (synthetic)" : models[side]->ClockEdge < 0 ? (models[side]->ClockInput < 0 ? "none" : "unused (paired)") :
                models[side]->ClockEdge ? "falling" : "rising",
            models[side]->Unknown);
    }
    if (extract.nResetCycles)
    {
        fprintf(out, "SEC contract: %d startup reset edges, then reset held deasserted; known initial bits preserved; %s initial choices %s=%d %s=%d; positional ports.\n",
            extract.nResetCycles, extract.fPairState ? "named correspondence for" : "independent",
            supplied ? "miter" : "left", models[0]->Unknown,
            supplied ? "zero-reference" : "right", models[1]->Unknown);
        for (int i = 0; i < Vec_PtrSize(resets); i++) fprintf(out, "SEC startup reset: %s.\n", (char *)Vec_PtrEntry(resets, i));
        if (extract.fPairState)
        {
            fprintf(out, "SEC assumed source-state relation: %d paired words / %d bits; independent unmatched left=%d right=%d. Names specify an assumption, not proof of intended correspondence.\n",
                models[0]->PairedWords, models[0]->Paired, models[0]->Unmatched, models[1]->Unmatched);
            if (verbose)
                for (int side = 0; side < 2; side++)
                    for (int bit = 0; bit < Vec_StrSize(models[side]->vInit); bit++)
                        if (Vec_StrEntry(models[side]->vInit, bit) == 'x')
                            fprintf(out, "SEC state %s %s -> initial choice PI %d.\n", side ? "right" : "left",
                                (char *)Vec_PtrEntry(models[side]->vStateKeys, bit), Vec_IntEntry(models[side]->vChoicePis, bit));
        }
        if (!extract.fPairState || models[0]->Unmatched || models[1]->Unmatched)
            fprintf(out, "Independent choices are a stronger check: mismatches may be spurious for an intended corresponding-state relation.\n");
    }
    else fprintf(out, "SEC contract: %s; positional ports; reset inputs unconstrained.\n",
        zero ? "explicit zero assumption for unspecified initial bits (known bits preserved)" : "known initial state");
    solve = Abc_Clock();
    fprintf(out, "SEC import/extraction: %.3f s.\n", (double)(solve-start)/CLOCKS_PER_SEC);
    status = Sn_GiaSecProveMiterOnStream(miter, seconds, solverVerbose, &cex, &frames, error);
    fprintf(out, "SEC solver: %.3f s.\n", (double)(Abc_Clock()-solve)/CLOCKS_PER_SEC);
    if (status == 0)
    {
        int trace_status;
        int replay_status = Sn_SecReplayStart(replay, cex);
        if (!replay_status)
        { fprintf(error, "SEC internal error reconstructing counterexample.\n"); status = -2; goto finish_proof; }
        trace_status = Sn_SecTrace(replay, models[0], models[1], cex, out,
            &trace, trace_name, error, verbose, replay_status);
        if (!trace_status)
        { fprintf(error, "SEC internal error reconstructing counterexample.\n"); status = -2; }
        else ret = trace_status < 0 || (trace_name && !trace);
        if (trace)
        {
            int failed = ferror(trace);
            failed |= fclose(trace) != 0;
            trace = NULL;
            if (failed) { fprintf(error, "SEC trace write failed; file may be incomplete.\n"); ret = 1; }
            else if (trace_status > 0) fprintf(out, "SEC trace saved: %s.\n", trace_name);
        }
        if (trace_status > 0 && vcd_name)
        {
            vcd = Sn_SecOpenTrace(vcd_name, error);
            if (!vcd) ret = 1;
            else
            {
                int valid = Sn_SecWriteVcd(vcd, replay, models[0], models[1], cex);
                int failed = ferror(vcd);
                failed |= fclose(vcd) != 0;
                vcd = NULL;
                if (!valid || failed)
                { fprintf(error, "SEC VCD write failed; file may be incomplete.\n"); ret = 1; }
                else fprintf(out, "SEC VCD saved: %s.\n", vcd_name);
            }
        }
        if (replay_status > 0) Gia_ManCounterExampleValueStop(replay);
    }
    else if (status == 1) { fprintf(out, "SEC EQUIVALENT under the stated contract.\n"); ret = 0; }
    else if (status == -1) { fprintf(out, "SEC UNKNOWN (inconclusive or solver budget exhausted).\n"); ret = 0; }
    else fprintf(error, "SEC internal error: missing or invalid solver witness.\n");
finish_proof:
    frame->Status = status < 0 ? -1 : status;
    frame->nFrames = status == -2 ? 0 : Abc_MaxInt(frames, 0);
    if (status == 0) Abc_FrameReplaceCex(frame, &cex);
    if ((trace_name || vcd_name) && status != 0) fprintf(out, "No SEC trace generated.\n");
    goto done;
usage:
    fprintf(error, "usage: &sec [-M top] [-D define]... [-F extra.v] [-T seconds] [-O trace.txt] [-W trace.vcd] [-R pin=0|1]... [-N edges] [-zpumxvwh] a.v [b.v]\n"
        "  Compare two single-clock HDL designs, or check one HDL miter with -m; preserve known initial bits.\n"
        "  -z assumes zero only for unspecified initial bits; reset remains a free input.\n"
        "  -R asserts scalar reset pins for -N edges (default 1), then holds them deasserted.\n"
        "     Without -p, unknown initial bits are independent; -R and -z cannot be combined.\n"
        "     Unlike @blast -R, this is a startup sequence, not a permanent constant.\n"
        "  -v prints state correspondence details and a bounded input/output/register trace.\n"
        "  -w enables solver phase messages and backend progress/statistics; may be combined with -v.\n"
        "  -O saves the complete input/output/register trace to a new file (never overwrites).\n"
        "  -W saves a sampled-cycle VCD on a validated mismatch to a new file.\n"
        "  -T is a solver budget in whole seconds, excluding import/extraction (not a hard process timeout).\n"
        "  -p with -R assumes matching source state (simple identifiers and compatible packed layouts).\n"
        "  -u with -p permits independent unmatched bits; ambiguous identities still refuse.\n"
        "  -m reads one HDL miter: all outputs are bad indicators; no implicit state pairing.\n"
        "  -x with -m compares exactly two equal-width output words bitwise before proof.\n"
        "  No current-GIA or binary inputs.\n");
done:
    if (miter) Gia_ManStop(miter);
    if (replay) Gia_ManStop(replay);
    Sn_SecModelFree(models[0]);
    Sn_SecModelFree(models[1]);
    ABC_FREE(cex);
    Vec_PtrFree(files);
    Vec_PtrFree(defines);
    Vec_PtrFree(resets);
    return ret;
}

ABC_NAMESPACE_IMPL_END
