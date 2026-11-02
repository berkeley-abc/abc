/**CFile****************************************************************

  FileName    [snRetime.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Retiming with cached delays and optional initialization computation.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 28, 2026.]

***********************************************************************/
#include "snRetime.h"
#include "snBlast.h"
#include "snBoundary.h"
#include "base/wln/wln.h"
#include "misc/vec/vecHsh.h"
#include "sat/bsat/satSolver.h"

ABC_NAMESPACE_IMPL_START

typedef struct Sn_RetOp_t_ {
    Mini_Aig_t * aig;
    Vec_Int_t * inputs; // original nonconstant fanin slots, in MiniAIG PI order
    int delay;
} Sn_RetOp_t;

/**Function*************************************************************

  Synopsis    [Identifies literal constants.]

***********************************************************************/
static int Sn_RetConst(const sn_module_t * m, sn_obj_id_t o)
{
    int t = sn_obj_type(m, o);
    return t == SN_CONST || t == SN_CONST0 || t == SN_CONST1;
}

/**Function*************************************************************

  Synopsis    [Marks required logic and all state and opaque boundaries.]

  Description [Frontends can leave the old enable/reset mux behind after extracting native
  controls. Its dangling cone must not create timing paths or keep state alive.
  Retain every state/opaque object and its inputs, even unused state; only pure
  combinational objects and constants are eligible for this liveness pruning.]

***********************************************************************/
static unsigned char * Sn_RetLive(const sn_module_t * m)
{
    unsigned char * live = ABC_CALLOC(unsigned char, m->obj_types.size);
    Vec_Int_t * todo = Vec_IntAlloc(100);
    for (sn_obj_id_t o = 0; o < m->obj_types.size; ++o)
        if (!sn_obj_type_is_operator(sn_obj_type(m, o)) && !Sn_RetConst(m, o)) {
            live[o] = 1; Vec_IntPush(todo, (int)o);
        }
    while (Vec_IntSize(todo)) {
        sn_obj_id_t o = (sn_obj_id_t)Vec_IntPop(todo);
        for (uint32_t k = 0; k < sn_obj_fanin_count(m, o); ++k) {
            sn_obj_id_t f = sn_obj_fanin(m, o, k);
            if (f != SN_INVALID_ID && !live[f]) { live[f] = 1; Vec_IntPush(todo, (int)f); }
        }
    }
    Vec_IntFree(todo);
    return live;
}

/**Function*************************************************************

  Synopsis    [Identifies RTL operators with modeled delay.]

  Description [All RTL operators are timed, including those too large or unsuitable for a
  move. Technology cells remain explicit black boxes in this RTL flow.]

***********************************************************************/
static int Sn_RetTimed(const sn_module_t * m, sn_obj_id_t o)
{
    return sn_obj_type_is_operator(sn_obj_type(m, o)) && sn_obj_type(m, o) != SN_GATE;
}

/**Function*************************************************************

  Synopsis    [Checks the operator limits for move replay.]

  Description [Bound replay and reset-preimage work independently of timing characterization.]

***********************************************************************/
static int Sn_RetOperator(const sn_module_t * m, sn_obj_id_t o)
{
    int t = sn_obj_type(m, o);
    uint64_t bits = sn_obj_width(m, o);
    if (!Sn_RetTimed(m, o) || t == SN_DIV || t == SN_MOD || t == SN_POW ||
        t == SN_PMUX || t == SN_WILDCARD_EQ || t == SN_WILDCARD_NE || !sn_obj_fanin_count(m, o)) return 0;
    if (bits > 256 || sn_obj_fanin_count(m, o) > 64) return 0;
    for (uint32_t k = 0; k < sn_obj_fanin_count(m, o); ++k)
        bits += sn_obj_width(m, sn_obj_fanin(m, o, k));
    return bits <= 1024;
}

/**Function*************************************************************

  Synopsis    [Checks register controls, width, and initialization.]

***********************************************************************/
static int Sn_RetMovable(const sn_module_t * m, sn_obj_id_t o, int ignore_init)
{
    sn_obj_id_t d, init, mask, reset;
    if (sn_obj_type(m, o) != SN_REG_OUT || sn_obj_reg_flags(m, o) & SN_REG_LATCH) return 0;
    if (sn_reg_fanin(m, o, SN_REG_CLOCK) == SN_INVALID_ID) return 0;
    reset = sn_reg_fanin(m, o, SN_REG_RESET_VALUE);
    // A variable asynchronous load is not a constant reset state.
    if (sn_reg_fanin(m, o, SN_REG_RESET) != SN_INVALID_ID &&
        reset != SN_INVALID_ID && !Sn_RetConst(m, reset)) return 0;
    d = sn_reg_fanin(m, o, SN_REG_DATA);
    if (d == SN_INVALID_ID || sn_obj_width(m, d) != sn_obj_width(m, o) ||
        sn_obj_is_signed(m, d) != sn_obj_is_signed(m, o)) return 0;
    if (ignore_init) return 1;
    init = sn_obj_reg_init_data(m, o);
    mask = sn_obj_reg_init_mask(m, o);
    if (init == SN_INVALID_ID) return 0;
    for (uint32_t b = 0; b < sn_obj_width(m, o); ++b)
        if (mask != SN_INVALID_ID && !sn_const_bit(m, mask, b)) return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Normalizes scalar control expressions.]

  Description [Reset values are data, not part of the control class: a forward move computes
  f(reset_inputs), and a backward move solves f(reset_inputs) = reset_output.]

***********************************************************************/
static int Sn_RetControlLit(const sn_module_t * m, sn_obj_id_t o)
{
    int complement = 0;
    if (o == SN_INVALID_ID) return -1;
    // Recognize scalar Boolean wrappers emitted separately for each always
    // block, e.g. (en === 1). Do not merge arbitrary control expressions.
    while (sn_obj_width(m, o) == 1) {
        int t = sn_obj_type(m, o);
        sn_obj_id_t next = SN_INVALID_ID;
        if (t == SN_BUF || t == SN_CAST || t == SN_POS || t == SN_BIT_NOT || t == SN_LOG_NOT) {
            next = sn_obj_fanin(m, o, 0);
            if (sn_obj_width(m, next) != 1) break;
            complement ^= t == SN_BIT_NOT || t == SN_LOG_NOT;
        } else if (t == SN_EQ || t == SN_CASE_EQ || t == SN_NE || t == SN_CASE_NE) {
            sn_obj_id_t a = sn_obj_fanin(m, o, 0), b = sn_obj_fanin(m, o, 1);
            if (sn_obj_width(m, a) != 1 || sn_obj_width(m, b) != 1) break;
            if (Sn_RetConst(m, a)) { sn_obj_id_t tmp = a; a = b; b = tmp; }
            if (!Sn_RetConst(m, b)) break;
            next = a;
            complement ^= !sn_const_bit(m, b, 0) ^ (t == SN_NE || t == SN_CASE_NE);
        } else if (t == SN_MUX) {
            sn_obj_id_t yes = sn_obj_fanin(m, o, SN_MUX_SELECTED), no = sn_obj_fanin(m, o, SN_MUX_DEFAULT);
            if (!Sn_RetConst(m, yes) || !Sn_RetConst(m, no) ||
                sn_const_bit(m, yes, 0) == sn_const_bit(m, no, 0)) break;
            next = sn_obj_fanin(m, o, SN_MUX_SELECT);
            if (sn_obj_width(m, next) != 1) break;
            complement ^= sn_const_bit(m, no, 0);
        }
        if (next == SN_INVALID_ID) break;
        o = next;
    }
    return (int)(2 * o + complement);
}

/**Function*************************************************************

  Synopsis    [Resolves one clock alias, including a LOOP pair.]

***********************************************************************/
static int Sn_RetClockNext(const sn_module_t * m, int clock_lit)
{
    int next = Sn_RetControlLit(m, (sn_obj_id_t)(clock_lit >> 1)) ^ (clock_lit & 1);
    sn_obj_id_t o = (sn_obj_id_t)(next >> 1);
    if (sn_obj_type(m, o) == SN_LOOP_OUT && sn_obj_width(m, o) == 1) {
        sn_obj_id_t f = sn_obj_fanin(m, sn_obj_pair_in(m, o), 0);
        if (sn_obj_width(m, f) == 1) return (int)(2 * f + (next & 1));
    }
    return next;
}

/**Function*************************************************************

  Synopsis    [Resolves clock aliases with cycle detection.]

  Description [Clock aliases can cross LOOP pairs. Detect cycles without recursion or a
  per-register visited array; unresolved cyclic aliases retain their identity.]

***********************************************************************/
static int Sn_RetClockLit(const sn_module_t * m, sn_obj_id_t clock)
{
    int first, slow, fast;
    if (clock == SN_INVALID_ID) return -1;
    first = slow = fast = Sn_RetControlLit(m, clock);
    for (;;) {
        int next = Sn_RetClockNext(m, slow);
        if (next == slow) return slow;
        slow = next;
        fast = Sn_RetClockNext(m, Sn_RetClockNext(m, fast));
        if (slow == fast) return Sn_RetClockNext(m, slow) == slow ? slow : first;
    }
}

/**Function*************************************************************

  Synopsis    [Returns the canonical literal for a register control.]

***********************************************************************/
static int Sn_RetRegControl(const sn_module_t * m, sn_obj_id_t q, int slot)
{
    sn_obj_id_t f = sn_reg_fanin(m, q, (sn_reg_fanin_t)slot);
    return slot == SN_REG_CLOCK ? Sn_RetClockLit(m, f) : Sn_RetControlLit(m, f);
}

/**Function*************************************************************

  Synopsis    [Builds the register control-class key.]

***********************************************************************/
static void Sn_RetClassKey(const sn_module_t * m, sn_obj_id_t q, Vec_Int_t * key)
{
    Vec_IntClear(key);
    Vec_IntPush(key, (int)sn_obj_reg_flags(m, q));
    for (int k = SN_REG_CLOCK; k <= SN_REG_RESET; ++k)
        Vec_IntPush(key, Sn_RetRegControl(m, q, k));
}

/**Function*************************************************************

  Synopsis    [Compares register control classes.]

***********************************************************************/
static int Sn_RetSameControls(const sn_module_t * m, sn_obj_id_t a, sn_obj_id_t b)
{
    if (sn_obj_reg_flags(m, a) != sn_obj_reg_flags(m, b)) return 0;
    for (int k = SN_REG_CLOCK; k <= SN_REG_RESET; ++k)
        if (Sn_RetRegControl(m, a, k) != Sn_RetRegControl(m, b, k)) return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Reads an initialization, reset, or preset bit.]

***********************************************************************/
static int Sn_RetStateBit(const sn_module_t * m, sn_obj_id_t q, int mode, uint32_t b)
{
    sn_obj_id_t value;
    if (Sn_RetConst(m, q)) return sn_const_bit(m, q, b);
    if (mode == SN_REG_SET) return 1;
    value = sn_reg_fanin(m, q, (sn_reg_fanin_t)mode);
    return value != SN_INVALID_ID && sn_const_bit(m, value, b);
}

/**Function*************************************************************

  Synopsis    [Evaluates an operator on register state values.]

  Description [Evaluate initialization, reset, or preset through the same bit-blast used for
  timing. The operator may have literal constants embedded in its prototype.]

***********************************************************************/
static void Sn_RetEval(const sn_module_t * m, sn_obj_id_t o, Sn_RetOp_t * op, int mode, uint32_t * words)
{
    uint8_t * values = ABC_CALLOC(uint8_t, Mini_AigNodeNum(op->aig));
    int pi = 1, po = 0;
    memset(words, 0, sizeof(uint32_t) * sn_const_word_count(sn_obj_width(m, o)));
    for (int input = 0; input < Vec_IntSize(op->inputs); ++input) {
        sn_obj_id_t f = sn_obj_fanin(m, o, (uint32_t)Vec_IntEntry(op->inputs, input));
        for (uint32_t b = 0; b < sn_obj_width(m, f); ++b)
            values[pi++] = (uint8_t)Sn_RetStateBit(m, f, mode, b);
    }
    for (int i = pi; i < Mini_AigNodeNum(op->aig); ++i) {
        int a = Mini_AigNodeFanin0(op->aig, i);
        int v = values[a >> 1] ^ (a & 1);
        if (Mini_AigNodeIsPo(op->aig, i)) {
            if (v) words[po / 32] |= UINT32_C(1) << (po % 32);
            ++po;
        } else {
            int b = Mini_AigNodeFanin1(op->aig, i);
            values[i] = (uint8_t)(v & (values[b >> 1] ^ (b & 1)));
        }
    }
    ABC_FREE(values);
}

/**Function*************************************************************

  Synopsis    [Solves an initialization or reset preimage with MiniSAT.]

  Description [Return an initial or reset assignment in prototype PI order. These are
  separate SAT queries; -i skips only the initial-state query. A forward move may
  replace an original nonconstant fanin by its constant D input, so constrain
  those prototype PIs to their current literal values.]

***********************************************************************/
static int Sn_RetStatePreimage(const sn_module_t * m, sn_obj_id_t o, Sn_RetOp_t * op,
                               sn_obj_id_t q, int mode, Vec_Int_t * bits, int conflicts)
{
    sat_solver * sat = sat_solver_new();
    Vec_Int_t * assumptions = Vec_IntAlloc(256);
    int i, po = 0, pi = 1, status;
    sat_solver_setnvars(sat, Mini_AigNodeNum(op->aig));
    Mini_AigForEachAnd(op->aig, i) {
        int a = Mini_AigNodeFanin0(op->aig, i), b = Mini_AigNodeFanin1(op->aig, i);
        sat_solver_add_and(sat, i, a >> 1, b >> 1, a & 1, b & 1, 0);
    }
    Vec_IntPush(assumptions, 1); // MiniAIG node zero is false.
    Mini_AigForEachPo(op->aig, i) {
        int value = Sn_RetStateBit(m, q, mode, (uint32_t)po++);
        Vec_IntPush(assumptions, Mini_AigNodeFanin0(op->aig, i) ^ !value);
    }
    for (int input = 0; input < Vec_IntSize(op->inputs); ++input) {
        sn_obj_id_t f = sn_obj_fanin(m, o, (uint32_t)Vec_IntEntry(op->inputs, input));
        for (uint32_t b = 0; b < sn_obj_width(m, f); ++b, ++pi)
            if (Sn_RetConst(m, f)) Vec_IntPush(assumptions, Abc_Var2Lit(pi, !sn_const_bit(m, f, b)));
    }
    status = sat_solver_solve(sat, Vec_IntArray(assumptions), Vec_IntArray(assumptions) + Vec_IntSize(assumptions),
                              conflicts, 0, 0, 0); // Zero means unlimited.
    Vec_IntClear(bits);
    if (status == l_True) {
        Mini_AigForEachPi(op->aig, i) Vec_IntPush(bits, sat_solver_var_value(sat, i));
    }
    Vec_IntFree(assumptions);
    sat_solver_delete(sat);
    return status == l_True ? 1 : status == l_False ? 0 : -1;
}

/**Function*************************************************************

  Synopsis    [Builds the complete operator characterization key.]

  Description [The full key is hash-consed (not just its hash), including literal constants.]

***********************************************************************/
static void Sn_RetKey(const sn_module_t * m, sn_obj_id_t o, Vec_Int_t * key)
{
    Vec_IntClear(key);
    Vec_IntPush(key, sn_obj_type(m, o));
    Vec_IntPush(key, sn_obj_width(m, o));
    Vec_IntPush(key, sn_obj_is_signed(m, o));
    Vec_IntPush(key, sn_obj_type(m, o) == SN_SLICE || sn_obj_type(m, o) == SN_REPLICATE ? (int)sn_obj_data(m, o) : 0);
    Vec_IntPush(key, sn_obj_fanin_count(m, o));
    if (sn_obj_type(m, o) == SN_LUT) {
        uint64_t truth = sn_obj_lut_truth(m, o);
        Vec_IntPush(key, (int)truth); Vec_IntPush(key, (int)(truth >> 32));
    }
    for (uint32_t k = 0; k < sn_obj_fanin_count(m, o); ++k) {
        sn_obj_id_t f = sn_obj_fanin(m, o, k);
        int constant = Sn_RetConst(m, f);
        Vec_IntPush(key, sn_obj_width(m, f));
        Vec_IntPush(key, sn_obj_is_signed(m, f));
        Vec_IntPush(key, constant);
        if (constant)
            for (uint32_t w = 0; w < sn_const_word_count(sn_obj_width(m, f)); ++w)
                Vec_IntPush(key, (int)sn_const_word(m, f, w));
    }
}

/**Function*************************************************************

  Synopsis    [Builds a MiniAIG prototype and computes its logic depth.]

***********************************************************************/
static Sn_RetOp_t * Sn_RetCompile(const sn_module_t * m, sn_obj_id_t o)
{
    sn_design_t * d = sn_design_create();
    sn_module_t * proto = sn_design_get_module(d, sn_design_add_module(d, "retime_operator"));
    sn_obj_id_t * fanins = ABC_ALLOC(sn_obj_id_t, sn_obj_fanin_count(m, o)), node;
    sn_blast_ctx_t ctx;
    Sn_RetOp_t * result = ABC_CALLOC(Sn_RetOp_t, 1);
    result->inputs = Vec_IntAlloc(8);
    memset(&ctx, 0, sizeof(ctx));
    for (uint32_t k = 0; k < sn_obj_fanin_count(m, o); ++k) {
        sn_obj_id_t f = sn_obj_fanin(m, o, k);
        if (Sn_RetConst(m, f)) {
            uint32_t nWords = sn_const_word_count(sn_obj_width(m, f));
            uint32_t * words = ABC_ALLOC(uint32_t, nWords);
            for (uint32_t w = 0; w < nWords; ++w) words[w] = sn_const_word(m, f, w);
            fanins[k] = sn_module_add_const(proto, sn_obj_width(m, f), sn_obj_is_signed(m, f), words, NULL);
            ABC_FREE(words);
        } else fanins[k] = sn_module_add_pi(proto, sn_obj_width(m, f), sn_obj_is_signed(m, f), NULL);
    }
    node = sn_obj_type(m, o) == SN_LUT
               ? sn_module_add_lut(proto, sn_obj_fanin_count(m, o), fanins, sn_obj_lut_truth(m, o), NULL)
               : sn_module_add_operator(proto, sn_obj_type(m, o), sn_obj_width(m, o),
                                        sn_obj_is_signed(m, o), sn_obj_fanin_count(m, o), fanins, NULL);
    if (sn_obj_type(m, o) == SN_SLICE || sn_obj_type(m, o) == SN_REPLICATE)
        sn_obj_set_data(proto, node, sn_obj_data(m, o));
    ctx.module = proto;
    ctx.aig = result->aig = Mini_AigStart();
    ctx.options = sn_blast_default_options();
    ctx.bits = ABC_CALLOC(int *, proto->obj_types.size);
    ctx.state = ABC_CALLOC(uint8_t, proto->obj_types.size);
    for (uint32_t k = 0; k < sn_obj_fanin_count(m, o); ++k)
        if (!Sn_RetConst(m, sn_obj_fanin(m, o, k))) {
            Vec_IntPush(result->inputs, (int)k);
            ctx.bits[fanins[k]] = sn_blast_alloc_bits(sn_obj_width(proto, fanins[k]));
            for (uint32_t b = 0; b < sn_obj_width(proto, fanins[k]); ++b)
                ctx.bits[fanins[k]][b] = Mini_AigCreatePi(ctx.aig);
        }
    {
        int * outputs = sn_blast_eval(&ctx, node);
        for (uint32_t b = 0; b < sn_obj_width(m, o); ++b) Mini_AigCreatePo(ctx.aig, outputs[b]);
    }
    // Positive epsilon prevents zero-delay frontiers in the legacy engine.
    result->delay = Abc_MaxInt(1, Mini_AigLevelNum(ctx.aig));
    for (size_t i = 0; i < proto->obj_types.size; ++i) ABC_FREE(ctx.bits[i]);
    ABC_FREE(ctx.bits);
    ABC_FREE(ctx.state);
    ABC_FREE(fanins);
    sn_design_destroy(d);
    return result;
}

/**Function*************************************************************

  Synopsis    [Finds or creates a cached operator prototype.]

***********************************************************************/
static int Sn_RetCache(const sn_module_t * m, sn_obj_id_t o, Hsh_VecMan_t * cache,
                       Vec_Ptr_t * ops, Vec_Int_t * key)
{
    Sn_RetKey(m, o, key);
    int id = Hsh_VecManAdd(cache, key);
    if (id == Vec_PtrSize(ops)) Vec_PtrPush(ops, Sn_RetCompile(m, o));
    return id;
}

/**Function*************************************************************

  Synopsis    [Frees cached operator prototypes.]

***********************************************************************/
static void Sn_RetFreeOps(Vec_Ptr_t * ops)
{
    for (int i = 0; i < Vec_PtrSize(ops); ++i) {
        Sn_RetOp_t * op = (Sn_RetOp_t *)Vec_PtrEntry(ops, i);
        Mini_AigStop(op->aig); Vec_IntFree(op->inputs); ABC_FREE(op);
    }
    Vec_PtrFree(ops);
}

/**Function*************************************************************

  Synopsis    [Marks clock cones that must remain fixed.]

  Description [All clock cones are fixed, including clocks used by other domains and memory
  ports. A LOOP_OUT fanin links to its LOOP_IN, whose fanin is the driver;
  the ordinary walk follows both links. Stop at register and memory outputs.]

***********************************************************************/
static unsigned char * Sn_RetProtectClocks(const sn_module_t * m)
{
    unsigned char * fixed = ABC_CALLOC(unsigned char, m->obj_types.size);
    Vec_Int_t * todo = Vec_IntAlloc(100);
    for (sn_obj_id_t o = 0; o < m->obj_types.size; ++o) {
        sn_obj_type_t t = sn_obj_type(m, o);
        sn_obj_id_t c = t == SN_REG_OUT ? sn_reg_fanin(m, o, SN_REG_CLOCK) :
                       t == SN_MEM_READ ? sn_obj_fanin(m, o, SN_MEM_READ_CLOCK) :
                       t == SN_MEM_WRITE ? sn_obj_fanin(m, o, SN_MEM_WRITE_CLOCK) : SN_INVALID_ID;
        if (c != SN_INVALID_ID && !fixed[c]) { fixed[c] = 1; Vec_IntPush(todo, (int)c); }
    }
    while (Vec_IntSize(todo)) {
        sn_obj_id_t o = (sn_obj_id_t)Vec_IntPop(todo);
        if (sn_obj_type(m, o) == SN_REG_OUT || sn_obj_type(m, o) == SN_MEM_OUT) continue;
        for (uint32_t k = 0; k < sn_obj_fanin_count(m, o); ++k) {
            sn_obj_id_t f = sn_obj_fanin(m, o, k);
            if (f != SN_INVALID_ID && !fixed[f]) { fixed[f] = 1; Vec_IntPush(todo, (int)f); }
        }
    }
    Vec_IntFree(todo);
    return fixed;
}

/**Function*************************************************************

  Synopsis    [Marks the timing cones of one clock domain.]

  Description [Time both the data fanin and fanout cones of the active domain. Unrelated
  domains must not block this pass merely because their fixed paths are longer.]

***********************************************************************/
static unsigned char * Sn_RetCone(const sn_module_t * m, const unsigned char * movable, const int * opids)
{
    unsigned char * active = ABC_CALLOC(unsigned char, m->obj_types.size);
    Vec_Int_t * todo = Vec_IntAlloc(100), * edges = Vec_IntAlloc(100);
    int * heads = ABC_ALLOC(int, m->obj_types.size);
    for (sn_obj_id_t o = 0; o < m->obj_types.size; ++o) heads[o] = -1;
    for (sn_obj_id_t o = 0; o < m->obj_types.size; ++o) {
        if (movable[o]) {
            sn_obj_id_t f = sn_reg_fanin(m, o, SN_REG_DATA);
            if (opids[f] >= 0 && !(active[f] & 1)) { active[f] |= 1; Vec_IntPush(todo, (int)f); }
        }
        if (opids[o] < 0) continue;
        for (uint32_t k = 0; k < sn_obj_fanin_count(m, o); ++k) {
            sn_obj_id_t f = sn_obj_fanin(m, o, k);
            int e = Vec_IntSize(edges);
            Vec_IntPushTwo(edges, (int)o, heads[f]); heads[f] = e;
        }
    }
    while (Vec_IntSize(todo)) {
        sn_obj_id_t o = (sn_obj_id_t)Vec_IntPop(todo);
        for (uint32_t k = 0; k < sn_obj_fanin_count(m, o); ++k) {
            sn_obj_id_t f = sn_obj_fanin(m, o, k);
            if (opids[f] >= 0 && !(active[f] & 1)) { active[f] |= 1; Vec_IntPush(todo, (int)f); }
        }
    }
    for (sn_obj_id_t o = 0; o < m->obj_types.size; ++o)
        if (movable[o]) { active[o] |= 2; Vec_IntPush(todo, (int)o); }
    while (Vec_IntSize(todo)) {
        int o = Vec_IntPop(todo);
        for (int e = heads[o]; e >= 0; e = Vec_IntEntry(edges, e + 1)) {
            int fanout = Vec_IntEntry(edges, e);
            if (!(active[fanout] & 2)) { active[fanout] |= 2; Vec_IntPush(todo, fanout); }
        }
    }
    // Side inputs of a forward cone still contribute their real arrival times.
    for (sn_obj_id_t o = 0; o < m->obj_types.size; ++o)
        if (active[o] && opids[o] >= 0) { active[o] |= 4; Vec_IntPush(todo, (int)o); }
    while (Vec_IntSize(todo)) {
        sn_obj_id_t o = (sn_obj_id_t)Vec_IntPop(todo);
        for (uint32_t k = 0; k < sn_obj_fanin_count(m, o); ++k) {
            sn_obj_id_t f = sn_obj_fanin(m, o, k);
            if (opids[f] >= 0 && !(active[f] & 4)) { active[f] |= 4; Vec_IntPush(todo, (int)f); }
        }
    }
    ABC_FREE(heads); Vec_IntFree(edges); Vec_IntFree(todo);
    return active;
}

/**Function*************************************************************

  Synopsis    [Measures the maximum segment delay of a module.]

  Description [Report the maximum over all segments, independently of the active domain.
  Latch, memory, LOOP and opaque-cell outputs start new zero-arrival segments.
  Requires topological combinational IDs; Sn_RetRebuild restores this order
  after each domain's replay.]

***********************************************************************/
static int Sn_RetMeasure(const sn_module_t * m, int * configs)
{
    Hsh_VecMan_t * cache = Hsh_VecManStart(100);
    Vec_Ptr_t * ops = Vec_PtrAlloc(100);
    Vec_Int_t * key = Vec_IntAlloc(100);
    unsigned char * live = Sn_RetLive(m);
    int * arrival = ABC_CALLOC(int, m->obj_types.size), maximum = 0;
    for (sn_obj_id_t o = 0; o < m->obj_types.size; ++o) if (live[o] && Sn_RetTimed(m, o)) {
        int id = Sn_RetCache(m, o, cache, ops, key);
        for (uint32_t k = 0; k < sn_obj_fanin_count(m, o); ++k) {
            sn_obj_id_t f = sn_obj_fanin(m, o, k);
            assert(f < o || !Sn_RetTimed(m, f));
            arrival[o] = Abc_MaxInt(arrival[o], arrival[f]);
        }
        arrival[o] += ((Sn_RetOp_t *)Vec_PtrEntry(ops, id))->delay;
        maximum = Abc_MaxInt(maximum, arrival[o]);
    }
    if (configs) *configs = Vec_PtrSize(ops);
    ABC_FREE(arrival); ABC_FREE(live);
    Hsh_VecManStop(cache); Vec_IntFree(key); Sn_RetFreeOps(ops);
    return maximum;
}

/**Function*************************************************************

  Synopsis    [Connects a fanin and updates the replay fanout index.]

  Description [Connections are indexed once. Stale entries are checked before use, avoiding
  a full-module scan for each move; adding a connection never invalidates IDs.]

***********************************************************************/
static void Sn_RetConnect(sn_module_t * m, Vec_Int_t * heads, Vec_Int_t * edges,
                          sn_obj_id_t owner, uint32_t slot, sn_obj_id_t f)
{
    int edge = Vec_IntSize(edges);
    Vec_IntFillExtra(heads, (int)m->obj_types.size, -1);
    sn_obj_connect(m, owner, slot, f);
    if (f == SN_INVALID_ID) return;
    Vec_IntPush(edges, (int)owner);
    Vec_IntPush(edges, (int)slot);
    Vec_IntPush(edges, Vec_IntEntry(heads, f));
    Vec_IntWriteEntry(heads, f, edge);
}

/**Function*************************************************************

  Synopsis    [Copies register controls and the computed reset value.]

***********************************************************************/
static void Sn_RetCopyControls(sn_module_t * m, sn_obj_id_t q, sn_obj_id_t source,
                               const uint32_t * reset, Vec_Int_t * heads, Vec_Int_t * edges)
{
    sn_obj_id_t in = sn_reg_in(m, q);
    sn_reg_set_flags(m, q, sn_obj_reg_flags(m, source));
    for (int k = SN_REG_CLOCK; k <= SN_REG_RESET; ++k)
        Sn_RetConnect(m, heads, edges, in, (uint32_t)k, sn_reg_fanin(m, source, (sn_reg_fanin_t)k));
    if (reset) {
        sn_obj_id_t value = sn_module_add_const(m, sn_obj_width(m, q), false, reset, NULL);
        Sn_RetConnect(m, heads, edges, in, SN_REG_RESET_VALUE, value);
    }
}

/**Function*************************************************************

  Synopsis    [Validates and replays one forward operator move.]

***********************************************************************/
static int Sn_RetMove(sn_module_t * m, sn_obj_id_t o, Sn_RetOp_t * op,
                      Vec_Int_t * heads, Vec_Int_t * edges, Vec_Int_t * consumed,
                      int ignore_init, int entry, FILE * error)
{
    sn_obj_id_t reference = SN_INVALID_ID;
    uint32_t init[8], reset[8], preset[8];
    int has_reset, oldhead;
    sn_obj_pair_t pair;
    char name[64];
    for (int input = 0; input < Vec_IntSize(op->inputs); ++input) {
        uint32_t k = (uint32_t)Vec_IntEntry(op->inputs, input);
        sn_obj_id_t f = sn_obj_fanin(m, o, k);
        if (Sn_RetConst(m, f)) continue;
        if (!Sn_RetMovable(m, f, ignore_init)) {
            fprintf(error, "@retime: guidance entry %d, forward object %u, input %u: expected a movable register.\n", entry, o, k);
            return 0;
        }
        if (reference != SN_INVALID_ID && !Sn_RetSameControls(m, reference, f)) {
            fprintf(error, "@retime: guidance entry %d, forward object %u, input %u: incompatible register controls.\n", entry, o, k);
            return 0;
        }
        reference = f;
    }
    if (reference == SN_INVALID_ID) {
        fprintf(error, "@retime: guidance entry %d, forward object %u: no register remains on a nonconstant input.\n", entry, o);
        return 0;
    }
    if (!ignore_init) Sn_RetEval(m, o, op, SN_REG_INIT_DATA, init);
    has_reset = sn_reg_fanin(m, reference, SN_REG_RESET) != SN_INVALID_ID;
    if (has_reset) Sn_RetEval(m, o, op, SN_REG_RESET_VALUE, reset);
    if (sn_reg_fanin(m, reference, SN_REG_SET) != SN_INVALID_ID) {
        // SN's separate SET pin forces all ones. Do not silently change that
        // control into a reset, or lose its priority relative to RESET.
        Sn_RetEval(m, o, op, SN_REG_SET, preset);
        for (uint32_t b = 0; b < sn_obj_width(m, o); ++b)
            if (!(preset[b / 32] >> (b % 32) & 1)) {
                fprintf(error, "@retime: guidance entry %d, forward object %u: preset result is not representable by the SET pin.\n", entry, o);
                return -1;
            }
    }
    for (uint32_t k = 0; k < sn_obj_fanin_count(m, o); ++k) {
        sn_obj_id_t f = sn_obj_fanin(m, o, k);
        if (!Sn_RetConst(m, f)) {
            Vec_IntFillExtra(consumed, (int)m->obj_types.size, 0);
            Vec_IntWriteEntry(consumed, f, 1);
            Sn_RetConnect(m, heads, edges, o, k, sn_reg_fanin(m, f, SN_REG_DATA));
        }
    }
    snprintf(name, sizeof(name), "__sn_retime_%u_%u", o, (unsigned)m->obj_types.size);
    pair = sn_module_add_reg_pair(m, sn_obj_width(m, o), sn_obj_is_signed(m, o), name, NULL,
                                  sn_reg_fanin(m, reference, SN_REG_CLOCK));
    Sn_RetCopyControls(m, pair.out, reference, has_reset ? reset : NULL, heads, edges);
    if (!ignore_init) {
        sn_obj_id_t value = sn_module_add_const(m, sn_obj_width(m, o), false, init, NULL);
        Sn_RetConnect(m, heads, edges, pair.in, SN_REG_INIT_DATA, value);
    }
    Vec_IntFillExtra(heads, (int)m->obj_types.size, -1);
    // Include feedback exposed by bypassing input registers and new control
    // connections. Only the new register's D must continue to see the operator.
    oldhead = Vec_IntEntry(heads, o);
    for (int e = oldhead; e != -1; e = Vec_IntEntry(edges, e + 2)) {
        sn_obj_id_t owner = (sn_obj_id_t)Vec_IntEntry(edges, e);
        uint32_t slot = (uint32_t)Vec_IntEntry(edges, e + 1);
        if (sn_obj_fanin(m, owner, slot) == o) Sn_RetConnect(m, heads, edges, owner, slot, pair.out);
    }
    Sn_RetConnect(m, heads, edges, pair.in, SN_REG_DATA, o);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Validates and replays one backward operator move.]

  Description [Every use of the operator must enter the data pin of a compatible register.
  Solve initial and reset values for the new input registers independently;
  literal constants stay put. With -i, only the initial-state solve is skipped.]

***********************************************************************/
static int Sn_RetMoveBackward(sn_module_t * m, sn_obj_id_t o, Sn_RetOp_t * op,
                              Vec_Int_t * heads, Vec_Int_t * edges, Vec_Int_t * consumed,
                              int ignore_init, int conflicts, int * created, int entry, FILE * error)
{
    sn_obj_id_t reference = SN_INVALID_ID;
    Vec_Int_t * outputs = Vec_IntAlloc(4);
    Vec_Int_t * reset_bits = Vec_IntAlloc(0);
    Vec_Int_t * init_bits = Vec_IntAlloc(0);
    int has_reset, pi = 0, result = 0;
    const char * reason = "no registered output fanout";
    for (int e = Vec_IntEntry(heads, o); e != -1; e = Vec_IntEntry(edges, e + 2)) {
        sn_obj_id_t owner = (sn_obj_id_t)Vec_IntEntry(edges, e);
        uint32_t slot = (uint32_t)Vec_IntEntry(edges, e + 1);
        sn_obj_id_t q;
        if (sn_obj_fanin(m, owner, slot) != o) continue;
        if (sn_obj_type(m, owner) != SN_REG_IN || slot != SN_REG_DATA) {
            reason = "an output fanout is not a register data input"; goto fail;
        }
        q = sn_reg_out(m, owner);
        if (!Sn_RetMovable(m, q, ignore_init)) { reason = "an output register is not movable"; goto fail; }
        if (reference != SN_INVALID_ID && !Sn_RetSameControls(m, reference, q)) {
            reason = "output registers have incompatible controls"; goto fail;
        }
        reference = q;
        Vec_IntPushUnique(outputs, (int)q);
    }
    if (reference == SN_INVALID_ID) goto fail;
    has_reset = sn_reg_fanin(m, reference, SN_REG_RESET) != SN_INVALID_ID;
    for (int initial = 0; initial < 2; ++initial) {
        int mode = initial ? SN_REG_INIT_DATA : SN_REG_RESET_VALUE;
        int status;
        if (initial ? ignore_init : !has_reset) continue;
        for (int i = 0; i < Vec_IntSize(outputs); ++i)
            for (uint32_t b = 0; b < sn_obj_width(m, o); ++b)
                if (Sn_RetStateBit(m, reference, mode, b) !=
                    Sn_RetStateBit(m, (sn_obj_id_t)Vec_IntEntry(outputs, i), mode, b)) {
                    reason = initial ? "output registers have conflicting initial values" :
                                       "output registers have conflicting reset values";
                    result = -1; goto fail;
                }
        status = Sn_RetStatePreimage(m, o, op, reference, mode, initial ? init_bits : reset_bits, conflicts);
        if (status != 1) {
            reason = initial ? (status == 0 ? "no input initial values produce the required output state" : "initial-state SAT limit reached") :
                               (status == 0 ? "no input reset values produce the required output reset" : "reset-value SAT limit reached");
            result = -1; goto fail;
        }
    }
    if (sn_reg_fanin(m, reference, SN_REG_SET) != SN_INVALID_ID) {
        uint32_t preset[8];
        Sn_RetEval(m, o, op, SN_REG_SET, preset);
        for (uint32_t b = 0; b < sn_obj_width(m, o); ++b)
            if (!(preset[b / 32] >> (b % 32) & 1)) {
                reason = "input SET values do not produce the required output preset"; result = -1; goto fail;
            }
    }
    for (int input = 0; input < Vec_IntSize(op->inputs); ++input) {
        uint32_t k = (uint32_t)Vec_IntEntry(op->inputs, input);
        sn_obj_id_t f = sn_obj_fanin(m, o, k);
        sn_obj_pair_t pair;
        char name[64];
        uint32_t reset[32] = {0}, init[32] = {0};
        // Keep prototype PI offsets even for fanins made constant by replay.
        if (Sn_RetConst(m, f)) { pi += (int)sn_obj_width(m, f); continue; }
        if (has_reset || !ignore_init)
            for (uint32_t b = 0; b < sn_obj_width(m, f); ++b, ++pi) {
                if (has_reset && Vec_IntEntry(reset_bits, pi)) reset[b / 32] |= UINT32_C(1) << (b % 32);
                if (!ignore_init && Vec_IntEntry(init_bits, pi)) init[b / 32] |= UINT32_C(1) << (b % 32);
            }
        snprintf(name, sizeof(name), "__sn_retime_%u_%u", o, (unsigned)m->obj_types.size);
        pair = sn_module_add_reg_pair(m, sn_obj_width(m, f), sn_obj_is_signed(m, f), name, NULL,
                                      sn_reg_fanin(m, reference, SN_REG_CLOCK));
        Sn_RetCopyControls(m, pair.out, reference, has_reset ? reset : NULL, heads, edges);
        if (!ignore_init) {
            sn_obj_id_t value = sn_module_add_const(m, sn_obj_width(m, f), false, init, NULL);
            Sn_RetConnect(m, heads, edges, pair.in, SN_REG_INIT_DATA, value);
        }
        Sn_RetConnect(m, heads, edges, pair.in, SN_REG_DATA, f);
        Sn_RetConnect(m, heads, edges, o, k, pair.out);
        ++*created;
    }
    for (int i = 0; i < Vec_IntSize(outputs); ++i) {
        sn_obj_id_t q = (sn_obj_id_t)Vec_IntEntry(outputs, i);
        // This also redirects feedback entering a newly created register's D.
        for (int e = Vec_IntEntry(heads, q); e != -1; e = Vec_IntEntry(edges, e + 2)) {
            sn_obj_id_t owner = (sn_obj_id_t)Vec_IntEntry(edges, e);
            uint32_t slot = (uint32_t)Vec_IntEntry(edges, e + 1);
            if (sn_obj_fanin(m, owner, slot) == q) Sn_RetConnect(m, heads, edges, owner, slot, o);
        }
        Vec_IntFillExtra(consumed, (int)m->obj_types.size, 0);
        Vec_IntWriteEntry(consumed, q, 1);
        // The dead D pin must not look like an extra registered fanout to a
        // subsequent backward move. Both halves are removed before validation.
        Sn_RetConnect(m, heads, edges, sn_reg_in(m, q), SN_REG_DATA, SN_INVALID_ID);
    }
    Vec_IntFree(outputs);
    Vec_IntFree(reset_bits);
    Vec_IntFree(init_bits);
    return 1;
fail:
    fprintf(error, "@retime: guidance entry %d, backward object %u: %s.\n", entry, o, reason);
    Vec_IntFree(outputs);
    Vec_IntFree(reset_bits);
    Vec_IntFree(init_bits);
    return result;
}

/**Function*************************************************************

  Synopsis    [Retires consumed registers that no longer drive live logic.]

  Description [Retire only unused, previously validated consumed register outputs.
  Mark retired pairs as temporary constants and rebuild inverse type lists.
  Sn_RetRebuild removes these placeholders and other unreferenced constants.]

***********************************************************************/
static unsigned Sn_RetRetire(sn_module_t * m, Vec_Int_t * consumed)
{
    unsigned removed = 0;
    uint32_t * refs = ABC_CALLOC(uint32_t, m->obj_types.size);
    uint8_t * dead = ABC_CALLOC(uint8_t, m->obj_types.size);
    unsigned char * live = Sn_RetLive(m);
    for (sn_obj_id_t o = 0; o < m->obj_types.size; ++o) if (live[o])
        for (uint32_t k = 0; k < sn_obj_fanin_count(m, o); ++k) {
            sn_obj_id_t f = sn_obj_fanin(m, o, k);
            if (f != SN_INVALID_ID && !sn_obj_type_is_pair_out(sn_obj_type(m, o))) ++refs[f];
        }
    for (size_t i = 0; i < m->type_objects[SN_REG_OUT].size; ++i) {
        sn_obj_id_t o = sn_vec_at(sn_obj_id_t, &m->type_objects[SN_REG_OUT], i);
        if (!refs[o] && o < (unsigned)Vec_IntSize(consumed) && Vec_IntEntry(consumed, o)) {
            dead[o] = dead[sn_reg_in(m, o)] = 1;
            ++removed;
        }
    }
    for (int t = 0; t < SN_OBJ_TYPE_COUNT; ++t) m->type_objects[t].size = 0;
    for (sn_obj_id_t o = 0; o < m->obj_types.size; ++o) {
        sn_obj_type_t type = sn_obj_type(m, o);
        if (dead[o]) {
            uint32_t zero = 0;
            type = SN_CONST0;
            sn_vec_at(sn_obj_type_t, &m->obj_types, o) = type;
            sn_vec_at(sn_fanin_count_t, &m->fanin_counts, o) = 0;
            sn_vec_at(uint32_t, &m->obj_data, o) = sn_design_intern_const(m->design, 1, &zero);
        }
        if (sn_obj_type_has_dense_index(type)) sn_vec_at(uint32_t, &m->obj_data, o) = (uint32_t)m->type_objects[type].size;
        *sn_vec_push(sn_obj_id_t, &m->type_objects[type]) = o;
    }
    {
        size_t n = 0;
        for (size_t i = 0; i < m->attribute_records.size; ++i) {
            sn_attribute_record_t a = sn_vec_at(sn_attribute_record_t, &m->attribute_records, i);
            if (a.object == SN_INVALID_ID || !dead[a.object]) sn_vec_at(sn_attribute_record_t, &m->attribute_records, n++) = a;
        }
        m->attribute_records.size = n;
    }
    ABC_FREE(refs); ABC_FREE(dead); ABC_FREE(live);
    return removed;
}

/**Function*************************************************************

  Synopsis    [Counts register bits, excluding pairs eligible for retirement.]

  Description [With a replay mask, use the same live-fanout criterion as
  Sn_RetRetire. Shared data and control fanouts keep the whole register.]

***********************************************************************/
static uint64_t Sn_RetRegisterBits(const sn_module_t * m, Vec_Int_t * consumed)
{
    uint64_t bits = 0;
    unsigned char * used = NULL, * live = NULL;
    if (consumed) {
        used = ABC_CALLOC(unsigned char, m->obj_types.size);
        live = Sn_RetLive(m);
        for (sn_obj_id_t o = 0; o < m->obj_types.size; ++o)
            if (live[o] && !sn_obj_type_is_pair_out(sn_obj_type(m, o)))
                for (uint32_t k = 0; k < sn_obj_fanin_count(m, o); ++k) {
                    sn_obj_id_t f = sn_obj_fanin(m, o, k);
                    if (f != SN_INVALID_ID) used[f] = 1;
                }
    }
    for (size_t i = 0; i < m->type_objects[SN_REG_OUT].size; ++i) {
        sn_obj_id_t q = sn_vec_at(sn_obj_id_t, &m->type_objects[SN_REG_OUT], i);
        if (!consumed || q >= (unsigned)Vec_IntSize(consumed) || !Vec_IntEntry(consumed, q) || used[q])
            bits += sn_obj_width(m, q);
    }
    ABC_FREE(used); ABC_FREE(live);
    return bits;
}

/**Function*************************************************************

  Synopsis    [Removes dead logic and remaps clock-domain literals.]

***********************************************************************/
static sn_module_id_t Sn_RetRebuild(sn_design_t * design, sn_module_id_t module, Vec_Int_t * domains)
{
    sn_module_t * m = sn_design_get_module(design, module);
    uint8_t * remove = Sn_RetLive(m);
    sn_module_id_t result;
    for (sn_obj_id_t o = 0; o < m->obj_types.size; ++o) remove[o] = !remove[o];
    result = sn_boundary_dup_filtered_topo(design, module, remove, "__sn_retimed");
    for (int i = 0; i < Vec_IntSize(domains); i += 2) {
        int clock_lit = Vec_IntEntry(domains, i);
        sn_obj_id_t copy = sn_vec_at(sn_obj_id_t, &m->copy_ids, (unsigned)clock_lit >> 1);
        assert(copy != SN_INVALID_ID); // Every clock cone is protected.
        Vec_IntWriteEntry(domains, i, (int)(2 * copy + (clock_lit & 1)));
    }
    ABC_FREE(remove);
    return result;
}

typedef struct Sn_RetStats_t_ {
    int moves, created, retired, backward;
} Sn_RetStats_t;

/**Function*************************************************************

  Synopsis    [Searches and replays retiming in one clock domain.]

***********************************************************************/
static int Sn_RetDomain(sn_design_t * design, sn_module_id_t module, Vec_Int_t * domains, int domain,
                        int steps, int ignore_init, int direction, int verbose, int conflicts, uint64_t bit_limit,
                        Sn_RetStats_t * stats, FILE * out, FILE * error)
{
    sn_module_t * m = sn_design_get_module(design, module);
    size_t n = m->obj_types.size;
    char network_name[] = "sn_retime";
    Wln_Ntk_t * w = NULL;
    Hsh_VecMan_t * cache = Hsh_VecManStart(100);
    Hsh_VecMan_t * classes = Hsh_VecManStart(16);
    Vec_Ptr_t * ops = Vec_PtrAlloc(100);
    Vec_Int_t * class_nodes = Vec_IntAlloc(16);
    Vec_Int_t * key = Vec_IntAlloc(100), * moves = NULL;
    Vec_Int_t * heads = Vec_IntAlloc(100), * edges = Vec_IntAlloc(100);
    Vec_Int_t * consumed = Vec_IntAlloc(100);
    int * map = ABC_CALLOC(int, n), * opids = ABC_ALLOC(int, n);
    unsigned char * allowed = NULL, * movable = ABC_CALLOC(unsigned char, n), * live = NULL;
    unsigned char * fixed = Sn_RetProtectClocks(m), * active = NULL;
    sn_module_id_t trial = SN_INVALID_ID;
    int success = 0, eligible = 0, best = 0, end = 0, count = 0, created = 0, backward = 0;
    int kept_end = 0, kept_delay = 0;
    if (n > INT_MAX / 16) { fprintf(error, "@retime: module is too large for WLN IDs.\n"); goto cleanup; }
    for (size_t i = 0; i < n; ++i) opids[i] = -1;
    // The WLN search uses recursive walks. Refuse pathological recursion and
    // signed-int edge-index overflow rather than risking a process crash.
    {
        uint64_t edgesCount = 0;
        int * depth = ABC_CALLOC(int, n);
        for (sn_obj_id_t o = 0; o < n; ++o) {
            edgesCount += sn_obj_fanin_count(m, o);
            if (sn_obj_type_is_pair_out(sn_obj_type(m, o))) continue;
            for (uint32_t k = 0; k < sn_obj_fanin_count(m, o); ++k) {
                sn_obj_id_t f = sn_obj_fanin(m, o, k);
                if (f != SN_INVALID_ID && f < o) depth[o] = Abc_MaxInt(depth[o], depth[f] + 1);
            }
            if (depth[o] > 2048 || edgesCount > INT_MAX / 6) {
                ABC_FREE(depth);
                fprintf(error, "@retime: module exceeds first-version graph depth/edge limits.\n"); goto cleanup;
            }
        }
        ABC_FREE(depth);
    }
    for (size_t i = 0; i < m->type_objects[SN_REG_OUT].size; ++i) {
        sn_obj_id_t o = sn_vec_at(sn_obj_id_t, &m->type_objects[SN_REG_OUT], i);
        movable[o] = !fixed[o] && Sn_RetMovable(m, o, ignore_init) &&
                     Sn_RetRegControl(m, o, SN_REG_CLOCK) == Vec_IntEntry(domains, 2 * domain) &&
                     (int)(sn_obj_reg_flags(m, o) & SN_REG_CLOCK_NEGEDGE) == Vec_IntEntry(domains, 2 * domain + 1);
        eligible += movable[o];
    }
    if (!eligible) { success = 1; goto cleanup; }
    live = Sn_RetLive(m);
    for (sn_obj_id_t o = 0; o < n; ++o)
        if (live[o] && Sn_RetTimed(m, o)) opids[o] = Sn_RetCache(m, o, cache, ops, key);
    active = Sn_RetCone(m, movable, opids);
    w = Wln_NtkAlloc(network_name, (int)n * 2 + 16);
    for (sn_obj_id_t o = 0; o < n; ++o) {
        int type = ABC_OPER_CI;
        if (!live[o] || sn_obj_type(m, o) == SN_REG_IN) continue;
        if (movable[o]) type = ABC_OPER_DFFRSE;
        else if (Sn_RetConst(m, o)) type = ABC_OPER_CONST;
        else if (opids[o] >= 0 && active[o]) type = ABC_OPER_BIT_BUF;
        map[o] = Wln_ObjAlloc(w, type, 0, (int)sn_obj_width(m, o) - 1, 0);
    }
    for (sn_obj_id_t o = 0; o < n; ++o) {
        int id = map[o];
        if (!id) continue;
        if (movable[o]) {
            int class_id;
            Sn_RetClassKey(m, o, key);
            class_id = Hsh_VecManAdd(classes, key);
            // A unique zero-delay constant encodes the full SN control class
            // in WLN's FF-control tuple, without making controls into D paths.
            if (class_id == Vec_IntSize(class_nodes))
                Vec_IntPush(class_nodes, Wln_ObjAlloc(w, ABC_OPER_CONST, 0, 0, 0));
            Wln_ObjAddFanin(w, id, map[sn_reg_fanin(m, o, SN_REG_DATA)]);
            Wln_ObjAddFanin(w, id, Vec_IntEntry(class_nodes, class_id));
            for (int k = 2; k < 8; ++k) Wln_ObjAddFanin(w, id, 0);
            // Real control uses remain fixed sinks. In particular, backward
            // retiming may not consume a register's enable/reset logic.
            for (int k = SN_REG_CLOCK; k <= SN_REG_RESET; ++k) {
                sn_obj_id_t f = sn_reg_fanin(m, o, (sn_reg_fanin_t)k);
                if (f != SN_INVALID_ID && map[f]) {
                    int co = Wln_ObjAlloc(w, ABC_OPER_CO, 0, 0, 0);
                    Wln_ObjAddFanin(w, co, map[f]);
                }
            }
        } else if (opids[o] >= 0 && active[o]) {
            for (uint32_t k = 0; k < sn_obj_fanin_count(m, o); ++k) Wln_ObjAddFanin(w, id, map[sn_obj_fanin(m, o, k)]);
        } else if (!Sn_RetConst(m, o)) {
            // Opaque nodes have independent outputs and fixed input sinks.
            sn_obj_id_t owner = sn_obj_type(m, o) == SN_REG_OUT ? sn_reg_in(m, o) : o;
            if (sn_obj_type_is_pair_out(sn_obj_type(m, o)) && owner == o) continue;
            for (uint32_t k = 0; k < sn_obj_fanin_count(m, owner); ++k) {
                sn_obj_id_t f = sn_obj_fanin(m, owner, k);
                if (f != SN_INVALID_ID && map[f]) {
                    int co = Wln_ObjAlloc(w, ABC_OPER_CO, 0, 0, 0);
                    Wln_ObjAddFanin(w, co, map[f]);
                }
            }
        }
    }
    Wln_NtkCleanNameId(w); Wln_NtkCleanInstId(w);
    allowed = ABC_CALLOC(unsigned char, Wln_NtkObjNum(w));
    for (sn_obj_id_t o = 0; o < n; ++o) if (map[o]) {
        Wln_ObjSetNameId(w, map[o], (int)o + 1);
        if (opids[o] >= 0 && active[o]) {
            Wln_ObjSetInstId(w, map[o], ((Sn_RetOp_t *)Vec_PtrEntry(ops, opids[o]))->delay);
            allowed[map[o]] = !fixed[o] && Sn_RetOperator(m, o) &&
                             Vec_IntSize(((Sn_RetOp_t *)Vec_PtrEntry(ops, opids[o]))->inputs) > 0;
        } else if (movable[o]) {
            // The edge links carry all state. This vertex is an identity whose
            // virtual moves only change which side holds those links.
            Wln_ObjSetInstId(w, map[o], 0);
            allowed[map[o]] = 1;
        }
    }
retry:
    // Replay on an ID-preserving private module, including in preview mode.
    // A state-infeasible operator is excluded and the search starts afresh;
    // no partially replayed batch can leak into the installed design.
    Vec_IntFreeP(&moves);
    best = end = 0;
    moves = Wln_NtkRetimeRestricted(w, allowed, steps, direction, verbose);
    if (!moves || Vec_IntSize(moves) < 2 || Vec_IntEntry(moves, 1) != 0) {
        fprintf(error, "@retime: invalid guidance header; expected initial delay and terminator.\n"); goto cleanup;
    }
    best = Vec_IntEntry(moves, 0);
    for (int i = 2; i < Vec_IntSize(moves);) {
        int delay = Vec_IntEntry(moves, i++);
        while (i < Vec_IntSize(moves) && Vec_IntEntry(moves, i)) ++i;
        if (i == Vec_IntSize(moves)) {
            fprintf(error, "@retime: guidance entry %d: unterminated move batch.\n", i); goto cleanup;
        }
        ++i;
        if (delay < best) { best = delay; end = i; }
    }
replay:
    if (trial != SN_INVALID_ID) {
        sn_module_t * discard = sn_design_get_module(design, trial);
        assert(trial + 1 == design->modules.size);
        sn_module_destroy(discard); ABC_FREE(discard); --design->modules.size;
        trial = SN_INVALID_ID;
    }
    m = sn_design_get_module(design, module);
    Vec_IntClear(edges); Vec_IntClear(consumed);
    count = created = backward = kept_end = 0;
    kept_delay = Vec_IntEntry(moves, 0);
    if (!end) {
        fprintf(out, "@retime: domain %d/%d segment delay %d -> %d; %d movable registers.\n",
                domain + 1, Vec_IntSize(domains) / 2, Vec_IntEntry(moves, 0), best, eligible);
        success = 1; goto cleanup; }
    trial = sn_design_add_module_name_id(design, m->name);
    sn_module_dup_contents(sn_design_get_module(design, trial), m);
    m = sn_design_get_module(design, trial);
    Vec_IntFill(heads, (int)n, -1);
    for (sn_obj_id_t o = 0; o < n; ++o) if (live[o])
        for (uint32_t k = 0; k < sn_obj_fanin_count(m, o); ++k)
            Sn_RetConnect(m, heads, edges, o, k, sn_obj_fanin(m, o, k));
    for (int i = 2; i < end;) {
        int delay = Vec_IntEntry(moves, i++);
        for (; Vec_IntEntry(moves, i); ++i) {
            int move = Vec_IntEntry(moves, i);
            int replay;
            sn_obj_id_t o = (sn_obj_id_t)((move < 0 ? -(int64_t)move : move) - 1);
            if (o >= n) {
                fprintf(error, "@retime: guidance entry %d: object %u is out of range.\n", i, o); goto cleanup;
            }
            if (opids[o] < 0) {
                fprintf(error, "@retime: guidance entry %d: object %u is not a cached operator.\n", i, o); goto cleanup;
            }
            if (!allowed[map[o]]) {
                fprintf(error, "@retime: guidance entry %d: object %u is fixed in this clock domain.\n", i, o); goto cleanup;
            }
            if (move < 0) {
                if (direction == 1) {
                    fprintf(error, "@retime: guidance entry %d: forward move is disabled.\n", i); goto cleanup;
                }
                replay = Sn_RetMove(m, o, (Sn_RetOp_t *)Vec_PtrEntry(ops, opids[o]), heads, edges, consumed, ignore_init, i, error);
                ++created;
            } else {
                if (direction == 0) {
                    fprintf(error, "@retime: guidance entry %d: backward move is disabled.\n", i); goto cleanup;
                }
                replay = Sn_RetMoveBackward(m, o, (Sn_RetOp_t *)Vec_PtrEntry(ops, opids[o]), heads, edges, consumed, ignore_init, conflicts, &created, i, error);
                ++backward;
            }
            if (!replay) goto cleanup;
            if (replay < 0) {
                allowed[map[o]] = 0;
                fprintf(out, "@retime: excluding object %u from guidance to preserve initial/reset/set behavior; retrying.\n", o);
                goto retry;
            }
            ++count;
        }
        ++i;
        if (bit_limit != UINT64_MAX) {
            uint64_t bits = Sn_RetRegisterBits(m, consumed);
            if (bits > bit_limit) {
                fprintf(out, "@retime: batch ending at guidance entry %d requires %llu register bits (limit %llu); keeping the best earlier legal prefix.\n",
                        i - 1, (unsigned long long)bits, (unsigned long long)bit_limit);
                best = kept_delay; end = kept_end;
                goto replay;
            }
            if (delay < kept_delay) { kept_delay = delay; kept_end = i; }
        }
    }
    fprintf(out, "@retime: domain %d/%d segment delay %d -> %d; %d movable registers.\n",
            domain + 1, Vec_IntSize(domains) / 2, Vec_IntEntry(moves, 0), best, eligible);
    {
        unsigned removed = Sn_RetRetire(m, consumed);
        sn_name_id_t name = m->name;
        sn_module_id_t replacement = Sn_RetRebuild(design, trial, domains);
        sn_design_replace_appended_module(design, trial, name, replacement);
        sn_design_replace_appended_module(design, module, name, trial);
        trial = SN_INVALID_ID;
        stats->moves += count; stats->created += created;
        stats->retired += (int)removed; stats->backward += backward;
    }
    success = 2; // installed private replacement
cleanup:
    if (trial != SN_INVALID_ID) {
        sn_module_t * discard = sn_design_get_module(design, trial);
        assert(trial + 1 == design->modules.size);
        sn_module_destroy(discard); ABC_FREE(discard); --design->modules.size;
    }
    if (w) Wln_NtkFree(w);
    Sn_RetFreeOps(ops);
    Hsh_VecManStop(cache); Hsh_VecManStop(classes); Vec_IntFree(class_nodes);
    Vec_IntFree(key); Vec_IntFreeP(&moves);
    Vec_IntFree(heads); Vec_IntFree(edges);
    Vec_IntFree(consumed);
    ABC_FREE(map); ABC_FREE(opids); ABC_FREE(movable); ABC_FREE(allowed); ABC_FREE(live);
    ABC_FREE(fixed); ABC_FREE(active);
    return success;
}

/**Function*************************************************************

  Synopsis    [Stages and validates a complete clock-domain sweep.]

***********************************************************************/
int Sn_DesignRetimeWithLimits(sn_design_t * design, sn_module_id_t module, int preview,
                              int steps, int ignore_init, int direction, int verbose,
                              int growth, int conflicts, FILE * out, FILE * error)
{
    sn_module_t * m = sn_design_get_module(design, module);
    sn_module_id_t work = SN_INVALID_ID;
    Hsh_VecMan_t * seen = Hsh_VecManStart(16);
    Vec_Int_t * domains = Vec_IntAlloc(16), * key = Vec_IntAlloc(2);
    unsigned char * fixed = NULL;
    Sn_RetStats_t stats = {0, 0, 0, 0};
    int eligible = 0, latches = 0, before, after, configs, success = 0;
    uint64_t bits_before, bits_after, bit_limit = UINT64_MAX;
    if (direction < 0 || direction > 2) {
        fprintf(error, "@retime: invalid retiming direction.\n"); goto cleanup;
    }
    if (m->obj_types.size > INT_MAX / 16) {
        fprintf(error, "@retime: module is too large for WLN IDs.\n"); goto cleanup;
    }
    if ((growth && (growth < 100 || growth > 100000)) || conflicts < 0) {
        fprintf(error, "@retime: invalid register-growth or SAT-conflict limit.\n"); goto cleanup;
    }
    bits_before = Sn_RetRegisterBits(m, NULL);
    if (growth) {
        uint64_t extra = bits_before % 100 * growth / 100;
        if (bits_before / 100 <= (UINT64_MAX - extra) / growth)
            bit_limit = bits_before / 100 * growth + extra;
        fprintf(out, "@retime: register-bit limit %llu (%d%% of the input module's %llu bits).\n",
                (unsigned long long)bit_limit, growth, (unsigned long long)bits_before);
    }
    if (ignore_init)
        fprintf(out, "@retime: warning: -i optimizes estimated longest combinational-path delay and skips initial-state computation.\n"
                     "@retime: moved state is treated as don't-care, including known bits; new registers are uninitialized. Initial behavior is not guaranteed.\n");
    fixed = Sn_RetProtectClocks(m);
    for (size_t i = 0; i < m->type_objects[SN_REG_OUT].size; ++i) {
        sn_obj_id_t q = sn_vec_at(sn_obj_id_t, &m->type_objects[SN_REG_OUT], i);
        int id;
        latches += (sn_obj_reg_flags(m, q) & SN_REG_LATCH) != 0;
        if (fixed[q] || !Sn_RetMovable(m, q, ignore_init)) continue;
        ++eligible;
        Vec_IntClear(key);
        Vec_IntPushTwo(key, Sn_RetRegControl(m, q, SN_REG_CLOCK), sn_obj_reg_flags(m, q) & SN_REG_CLOCK_NEGEDGE);
        id = Hsh_VecManAdd(seen, key);
        if (2 * id == Vec_IntSize(domains)) Vec_IntAppend(domains, key);
    }
    fprintf(out, "@retime: %d movable %sregisters; %zu fixed registers; only matching control classes move together.\n",
            eligible, ignore_init ? "" : "initialized ", m->type_objects[SN_REG_OUT].size - eligible);
    fprintf(out, "@retime: %d clock/edge domains; %d latch and %zu LOOP boundaries have zero output arrival.\n",
            Vec_IntSize(domains) / 2, latches, m->type_objects[SN_LOOP_OUT].size);
    before = Sn_RetMeasure(m, &configs);
    if (eligible) {
        // Stage the complete domain sweep, including preview, before replacing
        // the original module. A later failure cannot expose an earlier move.
        work = sn_design_add_module_name_id(design, m->name);
        sn_module_dup_contents(sn_design_get_module(design, work), m);
        for (int i = 0; i < Vec_IntSize(domains) / 2; ++i) {
            if (verbose)
                fprintf(out, "@retime: searching domain %d, clock literal %d, %s edge.\n", i + 1,
                        Vec_IntEntry(domains, 2 * i), Vec_IntEntry(domains, 2 * i + 1) ? "falling" : "rising");
            if (!Sn_RetDomain(design, work, domains, i, steps, ignore_init, direction, verbose, conflicts, bit_limit, &stats, out, error))
                goto cleanup;
        }
    }
    after = stats.moves ? Sn_RetMeasure(sn_design_get_module(design, work), NULL) : before;
    bits_after = stats.moves ? Sn_RetRegisterBits(sn_design_get_module(design, work), NULL) : bits_before;
    assert(bits_after <= bit_limit);
    if (after > before) {
        fprintf(error, "@retime: domain sweep increased maximum segment delay from %d to %d; result discarded.\n", before, after);
        goto cleanup;
    }
    fprintf(out, "@retime: estimated delay %d -> %d; %d cached operator configurations.\n", before, after, configs);
    fprintf(out, "@retime: register bits %llu -> %llu.\n", (unsigned long long)bits_before, (unsigned long long)bits_after);
    if (!stats.moves)
        fprintf(out, "@retime: no improving legal %sguidance; design unchanged.\n",
                direction == 0 ? "forward " : direction == 1 ? "backward " : "");
    else if (preview)
        fprintf(out, "@retime: preview only; %d operator moves across clock domains; design unchanged.\n", stats.moves);
    else {
        sn_design_replace_appended_module(design, module, m->name, work);
        work = SN_INVALID_ID;
        fprintf(out, "@retime: replayed %d operator moves; created %d and retired %d word registers.\n",
                stats.moves, stats.created, stats.retired);
        fprintf(out, "@retime: directions: %d forward, %d backward.\n", stats.moves - stats.backward, stats.backward);
        fprintf(out, "@retime: one clock-domain sweep completed; another call may improve delay further.\n");
    }
    success = !preview && stats.moves ? 2 : 1;
cleanup:
    if (work != SN_INVALID_ID) {
        sn_module_t * discard = sn_design_get_module(design, work);
        assert(work + 1 == design->modules.size);
        sn_module_destroy(discard); ABC_FREE(discard); --design->modules.size;
    }
    ABC_FREE(fixed); Hsh_VecManStop(seen); Vec_IntFree(domains); Vec_IntFree(key);
    return success;
}

/**Function*************************************************************

  Synopsis    [Retimes with unlimited register growth and SAT conflicts.]

***********************************************************************/
int Sn_DesignRetime(sn_design_t * design, sn_module_id_t module, int preview,
                    int steps, int ignore_init, int direction, int verbose, FILE * out, FILE * error)
{
    return Sn_DesignRetimeWithLimits(design, module, preview, steps, ignore_init, direction, verbose, 0, 0, out, error);
}

ABC_NAMESPACE_IMPL_END
