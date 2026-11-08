/**CFile****************************************************************

  FileName    [snMux4.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Priority balancing and bus-aware compression for LUT4 mapping.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 28, 2026.]

  Revision    [$Id: snMux4.h,v 1.00 2026/09/28 00:00:00 alanmi Exp $]

***********************************************************************/
#ifndef SN_MUX4_H
#define SN_MUX4_H
#include "snRewrite.h"
ABC_NAMESPACE_HEADER_START

// Metzgen and Nancekievill, DAC 2005, "Multiplexer Restructuring for FPGA
// Implementation Cost Reduction". Like Str_MuxRestructArea_rec() in giaStr.c
// (&blut), group adjacent, single-use mux triplets. SN words already provide
// the bus grouping. Unlike the GIA pass, explicitly expose the two-4-LUT
// decomposition rather than relying on a subsequent mux decomposition pass.
// A tree dynamic program chooses disjoint connected triplets among eligible
// candidates. The paper's four/five-node packing rotations are not implemented.
typedef struct sn_mux4_stats_t {
    size_t modules, triplets, chains;
    uint64_t bits, controls, savings;
    size_t rotations, views, folds;
} sn_mux4_stats_t;

/**Function*************************************************************

  Synopsis    [Finds an unshared same-width mux through wiring.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline sn_obj_id_t sn_mux4_child(const sn_module_t* m, sn_obj_id_t o,
                                        uint32_t width, const uint32_t* refs, size_t count)
{
    while (o < count && refs[o] == 1 && sn_obj_width(m, o) == width) {
        sn_obj_type_t t = sn_obj_type(m, o);
        if (t == SN_MUX) return o;
        if (t != SN_BUF && t != SN_POS && t != SN_CAST) break;
        o = sn_obj_fanin(m, o, 0);
    }
    return SN_INVALID_ID;
}

/**Function*************************************************************

  Synopsis    [Returns one data branch of a mux.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline sn_obj_id_t sn_mux4_data(const sn_module_t* m, sn_obj_id_t o, unsigned side)
{
    return sn_obj_fanin(m, o, side ? SN_MUX_SELECTED : SN_MUX_DEFAULT);
}

// At most three muxes are traversed, even in a deeply nested source design.
/**Function*************************************************************

  Synopsis    [Expands a three-mux group into its data leaves.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int sn_mux4_expand(const sn_module_t* m, sn_obj_id_t o, const sn_obj_id_t nodes[3],
                                  uint32_t width, const uint32_t* refs, size_t count,
                                  int edges[3][2], sn_obj_id_t leaves[4], unsigned* nleaves)
{
    sn_obj_id_t child = o == nodes[0] ? o : sn_mux4_child(m, o, width, refs, count);
    for (int k = 0; k < 3; ++k)
        if (child == nodes[k]) {
            for (unsigned side = 0; side < 2; ++side)
                edges[k][side] = sn_mux4_expand(m, sn_mux4_data(m, child, side), nodes,
                    width, refs, count, edges, leaves, nleaves);
            return k;
        }
    assert(*nleaves < 4);
    leaves[*nleaves] = o;
    return -(int)++*nleaves;
}

// Canonicalize repeated select IDs before making the small control truth table.
// Constants and complemented projections need no LUT; every other function
// of these (at most three) controls costs at most one LUT4.
/**Function*************************************************************

  Synopsis    [Estimates the LUT cost of a recoded selector.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned sn_mux4_control_cost(unsigned truth, unsigned count)
{
    unsigned mask = (1u << (1u << count)) - 1;
    if (!truth || truth == mask) return 0;
    for (unsigned k = 0; k < count; ++k) {
        unsigned projection = 0;
        for (unsigned v = 0; v < (1u << count); ++v)
            if ((v >> k) & 1) projection |= 1u << v;
        if (truth == projection || truth == (projection ^ mask)) return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Builds a recoded scalar selector.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline sn_obj_id_t sn_mux4_control(sn_module_t* m, unsigned truth, unsigned count,
                                          const sn_obj_id_t* controls)
{
    unsigned mask = (1u << (1u << count)) - 1;
    if (!truth || truth == mask) {
        uint32_t value = truth != 0;
        return sn_module_add_const(m, 1, false, &value, NULL);
    }
    for (unsigned k = 0; k < count; ++k) {
        unsigned projection = 0;
        for (unsigned v = 0; v < (1u << count); ++v)
            if ((v >> k) & 1) projection |= 1u << v;
        if (truth == projection) return controls[k];
        if (truth == (projection ^ mask))
            return sn_module_add_operator(m, SN_BIT_NOT, 1, false, 1, controls+k, NULL);
    }
    return sn_module_add_lut(m, count, controls, truth, NULL);
}

/**Function*************************************************************

  Synopsis    [Builds a word-level binary operator.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline sn_obj_id_t sn_mux4_binary(sn_module_t* m, sn_obj_type_t type, uint32_t width,
                                         sn_obj_id_t a, sn_obj_id_t b)
{
    sn_obj_id_t args[2] = {a, b};
    return sn_module_add_operator(m, type, width, false, 2, args, NULL);
}

/**Function*************************************************************

  Synopsis    [Replicates a scalar selector across a word.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline sn_obj_id_t sn_mux4_repeat(sn_module_t* m, sn_obj_id_t bit, uint32_t width)
{
    if (width == 1) return bit;
    sn_obj_id_t result = sn_module_add_operator(m, SN_REPLICATE, width, false, 1, &bit, NULL);
    sn_obj_set_data(m, result, width);
    return result;
}

/**Function*************************************************************

  Synopsis    [Retires mux objects made dead by a rewrite.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void sn_mux4_release(sn_module_t* m, sn_obj_id_t o, uint32_t* refs, sn_vec_t* pending)
{
    *sn_vec_push(sn_obj_id_t, pending) = o;
    while (pending->size) {
        sn_obj_id_t f = sn_vec_at(sn_obj_id_t, pending, --pending->size);
        assert(refs[f]);
        if (--refs[f] || !sn_obj_type_is_operator(sn_obj_type(m, f))) continue;
        for (uint32_t k = 0; k < sn_obj_fanin_count(m, f); ++k)
            *sn_vec_push(sn_obj_id_t, pending) = sn_obj_fanin(m, f, k);
        sn_vec_at(sn_obj_type_t, &m->obj_types, f) = SN_CONST0;
        sn_vec_at(sn_fanin_count_t, &m->fanin_counts, f) = 0;
        uint32_t zero = 0;
        sn_vec_at(uint32_t, &m->obj_data, f) = sn_design_intern_const(m->design, 1, &zero);
    }
}

/**Function*************************************************************

  Synopsis    [Restores module type lists and topological order.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void sn_mux4_rebuild(sn_design_t* d, sn_module_id_t id)
{
    sn_rewrite_rebuild(d, id);
}

/**Function*************************************************************

  Synopsis    [Distributes a slice or replicate over an unshared mux tree.]

  Description [Leaves other logic intact; at most 128 muxes are exposed.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline sn_obj_id_t sn_mux4_view(sn_module_t* m, sn_obj_id_t o, sn_obj_type_t type,
    uint32_t data, uint32_t width, const uint32_t* refs, size_t n, unsigned* budget)
{
    sn_obj_id_t child = sn_mux4_child(m, o, sn_obj_width(m, o), refs, n);
    if (*budget && child != SN_INVALID_ID) {
        --*budget;
        sn_obj_id_t args[3];
        args[SN_MUX_SELECT] = sn_obj_fanin(m, child, SN_MUX_SELECT);
        for (unsigned side = 0; side < 2; ++side)
            args[side ? SN_MUX_SELECTED : SN_MUX_DEFAULT] =
                sn_mux4_view(m, sn_mux4_data(m, child, side), type, data, width, refs, n, budget);
        return sn_module_add_operator(m, SN_MUX, width, false, 3, args, NULL);
    }
    sn_obj_id_t result = sn_module_add_operator(m, type, width, false, 1, &o, NULL);
    sn_obj_set_data(m, result, data);
    return result;
}

/**Function*************************************************************

  Synopsis    [Makes bus-uniform views visible to mux matching.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void sn_mux4_views(sn_design_t* d, sn_module_id_t id, sn_mux4_stats_t* stats)
{
    sn_module_t* m = sn_design_get_module(d, id);
    size_t n = m->obj_types.size, before = stats->views;
    uint32_t* refs = (uint32_t*)calloc(n ? n : 1, sizeof(uint32_t));
    uint32_t* slices = (uint32_t*)calloc(n ? n : 1, sizeof(uint32_t));
    uint64_t* bits = (uint64_t*)calloc(n ? n : 1, sizeof(uint64_t));
    unsigned char* shared = (unsigned char*)calloc(n ? n : 1, 1);
    sn_vec_t pending; sn_vec_init(&pending); assert(refs && slices && bits && shared);
    for (sn_obj_id_t o = 0; o < n; ++o)
        for (uint32_t k = 0; k < sn_obj_fanin_count(m, o); ++k) {
            sn_obj_id_t f = sn_obj_fanin(m, o, k); if (f != SN_INVALID_ID) ++refs[f];
        }
    for (sn_obj_id_t o = 0; o < n; ++o)
        if (sn_obj_type(m, o) == SN_SLICE && refs[o]) {
            sn_obj_id_t f = sn_obj_fanin(m, o, 0);
            ++slices[f]; bits[f] += sn_obj_width(m, o);
        }
    for (sn_obj_id_t o = 0; o < n; ++o)
        shared[o] = refs[o] > 1 && refs[o] == slices[o] && slices[o] <= 32 && bits[o] <= sn_obj_width(m, o);
    for (sn_obj_id_t o = 0; o < n; ++o) {
        sn_obj_type_t type = sn_obj_type(m, o);
        if ((type != SN_SLICE && type != SN_REPLICATE) || !refs[o]) continue;
        sn_obj_id_t old = sn_obj_fanin(m, o, 0);
        if (sn_obj_width(m, o) < 4 && !shared[old]) continue;
        // All users of this shared root are bounded slices. Expose the root
        // as if private, but restore its actual use count before retirement.
        uint32_t uses = refs[old];
        if (shared[old]) refs[old] = 1;
        if (sn_mux4_child(m, old, sn_obj_width(m, old), refs, n) == SN_INVALID_ID) {
            refs[old] = uses; continue;
        }
        unsigned budget = 128;
        size_t first = m->obj_types.size;
        sn_obj_id_t result = sn_mux4_view(m, old, type, sn_obj_data(m, o), sn_obj_width(m, o), refs, n, &budget);
        refs[old] = uses;
        for (sn_obj_id_t j = (sn_obj_id_t)first; j < m->obj_types.size; ++j)
            for (uint32_t k = 0; k < sn_obj_fanin_count(m, j); ++k) {
                sn_obj_id_t f = sn_obj_fanin(m, j, k); if (f < n) ++refs[f];
            }
        sn_vec_at(sn_obj_type_t, &m->obj_types, o) = SN_BUF;
        sn_obj_connect(m, o, 0, result);
        sn_mux4_release(m, old, refs, &pending);
        ++stats->views;
    }
    free(shared); free(bits); free(slices); free(refs); sn_vec_destroy(&pending);
    if (stats->views != before) sn_rewrite_rebuild(d, id);
}

#define SN_MUX4_ROTATE_MAX 128
typedef struct sn_mux4_group_t { sn_obj_id_t valid, data; } sn_mux4_group_t;

// Ordered tournament: a valid left group always wins over the right group.
// Recursion depth is logarithmic, even for an arbitrarily long source chain.
/**Function*************************************************************

  Synopsis    [Builds an ordered priority tournament.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline sn_mux4_group_t sn_mux4_tournament(sn_module_t* m, sn_mux4_group_t* items,
                                                size_t count, uint32_t width)
{
    if (count == 1) return items[0];
    size_t half = count / 2;
    sn_mux4_group_t l = sn_mux4_tournament(m, items, half, width);
    sn_mux4_group_t r = sn_mux4_tournament(m, items + half, count - half, width), result;
    sn_obj_id_t args[3];
    args[SN_MUX_SELECT] = l.valid; args[SN_MUX_SELECTED] = l.data; args[SN_MUX_DEFAULT] = r.data;
    result.data = sn_module_add_operator(m, SN_MUX, width, false, 3, args, NULL);
    result.valid = sn_mux4_binary(m, SN_BIT_OR, 1, l.valid, r.valid);
    return result;
}

/**Function*************************************************************

  Synopsis    [Balances long single-use priority chains.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void sn_mux4_balance(sn_design_t* d, sn_module_id_t id, sn_mux4_stats_t* stats, unsigned threshold)
{
    sn_module_t* m = sn_design_get_module(d, id);
    size_t n = m->obj_types.size, before = stats->chains;
    uint32_t* refs = (uint32_t*)calloc(n ? n : 1, sizeof(uint32_t));
    sn_vec_t items, pending; sn_vec_init(&items); sn_vec_init(&pending); assert(refs);
    for (sn_obj_id_t o = 0; o < n; ++o)
        for (uint32_t k = 0; k < sn_obj_fanin_count(m, o); ++k) {
            sn_obj_id_t f = sn_obj_fanin(m, o, k); if (f != SN_INVALID_ID) ++refs[f];
        }
    // Visit roots before children; do not revisit newly created tournament muxes.
    for (size_t i = n; i-- > 0;) {
        sn_obj_id_t root = (sn_obj_id_t)i, o = root;
        if (sn_obj_type(m, root) != SN_MUX || !refs[root]) continue;
        uint32_t width = sn_obj_width(m, root);
        items.size = 0;
        while (1) {
            sn_obj_id_t child[2];
            for (unsigned s = 0; s < 2; ++s) child[s] = sn_mux4_child(m, sn_mux4_data(m, o, s), width, refs, n);
            if ((child[0] != SN_INVALID_ID) == (child[1] != SN_INVALID_ID)) break;
            unsigned continuation = child[1] != SN_INVALID_ID;
            sn_mux4_group_t* item = sn_vec_push(sn_mux4_group_t, &items);
            // Store polarity temporarily; construct only after accepting the chain.
            item->valid = sn_obj_fanin(m, o, SN_MUX_SELECT);
            item->data = sn_mux4_data(m, o, !continuation);
            *sn_vec_push(sn_obj_id_t, &pending) = continuation;
            o = child[continuation];
        }
        // Keep the linear-time logarithmic-depth construction for long chains;
        // exhaustive critical-path pairs are best suited to smaller trees.
        if (items.size + 1 < (threshold ? threshold : width >= 4 ? 8u : 32u)) { pending.size = 0; continue; }
        sn_mux4_group_t* item = sn_vec_push(sn_mux4_group_t, &items);
        item->valid = sn_obj_fanin(m, o, SN_MUX_SELECT); item->data = sn_mux4_data(m, o, 1);
        *sn_vec_push(sn_obj_id_t, &pending) = 0;
        item = sn_vec_push(sn_mux4_group_t, &items);
        item->data = sn_mux4_data(m, o, 0);
        uint32_t one = 1; item->valid = sn_module_add_const(m, 1, false, &one, NULL);
        for (size_t k = 0; k < items.size; ++k) {
            item = &sn_vec_at(sn_mux4_group_t, &items, k);
            ++refs[item->data];
            if (k + 1 == items.size) continue;
            ++refs[item->valid];
            if (sn_vec_at(sn_obj_id_t, &pending, k))
                item->valid = sn_module_add_operator(m, SN_BIT_NOT, 1, false, 1, &item->valid, NULL);
        }
        pending.size = 0;
        sn_obj_id_t old[3]; for (unsigned k = 0; k < 3; ++k) old[k] = sn_obj_fanin(m, root, k);
        sn_mux4_group_t result = sn_mux4_tournament(m, (sn_mux4_group_t*)items.data, items.size, width);
        sn_vec_at(sn_obj_type_t, &m->obj_types, root) = SN_BUF;
        sn_vec_at(sn_fanin_count_t, &m->fanin_counts, root) = 1;
        sn_obj_connect(m, root, 0, result.data);
        for (unsigned k = 0; k < 3; ++k) sn_mux4_release(m, old[k], refs, &pending);
        ++stats->chains;
    }
    free(refs); sn_vec_destroy(&items); sn_vec_destroy(&pending);
    if (stats->chains != before) sn_mux4_rebuild(d, id);
}

// Port of Str_Delay2/3 and Str_MuxTryOnce in giaStr.c. Low four bits
// describe the current LUT's input budget; high bits describe completed levels.
/**Function*************************************************************

  Synopsis    [Estimates LUT arrival and input occupancy.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned sn_mux4_delay(unsigned a, unsigned b, unsigned c, bool three)
{
    unsigned d = a >> 4;
    if ((b >> 4) > d) d = b >> 4;
    if (three && (c >> 4) > d) d = c >> 4;
    unsigned n = ((a >> 4) == d ? a & 15 : 1) + ((b >> 4) == d ? b & 15 : 1);
    if (three) n += (c >> 4) == d ? c & 15 : 1;
    return (d << 4) + (n > 4 ? (three ? 19 : 18) : n);
}

/**Function*************************************************************

  Synopsis    [Estimates a four-input cone without counting reconvergence twice.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned sn_mux4_delay4(unsigned a, unsigned b, unsigned c, unsigned e)
{
    unsigned inputs[4] = {a, b, c, e}, level = 0, count = 0;
    for (unsigned i = 0; i < 4; ++i)
        if ((inputs[i] >> 4) > level) level = inputs[i] >> 4;
    for (unsigned i = 0; i < 4; ++i)
        count += (inputs[i] >> 4) == level ? inputs[i] & 15 : 1;
    return (level << 4) + (count > 4 ? 20 : count);
}

/**Function*************************************************************

  Synopsis    [Recognizes wiring from a primary or register input boundary.]

  Description [The word-level arrival estimate does not model the bit-level
               depth of arbitrary arithmetic, reductions, or selector logic.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline bool sn_mux4_boundary_word(const sn_module_t* m, sn_obj_id_t o)
{
    for (;;) {
        sn_obj_type_t type = sn_obj_type(m, o);
        if (type == SN_PI || type == SN_REG_OUT) return true;
        if (type != SN_BUF && type != SN_POS && type != SN_CAST &&
            type != SN_SLICE && type != SN_BIT_NOT && type != SN_REPLICATE) return false;
        if (sn_obj_fanin_count(m, o) != 1) return false;
        o = sn_obj_fanin(m, o, 0);
    }
}

/**Function*************************************************************

  Synopsis    [Marks values whose uses reach outputs through wiring only.]

  Description [A terminal cone may fill four LUT pins at unchanged depth.
               Internal cones retain the input-budget guard because their
               consumers may otherwise lose an opportunity to share a LUT.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned char* sn_mux4_terminal(const sn_module_t* m)
{
    size_t count = m->obj_types.size;
    unsigned char* terminal = (unsigned char*)malloc(count ? count : 1);
    assert(terminal);
    memset(terminal, 1, count);
    for (size_t index = count; index-- > 0;) {
        sn_obj_id_t o = (sn_obj_id_t)index;
        sn_obj_type_t type = sn_obj_type(m, o);
        bool wire = (type == SN_BUF || type == SN_POS || type == SN_CAST || type == SN_BIT_NOT) &&
                    sn_obj_fanin_count(m, o) == 1 &&
                    sn_obj_width(m, o) == sn_obj_width(m, sn_obj_fanin(m, o, 0));
        if (type == SN_PO || (wire && terminal[o])) continue;
        for (uint32_t k = 0; k < sn_obj_fanin_count(m, o); ++k) {
            sn_obj_id_t f = sn_obj_fanin(m, o, k);
            if (f != SN_INVALID_ID) terminal[f] = 0;
        }
    }
    return terminal;
}

typedef struct sn_mux4_edge_t { int node; sn_obj_id_t obj; unsigned delay; } sn_mux4_edge_t;
typedef struct sn_mux4_rot_t { sn_mux4_edge_t edge[3]; } sn_mux4_rot_t;
typedef struct sn_mux4_path_t { int node, side; } sn_mux4_path_t;

/**Function*************************************************************

  Synopsis    [Propagates delay through a tentative mux tree.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned sn_mux4_rot_delay(sn_mux4_rot_t* tree, int node, int side)
{
    sn_mux4_edge_t* edge = &tree[node].edge[side];
    if (edge->node) {
        int child = edge->node;
        edge->delay = sn_mux4_delay(sn_mux4_rot_delay(tree, child, 0),
            sn_mux4_rot_delay(tree, child, 1), tree[child].edge[2].delay, true);
    }
    return edge->delay;
}

/**Function*************************************************************

  Synopsis    [Finds a critical data path for rotation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int sn_mux4_rot_path(sn_mux4_rot_t* tree, int node, int side,
                                  sn_mux4_path_t* path, unsigned* length)
{
    int child = tree[node].edge[side].node;
    if (child) {
        unsigned d0 = tree[child].edge[0].delay, d1 = tree[child].edge[1].delay;
        unsigned dc = tree[child].edge[2].delay;
        int next = d0 >= d1 ? 0 : 1;
        if (dc > (next ? d1 : d0)) return 0; // Critical control: no data rotation.
        if (!sn_mux4_rot_path(tree, child, next, path, length)) return 0;
    }
    path[*length].node = node; path[(*length)++].side = side;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Applies or estimates one priority-preserving rotation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void sn_mux4_rotate_once(sn_module_t* m, sn_mux4_rot_t* tree,
    const sn_mux4_path_t* path, unsigned i, unsigned k, bool commit)
{
    sn_mux4_rot_t* bottom = tree + path[i].node;
    sn_mux4_rot_t* middle = tree + path[i+1].node;
    sn_mux4_rot_t* top = tree + path[k].node;
    sn_mux4_edge_t spare = bottom->edge[!path[i].side];
    bottom->edge[!path[i].side] = top->edge[path[k].side];
    top->edge[path[k].side].node = path[i].node;
    middle->edge[path[i+1].side] = spare;
    for (unsigned c = i+1; c < k; ++c)
        bottom->edge[2].delay = sn_mux4_delay(bottom->edge[2].delay,
            tree[path[c].node].edge[2].delay, 0, false);
    if (!commit) return;
    sn_obj_id_t condition = SN_INVALID_ID;
    for (unsigned c = i; c < k; ++c) {
        sn_obj_id_t pin = tree[path[c].node].edge[2].obj;
        if (!path[c].side) pin = sn_module_add_operator(m, SN_BIT_NOT, 1, false, 1, &pin, NULL);
        condition = condition == SN_INVALID_ID ? pin : sn_mux4_binary(m, SN_BIT_AND, 1, condition, pin);
    }
    if (!path[i].side) condition = sn_module_add_operator(m, SN_BIT_NOT, 1, false, 1, &condition, NULL);
    bottom->edge[2].obj = condition;
}

/**Function*************************************************************

  Synopsis    [Selects a bounded delay-improving rotation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned sn_mux4_rotate_try(sn_module_t* m, sn_mux4_rot_t* tree, int node, int side,
                                         unsigned* budget)
{
    sn_mux4_path_t path[SN_MUX4_ROTATE_MAX+1];
    unsigned length = 0, best = sn_mux4_rot_delay(tree, node, side), bi = 0, bk = 0;
    if (!*budget || !sn_mux4_rot_path(tree, node, side, path, &length)) return 0;
    for (unsigned i = 0; i < length; ++i)
        for (unsigned k = i+2; k < length && *budget; ++k) {
            sn_mux4_rot_t backup[3] = {tree[path[i].node], tree[path[i+1].node], tree[path[k].node]};
            --*budget;
            sn_mux4_rotate_once(m, tree, path, i, k, false);
            unsigned delay = sn_mux4_rot_delay(tree, node, side);
            tree[path[i].node] = backup[0]; tree[path[i+1].node] = backup[1]; tree[path[k].node] = backup[2];
            if (delay < best || (bk && delay == best)) { best = delay; bi = i; bk = k; }
        }
    if (!bk) { sn_mux4_rot_delay(tree, node, side); return 0; }
    sn_mux4_rotate_once(m, tree, path, bi, bk, true);
    sn_mux4_rot_delay(tree, node, side);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Improves mux subtrees and their critical paths.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned sn_mux4_rotate_rec(sn_module_t* m, sn_mux4_rot_t* tree, int node, int side,
                                         unsigned* budget)
{
    unsigned changes = 0;
    int branch = tree[node].edge[side].node;
    while (branch) {
        int a = tree[branch].edge[0].node, b = tree[branch].edge[1].node;
        if (a && b) {
            changes += sn_mux4_rotate_rec(m, tree, branch, 0, budget);
            changes += sn_mux4_rotate_rec(m, tree, branch, 1, budget);
            break;
        }
        branch = a ? a : b;
    }
    return changes + sn_mux4_rotate_try(m, tree, node, side, budget);
}

/**Function*************************************************************

  Synopsis    [Collects a bounded mux tree with boundary arrivals.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline sn_mux4_edge_t sn_mux4_collect(const sn_module_t* m, sn_obj_id_t obj, uint32_t width,
    const uint32_t* refs, size_t count, const unsigned* arrival, sn_mux4_rot_t* tree, unsigned* size,
    bool root)
{
    sn_mux4_edge_t edge = {0, obj, arrival[obj]};
    sn_obj_id_t child = root ? obj : sn_mux4_child(m, obj, width, refs, count);
    if (child == SN_INVALID_ID) return edge;
    int index = (int)++*size; assert(*size <= SN_MUX4_ROTATE_MAX);
    edge.node = index;
    for (unsigned side = 0; side < 2; ++side)
        tree[index].edge[side] = sn_mux4_collect(m, sn_mux4_data(m, child, side), width,
            refs, count, arrival, tree, size, false);
    sn_obj_id_t control = sn_obj_fanin(m, child, SN_MUX_SELECT);
    tree[index].edge[2].node = 0; tree[index].edge[2].obj = control;
    tree[index].edge[2].delay = arrival[control];
    return edge;
}

/**Function*************************************************************

  Synopsis    [Emits a restructured word-level mux tree.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline sn_obj_id_t sn_mux4_rot_emit(sn_module_t* m, sn_mux4_rot_t* tree,
                                         sn_mux4_edge_t edge, uint32_t width)
{
    if (!edge.node) return edge.obj;
    sn_mux4_rot_t* node = tree + edge.node;
    sn_obj_id_t args[3];
    args[SN_MUX_DEFAULT] = sn_mux4_rot_emit(m, tree, node->edge[0], width);
    args[SN_MUX_SELECTED] = sn_mux4_rot_emit(m, tree, node->edge[1], width);
    args[SN_MUX_SELECT] = node->edge[2].obj;
    return sn_module_add_operator(m, SN_MUX, width, false, 3, args, NULL);
}

/**Function*************************************************************

  Synopsis    [Estimates an object arrival in the LUT packing model.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned sn_mux4_obj_arrival(const sn_module_t* m, sn_obj_id_t obj, const unsigned* arrival, size_t n)
{
    sn_obj_type_t type = sn_obj_type(m, obj);
    if (type == SN_FAN && sn_obj_type(m, sn_fan_owner(m, obj)) == SN_FA)
        return arrival[sn_fan_owner(m, obj)];
    if (!sn_obj_type_is_operator(type) && type != SN_LUT) return 1;
    unsigned ds[3] = {1,1,1}, result = 0, maximum = 1;
    for (uint32_t k = 0; k < sn_obj_fanin_count(m, obj); ++k) {
        sn_obj_id_t f = sn_obj_fanin(m, obj, k);
        unsigned d = f < n ? arrival[f] : 1;
        if (d > maximum) maximum = d;
        if (k < 3) ds[k] = d;
        result = k ? sn_mux4_delay(result, d, 0, false) : d;
    }
    if (type == SN_MUX) return sn_mux4_delay(ds[0], ds[1], ds[2], true);
    if (type == SN_BUF || type == SN_POS || type == SN_CAST || type == SN_BIT_NOT ||
        type == SN_REPLICATE || type == SN_SLICE) return ds[0];
    if (type == SN_CONCAT) return maximum;
    if (type == SN_ADD || type == SN_SUB || type == SN_NEG || type == SN_MUL || type == SN_FA ||
        (type >= SN_EQ && type <= SN_GE) || (type >= SN_REDUCE_AND && type <= SN_REDUCE_XNOR) ||
        (type >= SN_SHL && type <= SN_ASHR)) {
        unsigned delay = sn_rewrite_delay(m, obj);
        return delay ? (((maximum >> 4) + ((maximum & 15) > 1) + delay) << 4) | 1 : maximum;
    }
    return result ? result : 1;
}

/**Function*************************************************************

  Synopsis    [Rotates eligible mux trees in one module definition.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void sn_mux4_rotate_module(sn_design_t* d, sn_module_id_t id, sn_mux4_stats_t* stats)
{
    sn_module_t* m = sn_design_get_module(d, id);
    size_t n = m->obj_types.size, before = stats->rotations;
    uint32_t* refs = (uint32_t*)calloc(n ? n : 1, sizeof(uint32_t));
    unsigned* sizes = (unsigned*)calloc(n ? n : 1, sizeof(unsigned));
    unsigned* arrival = (unsigned*)calloc(n ? n : 1, sizeof(unsigned));
    unsigned char* interior = (unsigned char*)calloc(n ? n : 1, 1);
    sn_vec_t pending; sn_vec_init(&pending); assert(refs && sizes && arrival && interior);
    for (sn_obj_id_t o = 0; o < n; ++o)
        for (uint32_t k = 0; k < sn_obj_fanin_count(m, o); ++k) {
            sn_obj_id_t f = sn_obj_fanin(m, o, k); if (f != SN_INVALID_ID) ++refs[f];
        }
    for (sn_obj_id_t o = 0; o < n; ++o) {
        if (sn_obj_type(m, o) != SN_MUX) continue;
        sizes[o] = 1;
        sn_obj_id_t child[2];
        for (unsigned s = 0; s < 2; ++s) {
            child[s] = sn_mux4_child(m, sn_mux4_data(m, o, s), sn_obj_width(m, o), refs, n);
            if (child[s] != SN_INVALID_ID) sizes[o] += sizes[child[s]];
        }
        if (sizes[o] <= SN_MUX4_ROTATE_MAX) {
            for (unsigned s = 0; s < 2; ++s) if (child[s] != SN_INVALID_ID) interior[child[s]] = 1;
        } else sizes[o] = SN_MUX4_ROTATE_MAX + 1;
    }
    for (sn_obj_id_t o = 0; o < n; ++o) {
        arrival[o] = sn_mux4_obj_arrival(m, o, arrival, n);
        if (interior[o] || sizes[o] < 2 || sizes[o] > SN_MUX4_ROTATE_MAX || !refs[o]) continue;
        size_t appended_start = m->obj_types.size;
        sn_mux4_rot_t tree[SN_MUX4_ROTATE_MAX+1];
        memset(tree, 0, sizeof(tree)); unsigned size = 0, changes = 0, budget = 8192;
        tree[0].edge[0] = sn_mux4_collect(m, o, sn_obj_width(m, o), refs, n, arrival, tree, &size, true);
        // Pin original boundary objects before any old data cones are released.
        unsigned step;
        do { step = sn_mux4_rotate_rec(m, tree, 0, 0, &budget); changes += step; } while (step && budget);
        if (!changes) continue;
        for (unsigned j = 1; j <= size; ++j)
            for (unsigned s = 0; s < 3; ++s)
                if (!tree[j].edge[s].node && tree[j].edge[s].obj < n) ++refs[tree[j].edge[s].obj];
        // Original selects feeding newly generated conditions must also survive.
        for (sn_obj_id_t j = (sn_obj_id_t)appended_start; j < m->obj_types.size; ++j)
            for (uint32_t k = 0; k < sn_obj_fanin_count(m, j); ++k) {
                sn_obj_id_t f = sn_obj_fanin(m, j, k); if (f < n) ++refs[f];
            }
        sn_obj_id_t old[3]; for (unsigned k = 0; k < 3; ++k) old[k] = sn_obj_fanin(m, o, k);
        sn_obj_id_t result = sn_mux4_rot_emit(m, tree, tree[0].edge[0], sn_obj_width(m, o));
        arrival[o] = sn_mux4_rot_delay(tree, 0, 0);
        sn_vec_at(sn_obj_type_t, &m->obj_types, o) = SN_BUF;
        sn_vec_at(sn_fanin_count_t, &m->fanin_counts, o) = 1;
        sn_obj_connect(m, o, 0, result);
        for (unsigned k = 0; k < 3; ++k) sn_mux4_release(m, old[k], refs, &pending);
        stats->rotations += changes;
    }
    free(refs); free(sizes); free(arrival); free(interior); sn_vec_destroy(&pending);
    if (stats->rotations != before) sn_mux4_rebuild(d, id);
}

typedef struct sn_mux4_cache_t {
    uint64_t key[3];
    sn_obj_id_t object;
    unsigned truth, count, width;
} sn_mux4_cache_t;

typedef struct sn_mux4_choice_t {
    sn_obj_id_t nodes[3], leaves[4], controls[3];
    unsigned truths[2], ncontrols, cost, delay, gain;
} sn_mux4_choice_t;

/**Function*************************************************************

  Synopsis    [Recognizes words whose bits are copies of one scalar.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline sn_obj_id_t sn_mux4_scalar(const sn_module_t* m, sn_obj_id_t o)
{
    for (;;) {
        sn_obj_type_t type = sn_obj_type(m, o);
        if (sn_obj_width(m, o) == 1) return o;
        if (type != SN_REPLICATE &&
            ((type != SN_BUF && type != SN_POS && type != SN_CAST) ||
             sn_obj_width(m, sn_obj_fanin(m, o, 0)) != sn_obj_width(m, o))) return SN_INVALID_ID;
        o = sn_obj_fanin(m, o, 0);
    }
}

/**Function*************************************************************

  Synopsis    [Canonicalizes scalar wiring for cross-bus control sharing.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline uint64_t sn_mux4_select_key(const sn_module_t* m, sn_obj_id_t o)
{
    for (;;) {
        sn_obj_type_t type = sn_obj_type(m, o);
        if (sn_obj_width(m, o) != 1) return o;
        if ((type == SN_BUF || type == SN_POS || type == SN_CAST) && sn_obj_width(m, sn_obj_fanin(m, o, 0)) == 1) {
            o = sn_obj_fanin(m, o, 0);
            continue;
        }
        if (type != SN_SLICE) return o;
        sn_slice_info_t slice = sn_obj_slice_info(m, o);
        if (sn_obj_width(m, sn_obj_fanin(m, o, 0)) == 1 && slice.right_index == 0) {
            o = sn_obj_fanin(m, o, 0);
            continue;
        }
        return (UINT64_C(1) << 63) | ((uint64_t)sn_obj_fanin(m, o, 0) << 31) | (uint32_t)slice.right_index;
    }
}

/**Function*************************************************************

  Synopsis    [Finds or creates a shared recoded control or replicated word.]

  Description [A nonzero width selects replication (truth 0) or complement
               (truth 1) of controls[0], instead of a scalar truth table.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline sn_obj_id_t sn_mux4_cached(sn_module_t* m, sn_mux4_cache_t* cache, size_t capacity,
    unsigned truth, unsigned count, const sn_obj_id_t* controls, uint32_t width, bool create)
{
    if (width == 1 && !truth) return controls[0];
    // A projection has no new owner. Its original slice can be retired when
    // another bus reuses a replicated alias, so never retain it in the cache.
    if (!width)
        for (unsigned k = 0; k < count; ++k) {
            unsigned projection = 0;
            for (unsigned v = 0; v < (1u << count); ++v)
                if ((v >> k) & 1) projection |= 1u << v;
            if (truth == projection) return controls[k];
        }
    uint64_t keys[3] = {0,0,0}, hash = UINT64_C(1469598103934665603);
    for (unsigned k = 0; k < count; ++k) {
        keys[k] = sn_mux4_select_key(m, controls[k]);
        hash = (hash ^ keys[k]) * UINT64_C(1099511628211);
    }
    hash = (hash ^ truth) * UINT64_C(1099511628211);
    hash = (hash ^ count) * UINT64_C(1099511628211);
    size_t slot = (size_t)(hash ^ width) & (capacity - 1);
    while (cache[slot].object != SN_INVALID_ID) {
        sn_mux4_cache_t* entry = cache + slot;
        if (entry->truth == truth && entry->count == count && entry->width == width &&
            !memcmp(entry->key, keys, sizeof(keys))) return entry->object;
        slot = (slot + 1) & (capacity - 1);
    }
    if (!create) return SN_INVALID_ID;
    sn_mux4_cache_t* entry = cache + slot;
    memcpy(entry->key, keys, sizeof(keys));
    entry->truth = truth; entry->count = count; entry->width = width;
    entry->object = !width ? sn_mux4_control(m, truth, count, controls) : !truth ?
        sn_mux4_repeat(m, controls[0], width) : sn_module_add_operator(m, SN_BIT_NOT, width, false, 1, controls, NULL);
    return entry->object;
}

/**Function*************************************************************

  Synopsis    [Prices one connected triplet with its exact selector functions.]

  Description [An already accepted plan is reconstructed without reconsidering
               its profitability after its members have been covered.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline bool sn_mux4_choice(sn_module_t* m, const sn_obj_id_t nodes[3],
    const uint32_t* refs, size_t n, const unsigned* levels, const unsigned char* terminal,
    sn_mux4_cache_t* cache, size_t capacity, bool area_only, bool accepted, sn_mux4_choice_t* choice)
{
    unsigned nleaves = 0, slots[3], reached = 0;
    int edges[3][2];
    uint32_t w = sn_obj_width(m, nodes[0]);
    memset(choice, 0, sizeof(*choice));
    memcpy(choice->nodes, nodes, sizeof(choice->nodes));
    sn_mux4_expand(m, nodes[0], nodes, w, refs, n, edges, choice->leaves, &nleaves);
    assert(nleaves == 4);
    unsigned constants = 0;
    for (unsigned k = 0; k < 4; ++k) {
        sn_obj_type_t t = sn_obj_type(m, choice->leaves[k]);
        constants += t == SN_CONST0 || t == SN_CONST1 || t == SN_CONST;
        if (!accepted)
            for (unsigned j = 0; j < k; ++j) if (choice->leaves[k] == choice->leaves[j]) return false;
    }
    for (unsigned k = 0; k < 3; ++k) {
        sn_obj_id_t c = sn_obj_fanin(m, nodes[k], SN_MUX_SELECT);
        uint64_t key = sn_mux4_select_key(m, c);
        unsigned j = 0;
        while (j < choice->ncontrols && sn_mux4_select_key(m, choice->controls[j]) < key) ++j;
        if (j < choice->ncontrols && sn_mux4_select_key(m, choice->controls[j]) == key) continue;
        for (unsigned i = choice->ncontrols; i > j; --i) choice->controls[i] = choice->controls[i-1];
        choice->controls[j] = c; ++choice->ncontrols;
    }
    for (unsigned k = 0; k < 3; ++k) {
        uint64_t key = sn_mux4_select_key(m, sn_obj_fanin(m, nodes[k], SN_MUX_SELECT));
        for (slots[k] = 0; sn_mux4_select_key(m, choice->controls[slots[k]]) != key; ++slots[k]) {}
    }
    for (unsigned v = 0; v < (1u << choice->ncontrols); ++v) {
        int pos = 0;
        while (pos >= 0) pos = edges[pos][(v >> slots[pos]) & 1];
        unsigned leaf = (unsigned)(-pos - 1);
        reached |= 1u << leaf;
        for (unsigned b = 0; b < 2; ++b)
            if ((leaf >> b) & 1) choice->truths[b] |= 1u << v;
    }
    unsigned direct_cost = 0;
    for (unsigned b = 0; b < 2; ++b) {
        unsigned cost = sn_mux4_control_cost(choice->truths[b], choice->ncontrols);
        direct_cost += cost;
        if (!cache || sn_mux4_cached(m, cache, capacity, choice->truths[b], choice->ncontrols,
                                    choice->controls, 0, false) == SN_INVALID_ID) choice->cost += cost;
    }
    bool uniform = true;
    for (unsigned k = 0; k < 4; ++k) uniform &= sn_mux4_scalar(m, choice->leaves[k]) != SN_INVALID_ID;
    unsigned effective_width = uniform ? 1 : w;
    // Constants already simplify the original muxes. Discount the nominal
    // saving by their share of the data leaves rather than pricing them as buses.
    unsigned saving = (unsigned)((uint64_t)effective_width * (4 - constants) / 4);
    choice->gain = saving > choice->cost ? saving - choice->cost : 0;
    choice->delay = levels[nodes[0]];
    if (accepted) return true;
    if (reached != 15 || !choice->gain) return false;
    if (area_only) return true;
    unsigned ctl[2] = {0,0};
    for (unsigned b = 0; b < 2; ++b) {
        for (unsigned k = 0; k < choice->ncontrols; ++k)
            for (unsigned v = 0; v < (1u << choice->ncontrols); ++v)
                if (((choice->truths[b] >> v) & 1) != ((choice->truths[b] >> (v ^ (1u << k))) & 1)) {
                    ctl[b] = ctl[b] ? sn_mux4_delay(ctl[b], levels[choice->controls[k]], 0, false) : levels[choice->controls[k]];
                    break;
                }
        if (!ctl[b]) ctl[b] = 1;
    }
    unsigned low = sn_mux4_delay(ctl[0], levels[choice->leaves[0]], levels[choice->leaves[1]], true);
    unsigned q = sn_mux4_delay(ctl[1], ctl[0], low, true);
    unsigned hi = sn_mux4_delay(q, levels[choice->leaves[2]], levels[choice->leaves[3]], true);
    unsigned output = sn_mux4_delay(ctl[1], hi, q, true), baseline = levels[nodes[0]];
    if (output > baseline) {
        if (direct_cost) return false;
        for (unsigned k = 0; k < choice->ncontrols; ++k)
            if (!sn_mux4_boundary_word(m, choice->controls[k])) return false;
        for (unsigned k = 0; k < 4; ++k)
            if (!sn_mux4_boundary_word(m, choice->leaves[k])) return false;
        q = sn_mux4_delay4(ctl[1], ctl[0], levels[choice->leaves[0]], levels[choice->leaves[1]]);
        output = sn_mux4_delay4(ctl[1], q, levels[choice->leaves[2]], levels[choice->leaves[3]]);
        if (output > baseline && (!terminal[nodes[0]] || (output >> 4) > (baseline >> 4))) return false;
    }
    choice->delay = output;
    return true;
}

/**Function*************************************************************

  Synopsis    [Builds the two four-input Boolean data cones of a triplet.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline sn_obj_id_t sn_mux4_emit(sn_module_t* m, const sn_mux4_choice_t* choice,
                                       sn_mux4_cache_t* cache, size_t capacity)
{
    sn_obj_id_t scalar[4];
    const sn_obj_id_t* leaves = choice->leaves;
    uint32_t width = sn_obj_width(m, choice->nodes[0]), w = width;
    bool uniform = true;
    for (unsigned k = 0; k < 4; ++k) {
        scalar[k] = sn_mux4_scalar(m, leaves[k]);
        uniform &= scalar[k] != SN_INVALID_ID;
    }
    if (uniform) { leaves = scalar; w = 1; }
    sn_obj_id_t t = sn_mux4_cached(m, cache, capacity, choice->truths[0], choice->ncontrols, choice->controls, 0, true);
    sn_obj_id_t r = sn_mux4_cached(m, cache, capacity, choice->truths[1], choice->ncontrols, choice->controls, 0, true);
    sn_obj_id_t tr = sn_mux4_cached(m, cache, capacity, 0, 1, &t, w, true);
    sn_obj_id_t rr = sn_mux4_cached(m, cache, capacity, 0, 1, &r, w, true);
    sn_obj_id_t nr = sn_mux4_cached(m, cache, capacity, 1, 1, &rr, w, true);
    sn_obj_id_t nt = sn_mux4_cached(m, cache, capacity, 1, 1, &tr, w, true);
    // Keep these as Boolean cones: recoding as an ordinary BMUX would
    // reintroduce three independent data muxes instead of two LUT4s per bit.
    sn_obj_id_t low = sn_mux4_binary(m, SN_BIT_OR, w,
        sn_mux4_binary(m, SN_BIT_AND, w, tr, leaves[1]), sn_mux4_binary(m, SN_BIT_AND, w, nt, leaves[0]));
    sn_obj_id_t q = sn_mux4_binary(m, SN_BIT_OR, w,
        sn_mux4_binary(m, SN_BIT_AND, w, rr, tr), sn_mux4_binary(m, SN_BIT_AND, w, nr, low));
    sn_obj_id_t nq = sn_module_add_operator(m, SN_BIT_NOT, w, false, 1, &q, NULL);
    sn_obj_id_t hi = sn_mux4_binary(m, SN_BIT_OR, w,
        sn_mux4_binary(m, SN_BIT_AND, w, q, leaves[3]), sn_mux4_binary(m, SN_BIT_AND, w, nq, leaves[2]));
    sn_obj_id_t result = sn_mux4_binary(m, SN_BIT_OR, w,
        sn_mux4_binary(m, SN_BIT_AND, w, rr, hi), sn_mux4_binary(m, SN_BIT_AND, w, nr, q));
    return w == width ? result : sn_mux4_repeat(m, result, width);
}

/**Function*************************************************************

  Synopsis    [Enumerates connected three-mux groups with a given root.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned sn_mux4_groups(const sn_module_t* m, sn_obj_id_t o, const uint32_t* refs,
                                      size_t n, sn_obj_id_t child[2], sn_obj_id_t groups[5][3])
{
    uint32_t w = sn_obj_width(m, o);
    unsigned count = 0;
    for (unsigned s = 0; s < 2; ++s) child[s] = sn_mux4_child(m, sn_mux4_data(m, o, s), w, refs, n);
    if (child[0] != SN_INVALID_ID && child[1] != SN_INVALID_ID) {
        groups[count][0] = o; groups[count][1] = child[0]; groups[count++][2] = child[1];
    }
    for (unsigned s = 0; s < 2; ++s) if (child[s] != SN_INVALID_ID)
        for (unsigned t = 0; t < 2; ++t) {
            sn_obj_id_t grand = sn_mux4_child(m, sn_mux4_data(m, child[s], t), w, refs, n);
            if (grand == SN_INVALID_ID) continue;
            groups[count][0] = o; groups[count][1] = child[s]; groups[count++][2] = grand;
        }
    return count;
}

/**Function*************************************************************

  Synopsis    [Folds repeated and constant data into at most four-input LUTs.]

  Description [Constant words share identical output columns. Scalar expansion
               is bounded to 256 output bits; other groups use normal recoding.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline sn_obj_id_t sn_mux4_fold(sn_module_t* m, const sn_obj_id_t nodes[3], const uint32_t* refs, size_t n)
{
    uint32_t width = sn_obj_width(m, nodes[0]);
    sn_obj_id_t leaves[4], controls[3], data[4], columns[256], memo[256];
    unsigned nleaves = 0, nc = 0, nd = 0, slots[3], data_slots[4];
    int edges[3][2];
    if (width > 256) return SN_INVALID_ID;
    sn_mux4_expand(m, nodes[0], nodes, width, refs, n, edges, leaves, &nleaves);
    for (unsigned k = 0; k < 3; ++k) {
        sn_obj_id_t c = sn_obj_fanin(m, nodes[k], SN_MUX_SELECT);
        for (slots[k] = 0; slots[k] < nc && sn_mux4_select_key(m, controls[slots[k]]) != sn_mux4_select_key(m, c); ++slots[k]) {}
        if (slots[k] == nc) controls[nc++] = c;
    }
    for (unsigned k = 0; k < 4; ++k) {
        sn_obj_type_t type = sn_obj_type(m, leaves[k]);
        data_slots[k] = 4;
        if (type == SN_CONST0 || type == SN_CONST1 || type == SN_CONST) continue;
        unsigned j;
        for (j = 0; j < nd && data[j] != leaves[k]; ++j) {}
        if (j == nd) data[nd++] = leaves[k];
        data_slots[k] = j;
    }
    if (nc + nd > 4) return SN_INVALID_ID;
    for (unsigned v = 0; v < 256; ++v) memo[v] = SN_INVALID_ID;
    for (uint32_t bit = 0; bit < width; ++bit) {
        unsigned truth = 0;
        for (unsigned v = 0; v < (1u << (nc + nd)); ++v) {
            int pos = 0;
            while (pos >= 0) pos = edges[pos][(v >> slots[pos]) & 1];
            unsigned leaf = (unsigned)(-pos - 1), slot = data_slots[leaf];
            unsigned value = slot == 4 ? sn_const_bit(m, leaves[leaf], bit) : (v >> (nc + slot)) & 1;
            truth |= value << v;
        }
        if (!nd && memo[truth] != SN_INVALID_ID) { columns[bit] = memo[truth]; continue; }
        sn_obj_id_t inputs[4];
        for (unsigned k = 0; k < nc; ++k) inputs[k] = controls[k];
        for (unsigned k = 0; k < nd; ++k)
            inputs[nc+k] = width == 1 ? data[k] : sn_module_add_slice(m, data[k], (int32_t)bit, (int32_t)bit, NULL);
        columns[bit] = sn_mux4_control(m, truth, nc + nd, inputs);
        if (!nd) memo[truth] = columns[bit];
    }
    return width == 1 ? columns[0] : sn_module_add_concat(m, width, columns, NULL);
}

/**Function*************************************************************

  Synopsis    [Simplifies degenerate mux groups before general triplet covering.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void sn_mux4_fold_module(sn_design_t* d, sn_module_id_t id, sn_mux4_stats_t* stats)
{
    sn_module_t* m = sn_design_get_module(d, id);
    size_t n = m->obj_types.size, before = stats->folds;
    uint32_t* refs = (uint32_t*)calloc(n ? n : 1, sizeof(uint32_t));
    sn_vec_t pending; sn_vec_init(&pending); assert(refs);
    for (sn_obj_id_t o = 0; o < n; ++o)
        for (uint32_t k = 0; k < sn_obj_fanin_count(m, o); ++k) {
            sn_obj_id_t f = sn_obj_fanin(m, o, k); if (f != SN_INVALID_ID) ++refs[f];
        }
    for (sn_obj_id_t o = 0; o < n; ++o) {
        if (sn_obj_type(m, o) != SN_MUX || !refs[o]) continue;
        sn_obj_id_t child[2], groups[5][3], result = SN_INVALID_ID, old[3];
        unsigned count = sn_mux4_groups(m, o, refs, n, child, groups);
        size_t first = m->obj_types.size;
        for (unsigned k = 0; k < count && result == SN_INVALID_ID; ++k)
            result = sn_mux4_fold(m, groups[k], refs, n);
        if (result == SN_INVALID_ID) continue;
        for (unsigned k = 0; k < 3; ++k) old[k] = sn_obj_fanin(m, o, k);
        for (sn_obj_id_t j = (sn_obj_id_t)first; j < m->obj_types.size; ++j)
            for (uint32_t k = 0; k < sn_obj_fanin_count(m, j); ++k) {
                sn_obj_id_t f = sn_obj_fanin(m, j, k); if (f < n) ++refs[f];
            }
        if (result < n) ++refs[result];
        sn_vec_at(sn_obj_type_t, &m->obj_types, o) = SN_BUF;
        sn_vec_at(sn_fanin_count_t, &m->fanin_counts, o) = 1;
        sn_obj_connect(m, o, 0, result);
        for (unsigned k = 0; k < 3; ++k) sn_mux4_release(m, old[k], refs, &pending);
        ++stats->folds;
    }
    free(refs); sn_vec_destroy(&pending);
    if (stats->folds != before) sn_rewrite_rebuild(d, id);
}

/**Function*************************************************************

  Synopsis    [Chooses profitable disjoint triplets by tree dynamic programming.]

  Description [Enumerates every connected three-node group rooted at a mux.
               The score includes optimal covers below its four data leaves.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void sn_mux4_module(sn_design_t* d, sn_module_id_t id, sn_mux4_stats_t* stats, bool area_only)
{
    sn_module_t* m = sn_design_get_module(d, id);
    size_t n = m->obj_types.size, before = stats->triplets, capacity = 16;
    while (capacity < 2 * n) capacity *= 2;
    uint32_t* refs = (uint32_t*)calloc(n ? n : 1, sizeof(uint32_t));
    unsigned* levels = (unsigned*)calloc(n ? n : 1, sizeof(unsigned));
    uint64_t* score = (uint64_t*)calloc(n ? n : 1, sizeof(uint64_t));
    sn_obj_id_t* plan = (sn_obj_id_t*)malloc(2 * (n ? n : 1) * sizeof(sn_obj_id_t));
    uint8_t* covered = (uint8_t*)calloc(n ? n : 1, 1);
    unsigned char* terminal = area_only ? NULL : sn_mux4_terminal(m);
    sn_mux4_cache_t* cache = (sn_mux4_cache_t*)malloc(capacity * sizeof(sn_mux4_cache_t));
    sn_vec_t pending; sn_vec_init(&pending);
    assert(refs && levels && score && plan && covered && cache);
    for (size_t k = 0; k < 2*n; ++k) plan[k] = SN_INVALID_ID;
    for (size_t k = 0; k < capacity; ++k) cache[k].object = SN_INVALID_ID;
    for (sn_obj_id_t o = 0; o < n; ++o)
        for (uint32_t k = 0; k < sn_obj_fanin_count(m, o); ++k) {
            sn_obj_id_t f = sn_obj_fanin(m, o, k);
            if (f != SN_INVALID_ID) ++refs[f];
        }
    for (sn_obj_id_t o = 0; o < n; ++o) {
        levels[o] = sn_mux4_obj_arrival(m, o, levels, n);
        if (sn_obj_type(m, o) != SN_MUX || !refs[o]) continue;
        uint32_t w = sn_obj_width(m, o);
        sn_obj_id_t child[2], groups[5][3];
        unsigned count = sn_mux4_groups(m, o, refs, n, child, groups);
        for (unsigned s = 0; s < 2; ++s) if (child[s] != SN_INVALID_ID) score[o] += score[child[s]];
        unsigned best_delay = levels[o];
        for (unsigned k = 0; k < count; ++k) {
            sn_mux4_choice_t choice;
            if (!sn_mux4_choice(m, groups[k], refs, n, levels, terminal, NULL, 0, area_only, false, &choice)) continue;
            uint64_t saving = choice.gain;
            for (unsigned j = 0; j < 4; ++j) {
                sn_obj_id_t leaf = sn_mux4_child(m, choice.leaves[j], w, refs, n);
                if (leaf != SN_INVALID_ID) saving += score[leaf];
            }
            if (saving > score[o]) {
                score[o] = saving; best_delay = choice.delay;
                plan[2*o] = groups[k][1]; plan[2*o+1] = groups[k][2];
            }
        }
        levels[o] = best_delay;
    }
    // Select covers from roots down, then emit them from leaves up. A selected
    // interior mux belongs to its parent's group, not its own saved choice.
    for (size_t o = n; o-- > 0;)
        if (!covered[o] && plan[2*o] != SN_INVALID_ID)
            covered[plan[2*o]] = covered[plan[2*o+1]] = 1;
    for (sn_obj_id_t o = 0; o < n; ++o) {
        if (covered[o] || plan[2*o] == SN_INVALID_ID) continue;
        sn_obj_id_t nodes[3] = {o, plan[2*o], plan[2*o+1]}, old[3];
        sn_mux4_choice_t choice;
        sn_mux4_choice(m, nodes, refs, n, levels, terminal, cache, capacity, area_only, true, &choice);
        for (unsigned k = 0; k < 3; ++k) old[k] = sn_obj_fanin(m, o, k);
        size_t first = m->obj_types.size;
        sn_obj_id_t result = sn_mux4_emit(m, &choice, cache, capacity);
        // Count actual uses, including shared controls and scalar projections.
        for (sn_obj_id_t j = (sn_obj_id_t)first; j < m->obj_types.size; ++j)
            for (uint32_t k = 0; k < sn_obj_fanin_count(m, j); ++k) {
                sn_obj_id_t f = sn_obj_fanin(m, j, k); if (f < n) ++refs[f];
            }
        if (result < n) ++refs[result];
        sn_vec_at(sn_obj_type_t, &m->obj_types, o) = SN_BUF;
        sn_vec_at(sn_fanin_count_t, &m->fanin_counts, o) = 1;
        sn_obj_connect(m, o, 0, result);
        for (unsigned k = 0; k < 3; ++k) sn_mux4_release(m, old[k], refs, &pending);
        ++stats->triplets; stats->bits += sn_obj_width(m, o);
        stats->controls += choice.cost; stats->savings += choice.gain;
    }
    if (stats->triplets != before) { ++stats->modules; sn_rewrite_rebuild(d, id); }
    free(cache); free(covered); free(plan); free(score); free(terminal); free(levels); free(refs);
    sn_vec_destroy(&pending);
}

/**Function*************************************************************

  Synopsis    [Restructures muxes in a reachable module hierarchy.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline sn_mux4_stats_t sn_design_mux4_config(sn_design_t* d, sn_module_id_t root,
                                                   FILE* verbose, bool area_only, unsigned threshold)
{
    sn_mux4_stats_t stats = {0,0,0,0,0,0,0,0,0};
    uint8_t* seen = (uint8_t*)calloc(d->modules.size, 1);
    sn_vec_t pending; sn_vec_init(&pending); assert(seen);
    *sn_vec_push(sn_module_id_t, &pending) = root;
    while (pending.size) {
        sn_module_id_t id = sn_vec_at(sn_module_id_t, &pending, --pending.size);
        if (seen[id]) continue;
        seen[id] = 1;
        const sn_module_t* m = sn_design_get_module_const(d, id);
        if (sn_module_is_blackbox(m)) continue;
        for (size_t i = 0; i < m->type_objects[SN_INST].size; ++i)
            *sn_vec_push(sn_module_id_t, &pending) = sn_inst_module_id(m, sn_vec_at(sn_obj_id_t, &m->type_objects[SN_INST], i));
        size_t before = stats.triplets;
        size_t chains = stats.chains;
        size_t rotations = stats.rotations;
        size_t views = stats.views, folds = stats.folds;
        sn_mux4_views(d, id, &stats);
        if (!area_only) sn_mux4_balance(d, id, &stats, threshold);
        if (!area_only) sn_mux4_rotate_module(d, id, &stats);
        sn_mux4_fold_module(d, id, &stats);
        sn_mux4_module(d, id, &stats, area_only);
        if ((stats.chains != chains || stats.rotations != rotations || stats.views != views || stats.folds != folds) && stats.triplets == before) ++stats.modules;
        if (verbose && (stats.triplets != before || stats.chains != chains || stats.rotations != rotations || stats.views != views || stats.folds != folds))
            fprintf(verbose, "@opt_mux4: module %s: %zu triplets, %zu priority chains, %zu rotations, %zu views, %zu folds.\n",
                sn_name_get(&d->names, sn_design_get_module(d, id)->name),
                stats.triplets - before, stats.chains - chains, stats.rotations - rotations,
                stats.views - views, stats.folds - folds);
    }
    free(seen); sn_vec_destroy(&pending);
    return stats;
}
/**Function*************************************************************

  Synopsis    [Uses a width-dependent priority-chain threshold.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline sn_mux4_stats_t sn_design_mux4_options(sn_design_t* d, sn_module_id_t root, FILE* verbose, bool area_only)
{
    return sn_design_mux4_config(d, root, verbose, area_only, 0);
}
/**Function*************************************************************

  Synopsis    [Restructures muxes in a reachable module hierarchy.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline sn_mux4_stats_t sn_design_mux4(sn_design_t* d, sn_module_id_t root, FILE* verbose)
{
    return sn_design_mux4_options(d, root, verbose, false);
}
ABC_NAMESPACE_HEADER_END
#endif
