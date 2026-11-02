/**CFile****************************************************************

  FileName    [giaDecGraph2.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Experimental improvements to multi-output circuit learning.]

  Author      [Jiun-Hao Chen]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - 2025.]

  Description [Derived from giaDecGraph.cpp. The original command is unchanged.]

***********************************************************************/

#ifdef _WIN32

#ifndef __MINGW32__
#pragma warning(disable : 4786) // warning C4786: identifier was truncated to '255' characters in the browser information
#endif
#endif

#include <cmath>
#include <vector>
#include <string>
#include <cstdint>
#include <cstring>
#include <set>
#include <numeric>
#include <unordered_set>
#include <unordered_map>
#include <algorithm>
#include <functional>
#include <iterator>
#include <type_traits>
#include <utility>

#include "gia.h"
#include "giaAig.h"
#include "bool/kit/kit.h"
#include "misc/vec/vecHash.h"
#include "misc/extra/extra.h"
#include "misc/util/utilTruth.h"

ABC_NAMESPACE_IMPL_START

namespace DecGraph2 {

template<typename I,
         typename std::enable_if<std::is_integral<I>::value, int>::type = 0>
struct integer_iterator {
    using iterator_category = std::input_iterator_tag;
    using value_type = I;
    using difference_type = I;
    using pointer = I*;
    using reference = I&;

    explicit integer_iterator(I value)
        : value(value) {
    }

    I operator*() const {
        return value;
    }

    I const* operator->() const {
        return &value;
    }

    integer_iterator& operator++() {
        ++value;
        return *this;
    }

    integer_iterator operator++(int) {
        const auto copy = *this;
        ++*this;
        return copy;
    }

    bool operator==(const integer_iterator& other) const {
        return value == other.value;
    }

    bool operator!=(const integer_iterator& other) const {
        return value != other.value;
    }

protected:
    I value;
};

template<typename I, typename std::enable_if<std::is_integral<I>::value,
                                             bool>::type
                     = true>
struct integer_range {
public:
    integer_range(I begin, I end)
        : begin_(begin), end_(end) {
    }
    integer_iterator<I> begin() const {
        return begin_;
    }
    integer_iterator<I> end() const {
        return end_;
    }

private:
    integer_iterator<I> begin_;
    integer_iterator<I> end_;
};

template<typename Integer1, typename Integer2,
         typename std::enable_if<std::is_integral<Integer1>::value,
                                 bool>::type
         = true,
         typename std::enable_if<std::is_integral<Integer2>::value,
                                 bool>::type
         = true>
integer_range<Integer2> irange(Integer1 begin, Integer2 end) {
    return {static_cast<Integer2>(begin),
            std::max(static_cast<Integer2>(begin), end)};
}

template<typename Integer,
         typename std::enable_if<std::is_integral<Integer>::value,
                                 bool>::type
         = true>
integer_range<Integer> irange(Integer end) {
    return {Integer(), std::max(Integer(), end)};
}
// End Iterger Iterator

static int IdToLit(int id, bool fCompl) {
    return (id << 1) | (fCompl ? 1 : 0);
}

static int LitToId(int lit) {
    return lit >> 1;
}

static int LitNot(int lit) {
    return lit ^ 1;
}
static int LitNotCond(int lit, bool cond) {
    return lit ^ (int)cond;
}

static int LitIsComplement(int lit) {
    return (lit & 1);
}

// Inline 32-bit population count; the builtin compiles to a library call
// without -mpopcnt. The original counts only the low 32 bits of each word.
static inline int popcount32(unsigned x) {
    x = x - ((x >> 1) & 0x55555555u);
    x = (x & 0x33333333u) + ((x >> 2) & 0x33333333u);
    x = (x + (x >> 4)) & 0x0F0F0F0Fu;
    return (int)((x * 0x01010101u) >> 24);
}

static inline const uint64_t elementary_mask[6] = {
    0xAAAAAAAAAAAAAAAA,
    0xCCCCCCCCCCCCCCCC,
    0xF0F0F0F0F0F0F0F0,
    0xFF00FF00FF00FF00,
    0xFFFF0000FFFF0000,
    0xFFFFFFFF00000000};
static inline const uint64_t ones_mask[7]{
    0x0000000000000001,
    0x0000000000000003,
    0x000000000000000f,
    0x00000000000000ff,
    0x000000000000ffff,
    0x00000000ffffffff,
    0xffffffffffffffff};

// Full tables are used only at the input boundary. Diagram nodes and their
// cofactors use Func below; no permutation or ref-counted full-table state is kept.
class TruthTable {
    int vars = 0;
    std::vector<uint64_t> words;

public:
    int nVars() const { return vars; }
    int nWords() const { return (int)words.size(); }
    uint64_t* data() { return words.data(); }
    const uint64_t* data() const { return words.data(); }

    void create(uint64_t bits) {
        assert(bits && !(bits & (bits - 1)) && bits <= 65536);
        vars = 0;
        while ((uint64_t(1) << vars) < bits)
            ++vars;
        words.assign((size_t)std::max(uint64_t(1), bits / 64), 0);
    }
    void readBinaryReverse(const char* text) {
        const size_t bits = strlen(text);
        create(bits);
        for (size_t i = 0; i < bits; ++i)
            if (text[bits - 1 - i] == '1')
                words[i >> 6] |= uint64_t(1) << (63 - (i & 63));
    }
    bool hasVariable(unsigned variable) const {
        if (variable < 6) {
            const int shift = 1 << variable;
            for (uint64_t w : words)
                if ((w & ~elementary_mask[variable]) != ((w & elementary_mask[variable]) >> shift))
                    return true;
        } else {
            const size_t step = size_t(1) << (variable - 6);
            for (size_t k = 0; k < words.size(); k += 2 * step)
                for (size_t i = 0; i < step; ++i)
                    if (words[k + i] != words[k + i + step])
                        return true;
        }
        return false;
    }
};

static uint64_t reverseBits(uint64_t n) {
    uint64_t result = 0;
    for (int i = 0; i < 64; ++i)
        result = (result << 1) | ((n >> i) & 1);
    return result;
}

class Combination {
public:
    Combination(int n, int r);
    bool next(void);
    void next(int n);
    std::vector<int>& get(void);
    std::vector<int> get_reverse(void);
    std::vector<int> get_reverse(int n);
    int count(void) const;
    int getN(void);
    int getR(void);

private:
    int n;
    int r;
    std::vector<int> data;
};

inline Combination::Combination(int n, int r)
    : n(n), r(r), data(r) {
    for (const auto& i : irange(r)) {
        data[i] = i;
    }
}

inline std::vector<int>& Combination::get(void) {
    return data;
}

inline int Combination::getN(void) {
    return n;
}

inline int Combination::getR(void) {
    return r;
}

bool Combination::next(void) {
    for (int i = r - 1; i >= 0; i--) {
        if (data[i] < n - r + i) {
            data[i]++;
            for (int j = i + 1; j < r; j++) {
                data[j] = data[j - 1] + 1;
            }
            return true;
        }
    }
    return false;
}

void Combination::next(int n) {
    for (const auto& i : irange(n)) {
        (void)i;
        next();
    }
}

int Combination::count(void) const {
    const int smaller = std::min(r, n - r);
    int ans = 1;

    for (const auto& i : irange(1, smaller + 1)) {
        ans *= n - smaller + i;
        ans /= i;
    }

    return ans;
}

std::vector<int> Combination::get_reverse(void) {
    std::vector<int> reverse_data = data;
    for (const auto& i : irange(r)) {
        reverse_data[i] = n - 1 - data[i];
    }
    return reverse_data;
}

std::vector<int> Combination::get_reverse(int n) {
    next(n);
    return get_reverse();
}

// Compact truth tables. A table with nLo in-word variables and nHi word
// variables has 2^nHi words; each word holds 2^nLo valid bits at its top, in
// the same most-significant-first order as TruthTable. When nLo == 6, or when
// nHi == 0, this is exactly the TruthTable layout.

// Removes in-word variable v from a word, keeping the half where v == keepOne.
// The remaining variables keep their relative order.
static inline uint64_t deleteInWordVar(uint64_t x, int v, int keepOne) {
    x = keepOne ? (x & ~elementary_mask[v]) : ((x & elementary_mask[v]) >> (1 << v));
    for (int k = v; k < 5; ++k)
        x = (x | (x >> (1 << k))) & ~elementary_mask[k + 1];
    return x << 32;
}

// Packs a (nLo, nHi) table into the standard layout of nLo + nHi variables.
static void packTable(std::vector<uint64_t>& words, int nLo, int nHi) {
    if (nLo == 6 || nHi == 0)
        return;
    const int chunk = 1 << nLo, perWord = 64 / chunk, nWords = 1 << nHi;
    const int nPacked = std::max(1, nWords / perWord);
    for (int i = 0; i < nPacked; ++i) {
        uint64_t packed = 0;
        for (int j = 0; j < perWord && i * perWord + j < nWords; ++j)
            packed |= words[i * perWord + j] >> (j * chunk);
        words[i] = packed;
    }
    words.resize(nPacked);
}

// Deletes every variable not in keepMask (bit j for local variable j) and
// packs the result. Returns the number of remaining variables.
static int compactTable(std::vector<uint64_t>& words, int nLo, int nHi, unsigned keepMask) {
    for (int j = nLo + nHi - 1; j >= nLo; --j) {
        if ((keepMask >> j) & 1)
            continue;
        const int bit = j - nLo, half = 1 << (nHi - 1);
        for (int i = 0; i < half; ++i)
            words[i] = words[(i & ((1 << bit) - 1)) | ((i >> bit) << (bit + 1))];
        words.resize(half);
        --nHi;
    }
    for (int j = nLo - 1; j >= 0; --j) {
        if ((keepMask >> j) & 1)
            continue;
        for (uint64_t& w : words)
            w = deleteInWordVar(w, j, 0);
        --nLo;
    }
    packTable(words, nLo, nHi);
    return nLo + nHi;
}

// Support of a (nLo, nHi) table as a mask over its local variables.
static unsigned tableSupport(const uint64_t* words, int nLo, int nHi) {
    unsigned mask = 0;
    const int nWords = 1 << nHi;
    for (int j = 0; j < nLo; ++j)
        for (int i = 0; i < nWords; ++i)
            if (((words[i] & elementary_mask[j]) >> (1 << j)) != (words[i] & ~elementary_mask[j])) {
                mask |= 1u << j;
                break;
            }
    for (int j = nLo; j < nLo + nHi; ++j) {
        const int step = 1 << (j - nLo);
        for (int i = 0; i < nWords && !((mask >> j) & 1); i += 2 * step)
            for (int k = 0; k < step; ++k)
                if (words[i + k] != words[i + step + k]) {
                    mask |= 1u << j;
                    break;
                }
    }
    return mask;
}

static inline int popcount64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ull);
    x = (x & 0x3333333333333333ull) + ((x >> 2) & 0x3333333333333333ull);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0Full;
    return (int)((x * 0x0101010101010101ull) >> 56);
}

static inline uint64_t validMask(int s) {
    return s >= 6 ? ~uint64_t(0) : (~uint64_t(0) << (64 - (1 << s)));
}

// A function of the diagram's variables stored over its support only, in the
// standard layout of s variables. Two equal functions have equal support and
// equal bits, so the pair is a canonical key. The original algorithm works on
// full-size tables; every quantity it derives from a table is recomputed here
// from the compact form, including the quirks of the original counting code.
struct Func {
    unsigned support;
    int s;
    std::vector<uint64_t> bits;

    // Unused pool entries have no table. Live functions initialize their bits.
    Func() : support(0), s(0) {}

    static Func fromTable(const TruthTable& tt) {
        Func f;
        const int n = tt.nVars();
        for (int v = 0; v < n; ++v)
            if (tt.hasVariable(v))
                f.support |= 1u << v;
        f.bits.assign(tt.data(), tt.data() + tt.nWords());
        f.s = compactTable(f.bits, std::min(n, 6), std::max(n - 6, 0), f.support);
        return f;
    }
    bool hasVar(int v) const {
        return (support >> v) & 1;
    }
    int rank(int v) const {
        return popcount32(support & ((1u << v) - 1));
    }
    // Canonical fingerprints screen lookups; full word comparisons decide
    // equality, including when unrelated functions have the same fingerprint.
    uint64_t canonicalHash() const {
        assert(!bits.empty());
        const uint64_t flip = bits[0] >> 63 ? validMask(s) : 0;
        uint64_t hash = uint64_t(support) + 0x9E3779B97F4A7C15ull;
        for (uint64_t w : bits)
            hash = (hash ^ (w ^ flip)) * 0x100000001B3ull;
        hash ^= hash >> 33;
        hash *= 0xC4CEB9FE1A85EC53ull;
        return hash ^ (hash >> 33);
    }
    bool sameCanonical(const Func& other) const {
        if (support != other.support)
            return false;
        assert(s == other.s && bits.size() == other.bits.size());
        const uint64_t flip = (bits[0] ^ other.bits[0]) >> 63 ? validMask(s) : 0;
        for (size_t w = 0; w < bits.size(); ++w)
            if (bits[w] != (other.bits[w] ^ flip))
                return false;
        return true;
    }
    // Drops variables the bits no longer depend on.
    void normalize() {
        const int nLo = std::min(s, 6), nHi = s - nLo;
        const unsigned keepLocal = tableSupport(bits.data(), nLo, nHi);
        if (keepLocal == (1u << s) - 1)
            return;
        unsigned newSupport = 0;
        for (int v = 0, r = 0; v < 32; ++v)
            if ((support >> v) & 1) {
                if ((keepLocal >> r) & 1)
                    newSupport |= 1u << v;
                ++r;
            }
        s = compactTable(bits, nLo, nHi, keepLocal);
        support = newSupport;
    }
    // Cofactor with respect to original variable v; value 1 keeps the v = 1 half.
    Func cofactor(int v, int value) const {
        if (!hasVar(v))
            return *this;
        Func r;
        r.support = support & ~(1u << v);
        r.s = s - 1;
        const int j = rank(v);
        if (j >= 6) {
            const int bit = j - 6, half = 1 << (s - 7);
            r.bits.resize(half);
            for (int i = 0; i < half; ++i)
                r.bits[i] = bits[(i & ((1 << bit) - 1)) | ((((i >> bit) << 1) | value) << bit)];
        } else {
            r.bits = bits;
            for (uint64_t& w : r.bits)
                w = deleteInWordVar(w, j, value);
            packTable(r.bits, std::min(s, 6) - 1, std::max(s - 6, 0));
        }
        r.normalize();
        return r;
    }
    // Number of minterms with f = 1 over the support, optionally restricted
    // by up to two local variables (-1 for none).
    uint64_t count(int varA, int valA, int varB = -1, int valB = 0) const {
        const int nLo = std::min(s, 6);
        const int nWords = s > 6 ? 1 << (s - 6) : 1;
        uint64_t wordMask = validMask(s);
        if (varA >= 0 && varA < nLo)
            wordMask &= valA ? ~elementary_mask[varA] : elementary_mask[varA];
        if (varB >= 0 && varB < nLo)
            wordMask &= valB ? ~elementary_mask[varB] : elementary_mask[varB];
        uint64_t total = 0;
        for (int w = 0; w < nWords; ++w) {
            if (varA >= nLo && ((w >> (varA - nLo)) & 1) != valA)
                continue;
            if (varB >= nLo && ((w >> (varB - nLo)) & 1) != valB)
                continue;
            total += popcount64(bits[w] & wordMask);
        }
        return total;
    }
    // Full single-word table for n <= 6 variables.
    uint64_t expand(int n) const {
        uint64_t word = 0;
        for (int m = 0; m < (1 << n); ++m) {
            int c = 0;
            for (int v = 0, r = 0; v < n; ++v)
                if ((support >> v) & 1)
                    c |= ((m >> v) & 1) << r++;
            word |= ((bits[0] >> (63 - c)) & 1) << (63 - m);
        }
        return word;
    }
    // Same value as the original fourierCost on the full table: unused
    // variables only add zero coefficients, in the same accumulation order.
    float fourierCost(int n, std::vector<int64_t>& spectrum) const {
        const int nBits = 1 << s;
        spectrum.resize(nBits);
        for (int k = 0; k < nBits; ++k)
            spectrum[k] = ((bits[k >> 6] >> (63 - (k & 63))) & 1) ? 1 : -1;
        for (int step = 1; step < nBits; step *= 2)
            for (int base = 0; base < nBits; base += 2 * step)
                for (int i = 0; i < step; ++i) {
                    int64_t a = spectrum[base + i], b = spectrum[base + step + i];
                    spectrum[base + i] = a + b;
                    spectrum[base + step + i] = a - b;
                }
        float weights[17] = {};
        int sparsity = 0;
        for (int k = 0; k < nBits; ++k) {
            float coefficient = (float)spectrum[k] / nBits;
            weights[popcount32((unsigned)k)] += std::pow(coefficient, 2);
            sparsity += spectrum[k] != 0;
        }
        float cost = 0;
        int weightSparsity = 0;
        for (int i = 0; i <= n; ++i) {
            cost += weights[i] * (i * 3);
            weightSparsity += weights[i] != 0;
        }
        return cost + (float)sparsity / weightSparsity;
    }
};

// The original counts ones with a 32-bit population count on 64-bit words, so
// for n >= 6 it counts the minterms with variable 5 equal to 1. For n <= 6 the
// single full word is rebuilt and the original expression is evaluated.
static uint64_t quirkCount(const Func& f, int n, int varA, int valA) {
    const int extra = n - f.s;
    if (varA == 5) {
        return f.hasVar(5) ? f.count(f.rank(5), valA) << extra : (f.count(-1, 0) << extra) >> 1;
    }
    const int ra = varA < 0 ? -1 : f.rank(varA);
    if (f.hasVar(5))
        return f.count(ra, valA, f.rank(5), 1) << extra;
    return (f.count(ra, valA) << extra) >> 1;
}

// An owned canonical key. A one-word function fits inline; larger functions
// own only the remaining words. Lookups compare the query directly, without
// allocating a temporary key.
struct FuncKey {
    unsigned support;
    uint64_t first;
    std::vector<uint64_t> rest;

    FuncKey(unsigned support, const std::vector<uint64_t>& bits, int s)
        : support(support), first(0) {
        assert(!bits.empty());
        const uint64_t flip = bits[0] >> 63 ? validMask(s) : 0;
        first = bits[0] ^ flip;
        rest.resize(bits.size() - 1);
        for (size_t w = 1; w < bits.size(); ++w)
            rest[w - 1] = bits[w] ^ flip;
    }
    bool matches(unsigned otherSupport, const std::vector<uint64_t>& bits, int s) const {
        if (support != otherSupport)
            return false;
        // Equal support fixes the packed table length.
        assert(rest.size() + 1 == bits.size());
        const uint64_t flip = bits[0] >> 63 ? validMask(s) : 0;
        if (first != (bits[0] ^ flip))
            return false;
        for (size_t w = 1; w < bits.size(); ++w)
            if (rest[w - 1] != (bits[w] ^ flip))
                return false;
        return true;
    }
};

// The union is closed under complementation, so count each stored pair twice.
struct CofactorSet {
    std::vector<FuncKey> keys;
    size_t rejectedSize = 0;
    size_t size() const { return rejectedSize ? rejectedSize : 2 * keys.size(); }
    void reject(size_t limit) { keys.clear(); rejectedSize = limit; }
    void insert(unsigned support, const std::vector<uint64_t>& bits, int s) {
        assert(!rejectedSize && !bits.empty());
        for (const FuncKey& key : keys)
            if (key.matches(support, bits, s))
                return;
        keys.emplace_back(support, bits, s);
    }
};

// Counts the distinct cofactors of every bound-set candidate, as the original
// did with permuted full-size tables. Each node is compacted to its support.
// Every cofactor row is keyed by its support over the original variables and
// its bits over that support, so equal functions get equal keys regardless of
// the node they come from. Distinct counts and union sizes are unchanged.
// Skip candidates whose union reached the threshold. Unequal partial hashes
// also prove unequal rows, allowing early rejection because the union grows.
void doDecomposition(const Func& f, int nBoundSet, const std::vector<int>& supportSet, std::vector<int>& record, std::vector<CofactorSet>& recordCof) {
    assert(nBoundSet <= (int)supportSet.size());
    const int limit = (1 << nBoundSet) * 3 / 4;
    // The node is already compact over its support.
    const unsigned keep = f.support;
    std::vector<int> support;
    for (int v = 0; v < 32; ++v)
        if ((keep >> v) & 1)
            support.push_back(v);
    const int s = f.s;
    const int nLo = std::min(s, 6), nHi = s - nLo;
    const uint64_t* data = f.bits.data();
    Combination generator((int)supportSet.size(), nBoundSet);
    std::vector<int> bLo, bHi, freeIds, hiPos;
    std::vector<unsigned> xw, groupBase;
    std::vector<uint64_t> rows, hashes, distinct, chunks, work;
    std::vector<int> seenRows;
    int genIndex = 0;
    do {
        const int index = genIndex++;
        CofactorSet& all = recordCof[index];
        if ((int)all.size() >= limit)
            continue;
        // Bound variables in the node's numbering; absent ones only duplicate rows.
        bLo.clear();
        bHi.clear();
        unsigned boundMask = 0;
        for (int i = 0; i < nBoundSet; ++i) {
            const int v = supportSet[supportSet.size() - 1 - generator.get()[i]];
            if (!((keep >> v) & 1))
                continue;
            const int local = (int)(std::lower_bound(support.begin(), support.end(), v) - support.begin());
            boundMask |= 1u << local;
            if (local < nLo)
                bLo.push_back(local);
            else
                bHi.push_back(local - nLo);
        }
        std::sort(bLo.begin(), bLo.end());
        std::sort(bHi.begin(), bHi.end());
        freeIds.clear();
        for (int j = 0; j < s; ++j)
            if (!((boundMask >> j) & 1))
                freeIds.push_back(support[j]);
        const int nBLo = (int)bLo.size(), nBHi = (int)bHi.size();
        const int nFLo = nLo - nBLo, nFHi = nHi - nBHi;
        const uint64_t topMask = nFLo == 6 ? ~uint64_t(0) : (~uint64_t(0) << (64 - (1 << nFLo)));
        unsigned bHiMask = 0;
        for (int b : bHi)
            bHiMask |= 1u << b;
        hiPos.clear();
        for (int b = 0; b < nHi; ++b)
            if (!((bHiMask >> b) & 1))
                hiPos.push_back(b);
        xw.assign(size_t(1) << nFHi, 0);
        for (int i = 1; i < (1 << nFHi); ++i) {
            const unsigned low = (unsigned)i & (0u - (unsigned)i);
            int r = 0;
            while (!((low >> r) & 1)) ++r;
            xw[i] = xw[i ^ low] | (1u << hiPos[r]);
        }
        groupBase.assign(size_t(1) << nBHi, 0);
        for (int bh = 0; bh < (1 << nBHi); ++bh)
            for (int r = 0; r < nBHi; ++r)
                groupBase[bh] |= ((bh >> r) & 1) << bHi[r];
        // Row r = group * 2^nBLo + chunk; a row has 2^nFHi words of 2^nFLo top bits.
        const int nRows = 1 << (nBLo + nBHi), rowWords = 1 << nFHi;
        rows.resize(size_t(nRows) * rowWords);   // every word is overwritten
        hashes.assign(nRows, 0);
        chunks.resize(size_t(1) << nBLo);
        const uint64_t K = 0x9E3779B97F4A7C15ull;
        uint64_t powerSum = 0;
        bool dead = false;
        for (int xh = 0; xh < rowWords && !dead; ++xh) {
            powerSum = powerSum * K + 1;
            for (int bh = 0; bh < (1 << nBHi); ++bh) {
                chunks[0] = data[groupBase[bh] | xw[xh]];
                int nChunks = 1;
                for (int b = nBLo - 1; b >= 0; --b, nChunks *= 2)
                    for (int c = nChunks - 1; c >= 0; --c) {
                        chunks[2 * c + 1] = deleteInWordVar(chunks[c], bLo[b], 1);
                        chunks[2 * c] = deleteInWordVar(chunks[c], bLo[b], 0);
                    }
                for (int c = 0; c < nChunks; ++c) {
                    const int r = (bh << nBLo) | c;
                    rows[size_t(r) * rowWords + xh] = chunks[c];
                    hashes[r] = hashes[r] * K + chunks[c];
                }
            }
            if (2 * nRows >= limit && (xh == 0 || xh == 1 || xh == 3 || xh == 7 ||
                xh == 31 || xh == 127 || xh == 511 || xh + 1 == rowWords)) {
                const uint64_t total = topMask * powerSum;
                distinct.resize(2 * nRows);
                for (int r = 0; r < nRows; ++r) {
                    distinct[2 * r] = hashes[r];
                    distinct[2 * r + 1] = total - hashes[r];
                }
                std::sort(distinct.begin(), distinct.end());
                if ((int)(std::unique(distinct.begin(), distinct.end()) - distinct.begin()) >= limit)
                    dead = true;
            }
        }
        if (dead) {
            all.reject(limit);
            continue;
        }
        seenRows.clear();
        for (int r = 0; r < nRows; ++r) {
            const uint64_t* row = &rows[size_t(r) * rowWords];
            // Hashes only screen comparisons: verify every word before skipping
            // a repeated row. Both polarities still count separately locally.
            bool duplicate = false, complemented = false;
            for (int old : seenRows) {
                const uint64_t* previous = &rows[size_t(old) * rowWords];
                if (hashes[r] == hashes[old] && !memcmp(row, previous, rowWords * sizeof(uint64_t))) {
                    duplicate = true;
                    break;
                }
                if (hashes[r] == topMask * powerSum - hashes[old]) {
                    int w = 0;
                    while (w < rowWords && row[w] == (previous[w] ^ topMask)) ++w;
                    complemented |= w == rowWords;
                }
            }
            if (duplicate)
                continue;
            seenRows.push_back(r);
            // Its complement already contributed the same pair to the union.
            if (complemented)
                continue;
            // Canonical key: support over original variables, then packed bits.
            const unsigned rowKeep = tableSupport(row, nFLo, nFHi);
            uint64_t supportMask = 0;
            for (int j = 0; j < nFLo + nFHi; ++j)
                if ((rowKeep >> j) & 1)
                    supportMask |= uint64_t(1) << freeIds[j];
            work.assign(row, row + rowWords);
            const int nRowVars = compactTable(work, nFLo, nFHi, rowKeep);
            all.insert((unsigned)supportMask, work, nRowVars);
            if ((int)all.size() >= limit)
                break;
        }
        record[index] += (int)seenRows.size();
    } while (generator.next());
}

class DecisionDiagram;

class DecisionNode {
    friend class DecisionDiagram;

public:
    DecisionNode();

private:
    static std::vector<float> computeEntropyCost(DecisionDiagram* mgr, const Func& f, std::set<int>& invalid_variables);

private:
    int decisionVariable;
    Func f;
    int left;
    int right;
};

inline DecisionNode::DecisionNode()
    : decisionVariable(-1), left(-1), right(-1) {
}

class DecisionDiagram {
    friend class DecisionNode;

public:
    DecisionDiagram();

public:
    void addOutput(TruthTable& tt);

    void build(void);
    void buildWithDecisionVariable(int node_id, int variable, std::set<int>& newWaitingNodes, int fInv = 0);
    void buildOneCluster(std::vector<int>& cluster);
    std::vector<std::vector<int> > buildClusters(std::vector<int> waitingNodes);
    std::vector<int> computeSupportSet(const std::vector<int>& nodes);
    std::vector<int> buildWithTheseSupportWithEntropyAndFourier(std::vector<int>& waitingNodes, std::set<int>& supportSet);

private:
    void init(int nVars);
    DecisionNode& getNode(int id) {
        return node_pool[id];
    }
    void prepareSpace(void);
    int newNode(void);
    int newNode(const Func& f);
    int findNode(const Func& f, uint64_t hash) const;
    int const0Node(void);
    int const1Node(void);
    float getEntropyCost(const Func& f);
    float getFourierCost(const Func& f);

public:
    void buildAig(Gia_Man_t *pAig);

private:
    void topoRec(int node, std::set<int>& visited, std::vector<int>& nodes);
    void topoSort(int root, std::vector<int>& nodes);

public:
    int nVars(void);
    int nDecomp(void);
    int nNodeAllocated(void) { return _num_node_allocated; }

private:
    int _nVars;
    int _nDecomp;
    int const0;
    int _num_node_allocated;
    std::vector<DecisionNode> node_pool;
    std::vector<int> roots;
    std::unordered_multimap<uint64_t, int> hash2node;
    std::unordered_multimap<uint64_t, std::pair<FuncKey, float>> hash2cost;
    std::vector<int> sortedNodes;
    std::vector<int64_t> spectrumScratch;
};

inline DecisionDiagram::DecisionDiagram()
    : _nVars(0), _nDecomp(0), const0(0), _num_node_allocated(0) {
}

inline int DecisionDiagram::nVars(void) {
    return _nVars;
}

inline int DecisionDiagram::nDecomp(void) {
    return _nDecomp;
}

inline int DecisionDiagram::const0Node(void) {
    return const0;
}
inline int DecisionDiagram::const1Node(void) {
    return LitNot(const0);
}

void DecisionDiagram::init(int nVars) {
    _nVars = nVars;
    const0 = newNode();
    getNode(LitToId(const0)).decisionVariable = 0;
    getNode(LitToId(const0)).right = -1;
    getNode(LitToId(const0)).left = -1;
    getNode(LitToId(const0)).f = Func();
    getNode(LitToId(const0)).f.bits.assign(1, 0);
    hash2node.emplace(getNode(LitToId(const0)).f.canonicalHash(), const0);
}

void DecisionDiagram::prepareSpace(void) {
    if (_num_node_allocated + 2 > node_pool.size() / 2) {
        node_pool.resize(node_pool.size() * 2);
    }
}

int DecisionDiagram::newNode(void) {
    if (_num_node_allocated > node_pool.size() / 2) {
        node_pool.resize(node_pool.size() * 2);
    }
    return IdToLit(_num_node_allocated++, false);
}

int DecisionDiagram::findNode(const Func& f, uint64_t hash) const {
    const auto range = hash2node.equal_range(hash);
    for (auto it = range.first; it != range.second; ++it)
        if (f.sameCanonical(node_pool[LitToId(it->second)].f))
            return it->second;
    return -1;
}

int DecisionDiagram::newNode(const Func& f) {
    // Index existing nodes by fingerprint and compare their owned functions.
    // Store literals, not pool pointers: growing the pool cannot invalidate keys.
    const int phase = (int)(f.bits[0] >> 63);
    const uint64_t hash = f.canonicalHash();
    const int found = findNode(f, hash);
    if (found >= 0)
        return LitNotCond(found, phase);
    int new_node = newNode();
    getNode(LitToId(new_node)).f = f;
    hash2node.emplace(hash, LitNotCond(new_node, phase));
    return new_node;
}

void DecisionDiagram::addOutput(TruthTable& tt) {
    if (node_pool.empty()) {
        node_pool.resize((uint64_t)1 << tt.nVars());
        this->init(tt.nVars());
    }
    roots.emplace_back(newNode(Func::fromTable(tt)));
}

float DecisionDiagram::getFourierCost(const Func& f) {
    // Complementation preserves the score. Construct an owned key only on a
    // cache miss; fingerprint collisions are resolved by exact word comparison.
    const uint64_t hash = f.canonicalHash();
    if (findNode(f, hash) >= 0)
        return 0;
    const auto range = hash2cost.equal_range(hash);
    for (auto it = range.first; it != range.second; ++it)
        if (it->second.first.matches(f.support, f.bits, f.s))
            return it->second.second;
    const float cost = f.fourierCost(_nVars, spectrumScratch);
    hash2cost.emplace(hash, std::make_pair(FuncKey(f.support, f.bits, f.s), cost));
    return cost;
}

float DecisionDiagram::getEntropyCost(const Func& f) {
    const uint64_t nBits = uint64_t(1) << _nVars;
    int out1 = _nVars <= 6 ? popcount32((unsigned)f.expand(_nVars)) : (int)quirkCount(f, _nVars, 5, 1);
    float p1 = (float)out1 / nBits;
    float p0 = 1 - p1;
    float entropy = -(((p0 != 0) ? p0 * log2(p0) : 0) + ((p1 != 0) ? p1 * log2(p1) : 0));
    return entropy;
}

std::set<int> getInvalidVariables(DecisionDiagram* mgr, std::vector<int>& available_variables) {
    std::vector<int> all_variable(mgr->nVars());
    std::iota(all_variable.begin(), all_variable.end(), 0);
    std::set<int> all_variable_set(all_variable.begin(), all_variable.end());
    std::set<int> invalid_variables;
    std::set_difference(all_variable_set.begin(), all_variable_set.end(), available_variables.begin(), available_variables.end(), std::inserter(invalid_variables, invalid_variables.begin()));
    return invalid_variables;
}

std::vector<float> DecisionNode::computeEntropyCost(DecisionDiagram* mgr, const Func& f, std::set<int>& invalid_variables) {
    const int n = mgr->nVars();
    float oriInfo = mgr->getEntropyCost(f);
    const uint64_t full = n <= 6 ? f.expand(n) : 0;
    std::vector<float> costs(n, 1024);
    for (int i = 0; i < n; ++i) {
        if (invalid_variables.count(i)) continue;
        if (!f.hasVar(i))
            continue;
        int out1_0 = 0, out1_1 = 0;
        if (n <= 6) {
            // The original expression on the single full word.
            uint64_t a = full & elementary_mask[i];
            uint64_t b = full & ~elementary_mask[i];
            out1_0 = popcount32((unsigned)(a | (a >> (1 << i))));
            out1_1 = popcount32((unsigned)(b | (b << (1 << i))));
        } else if (i == 5) {
            out1_0 = (int)quirkCount(f, n, 5, 0);
            out1_1 = (int)quirkCount(f, n, 5, 1);
        } else {
            out1_0 = 2 * (int)quirkCount(f, n, i, 0);
            out1_1 = 2 * (int)quirkCount(f, n, i, 1);
        }
        int out0_0 = (int)(uint64_t(1) << n) - out1_0;
        int out0_1 = (int)(uint64_t(1) << n) - out1_1;
        float p1_0 = (float)out1_0 / (out1_0 + out0_0 + 1e-8);
        float p0_0 = (float)out0_0 / (out1_0 + out0_0 + 1e-8);
        float p1_1 = (float)out1_1 / (out1_1 + out0_1 + 1e-8);
        float p0_1 = (float)out0_1 / (out1_1 + out0_1 + 1e-8);
        int n0 = out1_0 + out0_0;
        int n1 = out1_1 + out0_1;
        int nAll = n0 + n1;
        float info0 = ((float)n0 / nAll) * -(((p0_0 != 0) ? p0_0 * log2(p0_0) : 0) + ((p1_0 != 0) ? p1_0 * log2(p1_0) : 0));
        float info1 = ((float)n1 / nAll) * -(((p0_1 != 0) ? p0_1 * log2(p0_1) : 0) + ((p1_1 != 0) ? p1_1 * log2(p1_1) : 0));
        costs[i] = -(oriInfo - info0 - info1);
    }
    return costs;
}

double jaccardSimilarity(const std::unordered_set<int>& a, const std::unordered_set<int>& b) {
    std::unordered_set<int> intersection, unionSet = a;
    for (int num : b) {
        if (a.count(num)) intersection.insert(num);
        unionSet.insert(num);
    }
    return (double)intersection.size() / unionSet.size();
}

std::vector<std::vector<int> > autoClusterIndex(std::vector<std::vector<int> >& sequences, double threshold = 0.95) {
    int n = sequences.size();
    std::vector<std::unordered_set<int> > sets(n);

    for (int i = 0; i < n; i++) {
        sets[i] = std::unordered_set<int>(sequences[i].begin(), sequences[i].end());
    }

    std::vector<std::vector<int> > graph(n);
    for (int i = 0; i < n; i++) {
        for (int j = i + 1; j < n; j++) {
            if (jaccardSimilarity(sets[i], sets[j]) >= threshold) {
                graph[i].push_back(j);
                graph[j].push_back(i);
            }
        }
    }

    std::vector<bool> visited(n, false);
    std::vector<std::vector<int> > clusters;

    std::function<void(int, std::vector<int>&)> dfs = [&](int node, std::vector<int>& cluster) {
        visited[node] = true;
        cluster.push_back(node);
        for (int neighbor : graph[node]) {
            if (!visited[neighbor]) {
                dfs(neighbor, cluster);
            }
        }
    };

    for (int i = 0; i < n; i++) {
        if (!visited[i]) {
            std::vector<int> cluster;
            dfs(i, cluster);
            clusters.push_back(cluster);
        }
    }

    return clusters;
}

std::vector<std::vector<int> > DecisionDiagram::buildClusters(std::vector<int> waitingNodes) {
    int nVars = _nVars;
    std::vector<std::vector<int> > supportSetVec(waitingNodes.size());
    for (const auto& i : irange(waitingNodes.size())) {
        auto& node = getNode(waitingNodes[i]);
        for (const auto& var : irange(nVars)) {
            if (node.f.hasVar(var)) {
                supportSetVec[i].push_back(var);
            }
        }
    }

    auto clustersIndex = autoClusterIndex(supportSetVec);
    std::vector<std::vector<int> > clusters;
    for (const auto& cluster : clustersIndex) {
        std::vector<int> newCluster;
        for (const auto& index : cluster) {
            if (waitingNodes[index] == LitToId(const0Node())) { // FIX
                continue;
            }
            newCluster.push_back(waitingNodes[index]);
        }
        if (newCluster.empty()) { // FIX
            continue;
        }
        clusters.push_back(newCluster);
    }

    return clusters;
}

void DecisionDiagram::buildWithDecisionVariable(int node_id, int variable, std::set<int>& newWaitingNodes, int fInv) {
    prepareSpace();
    if (getNode(node_id).left != -1 || getNode(node_id).right != -1) {
        return;
    }
    getNode(node_id).decisionVariable = variable;
    if (getNode(node_id).f.hasVar(variable)) {
        // Left is the positive cofactor, right the negative one. Re-fetch the
        // parent after allocation, so pool growth cannot invalidate a reference.
        Func ltt = getNode(node_id).f.cofactor(variable, 1);
        Func rtt = getNode(node_id).f.cofactor(variable, 0);
        const int left = newNode(ltt);
        const int right = newNode(rtt);
        getNode(node_id).left = left;
        getNode(node_id).right = right;
    }
    const auto& node = getNode(node_id);
    if (node.left == -1 && node.right == -1) {
        newWaitingNodes.insert(node_id);
        return;
    }
    if (!fInv) {
        if (!LitIsComplement(node.left) && (node.left != const0Node())) {
            newWaitingNodes.insert(LitToId(node.left));
        }
        if (!LitIsComplement(node.right) && (node.right != const0Node())) {
            newWaitingNodes.insert(LitToId(node.right));
        }
    } else {
        if (node.left != const0Node() && node.left != const1Node()) {
            newWaitingNodes.insert(LitToId(node.left));
        }
        if (node.right != const0Node() && node.right != const1Node()) {
            newWaitingNodes.insert(LitToId(node.right));
        }
    }
}

std::vector<int> DecisionDiagram::computeSupportSet(const std::vector<int>& nodes) {
    unsigned mask = 0;
    for (const auto& node_id : nodes)
        mask |= getNode(node_id).f.support;
    std::vector<int> supportSet;
    for (int var = 0; var < _nVars; ++var)
        if ((mask >> var) & 1)
            supportSet.push_back(var);
    return supportSet;
}

template<typename T>
float min(std::vector<T>& array) {
    return *std::min_element(array.begin(), array.end());
}

void DecisionDiagram::build(void) {
    std::vector<int> trueNodeIds;
    for (const auto& root : roots) {
        int root_id = LitToId(root);
        // The original compares the root literal with node ids. This is kept so
        // that repeated or complemented outputs are processed exactly as in &dg.
        if (std::find(trueNodeIds.begin(), trueNodeIds.end(), root) == trueNodeIds.end())
            trueNodeIds.emplace_back(root_id);
    }
    std::vector<int> waitingNodes = trueNodeIds;

    auto clusters = buildClusters(waitingNodes);
    for (auto& cluster : clusters) {
        buildOneCluster(cluster);
    }

    // topo sort
    std::set<int> visited;
    for (const auto& root : roots) {
        this->topoRec(LitToId(root), visited, this->sortedNodes);
    }
}

std::vector<int> DecisionDiagram::buildWithTheseSupportWithEntropyAndFourier(std::vector<int>& waitingNodes, std::set<int>& supportSet) {
    int nVars = _nVars;
    std::set<int> invalid_variables;
    for (const auto& i : irange(nVars)) {
        if (supportSet.find(i) == supportSet.end()) {
            invalid_variables.insert(i);
        }
    }
    while (!waitingNodes.empty() && !supportSet.empty()) {
        // compute gain
        std::vector<float> costs(nVars, 1024);
        for (const auto& nodeId : waitingNodes) {
            auto& node = getNode(nodeId);
            auto cost = DecisionNode::computeEntropyCost(this, node.f, invalid_variables);
            for (const auto& i : irange(nVars)) {
                costs[i] += (cost[i] == 1024) ? 0 : cost[i];
            }
        }

        // find decision variable
        std::vector<int> decisionSet;
        int decisionVariable = std::distance(costs.begin(), std::min_element(costs.begin(), costs.end()));
        float decisionCost = costs[decisionVariable];
        for (const auto& i : irange(nVars)) {
            if (costs[i] == decisionCost && !invalid_variables.count(i)) {
                decisionSet.push_back(i);
            }
        }
        if (min(costs) == 1024) {
            decisionVariable = *supportSet.begin();
        }
        if (decisionSet.size() > 1) {
            std::vector<float> fouerierCost(decisionSet.size(), 0);
            for (const auto& nodeId : waitingNodes) {
                auto& node = getNode(nodeId);
                std::vector<float> cost(decisionSet.size(), 8192);
                for (const auto& i : irange(decisionSet.size())) {
                    if (invalid_variables.find(decisionSet[i]) != invalid_variables.end()) continue;
                    if (!node.f.hasVar(decisionSet[i])) {
                        continue;
                    }
                    Func cofactor0 = node.f.cofactor(decisionSet[i], 0);
                    Func cofactor1 = node.f.cofactor(decisionSet[i], 1);
                    cost[i] = getFourierCost(cofactor0) + getFourierCost(cofactor1);
                }
                for (const auto& i : irange(decisionSet.size())) {
                    fouerierCost[i] += cost[i];
                }
            }
            int decisionIndex = std::distance(fouerierCost.begin(), std::min_element(fouerierCost.begin(), fouerierCost.end()));
            decisionVariable = decisionSet[decisionIndex];
        }
        std::set<int> new_waiting_nodes;
        for (const auto& nodeId : waitingNodes) {
            buildWithDecisionVariable(nodeId, decisionVariable, new_waiting_nodes);
        }
        waitingNodes = std::vector<int>(new_waiting_nodes.begin(), new_waiting_nodes.end());
        invalid_variables.insert(decisionVariable);
        supportSet.erase(decisionVariable);
    }
    return waitingNodes;
}

void DecisionDiagram::buildOneCluster(std::vector<int>& cluster) {
    int enableFourier = 1;
    int enableDecompose = 1;

    std::vector<int> waiting_nodes = cluster;

    int nVars = _nVars;
    while (!waiting_nodes.empty()) {
        // compute support set
        std::vector<int> supportSet = computeSupportSet(waiting_nodes);
        std::set<int> invalid_variables = getInvalidVariables(this, supportSet);

        // compute multi-output decomposition
        // if the multi-output decomposition exist, then build the nodes
        int nBoundSet = std::max(2, std::min(4, (int)supportSet.size()));
        if (supportSet.size() > nBoundSet && enableDecompose) {
            std::vector<int> record(Combination(supportSet.size(), nBoundSet).count(), 0);
            std::vector<CofactorSet> recordCofoactor(Combination(supportSet.size(), nBoundSet).count());
            for (const auto& nodeIndex : waiting_nodes) {
                auto& node = getNode(nodeIndex);
                doDecomposition(node.f, nBoundSet, supportSet, record, recordCofoactor);
            }
            auto record_copy = record;
            for (const auto& i : irange(recordCofoactor.size())) {
                record[i] = recordCofoactor[i].size();
            }
            int minRecord = *std::min_element(record.begin(), record.end());
            if (minRecord < (1 << nBoundSet) * 3 / 4) {
                std::vector<int> minRecordIndex;
                std::vector<int> ref;
                for (const auto& i : irange(record.size())) {
                    if (record[i] == minRecord) {
                        minRecordIndex.push_back(i);
                        ref.push_back(record_copy[i]);
                    }
                }
                std::set<int> unionSet;
                for (const auto& index : minRecordIndex) {
                    auto comb = Combination(supportSet.size(), nBoundSet).get_reverse(index);
                    for (const auto& i : comb) {
                        unionSet.insert(supportSet[i]);
                    }
                }
                if (unionSet.size() == nBoundSet && min(ref) > nBoundSet) {
                    waiting_nodes = buildWithTheseSupportWithEntropyAndFourier(waiting_nodes, unionSet);
                    continue;
                }
                supportSet = std::vector<int>(unionSet.begin(), unionSet.end());
            }
        }

        int decisionVariable = 0;
        // compute gain
        std::vector<float> costs(nVars, 1024);
        for (const auto& nodeId : waiting_nodes) {
            auto& node = getNode(nodeId);
            auto cost = DecisionNode::computeEntropyCost(this, node.f, invalid_variables);
            for (const auto& i : irange(nVars)) {
                costs[i] += (cost[i] == 1024) ? 0 : cost[i];
            }
        }

        // find decision variable
        std::vector<int> decisionSet;
        decisionVariable = std::distance(costs.begin(), std::min_element(costs.begin(), costs.end()));
        float decisionCost = costs[decisionVariable];
        for (const auto& i : irange(nVars)) {
            if (costs[i] == decisionCost && !invalid_variables.count(i)) {
                decisionSet.push_back(i);
            }
        }
        if (min(costs) == 1024) {
            decisionVariable = supportSet[0];
        }
        if (decisionSet.size() > 1 && enableFourier) {
            std::vector<float> fouerierCost(decisionSet.size(), 0);
            for (const auto& nodeId : waiting_nodes) {
                auto& node = getNode(nodeId);
                std::vector<float> cost(decisionSet.size(), 8192);
                for (const auto& i : irange(decisionSet.size())) {
                    if (invalid_variables.find(decisionSet[i]) != invalid_variables.end()) continue;
                    if (!node.f.hasVar(decisionSet[i])) {
                        continue;
                    }
                    Func cofactor0 = node.f.cofactor(decisionSet[i], 0);
                    Func cofactor1 = node.f.cofactor(decisionSet[i], 1);
                    cost[i] = getFourierCost(cofactor0) + getFourierCost(cofactor1);
                }
                for (const auto& i : irange(decisionSet.size())) {
                    fouerierCost[i] += cost[i];
                }
            }
            int decisionIndex = std::distance(fouerierCost.begin(), std::min_element(fouerierCost.begin(), fouerierCost.end()));
            decisionVariable = decisionSet[decisionIndex];
        }

        std::set<int> next_waiting_nodes;
        for (const auto& nodeId : waiting_nodes) {
            buildWithDecisionVariable(nodeId, decisionVariable, next_waiting_nodes, 0);
        }
        waiting_nodes = std::vector<int>(next_waiting_nodes.begin(), next_waiting_nodes.end());
    }
}

void DecisionDiagram::topoRec(int node, std::set<int>& visited, std::vector<int>& nodes) {
    if (visited.find(node) != visited.end() || node == const0) {
        return;
    }
    visited.insert(node);
    if (getNode(node).left != -1) {
        topoRec(LitToId(getNode(node).left), visited, nodes);
    }
    if (getNode(node).right != -1) {
        topoRec(LitToId(getNode(node).right), visited, nodes);
    }
    nodes.push_back(node);
}

void DecisionDiagram::topoSort(int root, std::vector<int>& nodes) {
    std::set<int> visited;
    topoRec(root, visited, nodes);
}

void DecisionDiagram::buildAig(Gia_Man_t *pAig) {
    if (roots.size() == 0) {
        printf("[ERROR] Empty network\n");
        return;
    }

    std::vector<int> copy(_num_node_allocated, -1);
    copy[const0] = Gia_ManConst0Lit();
    for (const auto& node : sortedNodes) {
        // printf("node id %d: left %d right %d\n", node, getNode(node).left, getNode(node).right);
        if (getNode(node).left == -1 || getNode(node).right == -1) continue;

        int lhs = LitToId(getNode(node).left);
        bool is_lhs_const = (lhs == const0);
        bool is_lhs_complement = LitIsComplement(getNode(node).left);
        int rhs = LitToId(getNode(node).right);
        bool is_rhs_const = (rhs == const0);
        bool is_rhs_complement = LitIsComplement(getNode(node).right);
        // printf("lhs: %s%d rhs: %s%d\n", (is_lhs_complement) ? "~" : "", lhs, (is_rhs_complement) ? "~" : "", rhs);
        if (is_lhs_const && !is_lhs_complement && is_rhs_const && !is_rhs_complement) {
            copy[node] = Gia_ManConst0Lit();
        } else if (is_lhs_const && is_lhs_complement && is_rhs_const && is_rhs_complement) {
            copy[node] = Gia_ManConst1Lit();
        } else if (is_lhs_const && is_lhs_complement && is_rhs_const && !is_rhs_complement) {
            copy[node] = Gia_ManCiLit(pAig, getNode(node).decisionVariable);
        } else if (is_lhs_const && !is_lhs_complement && is_rhs_const && is_rhs_complement) {
            copy[node] = LitNot(Gia_ManCiLit(pAig, getNode(node).decisionVariable));
        } else if (!is_lhs_const && is_rhs_const && !is_rhs_complement) {
            copy[node] = Gia_ManHashAnd(pAig, Gia_ManCiLit(pAig, getNode(node).decisionVariable), LitNotCond(copy[lhs], is_lhs_complement));
        } else if (!is_rhs_const && is_lhs_const && !is_lhs_complement) {
            copy[node] = Gia_ManHashAnd(pAig, LitNot(Gia_ManCiLit(pAig, getNode(node).decisionVariable)), LitNotCond(copy[rhs], is_rhs_complement));
        } else if (is_lhs_const && is_lhs_complement && !is_rhs_const) {
            copy[node] = Gia_ManHashOr(pAig, Gia_ManCiLit(pAig, getNode(node).decisionVariable), LitNotCond(copy[rhs], is_rhs_complement));
        } else if (is_rhs_const && is_rhs_complement && !is_lhs_const) {
            copy[node] = Gia_ManHashOr(pAig, LitNot(Gia_ManCiLit(pAig, getNode(node).decisionVariable)), LitNotCond(copy[lhs], is_lhs_complement));
        } else {
            copy[node] = Gia_ManHashMux(pAig, Gia_ManCiLit(pAig, getNode(node).decisionVariable), LitNotCond(copy[lhs], is_lhs_complement), LitNotCond(copy[rhs], is_rhs_complement));
        }
    }

    for (const auto& i : irange(roots.size())) {
        int root_id = LitToId(roots[i]);
        bool is_complement = LitIsComplement(roots[i]);
        Gia_ManAppendCo(pAig, LitNotCond(copy[root_id], is_complement));
    }
}

} // namespace DecGraph2

/**Function*************************************************************

  Synopsis    [Converts the decision-graph bit order to ABC truth tables.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static std::vector<word> DecGraph2StandardTruth(const DecGraph2::TruthTable& tt) {
    std::vector<word> result(tt.nWords());
    for (int i = 0; i < tt.nWords(); ++i)
        result[i] = DecGraph2::reverseBits(tt.data()[i]);
    if (tt.nVars() < 6)
        result[0] = Abc_Tt6Stretch(result[0], tt.nVars());
    return result;
}

/**Function*************************************************************

  Synopsis    [Keeps fewer ANDs, breaking area ties by fewer levels.]

  Description [The caller transfers ownership of both managers.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t* DecGraph2KeepSmaller(Gia_Man_t* best, Gia_Man_t* candidate) {
    if (candidate == NULL)
        return best;
    if (Gia_ManAndNum(candidate) < Gia_ManAndNum(best) ||
        (Gia_ManAndNum(candidate) == Gia_ManAndNum(best) &&
         Gia_ManLevelNum(candidate) < Gia_ManLevelNum(best))) {
        ABC_FREE(candidate->pName);
        ABC_FREE(candidate->pSpec);
        candidate->pName = Abc_UtilStrsav(best->pName);
        candidate->pSpec = Abc_UtilStrsav(best->pSpec);
        Gia_ManSetRegNum(candidate, Gia_ManRegNum(best));
        Gia_ManStop(best);
        return candidate;
    }
    Gia_ManStop(candidate);
    return best;
}

#ifdef ABC_USE_CUDD

/**Function*************************************************************

  Synopsis    [Maps a shared BDD to AIG nodes, including unate muxes.]

  Description [If one cofactor implies the other, a two-AND realization
               replaces the general three-AND mux. Complemented BDD edges
               become complemented AIG literals.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int DecGraph2BddToGia(Gia_Man_t* p, DdManager* dd, DdNode* f,
    std::unordered_map<DdNode*, int>& memo, const std::vector<int>& inputs) {
    int phase = Cudd_IsComplement(f);
    f = Cudd_Regular(f);
    if (Cudd_IsConstant(f))
        return 1 ^ phase;
    auto entry = memo.find(f);
    if (entry != memo.end())
        return entry->second ^ phase;
    DdNode* t = Cudd_T(f);
    DdNode* e = Cudd_E(f);
    int a = DecGraph2BddToGia(p, dd, t, memo, inputs);
    int b = DecGraph2BddToGia(p, dd, e, memo, inputs);
    int c = inputs[Cudd_NodeReadIndex(f)];
    int result;
    if (Cudd_bddLeq(dd, e, t))
        result = Gia_ManHashOr(p, b, Gia_ManHashAnd(p, c, a));
    else if (Cudd_bddLeq(dd, t, e))
        result = Gia_ManHashOr(p, a, Gia_ManHashAnd(p, c ^ 1, b));
    else
        result = Gia_ManHashMux(p, c, a, b);
    memo[f] = result;
    return result ^ phase;
}

/**Function*************************************************************

  Synopsis    [Reconstructs the original inputs and outputs after reencoding.]

  Description [CUDD's linear transform uses XNOR, so a transformed input
               is one XOR the complemented original inputs in its row.
               Output operations are reversible XOR row operations and
               are undone in reverse order. Neither transform changes
               the external PI/PO ordering.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t* DecGraph2BddCandidate(DdManager* dd, std::vector<DdNode*>& roots,
    int nVars, const std::vector<std::pair<int, int>>& operations) {
    Gia_Man_t* p = Gia_ManStart(1000);
    p->pName = Abc_UtilStrsav((char*)"top");
    for (int i = 0; i < nVars; ++i)
        Gia_ManAppendCi(p);
    Gia_ManHashStart(p);
    std::vector<int> inputs(nVars), outputs;
    for (int i = 0; i < nVars; ++i) {
        inputs[i] = 1;
        for (int j = 0; j < nVars; ++j)
            if (Cudd_ReadLinear(dd, i, j))
                inputs[i] = Gia_ManHashXor(p, inputs[i], Gia_ManCiLit(p, nVars - 1 - j) ^ 1);
    }
    std::unordered_map<DdNode*, int> memo;
    for (DdNode* f : roots)
        outputs.push_back(DecGraph2BddToGia(p, dd, f, memo, inputs));
    for (auto op = operations.rbegin(); op != operations.rend(); ++op)
        outputs[op->first] = Gia_ManHashXor(p, outputs[op->first], outputs[op->second]);
    for (int lit : outputs)
        Gia_ManAppendCo(p, lit);
    Gia_ManHashStop(p);
    Gia_Man_t* result = Gia_ManCleanup(p);
    Gia_ManStop(p);
    return result;
}

/**Function*************************************************************

  Synopsis    [Counts distinct nonconstant BDD nodes outside an excluded set.]

  Description []

  SideEffects [Marks newly counted nodes in visited.]

  SeeAlso     []

***********************************************************************/
static int DecGraph2CountNodes(DdNode* f, std::unordered_set<DdNode*>& visited, const std::unordered_set<DdNode*>* excluded) {
    f = Cudd_Regular(f);
    if (Cudd_IsConstant(f) || (excluded && excluded->count(f)) || !visited.insert(f).second)
        return 0;
    return 1 + DecGraph2CountNodes(Cudd_T(f), visited, excluded) + DecGraph2CountNodes(Cudd_E(f), visited, excluded);
}

/**Function*************************************************************

  Synopsis    [Finds a shared output basis with smaller XOR residuals.]

  Description [Each step replaces output i by output i XOR output j.
               Measure the union of all BDD nodes, so sharing between
               outputs is counted once. Charge for the reconstruction
               XOR, and bound the number of greedy steps.]

  SideEffects [Updates referenced roots and records reversible operations.]

  SeeAlso     []

***********************************************************************/
static void DecGraph2OutputBasis(DdManager* dd, std::vector<DdNode*>& roots,
    std::vector<std::pair<int, int>>& operations, int fVerbose) {
    int nOuts = (int)roots.size();
    std::unordered_set<DdNode*> others, fresh;
    for (int round = 0; round < 32; ++round) {
        // Cost of a candidate set of roots is the number of distinct nonconstant
        // BDD nodes they share. For each replaced output, the nodes of the other
        // outputs are marked once; a candidate then adds only its unmarked nodes.
        others.clear();
        int oldCost = 0;
        for (int i = 0; i < nOuts; ++i)
            oldCost += DecGraph2CountNodes(roots[i], others, NULL);
        int bestCost = oldCost, bestI = -1, bestJ = -1;
        DdNode* bestFunction = NULL;
        for (int i = 0; i < nOuts; ++i) {
            others.clear();
            int otherCost = 0;
            for (int k = 0; k < nOuts; ++k)
                if (k != i)
                    otherCost += DecGraph2CountNodes(roots[k], others, NULL);
            for (int j = 0; j < nOuts; ++j) {
                if (i == j)
                    continue;
                DdNode* f = Cudd_bddXor(dd, roots[i], roots[j]);
                if (f == NULL) {
                    if (bestFunction)
                        Cudd_RecursiveDeref(dd, bestFunction);
                    return;
                }
                Cudd_Ref(f);
                fresh.clear();
                int cost = otherCost + DecGraph2CountNodes(f, fresh, &others) + 3;
                if (cost < bestCost) {
                    if (bestFunction)
                        Cudd_RecursiveDeref(dd, bestFunction);
                    bestFunction = f;
                    bestCost = cost;
                    bestI = i;
                    bestJ = j;
                } else
                    Cudd_RecursiveDeref(dd, f);
            }
        }
        if (bestI < 0)
            break;
        Cudd_RecursiveDeref(dd, roots[bestI]);
        roots[bestI] = bestFunction;
        operations.push_back(std::make_pair(bestI, bestJ));
        if (fVerbose)
            Abc_Print(1, "&dg2: output %d ^= output %d, shared BDD cost (nonconstant nodes + XOR charge) %d -> %d.\n",
                bestI, bestJ, oldCost, bestCost);
    }
}

/**Function*************************************************************

  Synopsis    [Tries shared input/output reencoding and AIG compression.]

  Description [The original fast result is retained unless a smaller
               candidate is found. Clean the smaller raw BDD candidate
               twice. Clean the other once unless it is over 25 percent
               larger than the best result already found. Every raw and
               intermediate result is eligible, with level-based area ties.]

  SideEffects [Takes ownership of best and returns the selected manager.]

  SeeAlso     []

***********************************************************************/
static Gia_Man_t* DecGraph2Improve(Gia_Man_t* best,
    std::vector<std::vector<word>>& truths, int fVerbose) {
    int nVars = Gia_ManCiNum(best);
    if (truths.empty() || nVars < 2 || Gia_ManAndNum(best) == 0)
        return best;
    DdManager* dd = Cudd_Init(nVars, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
    if (dd == NULL)
        return best;
    std::vector<DdNode*> roots;
    std::vector<std::pair<int, int>> operations;
    std::vector<unsigned> bddTruth(Abc_TruthWordNum(nVars));
    for (auto& truth : truths) {
        // KIT uses 32-bit words; avoid aliasing and native byte-order assumptions.
        for (size_t i = 0; i < bddTruth.size(); ++i)
            bddTruth[i] = (unsigned)(truth[i / 2] >> (32 * (i & 1)));
        DdNode* f = Kit_TruthToBdd(dd, bddTruth.data(), nVars, 1);
        if (f == NULL)
            break;
        Cudd_Ref(f);
        roots.push_back(f);
    }
    if (roots.size() == truths.size() && Cudd_ReduceHeap(dd, CUDD_REORDER_LINEAR, 0)) {
        // Compare both raw candidates before allocating cleanup effort.
        std::vector<Gia_Man_t*> candidates;
        for (int basis = 0; basis < 2; ++basis) {
            if (basis) {
                DecGraph2OutputBasis(dd, roots, operations, fVerbose);
                if (!Cudd_ReduceHeap(dd, CUDD_REORDER_SIFT, 0))
                    break;
            }
            candidates.push_back(DecGraph2BddCandidate(dd, roots, nVars, operations));
        }
        size_t smallest = 0;
        for (size_t i = 1; i < candidates.size(); ++i)
            if (Gia_ManAndNum(candidates[i]) < Gia_ManAndNum(candidates[smallest]))
                smallest = i;
        for (size_t step = 0; step < candidates.size(); ++step) {
            // Process the smallest first, then the remaining candidates in
            // their original order. The size margin trades some area for time;
            // it is a heuristic, not a bound on what dc3 could remove.
            const size_t i = step == 0 ? smallest : (step <= smallest ? step - 1 : step);
            const bool farLarger = uint64_t(Gia_ManAndNum(candidates[i])) * 4 >
                                  uint64_t(Gia_ManAndNum(best)) * 5;
            const int passes = i == smallest ? 2 : (farLarger ? 0 : 1);
            Gia_Man_t* work = candidates[i];
            for (int pass = 0; pass <= passes; ++pass) {
                if (fVerbose)
                    Abc_Print(1, "&dg2: %s, dc3 cleanup %d: %d ANDs.\n",
                        i ? "shared output basis" : "shared input basis", pass, Gia_ManAndNum(work));
                Gia_Man_t* next = pass < passes ? Gia_ManDc3(work, 0, 0) : NULL;
                best = DecGraph2KeepSmaller(best, work);
                work = next;
                if (work == NULL)
                    break;
            }
        }
    }
    for (DdNode* f : roots)
        Cudd_RecursiveDeref(dd, f);
    Cudd_Quit(dd);
    return best;
}
#endif

/**Function*************************************************************

  Synopsis    [Learns a shared decision graph from the current GIA.]

  Description [Quality mode also tries reversible input/output bases.]

  SideEffects []

  SeeAlso     [Gia_ManDecGraph2FromFile]

***********************************************************************/
Gia_Man_t* Gia_ManDecGraph2(Gia_Man_t* p, int fQuality, int fVerbose) {
    int nIns = Gia_ManCiNum(p);
    int nOuts = Gia_ManCoNum(p);
    Gia_Man_t* pNew;
    Gia_Obj_t* pObj;
    word v;
    word* pTruth;
    int i, k;
    if (Gia_ManRegNum(p)) {
        Abc_Print(-1, "&dg2 requires a combinational GIA.\n");
        return NULL;
    }
    if (nIns > 16) {
        Abc_Print(-1, "&dg2 supports at most 16 inputs.\n");
        return NULL;
    }
    if (nOuts == 0)
        return Gia_ManDup(p);
    pNew = Gia_ManStart(Gia_ManObjNum(p));
    pNew->pName = Abc_UtilStrsav(p->pName);
    pNew->pSpec = Abc_UtilStrsav(p->pSpec);
    Gia_ManForEachCi(p, pObj, k)
        Gia_ManAppendCi(pNew);
    if (p->vTtMemory)
        Gia_ObjComputeTruthTableStop(p);
    Gia_ObjComputeTruthTableStart(p, nIns);
    Gia_ManHashStart(pNew);
    DecGraph2::DecisionDiagram dd;
    std::vector<std::vector<word>> truths;
    for (k = 0; k < nOuts; k++) {
        DecGraph2::TruthTable tt;
        tt.create(uint64_t(1) << nIns);
        int num_words = tt.nWords();
        pObj = Gia_ManCo(p, k);
        pTruth = Gia_ObjComputeTruthTable(p, Gia_ObjFanin0(pObj));
        if (nIns >= 6) {
            for (i = num_words - 1; i >= 0; --i) {
                tt.data()[i] = Gia_ObjFaninC0(pObj) ? ~DecGraph2::reverseBits(pTruth[i]) : DecGraph2::reverseBits(pTruth[i]);
            }
        } else {
            v = DecGraph2::reverseBits((Gia_ObjFaninC0(pObj) ? ~pTruth[0] : pTruth[0]) & DecGraph2::ones_mask[nIns]);
            tt.data()[0] = v;
        }
        if (fQuality)
            truths.push_back(DecGraph2StandardTruth(tt));
        dd.addOutput(tt);
    }
    dd.build();
    dd.buildAig(pNew);
    Gia_ObjComputeTruthTableStop(p);
    Gia_ManHashStop(pNew);
    Gia_ManSetRegNum(pNew, Gia_ManRegNum(p));
#ifdef ABC_USE_CUDD
    if (fQuality)
        pNew = DecGraph2Improve(pNew, truths, fVerbose);
#endif
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Learns a shared decision graph from IWLS truth tables.]

  Description [Validates the input before constructing the new GIA.]

  SideEffects []

  SeeAlso     [Gia_ManDecGraph2]

***********************************************************************/
Gia_Man_t* Gia_ManDecGraph2FromFile(char* pFileName, int fQuality, int fVerbose) {
    char* pBuffer = Extra_FileReadContents(pFileName);
    if (pBuffer == NULL)
        return NULL;
    char *table = strtok(pBuffer, " \r\n\t|");
    DecGraph2::DecisionDiagram dd;
    std::vector<std::vector<word>> truths;
    size_t nBits = 0;
    while (table) {
        size_t length = strlen(table);
        if (length == 0 || length > 65536 || (length & (length - 1)) || (nBits && length != nBits)) {
            Abc_Print(-1, "&dg2 requires equal, power-of-two table lengths of at most 65536 bits.\n");
            ABC_FREE(pBuffer);
            return NULL;
        }
        for (size_t i = 0; i < length; ++i)
            if (table[i] != '0' && table[i] != '1') {
                Abc_Print(-1, "&dg2: invalid character in truth-table input.\n");
                ABC_FREE(pBuffer);
                return NULL;
            }
        nBits = length;
        DecGraph2::TruthTable tt;
        tt.readBinaryReverse(table);
        if (fQuality)
            truths.push_back(DecGraph2StandardTruth(tt));
        dd.addOutput(tt);
        table = strtok(NULL, " \r\n\t|");
    }
    ABC_FREE(pBuffer);
    if (nBits == 0) {
        Abc_Print(-1, "&dg2: the truth-table file is empty.\n");
        return NULL;
    }
    dd.build();
    Gia_Man_t* pNew = Gia_ManStart(dd.nNodeAllocated());
    pNew->pName = Abc_UtilStrsav((char *)"top");
    for (int i = 0; i < dd.nVars(); ++i)
        Gia_ManAppendCi(pNew);
    Gia_ManHashStart(pNew);
    dd.buildAig(pNew);
    Gia_ManHashStop(pNew);
#ifdef ABC_USE_CUDD
    if (fQuality)
        pNew = DecGraph2Improve(pNew, truths, fVerbose);
#endif
    return pNew;
}

ABC_NAMESPACE_IMPL_END
