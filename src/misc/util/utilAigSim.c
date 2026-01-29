/**CFile****************************************************************

  FileName    [utilAigSim.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [AIG simulation.]

  Synopsis    [AIG simulation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - Feburary 13, 2011.]

  Revision    [$Id: utilAigSim.c,v 1.00 2011/02/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>
#include <ctype.h>
#include <time.h>
#ifdef _WIN32
#include <io.h>
#define mkstemp(p) _mktemp_s(p, strlen(p)+1)
#else
#include <unistd.h>   // mkstemp(), close(), unlink()
#include <fcntl.h>
#include <sys/stat.h>
#endif

#ifdef _WIN32
// Windows doesn't have __builtin_ctzll, implement it using portable algorithm
static inline int __builtin_ctzll(uint64_t x) {
    if (x == 0) return 64;
    unsigned int n = 0;
    if ((x & 0xFFFFFFFFULL) == 0) {
        n += 32;
        x >>= 32;
    }
    if ((x & 0xFFFFULL) == 0) {
        n += 16;
        x >>= 16;
    }
    if ((x & 0xFFULL) == 0) {
        n += 8;
        x >>= 8;
    }
    if ((x & 0xFULL) == 0) {
        n += 4;
        x >>= 4;
    }
    if ((x & 0x3ULL) == 0) {
        n += 2;
        x >>= 2;
    }
    if ((x & 0x1ULL) == 0) {
        n += 1;
    }
    return n;
}
#endif

#define AIGSIM_LIBRARY_ONLY

#ifdef AIGSIM_LIBRARY_ONLY
#include "misc/util/abc_namespaces.h"
ABC_NAMESPACE_IMPL_START
#endif


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define ABC_ALLOC(type, n)   ((type*)malloc((size_t)(n) * sizeof(type)))
#define ABC_CALLOC(type, n)  ((type*)calloc((size_t)(n), sizeof(type)))
#define ABC_FREE(p)          do { free(p); (p) = NULL; } while (0)

typedef struct AigNode_ { uint32_t f0, f1; } AigNode;
typedef struct AigMan_ {
    AigNode *nodes;
    int nObjs, nCis, nAnds, nCos;
} AigMan;

static inline int  Aig_LitId(uint32_t lit)    { return (int)(lit >> 1); }
static inline int  Aig_LitCompl(uint32_t lit) { return (int)(lit & 1u); }
static inline uint32_t Aig_Lit(int id, int c) { return ((uint32_t)id << 1) | (uint32_t)(c & 1); }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

static AigMan* Aig_ManStartCompact(int nCis, int nAnds, int nCos) {
    AigMan *p = ABC_CALLOC(AigMan, 1);
    p->nCis = nCis; p->nAnds = nAnds; p->nCos = nCos;
    p->nObjs = 1 + nCis + nAnds + nCos;
    p->nodes = ABC_CALLOC(AigNode, p->nObjs);
    return p;
}
static void Aig_ManStop(AigMan *p) { ABC_FREE(p->nodes); ABC_FREE(p); }

/* ---------------------- AIGER binary loader ----------------------- */
/* Simple combinational (.aig) reader: header + O ASCII lines + A delta-encoded ANDs */

static int read_line(FILE *f, char *buf, size_t cap) {
    if (!fgets(buf, (int)cap, f)) return 0;
    size_t n = strlen(buf);
    while (n && (buf[n-1] == '\n' || buf[n-1] == '\r')) buf[--n] = 0;
    return 1;
}
static int parse_header(const char *s, unsigned *M, unsigned *I, unsigned *L, unsigned *O, unsigned *A) {
    if (strncmp(s, "aig ", 4) != 0) return 0;
    const char *p = s + 4;
    *M = (unsigned)strtoul(p, (char**)&p, 10);
    *I = (unsigned)strtoul(p, (char**)&p, 10);
    *L = (unsigned)strtoul(p, (char**)&p, 10);
    *O = (unsigned)strtoul(p, (char**)&p, 10);
    *A = (unsigned)strtoul(p, (char**)&p, 10);
    return 1;
}
static int read_ascii_uint_line(FILE *f, unsigned *out) {
    char buf[128]; if (!read_line(f, buf, sizeof(buf))) return 0;
    char *p = buf; while (*p && isspace((unsigned char)*p)) p++;
    *out = (unsigned)strtoul(p, NULL, 10);
    return 1;
}
static int read_uleb128(FILE *f, unsigned *out) {
    unsigned x = 0, shift = 0;
    for (;;) {
        int ch = fgetc(f); if (ch == EOF) return 0;
        x |= ((unsigned)(ch & 0x7F)) << shift;
        if (!(ch & 0x80)) break;
        shift += 7; if (shift > 28) return 0;
    }
    *out = x; return 1;
}
static AigMan* Aig_ManLoadAigerBinary(const char *filename, int verbose) {
    FILE *f = fopen(filename, "rb");
    if (!f) { fprintf(stderr, "Error: cannot open '%s'\n", filename); return NULL; }
    char hdr[256];
    if (!read_line(f, hdr, sizeof(hdr))) { fprintf(stderr, "Error: cannot read header\n"); fclose(f); return NULL; }
    unsigned M=0,I=0,L=0,O=0,A=0;
    if (!parse_header(hdr, &M,&I,&L,&O,&A)) { fprintf(stderr, "Error: bad header: %s\n", hdr); fclose(f); return NULL; }
    if (verbose) printf("[aiger] %s : M=%u I=%u L=%u O=%u A=%u\n", filename, M,I,L,O,A);
    if (L != 0) { fprintf(stderr, "Error: latches (L=%u) not supported.\n", L); fclose(f); return NULL; }

    unsigned *outs = ABC_ALLOC(unsigned, O);
    for (unsigned i = 0; i < O; i++) if (!read_ascii_uint_line(f, &outs[i])) {
        fprintf(stderr, "Error: cannot read output literal %u\n", i); ABC_FREE(outs); fclose(f); return NULL;
    }

    AigMan *p = Aig_ManStartCompact((int)I, (int)A, (int)O);

    for (unsigned k = 0; k < A; k++) {
        unsigned lhs_var = I + k + 1;
        unsigned lhs_lit = lhs_var << 1;
        unsigned d1=0, d2=0;
        if (!read_uleb128(f, &d1) || !read_uleb128(f, &d2)) {
            fprintf(stderr, "Error: cannot decode AND gate %u\n", k);
            ABC_FREE(outs); Aig_ManStop(p); fclose(f); return NULL;
        }
        unsigned rhs0 = lhs_lit - d1;
        unsigned rhs1 = rhs0   - d2;
        p->nodes[(int)lhs_var].f0 = (uint32_t)rhs0;
        p->nodes[(int)lhs_var].f1 = (uint32_t)rhs1;
    }

    for (unsigned i = 0; i < O; i++) {
        int id = p->nCis + p->nAnds + 1 + (int)i; // CO objects at the end
        p->nodes[id].f0 = (uint32_t)outs[i];
    }

    ABC_FREE(outs);
    fclose(f);
    return p;
}

/* ---------------------- sim helpers ---------------------- */

static inline uint64_t u64_mask_n(int nBits) {
    return (nBits >= 64) ? ~0ull : ((nBits <= 0) ? 0ull : ((1ull << nBits) - 1ull));
}

#ifdef _WIN32
// Windows doesn't support __int128, so we limit to 32 variables on Windows
static void u128_to_dec(uint64_t x, char *buf, size_t cap) {
    char tmp[64]; int n = 0;
    if (!x) { snprintf(buf, cap, "0"); return; }
    while (x && n < (int)sizeof(tmp)) { tmp[n++] = (char)('0' + (unsigned)(x % 10)); x /= 10; }
    int k = 0; while (n && k + 1 < (int)cap) buf[k++] = tmp[--n];
    buf[k] = 0;
}
#else
static void u128_to_dec(unsigned __int128 x, char *buf, size_t cap) {
    char tmp[64]; int n = 0;
    if (!x) { snprintf(buf, cap, "0"); return; }
    while (x && n < (int)sizeof(tmp)) { tmp[n++] = (char)('0' + (unsigned)(x % 10)); x /= 10; }
    int k = 0; while (n && k + 1 < (int)cap) buf[k++] = tmp[--n];
    buf[k] = 0;
}
#endif

enum { NW = 64, BATCH = NW * 64 }; // 4096 patterns/round

static inline uint64_t SimLit(const uint64_t *S, uint32_t lit, int w) {
    uint64_t v = S[(size_t)Aig_LitId(lit) * NW + (size_t)w];
    return Aig_LitCompl(lit) ? ~v : v;
}

static inline void SimulateOne(const AigMan *p, uint64_t *S) {
    const int firstAnd = p->nCis + 1;
    const int lastAnd  = p->nCis + p->nAnds;
    for (int id = firstAnd; id <= lastAnd; ++id) {
        uint32_t f0 = p->nodes[id].f0, f1 = p->nodes[id].f1;
        size_t off = (size_t)id * NW;
        for (int w = 0; w < NW; ++w)
            S[off + (size_t)w] = SimLit(S, f0, w) & SimLit(S, f1, w);
    }
}

/* ---------------------- mask string parser ---------------------- */
/* maskStr grammar: sequence of tokens N or (N)
     N   : N individual bits (each enumerated independently)
    (N)  : N bits grouped together (enumerated as all-0 or all-1)
   Total widths must sum to nCis.
   Output: varMasks[0..nVars-1] (each is a bitmask of input bits controlled by that var).
*/

static void PrintMaskSegmentsOneLine(const char *maskStr,
                                    const int *segS, const int *segW, const int *segG, int nSeg,
                                    int nVars, int nCis)
{
    char buf[1024];
    int n = 0;
    n += snprintf(buf + n, sizeof(buf) - (size_t)n, "[mask] \"%s\" segs:", maskStr ? maskStr : "");
    for (int i = 0; i < nSeg; ++i) {
        int s = segS[i], e = s + segW[i] - 1;
        if (segG[i]) n += snprintf(buf + n, sizeof(buf) - (size_t)n, " (%d-%d)", s, e);
        else         n += snprintf(buf + n, sizeof(buf) - (size_t)n, " %d-%d",  s, e);
    }
    n += snprintf(buf + n, sizeof(buf) - (size_t)n, "  vars=%d nCis=%d", nVars, nCis);
    printf("%s\n", buf);
}

static int ParseMaskString(const char *maskStr, int nCis, uint64_t *varMasks, int *pnVars, int verbose) {
    if (!maskStr || !*maskStr) {
        for (int i = 0; i < nCis; ++i) varMasks[i] = 1ull << i;
        *pnVars = nCis;
        if (verbose) {
             int segS[1] = {0};
             int segW[1] = {nCis};
             int segG[1] = {0};
             PrintMaskSegmentsOneLine("default", segS, segW, segG, 1, *pnVars, nCis);
        }
        return 1;
    }

    // For printing segments: each token becomes one segment
    int segS[128], segW[128], segG[128], nSeg = 0;

    const char *p = maskStr;
    int off = 0, nVars = 0;

    while (*p) {
        while (*p && isspace((unsigned char)*p)) p++;
        if (!*p) break;

        int grouped = 0;
        if (*p == '(') { grouped = 1; p++; while (*p && isspace((unsigned char)*p)) p++; }

        if (!isdigit((unsigned char)*p)) {
            fprintf(stderr, "Error: bad mask near '%s'\n", p);
            return 0;
        }

        char *end = NULL;
        long w = strtol(p, &end, 10);
        if (w <= 0 || w > 64) {
            fprintf(stderr, "Error: bad width %ld in mask\n", w);
            return 0;
        }
        p = end;

        while (*p && isspace((unsigned char)*p)) p++;
        if (grouped) {
            if (*p != ')') { fprintf(stderr, "Error: missing ')' in mask\n"); return 0; }
            p++;
        }

        if (off + (int)w > nCis) {
            fprintf(stderr, "Error: mask widths exceed nCis (%d)\n", nCis);
            return 0;
        }

        segS[nSeg] = off;
        segW[nSeg] = (int)w;
        segG[nSeg] = grouped;
        nSeg++;

        if (grouped) {
            uint64_t m = ((w == 64) ? ~0ull : (((1ull << (unsigned)w) - 1ull) << (unsigned)off));
            if (nVars >= 64) { fprintf(stderr, "Error: too many vars in mask\n"); return 0; }
            varMasks[nVars++] = m;
        } else {
            for (int t = 0; t < (int)w; ++t) {
                if (nVars >= 64) { fprintf(stderr, "Error: too many vars in mask\n"); return 0; }
                varMasks[nVars++] = 1ull << (unsigned)(off + t);
            }
        }
        off += (int)w;
    }

    if (off != nCis) {
        fprintf(stderr, "Error: mask widths sum to %d but nCis=%d\n", off, nCis);
        return 0;
    }

    *pnVars = nVars;
    if (verbose) PrintMaskSegmentsOneLine(maskStr, segS, segW, segG, nSeg, nVars, nCis);
    return 1;
}

/* ---------------------- file/binary helpers ---------------------- */

static int ends_with(const char *s, const char *suf) {
    size_t ns = strlen(s), nf = strlen(suf);
    return (ns >= nf) && !strcmp(s + (ns - nf), suf);
}

static int make_tmp_file(char *path, size_t cap, const char *prefix) {
    // Creates an existing temp file (for input)
#if defined(__wasm)
    static int seq = 0; // no risk of collision since we're in a sandbox
    snprintf(path, cap, "%s%08d", prefix, seq++);
    int fd = open(path, O_CREAT | O_EXCL | O_RDWR, S_IREAD | S_IWRITE);
#else
    snprintf(path, cap, "/tmp/%sXXXXXX", prefix);
    int fd = mkstemp(path);
#endif
    if (fd < 0) return 0;
    close(fd);
    return 1;
}

static int make_tmp_path_noexist(char *path, size_t cap, const char *prefix) {
    // Creates a unique temp path that does not exist (for output)
#if defined(__wasm)
    static int seq = 0; // no risk of collision since we're in a sandbox
    snprintf(path, cap, "%s%08d", prefix, seq++);
    int fd = open(path, O_CREAT | O_EXCL | O_RDWR, S_IREAD | S_IWRITE);
#else
    snprintf(path, cap, "/tmp/%sXXXXXX", prefix);
    int fd = mkstemp(path);
#endif
    if (fd < 0) return 0;
    close(fd);
    unlink(path);
    return 1;
}

static int write_words(const char *fname, const uint64_t *data, size_t nWords) {
    FILE *f = fopen(fname, "wb");
    if (!f) return 0;
    size_t wr = fwrite(data, sizeof(uint64_t), nWords, f);
    fclose(f);
    return wr == nWords;
}

static int read_words(const char *fname, uint64_t *data, size_t nWords) {
    FILE *f = fopen(fname, "rb");
    if (!f) return 0;
    size_t rd = fread(data, sizeof(uint64_t), nWords, f);
    fclose(f);
    return rd == nWords;
}

/* ---------------------- compare: AIG vs AIG ---------------------- */

static int SimulateCompareAigAig(const AigMan *p1, const AigMan *p2,
                                 const uint64_t *varMasks, int nVars, int verbose)
{
    if (p1->nCis != p2->nCis || p1->nCos != p2->nCos) {
        fprintf(stderr, "Error: interface mismatch: (I,O)=(%d,%d) vs (%d,%d)\n",
                p1->nCis, p1->nCos, p2->nCis, p2->nCos);
        return 0;
    }
    if (p1->nCis > 64 || p1->nCos > 64) {
        fprintf(stderr, "Error: supports nCis<=64 and nCos<=64 (got I=%d O=%d)\n", p1->nCis, p1->nCos);
        return 0;
    }

    const uint64_t inMask  = u64_mask_n(p1->nCis);
    const uint64_t outMask = u64_mask_n(p1->nCos);
#ifdef _WIN32
    // Windows doesn't support __int128, limit to 32 variables
    if (nVars > 32) {
        fprintf(stderr, "Error: Windows build supports nVars<=32 (got nVars=%d)\n", nVars);
        return 0;
    }
    const uint64_t combs = ((uint64_t)1) << (unsigned)nVars;
#else
    const unsigned __int128 combs = ((unsigned __int128)1) << (unsigned)nVars;
#endif

    uint32_t *co1 = ABC_ALLOC(uint32_t, p1->nCos);
    uint32_t *co2 = ABC_ALLOC(uint32_t, p2->nCos);
    for (int o = 0; o < p1->nCos; ++o) {
        co1[o] = p1->nodes[p1->nCis + p1->nAnds + 1 + o].f0;
        co2[o] = p2->nodes[p2->nCis + p2->nAnds + 1 + o].f0;
    }

    uint64_t *S1 = ABC_CALLOC(uint64_t, (size_t)p1->nObjs * NW);
    uint64_t *S2 = ABC_CALLOC(uint64_t, (size_t)p2->nObjs * NW);

    uint64_t inVec[BATCH], valid[NW];
    unsigned long long rounds = 0;
#ifdef _WIN32
    uint64_t patsDone = 0;
#else
    unsigned __int128 patsDone = 0;
#endif

    clock_t t0 = clock();

#ifdef _WIN32
    for (uint64_t base = 0; base < combs; base += BATCH) {
        uint64_t remain = combs - base;
#else
    for (unsigned __int128 base = 0; base < combs; base += BATCH) {
        unsigned __int128 remain = combs - base;
#endif
        int nThis = (remain < BATCH) ? (int)remain : BATCH;

        int left = nThis;
        for (int w = 0; w < NW; ++w) {
            if (left >= 64) { valid[w] = ~0ull; left -= 64; }
            else if (left > 0) { valid[w] = ((left == 64) ? ~0ull : ((1ull << left) - 1ull)); left = 0; }
            else valid[w] = 0ull;
        }

        // Clear CI words in both sims
        for (int i = 0; i < p1->nCis; ++i) {
            size_t off1 = (size_t)(1 + i) * NW;
            size_t off2 = (size_t)(1 + i) * NW;
            for (int w = 0; w < NW; ++w) S1[off1 + (size_t)w] = 0ull, S2[off2 + (size_t)w] = 0ull;
        }

        // Fill CIs
        for (int ptn = 0; ptn < nThis; ++ptn) {
            uint64_t idx = (uint64_t)(base + (unsigned)ptn);
            uint64_t in = 0;
            for (int j = 0; j < nVars; ++j) if ((idx >> j) & 1ull) in |= varMasks[j];
            in &= inMask;
            inVec[ptn] = in;

            int w = ptn >> 6;
            uint64_t bit = 1ull << (ptn & 63);
            uint64_t x = in;
            while (x) {
                int i = __builtin_ctzll(x);
                x &= x - 1;
                S1[(size_t)(1 + i) * NW + (size_t)w] |= bit;
                S2[(size_t)(1 + i) * NW + (size_t)w] |= bit;
            }
        }

        // Simulate AIG #1 then AIG #2
        SimulateOne(p1, S1);
        SimulateOne(p2, S2);

        // Compare COs
        for (int o = 0; o < p1->nCos; ++o) {
            for (int w = 0; w < NW; ++w) {
                uint64_t y1 = SimLit(S1, co1[o], w);
                uint64_t y2 = SimLit(S2, co2[o], w);
                uint64_t diff = (y1 ^ y2) & valid[w];
                if (!diff) continue;

                int bit = __builtin_ctzll(diff);
                int ptn = (w << 6) | bit;

                uint64_t out1 = 0, out2 = 0;
                for (int oo = 0; oo < p1->nCos; ++oo) {
                    out1 |= ((SimLit(S1, co1[oo], w) >> bit) & 1ull) << oo;
                    out2 |= ((SimLit(S2, co2[oo], w) >> bit) & 1ull) << oo;
                }

                int inHex  = (p1->nCis + 3) / 4;
                int outHex = (p1->nCos + 3) / 4;
                char gbuf[64]; u128_to_dec(patsDone + (unsigned)ptn, gbuf, sizeof(gbuf));

                printf("FAIL pattern=%s out_bit=%d\n", gbuf, o);
                printf("  in  = 0x%0*llx\n", inHex,  (unsigned long long)(inVec[ptn] & inMask));
                printf("  y1  = 0x%0*llx\n", outHex, (unsigned long long)(out1 & outMask));
                printf("  y2  = 0x%0*llx\n", outHex, (unsigned long long)(out2 & outMask));

                ABC_FREE(S1); ABC_FREE(S2); ABC_FREE(co1); ABC_FREE(co2);
                return 0;
            }
        }

        rounds++;
        patsDone += (unsigned)nThis;
        if (verbose && (rounds % 256ull) == 0ull) {
            char buf[64]; u128_to_dec(patsDone, buf, sizeof(buf));
            printf("[sim] rounds=%llu patterns=%s\n", rounds, buf);
        }
    }

    clock_t t1 = clock();
    double sec = (double)(t1 - t0) / (double)CLOCKS_PER_SEC;

    char totBuf[64]; u128_to_dec(combs, totBuf, sizeof(totBuf));
    printf("OK patterns=%s rounds=%llu time=%.3fs\n", totBuf, rounds, sec);

    ABC_FREE(S1); ABC_FREE(S2); ABC_FREE(co1); ABC_FREE(co2);
    return 1;
}

/* ---------------------- compare: AIG vs external binary ---------------------- */

static int SimulateCompareAigBin(const AigMan *p1, const char *bin,
                                 const uint64_t *varMasks, int nVars, int verbose)
{
    if (p1->nCis > 64 || p1->nCos > 64) {
        fprintf(stderr, "Error: supports nCis<=64 and nCos<=64 (got I=%d O=%d)\n", p1->nCis, p1->nCos);
        return 0;
    }

    const uint64_t inMask  = u64_mask_n(p1->nCis);
    const uint64_t outMask = u64_mask_n(p1->nCos);
#ifdef _WIN32
    // Windows doesn't support __int128, limit to 32 variables
    if (nVars > 32) {
        fprintf(stderr, "Error: Windows build supports nVars<=32 (got nVars=%d)\n", nVars);
        return 0;
    }
    const uint64_t combs = ((uint64_t)1) << (unsigned)nVars;
#else
    const unsigned __int128 combs = ((unsigned __int128)1) << (unsigned)nVars;
#endif

    // Precompute AIG CO literals
    uint32_t *co1 = ABC_ALLOC(uint32_t, p1->nCos);
    for (int o = 0; o < p1->nCos; ++o)
        co1[o] = p1->nodes[p1->nCis + p1->nAnds + 1 + o].f0;

    uint64_t *S1 = ABC_CALLOC(uint64_t, (size_t)p1->nObjs * NW);
    uint64_t *out2 = ABC_ALLOC(uint64_t, (size_t)p1->nCos * NW);

    // Temp IO files for the binary
    char inFile[128], outFile[128], cmd[512];
    if (!make_tmp_file(inFile, sizeof(inFile), "aigsim_in_") ||
        !make_tmp_path_noexist(outFile, sizeof(outFile), "aigsim_out_")) {
        fprintf(stderr, "Error: cannot create temp files\n");
        ABC_FREE(S1); ABC_FREE(co1); ABC_FREE(out2);
        return 0;
    }

    uint64_t inVec[BATCH], valid[NW];
    unsigned long long rounds = 0;
#ifdef _WIN32
    uint64_t patsDone = 0;
#else
    unsigned __int128 patsDone = 0;
#endif

    clock_t t0 = clock();

#ifdef _WIN32
    for (uint64_t base = 0; base < combs; base += BATCH) {
        uint64_t remain = combs - base;
#else
    for (unsigned __int128 base = 0; base < combs; base += BATCH) {
        unsigned __int128 remain = combs - base;
#endif
        int nThis = (remain < BATCH) ? (int)remain : BATCH;

        int left = nThis;
        for (int w = 0; w < NW; ++w) {
            if (left >= 64) { valid[w] = ~0ull; left -= 64; }
            else if (left > 0) { valid[w] = ((left == 64) ? ~0ull : ((1ull << left) - 1ull)); left = 0; }
            else valid[w] = 0ull;
        }

        // Clear CI words
        for (int i = 0; i < p1->nCis; ++i) {
            size_t off = (size_t)(1 + i) * NW;
            for (int w = 0; w < NW; ++w) S1[off + (size_t)w] = 0ull;
        }

        // Fill CIs for this batch
        for (int ptn = 0; ptn < nThis; ++ptn) {
            uint64_t idx = (uint64_t)(base + (unsigned)ptn);
            uint64_t in = 0;
            for (int j = 0; j < nVars; ++j) if ((idx >> j) & 1ull) in |= varMasks[j];
            in &= inMask;
            inVec[ptn] = in;

            int w = ptn >> 6;
            uint64_t bit = 1ull << (ptn & 63);

            uint64_t x = in;
            while (x) {
                int i = __builtin_ctzll(x);
                x &= x - 1;
                S1[(size_t)(1 + i) * NW + (size_t)w] |= bit;
            }
        }

        // Simulate AIG
        SimulateOne(p1, S1);

        // Write input sim-info file: nCis * NW words, CI major, word minor
        if (!write_words(inFile, &S1[1 * NW], (size_t)p1->nCis * NW)) {
            fprintf(stderr, "Error: cannot write %s\n", inFile);
            goto fail;
        }

        // Run external binary: "<bin> <inFile> <outFile>"
        remove(outFile);
        snprintf(cmd, sizeof(cmd), "%s %s %s", bin, inFile, outFile);
#if defined(__wasm)
        int rc = -1;
#else
        int rc = system(cmd);
#endif
        if (rc != 0) {
            fprintf(stderr, "Error: system() failed (rc=%d): %s\n", rc, cmd);
            goto fail;
        }

        // Read output sim-info file: nCos * NW words
        if (!read_words(outFile, out2, (size_t)p1->nCos * NW)) {
            fprintf(stderr, "Error: cannot read %s (expected %d*%d words)\n", outFile, p1->nCos, NW);
            goto fail;
        }

        // Compare AIG outputs vs binary outputs
        for (int o = 0; o < p1->nCos; ++o) {
            for (int w = 0; w < NW; ++w) {
                uint64_t y1 = SimLit(S1, co1[o], w);
                uint64_t y2 = out2[(size_t)o * NW + (size_t)w];
                uint64_t diff = (y1 ^ y2) & valid[w];
                if (!diff) continue;

                int bit = __builtin_ctzll(diff);
                int ptn = (w << 6) | bit;

                uint64_t out1 = 0, outB = 0;
                for (int oo = 0; oo < p1->nCos; ++oo) {
                    out1 |= ((SimLit(S1, co1[oo], w) >> bit) & 1ull) << oo;
                    outB |= ((out2[(size_t)oo * NW + (size_t)w] >> bit) & 1ull) << oo;
                }

                int inHex  = (p1->nCis + 3) / 4;
                int outHex = (p1->nCos + 3) / 4;
                char gbuf[64]; u128_to_dec(patsDone + (unsigned)ptn, gbuf, sizeof(gbuf));

                printf("FAIL pattern=%s out_bit=%d\n", gbuf, o);
                printf("  in   = 0x%0*llx\n", inHex,  (unsigned long long)(inVec[ptn] & inMask));
                printf("  aig  = 0x%0*llx\n", outHex, (unsigned long long)(out1 & outMask));
                printf("  bin  = 0x%0*llx\n", outHex, (unsigned long long)(outB & outMask));
                goto fail;
            }
        }

        rounds++;
        patsDone += (unsigned)nThis;
        if (verbose && (rounds % 256ull) == 0ull) {
            char buf[64]; u128_to_dec(patsDone, buf, sizeof(buf));
            printf("[sim] rounds=%llu patterns=%s\n", rounds, buf);
        }
    }

    {
        clock_t t1 = clock();
        double sec = (double)(t1 - t0) / (double)CLOCKS_PER_SEC;
        char totBuf[64]; u128_to_dec(combs, totBuf, sizeof(totBuf));
        printf("OK patterns=%s rounds=%llu time=%.3fs\n", totBuf, rounds, sec);
    }

    remove(inFile);
    remove(outFile);
    ABC_FREE(S1); ABC_FREE(co1); ABC_FREE(out2);
    return 1;

fail:
    remove(inFile);
    remove(outFile);
    ABC_FREE(S1); ABC_FREE(co1); ABC_FREE(out2);
    return 0;
}

/* ---------------------- top API ---------------------- */

int SimulateAigTop( char *fname1, char *fname2, char *mask, int verbose )
{
    AigMan *p1 = Aig_ManLoadAigerBinary(fname1, verbose);
    if (!p1) return 2;

    uint64_t varMasks[64];
    int nVars = 0;
    if (!ParseMaskString(mask, p1->nCis, varMasks, &nVars, verbose)) {
        Aig_ManStop(p1);
        return 2;
    }

    int ok = 0;

    if (ends_with(fname2, ".aig")) {
        AigMan *p2 = Aig_ManLoadAigerBinary(fname2, verbose);
        if (!p2) { Aig_ManStop(p1); return 2; }
        ok = SimulateCompareAigAig(p1, p2, varMasks, nVars, verbose);
        Aig_ManStop(p2);
    } else {
        // fname2 is an external binary: bin <inFile> <outFile>
        ok = SimulateCompareAigBin(p1, fname2, varMasks, nVars, verbose);
    }

    Aig_ManStop(p1);
    return ok ? 0 : 3;
}

/* ---------------------- main ---------------------- */
/* Usage:
     ./aig_equiv_2aigs [-v] file1.aig file2.aig_or_binary [mask_str]

   mask_str example for 16 inputs:
     "2(4)10" -> 2 individual bits, then 4 grouped bits (all-0/all-1), then 10 individual bits
*/
#ifndef AIGSIM_LIBRARY_ONLY
int main(int argc, char **argv) {
    int verbose = 0;
    const char *f1 = NULL, *f2 = NULL;
    const char *mask = NULL;

    int ai = 1;
    if (ai < argc && !strcmp(argv[ai], "-v")) { verbose = 1; ai++; }
    if (ai + 1 >= argc) {
        fprintf(stderr, "Usage: %s [-v] file1.aig file2.aig_or_binary [mask_str]\n", argv[0]);
        return 1;
    }
    f1 = argv[ai++];
    f2 = argv[ai++];
    if (ai < argc) mask = argv[ai++];

    return SimulateAigTop((char*)f1, (char*)f2, (char*)mask, verbose);
}
#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

#ifdef AIGSIM_LIBRARY_ONLY
ABC_NAMESPACE_IMPL_END
#endif


