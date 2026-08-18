// Regression tests for per-object origin tracking (vOrigins).
//
// Covers the core infrastructure (set/get/add/dedup/inline->overflow
// promotion/union/cap), propagation through Gia_ManDup, the AIGER "y"
// extension write/read round-trip, and preservation through the &nf
// standard-cell mapper (which maps in place and is therefore expected to
// preserve origins without dedicated propagation code).

#include "gtest/gtest.h"

#include "aig/gia/gia.h"
#include "base/main/main.h"
#include "base/cmd/cmd.h"

#include <cstdio>
#include <set>

ABC_NAMESPACE_IMPL_START

// --------------------------------------------------------------------------
// helpers
// --------------------------------------------------------------------------

// Build a 2-input single-AND combinational AIG: o = a & b.
static Gia_Man_t* BuildSmallAig() {
  Gia_Man_t* p = Gia_ManStart(100);
  int a = Gia_ManAppendCi(p);
  int b = Gia_ManAppendCi(p);
  int g = Gia_ManAppendAnd(p, a, b);
  Gia_ManAppendCo(p, g);
  return p;
}

// Build o = (a & b) | (c & d), expressed with ANDs and inverters so the
// mapper has something non-trivial to do.
static Gia_Man_t* BuildOrOfAnds() {
  Gia_Man_t* p = Gia_ManStart(100);
  int a = Gia_ManAppendCi(p);
  int b = Gia_ManAppendCi(p);
  int c = Gia_ManAppendCi(p);
  int d = Gia_ManAppendCi(p);
  int ab = Gia_ManAppendAnd(p, a, b);
  int cd = Gia_ManAppendAnd(p, c, d);
  int nand = Gia_ManAppendAnd(p, Abc_LitNot(ab), Abc_LitNot(cd));  // ~ab & ~cd
  Gia_ManAppendCo(p, Abc_LitNot(nand));                           // ab | cd
  return p;
}

static int FirstAndId(Gia_Man_t* p) {
  Gia_Obj_t* pObj;
  int i;
  Gia_ManForEachAnd(p, pObj, i) return i;
  return -1;
}

static int CountTotalOrigins(Gia_Man_t* p) {
  Gia_Obj_t* pObj;
  int i, total = 0;
  if (!p->vOrigins) return 0;
  Gia_ManForEachObj(p, pObj, i) total += Gia_ObjOriginsNum(p, i);
  return total;
}

// Allocate origins and seed every AND node with its own id (the "identity"
// mapping Yosys writes via the XAIGER "y" extension).
static void SeedIdentityOrigins(Gia_Man_t* p) {
  Gia_Obj_t* pObj;
  int i;
  p->vOrigins = Gia_ManOriginsAlloc(Gia_ManObjNum(p));
  Gia_ManForEachAnd(p, pObj, i) Gia_ObjSetOrigin(p, i, i);
}

// --------------------------------------------------------------------------
// core infrastructure
// --------------------------------------------------------------------------

TEST(OriginsTest, SetAndGetSingleOrigin) {
  Gia_Man_t* p = BuildSmallAig();
  p->vOrigins = Gia_ManOriginsAlloc(Gia_ManObjNum(p));
  int g = FirstAndId(p);
  Gia_ObjSetOrigin(p, g, 42);
  EXPECT_EQ(Gia_ObjOriginsNum(p, g), 1);
  EXPECT_EQ(Gia_ObjOriginsGet(p, g, 0), 42);
  Gia_ManStop(p);
}

TEST(OriginsTest, AddDeduplicates) {
  Gia_Man_t* p = BuildSmallAig();
  p->vOrigins = Gia_ManOriginsAlloc(Gia_ManObjNum(p));
  int g = FirstAndId(p);
  Gia_ObjAddOrigin(p, g, 7);
  Gia_ObjAddOrigin(p, g, 7);  // duplicate: ignored
  EXPECT_EQ(Gia_ObjOriginsNum(p, g), 1);
  Gia_ObjAddOrigin(p, g, 9);
  EXPECT_EQ(Gia_ObjOriginsNum(p, g), 2);
  Gia_ManStop(p);
}

TEST(OriginsTest, InlineToOverflowPromotion) {
  Gia_Man_t* p = BuildSmallAig();
  p->vOrigins = Gia_ManOriginsAlloc(Gia_ManObjNum(p));
  int g = FirstAndId(p);
  const int N = GIA_ORIGINS_INLINE + 3;  // force promotion past the inline buffer
  for (int k = 0; k < N; k++) Gia_ObjAddOrigin(p, g, 100 + k);
  EXPECT_EQ(Gia_ObjOriginsNum(p, g), N);
  std::set<int> got;
  for (int k = 0; k < N; k++) got.insert(Gia_ObjOriginsGet(p, g, k));
  for (int k = 0; k < N; k++) EXPECT_TRUE(got.count(100 + k)) << "missing origin " << (100 + k);
  Gia_ManStop(p);
}

TEST(OriginsTest, UnionAcrossManagers) {
  Gia_Man_t* src = BuildSmallAig();
  src->vOrigins = Gia_ManOriginsAlloc(Gia_ManObjNum(src));
  int sg = FirstAndId(src);
  Gia_ObjAddOrigin(src, sg, 11);
  Gia_ObjAddOrigin(src, sg, 22);

  Gia_Man_t* dst = BuildSmallAig();
  dst->vOrigins = Gia_ManOriginsAlloc(Gia_ManObjNum(dst));
  int dg = FirstAndId(dst);
  Gia_ObjAddOrigin(dst, dg, 11);  // overlaps with src

  Gia_ObjUnionOrigins(dst, dg, src, sg);
  EXPECT_EQ(Gia_ObjOriginsNum(dst, dg), 2);  // {11, 22} deduplicated

  Gia_ManStop(src);
  Gia_ManStop(dst);
}

TEST(OriginsTest, NOriginsMaxCapsAccumulation) {
  Gia_Man_t* p = BuildSmallAig();
  p->vOrigins = Gia_ManOriginsAlloc(Gia_ManObjNum(p));
  p->nOriginsMax = 10;
  int g = FirstAndId(p);
  for (int k = 0; k < 50; k++) Gia_ObjAddOrigin(p, g, 1000 + k);
  EXPECT_EQ(Gia_ObjOriginsNum(p, g), 10);  // capped once in overflow mode
  Gia_ManStop(p);
}

// --------------------------------------------------------------------------
// propagation
// --------------------------------------------------------------------------

TEST(OriginsTest, GiaManDupPreservesOrigins) {
  Gia_Man_t* p = BuildSmallAig();
  p->vOrigins = Gia_ManOriginsAlloc(Gia_ManObjNum(p));
  int g = FirstAndId(p);
  Gia_ObjAddOrigin(p, g, 55);

  Gia_Man_t* dup = Gia_ManDup(p);
  ASSERT_TRUE(dup->vOrigins != nullptr);
  EXPECT_EQ(CountTotalOrigins(dup), 1);
  int dg = FirstAndId(dup);
  ASSERT_GE(dg, 0);
  EXPECT_EQ(Gia_ObjOriginsNum(dup, dg), 1);
  EXPECT_EQ(Gia_ObjOriginsGet(dup, dg, 0), 55);

  Gia_ManStop(p);
  Gia_ManStop(dup);
}

TEST(OriginsTest, AigerWriteReadRoundTripPreservesOrigins) {
  Gia_Man_t* p = BuildSmallAig();
  p->vOrigins = Gia_ManOriginsAlloc(Gia_ManObjNum(p));
  int g = FirstAndId(p);
  Gia_ObjAddOrigin(p, g, 77);

  const char* fname = "test_origins_roundtrip.aig";
  Gia_AigerWrite(p, (char*)fname, 0, 0, 0);  // "y" extension emitted unconditionally
  Gia_Man_t* q = Gia_AigerRead((char*)fname, 0, 0, 0);
  remove(fname);

  ASSERT_TRUE(q != nullptr);
  ASSERT_TRUE(q->vOrigins != nullptr);
  EXPECT_EQ(CountTotalOrigins(q), 1);

  Gia_ManStop(p);
  Gia_ManStop(q);
}

// --------------------------------------------------------------------------
// engine: &nf standard-cell mapping
//
// &nf maps in place (Nf_ManDeriveMapping returns p->pGia without renumbering),
// so origins on the AIG nodes must survive standard-cell mapping unchanged.
// --------------------------------------------------------------------------

TEST(OriginsTest, NfMappingPreservesOrigins) {
  // Seed a design with origins and write it to AIGER (carries the "y" ext).
  Gia_Man_t* p = BuildOrOfAnds();
  SeedIdentityOrigins(p);
  const int seeded = CountTotalOrigins(p);
  ASSERT_GT(seeded, 0);
  const char* aig = "test_origins_nf_in.aig";
  Gia_AigerWrite(p, (char*)aig, 0, 0, 0);
  Gia_ManStop(p);

  Abc_Start();
  Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();

  ASSERT_EQ(Cmd_CommandExecute(pAbc, "read_genlib test_origins.genlib"), 0);
  char cmd[256];
  snprintf(cmd, sizeof(cmd), "&read %s", aig);
  ASSERT_EQ(Cmd_CommandExecute(pAbc, cmd), 0);

  Gia_Man_t* before = Abc_FrameReadGia(pAbc);
  ASSERT_TRUE(before != nullptr);
  ASSERT_GT(CountTotalOrigins(before), 0);  // origins read back from "y"

  ASSERT_EQ(Cmd_CommandExecute(pAbc, "&nf"), 0);

  Gia_Man_t* after = Abc_FrameReadGia(pAbc);
  ASSERT_TRUE(after != nullptr);
  ASSERT_TRUE(after->vOrigins != nullptr);
  EXPECT_GT(CountTotalOrigins(after), 0);  // preserved through &nf std-cell mapping

  remove(aig);
  Abc_Stop();
}

// Regression: writing a cell-mapped GIA emits an "M" (cell-mapping) section
// followed by the "y" origin section. The AIGER reader must SKIP the unknown
// "M" section rather than bail out of the extension loop, otherwise the "y"
// origins (written after "M") are silently lost on read-back.
TEST(OriginsTest, MappedAigerRoundTripPreservesOrigins) {
  Gia_Man_t* p = BuildOrOfAnds();
  SeedIdentityOrigins(p);
  const char* in = "test_origins_mapped_in.aig";
  Gia_AigerWrite(p, (char*)in, 0, 0, 0);
  Gia_ManStop(p);

  Abc_Start();
  Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
  ASSERT_EQ(Cmd_CommandExecute(pAbc, "read_genlib test_origins.genlib"), 0);
  char cmd[256];
  snprintf(cmd, sizeof(cmd), "&read %s", in);
  ASSERT_EQ(Cmd_CommandExecute(pAbc, cmd), 0);
  ASSERT_EQ(Cmd_CommandExecute(pAbc, "&nf"), 0);                                   // creates cell mapping
  ASSERT_EQ(Cmd_CommandExecute(pAbc, "&write test_origins_mapped_out.aig"), 0);   // emits "M" then "y"
  ASSERT_EQ(Cmd_CommandExecute(pAbc, "&read test_origins_mapped_out.aig"), 0);    // must skip "M" to reach "y"

  Gia_Man_t* after = Abc_FrameReadGia(pAbc);
  ASSERT_TRUE(after != nullptr);
  ASSERT_TRUE(after->vOrigins != nullptr);   // would be NULL without the "M"-skip fix
  EXPECT_GT(CountTotalOrigins(after), 0);

  remove(in);
  remove("test_origins_mapped_out.aig");
  Abc_Stop();
}

// Balancing rebuilds the AIG, creating new internal nodes with no 1:1 origin
// correspondence. Gia_ManOriginsDupFill must cover them bottom-up so no node
// (and thus no cell later mapped from it) loses provenance. A left-deep AND
// chain is restructured into a shallow tree, forcing fresh nodes.
TEST(OriginsTest, AreaBalancePreservesOriginCoverage) {
  Gia_Man_t* p = Gia_ManStart(100);
  int ci[8], i;
  for (i = 0; i < 8; i++) ci[i] = Gia_ManAppendCi(p);
  int lit = ci[0];
  for (i = 1; i < 8; i++) lit = Gia_ManAppendAnd(p, lit, ci[i]);
  Gia_ManAppendCo(p, lit);
  // Seed identity origins on every object (CIs included) as the XAIGER "y"
  // extension does — the fill propagates CI origins up into new leaf nodes.
  Gia_Obj_t* pSeed;
  p->vOrigins = Gia_ManOriginsAlloc(Gia_ManObjNum(p));
  Gia_ManForEachObj(p, pSeed, i)
    if (i > 0) Gia_ObjSetOrigin(p, i, i);

  Gia_Man_t* pNew = Gia_ManAreaBalance(p, 1, 1000, 0, 0);
  ASSERT_TRUE(pNew->vOrigins != nullptr);
  Gia_Obj_t* pObj;
  int uncovered = 0;
  Gia_ManForEachAnd(pNew, pObj, i)
    if (Gia_ObjOriginsNum(pNew, i) == 0) uncovered++;
  EXPECT_EQ(uncovered, 0) << "balanced AIG has AND nodes with no origin";

  Gia_ManStop(p);
  Gia_ManStop(pNew);
}

ABC_NAMESPACE_IMPL_END
