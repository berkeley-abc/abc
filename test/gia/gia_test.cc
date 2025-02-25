#include "gtest/gtest.h"

#include "aig/gia/gia.h"

ABC_NAMESPACE_IMPL_START

TEST(GiaTest, CanAllocateGiaManager) {
  Gia_Man_t* aig_manager =  Gia_ManStart(100);

  EXPECT_TRUE(aig_manager != nullptr);
  Gia_ManStop(aig_manager);
}

TEST(GiaTest, CanAddACi) {
  Gia_Man_t* aig_manager =  Gia_ManStart(100);
  Gia_ManAppendCi(aig_manager);

  EXPECT_EQ(Gia_ManCiNum(aig_manager), 1);
  Gia_ManStop(aig_manager);
}

TEST(GiaTest, CanAddACo) {
  Gia_Man_t* aig_manager =  Gia_ManStart(100);
  int input1 = Gia_ManAppendCi(aig_manager);
  Gia_ManAppendCo(aig_manager, input1);

  EXPECT_EQ(Gia_ManCiNum(aig_manager), 1);
  EXPECT_EQ(Gia_ManCoNum(aig_manager), 1);
  Gia_ManStop(aig_manager);
}

TEST(GiaTest, CanAddAnAndGate) {
  Gia_Man_t* aig_manager =  Gia_ManStart(100);

  int input1 = Gia_ManAppendCi(aig_manager);
  int input2 = Gia_ManAppendCi(aig_manager);

  int and_output = Gia_ManAppendAnd(aig_manager, input1, input2);
  Gia_ManAppendCo(aig_manager, and_output);

  Vec_Wrd_t* stimulus = Vec_WrdAlloc(2);
  Vec_WrdPush(stimulus, /*A*/1);
  Vec_WrdPush(stimulus, /*B*/1);
  Vec_Wrd_t* output = Gia_ManSimPatSimOut(aig_manager, stimulus, /*fouts*/1);

  EXPECT_EQ(Gia_ManCiNum(aig_manager), 2);
  EXPECT_EQ(Gia_ManCoNum(aig_manager), 1);
  // A = 1, B = 1 -> A & B == 1
  EXPECT_EQ(Vec_WrdGetEntry(output, 0), 1);
  Vec_WrdFree(output);
  Gia_ManStop(aig_manager);
}

ABC_NAMESPACE_IMPL_END
