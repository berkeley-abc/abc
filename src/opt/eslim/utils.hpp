/**CFile****************************************************************

  FileName    [utils.hpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM).]

  Synopsis    [Utilities]

  Author      [Franz-Xaver Reichl]
  
  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - April 2026.]

  Revision    [$Id: eSLIM.cpp,v 1.00 2025/04/14 00:00:00 Exp $]

***********************************************************************/

#ifndef ABC__OPT__ESLIM__UTILS_hpp
#define ABC__OPT__ESLIM__UTILS_hpp

#include <vector>
#include <unordered_map>
#include <unordered_set>

#include "misc/util/abc_global.h"

#if __cplusplus >= 202002L
  // C++20 (and later) code
  #include <bit>
#endif

#if __cplusplus >= 202002L
  // // C++20 (and later) code
  // #include <bit>
  #define popcount(x) std::popcount(x)
#elif defined(__GNUC__)
  #define popcount(x) __builtin_popcountll(x)
// #elif defined(_MSC_VER)
#elif defined(_WIN64)
  #define popcount(x) __popcnt64(x)
#else

  inline int popcount64Impl(ABC_UINT64_T x) {
    // Constants are 64-bit masks
    const ABC_UINT64_T m1 = 0x5555555555555555;
    const ABC_UINT64_T m2 = 0x3333333333333333; 
    const ABC_UINT64_T m3 = 0x0F0F0F0F0F0F0F0F; 
    const ABC_UINT64_T m4 = 0x0101010101010101; 
    x = x - ((x >> 1) & m1);
    x = (x & m2) + ((x >> 2) & m2);
    x = (x + (x >> 4)) & m3;
    return (x * m4) >> 56;
  }
  #define popcount(x) popcount64Impl(x)

#endif

ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM {

  inline int lsb(ABC_UINT64_T tt) {
    #if __cplusplus >= 202002L
      if (tt == 0) {
        return -1;
      }
      return std::countr_zero(tt);
    #elif defined(__GNUC__)
      return __builtin_ffsl(tt) - 1;
    // #elif defined(_MSC_VER)
    #elif defined(_WIN64)
      if (tt == 0) {
        return -1;
      }
      unsigned long x = 0;
      _BitScanForward64(&x, tt);
      return (int)x;
    #else
      if (tt == 0) {
        return -1;
      }
      ABC_UINT64_T lsb = tt & -tt;
      const ABC_UINT64_T debruijn = 0x03f79d71b4cb0a89ULL;
      ABC_UINT64_T scrambled = (lsb * debruijn) >> 58;
      const int index64[64] = {
        0,   1, 48,  2, 57, 49, 28,  3, 61, 58, 50, 42, 29, 17,  4, 62,
        55, 59, 36, 53, 51, 43, 22, 30, 18, 12,  5, 63, 35, 56, 60, 54,
        37, 52, 44, 27, 23, 31, 19,  8, 13,  6, 64, 32, 47, 38, 45, 21,
        26, 24, 39, 16,  7, 64, 33, 46, 20, 25, 41, 15, 64, 34, 40, 64
      };
      return index64[scrambled];
    #endif
  }

  struct eSLIMConfig {      
    bool aig = true;
    int gate_size = 2;
    
    bool apply_strash = true;                                   
    bool fix_seed = false;    
    bool fill_subcircuits = false;                              
    bool trial_limit_active = true;
    bool allow_xors = false;            

    unsigned int timeout = 3600;                    
    unsigned int iterations = 0;                          
    unsigned int subcircuit_max_size = 6;    
    unsigned int additional_gates = 0;        
    unsigned int strash_intervall = 100;    
    int seed = 0;
    unsigned int nselection_trials = 120;
    double expansion_probability = 0.5;  
    unsigned int bias = 2;
    unsigned int nwindows = 1;
    unsigned int window_size = 500;

    unsigned int taboo_time = 100;
    double taboo_ratio = 0.5;

    // times given in sec
    int minimum_sat_timeout = 1;
    int base_sat_timeout = 120;
    int minimum_dynamic_timeout_sample_size = 50;
    double dynamic_timeout_buffer_factor = 1.4;

    int relation_generation_timeout = 180;
    bool approximate_relation = false; // Compute an overapproximation of the relation that may not use all don't cares by limiting the tfo of the subcircuit
    bool generate_relation_with_tfi_limit = false; // If approximate_relation is true, also limit the tfi of the subcircuit
    unsigned int relation_tfi_bound = 0;
    unsigned int relation_tfo_bound = 0;

    int verbosity_level = 0;
  };

  class eSLIMLog {

    public:
      unsigned int iteration_count = 0;
      double relation_generation_time = 0;
      double synthesis_time = 0;
      unsigned int subcircuits_with_forbidden_pairs = 0;

      std::vector<int> nof_analyzed_circuits_per_size;
      std::vector<int> nof_replaced_circuits_per_size;
      std::vector<int> nof_reduced_circuits_per_size;

      std::vector<ABC_UINT64_T> cummulative_sat_runtimes_per_size;
      std::vector<int> nof_sat_calls_per_size;
      std::vector<ABC_UINT64_T> cummulative_unsat_runtimes_per_size;
      std::vector<int> nof_unsat_calls_per_size;
      std::vector<double> cummulative_relation_generation_times_per_size;
      std::vector<int> nof_relation_generations_per_size;

      double cummulative_sat_runtime_synthesis = 0; // msec
      double max_sat_runtime_synthesis = 0; // msec
      ABC_UINT64_T nof_sat_calls_synthesis = 0;

      double cummulative_sat_runtime_relation_generation = 0; // sec
      double max_sat_runtime_relation_generation = 0; // sec
      ABC_UINT64_T nof_sat_calls_relation_generation = 0; 

      eSLIMLog(int size);
      int getSize() const;
      void resize(int size);
  };


  inline eSLIMLog::eSLIMLog(int size) 
          : nof_analyzed_circuits_per_size(size + 1, 0), nof_replaced_circuits_per_size(size + 1, 0),
            nof_reduced_circuits_per_size(size + 1, 0), 
            cummulative_sat_runtimes_per_size(size + 1, 0), nof_sat_calls_per_size(size + 1, 0), 
            cummulative_unsat_runtimes_per_size(size + 1, 0), nof_unsat_calls_per_size(size + 1, 0),
            cummulative_relation_generation_times_per_size(size + 1, 0), nof_relation_generations_per_size(size + 1, 0) {
  }

  inline int eSLIMLog::getSize() const {
    return nof_analyzed_circuits_per_size.size() - 1;
  }

  inline void eSLIMLog::resize(int size) {
    int sz = size + 1;
    nof_analyzed_circuits_per_size.resize(sz);
    nof_replaced_circuits_per_size.resize(sz);
    nof_reduced_circuits_per_size.resize(size);
    cummulative_sat_runtimes_per_size.resize(sz);
    nof_sat_calls_per_size.resize(sz);
    cummulative_unsat_runtimes_per_size.resize(sz);
    nof_unsat_calls_per_size.resize(sz);
    cummulative_relation_generation_times_per_size.resize(sz);
    nof_relation_generations_per_size.resize(sz);
  }

}
ABC_NAMESPACE_CXX_HEADER_END
#endif