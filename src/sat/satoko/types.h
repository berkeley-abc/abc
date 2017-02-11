//===--- types.h ------------------------------------------------------------===
//
//                     satoko: Satisfiability solver
//
// This file is distributed under the BSD 2-Clause License.
// See LICENSE for details.
//
//===------------------------------------------------------------------------===
#ifndef satoko__types_h
#define satoko__types_h

#include "utils/fixed.h"
#include "utils/vec/vec_dble.h"
#include "utils/vec/vec_uint.h"

#include "misc/util/abc_global.h"
ABC_NAMESPACE_HEADER_START

#define SATOKO_ACT_VAR_DBLE
// #define SATOKO_ACT_VAR_FIXED
// #define SATOKO_ACT_CLAUSE_FLOAT

#ifdef SATOKO_ACT_VAR_DBLE
    #define VAR_ACT_INIT_INC 1.0
    #define VAR_ACT_LIMIT (double)1e100
    #define VAR_ACT_RESCALE (double)1e-100
    #define VAR_ACT_DECAY (double)0.95
    typedef double act_t;
    typedef vec_dble_t vec_act_t ;
    #define vec_act_alloc(size) vec_dble_alloc(size)
    #define vec_act_free(vec) vec_dble_free(vec)
    #define vec_act_size(vec) vec_dble_size(vec)
    #define vec_act_data(vec) vec_dble_data(vec)
    #define vec_act_at(vec, idx) vec_dble_at(vec, idx)
    #define vec_act_push_back(vec, value) vec_dble_push_back(vec, value)
#elif defined(SATOKO_ACT_VAR_FIXED)
    #define VAR_ACT_INIT_INC FIXED_ONE
    #define VAR_ACT_LIMIT  (fixed_t)0xDFFFFFFF
    #define VAR_ACT_RESCALE (fixed_t)0x00000012
    #define VAR_ACT_DECAY (double)0.96
    typedef fixed_t act_t;
    typedef    vec_uint_t vec_act_t;
    #define vec_act_alloc(size) vec_uint_alloc(size)
    #define vec_act_free(vec) vec_uint_free(vec)
    #define vec_act_size(vec) vec_uint_size(vec)
    #define vec_act_data(vec) vec_uint_data(vec)
    #define vec_act_at(vec, idx) vec_uint_at(vec, idx)
    #define vec_act_push_back(vec, value) vec_uint_push_back(vec, value)
#else
    #define VAR_ACT_INIT_INC (1 << 5)
    typedef unsigned act_t;
    typedef    vec_uint_t vec_act_t;
    #define vec_act_alloc(size) vec_uint_alloc(size)
    #define vec_act_free(vec) vec_uint_free(vec)
    #define vec_act_size(vec) vec_uint_size(vec)
    #define vec_act_data(vec) vec_uint_data(vec)
    #define vec_act_at(vec, idx) vec_uint_at(vec, idx)
    #define vec_act_push_back(vec, value) vec_uint_push_back(vec, value)
#endif /* SATOKO_ACT_VAR_DBLE */

#ifdef SATOKO_ACT_CLAUSE_FLOAT
    #define CLAUSE_ACT_INIT_INC 1.0
    typedef float clause_act_t;
#else
    #define CLAUSE_ACT_INIT_INC (1 << 11)
    typedef unsigned clause_act_t;
#endif /* SATOKO_ACT_CLAUSE_FLOAT */

ABC_NAMESPACE_HEADER_END
#endif /* satoko__types_h */
