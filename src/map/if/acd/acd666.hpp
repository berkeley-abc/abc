/**C++File**************************************************************

  FileName    [acd666.hpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Ashenhurst-Curtis decomposition.]

  Synopsis    [Interface with the FPGA mapping package.]

  Author      [Alessandro Tempia Calvino]

  Affiliation [EPFL]

  Date        [Ver. 1.0. Started - Feb 8, 2024.]

***********************************************************************/
/*!
  \file acd666.hpp
  \brief Ashenhurst-Curtis decomposition for "666" cascade

  \author Alessandro Tempia Calvino
*/

#ifndef _ACD666_H_
#define _ACD666_H_
#pragma once

#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <type_traits>

#include "kitty_constants.hpp"
#include "kitty_constructors.hpp"
#include "kitty_dynamic_tt.hpp"
#include "kitty_operations.hpp"
#include "kitty_operators.hpp"
#include "kitty_static_tt.hpp"

ABC_NAMESPACE_CXX_HEADER_START

namespace acd
{

class acd666_impl
{
private:
  static constexpr uint32_t max_num_vars = 16;
  using STT = kitty::static_truth_table<max_num_vars>;
  using LTT = kitty::static_truth_table<6>;

public:
  explicit acd666_impl( uint32_t const num_vars, bool const verify = false )
      : num_vars( num_vars ), verify( verify )
  {
    std::iota( permutations.begin(), permutations.end(), 0 );
  }

  /*! \brief Runs ACD 666 */
  bool run( word* ptt )
  {
    assert( num_vars > 6 );

    /* truth table is too large for the settings */
    if ( num_vars > max_num_vars || num_vars > 16 )
    {
      return false;
    }

    /* convert to static TT */
    init_truth_table( ptt );

    /* run ACD trying different bound sets and free sets */
    return find_decomposition();
  }

  int compute_decomposition()
  {
    if ( best_multiplicity == UINT32_MAX )
      return -1;

    uint32_t n = num_luts == 3 ? rm_support_size : num_vars;
    compute_decomposition_impl( n );

    if ( verify && !verify_impl() )
    {
      return 1;
    }

    return 0;
  }

  uint32_t get_num_edges()
  {
    if ( support_sizes[0] == UINT32_MAX )
    {
      return UINT32_MAX;
    }

    uint32_t num_edges = support_sizes[0] + support_sizes[1] + 1 + ( shared_vars[0] < UINT32_MAX ? 1 : 0 );

    if ( num_luts == 2 )
      return num_edges;

    /* real value after support minimization */
    return num_edges + support_sizes[2] + 1 + ( shared_vars[1] < UINT32_MAX ? 1 : 0 );
  }

  /* contains a 1 for BS variables */
  // unsigned get_profile()
  // {
  //   unsigned profile = 0;

  //   if ( support_sizes[0] == UINT32_MAX )
  //     return -1;

  //   for ( uint32_t i = 0; i < bs_support_size; ++i )
  //   {
  //     profile |= 1 << permutations[best_free_set + bs_support[i]];
  //   }

  //   return profile;
  // }

  // void get_decomposition( unsigned char* decompArray )
  // {
  //   if ( support_sizes[0] == UINT32_MAX )
  //     return;

  //   get_decomposition_abc( decompArray );
  // }

private:
  bool find_decomposition()
  {
    best_multiplicity = UINT32_MAX;
    best_free_set = UINT32_MAX;

    /* find ACD "66" for different number of variables in the free set */
    for ( uint32_t i = num_vars - 6; i <= 5; ++i )
    {
      if ( find_decomposition_bs( start_tt, num_vars, i ) )
      {
        num_luts = 2;
        return true;
      }
    }

    /* find ACD "666" for different number of variables in the free set */
    bool dec_found = false;
    uint32_t min_vars_free_set = num_vars <= 11 ? 1 : num_vars - 11;
    uint32_t max_vars_free_set = num_vars <= 11 ? num_vars - 7 : 5;
    for ( uint32_t i = max_vars_free_set; i >= min_vars_free_set; --i )
    // for ( uint32_t i = min_vars_free_set; i <= max_vars_free_set; ++i )
    {
      dec_found = find_decomposition_bs( start_tt, num_vars, i );
      if ( dec_found )
        break;
    }

    if ( !dec_found )
    {
      best_multiplicity = UINT32_MAX;
      return false;
    }

    /* compute functions for the top and reminder LUT */
    compute_decomposition_impl_top( num_vars );

    /* find ACD "66" for the remainder function */
    for ( uint32_t i = rm_support_size - 6; i <= 5; ++i )
    {
      if ( find_decomposition_bs( remainder, rm_support_size, i ) )
      {
        num_luts = 3;
        fix_permutations_remainder( rm_support_size );
        return true;
      }
    }

    best_multiplicity = UINT32_MAX;
    return false;
  }

  void init_truth_table( word* ptt )
  {
    uint32_t const num_blocks = ( num_vars <= 6 ) ? 1 : ( 1 << ( num_vars - 6 ) );

    for ( uint32_t i = 0; i < num_blocks; ++i )
    {
      start_tt._bits[i] = ptt[i];
    }

    local_extend_to( start_tt, num_vars );
  }

  uint32_t column_multiplicity( STT const& tt, uint32_t n, uint32_t free_set_size )
  {
    assert( free_set_size <= 5 );

    uint32_t const num_blocks = ( n > 6 ) ? ( 1u << ( n - 6 ) ) : 1;
    uint64_t const shift = UINT64_C( 1 ) << free_set_size;
    uint64_t const mask = ( UINT64_C( 1 ) << shift ) - 1;
    uint32_t const limit = free_set_size < 5 ? 4 : 2;
    uint32_t cofactors[4];
    uint32_t size = 0;

    /* extract iset functions */
    for ( auto i = 0u; i < num_blocks; ++i )
    {
      uint64_t sub = tt._bits[i];
      for ( auto j = 0; j < ( 64 >> free_set_size ); ++j )
      {
        uint32_t fs_fn = static_cast<uint32_t>( sub & mask );
        uint32_t k;
        for ( k = 0; k < size; ++k )
        {
          if ( fs_fn == cofactors[k] )
            break;
        }
        if ( k == limit )
          return 5;
        if ( k == size )
          cofactors[size++] = fs_fn;
        sub >>= shift;
      }
    }

    return size;
  }

  inline bool combinations_next( uint32_t n, uint32_t k, uint32_t* pComb, uint32_t* pInvPerm, STT& tt )
  {
    uint32_t i;

    for ( i = k - 1; pComb[i] == n - k + i; --i )
    {
      if ( i == 0 )
        return false;
    }

    /* move vars */
    uint32_t var_old = pComb[i];
    uint32_t pos_new = pInvPerm[var_old + 1];
    std::swap( pInvPerm[var_old + 1], pInvPerm[var_old] );
    std::swap( pComb[i], pComb[pos_new] );
    swap_inplace_local( tt, n, i, pos_new );

    for ( uint32_t j = i + 1; j < k; j++ )
    {
      var_old = pComb[j];
      pos_new = pInvPerm[pComb[j - 1] + 1];
      std::swap( pInvPerm[pComb[j - 1] + 1], pInvPerm[var_old] );
      std::swap( pComb[j], pComb[pos_new] );
      swap_inplace_local( tt, n, j, pos_new );
    }

    return true;
  }

  bool find_decomposition_bs( STT tt, uint32_t n, uint32_t free_set_size )
  {
    /* works up to 16 input truth tables */
    assert( n <= 16 );

    /* init combinations */
    uint32_t pComb[16], pInvPerm[16];
    for ( uint32_t i = 0; i < n; ++i )
    {
      pComb[i] = pInvPerm[i] = i;
    }

    /* enumerate combinations */
    best_free_set = free_set_size;
    do
    {
      uint32_t cost = column_multiplicity( tt, n, free_set_size );
      if ( cost == 2 )
      {
        best_tt = tt;
        best_multiplicity = cost;
        for ( uint32_t i = 0; i < n; ++i )
        {
          permutations[i] = pComb[i];
        }
        return true;
      }
      else if ( cost <= 4 && free_set_size < 5 )
      {
        /* look for a shared variable */
        best_multiplicity = cost;
        int res = check_shared_set( tt, n );

        if ( res > 0 )
        {
          best_tt = tt;
          for ( uint32_t i = 0; i < n; ++i )
          {
            permutations[i] = pComb[i];
          }
          /* move shared variable as the most significative one */
          swap_inplace_local( best_tt, n, res, n - 1 );
          std::swap( permutations[res], permutations[n - 1] );
          return true;
        }
      }
    } while ( combinations_next( n, free_set_size, pComb, pInvPerm, tt ) );

    return false;
  }

  inline bool check_shared_var( STT const& tt, uint32_t n, uint32_t free_set_size, uint32_t shared_var )
  {
    assert( free_set_size <= 5 );

    uint32_t const num_blocks = ( n > 6 ) ? ( 1u << ( n - 6 ) ) : 1;
    uint64_t const shift = UINT64_C( 1 ) << free_set_size;
    uint64_t const mask = ( UINT64_C( 1 ) << shift ) - 1;
    uint32_t cofactors[2][4];
    uint32_t size[2] = { 0, 0 };
    uint32_t shared_var_shift = shared_var - free_set_size;

    /* extract iset functions */
    uint32_t iteration_counter = 0;
    for ( auto i = 0u; i < num_blocks; ++i )
    {
      uint64_t sub = tt._bits[i];
      for ( auto j = 0; j < ( 64 >> free_set_size ); ++j )
      {
        uint32_t fs_fn = static_cast<uint32_t>( sub & mask );
        uint32_t p = ( iteration_counter >> shared_var_shift ) & 1;
        uint32_t k;
        for ( k = 0; k < size[p]; ++k )
        {
          if ( fs_fn == cofactors[p][k] )
            break;
        }
        if ( k == 2 )
          return false;
        if ( k == size[p] )
          cofactors[p][size[p]++] = fs_fn;
        sub >>= shift;
        ++iteration_counter;
      }
    }

    return true;
  }

  inline int check_shared_set( STT const& tt, uint32_t n )
  {
    /* find one shared set variable */
    for ( uint32_t i = best_free_set; i < n; ++i )
    {
      /* check the multiplicity of cofactors */
      if ( check_shared_var( tt, n, best_free_set, i ) )
      {
        return i;
      }
    }

    return -1;
  }

  void compute_decomposition_impl_top( uint32_t n, bool verbose = false )
  {
    bool has_shared_set = best_multiplicity > 2;

    /* construct isets involved in multiplicity */
    STT isets0[2];
    STT isets1[2];

    /* construct isets */
    uint32_t offset = 0;
    uint32_t num_blocks = ( n > 6 ) ? ( 1u << ( n - 6 ) ) : 1;
    uint64_t const shift = UINT64_C( 1 ) << best_free_set;
    uint64_t const mask = ( UINT64_C( 1 ) << shift ) - 1;

    /* limit analysis on 0 cofactor of the shared variable */
    if ( has_shared_set )
      num_blocks >>= 1;

    uint64_t fs_fun[4] = { best_tt._bits[0] & mask, 0, 0, 0 };

    for ( auto i = 0u; i < num_blocks; ++i )
    {
      uint64_t cof = best_tt._bits[i];
      for ( auto j = 0; j < ( 64 >> best_free_set ); ++j )
      {
        uint64_t val = cof & mask;
        if ( val == fs_fun[0] )
        {
          isets0[0]._bits[i / shift] |= UINT64_C( 1 ) << ( j + offset );
        }
        else
        {
          isets0[1]._bits[i / shift] |= UINT64_C( 1 ) << ( j + offset );
          fs_fun[1] = val;
        }
        cof >>= shift;
      }
      offset = ( offset + ( 64 >> best_free_set ) ) & 0x3F;
    }

    /* continue on the 1 cofactor if shared set */
    if ( has_shared_set )
    {
      fs_fun[2] = best_tt._bits[num_blocks] & mask;
      for ( auto i = num_blocks; i < ( num_blocks << 1 ); ++i )
      {
        uint64_t cof = best_tt._bits[i];
        for ( auto j = 0; j < ( 64 >> best_free_set ); ++j )
        {
          uint64_t val = cof & mask;
          if ( val == fs_fun[2] )
          {
            isets1[0]._bits[i / shift] |= UINT64_C( 1 ) << ( j + offset );
          }
          else
          {
            isets1[1]._bits[i / shift] |= UINT64_C( 1 ) << ( j + offset );
            fs_fun[3] = val;
          }
          cof >>= shift;
        }
        offset = ( offset + ( 64 >> best_free_set ) ) & 0x3F;
      }
    }

    /* find the support minimizing combination with shared set */
    compute_functions_top( isets0, isets1, fs_fun, n );

    /* print functions */
    if ( verbose )
    {
      std::cout << "RM function         : ";
      kitty::print_hex( remainder );
      std::cout << "\n";
      LTT f;
      f._bits = dec_funcs[2];
      std::cout << "Composition function: ";
      kitty::print_hex( f );
      std::cout << "\n";
    }
  }

  void compute_decomposition_impl( uint32_t n, bool verbose = false )
  {
    bool has_shared_set = best_multiplicity > 2;

    /* construct isets involved in multiplicity */
    LTT isets0[2];
    LTT isets1[2];

    /* construct isets */
    uint32_t offset = 0;
    uint32_t num_blocks = ( n > 6 ) ? ( 1u << ( n - 6 ) ) : 1;
    uint64_t const shift = UINT64_C( 1 ) << best_free_set;
    uint64_t const mask = ( UINT64_C( 1 ) << shift ) - 1;

    /* limit analysis on 0 cofactor of the shared variable */
    if ( has_shared_set )
      num_blocks >>= 1;

    uint64_t fs_fun[4] = { best_tt._bits[0] & mask, 0, 0, 0 };

    for ( auto i = 0u; i < num_blocks; ++i )
    {
      uint64_t cof = best_tt._bits[i];
      for ( auto j = 0; j < ( 64 >> best_free_set ); ++j )
      {
        uint64_t val = cof & mask;

        if ( val == fs_fun[0] )
        {
          isets0[0]._bits |= UINT64_C( 1 ) << ( j + offset );
        }
        else
        {
          isets0[1]._bits |= UINT64_C( 1 ) << ( j + offset );
          fs_fun[1] = val;
        }

        cof >>= shift;
      }

      offset = ( offset + ( 64 >> best_free_set ) ) % 64;
    }

    /* continue on the 1 cofactor if shared set */
    if ( has_shared_set )
    {
      fs_fun[2] = best_tt._bits[num_blocks] & mask;
      for ( auto i = num_blocks; i < ( num_blocks << 1 ); ++i )
      {
        uint64_t cof = best_tt._bits[i];
        for ( auto j = 0; j < ( 64 >> best_free_set ); ++j )
        {
          uint64_t val = cof & mask;

          if ( val == fs_fun[2] )
          {
            isets1[0]._bits |= UINT64_C( 1 ) << ( j + offset );
          }
          else
          {
            isets1[1]._bits |= UINT64_C( 1 ) << ( j + offset );
            fs_fun[3] = val;
          }

          cof >>= shift;
        }

        offset = ( offset + ( 64 >> best_free_set ) ) % 64;
      }
    }

    /* find the support minimizing combination with shared set */
    compute_functions( isets0, isets1, fs_fun, n );

    /* print functions */
    if ( verbose )
    {
      LTT f;
      f._bits = dec_funcs[0];
      std::cout << "BS function         : ";
      kitty::print_hex( f );
      std::cout << "\n";
      f._bits = dec_funcs[1];
      std::cout << "Composition function: ";
      kitty::print_hex( f );
      std::cout << "\n";
    }
  }

  inline void compute_functions_top( STT isets0[2], STT isets1[2], uint64_t fs_fun[4], uint32_t n )
  {
    /* u = 2 no support minimization */
    if ( best_multiplicity < 3 )
    {
      shared_vars[1] = UINT32_MAX;
      remainder = isets0[0];
      rm_support_size = n - best_free_set;
      for ( uint32_t i = 0; i < n - best_free_set; ++i )
      {
        rm_support[i] = permutations[i + best_free_set];
      }
      compute_composition( fs_fun, 2 );
      return;
    }

    shared_vars[1] = permutations[n - 1];

    /* u = 4 two possibilities */
    if ( best_multiplicity == 4 )
    {
      compute_functions4_top( isets0, isets1, fs_fun, n );
      return;
    }

    /* u = 3 if both sets have multiplicity 2 there are no don't cares */
    if ( best_multiplicity0 == best_multiplicity1 )
    {
      compute_functions4_top( isets0, isets1, fs_fun, n );
      return;
    }

    /* u = 3 one set has multiplicity 1, use don't cares */
    compute_functions3_top( isets0, isets1, fs_fun, n );
  }

  inline void compute_functions( LTT isets0[2], LTT isets1[2], uint64_t fs_fun[4], uint32_t n )
  {
    /* u = 2 no support minimization */
    if ( best_multiplicity < 3 )
    {
      shared_vars[0] = UINT32_MAX;
      dec_funcs[0] = isets0[0]._bits;
      support_sizes[0] = n - best_free_set;
      for ( uint32_t i = 0; i < n - best_free_set; ++i )
      {
        supports[0][i] = permutations[i + best_free_set];
      }
      compute_composition( fs_fun, 1 );
      return;
    }

    shared_vars[0] = permutations[n - 1];

    /* u = 4 two possibilities */
    if ( best_multiplicity == 4 )
    {
      compute_functions4( isets0, isets1, fs_fun, n );
      return;
    }

    /* u = 3 if both sets have multiplicity 2 there are no don't cares */
    if ( best_multiplicity0 == best_multiplicity1 )
    {
      compute_functions4( isets0, isets1, fs_fun, n );
      return;
    }

    /* u = 3 one set has multiplicity 1, use don't cares */
    compute_functions3( isets0, isets1, fs_fun, n );
  }

  inline void compute_functions4_top( STT isets0[2], STT isets1[2], uint64_t fs_fun[4], uint32_t n )
  {
    STT f;
    uint32_t const num_iset_vars = n - best_free_set;
    uint32_t const num_blocks = 1u << ( num_iset_vars - 6 );

    assert( num_iset_vars > 6 );
    for ( uint32_t i = 0; i < num_blocks; ++i )
    {
      f._bits[i] = isets0[0]._bits[i] | isets1[1]._bits[i];
    }

    /* count the number of support variables */
    uint32_t support_vars1 = 0;
    for ( uint32_t i = 0; i < num_iset_vars; ++i )
    {
      support_vars1 += has_var( f, num_iset_vars, i ) ? 1 : 0;
      rm_support[i] = permutations[i + best_free_set];
    }

    /* use a different set */
    for ( uint32_t i = 0; i < num_blocks; ++i )
    {
      f._bits[i] = isets0[0]._bits[i] | isets1[0]._bits[i];
    }

    uint32_t support_vars2 = 0;
    for ( uint32_t i = 0; i < n - best_free_set; ++i )
    {
      support_vars2 += has_var( f, num_iset_vars, i ) ? 1 : 0;
    }

    rm_support_size = support_vars2;
    if ( support_vars2 > support_vars1 )
    {
      for ( uint32_t i = 0; i < num_blocks; ++i )
      {
        f._bits[i] = isets0[0]._bits[i] | isets1[1]._bits[i];
      }
      std::swap( fs_fun[2], fs_fun[3] );
      rm_support_size = support_vars1;
    }

    /* move variables */
    if ( rm_support_size < num_iset_vars )
    {
      support_vars1 = 0;
      for ( uint32_t i = 0; i < num_iset_vars; ++i )
      {
        if ( !has_var( f, num_iset_vars, i ) )
        {
          continue;
        }

        if ( support_vars1 < i )
        {
          swap_inplace_local( f, num_iset_vars, support_vars1, i );
        }

        rm_support[support_vars1] = permutations[i + best_free_set];
        ++support_vars1;
      }
    }

    remainder = f;
    compute_composition( fs_fun, 2 );
  }

  inline void compute_functions4( LTT isets0[2], LTT isets1[2], uint64_t fs_fun[4], uint32_t n )
  {
    uint64_t constexpr masks[] = { 0x0, 0x3, 0xF, 0xFF, 0xFFFF, 0xFFFFFFFF, UINT64_MAX };
    LTT f = isets0[0] | isets1[1];
    LTT care;

    assert( n - best_free_set <= 6 );
    care._bits = masks[n - best_free_set];

    /* count the number of support variables */
    uint32_t support_vars1 = 0;
    for ( uint32_t i = 0; i < n - best_free_set; ++i )
    {
      support_vars1 += has_var6( f, care, i ) ? 1 : 0;
      supports[0][i] = permutations[i + best_free_set];
    }

    /* use a different set */
    f = isets0[0] | isets1[0];

    uint32_t support_vars2 = 0;
    for ( uint32_t i = 0; i < n - best_free_set; ++i )
    {
      support_vars2 += has_var6( f, care, i ) ? 1 : 0;
    }

    support_sizes[0] = support_vars2;
    if ( support_vars2 > support_vars1 )
    {
      f = isets0[0] | isets1[1];
      std::swap( fs_fun[2], fs_fun[3] );
      support_sizes[0] = support_vars1;
    }

    /* move variables */
    if ( support_sizes[0] < n - best_free_set )
    {
      support_vars1 = 0;
      for ( uint32_t i = 0; i < n - best_free_set; ++i )
      {
        if ( !has_var6( f, care, i ) )
        {
          continue;
        }

        if ( support_vars1 < i )
        {
          kitty::swap_inplace( f, support_vars1, i );
        }

        supports[0][support_vars1] = permutations[i + best_free_set];
        ++support_vars1;
      }
    }

    dec_funcs[0] = f._bits;
    compute_composition( fs_fun, 1 );
  }

  inline void compute_functions3_top( STT isets0[2], STT isets1[2], uint64_t fs_fun[4], uint32_t n )
  {
    STT f, care;
    uint32_t const num_iset_vars = n - best_free_set;
    uint32_t const num_blocks = 1u << ( num_iset_vars - 6 );

    assert( num_iset_vars > 6 );
    for ( uint32_t i = 0; i < num_blocks; ++i )
    {
      f._bits[i] = isets0[0]._bits[i] | isets1[0]._bits[i];
    }

    assert( n - best_free_set <= 6 );

    /* init the care set */
    if ( best_multiplicity0 == 1 )
    {
      for ( uint32_t i = 0; i < num_blocks; ++i )
      {
        care._bits[i] = ~( isets0[0]._bits[i] );
      }
      fs_fun[1] = fs_fun[0];
    }
    else
    {
      for ( uint32_t i = 0; i < num_blocks; ++i )
      {
        care._bits[i] = ~( isets1[0]._bits[i] );
      }
      fs_fun[3] = fs_fun[2];
    }

    /* count the number of support variables */
    uint32_t support_vars = 0;
    for ( uint32_t i = 0; i < num_iset_vars; ++i )
    {
      if ( !has_var_support( f, care, num_iset_vars, i ) )
      {
        adjust_truth_table_on_dc( f, care, n, i );
        continue;
      }

      if ( support_vars < i )
      {
        kitty::swap_inplace( f, support_vars, i );
      }

      rm_support[support_vars] = permutations[i + best_free_set];
      ++support_vars;
    }

    rm_support_size = support_vars;
    remainder = f;
    compute_composition( fs_fun, 2 );
  }

  inline void compute_functions3( LTT isets0[2], LTT isets1[2], uint64_t fs_fun[4], uint32_t n )
  {
    uint64_t constexpr masks[] = { 0x0, 0x3, 0xF, 0xFF, 0xFFFF, 0xFFFFFFFF, UINT64_MAX };
    LTT f = isets0[0] | isets1[0];
    LTT care;

    assert( n - best_free_set <= 6 );

    /* init the care set */
    if ( best_multiplicity0 == 1 )
    {
      care._bits = masks[n - best_free_set] & ( ~isets0[0]._bits );
      fs_fun[1] = fs_fun[0];
    }
    else
    {
      care._bits = masks[n - best_free_set] & ( ~isets1[0]._bits );
      fs_fun[3] = fs_fun[2];
    }

    /* count the number of support variables */
    uint32_t support_vars = 0;
    for ( uint32_t i = 0; i < n - best_free_set; ++i )
    {
      if ( !has_var6( f, care, i ) )
      {
        adjust_truth_table_on_dc6( f, care, i );
        continue;
      }

      if ( support_vars < i )
      {
        kitty::swap_inplace( f, support_vars, i );
      }

      supports[0][support_vars] = i;
      ++support_vars;
    }

    support_sizes[0] = support_vars;
    dec_funcs[0] = f._bits;
    compute_composition( fs_fun, 1 );
  }

  void compute_composition( uint64_t fs_fun[4], uint32_t index )
  {
    dec_funcs[index] = fs_fun[0] << ( 1 << best_free_set );
    dec_funcs[index] |= fs_fun[1];

    if ( best_multiplicity > 2 )
    {
      dec_funcs[index] |= fs_fun[2] << ( ( 2 << best_free_set ) + ( 1 << best_free_set ) );
      dec_funcs[index] |= fs_fun[3] << ( 2 << best_free_set );
    }

    for ( uint32_t i = 0; i < best_free_set; ++i )
    {
      supports[index][i] = permutations[i];
    }
    support_sizes[index] = best_free_set;
  }

  void fix_permutations_remainder( uint32_t n )
  {
    for ( uint32_t i = 0; i < n; ++i )
    {
      permutations[i] = rm_support[permutations[i]];
    }
  }

  template<typename TT_type>
  void local_extend_to( TT_type& tt, uint32_t real_num_vars )
  {
    if ( real_num_vars < 6 )
    {
      auto mask = *tt.begin();

      for ( auto i = real_num_vars; i < num_vars; ++i )
      {
        mask |= ( mask << ( 1 << i ) );
      }

      std::fill( tt.begin(), tt.end(), mask );
    }
    else
    {
      uint32_t num_blocks = ( 1u << ( real_num_vars - 6 ) );
      auto it = tt.begin();
      while ( it != tt.end() )
      {
        it = std::copy( tt.cbegin(), tt.cbegin() + num_blocks, it );
      }
    }
  }

  void swap_inplace_local( STT& tt, uint32_t n, uint8_t var_index1, uint8_t var_index2 )
  {
    if ( var_index1 == var_index2 )
    {
      return;
    }

    if ( var_index1 > var_index2 )
    {
      std::swap( var_index1, var_index2 );
    }

    assert( n > 6 );
    const uint32_t num_blocks = 1 << ( n - 6 );

    if ( var_index2 <= 5 )
    {
      const auto& pmask = kitty::detail::ppermutation_masks[var_index1][var_index2];
      const auto shift = ( 1 << var_index2 ) - ( 1 << var_index1 );
      std::transform( std::begin( tt._bits ), std::begin( tt._bits ) + num_blocks, std::begin( tt._bits ),
                      [shift, &pmask]( uint64_t word ) {
                        return ( word & pmask[0] ) | ( ( word & pmask[1] ) << shift ) | ( ( word & pmask[2] ) >> shift );
                      } );
    }
    else if ( var_index1 <= 5 ) /* in this case, var_index2 > 5 */
    {
      const auto step = 1 << ( var_index2 - 6 );
      const auto shift = 1 << var_index1;
      auto it = std::begin( tt._bits );
      while ( it != std::begin( tt._bits ) + num_blocks )
      {
        for ( auto i = decltype( step ){ 0 }; i < step; ++i )
        {
          const auto low_to_high = ( *( it + i ) & kitty::detail::projections[var_index1] ) >> shift;
          const auto high_to_low = ( *( it + i + step ) << shift ) & kitty::detail::projections[var_index1];
          *( it + i ) = ( *( it + i ) & ~kitty::detail::projections[var_index1] ) | high_to_low;
          *( it + i + step ) = ( *( it + i + step ) & kitty::detail::projections[var_index1] ) | low_to_high;
        }
        it += 2 * step;
      }
    }
    else
    {
      const auto step1 = 1 << ( var_index1 - 6 );
      const auto step2 = 1 << ( var_index2 - 6 );
      auto it = std::begin( tt._bits );
      while ( it != std::begin( tt._bits ) + num_blocks )
      {
        for ( auto i = 0; i < step2; i += 2 * step1 )
        {
          for ( auto j = 0; j < step1; ++j )
          {
            std::swap( *( it + i + j + step1 ), *( it + i + j + step2 ) );
          }
        }
        it += 2 * step2;
      }
    }
  }

  inline bool has_var6( const LTT& tt, const LTT& care, uint8_t var_index )
  {
    if ( ( ( ( tt._bits >> ( uint64_t( 1 ) << var_index ) ) ^ tt._bits ) & kitty::detail::projections_neg[var_index] & ( care._bits >> ( uint64_t( 1 ) << var_index ) ) & care._bits ) != 0 )
    {
      return true;
    }

    return false;
  }

  inline bool has_var( const STT& tt, uint32_t n, uint8_t var_index )
  {
    uint32_t const num_blocks = 1u << ( n - 6 );

    if ( var_index < 6 )
    {
      return std::any_of( std::begin( tt._bits ), std::begin( tt._bits ) + num_blocks,
                          [var_index]( uint64_t word ) { return ( ( word >> ( uint64_t( 1 ) << var_index ) ) & kitty::detail::projections_neg[var_index] ) !=
                                                                ( word & kitty::detail::projections_neg[var_index] ); } );
    }

    const auto step = 1 << ( var_index - 6 );
    for ( auto i = 0u; i < num_blocks; i += 2 * step )
    {
      for ( auto j = 0; j < step; ++j )
      {
        if ( tt._bits[i + j] != tt._bits[i + j + step] )
        {
          return true;
        }
      }
    }
    return false;
  }

  bool has_var_support( const STT& tt, const STT& care, uint32_t real_num_vars, uint8_t var_index )
  {
    assert( var_index < real_num_vars );
    assert( real_num_vars <= tt.num_vars() );
    assert( tt.num_vars() == care.num_vars() );

    const uint32_t num_blocks = real_num_vars <= 6 ? 1 : ( 1 << ( real_num_vars - 6 ) );
    if ( real_num_vars <= 6 || var_index < 6 )
    {
      auto it_tt = std::begin( tt._bits );
      auto it_care = std::begin( care._bits );
      while ( it_tt != std::begin( tt._bits ) + num_blocks )
      {
        if ( ( ( ( *it_tt >> ( uint64_t( 1 ) << var_index ) ) ^ *it_tt ) & kitty::detail::projections_neg[var_index] & ( *it_care >> ( uint64_t( 1 ) << var_index ) ) & *it_care ) != 0 )
        {
          return true;
        }
        ++it_tt;
        ++it_care;
      }

      return false;
    }

    const auto step = 1 << ( var_index - 6 );
    for ( auto i = 0u; i < num_blocks; i += 2 * step )
    {
      for ( auto j = 0; j < step; ++j )
      {
        if ( ( ( tt._bits[i + j] ^ tt._bits[i + j + step] ) & care._bits[i + j] & care._bits[i + j + step] ) != 0 )
        {
          return true;
        }
      }
    }

    return false;
  }

  void adjust_truth_table_on_dc6( LTT& tt, LTT& care, uint32_t var_index )
  {
    uint64_t new_bits = tt._bits & care._bits;
    tt._bits = ( ( new_bits | ( new_bits >> ( uint64_t( 1 ) << var_index ) ) ) & kitty::detail::projections_neg[var_index] ) |
               ( ( new_bits | ( new_bits << ( uint64_t( 1 ) << var_index ) ) ) & kitty::detail::projections[var_index] );
    care._bits = care._bits | ( care._bits >> ( uint64_t( 1 ) << var_index ) );
  }

  void adjust_truth_table_on_dc( STT& tt, STT& care, uint32_t n, uint32_t var_index )
  {
    assert( var_index < n );
    const uint32_t num_blocks = n <= 6 ? 1 : ( 1 << ( n - 6 ) );

    if ( n <= 6 || var_index < 6 )
    {
      auto it_tt = std::begin( tt._bits );
      auto it_care = std::begin( care._bits );
      while ( it_tt != std::begin( tt._bits ) + num_blocks )
      {
        uint64_t new_bits = *it_tt & *it_care;
        *it_tt = ( ( new_bits | ( new_bits >> ( uint64_t( 1 ) << var_index ) ) ) & kitty::detail::projections_neg[var_index] ) |
                 ( ( new_bits | ( new_bits << ( uint64_t( 1 ) << var_index ) ) ) & kitty::detail::projections[var_index] );
        *it_care = *it_care | ( *it_care >> ( uint64_t( 1 ) << var_index ) );

        ++it_tt;
        ++it_care;
      }
      return;
    }

    const auto step = 1 << ( var_index - 6 );
    for ( auto i = 0u; i < num_blocks; i += 2 * step )
    {
      for ( auto j = 0; j < step; ++j )
      {
        tt._bits[i + j] = ( tt._bits[i + j] & care._bits[i + j] ) | ( tt._bits[i + j + step] & care._bits[i + j + step] );
        tt._bits[i + j + step] = tt._bits[i + j];
        care._bits[i + j] = care._bits[i + j] | care._bits[i + j + step];
        care._bits[i + j + step] = care._bits[i + j];
      }
    }
  }

  /* Decomposition format for ABC
   *
   * The record is an array of unsigned chars where:
   *   - the first unsigned char entry stores the number of unsigned chars in the record
   *   - the second entry stores the number of LUTs
   * After this, several sub-records follow, each representing one LUT as follows:
   *   - an unsigned char entry listing the number of fanins
   *   - a list of fanins, from the LSB to the MSB of the truth table. The N inputs of the original function
   *     have indexes from 0 to N-1, followed by the internal signals in a topological order
   *   - the LUT truth table occupying 2^(M-3) bytes, where M is the fanin count of the LUT, from the LSB to the MSB.
   *     A 2-input LUT, which takes 4 bits, should be stretched to occupy 8 bits (one unsigned char)
   *     A 0- or 1-input LUT can be represented similarly but it is not expected that such LUTs will be represented
   */
  // void get_decomposition_abc( unsigned char* decompArray )
  // {
  //   unsigned char* pArray = decompArray;
  //   unsigned char bytes = 2;

  //   /* write number of LUTs */
  //   pArray++;
  //   *pArray = 2;
  //   pArray++;

  //   /* write BS LUT */
  //   /* write fanin size */
  //   *pArray = bs_support_size;
  //   pArray++;
  //   ++bytes;

  //   /* write support */
  //   for ( uint32_t i = 0; i < bs_support_size; ++i )
  //   {
  //     *pArray = (unsigned char)permutations[bs_support[i] + best_free_set];
  //     pArray++;
  //     ++bytes;
  //   }

  //   /* write truth table */
  //   uint32_t tt_num_bytes = ( bs_support_size <= 3 ) ? 1 : ( 1 << ( bs_support_size - 3 ) );
  //   for ( uint32_t i = 0; i < tt_num_bytes; ++i )
  //   {
  //     *pArray = (unsigned char)( ( dec_funcs[0] >> ( 8 * i ) ) & 0xFF );
  //     pArray++;
  //     ++bytes;
  //   }

  //   /* write top LUT */
  //   /* write fanin size */
  //   uint32_t support_size = best_free_set + 1 + ( best_multiplicity > 2 ? 1 : 0 );
  //   *pArray = support_size;
  //   pArray++;
  //   ++bytes;

  //   /* write support */
  //   for ( uint32_t i = 0; i < best_free_set; ++i )
  //   {
  //     *pArray = (unsigned char)permutations[i];
  //     pArray++;
  //     ++bytes;
  //   }

  //   *pArray = (unsigned char)num_vars;
  //   pArray++;
  //   ++bytes;

  //   if ( best_multiplicity > 2 )
  //   {
  //     *pArray = (unsigned char)permutations[num_vars - 1];
  //     pArray++;
  //     ++bytes;
  //   }

  //   /* write truth table */
  //   tt_num_bytes = ( support_size <= 3 ) ? 1 : ( 1 << ( support_size - 3 ) );
  //   for ( uint32_t i = 0; i < tt_num_bytes; ++i )
  //   {
  //     *pArray = (unsigned char)( ( dec_funcs[1] >> ( 8 * i ) ) & 0xFF );
  //     pArray++;
  //     ++bytes;
  //   }

  //   /* write numBytes */
  //   *decompArray = bytes;
  // }

  bool verify_impl()
  {
    /* create PIs */
    STT pis[max_num_vars];
    for ( uint32_t i = 0; i < num_vars; ++i )
    {
      kitty::create_nth_var( pis[i], i );
    }

    STT bsi[6];
    STT bsf_sim;
    for ( uint32_t lut_i = 0; lut_i < num_luts; ++lut_i )
    {
      for ( uint32_t i = 0; i < support_sizes[lut_i]; ++i )
      {
        bsi[i] = pis[supports[lut_i][i]];
      }

      STT top_sim;
      for ( uint32_t i = 0u; i < ( 1 << num_vars ); ++i )
      {
        uint32_t pattern = 0u;
        for ( auto j = 0; j < support_sizes[lut_i]; ++j )
        {
          pattern |= get_bit( bsi[j], i ) << j;
        }
        if ( lut_i != 0 )
        {
          pattern |= get_bit( bsf_sim, i ) << support_sizes[lut_i];
          if ( shared_vars[lut_i - 1] < UINT32_MAX )
          {
            pattern |= get_bit( pis[shared_vars[lut_i - 1]], i ) << ( support_sizes[lut_i] + 1 );
          }
        }
        if ( ( dec_funcs[lut_i] >> pattern ) & 1 )
        {
          set_bit( top_sim, i );
        }
      }

      bsf_sim = top_sim;
    }

    /* extend function */
    local_extend_to( bsf_sim, num_vars );

    for ( uint32_t i = 0; i < ( 1 << ( num_vars - 6 ) ); ++i )
    {
      if ( bsf_sim._bits[i] != start_tt._bits[i] )
      {
        std::cout << "Found incorrect decomposition\n";
        report_tt( bsf_sim );
        std::cout << " instead_of\n";
        report_tt( start_tt );
        return false;
      }
    }

    return true;
  }

  uint32_t get_bit( const STT& tt, uint64_t index )
  {
    return ( tt._bits[index >> 6] >> ( index & 0x3f ) ) & 0x1;
  }

  void set_bit( STT& tt, uint64_t index )
  {
    tt._bits[index >> 6] |= uint64_t( 1 ) << ( index & 0x3f );
  }

  void report_tt( STT const& stt )
  {
    kitty::dynamic_truth_table tt( num_vars );

    std::copy( std::begin( stt._bits ), std::begin( stt._bits ) + ( 1 << ( num_vars - 6 ) ), std::begin( tt ) );
    kitty::print_hex( tt );
    std::cout << "\n";
  }

private:
  uint32_t best_multiplicity{ UINT32_MAX };
  uint32_t best_free_set{ UINT32_MAX };
  uint32_t best_multiplicity0{ UINT32_MAX };
  uint32_t best_multiplicity1{ UINT32_MAX };
  uint32_t rm_support_size{ UINT32_MAX };
  uint32_t num_luts{ 0 };

  STT start_tt;
  STT best_tt;
  STT remainder;

  uint64_t dec_funcs[3];
  uint32_t supports[3][6];
  uint32_t support_sizes[3] = { UINT32_MAX, UINT32_MAX, UINT32_MAX };
  uint32_t rm_support[15];
  uint32_t shared_vars[2];

  uint32_t const num_vars;
  bool const verify;
  std::array<uint32_t, max_num_vars> permutations;
};

} // namespace acd

ABC_NAMESPACE_CXX_HEADER_END

#endif // _ACD666_H_