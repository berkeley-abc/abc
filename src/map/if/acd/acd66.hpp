/**C++File**************************************************************

  FileName    [acd66.hpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Ashenhurst-Curtis decomposition.]

  Synopsis    [Interface with the FPGA mapping package.]

  Author      [Alessandro Tempia Calvino]

  Affiliation [EPFL]

  Date        [Ver. 1.0. Started - Feb 8, 2024.]

***********************************************************************/
/*!
  \file acd66.hpp
  \brief Ashenhurst-Curtis decomposition for "66" cascade

  \author Alessandro Tempia Calvino
*/

#ifndef _ACD66_H_
#define _ACD66_H_
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

/*! \brief Parameters for acd66 */
struct acd66_params
{
  /*! \brief Maximum size of the free set (1 < num < 6). */
  uint32_t max_free_set_vars{ 5 };

  /*! \brief Number of configurations to test for decomposition. */
  uint32_t max_evaluations{ 3 };

  /*! \brief Run verification before returning. */
  bool verify{ false };
};

/*! \brief Statistics for acd66 */
struct acd66_stats
{
  uint32_t num_edges{ 0 };
};

class acd66_impl
{
private:
  static constexpr uint32_t max_num_vars = 11;
  using STT = kitty::static_truth_table<max_num_vars>;
  using LTT = kitty::static_truth_table<6>;

public:
  explicit acd66_impl( uint32_t num_vars, acd66_params const& ps, acd66_stats* pst = nullptr )
      : num_vars( num_vars ), ps( ps ), pst( pst )
  {
    std::iota( permutations.begin(), permutations.end(), 0 );
  }

  /*! \brief Runs ACD 66 */
  int run( word* ptt )
  {
    assert( num_vars > 6 );

    /* truth table is too large for the settings */
    if ( num_vars > max_num_vars || num_vars > 11 )
    {
      return -1;
    }

    /* convert to static TT */
    init_truth_table( ptt );

    /* run ACD trying different bound sets and free sets */
    return find_decomposition() ? 1 : 0;
  }

  int compute_decomposition()
  {
    if ( best_multiplicity == UINT32_MAX )
      return -1;

    compute_decomposition_impl();

    if ( ps.verify && !verify_impl() )
    {
      return 1;
    }

    if ( pst )
    {
      pst->num_edges = bs_support_size + best_free_set + 1 + ( best_multiplicity > 2 ? 1 : 0 );
    }

    return 0;
  }

  /* contains a 1 for BS variables */
  unsigned get_profile()
  {
    unsigned profile = 0;

    if ( bs_support_size == UINT32_MAX )
      return -1;

    for ( uint32_t i = 0; i < bs_support_size; ++i )
    {
      profile |= 1 << permutations[best_free_set + bs_support[i]];
    }

    return profile;
  }

  void get_decomposition( unsigned char* decompArray )
  {
    if ( bs_support_size == UINT32_MAX )
      return;

    get_decomposition_abc( decompArray );
  }

private:
  bool find_decomposition()
  {
    best_multiplicity = UINT32_MAX;
    best_free_set = UINT32_MAX;

    /* find AC decompositions with minimal multiplicity */
    for ( uint32_t i = num_vars - 6; i <= 5 && i <= ps.max_free_set_vars; ++i )
    {
      if ( find_decomposition_bs( i ) )
        return true;
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

  uint32_t column_multiplicity( STT const& tt, uint32_t free_set_size )
  {
    assert( free_set_size <= 5 );

    uint32_t const num_blocks = ( num_vars > 6 ) ? ( 1u << ( num_vars - 6 ) ) : 1;
    uint64_t shift = UINT64_C( 1 ) << free_set_size;
    uint64_t mask = ( UINT64_C( 1 ) << shift ) - 1;
    uint32_t cofactors[4];
    uint32_t size = 0;

    /* extract iset functions */
    auto it = std::begin( tt );
    for ( auto i = 0u; i < num_blocks; ++i )
    {
      uint64_t sub = *it;
      for ( auto j = 0; j < ( 64 >> free_set_size ); ++j )
      {
        uint32_t fs_fn = static_cast<uint32_t>( sub & mask );
        uint32_t k;
        for ( k = 0; k < size; ++k )
        {
          if ( fs_fn == cofactors[k] )
            break;
        }
        if ( k == 4 )
          return 5;
        if ( k == size )
          cofactors[size++] = fs_fn;
        sub >>= shift;
      }
      ++it;
    }

    return size;
  }

  inline bool combinations_next( uint32_t k, uint32_t* pComb, uint32_t* pInvPerm, STT& tt )
  {
    uint32_t i;

    for ( i = k - 1; pComb[i] == num_vars - k + i; --i )
    {
      if ( i == 0 )
        return false;
    }

    /* move vars */
    uint32_t var_old = pComb[i];
    uint32_t pos_new = pInvPerm[var_old + 1];
    std::swap( pInvPerm[var_old + 1], pInvPerm[var_old] );
    std::swap( pComb[i], pComb[pos_new] );
    swap_inplace_local( tt, i, pos_new );

    for ( uint32_t j = i + 1; j < k; j++ )
    {
      var_old = pComb[j];
      pos_new = pInvPerm[pComb[j - 1] + 1];
      std::swap( pInvPerm[pComb[j - 1] + 1], pInvPerm[var_old] );
      std::swap( pComb[j], pComb[pos_new] );
      swap_inplace_local( tt, j, pos_new );
    }

    return true;
  }

  bool find_decomposition_bs( uint32_t free_set_size )
  {
    STT tt = start_tt;

    /* works up to 16 input truth tables */
    assert( num_vars <= 16 );

    /* init combinations */
    uint32_t pComb[16], pInvPerm[16];
    for ( uint32_t i = 0; i < num_vars; ++i )
    {
      pComb[i] = pInvPerm[i] = i;
    }

    /* enumerate combinations */
    best_free_set = free_set_size;
    do
    {
      uint32_t cost = column_multiplicity( tt, free_set_size );
      if ( cost == 2 )
      {
        best_tt = tt;
        best_multiplicity = cost;
        for ( uint32_t i = 0; i < num_vars; ++i )
        {
          permutations[i] = pComb[i];
        }
        return true;
      }
      else if ( cost <= 4 && free_set_size < 5 )
      {
        /* look for a shared variable */
        best_multiplicity = cost;
        int res = check_shared_set( tt );

        if ( res > 0 )
        {
          best_tt = tt;
          for ( uint32_t i = 0; i < num_vars; ++i )
          {
            permutations[i] = pComb[i];
          }
          /* move shared variable as the most significative one */
          swap_inplace_local( best_tt, res, num_vars - 1 );
          std::swap( permutations[res], permutations[num_vars - 1] );
          return true;
        }
      }
    } while ( combinations_next( free_set_size, pComb, pInvPerm, tt ) );

    return false;
  }

  bool check_shared_var( STT const& tt, uint32_t free_set_size, uint32_t shared_var )
  {
    assert( free_set_size <= 5 );

    uint32_t const num_blocks = ( num_vars > 6 ) ? ( 1u << ( num_vars - 6 ) ) : 1;
    uint64_t shift = UINT64_C( 1 ) << free_set_size;
    uint64_t mask = ( UINT64_C( 1 ) << shift ) - 1;
    uint32_t cofactors[2][4];
    uint32_t size[2] = { 0, 0 };
    uint32_t shared_var_shift = shared_var - free_set_size;

    /* extract iset functions */
    uint32_t iteration_counter = 0;
    auto it = std::begin( tt );
    for ( auto i = 0u; i < num_blocks; ++i )
    {
      uint64_t sub = *it;
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
      ++it;
    }

    return true;
  }

  inline int check_shared_set( STT const& tt )
  {
    /* find one shared set variable */
    for ( uint32_t i = best_free_set; i < num_vars; ++i )
    {
      /* check the multiplicity of cofactors */
      if ( check_shared_var( tt, best_free_set, i ) )
      {
        return i;
      }
    }

    return -1;
  }

  void compute_decomposition_impl( bool verbose = false )
  {
    bool has_shared_set = best_multiplicity > 2;

    /* construct isets involved in multiplicity */
    LTT isets0[2];
    LTT isets1[2];

    /* construct isets */
    STT tt = best_tt;
    uint32_t offset = 0;
    uint32_t num_blocks = ( num_vars > 6 ) ? ( 1u << ( num_vars - 6 ) ) : 1;
    uint64_t constexpr masks[] = { 0x0, 0x3, 0xF, 0xFF, 0xFFFF, 0xFFFFFFFF };

    /* limit analysis on 0 cofactor of the shared variable */
    if ( has_shared_set )
      num_blocks >>= 1;

    auto it = std::begin( tt );
    uint64_t fs_fun[4] = { *it & masks[best_free_set], 0, 0, 0 };

    for ( auto i = 0u; i < num_blocks; ++i )
    {
      for ( auto j = 0; j < ( 64 >> best_free_set ); ++j )
      {
        uint64_t val = *it & masks[best_free_set];

        if ( val == fs_fun[0] )
        {
          isets0[0]._bits |= UINT64_C( 1 ) << ( j + offset );
        }
        else
        {
          isets0[1]._bits |= UINT64_C( 1 ) << ( j + offset );
          fs_fun[1] = val;
        }

        *it >>= ( 1u << best_free_set );
      }

      offset = ( offset + ( 64 >> best_free_set ) ) % 64;
      ++it;
    }

    /* continue on the 1 cofactor if shared set */
    if ( has_shared_set )
    {
      fs_fun[2] = *it & masks[best_free_set];
      for ( auto i = num_blocks; i < ( num_blocks << 1 ); ++i )
      {
        for ( auto j = 0; j < ( 64 >> best_free_set ); ++j )
        {
          uint64_t val = *it & masks[best_free_set];

          if ( val == fs_fun[2] )
          {
            isets1[0]._bits |= UINT64_C( 1 ) << ( j + offset );
          }
          else
          {
            isets1[1]._bits |= UINT64_C( 1 ) << ( j + offset );
            fs_fun[3] = val;
          }

          *it >>= ( 1u << best_free_set );
        }

        offset = ( offset + ( 64 >> best_free_set ) ) % 64;
        ++it;
      }
    }

    /* find the support minimizing combination with shared set */
    compute_functions( isets0, isets1, fs_fun );

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

  inline void compute_functions( LTT isets0[2], LTT isets1[2], uint64_t fs_fun[4] )
  {
    /* u = 2 no support minimization */
    if ( best_multiplicity < 3 )
    {
      dec_funcs[0] = isets0[0]._bits;
      bs_support_size = num_vars - best_free_set;
      for ( uint32_t i = 0; i < num_vars - best_free_set; ++i )
      {
        bs_support[i] = i;
      }
      compute_composition( fs_fun );
      return;
    }

    /* u = 4 two possibilities */
    if ( best_multiplicity == 4 )
    {
      compute_functions4( isets0, isets1, fs_fun );
      return;
    }

    /* u = 3 if both sets have multiplicity 2 there are no don't cares */
    if ( best_multiplicity0 == best_multiplicity1 )
    {
      compute_functions4( isets0, isets1, fs_fun );
      return;
    }

    /* u = 3 one set has multiplicity 1, use don't cares */
    compute_functions3( isets0, isets1, fs_fun );
    compute_composition( fs_fun );
  }

  inline void compute_functions4( LTT isets0[2], LTT isets1[2], uint64_t fs_fun[4] )
  {
    uint64_t constexpr masks[] = { 0x0, 0x3, 0xF, 0xFF, 0xFFFF, 0xFFFFFFFF, UINT64_MAX };
    LTT f = isets0[0] | isets1[1];
    LTT care;
    care._bits = masks[num_vars - best_free_set];

    /* count the number of support variables */
    uint32_t support_vars1 = 0;
    for ( uint32_t i = 0; i < num_vars - best_free_set; ++i )
    {
      support_vars1 += has_var6( f, care, i ) ? 1 : 0;
      bs_support[i] = i;
    }

    /* use a different set */
    f = isets0[0] | isets1[0];

    uint32_t support_vars2 = 0;
    for ( uint32_t i = 0; i < num_vars - best_free_set; ++i )
    {
      support_vars2 += has_var6( f, care, i ) ? 1 : 0;
    }

    bs_support_size = support_vars2;
    if ( support_vars2 > support_vars1 )
    {
      f = isets0[0] | isets1[1];
      std::swap( fs_fun[3], fs_fun[4] );
      bs_support_size = support_vars1;
    }

    /* move variables */
    if ( bs_support_size < num_vars - best_free_set )
    {
      support_vars1 = 0;
      for ( uint32_t i = 0; i < num_vars - best_free_set; ++i )
      {
        if ( !has_var6( f, care, i ) )
        {
          adjust_truth_table_on_dc( f, care, i );
          continue;
        }

        if ( support_vars1 < i )
        {
          kitty::swap_inplace( f, support_vars1, i );
        }

        bs_support[support_vars1] = i;
        ++support_vars1;
      }
    }

    dec_funcs[0] = f._bits;
    compute_composition( fs_fun );
  }

  inline void compute_functions3( LTT isets0[2], LTT isets1[2], uint64_t fs_fun[4] )
  {
    uint64_t constexpr masks[] = { 0x0, 0x3, 0xF, 0xFF, 0xFFFF, 0xFFFFFFFF, UINT64_MAX };
    LTT f = isets0[0] | isets1[0];
    LTT care;

    /* init the care set */
    if ( best_multiplicity0 == 1 )
    {
      care._bits = masks[num_vars - best_free_set] & ( ~isets0[0]._bits );
      fs_fun[1] = fs_fun[0];
    }
    else
    {
      care._bits = masks[num_vars - best_free_set] & ( ~isets1[0]._bits );
      fs_fun[3] = fs_fun[2];
    }

    /* count the number of support variables */
    uint32_t support_vars = 0;
    for ( uint32_t i = 0; i < num_vars - best_free_set; ++i )
    {
      if ( !has_var6( f, care, i ) )
      {
        adjust_truth_table_on_dc( f, care, i );
        continue;
      }

      if ( support_vars < i )
      {
        kitty::swap_inplace( f, support_vars, i );
      }

      bs_support[support_vars] = i;
      ++support_vars;
    }

    bs_support_size = support_vars;
    dec_funcs[0] = f._bits;
    compute_composition( fs_fun );
  }

  void compute_composition( uint64_t fs_fun[4] )
  {
    dec_funcs[1] = fs_fun[0] << ( 1 << best_free_set );
    dec_funcs[1] |= fs_fun[1];

    if ( best_multiplicity > 2 )
    {
      dec_funcs[1] |= fs_fun[2] << ( ( 2 << best_free_set ) + ( 1 << best_free_set ) );
      dec_funcs[1] |= fs_fun[3] << ( 2 << best_free_set );
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

  void swap_inplace_local( STT& tt, uint8_t var_index1, uint8_t var_index2 )
  {
    if ( var_index1 == var_index2 )
    {
      return;
    }

    if ( var_index1 > var_index2 )
    {
      std::swap( var_index1, var_index2 );
    }

    assert( num_vars > 6 );
    const uint32_t num_blocks = 1 << ( num_vars - 6 );

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

  template<typename TT_type>
  bool has_var_support( const TT_type& tt, const TT_type& care, uint32_t real_num_vars, uint8_t var_index )
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

  void adjust_truth_table_on_dc( LTT& tt, LTT& care, uint32_t var_index )
  {
    uint64_t new_bits = tt._bits & care._bits;
    tt._bits = ( ( new_bits | ( new_bits >> ( uint64_t( 1 ) << var_index ) ) ) & kitty::detail::projections_neg[var_index] ) |
               ( ( new_bits | ( new_bits << ( uint64_t( 1 ) << var_index ) ) ) & kitty::detail::projections[var_index] );
    care._bits = care._bits | ( care._bits >> ( uint64_t( 1 ) << var_index ) );
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
  void get_decomposition_abc( unsigned char* decompArray )
  {
    unsigned char* pArray = decompArray;
    unsigned char bytes = 2;

    /* write number of LUTs */
    pArray++;
    *pArray = 2;
    pArray++;

    /* write BS LUT */
    /* write fanin size */
    *pArray = bs_support_size;
    pArray++;
    ++bytes;

    /* write support */
    for ( uint32_t i = 0; i < bs_support_size; ++i )
    {
      *pArray = (unsigned char)permutations[bs_support[i] + best_free_set];
      pArray++;
      ++bytes;
    }

    /* write truth table */
    uint32_t tt_num_bytes = ( bs_support_size <= 3 ) ? 1 : ( 1 << ( bs_support_size - 3 ) );
    for ( uint32_t i = 0; i < tt_num_bytes; ++i )
    {
      *pArray = (unsigned char)( ( dec_funcs[0] >> ( 8 * i ) ) & 0xFF );
      pArray++;
      ++bytes;
    }

    /* write top LUT */
    /* write fanin size */
    uint32_t support_size = best_free_set + 1 + ( best_multiplicity > 2 ? 1 : 0 );
    *pArray = support_size;
    pArray++;
    ++bytes;

    /* write support */
    for ( uint32_t i = best_free_set; i < best_free_set; ++i )
    {
      *pArray = (unsigned char)permutations[i];
      pArray++;
      ++bytes;
    }

    *pArray = (unsigned char)num_vars;
    pArray++;
    ++bytes;

    if ( best_multiplicity > 2 )
    {
      *pArray = (unsigned char)permutations[num_vars - 1];
      pArray++;
      ++bytes;
    }

    /* write truth table */
    tt_num_bytes = ( support_size <= 3 ) ? 1 : ( 1 << ( support_size - 3 ) );
    for ( uint32_t i = 0; i < tt_num_bytes; ++i )
    {
      *pArray = (unsigned char)( ( dec_funcs[1] >> ( 8 * i ) ) & 0xFF );
      pArray++;
      ++bytes;
    }

    /* write numBytes */
    *decompArray = bytes;
  }

  bool verify_impl()
  {
    /* create PIs */
    STT pis[max_num_vars];
    for ( uint32_t i = 0; i < num_vars; ++i )
    {
      kitty::create_nth_var( pis[i], permutations[i] );
    }

    /* BS function patterns */
    STT bsi[6];
    for ( uint32_t i = 0; i < bs_support_size; ++i )
    {
      bsi[i] = pis[best_free_set + bs_support[i]];
    }

    /* compute first function */
    STT bsf_sim;
    for ( uint32_t i = 0u; i < ( 1 << num_vars ); ++i )
    {
      uint32_t pattern = 0u;
      for ( auto j = 0; j < bs_support_size; ++j )
      {
        pattern |= get_bit( bsi[j], i ) << j;
      }
      if ( ( dec_funcs[0] >> pattern ) & 1 )
      {
        set_bit( bsf_sim, i );
      }
    }

    /* compute first function */
    STT top_sim;
    for ( uint32_t i = 0u; i < ( 1 << num_vars ); ++i )
    {
      uint32_t pattern = 0u;
      for ( auto j = 0; j < best_free_set; ++j )
      {
        pattern |= get_bit( pis[j], i ) << j;
      }
      pattern |= get_bit( bsf_sim, i ) << best_free_set;
      if ( best_multiplicity > 2 )
      {
        pattern |= get_bit( pis[num_vars - 1], i ) << ( best_free_set + 1 );
      }

      if ( ( dec_funcs[1] >> pattern ) & 1 )
      {
        set_bit( top_sim, i );
      }
    }

    for ( uint32_t i = 0; i < ( 1 << ( num_vars - 6 ) ); ++i )
    {
      if ( top_sim._bits[i] != start_tt._bits[i] )
      {
        /* convert to dynamic_truth_table */
        // report_tt( bsf_sim );
        std::cout << "Found incorrect decomposition\n";
        report_tt( top_sim );
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
  uint32_t bs_support_size{ UINT32_MAX };
  STT best_tt;
  STT start_tt;
  uint64_t dec_funcs[2];
  uint32_t bs_support[6];

  uint32_t num_vars;
  acd66_params const& ps;
  acd66_stats* pst;
  std::array<uint32_t, max_num_vars> permutations;
};

} // namespace acd

ABC_NAMESPACE_CXX_HEADER_END

#endif // _ACD66_H_