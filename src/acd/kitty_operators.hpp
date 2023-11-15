#ifndef _KITTY_OPERATORS_TT_H_
#define _KITTY_OPERATORS_TT_H_
#pragma once

#include <algorithm>
#include <cassert>
#include <functional>
#include <iterator>
#include <optional>

#include "kitty_constants.hpp"
#include "kitty_dynamic_tt.hpp"
#include "kitty_static_tt.hpp"
#include "kitty_operations.hpp"

namespace kitty
{

/*! \brief Operator for unary_not */
inline dynamic_truth_table operator~( const dynamic_truth_table& tt )
{
  return unary_not( tt );
}

/*! \brief Operator for unary_not */
template<uint32_t NumVars>
inline static_truth_table<NumVars> operator~( const static_truth_table<NumVars>& tt )
{
  return unary_not( tt );
}

/*! \brief Operator for binary_and */
inline dynamic_truth_table operator&( const dynamic_truth_table& first, const dynamic_truth_table& second )
{
  return binary_and( first, second );
}

/*! \brief Operator for binary_and */
template<uint32_t NumVars>
inline static_truth_table<NumVars> operator&( const static_truth_table<NumVars>& first, const static_truth_table<NumVars>& second )
{
  return binary_and( first, second );
}

/*! \brief Operator for binary_and and assign */
inline void operator&=( dynamic_truth_table& first, const dynamic_truth_table& second )
{
  first = binary_and( first, second );
}

/*! \brief Operator for binary_and and assign */
template<uint32_t NumVars>
inline void operator&=( static_truth_table<NumVars>& first, const static_truth_table<NumVars>& second )
{
  first = binary_and( first, second );
}

/*! \brief Operator for binary_or */
inline dynamic_truth_table operator|( const dynamic_truth_table& first, const dynamic_truth_table& second )
{
  return binary_or( first, second );
}

/*! \brief Operator for binary_or */
template<uint32_t NumVars>
inline static_truth_table<NumVars> operator|( const static_truth_table<NumVars>& first, const static_truth_table<NumVars>& second )
{
  return binary_or( first, second );
}

/*! \brief Operator for binary_or and assign */
inline void operator|=( dynamic_truth_table& first, const dynamic_truth_table& second )
{
  first = binary_or( first, second );
}

/*! \brief Operator for binary_or and assign */
template<uint32_t NumVars>
inline void operator|=( static_truth_table<NumVars>& first, const static_truth_table<NumVars>& second )
{
  first = binary_or( first, second );
}

} // namespace kitty

#endif // _KITTY_OPERATORS_TT_H_