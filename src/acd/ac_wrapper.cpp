// #include "base/main/main.h"
#include "ac_wrapper.h"
#include "ac_decomposition.hpp"

// ABC_NAMESPACE_IMPL_START

int acd_evaluate( word * pTruth, unsigned nVars, int lutSize, unsigned *pdelay, unsigned *cost )
{
  using namespace mockturtle;

  int num_blocks = ( nVars <= 6 ) ? 1 : ( 1 << ( nVars - 6 ) );

  /* translate truth table into static table */
  kitty::dynamic_truth_table tt( nVars );
  for ( int i = 0; i < num_blocks; ++i )
    tt._bits[i] = pTruth[i];

  ac_decomposition_params ps;
  ps.lut_size = lutSize;
  ac_decomposition_stats st;

  ac_decomposition_impl acd( tt, nVars, ps, &st );
  int val = acd.run( *pdelay );
  // int val = acd.compute_decomposition();

  if ( val < 0 )
  {
    *pdelay = 0;
    return -1;
  }

  *pdelay = acd.get_profile();
  *cost = st.num_luts;

  return 0;
}

int acd_decompose( word * pTruth, unsigned nVars, int lutSize, unsigned *pdelay, unsigned char *decomposition )
{
  using namespace mockturtle;

  int num_blocks = ( nVars <= 6 ) ? 1 : ( 1 << ( nVars - 6 ) );

  /* translate truth table into static table */
  kitty::dynamic_truth_table tt( nVars );
  for ( int i = 0; i < num_blocks; ++i )
    tt._bits[i] = pTruth[i];

  ac_decomposition_params ps;
  ps.lut_size = lutSize;
  ac_decomposition_stats st;

  ac_decomposition_impl acd( tt, nVars, ps, &st );
  acd.run( *pdelay );
  int val = acd.compute_decomposition();

  if ( val < 0 )
  {
    *pdelay = 0;
    return -1;
  }

  *pdelay = acd.get_profile();

  acd.get_decomposition( decomposition );
  return 0;
}

// ABC_NAMESPACE_IMPL_END