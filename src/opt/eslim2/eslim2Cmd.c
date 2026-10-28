/**CFile****************************************************************

  FileName    [eslim2Cmd.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based local improvement of AIGs.]

  Synopsis    [Command interface to the experimental eSLIM2 package.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - October 2026.]

***********************************************************************/

#include <errno.h>
#include <limits.h>

#include "base/main/main.h"
#include "misc/extra/extra.h"
#include "eSLIM2.h"

ABC_NAMESPACE_IMPL_START

/**Function*************************************************************

  Synopsis    [Reads an unsigned command-line argument without wrapping.]

  SideEffects []

***********************************************************************/

static int Es2_ReadUnsigned( const char * pText, unsigned int * pValue )
{
    char * pEnd;
    unsigned long Value;
    if ( *pText == '-' )
        return 0;
    errno = 0;
    Value = strtoul( pText, &pEnd, 10 );
    if ( pText == pEnd || *pEnd || errno == ERANGE || Value > UINT_MAX )
        return 0;
    *pValue = (unsigned int)Value;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Optimizes the current AIG using the eSLIM2 package.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/

int Abc_CommandAbc9eSLIM2( Abc_Frame_t * pAbc, int argc, char ** argv ) {
  extern void seteSLIM2Params(eSLIM2_ParamStruct* params);
  extern Gia_Man_t* applyeSLIM2(Gia_Man_t * pGia, const eSLIM2_ParamStruct* params);

  eSLIM2_ParamStruct params;
  int c;
  Gia_Man_t * pTemp;
  seteSLIM2Params(&params);
  params.aig = 1;
  Extra_UtilGetoptReset();
  while ( ( c = Extra_UtilGetopt( argc, argv, "ABCDEIJPRSTVWXZcefghilmqstx" ) ) != EOF ) {
      switch ( c ) {
        case 'J':
          if (globalUtilOptind >= argc || !Es2_ReadUnsigned(argv[globalUtilOptind++], &params.rewrite_mode) || params.rewrite_mode > 2)
            goto usage;
          break;
        case 'A':
          if (globalUtilOptind >= argc || !Es2_ReadUnsigned(argv[globalUtilOptind++], &params.aig_encoding) || params.aig_encoding > 2)
            goto usage;
          break;
        case 'l':
          params.initial_depth_bound ^= 1;
          break;
        case 'm':
          params.mux_consensus ^= 1;
          break;
        case 'g':
          params.fast_simulation ^= 1;
          break;
        case 'q':
          params.tune_relation_solver ^= 1;
          break;
        case 'B':
          if (globalUtilOptind >= argc || !Es2_ReadUnsigned(argv[globalUtilOptind++], &params.synthesis_timeout_ms))
            goto usage;
          break;
        case 'e':
          params.compact_timing ^= 1;
          break;
        case 'C':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
              goto usage;
          }
          params.approximate_relation = 1;
          params.relation_tfo_bound  = atoi(argv[globalUtilOptind]);
          globalUtilOptind++;
          if ( params.relation_tfo_bound < 0 )
              goto usage;
          if (globalUtilOptind < argc) {
            char *next;
            int tfi_bound = strtol (argv[globalUtilOptind], &next, 10);
            if (argv[globalUtilOptind] != next && *next == '\0') {
              params.generate_relation_with_tfi_limit = 1;
              params.relation_tfi_bound = tfi_bound;
              globalUtilOptind++;
              if (params.relation_tfi_bound < 0) {
                goto usage;
              }
            }
          }
          break;
        case 'D':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
              goto usage;
          }
          params.synthesis_approach = atoi(argv[globalUtilOptind]);
          globalUtilOptind++;
          if ( params.synthesis_approach < 0 ||  params.synthesis_approach > 3)
              goto usage;
          break;
        case 'I':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
              goto usage;
          }
          if ( !Es2_ReadUnsigned(argv[globalUtilOptind], &params.iterations) )
              goto usage;
          globalUtilOptind++;
          break;
        case 'P':
          if (globalUtilOptind >= argc || !Es2_ReadUnsigned(argv[globalUtilOptind++], &params.ncores) || !params.ncores) {
            Abc_Print( -1, "Command line switch \"-P\" requires a positive integer core limit.\n" );
            goto usage;
          }
          break;
        case 'E':
        {
          char * pEnd;
          const char * pText;
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-E\" should be followed by a probability.\n" );
              goto usage;
          }
          pText = argv[globalUtilOptind++];
          errno = 0;
          params.expansion_probability = strtod(pText, &pEnd);
          if (pText == pEnd || *pEnd || errno == ERANGE ||
              !(params.expansion_probability > 0 && params.expansion_probability <= 1))
              goto usage;
          break;
        }
        case 'R':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
              goto usage;
          }
          if ( !Es2_ReadUnsigned(argv[globalUtilOptind], &params.nruns) )
              goto usage;
          globalUtilOptind++;
          if ( params.nruns < 1 )
              goto usage;
          break;
        case 'S':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
              goto usage;
          }
          if ( !Es2_ReadUnsigned(argv[globalUtilOptind], &params.subcircuit_max_size) )
              goto usage;
          globalUtilOptind++;
          if ( params.subcircuit_max_size < 2 )
              goto usage;
          break;
        case 'T':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
              goto usage;
          }
          if ( !Es2_ReadUnsigned(argv[globalUtilOptind], &params.timeout) )
              goto usage;
          globalUtilOptind++;
          if ( params.timeout < 1 )
              goto usage;
          break;
        case 'V':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-V\" should be followed by an integer.\n" );
              goto usage;
          }
          params.verbosity_level = atoi(argv[globalUtilOptind]);
          globalUtilOptind++;
          if ( params.verbosity_level < 0 || params.verbosity_level > 3 )
              goto usage;
          break;
        case 'W':
        {
          unsigned int nWindows, nSize;
          if ( globalUtilOptind + 1 >= argc)
          {
              Abc_Print( -1, "Command line switch \"-W\" should be followed by two integers.\n" );
              goto usage;
          }
          if (!Es2_ReadUnsigned(argv[globalUtilOptind++], &nWindows) || !nWindows || nWindows > INT_MAX ||
              !Es2_ReadUnsigned(argv[globalUtilOptind++], &nSize) || !nSize || nSize > INT_MAX)
            goto usage;
          params.nWindows = (int)nWindows;
          params.window_size = (int)nSize;
          break;
        }
        case 'X':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-X\" should be followed by an integer.\n" );
              goto usage;
          }
          if ( !Es2_ReadUnsigned(argv[globalUtilOptind], &params.additional_gates) )
              goto usage;
          globalUtilOptind++;
          break;
        case 'Z':
          if ( globalUtilOptind >= argc )
          {
              Abc_Print( -1, "Command line switch \"-Z\" should be followed by an integer.\n" );
              goto usage;
          }
          params.fix_seed = 1;
          params.seed = atoi(argv[globalUtilOptind]);
          globalUtilOptind++;
          break;
        case 'c' :
          params.criticial_path_selection_bias ^= 1;
          break;
        case 'f' :
          params.forward_search ^= 1;
          break;
        case 'h':
          goto usage;
        case 'i' :
          params.apply_inprocessing ^= 1;
          break;
        case 's' :
          params.fill_subcircuits ^= 1;
          break;
        case 't' :
          params.use_taboo_list ^= 1;
          break;
        case 'x' :
          params.aig = 0;
          break;
        default:
          goto usage;
      }
  }
  if ((params.nWindows > 0 || params.ncores > 1) && params.synthesis_approach > 1) {
    Abc_Print( -1, "Parallel windows require -D 0 (area) or -D 1 (area with a depth bound).\n" );
    return 1;
  }
  if (params.synthesis_approach == 1 && !params.aig) {
    Abc_Print( -1, "Mode 1 requires AND gates; -x counts XOR nodes rather than their exported AIG cost.\n" );
    return 1;
  }
  if ( Abc_FrameReadGia(pAbc) == NULL ) {
        Abc_Print( -1, "There is no AIG.\n" );
        return 1;
  }

  pTemp = applyeSLIM2(Abc_FrameReadGia(pAbc), &params);
  if (pTemp == NULL) {
    Abc_Print( -1, "eSLIM2 could not process the given circuit.\n" );
    return 1;
  }

  Abc_FrameUpdateGia( pAbc, pTemp );
  return 0;


  usage:
    seteSLIM2Params(&params); // show the correct default values
    Abc_Print( -2, "usage: &eslim2 [-ABCDEIJPRSTVWXZ <num>] [-cefghilmqstx]\n" );
    Abc_Print( -2, "\t           circuit optimization using exact synthesis and the SAT-based local improvement method (SLIM)\n" );
    Abc_Print( -2, "\t-A <num> : AIG encoding in mode 1: 0 = generic, 1 = ordered pins, 2 = ordered pins and gates [default = %u]\n", params.aig_encoding );
    Abc_Print( -2, "\t-B <num> : base SAT-call budget in milliseconds for mode 1 (0 = legacy allocation) [default = %u]\n", params.synthesis_timeout_ms );
    Abc_Print( -2, "\t           Existing-size searches receive 4x this budget; every 16th search receives another 10x.\n" );
    Abc_Print( -2, "\t-C <num> : approximate Boolean relations by only considering the first C levels in the cone \n");
    Abc_Print( -2, "\t-D <num> : delay mode: 0 = area, 1 = area with depth bound, 2 = area then depth, 3 = depth [default = %d]\n",  params.synthesis_approach );
    Abc_Print( -2, "\t           Mode 1 keeps both exported AIG node count and level count at most their input values.\n" );
    Abc_Print( -2, "\t           Area mode (0), including windows, may increase levels. Use mode 1 to preserve the input bound.\n" );
    Abc_Print( -2, "\t-E <prob>: the probability of expanding a node (formerly -P) [default = %.2f]\n", params.expansion_probability );
    Abc_Print( -2, "\t-I <num> : the maximal number of iterations (0 = no limit) for the individual eSLIM2 runs [default = %d]\n",  params.iterations  );
    Abc_Print( -2, "\t-J <num> : AIG rewriting in mode 1: 0 = off, 1 = initial, 2 = adaptive [default = %u]\n", params.rewrite_mode );
    Abc_Print( -2, "\t           Adaptive repeats every 2 seconds only if the initial pass removed nodes.\n" );
    Abc_Print( -2, "\t           Rewriting preserves size and depth and is disabled by -i.\n" );
    Abc_Print( -2, "\t           Windows disable -J and strash in both modes; -i controls final inprocessing.\n" );
    Abc_Print( -2, "\t-P <num> : maximum number of worker cores; 1 uses the serial command [default = %u]\n", params.ncores );
    Abc_Print( -2, "\t           More cores use automatic windows in modes 0/1; small designs may use fewer.\n" );
    Abc_Print( -2, "\t-R <num> : the number of runs of eSLIM2 + Inprocessing [default = %d]\n",    params.nruns );
    Abc_Print( -2, "\t-S <num> : the maximal size of considered subcircuits [default = %d]\n",    params.subcircuit_max_size );
    Abc_Print( -2, "\t-T <num> : the timeout in seconds for the individual eSLIM2 runs [default = %d]\n",    params.timeout );
    Abc_Print( -2, "\t-V <num> : the verbosity level [default = %d]\n",       params.verbosity_level);
    Abc_Print( -2, "\t           Level 1 includes search/cache counters; level 2 adds SAT-call timings; level 3 adds per-size details.\n" );
    Abc_Print( -2, "\t-W <m> <n>: select up to m windows of n nodes instead of automatic partitioning\n" );
    Abc_Print( -2, "\t           Windows share the -T budget and use at most -P cores; -I applies per window.\n" );
    Abc_Print( -2, "\t-X <num> : the maximal number of additional gates that may be used for depth optimization [default = %d]\n", params.additional_gates);
    Abc_Print( -2, "\t-Z <num> : use a fixed seed\n");
    Abc_Print( -2, "\t-c       : toggle bias for selection of nodes on the critical path\n");
    Abc_Print( -2, "\t-e       : toggle compact encoding of the depth bound in mode 1 [default = %s]\n", params.compact_timing ? "yes" : "no" );
    Abc_Print( -2, "\t-f       : toggle forward expansion of root nodes\n");
    Abc_Print( -2, "\t-g       : toggle specialized gate simulation and Gray-code traversal [default = %s]\n", params.fast_simulation ? "yes" : "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    Abc_Print( -2, "\t-i       : toggle inprocessing (disabling it also disables mode-1 rewriting)\n");
    Abc_Print( -2, "\t-l       : toggle keeping the initial depth bound throughout mode 1 [default = %s]\n", params.initial_depth_bound ? "yes" : "no" );
    Abc_Print( -2, "\t           With this enabled, intermediate depth gains may be traded for area within the input depth.\n" );
    Abc_Print( -2, "\t-m       : toggle redundant mux clauses for two-input gates [default = %s]\n", params.mux_consensus ? "yes" : "no" );
    Abc_Print( -2, "\t-q       : toggle relation SAT tuning (disable lucky phases) [default = %s]\n", params.tune_relation_solver ? "yes" : "no" );
    Abc_Print( -2, "\t-s       : toggle fill subcircuits\n");
    Abc_Print( -2, "\t-t       : toggle use taboo list\n");
    Abc_Print( -2, "\t-x       : allow xor-gates (not supported with -D 1)\n");
    Abc_Print( -2, "\t\n" );
    Abc_Print( -2, "\t           This command was contributed by Franz-Xaver Reichl from University of Freiburg.\n" );

    return 1;

}

ABC_NAMESPACE_IMPL_END
