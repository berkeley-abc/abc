/**CFile****************************************************************

  FileName    [abs2Cmd.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Incremental flop abstraction.]

  Synopsis    [Command interface for bounded flop abstraction.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 21, 2026.]

  Revision    [$Id: abs2Cmd.c,v 1.00 2026/10/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abs2.h"
#include "base/main/mainInt.h"
#include "misc/extra/extra.h"
#include <errno.h>

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Implements the bounded flop-abstraction command.]

  Description [Stores the abstraction map on the current Gia manager. A bounded
  UNSAT prefix is not reported as a safety proof.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abs2_Command( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abs2_Par_t Pars;
    Abc_Cex_t * pEmpty = NULL;
    char * pFile = NULL;
    int c, Result, fDerive = 0, i, nConcrete = 0;
    Abs2_SetDefaultParams( &Pars );
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "FTCSMLKAJRNDQHOprdkmjquvh")) != EOF )
    {
        switch ( c )
        {
        case 'F': case 'T': case 'C': case 'S': case 'M': case 'L': case 'K': case 'A': case 'J': case 'R': case 'N': case 'D': case 'Q': case 'H':
        {
            char * pEnd;
            long Value;
            if ( globalUtilOptind >= argc ) goto usage;
            errno = 0;
            Value = strtol(argv[globalUtilOptind++], &pEnd, 10);
            if ( errno || !argv[globalUtilOptind-1][0] || *pEnd || Value < (c == 'F' ? -1 : 0) || Value > 100000000 ) goto usage;
            if ( c == 'F' ) Pars.nFramesMax = (int)Value;
            if ( c == 'T' ) Pars.nTimeOut = (int)Value;
            if ( c == 'C' ) Pars.nConfLimit = (int)Value;
            if ( c == 'S' ) Pars.nStableMin = (int)Value;
            if ( c == 'M' ) { if ( Value > 8 ) goto usage; Pars.nSatMode = (int)Value; }
            if ( c == 'L' ) { if ( Value > 2 ) goto usage; Pars.nProofMode = (int)Value; }
            if ( c == 'K' ) { if ( Value && (Value < 3 || Value > 6) ) goto usage; Pars.nCutMax = (int)Value; }
            if ( c == 'A' ) { if ( Value > 2 ) goto usage; Pars.nActMode = (int)Value; }
            if ( c == 'J' ) Pars.nCompactDepth = (int)Value;
            if ( c == 'R' ) Pars.nSimplifyEvery = (int)Value;
            if ( c == 'N' ) { if ( Value > 3 ) goto usage; Pars.nCbaOrder = (int)Value; }
            if ( c == 'D' ) { if ( Value > 2 ) goto usage; Pars.nCnfMode = (int)Value; }
            if ( c == 'Q' ) { if ( Value > 5 ) goto usage; Pars.nResolveMode = (int)Value; }
            if ( c == 'H' ) { if ( Value > 3 ) goto usage; Pars.nAssumeOrder = (int)Value; }
            break;
        }
        case 'O': if ( globalUtilOptind >= argc ) goto usage; pFile = argv[globalUtilOptind++]; break;
        case 'p': Pars.fUsePba ^= 1; break;
        case 'r': Pars.fUseStart ^= 1; break;
        case 'd': fDerive ^= 1; break;
        case 'k': Pars.fUseCuts ^= 1; break;
        case 'm': Pars.fMuxProp ^= 1; break;
        case 'j': Pars.fCompactVars ^= 1; break;
        case 'q': Pars.fClauseQuery ^= 1; if ( Pars.fClauseQuery ) Pars.fNativeQuery = 0; break;
        case 'u': Pars.fNativeQuery ^= 1; if ( Pars.fNativeQuery ) Pars.fClauseQuery = 0; break;
        case 'v': Pars.fVerbose ^= 1; break;
        default: goto usage;
        }
    }
    if ( globalUtilOptind != argc ) goto usage;
    if ( Pars.fClauseQuery && Pars.fNativeQuery ) goto usage;
    if ( Pars.nCnfMode && !Pars.fUseCuts )
    {
        Abc_Print(-1, "&abs: directional CNF requires lazy cut encoding.\n");
        return 1;
    }
    if ( Pars.nResolveMode && (!Pars.fUseCuts || Pars.nCnfMode) )
    {
        Abc_Print(-1, "&abs: resolution cuts require lazy encoding and -D 0.\n");
        return 1;
    }
    if ( Pars.nSimplifyEvery && Pars.nSatMode == 3 )
    {
        Abc_Print(-1, "&abs: periodic simplification requires elimination; -M 3 disables it.\n");
        return 1;
    }
    if ( !pAbc->pGia || !Gia_ManPoNum(pAbc->pGia) || Gia_ManConstrNum(pAbc->pGia) )
    {
        Abc_Print( -1, "&abs requires an AIG with bad-state outputs and no constraints (use fold).\n" );
        return 1;
    }
    if ( !Abs2_ManCheckZeroInit(pAbc->pGia) )
    {
        Abc_Print( -1, "&abs requires normalized zero initial states. Load AIGER with &read without -s.\n" );
        return 1;
    }
    Abc_FrameReplaceCex( pAbc, &pEmpty );
    Result = Abs2_ManPerform( pAbc->pGia, &Pars );
    pAbc->Status = Result == 0 ? 0 : -1;
    pAbc->nFrames = Pars.iFrame;
    if ( Result == -2 )
    {
        Abc_Print( -1, "&abs failed; no verification result was accepted.\n" );
        return 1;
    }
    if ( Result == 0 )
    {
        pAbc->nFrames = pAbc->pGia->pCexSeq->iFrame;
        Abc_Print( 1, "abs2 original counterexample simulation: PASS. Output %d asserted in frame %d.\n",
            pAbc->pGia->pCexSeq->iPo, pAbc->pGia->pCexSeq->iFrame );
        Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexSeq );
    }
    else
    {
        for ( i = 0; i < Vec_IntSize(pAbc->pGia->vFlopClasses); ++i )
            nConcrete += Vec_IntEntry(pAbc->pGia->vFlopClasses, i) != 0;
        Abc_Print( 1, "abs2 abstraction: %d/%d concrete registers; bug-free depth %d; %.3f seconds.\n",
            nConcrete, Gia_ManRegNum(pAbc->pGia), Pars.iFrame, Pars.timeTotal );
        if ( pFile || fDerive )
        {
            Gia_Man_t * pAbs = Abs2_ManDerive(pAbc->pGia, pAbc->pGia->vFlopClasses);
            if ( !pAbs ) return 1;
            if ( pFile ) Gia_AigerWrite(pAbs, pFile, 0, 0, 0);
            if ( fDerive ) Abc_FrameUpdateGia(pAbc, pAbs);
            else Gia_ManStop(pAbs);
        }
    }
    if ( Pars.fVerbose )
        Abc_Print( 1, "abs2 profile: calls=%d counterexamples=%d added=%d removed=%d SAT=%.3f refinement=%.3f total=%.3f truth-cuts=%d compact-at=%d simplifies=%d/%.3f reactivations=%d resolve=%d/%d/%d/%.3f minimized=%d/%d memo-hits=%d\n",
            Pars.nCalls, Pars.nCexes, Pars.nAdded, Pars.nRemoved, Pars.timeSat, Pars.timeRefine, Pars.timeTotal, Pars.nTruthCuts, Pars.iCompactFrame, Pars.nSimplifies, Pars.timeSimplify, Pars.nReactivations,
            Pars.nResolveCalls, Pars.nResolveCuts, Pars.nResolvedNodes, Pars.timeResolve, Pars.nMinimizedCuts, Pars.nClausesSaved, Pars.nCnfMemoHits );
    return 0;
usage:
    Abc_Print( -2, "usage: &abs [-FTCSMLKAJRNDQH <num>] [-O <file>] [-prdkmjquvh]\n" );
    Abc_Print( -2, "\t           incremental bounded flop abstraction using CaDiCaL\n" );
    Abc_Print( -2, "\t-F <num>  : last BMC depth, inclusive (-1 = unlimited) [default = %d]\n", Pars.nFramesMax );
    Abc_Print( -2, "\t-T <num>  : wall-time limit in seconds (0 = unlimited) [default = %d]\n", Pars.nTimeOut );
    Abc_Print( -2, "\t-C <num>  : conflicts per query; limit ends the session (0 = unlimited) [default = %d]\n", Pars.nConfLimit );
    Abc_Print( -2, "\t-S <num>  : stable depths after the depth limit [default = %d]\n", Pars.nStableMin );
    Abc_Print( -2, "\t-M <num>  : SAT mode (0=default, 1=focused, 2=plain, 3..8=experimental) [default = %d]\n", Pars.nSatMode );
    Abc_Print( -2, "\t-L <num>  : prefix cache (0=off, 1=flat, 2=shared guard) [default = %d]\n", Pars.nProofMode );
    Abc_Print( -2, "\t-K <num>  : truth-table cut size (0=off, 3..6 leaves) [default = %d]\n", Pars.nCutMax );
    Abc_Print( -2, "\t-D <num>  : directional CNF (0=off, 1=gates, 2=gates/flops) [default = %d]\n", Pars.nCnfMode );
    Abc_Print( -2, "\t-Q <num>  : resolution-cut mode (0=off, 1..5=experimental) [default = %d]\n", Pars.nResolveMode );
    Abc_Print( -2, "\t            enabled modes require lazy encoding and -D 0\n" );
    Abc_Print( -2, "\t-A <num>  : inactive guards (0=free, 1=prefer false, 2=assume false) [default = %d]\n", Pars.nActMode );
    Abc_Print( -2, "\t-H <num>  : assumption order (0=natural, 1=reverse, 2=old, 3=new) [default = %d]\n", Pars.nAssumeOrder );
    Abc_Print( -2, "\t-J <num>  : depth to start compact SAT numbering (0=off) [default = %d]\n", Pars.nCompactDepth );
    Abc_Print( -2, "\t-R <num>  : simplify every num proved depths (0=off; incompatible with -M 3) [default = %d]\n", Pars.nSimplifyEvery );
    Abc_Print( -2, "\t-N <num>  : CBA order (0=natural, 1=reverse, 2=depth, 3=area) [default = %d]\n", Pars.nCbaOrder );
    Abc_Print( -2, "\t-O <file> : write the abstract model as AIGER [default = %s]\n", pFile ? pFile : "none" );
    Abc_Print( -2, "\t-p        : toggle proof-based pruning [default = %s]\n", Pars.fUsePba ? "yes" : "no" );
    Abc_Print( -2, "\t-r        : toggle starting with the existing flop map [default = %s]\n", Pars.fUseStart ? "yes" : "no" );
    Abc_Print( -2, "\t-d        : toggle replacing the &-space AIG with the abstraction [default = %s]\n", fDerive ? "yes" : "no" );
    Abc_Print( -2, "\t-k        : toggle lazy mux/AND-cut CNF encoding [default = %s]\n", Pars.fUseCuts ? "yes" : "no" );
    Abc_Print( -2, "\t-m        : toggle mux consensus clauses [default = %s]\n", Pars.fMuxProp ? "yes" : "no" );
    Abc_Print( -2, "\t-j        : toggle compact SAT numbering from the start [default = %s]\n", Pars.fCompactVars ? "yes" : "no" );
    Abc_Print( -2, "\t-q        : toggle guarded queries (disables native queries) [default = %s]\n", Pars.fClauseQuery ? "yes" : "no" );
    Abc_Print( -2, "\t-u        : toggle native queries (disables guarded queries) [default = %s]\n", Pars.fNativeQuery ? "yes" : "no" );
    Abc_Print( -2, "\t-v        : toggle per-depth statistics [default = %s]\n", Pars.fVerbose ? "yes" : "no" );
    Abc_Print( -2, "\t-h        : print the command usage\n" );
    Abc_Print( -2, "\t           Example: &read design.aig; &abs -T 5 -O abstract.aig\n" );
    Abc_Print( -2, "\t           A bounded UNSAT prefix is not a safety proof.\n" );
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
