/**CFile****************************************************************

  FileName    [pdrIncr.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Property driven reachability.]

  Synopsis    [PDR with incremental solving.]

  Author      [Yen-Sheng Ho, Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - Feb. 17, 2017.]

  Revision    [$Id: pdrIncr.c$]

***********************************************************************/

#include "pdrInt.h"
#include "base/main/main.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
extern int Pdr_ManBlockCube( Pdr_Man_t * p, Pdr_Set_t * pCube );
extern int Pdr_ManPushClauses( Pdr_Man_t * p );
extern int Gia_ManToBridgeAbort( FILE * pFile, int Size, unsigned char * pBuffer );
extern int Gia_ManToBridgeResult( FILE * pFile, int Result, Abc_Cex_t * pCex, int iPoProved );


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void IPdr_ManPrintClauses( Vec_Vec_t * vClauses, int kStart, int nRegs )
{
    Vec_Ptr_t * vArrayK;
    Pdr_Set_t * pCube;
    int i, k, Counter = 0;
    Vec_VecForEachLevelStart( vClauses, vArrayK, k, kStart )
    {
        Vec_PtrSort( vArrayK, (int (*)(void))Pdr_SetCompare );
        Vec_PtrForEachEntry( Pdr_Set_t *, vArrayK, pCube, i )
        {
            Abc_Print( 1, "C=%4d. F=%4d ", Counter++, k );
            Pdr_SetPrint( stdout, pCube, nRegs, NULL );  
            Abc_Print( 1, "\n" ); 
        }
    }
}

/**Function*************************************************************

  Synopsis    [ Check if each cube c_k in frame k satisfies the query
                R_{k-1} && T && !c_k && c_k' (must be UNSAT).
                Return True if all cubes pass the check. ]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int IPdr_ManCheckClauses( Pdr_Man_t * p )
{
    Pdr_Set_t * pCubeK;
    Vec_Ptr_t * vArrayK;
    int j, k, RetValue, kMax = Vec_PtrSize(p->vSolvers);
    int iStartFrame = 1;
    int counter = 0;

    Vec_VecForEachLevelStartStop( p->vClauses, vArrayK, k, iStartFrame, kMax )
    {
        Vec_PtrForEachEntry( Pdr_Set_t *, vArrayK, pCubeK, j )
        {
            ++counter;
            RetValue = Pdr_ManCheckCube( p, k - 1, pCubeK, NULL, 0, 0, 1 );

            if ( !RetValue ) {
                printf( "Cube[%d][%d] not inductive!\n", k, j );
            }

            assert( RetValue == 1 );
        }
    }

    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Vec_t * IPdr_ManSaveClauses( Pdr_Man_t * p, int fDropLast )
{
    int i, k;
    Vec_Vec_t * vClausesSaved;
    Pdr_Set_t * pCla;

    if ( Vec_VecSize( p->vClauses ) == 1 )
        return NULL;
    if ( Vec_VecSize( p->vClauses ) == 2 && fDropLast )
        return NULL;

    if ( fDropLast )
        vClausesSaved = Vec_VecStart( Vec_VecSize(p->vClauses)-1 );
    else 
        vClausesSaved = Vec_VecStart( Vec_VecSize(p->vClauses) );

    Vec_VecForEachEntryStartStop( Pdr_Set_t *, p->vClauses, pCla, i, k, 0, Vec_VecSize(vClausesSaved) )
        Vec_VecPush(vClausesSaved, i, Pdr_SetDup(pCla));
 
    return vClausesSaved;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
sat_solver * IPdr_ManSetSolver( Pdr_Man_t * p, int k, int nTotal )
{
    sat_solver * pSat;
    Vec_Ptr_t * vArrayK;
    Pdr_Set_t * pCube;
    int i, j;

    assert( Vec_PtrSize(p->vSolvers) == k );
    assert( Vec_IntSize(p->vActVars) == k );

    pSat = zsat_solver_new_seed(p->pPars->nRandomSeed);
    pSat = Pdr_ManNewSolver( pSat, p, k, (int)(k == 0) );
    Vec_PtrPush( p->vSolvers, pSat );
    Vec_IntPush( p->vActVars, 0 );

    // set the property output
    if ( k < nTotal - 1 )
        Pdr_ManSetPropertyOutput( p, k );

    if (k == 0)
        return pSat;

    // add the clauses
    Vec_VecForEachLevelStart( p->vClauses, vArrayK, i, k )
        Vec_PtrForEachEntry( Pdr_Set_t *, vArrayK, pCube, j )
            Pdr_ManSolverAddClause( p, k, pCube );
    return pSat;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

int IPdr_ManRestoreAbsFlops( Pdr_Man_t * p )
{
    Pdr_Set_t * pSet; int i, j, k;   

    Vec_VecForEachEntry( Pdr_Set_t *, p->vClauses, pSet, i, j )
    {
        for ( k = 0; k < pSet->nLits; k++ )
        {
            Vec_IntWriteEntry( p->vAbsFlops, Abc_Lit2Var(pSet->Lits[k]), 1 );
        }
    }
    return 0;
}

int IPdr_ManRestore( Pdr_Man_t * p, Vec_Vec_t * vClauses, Vec_Int_t * vMap )
{
    int i;

    assert(vClauses);

    Vec_VecFree(p->vClauses);
    p->vClauses = vClauses;

    // remap clause literals using mapping (old flop -> new flop) found in array vMap
    if ( vMap )
    {
        Pdr_Set_t * pSet; int j, k;   
        Vec_VecForEachEntry( Pdr_Set_t *, vClauses, pSet, i, j )
            for ( k = 0; k < pSet->nLits; k++ )
                pSet->Lits[k] = Abc_Lit2LitV( Vec_IntArray(vMap), pSet->Lits[k] );
    }

    for ( i = 0; i < Vec_VecSize(p->vClauses); ++i )
        IPdr_ManSetSolver( p, i, Vec_VecSize( p->vClauses ) );

    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int IPdr_ManSolveInt( Pdr_Man_t * p, int fCheckClauses, int fPushClauses )
{
    int fPrintClauses = 0;
    Pdr_Set_t * pCube = NULL;
    Aig_Obj_t * pObj;
    Abc_Cex_t * pCexNew;
    int iFrame, RetValue = -1;
    int nOutDigits = Abc_Base10Log( Saig_ManPoNum(p->pAig) );
    abctime clkStart = Abc_Clock(), clkOne = 0;
    p->timeToStop = p->pPars->nTimeOut ? p->pPars->nTimeOut * CLOCKS_PER_SEC + Abc_Clock(): 0;
    // assert( Vec_PtrSize(p->vSolvers) == 0 );
    // in the multi-output mode, mark trivial POs (those fed by const0) as solved 
    if ( p->pPars->fSolveAll )
        Saig_ManForEachPo( p->pAig, pObj, iFrame )
            if ( Aig_ObjChild0(pObj) == Aig_ManConst0(p->pAig) )
            {
                Vec_IntWriteEntry( p->pPars->vOutMap, iFrame, 1 ); // unsat
                p->pPars->nProveOuts++;
                if ( p->pPars->fUseBridge )
                    Gia_ManToBridgeResult( stdout, 1, NULL, iFrame );
            }
    // create the first timeframe
    p->pPars->timeLastSolved = Abc_Clock();

    if ( Vec_VecSize(p->vClauses) == 0 )
        Pdr_ManCreateSolver( p, (iFrame = 0) );
    else {
        iFrame = Vec_VecSize(p->vClauses) - 1;

        if ( fCheckClauses )
        {
            if ( p->pPars->fVerbose )
               Abc_Print( 1, "IPDR: Checking the reloaded length-%d trace...", iFrame + 1 ) ;
            IPdr_ManCheckClauses( p );
            if ( p->pPars->fVerbose )
               Abc_Print( 1, " Passed!\n" ) ;
        }

        if ( fPushClauses )
        {
            p->iUseFrame = Abc_MaxInt(iFrame, 1);

            if ( p->pPars->fVerbose ) 
            {
                Abc_Print( 1, "IPDR: Pushing the reloaded clauses. Before:\n" );
                Pdr_ManPrintProgress( p, 1, Abc_Clock() - clkStart );
            }

            RetValue = Pdr_ManPushClauses( p );

            if ( p->pPars->fVerbose ) 
            {
                Abc_Print( 1, "IPDR: Finished pushing. After:\n" );
                Pdr_ManPrintProgress( p, 1, Abc_Clock() - clkStart );
            }

            if ( RetValue ) 
            {
                Pdr_ManReportInvariant( p );
                Pdr_ManVerifyInvariant( p );
                return 1;
            }
        }

        if ( p->pPars->fUseAbs && p->vAbsFlops == NULL && iFrame >= 1 )
        {
            assert( p->vAbsFlops == NULL );
            p->vAbsFlops  = Vec_IntStart( Saig_ManRegNum(p->pAig) );
            p->vMapFf2Ppi = Vec_IntStartFull( Saig_ManRegNum(p->pAig) );
            p->vMapPpi2Ff = Vec_IntAlloc( 100 );
            
            IPdr_ManRestoreAbsFlops( p );
        }
 
    }
    while ( 1 )
    {
        int fRefined = 0;
        if ( p->pPars->fUseAbs && p->vAbsFlops == NULL && iFrame == 1 )
        {
//            int i, Prio;
            assert( p->vAbsFlops == NULL );
            p->vAbsFlops  = Vec_IntStart( Saig_ManRegNum(p->pAig) );
            p->vMapFf2Ppi = Vec_IntStartFull( Saig_ManRegNum(p->pAig) );
            p->vMapPpi2Ff = Vec_IntAlloc( 100 );
//            Vec_IntForEachEntry( p->vPrio, Prio, i )
//                if ( Prio >> p->nPrioShift  )
//                    Vec_IntWriteEntry( p->vAbsFlops, i, 1 );
        }
        //if ( p->pPars->fUseAbs && p->vAbsFlops )
        //    printf( "Starting frame %d with %d (%d) flops.\n", iFrame, Vec_IntCountPositive(p->vAbsFlops), Vec_IntCountPositive(p->vPrio) );
        p->nFrames = iFrame;
        assert( iFrame == Vec_PtrSize(p->vSolvers)-1 );
        p->iUseFrame = Abc_MaxInt(iFrame, 1);
        Saig_ManForEachPo( p->pAig, pObj, p->iOutCur )
        {
            // skip disproved outputs
            if ( p->vCexes && Vec_PtrEntry(p->vCexes, p->iOutCur) )
                continue;
            // skip output whose time has run out
            if ( p->pTime4Outs && p->pTime4Outs[p->iOutCur] == 0 )
                continue;
            // check if the output is trivially solved
            if ( Aig_ObjChild0(pObj) == Aig_ManConst0(p->pAig) )
                continue;
            // check if the output is trivially solved
            if ( Aig_ObjChild0(pObj) == Aig_ManConst1(p->pAig) )
            {
                if ( !p->pPars->fSolveAll )
                {
                    pCexNew = Abc_CexMakeTriv( Aig_ManRegNum(p->pAig), Saig_ManPiNum(p->pAig), Saig_ManPoNum(p->pAig), iFrame*Saig_ManPoNum(p->pAig)+p->iOutCur );
                    p->pAig->pSeqModel = pCexNew;
                    return 0; // SAT
                }
                pCexNew = (p->pPars->fUseBridge || p->pPars->fStoreCex) ? Abc_CexMakeTriv( Aig_ManRegNum(p->pAig), Saig_ManPiNum(p->pAig), Saig_ManPoNum(p->pAig), iFrame*Saig_ManPoNum(p->pAig)+p->iOutCur ) : (Abc_Cex_t *)(ABC_PTRINT_T)1;
                p->pPars->nFailOuts++;
                if ( p->pPars->vOutMap ) Vec_IntWriteEntry( p->pPars->vOutMap, p->iOutCur, 0 );
                if ( !p->pPars->fNotVerbose )
                Abc_Print( 1, "Output %*d was trivially asserted in frame %2d (solved %*d out of %*d outputs).\n",
                    nOutDigits, p->iOutCur, iFrame, nOutDigits, p->pPars->nFailOuts, nOutDigits, Saig_ManPoNum(p->pAig) );
                assert( Vec_PtrEntry(p->vCexes, p->iOutCur) == NULL );
                if ( p->pPars->fUseBridge )
                    Gia_ManToBridgeResult( stdout, 0, pCexNew, pCexNew->iPo );
                Vec_PtrWriteEntry( p->vCexes, p->iOutCur, pCexNew );
                if ( p->pPars->pFuncOnFail && p->pPars->pFuncOnFail(p->iOutCur, p->pPars->fStoreCex ? (Abc_Cex_t *)Vec_PtrEntry(p->vCexes, p->iOutCur) : NULL) )
                {
                    if ( p->pPars->fVerbose )
                        Pdr_ManPrintProgress( p, 1, Abc_Clock() - clkStart );
                    if ( !p->pPars->fSilent )
                        Abc_Print( 1, "Quitting due to callback on fail in frame %d.\n", iFrame );
                    p->pPars->iFrame = iFrame;
                    return -1;
                }
                if ( p->pPars->nFailOuts + p->pPars->nDropOuts == Saig_ManPoNum(p->pAig) )
                    return p->pPars->nFailOuts ? 0 : -1; // SAT or UNDEC
                p->pPars->timeLastSolved = Abc_Clock();
                continue;
            }
            // try to solve this output
            if ( p->pTime4Outs )
            {
                assert( p->pTime4Outs[p->iOutCur] > 0 );
                clkOne = Abc_Clock();
                p->timeToStopOne = p->pTime4Outs[p->iOutCur] + Abc_Clock();
            }
            while ( 1 )
            {
                if ( p->pPars->nTimeOutGap && p->pPars->timeLastSolved && Abc_Clock() > p->pPars->timeLastSolved + p->pPars->nTimeOutGap * CLOCKS_PER_SEC )
                {
                    if ( p->pPars->fVerbose )
                        Pdr_ManPrintProgress( p, 1, Abc_Clock() - clkStart );
                    if ( !p->pPars->fSilent )
                        Abc_Print( 1, "Reached gap timeout (%d seconds) in frame %d.\n",  p->pPars->nTimeOutGap, iFrame );
                    p->pPars->iFrame = iFrame;
                    return -1;
                }
                RetValue = Pdr_ManCheckCube( p, iFrame, NULL, &pCube, p->pPars->nConfLimit, 0, 1 );
                if ( RetValue == 1 )
                    break;
                if ( RetValue == -1 )
                {
                    if ( p->pPars->fVerbose )
                        Pdr_ManPrintProgress( p, 1, Abc_Clock() - clkStart );
                    if ( p->timeToStop && Abc_Clock() > p->timeToStop )
                        Abc_Print( 1, "Reached timeout (%d seconds) in frame %d.\n",  p->pPars->nTimeOut, iFrame );
                    else if ( p->pPars->nTimeOutGap && p->pPars->timeLastSolved && Abc_Clock() > p->pPars->timeLastSolved + p->pPars->nTimeOutGap * CLOCKS_PER_SEC )
                        Abc_Print( 1, "Reached gap timeout (%d seconds) in frame %d.\n",  p->pPars->nTimeOutGap, iFrame );
                    else if ( p->timeToStopOne && Abc_Clock() > p->timeToStopOne )
                    {
                        Pdr_QueueClean( p );
                        pCube = NULL;
                        break; // keep solving
                    }
                    else if ( p->pPars->nConfLimit )
                        Abc_Print( 1, "Reached conflict limit (%d) in frame %d.\n",  p->pPars->nConfLimit, iFrame );
                    else if ( p->pPars->fVerbose )
                        Abc_Print( 1, "Computation cancelled by the callback in frame %d.\n", iFrame );
                    p->pPars->iFrame = iFrame;
                    return -1;
                }
                if ( RetValue == 0 )
                {
                    RetValue = Pdr_ManBlockCube( p, pCube );
                    if ( RetValue == -1 )
                    {
                        if ( p->pPars->fVerbose )
                            Pdr_ManPrintProgress( p, 1, Abc_Clock() - clkStart );
                        if ( p->timeToStop && Abc_Clock() > p->timeToStop )
                            Abc_Print( 1, "Reached timeout (%d seconds) in frame %d.\n",  p->pPars->nTimeOut, iFrame );
                        else if ( p->pPars->nTimeOutGap && p->pPars->timeLastSolved && Abc_Clock() > p->pPars->timeLastSolved + p->pPars->nTimeOutGap * CLOCKS_PER_SEC )
                            Abc_Print( 1, "Reached gap timeout (%d seconds) in frame %d.\n",  p->pPars->nTimeOutGap, iFrame );
                        else if ( p->timeToStopOne && Abc_Clock() > p->timeToStopOne )
                        {
                            Pdr_QueueClean( p );
                            pCube = NULL;
                            break; // keep solving
                        }
                        else if ( p->pPars->nConfLimit )
                            Abc_Print( 1, "Reached conflict limit (%d) in frame %d.\n",  p->pPars->nConfLimit, iFrame );
                        else if ( p->pPars->fVerbose )
                            Abc_Print( 1, "Computation cancelled by the callback in frame %d.\n", iFrame );
                        p->pPars->iFrame = iFrame;
                        return -1;
                    }
                    if ( RetValue == 0 )
                    {
                        if ( fPrintClauses )
                        {
                            Abc_Print( 1, "*** Clauses after frame %d:\n", iFrame );
                            Pdr_ManPrintClauses( p, 0 );
                        }
                        if ( p->pPars->fVerbose && !p->pPars->fUseAbs )
                            Pdr_ManPrintProgress( p, !p->pPars->fSolveAll, Abc_Clock() - clkStart );
                        p->pPars->iFrame = iFrame;
                        if ( !p->pPars->fSolveAll )
                        {
                            abctime clk = Abc_Clock();
                            Abc_Cex_t * pCex = Pdr_ManDeriveCexAbs(p);
                            p->tAbs += Abc_Clock() - clk;
                            if ( pCex == NULL )
                            {
                                assert( p->pPars->fUseAbs );
                                Pdr_QueueClean( p );
                                pCube = NULL;
                                fRefined = 1;
                                break; // keep solving
                            }
                            p->pAig->pSeqModel = pCex;

                            if ( p->pPars->fVerbose && p->pPars->fUseAbs )
                                Pdr_ManPrintProgress( p, !p->pPars->fSolveAll, Abc_Clock() - clkStart );
                            return 0; // SAT
                        }
                        p->pPars->nFailOuts++;
                        pCexNew = (p->pPars->fUseBridge || p->pPars->fStoreCex) ? Pdr_ManDeriveCex(p) : (Abc_Cex_t *)(ABC_PTRINT_T)1;
                        if ( p->pPars->vOutMap ) Vec_IntWriteEntry( p->pPars->vOutMap, p->iOutCur, 0 );
                        assert( Vec_PtrEntry(p->vCexes, p->iOutCur) == NULL );
                        if ( p->pPars->fUseBridge )
                            Gia_ManToBridgeResult( stdout, 0, pCexNew, pCexNew->iPo );
                        Vec_PtrWriteEntry( p->vCexes, p->iOutCur, pCexNew );
                        if ( p->pPars->pFuncOnFail && p->pPars->pFuncOnFail(p->iOutCur, p->pPars->fStoreCex ? (Abc_Cex_t *)Vec_PtrEntry(p->vCexes, p->iOutCur) : NULL) )
                        {
                            if ( p->pPars->fVerbose )
                                Pdr_ManPrintProgress( p, 1, Abc_Clock() - clkStart );
                            if ( !p->pPars->fSilent )
                                Abc_Print( 1, "Quitting due to callback on fail in frame %d.\n", iFrame );
                            p->pPars->iFrame = iFrame;
                            return -1;
                        }
                        if ( !p->pPars->fNotVerbose )
                            Abc_Print( 1, "Output %*d was asserted in frame %2d (%2d) (solved %*d out of %*d outputs).\n",
                                nOutDigits, p->iOutCur, iFrame, iFrame, nOutDigits, p->pPars->nFailOuts, nOutDigits, Saig_ManPoNum(p->pAig) );
                        if ( p->pPars->nFailOuts == Saig_ManPoNum(p->pAig) )
                            return 0; // all SAT
                        Pdr_QueueClean( p );
                        pCube = NULL;
                        break; // keep solving
                    }
                    if ( p->pPars->fVerbose )
                        Pdr_ManPrintProgress( p, 0, Abc_Clock() - clkStart );
                }
            }
            if ( fRefined )
                break;
            if ( p->pTime4Outs )
            {
                abctime timeSince = Abc_Clock() - clkOne;
                assert( p->pTime4Outs[p->iOutCur] > 0 );
                p->pTime4Outs[p->iOutCur] = (p->pTime4Outs[p->iOutCur] > timeSince) ? p->pTime4Outs[p->iOutCur] - timeSince : 0;
                if ( p->pTime4Outs[p->iOutCur] == 0 && Vec_PtrEntry(p->vCexes, p->iOutCur) == NULL ) // undecided
                {
                    p->pPars->nDropOuts++;
                    if ( p->pPars->vOutMap ) 
                        Vec_IntWriteEntry( p->pPars->vOutMap, p->iOutCur, -1 );
                    if ( !p->pPars->fNotVerbose ) 
                        Abc_Print( 1, "Timing out on output %*d in frame %d.\n", nOutDigits, p->iOutCur, iFrame );
                }
                p->timeToStopOne = 0;
            }
        }
        /*
        if ( p->pPars->fUseAbs && p->vAbsFlops && !fRefined )
        {
            int i, Used;
            Vec_IntForEachEntry( p->vAbsFlops, Used, i )
                if ( Used && (Vec_IntEntry(p->vPrio, i) >> p->nPrioShift) == 0 )
                    Vec_IntWriteEntry( p->vAbsFlops, i, 0 );
        }
        */
        if ( p->pPars->fUseAbs && p->vAbsFlops && !fRefined )
        {
            Pdr_Set_t * pSet;
            int i, j, k;
            Vec_IntFill( p->vAbsFlops, Vec_IntSize( p->vAbsFlops ), 0 );
            Vec_VecForEachEntry( Pdr_Set_t *, p->vClauses, pSet, i, j )
                for ( k = 0; k < pSet->nLits; k++ )
                    Vec_IntWriteEntry( p->vAbsFlops, Abc_Lit2Var(pSet->Lits[k]), 1 );
        }

        if ( p->pPars->fVerbose )
            Pdr_ManPrintProgress( p, !fRefined, Abc_Clock() - clkStart );
        if ( fRefined )
            continue;
        //if ( p->pPars->fUseAbs && p->vAbsFlops )
        //    printf( "Finished frame %d with %d (%d) flops.\n", iFrame, Vec_IntCountPositive(p->vAbsFlops), Vec_IntCountPositive(p->vPrio) );
        // open a new timeframe
        p->nQueLim = p->pPars->nRestLimit;
        assert( pCube == NULL );
        Pdr_ManSetPropertyOutput( p, iFrame );
        Pdr_ManCreateSolver( p, ++iFrame );
        if ( fPrintClauses )
        {
            Abc_Print( 1, "*** Clauses after frame %d:\n", iFrame );
            Pdr_ManPrintClauses( p, 0 );
        }
        // push clauses into this timeframe
        RetValue = Pdr_ManPushClauses( p );
        if ( RetValue == -1 )
        {
            if ( p->pPars->fVerbose )
                Pdr_ManPrintProgress( p, 1, Abc_Clock() - clkStart );
            if ( !p->pPars->fSilent )
            {
                if ( p->timeToStop && Abc_Clock() > p->timeToStop )
                    Abc_Print( 1, "Reached timeout (%d seconds) in frame %d.\n",  p->pPars->nTimeOut, iFrame );
                else
                    Abc_Print( 1, "Reached conflict limit (%d) in frame.\n",  p->pPars->nConfLimit, iFrame );
            }
            p->pPars->iFrame = iFrame;
            return -1;
        }
        if ( RetValue )
        {
            if ( p->pPars->fVerbose )
                Pdr_ManPrintProgress( p, 1, Abc_Clock() - clkStart );
            if ( !p->pPars->fSilent )
                Pdr_ManReportInvariant( p );
            if ( !p->pPars->fSilent )
                Pdr_ManVerifyInvariant( p );
            p->pPars->iFrame = iFrame;
            // count the number of UNSAT outputs
            p->pPars->nProveOuts = Saig_ManPoNum(p->pAig) - p->pPars->nFailOuts - p->pPars->nDropOuts;
            // convert previously 'unknown' into 'unsat'
            if ( p->pPars->vOutMap )
                for ( iFrame = 0; iFrame < Saig_ManPoNum(p->pAig); iFrame++ )
                    if ( Vec_IntEntry(p->pPars->vOutMap, iFrame) == -2 ) // unknown
                    {
                        Vec_IntWriteEntry( p->pPars->vOutMap, iFrame, 1 ); // unsat
                        if ( p->pPars->fUseBridge )
                            Gia_ManToBridgeResult( stdout, 1, NULL, iFrame );
                    }
            if ( p->pPars->nProveOuts == Saig_ManPoNum(p->pAig) )
                return 1; // UNSAT
            if ( p->pPars->nFailOuts > 0 )
                return 0; // SAT
            return -1;
        }
        if ( p->pPars->fVerbose )
            Pdr_ManPrintProgress( p, 0, Abc_Clock() - clkStart );

        // check termination
        if ( p->pPars->pFuncStop && p->pPars->pFuncStop(p->pPars->RunId) )
        {
            p->pPars->iFrame = iFrame;
            return -1;
        }
        if ( p->timeToStop && Abc_Clock() > p->timeToStop )
        {
            if ( fPrintClauses )
            {
                Abc_Print( 1, "*** Clauses after frame %d:\n", iFrame );
                Pdr_ManPrintClauses( p, 0 );
            }
            if ( p->pPars->fVerbose )
                Pdr_ManPrintProgress( p, 1, Abc_Clock() - clkStart );
            if ( !p->pPars->fSilent )
                Abc_Print( 1, "Reached timeout (%d seconds) in frame %d.\n",  p->pPars->nTimeOut, iFrame );
            p->pPars->iFrame = iFrame;
            return -1;
        }
        if ( p->pPars->nTimeOutGap && p->pPars->timeLastSolved && Abc_Clock() > p->pPars->timeLastSolved + p->pPars->nTimeOutGap * CLOCKS_PER_SEC )
        {
            if ( fPrintClauses )
            {
                Abc_Print( 1, "*** Clauses after frame %d:\n", iFrame );
                Pdr_ManPrintClauses( p, 0 );
            }
            if ( p->pPars->fVerbose )
                Pdr_ManPrintProgress( p, 1, Abc_Clock() - clkStart );
            if ( !p->pPars->fSilent )
                Abc_Print( 1, "Reached gap timeout (%d seconds) in frame %d.\n",  p->pPars->nTimeOutGap, iFrame );
            p->pPars->iFrame = iFrame;
            return -1;
        }
        if ( p->pPars->nFrameMax && iFrame >= p->pPars->nFrameMax )
        {
            if ( p->pPars->fVerbose )
                Pdr_ManPrintProgress( p, 1, Abc_Clock() - clkStart );
            if ( !p->pPars->fSilent )
                Abc_Print( 1, "Reached limit on the number of timeframes (%d).\n", p->pPars->nFrameMax );
            p->pPars->iFrame = iFrame;
            return -1;
        }
    }
    assert( 0 );
    return -1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int IPdr_ManSolve( Aig_Man_t * pAig, Pdr_Par_t * pPars )
{
    Pdr_Man_t * p;
    int k, RetValue;
    Vec_Vec_t * vClausesSaved;

    abctime clk = Abc_Clock();
    if ( pPars->nTimeOutOne && !pPars->fSolveAll )
        pPars->nTimeOutOne = 0;
    if ( pPars->nTimeOutOne && pPars->nTimeOut == 0 )
        pPars->nTimeOut = pPars->nTimeOutOne * Saig_ManPoNum(pAig) / 1000 + (int)((pPars->nTimeOutOne * Saig_ManPoNum(pAig) % 1000) > 0);
    if ( pPars->fVerbose )
    {
//    Abc_Print( 1, "Running PDR by Niklas Een (aka IC3 by Aaron Bradley) with these parameters:\n" );
        Abc_Print( 1, "VarMax = %d. FrameMax = %d. QueMax = %d. TimeMax = %d. ",
            pPars->nRecycle,
            pPars->nFrameMax,
            pPars->nRestLimit,
            pPars->nTimeOut );
        Abc_Print( 1, "MonoCNF = %s. SkipGen = %s. SolveAll = %s.\n",
            pPars->fMonoCnf ?     "yes" : "no",
            pPars->fSkipGeneral ? "yes" : "no",
            pPars->fSolveAll ?    "yes" : "no" );
    }
    ABC_FREE( pAig->pSeqModel );


    p = Pdr_ManStart( pAig, pPars, NULL );
    while ( 1 ) {
        RetValue = IPdr_ManSolveInt( p, 1, 0 );

        if ( RetValue == -1 && pPars->iFrame == pPars->nFrameMax) {
            vClausesSaved = IPdr_ManSaveClauses( p, 1 );

            Pdr_ManStop( p );

            p = Pdr_ManStart( pAig, pPars, NULL );
            IPdr_ManRestore( p, vClausesSaved, NULL );

            pPars->nFrameMax = pPars->nFrameMax << 1;

            continue;
        }

        if ( RetValue == 0 )
            assert( pAig->pSeqModel != NULL || p->vCexes != NULL );
        if ( p->vCexes )
        {
            assert( p->pAig->vSeqModelVec == NULL );
            p->pAig->vSeqModelVec = p->vCexes;
            p->vCexes = NULL;
        }
        if ( p->pPars->fDumpInv )
        {
            char * pFileName = Extra_FileNameGenericAppend(p->pAig->pName, "_inv.pla");
                Abc_FrameSetInv( Pdr_ManDeriveInfinityClauses( p, RetValue!=1 ) );
                Pdr_ManDumpClauses( p, pFileName, RetValue==1 );
        }
        else if ( RetValue == 1 )
            Abc_FrameSetInv( Pdr_ManDeriveInfinityClauses( p, RetValue!=1 ) );

        p->tTotal += Abc_Clock() - clk;
        Pdr_ManStop( p );

        break;
    }
    
    
    pPars->iFrame--;
    // convert all -2 (unknown) entries into -1 (undec)
    if ( pPars->vOutMap )
        for ( k = 0; k < Saig_ManPoNum(pAig); k++ )
            if ( Vec_IntEntry(pPars->vOutMap, k) == -2 ) // unknown
                Vec_IntWriteEntry( pPars->vOutMap, k, -1 ); // undec
    if ( pPars->fUseBridge )
        Gia_ManToBridgeAbort( stdout, 7, (unsigned char *)"timeout" );
    return RetValue;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkDarIPdr ( Abc_Ntk_t * pNtk, Pdr_Par_t * pPars )
{
    int RetValue = -1;
    abctime clk = Abc_Clock();
    Aig_Man_t * pMan;
    pMan = Abc_NtkToDar( pNtk, 0, 1 );

    RetValue = IPdr_ManSolve( pMan, pPars );
 
    if ( RetValue == 1 )
        Abc_Print( 1, "Property proved.  " );
    else 
    {
        if ( RetValue == 0 )
        {
            if ( pMan->pSeqModel == NULL )
                Abc_Print( 1, "Counter-example is not available.\n" );
            else
            {
                Abc_Print( 1, "Output %d of miter \"%s\" was asserted in frame %d.  ", pMan->pSeqModel->iPo, pNtk->pName, pMan->pSeqModel->iFrame );
                if ( !Saig_ManVerifyCex( pMan, pMan->pSeqModel ) )
                    Abc_Print( 1, "Counter-example verification has FAILED.\n" );
            }
        }
        else if ( RetValue == -1 )
            Abc_Print( 1, "Property UNDECIDED.  " );
        else
            assert( 0 );
    }
    ABC_PRT( "Time", Abc_Clock() - clk );


    ABC_FREE( pNtk->pSeqModel );
    pNtk->pSeqModel = pMan->pSeqModel;
    pMan->pSeqModel = NULL;
    if ( pNtk->vSeqModelVec )
        Vec_PtrFreeFree( pNtk->vSeqModelVec );
    pNtk->vSeqModelVec = pMan->vSeqModelVec;
    pMan->vSeqModelVec = NULL;
    Aig_ManStop( pMan );
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
