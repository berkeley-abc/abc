/**CFile****************************************************************

  FileName    [pdrCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Property driven reachability.]

  Synopsis    [Core procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 20, 2010.]

  Revision    [$Id: pdrCore.c,v 1.00 2010/11/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "pdrInt.h"
#include "base/main/main.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern int Gia_ManToBridgeResult( FILE * pFile, int Result, Abc_Cex_t * pCex, int iPoProved );
extern int Gia_ManToBridgeAbort( FILE * pFile, int Size, unsigned char * pBuffer );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns 1 if the state could be blocked.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_ManSetDefaultParams( Pdr_Par_t * pPars )
{
    memset( pPars, 0, sizeof(Pdr_Par_t) );
//    pPars->iOutput        =      -1;  // zero-based output number
    pPars->nRecycle       =     300;  // limit on vars for recycling
    pPars->nFrameMax      =   10000;  // limit on number of timeframes
    pPars->nTimeOut       =       0;  // timeout in seconds
    pPars->nTimeOutGap    =       0;  // timeout in seconds since the last solved
    pPars->nConfLimit     =       0;  // limit on SAT solver conflicts
    pPars->nRestLimit     =       0;  // limit on the number of proof-obligations
    pPars->fTwoRounds     =       0;  // use two rounds for generalization
    pPars->fMonoCnf       =       0;  // monolythic CNF
    pPars->fDumpInv       =       0;  // dump inductive invariant
    pPars->fShortest      =       0;  // forces bug traces to be shortest
    pPars->fVerbose       =       0;  // verbose output
    pPars->fVeryVerbose   =       0;  // very verbose output
    pPars->fNotVerbose    =       0;  // not printing line-by-line progress
    pPars->iFrame         =      -1;  // explored up to this frame
    pPars->nFailOuts      =       0;  // the number of disproved outputs
    pPars->nDropOuts      =       0;  // the number of timed out outputs
    pPars->timeLastSolved =       0;  // last one solved
}

/**Function*************************************************************

  Synopsis    [Reduces clause using analyzeFinal.]

  Description [Assumes that the SAT solver just terminated an UNSAT call.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr_Set_t * Pdr_ManReduceClause( Pdr_Man_t * p, int k, Pdr_Set_t * pCube )
{
    Pdr_Set_t * pCubeMin;
    Vec_Int_t * vLits;
    int i, Entry, nCoreLits, * pCoreLits;
    // get relevant SAT literals
    nCoreLits = sat_solver_final(Pdr_ManSolver(p, k), &pCoreLits);
    // translate them into register literals and remove auxiliary
    vLits = Pdr_ManLitsToCube( p, k, pCoreLits, nCoreLits );
    // skip if there is no improvement
    if ( Vec_IntSize(vLits) == pCube->nLits )
        return NULL;
    assert( Vec_IntSize(vLits) < pCube->nLits );
    // if the cube overlaps with init, add any literal
    Vec_IntForEachEntry( vLits, Entry, i )
        if ( lit_sign(Entry) == 0 ) // positive literal
            break;
    if ( i == Vec_IntSize(vLits) ) // only negative literals
    {
        // add the first positive literal
        for ( i = 0; i < pCube->nLits; i++ )
            if ( lit_sign(pCube->Lits[i]) == 0 ) // positive literal
            {
                Vec_IntPush( vLits, pCube->Lits[i] );
                break;
            }
        assert( i < pCube->nLits );
    }
    // generate a starting cube
    pCubeMin  = Pdr_SetCreateSubset( pCube, Vec_IntArray(vLits), Vec_IntSize(vLits) );
    assert( !Pdr_SetIsInit(pCubeMin, -1) );
/*
    // make sure the cube works
    {
    int RetValue;
    RetValue = Pdr_ManCheckCube( p, k, pCubeMin, NULL, 0 );
    assert( RetValue );
    }
*/
    return pCubeMin;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the state could be blocked.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_ManPushClauses( Pdr_Man_t * p )
{
    Pdr_Set_t * pTemp, * pCubeK, * pCubeK1;
    Vec_Ptr_t * vArrayK, * vArrayK1;
    int i, j, k, m, RetValue = 0, RetValue2, kMax = Vec_PtrSize(p->vSolvers)-1;
    int iStartFrame = p->pPars->fShiftStart ? p->iUseFrame : 1;
    int Counter = 0;
    abctime clk = Abc_Clock();
    assert( p->iUseFrame > 0 );
    Vec_VecForEachLevelStartStop( p->vClauses, vArrayK, k, iStartFrame, kMax )
    {
        Vec_PtrSort( vArrayK, (int (*)(void))Pdr_SetCompare );
        vArrayK1 = Vec_VecEntry( p->vClauses, k+1 );
        Vec_PtrForEachEntry( Pdr_Set_t *, vArrayK, pCubeK, j )
        {
            Counter++;

            // remove cubes in the same frame that are contained by pCubeK
            Vec_PtrForEachEntryStart( Pdr_Set_t *, vArrayK, pTemp, m, j+1 )
            {
                if ( !Pdr_SetContains( pTemp, pCubeK ) ) // pCubeK contains pTemp
                    continue;
                Pdr_SetDeref( pTemp );
                Vec_PtrWriteEntry( vArrayK, m, Vec_PtrEntryLast(vArrayK) );
                Vec_PtrPop(vArrayK);
                m--;
            }

            // check if the clause can be moved to the next frame
            RetValue2 = Pdr_ManCheckCube( p, k, pCubeK, NULL, 0 );
            if ( RetValue2 == -1 )
                return -1;
            if ( !RetValue2 )
                continue;

            {
                Pdr_Set_t * pCubeMin;
                pCubeMin = Pdr_ManReduceClause( p, k, pCubeK );
                if ( pCubeMin != NULL )
                {
//                Abc_Print( 1, "%d ", pCubeK->nLits - pCubeMin->nLits );
                    Pdr_SetDeref( pCubeK );
                    pCubeK = pCubeMin;
                }
            }

            // if it can be moved, add it to the next frame
            Pdr_ManSolverAddClause( p, k+1, pCubeK );
            // check if the clause subsumes others
            Vec_PtrForEachEntry( Pdr_Set_t *, vArrayK1, pCubeK1, i )
            {
                if ( !Pdr_SetContains( pCubeK1, pCubeK ) ) // pCubeK contains pCubeK1
                    continue;
                Pdr_SetDeref( pCubeK1 );
                Vec_PtrWriteEntry( vArrayK1, i, Vec_PtrEntryLast(vArrayK1) );
                Vec_PtrPop(vArrayK1);
                i--;
            }
            // add the last clause
            Vec_PtrPush( vArrayK1, pCubeK );
            Vec_PtrWriteEntry( vArrayK, j, Vec_PtrEntryLast(vArrayK) );
            Vec_PtrPop(vArrayK);
            j--;
        }
        if ( Vec_PtrSize(vArrayK) == 0 )
            RetValue = 1;
    }

    // clean up the last one
    vArrayK = Vec_VecEntry( p->vClauses, kMax );
    Vec_PtrSort( vArrayK, (int (*)(void))Pdr_SetCompare );
    Vec_PtrForEachEntry( Pdr_Set_t *, vArrayK, pCubeK, j )
    {
        // remove cubes in the same frame that are contained by pCubeK
        Vec_PtrForEachEntryStart( Pdr_Set_t *, vArrayK, pTemp, m, j+1 )
        {
            if ( !Pdr_SetContains( pTemp, pCubeK ) ) // pCubeK contains pTemp
                continue;
/*
            Abc_Print( 1, "===\n" );
            Pdr_SetPrint( stdout, pCubeK, Aig_ManRegNum(p->pAig), NULL );
            Abc_Print( 1, "\n" );
            Pdr_SetPrint( stdout, pTemp, Aig_ManRegNum(p->pAig), NULL );
            Abc_Print( 1, "\n" );
*/
            Pdr_SetDeref( pTemp );
            Vec_PtrWriteEntry( vArrayK, m, Vec_PtrEntryLast(vArrayK) );
            Vec_PtrPop(vArrayK);
            m--;
        }
    }
    p->tPush += Abc_Clock() - clk;
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the clause is contained in higher clauses.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_ManCheckContainment( Pdr_Man_t * p, int k, Pdr_Set_t * pSet )
{
    Pdr_Set_t * pThis;
    Vec_Ptr_t * vArrayK;
    int i, j, kMax = Vec_PtrSize(p->vSolvers)-1;
    Vec_VecForEachLevelStartStop( p->vClauses, vArrayK, i, k, kMax+1 )
        Vec_PtrForEachEntry( Pdr_Set_t *, vArrayK, pThis, j )
            if ( Pdr_SetContains( pSet, pThis ) )
                return 1;
    return 0;
}


/**Function*************************************************************

  Synopsis    [Sorts literals by priority.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int * Pdr_ManSortByPriority( Pdr_Man_t * p, Pdr_Set_t * pCube )
{
    int * pPrios = Vec_IntArray(p->vPrio);
    int * pArray = p->pOrder;
    int temp, i, j, best_i, nSize = pCube->nLits;
    // initialize variable order
    for ( i = 0; i < nSize; i++ )
        pArray[i] = i;
    for ( i = 0; i < nSize-1; i++ )
    {
        best_i = i;
        for ( j = i+1; j < nSize; j++ )
//            if ( pArray[j] < pArray[best_i] )
            if ( pPrios[pCube->Lits[pArray[j]]>>1] < pPrios[pCube->Lits[pArray[best_i]]>>1] )
                best_i = j;
        temp = pArray[i];
        pArray[i] = pArray[best_i];
        pArray[best_i] = temp;
    }
/*
    for ( i = 0; i < pCube->nLits; i++ )
        Abc_Print( 1, "%2d : %5d    %5d  %5d\n", i, pArray[i], pCube->Lits[pArray[i]]>>1, pPrios[pCube->Lits[pArray[i]]>>1] );
    Abc_Print( 1, "\n" );
*/
    return pArray;
}


/**Function*************************************************************

  Synopsis    [Returns 1 if the state could be blocked.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_ManGeneralize( Pdr_Man_t * p, int k, Pdr_Set_t * pCube, Pdr_Set_t ** ppPred, Pdr_Set_t ** ppCubeMin )
{
    Pdr_Set_t * pCubeMin, * pCubeTmp = NULL;
    int i, j, n, Lit, RetValue;
    abctime clk = Abc_Clock();
    int * pOrder;
    // if there is no induction, return
    *ppCubeMin = NULL;
    RetValue = Pdr_ManCheckCube( p, k, pCube, ppPred, p->pPars->nConfLimit );
    if ( RetValue == -1 )
        return -1;
    if ( RetValue == 0 )
    {
        p->tGeneral += Abc_Clock() - clk;
        return 0;
    }

    // reduce clause using assumptions
//    pCubeMin = Pdr_SetDup( pCube );
    pCubeMin = Pdr_ManReduceClause( p, k, pCube );
    if ( pCubeMin == NULL )
        pCubeMin = Pdr_SetDup( pCube );

    // perform generalization
    if ( !p->pPars->fSkipGeneral )
    {
        // sort literals by their occurences
        pOrder = Pdr_ManSortByPriority( p, pCubeMin );
        // try removing literals
        for ( j = 0; j < pCubeMin->nLits; j++ )
        {
            // use ordering
    //        i = j;
            i = pOrder[j];

            // check init state
            assert( pCubeMin->Lits[i] != -1 );
            if ( Pdr_SetIsInit(pCubeMin, i) )
                continue;
            // try removing this literal
            Lit = pCubeMin->Lits[i]; pCubeMin->Lits[i] = -1;
            RetValue = Pdr_ManCheckCube( p, k, pCubeMin, NULL, p->pPars->nConfLimit );
            if ( RetValue == -1 )
            {
                Pdr_SetDeref( pCubeMin );
                return -1;
            }
            pCubeMin->Lits[i] = Lit;
            if ( RetValue == 0 )
                continue;

            // remove j-th entry
            for ( n = j; n < pCubeMin->nLits-1; n++ )
                pOrder[n] = pOrder[n+1];
            j--;

            // success - update the cube
            pCubeMin = Pdr_SetCreateFrom( pCubeTmp = pCubeMin, i );
            Pdr_SetDeref( pCubeTmp );
            assert( pCubeMin->nLits > 0 );
            i--;

            // get the ordering by decreasing priorit
            pOrder = Pdr_ManSortByPriority( p, pCubeMin );
        }

        if ( p->pPars->fTwoRounds )
        for ( j = 0; j < pCubeMin->nLits; j++ )
        {
            // use ordering
    //        i = j;
            i = pOrder[j];

            // check init state
            assert( pCubeMin->Lits[i] != -1 );
            if ( Pdr_SetIsInit(pCubeMin, i) )
                continue;
            // try removing this literal
            Lit = pCubeMin->Lits[i]; pCubeMin->Lits[i] = -1;
            RetValue = Pdr_ManCheckCube( p, k, pCubeMin, NULL, p->pPars->nConfLimit );
            if ( RetValue == -1 )
            {
                Pdr_SetDeref( pCubeMin );
                return -1;
            }
            pCubeMin->Lits[i] = Lit;
            if ( RetValue == 0 )
                continue;

            // remove j-th entry
            for ( n = j; n < pCubeMin->nLits-1; n++ )
                pOrder[n] = pOrder[n+1];
            j--;

            // success - update the cube
            pCubeMin = Pdr_SetCreateFrom( pCubeTmp = pCubeMin, i );
            Pdr_SetDeref( pCubeTmp );
            assert( pCubeMin->nLits > 0 );
            i--;

            // get the ordering by decreasing priorit
            pOrder = Pdr_ManSortByPriority( p, pCubeMin );
        }
    }

    assert( ppCubeMin != NULL );
    *ppCubeMin = pCubeMin;
    p->tGeneral += Abc_Clock() - clk;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the state could be blocked.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_ManBlockCube( Pdr_Man_t * p, Pdr_Set_t * pCube )
{
    Pdr_Obl_t * pThis;
    Pdr_Set_t * pPred, * pCubeMin;
    int i, k, RetValue, Prio = ABC_INFINITY, Counter = 0;
    int kMax = Vec_PtrSize(p->vSolvers)-1;
    abctime clk;
    p->nBlocks++;
    // create first proof obligation
//    assert( p->pQueue == NULL );
    pThis = Pdr_OblStart( kMax, Prio--, pCube, NULL ); // consume ref
    Pdr_QueuePush( p, pThis );
    // try to solve it recursively
    while ( !Pdr_QueueIsEmpty(p) )
    {
        Counter++;
        pThis = Pdr_QueueHead( p );
        if ( pThis->iFrame == 0 )
            return 0; // SAT
        if ( pThis->iFrame > kMax ) // finished this level
            return 1;
        if ( p->nQueLim && p->nQueCur >= p->nQueLim )
        {
            p->nQueLim = p->nQueLim * 3 / 2;
            Pdr_QueueStop( p );
            return 1; // restart
        }
        pThis = Pdr_QueuePop( p );
        assert( pThis->iFrame > 0 );
        assert( !Pdr_SetIsInit(pThis->pState, -1) );
        p->iUseFrame = Abc_MinInt( p->iUseFrame, pThis->iFrame );
        clk = Abc_Clock();
        if ( Pdr_ManCheckContainment( p, pThis->iFrame, pThis->pState ) )
        {
            p->tContain += Abc_Clock() - clk;
            Pdr_OblDeref( pThis );
            continue;
        }
        p->tContain += Abc_Clock() - clk;

        // check if the cube is already contained
        RetValue = Pdr_ManCheckCubeCs( p, pThis->iFrame, pThis->pState );
        if ( RetValue == -1 ) // resource limit is reached
        {
            Pdr_OblDeref( pThis );
            return -1;
        }
        if ( RetValue ) // cube is blocked by clauses in this frame
        {
            Pdr_OblDeref( pThis );
            continue;
        }

        // check if the cube holds with relative induction
        pCubeMin = NULL;
        RetValue = Pdr_ManGeneralize( p, pThis->iFrame-1, pThis->pState, &pPred, &pCubeMin );
        if ( RetValue == -1 ) // resource limit is reached
        {
            Pdr_OblDeref( pThis );
            return -1;
        }
        if ( RetValue ) // cube is blocked inductively in this frame
        {
            assert( pCubeMin != NULL );
            // k is the last frame where pCubeMin holds
            k = pThis->iFrame;
            // check other frames
            assert( pPred == NULL );
            for ( k = pThis->iFrame; k < kMax; k++ )
            {
                RetValue = Pdr_ManCheckCube( p, k, pCubeMin, NULL, 0 );
                if ( RetValue == -1 )
                {
                    Pdr_OblDeref( pThis );
                    return -1;
                }
                if ( !RetValue )
                    break;
            }
            // add new clause
            if ( p->pPars->fVeryVerbose )
            {
                Abc_Print( 1, "Adding cube " );
                Pdr_SetPrint( stdout, pCubeMin, Aig_ManRegNum(p->pAig), NULL );
                Abc_Print( 1, " to frame %d.\n", k );
            }
            // set priority flops
            for ( i = 0; i < pCubeMin->nLits; i++ )
            {
                assert( pCubeMin->Lits[i] >= 0 );
                assert( (pCubeMin->Lits[i] / 2) < Aig_ManRegNum(p->pAig) );
                Vec_IntAddToEntry( p->vPrio, pCubeMin->Lits[i] / 2, 1 );
            }
            Vec_VecPush( p->vClauses, k, pCubeMin );   // consume ref
            p->nCubes++;
            // add clause
            for ( i = 1; i <= k; i++ )
                Pdr_ManSolverAddClause( p, i, pCubeMin );
            // schedule proof obligation
            if ( (k < kMax || p->pPars->fReuseProofOblig) && !p->pPars->fShortest )
            {
                pThis->iFrame = k+1;
                pThis->prio   = Prio--;
                Pdr_QueuePush( p, pThis );
            }
            else
            {
                Pdr_OblDeref( pThis );
            }
        }
        else
        {
            assert( pCubeMin == NULL );
            assert( pPred != NULL );
            pThis->prio = Prio--;
            Pdr_QueuePush( p, pThis );
            pThis = Pdr_OblStart( pThis->iFrame-1, Prio--, pPred, Pdr_OblRef(pThis) );
            Pdr_QueuePush( p, pThis );
        }

        // check termination
        if ( p->pPars->pFuncStop && p->pPars->pFuncStop(p->pPars->RunId) )
            return -1;
        if ( p->timeToStop && Abc_Clock() > p->timeToStop )
            return -1;
        if ( p->timeToStopOne && Abc_Clock() > p->timeToStopOne )
            return -1;
        if ( p->pPars->nTimeOutGap && p->pPars->timeLastSolved && Abc_Clock() > p->pPars->timeLastSolved + p->pPars->nTimeOutGap * CLOCKS_PER_SEC )
            return -1;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_ManSolveInt( Pdr_Man_t * p )
{
    int fPrintClauses = 0;
    Pdr_Set_t * pCube = NULL;
    Aig_Obj_t * pObj;
    Abc_Cex_t * pCexNew;
    int k, RetValue = -1;
    int nOutDigits = Abc_Base10Log( Saig_ManPoNum(p->pAig) );
    abctime clkStart = Abc_Clock(), clkOne = 0;
    p->timeToStop = p->pPars->nTimeOut ? p->pPars->nTimeOut * CLOCKS_PER_SEC + Abc_Clock(): 0;
    assert( Vec_PtrSize(p->vSolvers) == 0 );
    // in the multi-output mode, mark trivial POs (those fed by const0) as solved 
    if ( p->pPars->fSolveAll )
        Saig_ManForEachPo( p->pAig, pObj, k )
            if ( Aig_ObjChild0(pObj) == Aig_ManConst0(p->pAig) )
            {
                Vec_IntWriteEntry( p->pPars->vOutMap, k, 1 ); // unsat
                p->pPars->nProveOuts++;
                if ( p->pPars->fUseBridge )
                    Gia_ManToBridgeResult( stdout, 1, NULL, k );
            }
    // create the first timeframe
    p->pPars->timeLastSolved = Abc_Clock();
    Pdr_ManCreateSolver( p, (k = 0) );
    while ( 1 )
    {
        p->nFrames = k;
        assert( k == Vec_PtrSize(p->vSolvers)-1 );
        p->iUseFrame = Abc_MaxInt(k, 1);
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
                    pCexNew = Abc_CexMakeTriv( Aig_ManRegNum(p->pAig), Saig_ManPiNum(p->pAig), Saig_ManPoNum(p->pAig), k*Saig_ManPoNum(p->pAig)+p->iOutCur );
                    p->pAig->pSeqModel = pCexNew;
                    return 0; // SAT
                }
                pCexNew = (p->pPars->fUseBridge || p->pPars->fStoreCex) ? Abc_CexMakeTriv( Aig_ManRegNum(p->pAig), Saig_ManPiNum(p->pAig), Saig_ManPoNum(p->pAig), k*Saig_ManPoNum(p->pAig)+p->iOutCur ) : (Abc_Cex_t *)(ABC_PTRINT_T)1;
                p->pPars->nFailOuts++;
                if ( p->pPars->vOutMap ) Vec_IntWriteEntry( p->pPars->vOutMap, p->iOutCur, 0 );
                if ( !p->pPars->fNotVerbose )
                Abc_Print( 1, "Output %*d was trivially asserted in frame %2d (solved %*d out of %*d outputs).\n",
                    nOutDigits, p->iOutCur, k, nOutDigits, p->pPars->nFailOuts, nOutDigits, Saig_ManPoNum(p->pAig) );
                assert( Vec_PtrEntry(p->vCexes, p->iOutCur) == NULL );
                if ( p->pPars->fUseBridge )
                    Gia_ManToBridgeResult( stdout, 0, pCexNew, pCexNew->iPo );
                Vec_PtrWriteEntry( p->vCexes, p->iOutCur, pCexNew );
                if ( p->pPars->pFuncOnFail && p->pPars->pFuncOnFail(p->iOutCur, p->pPars->fStoreCex ? (Abc_Cex_t *)Vec_PtrEntry(p->vCexes, p->iOutCur) : NULL) )
                {
                    if ( p->pPars->fVerbose )
                        Pdr_ManPrintProgress( p, 1, Abc_Clock() - clkStart );
                    if ( !p->pPars->fSilent )
                        Abc_Print( 1, "Quitting due to callback on fail.\n" );
                    p->pPars->iFrame = k;
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
                        Abc_Print( 1, "Reached gap timeout (%d seconds).\n",  p->pPars->nTimeOutGap );
                    p->pPars->iFrame = k;
                    return -1;
                }
                RetValue = Pdr_ManCheckCube( p, k, NULL, &pCube, p->pPars->nConfLimit );
                if ( RetValue == 1 )
                    break;
                if ( RetValue == -1 )
                {
                    if ( p->pPars->fVerbose )
                        Pdr_ManPrintProgress( p, 1, Abc_Clock() - clkStart );
                    if ( p->timeToStop && Abc_Clock() > p->timeToStop )
                        Abc_Print( 1, "Reached timeout (%d seconds).\n",  p->pPars->nTimeOut );
                    else if ( p->pPars->nTimeOutGap && p->pPars->timeLastSolved && Abc_Clock() > p->pPars->timeLastSolved + p->pPars->nTimeOutGap * CLOCKS_PER_SEC )
                        Abc_Print( 1, "Reached gap timeout (%d seconds).\n",  p->pPars->nTimeOutGap );
                    else if ( p->timeToStopOne && Abc_Clock() > p->timeToStopOne )
                    {
                        Pdr_QueueClean( p );
                        pCube = NULL;
                        break; // keep solving
                    }
                    else if ( p->pPars->nConfLimit )
                        Abc_Print( 1, "Reached conflict limit (%d).\n",  p->pPars->nConfLimit );
                    else if ( p->pPars->fVerbose )
                        Abc_Print( 1, "Computation cancelled by the callback.\n" );
                    p->pPars->iFrame = k;
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
                            Abc_Print( 1, "Reached timeout (%d seconds).\n",  p->pPars->nTimeOut );
                        else if ( p->pPars->nTimeOutGap && p->pPars->timeLastSolved && Abc_Clock() > p->pPars->timeLastSolved + p->pPars->nTimeOutGap * CLOCKS_PER_SEC )
                            Abc_Print( 1, "Reached gap timeout (%d seconds).\n",  p->pPars->nTimeOutGap );
                        else if ( p->timeToStopOne && Abc_Clock() > p->timeToStopOne )
                        {
                            Pdr_QueueClean( p );
                            pCube = NULL;
                            break; // keep solving
                        }
                        else if ( p->pPars->nConfLimit )
                            Abc_Print( 1, "Reached conflict limit (%d).\n",  p->pPars->nConfLimit );
                        else if ( p->pPars->fVerbose )
                            Abc_Print( 1, "Computation cancelled by the callback.\n" );
                        p->pPars->iFrame = k;
                        return -1;
                    }
                    if ( RetValue == 0 )
                    {
                        if ( fPrintClauses )
                        {
                            Abc_Print( 1, "*** Clauses after frame %d:\n", k );
                            Pdr_ManPrintClauses( p, 0 );
                        }
                        if ( p->pPars->fVerbose )
                            Pdr_ManPrintProgress( p, !p->pPars->fSolveAll, Abc_Clock() - clkStart );
                        p->pPars->iFrame = k;
                        if ( !p->pPars->fSolveAll )
                        {
                            p->pAig->pSeqModel = Pdr_ManDeriveCex(p);
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
                                Abc_Print( 1, "Quitting due to callback on fail.\n" );
                            p->pPars->iFrame = k;
                            return -1;
                        }
                        if ( !p->pPars->fNotVerbose )
                            Abc_Print( 1, "Output %*d was asserted in frame %2d (%2d) (solved %*d out of %*d outputs).\n",
                                nOutDigits, p->iOutCur, k, k, nOutDigits, p->pPars->nFailOuts, nOutDigits, Saig_ManPoNum(p->pAig) );
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
                        Abc_Print( 1, "Timing out on output %*d.\n", nOutDigits, p->iOutCur );
                }
                p->timeToStopOne = 0;
            }
        }

        if ( p->pPars->fVerbose )
            Pdr_ManPrintProgress( p, 1, Abc_Clock() - clkStart );
        // open a new timeframe
        p->nQueLim = p->pPars->nRestLimit;
        assert( pCube == NULL );
        Pdr_ManSetPropertyOutput( p, k );
        Pdr_ManCreateSolver( p, ++k );
        if ( fPrintClauses )
        {
            Abc_Print( 1, "*** Clauses after frame %d:\n", k );
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
                    Abc_Print( 1, "Reached timeout (%d seconds).\n",  p->pPars->nTimeOut );
                else
                    Abc_Print( 1, "Reached conflict limit (%d).\n",  p->pPars->nConfLimit );
            }
            p->pPars->iFrame = k;
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
            p->pPars->iFrame = k;
            // count the number of UNSAT outputs
            p->pPars->nProveOuts = Saig_ManPoNum(p->pAig) - p->pPars->nFailOuts - p->pPars->nDropOuts;
            // convert previously 'unknown' into 'unsat'
            if ( p->pPars->vOutMap )
                for ( k = 0; k < Saig_ManPoNum(p->pAig); k++ )
                    if ( Vec_IntEntry(p->pPars->vOutMap, k) == -2 ) // unknown
                    {
                        Vec_IntWriteEntry( p->pPars->vOutMap, k, 1 ); // unsat
                        if ( p->pPars->fUseBridge )
                            Gia_ManToBridgeResult( stdout, 1, NULL, k );
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
            p->pPars->iFrame = k;
            return -1;
        }
        if ( p->timeToStop && Abc_Clock() > p->timeToStop )
        {
            if ( fPrintClauses )
            {
                Abc_Print( 1, "*** Clauses after frame %d:\n", k );
                Pdr_ManPrintClauses( p, 0 );
            }
            if ( p->pPars->fVerbose )
                Pdr_ManPrintProgress( p, 1, Abc_Clock() - clkStart );
            if ( !p->pPars->fSilent )
                Abc_Print( 1, "Reached timeout (%d seconds).\n",  p->pPars->nTimeOut );
            p->pPars->iFrame = k;
            return -1;
        }
        if ( p->pPars->nTimeOutGap && p->pPars->timeLastSolved && Abc_Clock() > p->pPars->timeLastSolved + p->pPars->nTimeOutGap * CLOCKS_PER_SEC )
        {
            if ( fPrintClauses )
            {
                Abc_Print( 1, "*** Clauses after frame %d:\n", k );
                Pdr_ManPrintClauses( p, 0 );
            }
            if ( p->pPars->fVerbose )
                Pdr_ManPrintProgress( p, 1, Abc_Clock() - clkStart );
            if ( !p->pPars->fSilent )
                Abc_Print( 1, "Reached gap timeout (%d seconds).\n",  p->pPars->nTimeOutGap );
            p->pPars->iFrame = k;
            return -1;
        }
        if ( p->pPars->nFrameMax && k >= p->pPars->nFrameMax )
        {
            if ( p->pPars->fVerbose )
                Pdr_ManPrintProgress( p, 1, Abc_Clock() - clkStart );
            if ( !p->pPars->fSilent )
                Abc_Print( 1, "Reached limit on the number of timeframes (%d).\n", p->pPars->nFrameMax );
            p->pPars->iFrame = k;
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
int Pdr_ManSolve( Aig_Man_t * pAig, Pdr_Par_t * pPars )
{
    Pdr_Man_t * p;
    int k, RetValue;
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
    RetValue = Pdr_ManSolveInt( p );
    if ( RetValue == 0 )
        assert( pAig->pSeqModel != NULL || p->vCexes != NULL );
    if ( RetValue == 1 )
        Abc_FrameSetInv( Pdr_ManCountFlopsInv(p) );
    else
        Abc_FrameSetInv( NULL );
    if ( p->vCexes )
    {
        assert( p->pAig->vSeqModelVec == NULL );
        p->pAig->vSeqModelVec = p->vCexes;
        p->vCexes = NULL;
    }
    if ( p->pPars->fDumpInv )
        Pdr_ManDumpClauses( p, (char *)"inv.pla", RetValue==1 );
    p->tTotal += Abc_Clock() - clk;
    Pdr_ManStop( p );
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

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
