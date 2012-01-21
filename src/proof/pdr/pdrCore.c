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

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

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
    pPars->iOutput       =      -1;  // zero-based output number
    pPars->nRecycle      =     300;  // limit on vars for recycling
    pPars->nFrameMax     =    5000;  // limit on number of timeframes
    pPars->nTimeOut      =       0;  // timeout in seconds
    pPars->nConfLimit    =  100000;  // limit on SAT solver conflicts
    pPars->fTwoRounds    =       0;  // use two rounds for generalization
    pPars->fMonoCnf      =       0;  // monolythic CNF
    pPars->fDumpInv      =       0;  // dump inductive invariant
    pPars->fShortest     =       0;  // forces bug traces to be shortest
    pPars->fVerbose      =       0;  // verbose output
    pPars->fVeryVerbose  =       0;  // very verbose output
    pPars->iFrame        =      -1;  // explored up to this frame
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
    int Counter = 0;
    int clk = clock();
    Vec_VecForEachLevelStartStop( p->vClauses, vArrayK, k, 1, kMax )
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
//                printf( "%d ", pCubeK->nLits - pCubeMin->nLits );
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
            printf( "===\n" );
            Pdr_SetPrint( stdout, pCubeK, Aig_ManRegNum(p->pAig), NULL );
            printf( "\n" );
            Pdr_SetPrint( stdout, pTemp, Aig_ManRegNum(p->pAig), NULL );
            printf( "\n" );
*/
            Pdr_SetDeref( pTemp );
            Vec_PtrWriteEntry( vArrayK, m, Vec_PtrEntryLast(vArrayK) );
            Vec_PtrPop(vArrayK);
            m--;
        }
    }
    p->tPush += clock() - clk;
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
        printf( "%2d : %5d    %5d  %5d\n", i, pArray[i], pCube->Lits[pArray[i]]>>1, pPrios[pCube->Lits[pArray[i]]>>1] );
    printf( "\n" );
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
    int i, j, n, Lit, RetValue,  clk = clock();
    int * pOrder;
    // if there is no induction, return
    *ppCubeMin = NULL;
    RetValue = Pdr_ManCheckCube( p, k, pCube, ppPred, p->pPars->nConfLimit );
    if ( RetValue == -1 )
        return -1;
    if ( RetValue == 0 )
    {
        p->tGeneral += clock() - clk;
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
    p->tGeneral += clock() - clk;
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
    int kMax = Vec_PtrSize(p->vSolvers)-1, clk;
    p->nBlocks++;
    // create first proof obligation
    assert( p->pQueue == NULL );
    pThis = Pdr_OblStart( kMax, Prio--, pCube, NULL ); // consume ref
    Pdr_QueuePush( p, pThis );
    // try to solve it recursively
    while ( !Pdr_QueueIsEmpty(p) )
    {
        Counter++;
        pThis = Pdr_QueueHead( p );
        if ( pThis->iFrame == 0 )
            return 0; // SAT
        pThis = Pdr_QueuePop( p );
        assert( pThis->iFrame > 0 );
        assert( !Pdr_SetIsInit(pThis->pState, -1) );

        clk = clock();
        if ( Pdr_ManCheckContainment( p, pThis->iFrame, pThis->pState ) )
        {
            p->tContain += clock() - clk;
            Pdr_OblDeref( pThis );
            continue;
        }
        p->tContain += clock() - clk;

        // check if the cube is already contained
        RetValue = Pdr_ManCheckCubeCs( p, pThis->iFrame, pThis->pState );
        if ( RetValue == -1 ) // cube is blocked by clauses in this frame
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
        if ( RetValue == -1 )
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
                if ( !Pdr_ManCheckCube( p, k, pCubeMin, NULL, 0 ) )
                    break;

            // add new clause
            if ( p->pPars->fVeryVerbose )
            {
            printf( "Adding cube " );
            Pdr_SetPrint( stdout, pCubeMin, Aig_ManRegNum(p->pAig), NULL );
            printf( " to frame %d.\n", k );
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
            if ( k < kMax && !p->pPars->fShortest )
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

        // check the timeout
        if ( p->timeToStop && time(NULL) > p->timeToStop )
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
    Pdr_Set_t * pCube;
    int k, RetValue = -1;
    int clkTotal = clock();
    int clkStart = clock();
    p->timeToStop = p->pPars->nTimeOut ? time(NULL) + p->pPars->nTimeOut : 0;
    assert( Vec_PtrSize(p->vSolvers) == 0 );
    // create the first timeframe
    Pdr_ManCreateSolver( p, (k = 0) );
    while ( 1 )
    {
        p->nFrames = k;
        assert( k == Vec_PtrSize(p->vSolvers)-1 );
        RetValue = Pdr_ManCheckCube( p, k, NULL, &pCube, p->pPars->nConfLimit );
        if ( RetValue == -1 )
        {
            if ( p->pPars->fVerbose ) 
                Pdr_ManPrintProgress( p, 1, clock() - clkStart );
            printf( "Reached conflict limit (%d).\n",  p->pPars->nConfLimit );
            p->pPars->iFrame = k;
            return -1;
        }
        if ( RetValue == 0 )
        {
            RetValue = Pdr_ManBlockCube( p, pCube );
            if ( RetValue == -1 )
            {
                if ( p->pPars->fVerbose ) 
                    Pdr_ManPrintProgress( p, 1, clock() - clkStart );
                printf( "Reached conflict limit (%d).\n",  p->pPars->nConfLimit );
                p->pPars->iFrame = k;
                return -1;
            }
            if ( RetValue == 0 )
            {
                if ( fPrintClauses )
                {
                    printf( "*** Clauses after frame %d:\n", k );
                    Pdr_ManPrintClauses( p, 0 );
                }
                if ( p->pPars->fVerbose ) 
                    Pdr_ManPrintProgress( p, 1, clock() - clkStart );
                p->pPars->iFrame = k;
                return 0; // SAT
            }
        }
        else
        {
            if ( p->pPars->fVerbose ) 
                Pdr_ManPrintProgress( p, 1, clock() - clkStart );
            // open a new timeframe
            assert( pCube == NULL );
            Pdr_ManSetPropertyOutput( p, k );
            Pdr_ManCreateSolver( p, ++k );
            if ( fPrintClauses )
            {
                printf( "*** Clauses after frame %d:\n", k );
                Pdr_ManPrintClauses( p, 0 );
            }
            // push clauses into this timeframe
            RetValue = Pdr_ManPushClauses( p );
            if ( RetValue == -1 )
            {
                if ( p->pPars->fVerbose ) 
                    Pdr_ManPrintProgress( p, 1, clock() - clkStart );
                printf( "Reached conflict limit (%d).\n",  p->pPars->nConfLimit );
                p->pPars->iFrame = k;
                return -1;
            }
            if ( RetValue )
            {
                if ( p->pPars->fVerbose ) 
                    Pdr_ManPrintProgress( p, 1, clock() - clkStart );
                Pdr_ManReportInvariant( p );
                Pdr_ManVerifyInvariant( p );
                p->pPars->iFrame = k;
                return 1; // UNSAT
            }
            if ( p->pPars->fVerbose ) 
                Pdr_ManPrintProgress( p, 0, clock() - clkStart );
            clkStart = clock();
        }

        // check the timeout
        if ( p->timeToStop && time(NULL) > p->timeToStop )
        {
            if ( fPrintClauses )
            {
                printf( "*** Clauses after frame %d:\n", k );
                Pdr_ManPrintClauses( p, 0 );
            }
            if ( p->pPars->fVerbose ) 
                Pdr_ManPrintProgress( p, 1, clock() - clkStart );
            printf( "Reached timeout (%d seconds).\n",  p->pPars->nTimeOut );
            p->pPars->iFrame = k;
            return -1;
        }
        if ( p->pPars->nFrameMax && k >= p->pPars->nFrameMax )
        {
            if ( p->pPars->fVerbose ) 
                Pdr_ManPrintProgress( p, 1, clock() - clkStart );
            printf( "Reached limit on the number of timeframes (%d).\n", p->pPars->nFrameMax );
            p->pPars->iFrame = k;
            return -1;
        } 
    }
    return RetValue;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_ManSolve_( Aig_Man_t * pAig, Pdr_Par_t * pPars, Vec_Int_t ** pvPrioInit, Abc_Cex_t ** ppCex )
{
    Pdr_Man_t * p;
    int RetValue;
    int clk = clock();
    p = Pdr_ManStart( pAig, pPars, pvPrioInit? *pvPrioInit : NULL );
    RetValue = Pdr_ManSolveInt( p );
    *ppCex = RetValue ? NULL : Pdr_ManDeriveCex( p );
    if ( p->pPars->fDumpInv )
        Pdr_ManDumpClauses( p, (char *)"inv.pla", RetValue==1 );

//    if ( *ppCex && pPars->fVerbose )
//        printf( "Found counter-example in frame %d after exploring %d frames.\n", 
//            (*ppCex)->iFrame, p->nFrames );
    p->tTotal += clock() - clk;
    if ( pvPrioInit )
    {
        *pvPrioInit = p->vPrio;
        p->vPrio = NULL;
    }
    Pdr_ManStop( p );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_ManSolve( Aig_Man_t * pAig, Pdr_Par_t * pPars, Abc_Cex_t ** ppCex )
{
/*
    Vec_Int_t * vPrioInit = NULL;
    int RetValue, nTimeOut;
    if ( pPars->nTimeOut > 0 )
        return Pdr_ManSolve_( pAig, pPars, NULL, ppCex );
    nTimeOut = pPars->nTimeOut;
    pPars->nTimeOut = 10;
    RetValue = Pdr_ManSolve_( pAig, pPars, &vPrioInit, ppCex );
    pPars->nTimeOut = nTimeOut;
    if ( RetValue == -1 )
        RetValue = Pdr_ManSolve_( pAig, pPars, &vPrioInit, ppCex );
    Vec_IntFree( vPrioInit );
    return RetValue;
*/
    return Pdr_ManSolve_( pAig, pPars, NULL, ppCex );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

