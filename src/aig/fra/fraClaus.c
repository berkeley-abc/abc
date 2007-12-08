/**CFile****************************************************************

  FileName    [fraClaus.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New FRAIG package.]

  Synopsis    [Induction with clause strengthening.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 30, 2007.]

  Revision    [$Id: fraClau.c,v 1.00 2007/06/30 00:00:00 alanmi Exp $]

***********************************************************************/

#include "fra.h"
#include "cnf.h"
#include "satSolver.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Clu_Man_t_    Clu_Man_t;
struct Clu_Man_t_
{
    // parameters
    int              nFrames;
    int              nClausesMax;
    int              fVerbose;
    int              fVeryVerbose;
    int              nSimWords;
    int              nSimFrames;
    // the network
    Aig_Man_t *      pAig;
    // SAT solvers
    sat_solver *     pSatMain;
    sat_solver *     pSatBmc;
    // CNF for the test solver
    Cnf_Dat_t *      pCnf;
    // the counter example
    Vec_Int_t *      vValues;
    // clauses
    Vec_Int_t *      vLits;
    Vec_Int_t *      vClauses;
    Vec_Int_t *      vCosts;
    int              nClauses;
    // counter-examples
    Vec_Ptr_t *      vCexes;
    int              nCexes;
    int              nCexesAlloc;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Runs the SAT solver on the problem.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_ClausRunBmc( Clu_Man_t * p )
{
    Aig_Obj_t * pObj;
    int * pLits;
    int nBTLimit = 0;
    int i, RetValue;
    pLits = ALLOC( int, p->nFrames + 1 );
    // set the output literals
    pObj = Aig_ManPo(p->pAig, 0);
    for ( i = 0; i < p->nFrames; i++ )
        pLits[i] = i * 2 * p->pCnf->nVars + toLitCond( p->pCnf->pVarNums[pObj->Id], 0 ); 
    // try to solve the problem
//    sat_solver_act_var_clear( p->pSatBmc );
//    RetValue = sat_solver_solve( p->pSatBmc, NULL, NULL, (sint64)nBTLimit, (sint64)0, (sint64)0, (sint64)0 );
    for ( i = 0; i < p->nFrames; i++ )
    {
        RetValue = sat_solver_solve( p->pSatBmc, pLits + i, pLits + i + 1, (sint64)nBTLimit, (sint64)0, (sint64)0, (sint64)0 );
        if ( RetValue != l_False )
        {
            free( pLits );
            return 0;
        }
    }
    free( pLits );

/*
    // get the counter-example
    assert( RetValue == l_True );
    nVarsTot = p->nFrames * p->pCnf->nVars;
    Aig_ManForEachObj( p->pAig, pObj, i )
        Vec_IntWriteEntry( p->vValues, i, sat_solver_var_value(p->pSatBmc, nVarsTot + p->pCnf->pVarNums[i]) );
*/
    return 1;
}

/**Function*************************************************************

  Synopsis    [Runs the SAT solver on the problem.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_ClausRunSat( Clu_Man_t * p )
{
    int nBTLimit = 0;
    Aig_Obj_t * pObj;
    int * pLits;
    int i, nVarsTot, RetValue;
    pLits = ALLOC( int, p->nFrames + 1 );
    // set the output literals
    pObj = Aig_ManPo(p->pAig, 0);
    for ( i = 0; i <= p->nFrames; i++ )
        pLits[i] = i * 2 * p->pCnf->nVars + toLitCond( p->pCnf->pVarNums[pObj->Id], i != p->nFrames ); 
    // try to solve the problem
//    sat_solver_act_var_clear( p->pSatMain );
//    RetValue = sat_solver_solve( p->pSatMain, NULL, NULL, (sint64)nBTLimit, (sint64)0, (sint64)0, (sint64)0 );
    RetValue = sat_solver_solve( p->pSatMain, pLits, pLits + p->nFrames + 1, (sint64)nBTLimit, (sint64)0, (sint64)0, (sint64)0 );
    free( pLits );
    if ( RetValue == l_False )
        return 1;
    // get the counter-example
    assert( RetValue == l_True );
    nVarsTot = p->nFrames * p->pCnf->nVars;
    Aig_ManForEachObj( p->pAig, pObj, i )
        Vec_IntWriteEntry( p->vValues, i, sat_solver_var_value(p->pSatMain, nVarsTot + p->pCnf->pVarNums[i]) );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Runs the SAT solver on the problem.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_ClausRunSat0( Clu_Man_t * p )
{
    int nBTLimit = 0;
    Aig_Obj_t * pObj;
    int Lits[2], RetValue;
    pObj = Aig_ManPo(p->pAig, 0);
    Lits[0] = toLitCond( p->pCnf->pVarNums[pObj->Id], 0 ); 
    RetValue = sat_solver_solve( p->pSatMain, Lits, Lits + 1, (sint64)nBTLimit, (sint64)0, (sint64)0, (sint64)0 );
    if ( RetValue == l_False )
        return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Processes the clauses.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
/*
int Fra_ClausProcessClausesCut( Clu_Man_t * p, Dar_Cut_t * pCut )
{
    unsigned * pSimsC[4], * pSimsS[4];
    int pLits[4];
    int i, b, k, iMint, uMask, RetValue, nLeaves, nWordsTotal, nCounter;
    // compute parameters
    nLeaves = pCut->nLeaves;
    nWordsTotal = p->pComb->nWordsTotal;
    assert( nLeaves > 1 && nLeaves < 5 );
    assert( nWordsTotal == p->pSeq->nWordsTotal );
    // get parameters
    for ( i = 0; i < (int)pCut->nLeaves; i++ )
    {
        pSimsC[i] = Fra_ObjSim( p->pComb, pCut->pLeaves[i] );
        pSimsS[i] = Fra_ObjSim( p->pSeq,  pCut->pLeaves[i] );
    }
    // add combinational patterns
    uMask = 0;
    for ( i = 0; i < nWordsTotal; i++ )
        for ( k = 0; k < 32; k++ )
        {
            iMint = 0;
            for ( b = 0; b < nLeaves; b++ )
                if ( pSimsC[b][i] & (1 << k) )
                    iMint |= (1 << b);
            uMask |= (1 << iMint);
        }
    // remove sequential patterns
    for ( i = 0; i < nWordsTotal; i++ )
        for ( k = 0; k < 32; k++ )
        {
            iMint = 0;
            for ( b = 0; b < nLeaves; b++ )
                if ( pSimsS[b][i] & (1 << k) )
                    iMint |= (1 << b);
            uMask &= ~(1 << iMint);
        }
    if ( uMask == 0 )
        return 0;
    // add clauses for the remaining patterns
    nCounter = 0;
    for ( i = 0; i < (1<<nLeaves); i++ )
    {
        if ( (uMask & (1 << i)) == 0 )
            continue;
        nCounter++;
//        continue;

        // add every third clause
//        if ( (nCounter % 2) == 0 )
//            continue;

        for ( b = 0; b < nLeaves; b++ )
            pLits[b] = toLitCond( p->pCnf->pVarNums[pCut->pLeaves[b]], (i&(1<<b)) );
        // add the clause
        RetValue = sat_solver_addclause( p->pSatMain, pLits, pLits + nLeaves );
//        assert( RetValue == 1 );
        if ( RetValue == 0 )
        {
            printf( "Already UNSAT after %d clauses.\n", nCounter );
            return -1;
        }
    }
    return nCounter;
}
*/


/**Function*************************************************************

  Synopsis    [Return combinations appearing in the cut.]

  Description [This procedure is taken from "Hacker's Delight" by H.S.Warren.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void transpose32a( unsigned a[32] ) 
{
    int j, k;
    unsigned long m, t;
    for ( j = 16, m = 0x0000FFFF; j; j >>= 1, m ^= m << j ) 
    {
        for ( k = 0; k < 32; k = ((k | j) + 1) & ~j ) 
        {
            t = (a[k] ^ (a[k|j] >> j)) & m;
            a[k] ^= t;
            a[k|j] ^= (t << j);
        }
    }
}

/**Function*************************************************************

  Synopsis    [Return combinations appearing in the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_ClausProcessClausesCut( Clu_Man_t * p, Fra_Sml_t * pSimMan, Dar_Cut_t * pCut, int * pScores )
{
    unsigned Matrix[32];
    unsigned * pSims[4], uWord;
    int nSeries, i, k, j;
    // compute parameters
    assert( pCut->nLeaves > 1 && pCut->nLeaves < 5 );
    assert( pSimMan->nWordsTotal % 8 == 0 );
    // get parameters
    for ( i = 0; i < (int)pCut->nLeaves; i++ )
        pSims[i] = Fra_ObjSim( pSimMan, pCut->pLeaves[i] );
    // add combinational patterns
    memset( pScores, 0, sizeof(int) * 16 );
    nSeries = pSimMan->nWordsTotal / 8;
    for ( i = 0; i < nSeries; i++ )
    {
        memset( Matrix, 0, sizeof(unsigned) * 32 );
        for ( k = 0; k < 8; k++ )
            for ( j = 0; j < (int)pCut->nLeaves; j++ )
                Matrix[31-(k*4+j)] = pSims[j][i*8+k];
/*
        for ( k = 0; k < 32; k++ )
        {
            Extra_PrintBinary( stdout, Matrix + k, 32 ); printf( "\n" );
        }
        printf( "\n" );
*/
        transpose32a( Matrix );
/*
        for ( k = 0; k < 32; k++ )
        {
            Extra_PrintBinary( stdout, Matrix + k, 32 ); printf( "\n" );
        }
        printf( "\n" );
*/
        for ( k = 0; k < 32; k++ )
            for ( j = 0, uWord = Matrix[k]; j < 8; j++, uWord >>= 4 )
                pScores[uWord & 0xF]++;
    }
    // collect patterns
    uWord = 0;
    for ( i = 0; i < 16; i++ )
        if ( pScores[i] )
            uWord |= (1 << i);
//    Extra_PrintBinary( stdout, &uWord, 16 ); printf( "\n" );
    return (int)uWord;
}

/**Function*************************************************************

  Synopsis    [Return combinations appearing in the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_ClausProcessClausesCut2( Clu_Man_t * p, Fra_Sml_t * pSimMan, Dar_Cut_t * pCut, int * pScores )
{
    unsigned * pSims[4], uWord;
    int iMint, i, k, b;
    // compute parameters
    assert( pCut->nLeaves > 1 && pCut->nLeaves < 5 );
    assert( pSimMan->nWordsTotal % 8 == 0 );
    // get parameters
    for ( i = 0; i < (int)pCut->nLeaves; i++ )
        pSims[i] = Fra_ObjSim( pSimMan, pCut->pLeaves[i] );
    // add combinational patterns
    memset( pScores, 0, sizeof(int) * 16 );
    for ( i = 0; i < pSimMan->nWordsTotal; i++ )
        for ( k = 0; k < 32; k++ )
        {
            iMint = 0;
            for ( b = 0; b < (int)pCut->nLeaves; b++ )
                if ( pSims[b][i] & (1 << k) )
                    iMint |= (1 << b);
            pScores[iMint]++;
        }
    // collect patterns
    uWord = 0;
    for ( i = 0; i < 16; i++ )
        if ( pScores[i] )
            uWord |= (1 << i);
//    Extra_PrintBinary( stdout, &uWord, 16 ); printf( "\n" );
    return (int)uWord;
}

/**Function*************************************************************

  Synopsis    [Processes the clauses.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_ClausRecordClause( Clu_Man_t * p, Dar_Cut_t * pCut, int iMint, int Cost )
{
    int i;
    for ( i = 0; i < (int)pCut->nLeaves; i++ )
        Vec_IntPush( p->vLits, toLitCond( p->pCnf->pVarNums[pCut->pLeaves[i]], (iMint&(1<<i)) ) );
    Vec_IntPush( p->vClauses, Vec_IntSize(p->vLits) );
    Vec_IntPush( p->vCosts, Cost );
}

/**Function*************************************************************

  Synopsis    [Processes the clauses.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_ClausProcessClauses( Clu_Man_t * p )
{
    Aig_MmFixed_t * pMemCuts;
    Fra_Sml_t * pComb, * pSeq;
    Aig_Obj_t * pObj;
    Dar_Cut_t * pCut;
    int Scores[16], uScores, i, k, j, clk, nCuts = 0;

    // simulate the AIG
clk = clock();
    srand( 0xAABBAABB );
    pSeq = Fra_SmlSimulateSeq( p->pAig, 0, p->nSimFrames, p->nSimWords/p->nSimFrames );
    if ( pSeq->fNonConstOut )
    {
        printf( "Property failed after sequential simulation!\n" );
        Fra_SmlStop( pSeq );
        return 0;
    }
PRT( "Sim-seq", clock() - clk );

    // generate cuts for all nodes, assign cost, and find best cuts
clk = clock();
    pMemCuts = Dar_ManComputeCuts( p->pAig, 10 );
PRT( "Cuts   ", clock() - clk );

    // collect sequential info for each cut
clk = clock();
    Aig_ManForEachNode( p->pAig, pObj, i )
        Dar_ObjForEachCut( pObj, pCut, k )
            if ( pCut->nLeaves > 1 )
            {
                pCut->uTruth = Fra_ClausProcessClausesCut( p, pSeq, pCut, Scores );
//                uScores = Fra_ClausProcessClausesCut2( p, pSeq, pCut, Scores );
//                if ( uScores != pCut->uTruth )
//                {
//                    int x = 0;
//                }
            }
PRT( "Infoseq", clock() - clk );
    Fra_SmlStop( pSeq );

    // perform combinational simulation
clk = clock();
    srand( 0xAABBAABB );
    pComb = Fra_SmlSimulateComb( p->pAig, p->nSimWords );
PRT( "Sim-cmb", clock() - clk );

    // collect combinational info for each cut
clk = clock();
    Aig_ManForEachNode( p->pAig, pObj, i )
        Dar_ObjForEachCut( pObj, pCut, k )
            if ( pCut->nLeaves > 1 )
            {
                nCuts++;
                uScores = Fra_ClausProcessClausesCut( p, pComb, pCut, Scores );
                uScores &= ~pCut->uTruth; pCut->uTruth = 0;
                if ( uScores == 0 )
                    continue;
                // write the clauses
                for ( j = 0; j < (1<<pCut->nLeaves); j++ )
                    if ( uScores & (1 << j) )
                        Fra_ClausRecordClause( p, pCut, j, Scores[j] );

            }
    Fra_SmlStop( pComb );
    Aig_MmFixedStop( pMemCuts, 0 );
PRT( "Infocmb", clock() - clk );

    printf( "Node = %5d. Non-triv cuts = %7d. Clauses = %6d. Clause per cut = %6.2f.\n", 
        Aig_ManNodeNum(p->pAig), nCuts, Vec_IntSize(p->vClauses), 1.0*Vec_IntSize(p->vClauses)/nCuts );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Converts AIG into the SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_ClausBmcClauses( Clu_Man_t * p )
{
    int nBTLimit = 0;
    int * pStart, nLitsTot, RetValue, Beg, End, Counter, i, k, f;
/*
    for ( i = 0; i < Vec_IntSize(p->vLits); i++ )
        printf( "%d ", p->vLits->pArray[i] );
    printf( "\n" );
*/
    // add the clauses
    Counter = 0;
    nLitsTot = 2 * p->pCnf->nVars;
    for ( f = 0; f < p->nFrames; f++ )
    {
        Beg = 0;
        Vec_IntForEachEntry( p->vClauses, End, i )
        {
            if ( Vec_IntEntry( p->vCosts, i ) == -1 )
            {
                Beg = End;
                continue;
            }
            assert( Vec_IntEntry( p->vCosts, i ) > 0 );
            assert( End - Beg < 5 );
            pStart = Vec_IntArray(p->vLits);
            for ( k = Beg; k < End; k++ )
                pStart[k] = lit_neg( pStart[k] );
            RetValue = sat_solver_solve( p->pSatBmc, pStart + Beg, pStart + End, (sint64)nBTLimit, (sint64)0, (sint64)0, (sint64)0 );
            for ( k = Beg; k < End; k++ )
                pStart[k] = lit_neg( pStart[k] );
            if ( RetValue != l_False )
            {
                Beg = End;
                Vec_IntWriteEntry( p->vCosts, i, -1 );
                Counter++;
                continue;
            }
/*
            // add the clause
            RetValue = sat_solver_addclause( p->pSatBmc, pStart + Beg, pStart + End );
    //        assert( RetValue == 1 );
            if ( RetValue == 0 )
            {
                printf( "Error: Solver is UNSAT after adding BMC clauses.\n" );
                return -1;
            }
*/
            Beg = End;

            // simplify the solver
            if ( p->pSatBmc->qtail != p->pSatBmc->qhead )
            {
                RetValue = sat_solver_simplify(p->pSatBmc);
                assert( RetValue != 0 );
                assert( p->pSatBmc->qtail == p->pSatBmc->qhead );
            }
        }
        // increment literals
        for ( i = 0; i < Vec_IntSize(p->vLits); i++ )
            p->vLits->pArray[i] += nLitsTot;
    }

    // return clauses back to normal
    nLitsTot = p->nFrames * nLitsTot;
    for ( i = 0; i < Vec_IntSize(p->vLits); i++ )
        p->vLits->pArray[i] -= nLitsTot;
/*
    for ( i = 0; i < Vec_IntSize(p->vLits); i++ )
        printf( "%d ", p->vLits->pArray[i] );
    printf( "\n" );
*/
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Converts AIG into the SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_ClausInductiveClauses( Clu_Man_t * p )
{
    int nBTLimit = 0;
    int * pStart, nLitsTot, RetValue, Beg, End, Counter, i, k, f;

    // reset the solver
    if ( p->pSatMain )  sat_solver_delete( p->pSatMain );
    p->pSatMain = Cnf_DataWriteIntoSolver( p->pCnf, p->nFrames+1, 0 );
    if ( p->pSatMain == NULL )
    {
        printf( "Error: Main solver is unsat.\n" );
        return -1;
    }
/*
    // check if the property holds
    if ( Fra_ClausRunSat0( p ) )
        printf( "Property holds without strengthening.\n" );
    else
        printf( "Property does not hold without strengthening.\n" );
*/
    // add the clauses
    nLitsTot = 2 * p->pCnf->nVars;
    for ( f = 0; f < p->nFrames; f++ )
    {
        Beg = 0;
        Vec_IntForEachEntry( p->vClauses, End, i )
        {
            if ( Vec_IntEntry( p->vCosts, i ) == -1 )
            {
                Beg = End;
                continue;
            }
            assert( Vec_IntEntry( p->vCosts, i ) > 0 );
            assert( End - Beg < 5 );
            pStart = Vec_IntArray(p->vLits);
            // add the clause to all timeframes
            RetValue = sat_solver_addclause( p->pSatMain, pStart + Beg, pStart + End );
            if ( RetValue == 0 )
            {
                printf( "Error: Solver is UNSAT after adding assumption clauses.\n" );
                return -1;
            }
            Beg = End;
        }
        // increment literals
        for ( i = 0; i < Vec_IntSize(p->vLits); i++ )
            p->vLits->pArray[i] += nLitsTot;
    }

    // simplify the solver
    if ( p->pSatMain->qtail != p->pSatMain->qhead )
    {
        RetValue = sat_solver_simplify(p->pSatMain);
        assert( RetValue != 0 );
        assert( p->pSatMain->qtail == p->pSatMain->qhead );
    }
  
    // check if the property holds
    if ( Fra_ClausRunSat0( p ) )
    {
//        printf( "Property holds with strengthening.\n" );
        printf( " Property holds.  " );
    }
    else
    {
        printf( " Property fails.  " );
        return -2;
    }

/*
    // add the property for the first K frames
    for ( i = 0; i < p->nFrames; i++ )
    {
        Aig_Obj_t * pObj;
        int Lits[2];
        // set the output literals
        pObj = Aig_ManPo(p->pAig, 0);
        Lits[0] = i * nLitsTot + toLitCond( p->pCnf->pVarNums[pObj->Id], 1 ); 
        // add the clause
        RetValue = sat_solver_addclause( p->pSatMain, Lits, Lits + 1 );
//        assert( RetValue == 1 );
        if ( RetValue == 0 )
        {
            printf( "Error: Solver is UNSAT after adding property for the first K frames.\n" );
            return -1;
        }
    }
*/

    // simplify the solver
    if ( p->pSatMain->qtail != p->pSatMain->qhead )
    {
        RetValue = sat_solver_simplify(p->pSatMain);
        assert( RetValue != 0 );
        assert( p->pSatMain->qtail == p->pSatMain->qhead );
    }


    // check the clause in the last timeframe
    Beg = 0;
    Counter = 0;
    Vec_IntForEachEntry( p->vClauses, End, i )
    {
        if ( Vec_IntEntry( p->vCosts, i ) == -1 )
        {
            Beg = End;
            continue;
        }
        assert( Vec_IntEntry( p->vCosts, i ) > 0 );
        assert( End - Beg < 5 );
        pStart = Vec_IntArray(p->vLits);

        for ( k = Beg; k < End; k++ )
            pStart[k] = lit_neg( pStart[k] );
        RetValue = sat_solver_solve( p->pSatMain, pStart + Beg, pStart + End, (sint64)nBTLimit, (sint64)0, (sint64)0, (sint64)0 );
        for ( k = Beg; k < End; k++ )
            pStart[k] = lit_neg( pStart[k] );

        // the problem is not solved
        if ( RetValue != l_False )
        {
            Beg = End;
            Vec_IntWriteEntry( p->vCosts, i, -1 );
            Counter++;
            continue;
        }
        // add the clause
        RetValue = sat_solver_addclause( p->pSatMain, pStart + Beg, pStart + End );
//        assert( RetValue == 1 );
        if ( RetValue == 0 )
        {
            printf( "Error: Solver is UNSAT after adding BMC clauses.\n" );
            return -1;
        }
        Beg = End;

        // simplify the solver
        if ( p->pSatMain->qtail != p->pSatMain->qhead )
        {
            RetValue = sat_solver_simplify(p->pSatMain);
            assert( RetValue != 0 );
            assert( p->pSatMain->qtail == p->pSatMain->qhead );
        }
    }

    // return clauses back to normal
    nLitsTot = p->nFrames * nLitsTot;
    for ( i = 0; i < Vec_IntSize(p->vLits); i++ )
        p->vLits->pArray[i] -= nLitsTot;

    return Counter;
}


/**Function*************************************************************

  Synopsis    [Converts AIG into the SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Clu_Man_t * Fra_ClausAlloc( Aig_Man_t * pAig, int nFrames, int nClausesMax, int fVerbose, int fVeryVerbose )
{
    Clu_Man_t * p;
    p = ALLOC( Clu_Man_t, 1 );
    memset( p, 0, sizeof(Clu_Man_t) );
    p->pAig         = pAig;
    p->nFrames      = nFrames;
    p->nClausesMax  = nClausesMax;
    p->fVerbose     = fVerbose;
    p->fVeryVerbose = fVeryVerbose;
    p->nSimWords    = 256;//1024;//64;
    p->nSimFrames   = 16;//8;//32;
    p->vValues      = Vec_IntStart( Aig_ManObjNumMax(p->pAig) );

    p->vLits        = Vec_IntAlloc( 1<<14 );
    p->vClauses     = Vec_IntAlloc( 1<<12 );
    p->vCosts       = Vec_IntAlloc( 1<<12 );

    p->nCexesAlloc  = 1024;
    p->vCexes       = Vec_PtrAllocSimInfo( Aig_ManObjNumMax(p->pAig), p->nCexesAlloc/32 );
    Vec_PtrCleanSimInfo( p->vCexes, 0, p->nCexesAlloc/32 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Converts AIG into the SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_ClausFree( Clu_Man_t * p )
{
    if ( p->vCexes )    Vec_PtrFree( p->vCexes );
    if ( p->vLits )     Vec_IntFree( p->vLits );
    if ( p->vClauses )  Vec_IntFree( p->vClauses );
    if ( p->vCosts )    Vec_IntFree( p->vCosts );
    if ( p->vValues )   Vec_IntFree( p->vValues );
    if ( p->pCnf )      Cnf_DataFree( p->pCnf );
    if ( p->pSatMain )  sat_solver_delete( p->pSatMain );
    if ( p->pSatBmc )   sat_solver_delete( p->pSatBmc );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Converts AIG into the SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_Claus( Aig_Man_t * pAig, int nFrames, int nClausesMax, int fBmc, int fVerbose, int fVeryVerbose )
{
    Clu_Man_t * p;
    int clk, clkTotal = clock();
    int Iter, Counter;

    assert( Aig_ManPoNum(pAig) - Aig_ManRegNum(pAig) == 1 );

    // create the manager
    p = Fra_ClausAlloc( pAig, nFrames, nClausesMax, fVerbose, fVeryVerbose );

clk = clock();
    // derive CNF
    p->pAig->nRegs++;
    p->pCnf = Cnf_DeriveSimple( p->pAig, Aig_ManPoNum(p->pAig) );
    p->pAig->nRegs--;
PRT( "CNF    ", clock() - clk );

    // check BMC
clk = clock();
    p->pSatBmc = Cnf_DataWriteIntoSolver( p->pCnf, p->nFrames, 1 );
    if ( p->pSatBmc == NULL )
    {
        printf( "Error: BMC solver is unsat.\n" );
        Fra_ClausFree( p );
        return 1;
    }
    if ( !Fra_ClausRunBmc( p ) )
    {
        printf( "Problem trivially fails the base case.\n" );
        Fra_ClausFree( p );
        return 1;
    }
PRT( "SAT try", clock() - clk );

    // start the SAT solver
clk = clock();
    p->pSatMain = Cnf_DataWriteIntoSolver( p->pCnf, p->nFrames+1, 0 );
    if ( p->pSatMain == NULL )
    {
        printf( "Error: Main solver is unsat.\n" );
        Fra_ClausFree( p );
        return 1;
    } 
    // try solving without additional clauses
    if ( Fra_ClausRunSat( p ) )
    {
        printf( "Problem is inductive without strengthening.\n" );
        Fra_ClausFree( p );
        return 1;
    }
PRT( "SAT try", clock() - clk );
 
    // collect the candidate inductive clauses using 4-cuts
clk = clock();
    Fra_ClausProcessClauses( p );
    p->nClauses = Vec_IntSize( p->vClauses );
PRT( "Clauses", clock() - clk );


    // check clauses using BMC
    if ( fBmc ) 
    {
clk = clock();
        Counter = Fra_ClausBmcClauses( p );
        p->nClauses -= Counter;
        printf( "BMC disproved %d clauses.\n", Counter );
PRT( "Cla-bmc", clock() - clk );
    }


    // prove clauses inductively
clk = clock();
    Counter = 1;
    for ( Iter = 0; Counter > 0; Iter++ )
    {
        printf( "Iter %3d :  Begin = %5d. ", Iter, p->nClauses );
        Counter = Fra_ClausInductiveClauses( p );
        if ( Counter > 0 )
           p->nClauses -= Counter;
        printf( "End = %5d. ", p->nClauses );
//        printf( "\n" );
        PRT( "Time", clock() - clk );
        clk = clock();
    }
    if ( Counter == -1 )
        printf( "Fra_Claus(): Internal error.\n" );
    else if ( Counter == -2 )
        printf( "Property FAILS after %d iterations of refinement.\n", Iter );
    else
        printf( "Property HOLDS inductively after strengthening.\n" );

/*
clk = clock();
    if ( Fra_ClausRunSat( p ) )
        printf( "Problem is solved.\n" );
    else
        printf( "Problem is unsolved.\n" );
PRT( "SAT try", clock() - clk );
*/

PRT( "TOTAL  ", clock() - clkTotal );
printf( "\n" );
    // clean the manager
    Fra_ClausFree( p );
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


