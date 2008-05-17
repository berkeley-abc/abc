/**CFile****************************************************************

  FileName    [saigHaig.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [Experiments with history AIG recording.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: saigHaig.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "saig.h"
#include "satSolver.h"
#include "cnf.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Prepares the inductive case with speculative reduction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManHaigSpeculate( Aig_Man_t * pFrames, Aig_Obj_t * pObj )
{
    Aig_Obj_t * pObjNew, * pObjNew2, * pObjRepr, * pObjReprNew, * pMiter;
    // skip nodes without representative
    pObjRepr = pObj->pHaig;
    if ( pObjRepr == NULL )
        return;
    assert( pObjRepr->Id < pObj->Id );
    // get the new node 
    pObjNew = pObj->pData;
    // get the new node of the representative
    pObjReprNew = pObjRepr->pData;
    // if this is the same node, no need to add constraints
    if ( Aig_Regular(pObjNew) == Aig_Regular(pObjReprNew) )
        return;
    // these are different nodes - perform speculative reduction
    pObjNew2 = Aig_NotCond( pObjReprNew, pObj->fPhase ^ pObjRepr->fPhase );
    // set the new node
    pObj->pData = pObjNew2;
    // add the constraint
    pMiter = Aig_Exor( pFrames, pObjNew, pObjReprNew );
    pMiter = Aig_NotCond( pMiter, !Aig_ObjPhaseReal(pMiter) );
    assert( Aig_ObjPhaseReal(pMiter) == 1 );
    Aig_ObjCreatePo( pFrames, pMiter );
}

/**Function*************************************************************

  Synopsis    [Prepares the inductive case with speculative reduction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManHaigFrames( Aig_Man_t * pHaig, int nFrames )
{
    Aig_Man_t * pFrames;
    Aig_Obj_t * pObj, * pObjLi, * pObjLo;
    int i, f, nAssumptions = 0;
    assert( nFrames == 1 || nFrames == 2 );
    assert( nFrames == 1 || Saig_ManRegNum(pHaig) > 0 );
    // start AIG manager for timeframes
    pFrames = Aig_ManStart( Aig_ManNodeNum(pHaig) * nFrames );
    pFrames->pName = Aig_UtilStrsav( pHaig->pName );
    pFrames->pSpec = Aig_UtilStrsav( pHaig->pSpec );
    // map the constant node
    Aig_ManConst1(pHaig)->pData = Aig_ManConst1( pFrames );
    // create variables for register outputs
    Saig_ManForEachLo( pHaig, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pFrames );
    // add timeframes
    Aig_ManSetPioNumbers( pHaig );
    for ( f = 0; f < nFrames; f++ )
    {
        Aig_ManForEachObj( pHaig, pObj, i )
        {
            if ( Aig_ObjIsConst1(pObj) || Aig_ObjIsPo(pObj) )
                continue;
            if ( Saig_ObjIsPi(pHaig, pObj) )
            {
                pObj->pData = Aig_ObjCreatePi( pFrames );
                continue;
            }
            if ( Saig_ObjIsLo(pHaig, pObj) )
            {
                Aig_ManHaigSpeculate( pFrames, pObj );
                continue;
            }
            if ( Aig_ObjIsNode(pObj) )
            {
                pObj->pData = Aig_And( pFrames, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
                Aig_ManHaigSpeculate( pFrames, pObj );
                continue;
            }
            assert( 0 );
        }
        if ( f == nFrames - 2 )
            nAssumptions = Aig_ManPoNum(pFrames);
        if ( f == nFrames - 1 )
            break;
        // save register inputs
        Saig_ManForEachLi( pHaig, pObj, i )
            pObj->pData = Aig_ObjChild0Copy(pObj);
        // transfer to register outputs
        Saig_ManForEachLiLo(  pHaig, pObjLi, pObjLo, i )
            pObjLo->pData = pObjLi->pData;
    }
    Aig_ManCleanup( pFrames );
    pFrames->nAsserts = Aig_ManPoNum(pFrames) - nAssumptions;
    Aig_ManSetRegNum( pFrames, 0 );
    return pFrames;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ManHaigVerify2( Aig_Man_t * pAig, Aig_Man_t * pHaig, int nFrames )
{
    int nBTLimit = 0;
    Aig_Man_t * pFrames;
    Cnf_Dat_t * pCnf;
    sat_solver * pSat;
    Aig_Obj_t * pObj;
    int i, Lit, RetValue, Counter;
    int clk = clock();

    // create time frames with speculative reduction and convert them into CNF
clk = clock();
    pFrames = Aig_ManHaigFrames( pHaig, nFrames );
Aig_ManShow( pFrames, 0, NULL ); 

    printf( "AIG:    " );
    Aig_ManPrintStats( pAig );
    printf( "HAIG:   " );
    Aig_ManPrintStats( pHaig );
    printf( "Frames: " );
    Aig_ManPrintStats( pFrames );
    printf( "Additional frames stats: Assumptions = %d. Asserts = %d.\n", 
        Aig_ManPoNum(pFrames) - pFrames->nAsserts, pFrames->nAsserts );
    pCnf = Cnf_DeriveSimple( pFrames, pFrames->nAsserts );
PRT( "Preparation", clock() - clk );

//    pCnf = Cnf_Derive( pFrames, Aig_ManPoNum(pFrames) - pFrames->nAsserts );
//Cnf_DataWriteIntoFile( pCnf, "temp.cnf", 1 );
    Saig_ManDumpBlif( pHaig, "haig_temp.blif" );
    Saig_ManDumpBlif( pFrames, "haig_temp_frames.blif" );
    // create the SAT solver to be used for this problem
    pSat = Cnf_DataWriteIntoSolver( pCnf, 1, 0 );
    if ( pSat == NULL )
    {
        printf( "Aig_ManHaigVerify(): Computed CNF is not valid.\n" );
        return -1;
    }
    
    // solve each output
clk = clock();
    if ( pFrames->nAsserts == 0 )
    {
        RetValue = sat_solver_solve( pSat, NULL, NULL, (sint64)nBTLimit, (sint64)0, (sint64)0, (sint64)0 );
        if ( RetValue != l_False )
            printf( "SAT solver is wrong\n" );
    }
    else
    {
        Counter = 0;
        Aig_ManForEachPo( pFrames, pObj, i )
        {
            if ( i < Aig_ManPoNum(pFrames) - pFrames->nAsserts )
                continue;
            Lit = toLitCond( pCnf->pVarNums[pObj->Id], 1 );
            RetValue = sat_solver_solve( pSat, &Lit, &Lit + 1, (sint64)nBTLimit, (sint64)0, (sint64)0, (sint64)0 );
            if ( RetValue != l_False )
                Counter++;
        }
PRT( "Solving    ", clock() - clk );
        if ( Counter )
            printf( "Verification failed for %d classes.\n", Counter );
        else
            printf( "Verification is successful.\n" );
    }

    // clean up
    Aig_ManStop( pFrames );
    Cnf_DataFree( pCnf );
    sat_solver_delete( pSat );
    return Counter;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ManHaigVerify( Aig_Man_t * pAig, Aig_Man_t * pHaig, int nFrames )
{
    int nBTLimit = 0;
    Cnf_Dat_t * pCnf;
    sat_solver * pSat;
    Aig_Obj_t * pObj, * pRepr;
    int i, RetValue, Counter, Lits[2];
    int nClasses = 0;
    int clk = clock();

    assert( nFrames == 1 || nFrames == 2 );

clk = clock();
    pCnf = Cnf_DeriveSimple( pHaig, Aig_ManPoNum(pHaig) );
    // create the SAT solver to be used for this problem
    pSat = Cnf_DataWriteIntoSolver( pCnf, nFrames, 0 );
    if ( pSat == NULL )
    {
        printf( "Aig_ManHaigVerify(): Computed CNF is not valid.\n" );
        return -1;
    }

    if ( nFrames == 2 )
    {
        // add clauses for the first frame
        Aig_ManForEachObj( pHaig, pObj, i )
        {
            pRepr = pObj->pHaig;
            if ( pRepr == NULL )
                continue;
            if ( pRepr->fPhase ^ pObj->fPhase )
            {
                Lits[0] = toLitCond( pCnf->pVarNums[pObj->Id], 0 );
                Lits[1] = toLitCond( pCnf->pVarNums[pRepr->Id], 0 );
                if ( !sat_solver_addclause( pSat, Lits, Lits + 2 ) )
                {
                    sat_solver_delete( pSat );
                    return 0;
                }
                Lits[0]++;
                Lits[1]++;
                if ( !sat_solver_addclause( pSat, Lits, Lits + 2 ) )
                {
                    sat_solver_delete( pSat );
                    return 0;
                }
            }
            else
            {
                Lits[0] = toLitCond( pCnf->pVarNums[pObj->Id], 0 );
                Lits[1] = toLitCond( pCnf->pVarNums[pRepr->Id], 1 );
                if ( !sat_solver_addclause( pSat, Lits, Lits + 2 ) )
                {
                    sat_solver_delete( pSat );
                    return 0;
                }
                Lits[0]++;
                Lits[1]--;
                if ( !sat_solver_addclause( pSat, Lits, Lits + 2 ) )
                {
                    sat_solver_delete( pSat );
                    return 0;
                }
            }
        }

        // add clauses for the next timeframe
        { 
            int nLitsAll = 2 * pCnf->nVars;
            int * pLits = pCnf->pClauses[0];
            for ( i = 0; i < pCnf->nLiterals; i++ )
                pLits[i] += nLitsAll;
        }
    }
PRT( "Preparation", clock() - clk );


    // check in the second timeframe
clk = clock();
    Counter = 0;
    nClasses = 0;
    Aig_ManForEachObj( pHaig, pObj, i )
    {
        pRepr = pObj->pHaig;
        if ( pRepr == NULL )
            continue;
        nClasses++;
        if ( pRepr->fPhase ^ pObj->fPhase )
        {
            Lits[0] = toLitCond( pCnf->pVarNums[pObj->Id], 0 );
            Lits[1] = toLitCond( pCnf->pVarNums[pRepr->Id], 0 );

            RetValue = sat_solver_solve( pSat, Lits, Lits + 2, (sint64)nBTLimit, (sint64)0, (sint64)0, (sint64)0 );
            if ( RetValue != l_False )
                Counter++;

            Lits[0]++;
            Lits[1]++;

            RetValue = sat_solver_solve( pSat, Lits, Lits + 2, (sint64)nBTLimit, (sint64)0, (sint64)0, (sint64)0 );
            if ( RetValue != l_False )
                Counter++;
        }
        else
        {
            Lits[0] = toLitCond( pCnf->pVarNums[pObj->Id], 0 );
            Lits[1] = toLitCond( pCnf->pVarNums[pRepr->Id], 1 );

            RetValue = sat_solver_solve( pSat, Lits, Lits + 2, (sint64)nBTLimit, (sint64)0, (sint64)0, (sint64)0 );
            if ( RetValue != l_False )
                Counter++;

            Lits[0]++;
            Lits[1]--;

            RetValue = sat_solver_solve( pSat, Lits, Lits + 2, (sint64)nBTLimit, (sint64)0, (sint64)0, (sint64)0 );
            if ( RetValue != l_False )
                Counter++;
        }
    }
PRT( "Solving    ", clock() - clk );
    if ( Counter )
        printf( "Verification failed for %d out of %d classes.\n", Counter, nClasses );
    else
        printf( "Verification is successful for all %d classes.\n", nClasses );

    Cnf_DataFree( pCnf );
    sat_solver_delete( pSat );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManHaigRecord( Aig_Man_t * p )
{
    extern void Saig_ManRetimeSteps( Aig_Man_t * p, int nSteps, int fForward );
    int fUseRetiming = (int)( Aig_ManRegNum(p) > 0 );
    Dar_RwrPar_t ParsRwr, * pParsRwr = &ParsRwr;
    Aig_Man_t * pNew, * pTemp;
    Aig_Obj_t * pObj;
    int i;
    Dar_ManDefaultRwrParams( pParsRwr );
    // duplicate this manager
    pNew = Aig_ManDupSimple( p );

    // create its history AIG
    pNew->pManHaig = Aig_ManDupSimple( pNew );
    Aig_ManForEachObj( pNew, pObj, i )
        pObj->pHaig = pObj->pData;
    // remove structural hashing table
    Aig_TableClear( pNew->pManHaig );

    // perform retiming
    if ( fUseRetiming )
    {
/*
        // perform balancing
        pNew = Dar_ManBalance( pTemp = pNew, 0 );
        assert( pNew->pManHaig != NULL );
        assert( pTemp->pManHaig == NULL );
        Aig_ManStop( pTemp );

        // perform rewriting
        Dar_ManRewrite( pNew, pParsRwr );
        pNew = Aig_ManDupDfs( pTemp = pNew ); 
        assert( pNew->pManHaig != NULL );
        assert( pTemp->pManHaig == NULL );
        Aig_ManStop( pTemp );
*/
        // perform retiming
        Saig_ManRetimeSteps( pNew, 1000, 1 ); 
        pNew = Aig_ManDupSimpleDfs( pTemp = pNew ); 
        assert( pNew->pManHaig != NULL );
        assert( pTemp->pManHaig == NULL );
        Aig_ManStop( pTemp );

        // perform balancing
        pNew = Dar_ManBalance( pTemp = pNew, 0 );
        assert( pNew->pManHaig != NULL );
        assert( pTemp->pManHaig == NULL );
        Aig_ManStop( pTemp );

        // perform rewriting
        Dar_ManRewrite( pNew, pParsRwr );
        pNew = Aig_ManDupDfs( pTemp = pNew ); 
        assert( pNew->pManHaig != NULL );
        assert( pTemp->pManHaig == NULL );
        Aig_ManStop( pTemp );
    }
    else
    {
        // perform balancing
        pNew = Dar_ManBalance( pTemp = pNew, 0 );
        assert( pNew->pManHaig != NULL );
        assert( pTemp->pManHaig == NULL );
        Aig_ManStop( pTemp );
/*
        // perform rewriting
        Dar_ManRewrite( pNew, pParsRwr );
        pNew = Aig_ManDupDfs( pTemp = pNew ); 
        assert( pNew->pManHaig != NULL );
        assert( pTemp->pManHaig == NULL );
        Aig_ManStop( pTemp );
*/
    } 

    // use the haig for verification
    Aig_ManAntiCleanup( pNew->pManHaig );
    Aig_ManSetRegNum( pNew->pManHaig, pNew->pManHaig->nRegs );
//Aig_ManShow( pNew->pManHaig, 0, NULL ); 

    printf( "AIG:    " );
    Aig_ManPrintStats( pNew );
    printf( "HAIG:   " );
    Aig_ManPrintStats( pNew->pManHaig );

    if ( !Aig_ManHaigVerify( pNew, pNew->pManHaig, 1+fUseRetiming ) )
        printf( "Constructing SAT solver has failed.\n" );         

    // cleanup
    Aig_ManStop( pNew->pManHaig );
    pNew->pManHaig = NULL;
    Aig_ManStop( pNew );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


