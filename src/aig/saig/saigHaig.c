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
#include "sat/bsat/satSolver.h"
#include "sat/cnf/cnf.h"

ABC_NAMESPACE_IMPL_START


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
    Aig_Obj_t * pObjNew, * pObjNew2, * pObjRepr, * pObjReprNew;//, * pMiter;
    Aig_Obj_t * pPo;
    // skip nodes without representative
    pObjRepr = pObj->pHaig;
    if ( pObjRepr == NULL )
        return;
//    assert( pObjRepr->Id < pObj->Id );
    // get the new node 
    pObjNew = (Aig_Obj_t *)pObj->pData;
    // get the new node of the representative
    pObjReprNew = (Aig_Obj_t *)pObjRepr->pData;
    // if this is the same node, no need to add constraints
    assert( pObjNew != NULL && pObjReprNew != NULL );
    if ( Aig_Regular(pObjNew) == Aig_Regular(pObjReprNew) )
        return;
    // these are different nodes - perform speculative reduction
    pObjNew2 = Aig_NotCond( pObjReprNew, pObj->fPhase ^ pObjRepr->fPhase );
    // set the new node
    pObj->pData = pObjNew2;
    // add the constraint
    if ( pObj->fMarkA )
        return;
//    pMiter = Aig_Exor( pFrames, pObjNew, pObjReprNew );
//    pMiter = Aig_NotCond( pMiter, !Aig_ObjPhaseReal(pMiter) );
//    assert( Aig_ObjPhaseReal(pMiter) == 1 );
//    Aig_ObjCreateCo( pFrames, pMiter );
    if ( Aig_ObjPhaseReal(pObjNew) != Aig_ObjPhaseReal(pObjReprNew) )
        pObjReprNew = Aig_Not(pObjReprNew);
    pPo = Aig_ObjCreateCo( pFrames, pObjNew );
    Aig_ObjCreateCo( pFrames, pObjReprNew );

    // remember the node corresponding to this PO
    pPo->pData = pObj;
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
    pFrames->pName = Abc_UtilStrsav( pHaig->pName );
    pFrames->pSpec = Abc_UtilStrsav( pHaig->pSpec );
    // map the constant node
    Aig_ManConst1(pHaig)->pData = Aig_ManConst1( pFrames );
    // create variables for register outputs
    Saig_ManForEachLo( pHaig, pObj, i )
        pObj->pData = Aig_ObjCreateCi( pFrames );
    // add timeframes
    Aig_ManSetCioIds( pHaig );
    for ( f = 0; f < nFrames; f++ )
    {
        // create primary inputs
        Saig_ManForEachPi( pHaig, pObj, i )
            pObj->pData = Aig_ObjCreateCi( pFrames );
        // create internal nodes
        Aig_ManForEachNode( pHaig, pObj, i )
        {        
            pObj->pData = Aig_And( pFrames, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
            Aig_ManHaigSpeculate( pFrames, pObj );
        }
        if ( f == nFrames - 2 )
            nAssumptions = Aig_ManCoNum(pFrames);
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
    pFrames->nAsserts = Aig_ManCoNum(pFrames) - nAssumptions;
    Aig_ManSetRegNum( pFrames, 0 );
    return pFrames;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ManMapHaigNodes( Aig_Man_t * pHaig )
{
    Aig_Obj_t * pObj1, * pObj2;
    int Id1, Id2, i, Counter = 0;
    Aig_ManForEachObj( pHaig, pObj1, i )
        pObj1->pHaig = NULL;
    Vec_IntForEachEntry( pHaig->vEquPairs, Id1, i )
    {
        Id2 = Vec_IntEntry( pHaig->vEquPairs, ++i );
        pObj1 = Aig_ManObj( pHaig, Id1 );
        pObj2 = Aig_ManObj( pHaig, Id2 );
        assert( pObj1 != pObj2 );
        assert( !Aig_ObjIsCi(pObj1) || !Aig_ObjIsCi(pObj2) );
        if ( Aig_ObjIsCi(pObj1) )
        {
            Counter += (int)(pObj2->pHaig != NULL);
            pObj2->pHaig = pObj1;
        }
        else if ( Aig_ObjIsCi(pObj2) )
        {
            Counter += (int)(pObj1->pHaig != NULL);
            pObj1->pHaig = pObj2;
        }
        else if ( pObj1->Id < pObj2->Id )
        {
            Counter += (int)(pObj2->pHaig != NULL);
            pObj2->pHaig = pObj1;
        }
        else 
        {
            Counter += (int)(pObj1->pHaig != NULL);
            pObj1->pHaig = pObj2;
        }
    }
//    printf( "Overwrites %d out of %d.\n", Counter, Vec_IntSize(pHaig->vEquPairs)/2 );
    return Counter;
}
 
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ManHaigVerify( Aig_Man_t * p, Aig_Man_t * pAig, Aig_Man_t * pHaig, int nFrames, clock_t clkSynth )
{
    int nBTLimit = 0;
    Aig_Man_t * pFrames, * pTemp;
    Cnf_Dat_t * pCnf;
    sat_solver * pSat;
    Aig_Obj_t * pObj1, * pObj2;
    int i, RetValue1, RetValue2, Counter, Lits[2], nOvers;
    clock_t clk = clock(), clkVerif;

    nOvers = Aig_ManMapHaigNodes( pHaig );

    // create time frames with speculative reduction and convert them into CNF
clk = clock();
    pFrames = Aig_ManHaigFrames( pHaig, nFrames );
    Aig_ManCleanMarkA( pHaig );

    printf( "Frames:     " );
    Aig_ManPrintStats( pFrames );

    pFrames = Dar_ManRwsat( pTemp = pFrames, 1, 0 );
    Aig_ManStop( pTemp );

    printf( "Frames synt:" );
    Aig_ManPrintStats( pFrames );

    printf( "Additional frames stats: Assumptions = %d. Assertions = %d. Pairs = %d. Over = %d.\n", 
        Aig_ManCoNum(pFrames)/2 - pFrames->nAsserts/2, pFrames->nAsserts/2, Vec_IntSize(pHaig->vEquPairs)/2, nOvers );
//    pCnf = Cnf_DeriveSimple( pFrames, Aig_ManCoNum(pFrames) );
    pCnf = Cnf_Derive( pFrames, Aig_ManCoNum(pFrames) );



//    pCnf = Cnf_Derive( pFrames, Aig_ManCoNum(pFrames) - pFrames->nAsserts );
//Cnf_DataWriteIntoFile( pCnf, "temp.cnf", 1 );
//    Saig_ManDumpBlif( pHaig, "haig_temp.blif" );
//    Saig_ManDumpBlif( pFrames, "haig_temp_frames.blif" );
    // create the SAT solver to be used for this problem
    pSat = (sat_solver *)Cnf_DataWriteIntoSolver( pCnf, 1, 0 );
    if ( pSat == NULL )
    {
        printf( "Aig_ManHaigVerify(): Computed CNF is not valid.\n" );
        return 0;
    }

    if ( nFrames == 2 )
    {
        // add clauses for the first frame
        Aig_ManForEachCo( pFrames, pObj1, i )
        {
            if ( i >= Aig_ManCoNum(pFrames) - pFrames->nAsserts )
                break;

            pObj2 = Aig_ManCo( pFrames, ++i );
            assert( pObj1->fPhase == pObj2->fPhase );

            Lits[0] = toLitCond( pCnf->pVarNums[pObj1->Id], 0 );
            Lits[1] = toLitCond( pCnf->pVarNums[pObj2->Id], 1 );
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

        if ( !sat_solver_simplify(pSat) )
        {
            sat_solver_delete( pSat );
            return 0;
        }
    }
ABC_PRT( "Preparation", clock() - clk );


    // check in the second timeframe
clk = clock();
    Counter = 0;
    printf( "Started solving ...\r" );
    Aig_ManForEachCo( pFrames, pObj1, i )
    {
        if ( i < Aig_ManCoNum(pFrames) - pFrames->nAsserts )
            continue;

        pObj2 = Aig_ManCo( pFrames, ++i );
        assert( pObj1->fPhase == pObj2->fPhase );

        Lits[0] = toLitCond( pCnf->pVarNums[pObj1->Id], 0 );
        Lits[1] = toLitCond( pCnf->pVarNums[pObj2->Id], 1 );

        RetValue1 = sat_solver_solve( pSat, Lits, Lits + 2, (ABC_INT64_T)nBTLimit, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
        if ( RetValue1 == l_False )
        {
            Lits[0] = lit_neg( Lits[0] );
            Lits[1] = lit_neg( Lits[1] );
//            RetValue = sat_solver_addclause( pSat, Lits, Lits + 2 );
//            assert( RetValue );
        }

        Lits[0]++;
        Lits[1]--;

        RetValue2 = sat_solver_solve( pSat, Lits, Lits + 2, (ABC_INT64_T)nBTLimit, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
        if ( RetValue2 == l_False )
        {
            Lits[0] = lit_neg( Lits[0] );
            Lits[1] = lit_neg( Lits[1] );
//            RetValue = sat_solver_addclause( pSat, Lits, Lits + 2 );
//            assert( RetValue );
        }

        if ( RetValue1 != l_False || RetValue2 != l_False )
            Counter++;

        if ( i % 50 == 1 )
            printf( "Solving assertion %6d out of %6d.\r", 
                (i - (Aig_ManCoNum(pFrames) - pFrames->nAsserts))/2, 
                pFrames->nAsserts/2 );
//        if ( nClasses == 1000 )
//            break;
    }
    printf( "                                                          \r" );
ABC_PRT( "Solving    ", clock() - clk );
clkVerif = clock() - clk;
    if ( Counter )
        printf( "Verification failed for %d out of %d assertions.\n", Counter, pFrames->nAsserts/2 );
    else
        printf( "Verification is successful for all %d assertions.\n", pFrames->nAsserts/2 );

    // print the statistic into a file
    {
        FILE * pTable;
        Aig_Man_t * pTemp, * pHaig2;

        pHaig2 = pAig->pManHaig; 
        pAig->pManHaig = NULL;
        pTemp = Aig_ManDupDfs( pAig );
        pAig->pManHaig = pHaig2;

        Aig_ManSeqCleanup( pTemp );

        pTable = fopen( "stats.txt", "a+" );
        fprintf( pTable, "%s ",  p->pName );
        fprintf( pTable, "%d ", Saig_ManPiNum(p) );
        fprintf( pTable, "%d ", Saig_ManPoNum(p) );

        fprintf( pTable, "%d ", Saig_ManRegNum(p) );
        fprintf( pTable, "%d ", Aig_ManNodeNum(p) );
        fprintf( pTable, "%d ", Aig_ManLevelNum(p) );

        fprintf( pTable, "%d ", Saig_ManRegNum(pTemp) );
        fprintf( pTable, "%d ", Aig_ManNodeNum(pTemp) );
        fprintf( pTable, "%d ", Aig_ManLevelNum(pTemp) );

        fprintf( pTable, "%d ", Saig_ManRegNum(pHaig) );
        fprintf( pTable, "%d ", Aig_ManNodeNum(pHaig) );
        fprintf( pTable, "%d ", Aig_ManLevelNum(pHaig) );

        fprintf( pTable, "%.2f", (float)(clkSynth)/(float)(CLOCKS_PER_SEC) );
        fprintf( pTable, "\n" );
        fclose( pTable );


        pTable = fopen( "stats2.txt", "a+" );
        fprintf( pTable, "%s ",  p->pName );
        fprintf( pTable, "%d ", Aig_ManNodeNum(pFrames) );
        fprintf( pTable, "%d ", Aig_ManLevelNum(pFrames) );

        fprintf( pTable, "%d ", pCnf->nVars );
        fprintf( pTable, "%d ", pCnf->nClauses );
        fprintf( pTable, "%d ", pCnf->nLiterals );

        fprintf( pTable, "%d ", Aig_ManCoNum(pFrames)/2 - pFrames->nAsserts/2 );
        fprintf( pTable, "%d ", pFrames->nAsserts/2 );
        fprintf( pTable, "%d ", Vec_IntSize(pHaig->vEquPairs)/2 );

        fprintf( pTable, "%.2f", (float)(clkVerif)/(float)(CLOCKS_PER_SEC) );
        fprintf( pTable, "\n" );
        fclose( pTable );

        Aig_ManStop( pTemp );
    }

    // clean up
    Aig_ManStop( pFrames );
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
int Aig_ManHaigVerify2( Aig_Man_t * p, Aig_Man_t * pAig, Aig_Man_t * pHaig, int nFrames )
{
    int nBTLimit = 0;
    Cnf_Dat_t * pCnf;
    sat_solver * pSat;
    Aig_Obj_t * pObj1, * pObj2;
    int i, RetValue1, RetValue2, Counter, Lits[2];
    clock_t clk = clock();
    int Delta;
    int Id1, Id2;

    assert( nFrames == 1 || nFrames == 2 );

clk = clock();
    pCnf = Cnf_DeriveSimple( pHaig, Aig_ManCoNum(pHaig) );
//    Aig_ManForEachObj( pHaig, pObj, i )
//        printf( "%d=%d  ", pObj->Id, pCnf->pVarNums[pObj->Id] );
//    printf( "\n" );

    // create the SAT solver to be used for this problem
    pSat = (sat_solver *)Cnf_DataWriteIntoSolver( pCnf, nFrames, 0 );
//Sat_SolverWriteDimacs( pSat, "1.cnf", NULL, NULL, 0 );
    if ( pSat == NULL )
    {
        printf( "Aig_ManHaigVerify(): Computed CNF is not valid.\n" );
        return -1;
    }

    if ( nFrames == 2 )
    {
        Vec_IntForEachEntry( pHaig->vEquPairs, Id1, i )
        {
            Id2 = Vec_IntEntry( pHaig->vEquPairs, ++i );
            pObj1 = Aig_ManObj( pHaig, Id1 );
            pObj2 = Aig_ManObj( pHaig, Id2 );
            if ( pObj1->fPhase ^ pObj2->fPhase )
            {
                Lits[0] = toLitCond( pCnf->pVarNums[pObj1->Id], 0 );
                Lits[1] = toLitCond( pCnf->pVarNums[pObj2->Id], 0 );
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
                Lits[0] = toLitCond( pCnf->pVarNums[pObj1->Id], 0 );
                Lits[1] = toLitCond( pCnf->pVarNums[pObj2->Id], 1 );
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

        if ( !sat_solver_simplify(pSat) )
        {
            sat_solver_delete( pSat );
            return 0;
        }
    }
ABC_PRT( "Preparation", clock() - clk );


    // check in the second timeframe
clk = clock();
    Counter = 0;
    Delta = (nFrames == 2)? pCnf->nVars : 0;
    Vec_IntForEachEntry( pHaig->vEquPairs, Id1, i )
    {
        Id2 = Vec_IntEntry( pHaig->vEquPairs, ++i );
        pObj1 = Aig_ManObj( pHaig, Id1 );
        pObj2 = Aig_ManObj( pHaig, Id2 );
        if ( pObj1->fPhase ^ pObj2->fPhase )
        {
            Lits[0] = toLitCond( pCnf->pVarNums[pObj1->Id]+Delta, 0 );
            Lits[1] = toLitCond( pCnf->pVarNums[pObj2->Id]+Delta, 0 );

            RetValue1 = sat_solver_solve( pSat, Lits, Lits + 2, (ABC_INT64_T)nBTLimit, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );

            Lits[0]++;
            Lits[1]++;

            RetValue2 = sat_solver_solve( pSat, Lits, Lits + 2, (ABC_INT64_T)nBTLimit, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );

            if ( RetValue1 != l_False || RetValue2 != l_False )
                Counter++;
        }
        else
        {
            Lits[0] = toLitCond( pCnf->pVarNums[pObj1->Id]+Delta, 0 );
            Lits[1] = toLitCond( pCnf->pVarNums[pObj2->Id]+Delta, 1 );

            RetValue1 = sat_solver_solve( pSat, Lits, Lits + 2, (ABC_INT64_T)nBTLimit, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );

            Lits[0]++;
            Lits[1]--;

            RetValue2 = sat_solver_solve( pSat, Lits, Lits + 2, (ABC_INT64_T)nBTLimit, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );

            if ( RetValue1 != l_False || RetValue2 != l_False )
                Counter++;
        }
        if ( i % 50 == 1 )
            printf( "Solving assertion %6d out of %6d.\r", i/2, Vec_IntSize(pHaig->vEquPairs)/2 );

//        if ( i / 2 > 1000 )
//            break;
    }
ABC_PRT( "Solving    ", clock() - clk );
    if ( Counter )
        printf( "Verification failed for %d out of %d classes.\n", Counter, Vec_IntSize(pHaig->vEquPairs)/2 );
    else
        printf( "Verification is successful for all %d classes.\n", Vec_IntSize(pHaig->vEquPairs)/2 );

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
Aig_Man_t * Saig_ManHaigDump( Aig_Man_t * pHaig )
{
    Vec_Ptr_t * vTemp;
    Aig_Obj_t * pObj, * pObj1, * pObj2, * pMiter;
    int Id1, Id2, i;
    // remove regular POs
    Aig_ManSetCioIds( pHaig );
    vTemp = Vec_PtrAlloc( Saig_ManRegNum(pHaig) );
    Aig_ManForEachCo( pHaig, pObj, i )
    {
        if ( Saig_ObjIsPo(pHaig, pObj) )
        {
            Aig_ObjDisconnect( pHaig, pObj );
            Vec_PtrWriteEntry( pHaig->vObjs, pObj->Id, NULL );
        }
        else
        {
            Vec_PtrPush( vTemp, pObj );
        }
    }
    Vec_PtrShrink( pHaig->vCos, 0 ); 
    pHaig->nObjs[AIG_OBJ_CO] = Vec_PtrSize( vTemp );
    // add new POs
    Vec_IntForEachEntry( pHaig->vEquPairs, Id1, i )
    {
        Id2 = Vec_IntEntry( pHaig->vEquPairs, ++i );
        pObj1 = Aig_ManObj( pHaig, Id1 );
        pObj2 = Aig_ManObj( pHaig, Id2 );
        assert( pObj1 != pObj2 );
        assert( !Aig_ObjIsCi(pObj1) || !Aig_ObjIsCi(pObj2) );
        pMiter = Aig_Exor( pHaig, pObj1, pObj2 );
        pMiter = Aig_NotCond( pMiter, Aig_ObjPhaseReal(pMiter) );
        assert( Aig_ObjPhaseReal(pMiter) == 0 );
        Aig_ObjCreateCo( pHaig, pMiter );
    }
    printf( "Added %d property outputs.\n", Vec_IntSize(pHaig->vEquPairs)/2 );
    // add the registers
    Vec_PtrForEachEntry( Aig_Obj_t *, vTemp, pObj, i )
        Vec_PtrPush( pHaig->vCos, pObj );
    Vec_PtrFree( vTemp );
    assert( pHaig->nObjs[AIG_OBJ_CO] ==  Vec_PtrSize(pHaig->vCos) ); 
    Aig_ManCleanup( pHaig );
    Aig_ManSetRegNum( pHaig, pHaig->nRegs );
//    return pHaig;

    printf( "HAIG:       " );
    Aig_ManPrintStats( pHaig );
    printf( "HAIG is written into file \"haig.blif\".\n" );
    Saig_ManDumpBlif( pHaig, "haig.blif" );

    Vec_IntFree( pHaig->vEquPairs );
    Aig_ManStop( pHaig );
    return NULL;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_ManHaigRecord( Aig_Man_t * p, int nIters, int nSteps, int fRetimingOnly, int fAddBugs, int fUseCnf, int fVerbose )
{
    int fSeqHaig = (int)( Aig_ManRegNum(p) > 0 );
    Dar_RwrPar_t ParsRwr, * pParsRwr = &ParsRwr;
    Aig_Man_t * pNew, * pTemp;
    Aig_Obj_t * pObj;
    int i, k, nStepsReal;
    clock_t clk = clock(), clkSynth;
    Dar_ManDefaultRwrParams( pParsRwr );

clk = clock();
    // duplicate this manager
    pNew = Aig_ManDupSimple( p );
    // create its history AIG
    pNew->pManHaig = Aig_ManDupSimple( pNew );
    Aig_ManForEachObj( pNew, pObj, i )
        pObj->pHaig = (Aig_Obj_t *)pObj->pData;
    // remove structural hashing table
    Aig_TableClear( pNew->pManHaig );
    pNew->pManHaig->vEquPairs = Vec_IntAlloc( 10000 );
ABC_PRT( "HAIG setup time", clock() - clk );

clk = clock();
    if ( fSeqHaig )
    {
        if ( fRetimingOnly )
        {
            // perform retiming
            nStepsReal = Saig_ManRetimeSteps( pNew, nSteps, 1, fAddBugs ); 
            pNew = Aig_ManDupSimpleDfs( pTemp = pNew ); 
            Aig_ManStop( pTemp );
            printf( "Performed %d retiming moves.\n", nStepsReal );
        }
        else
        {
            for ( k = 0; k < nIters; k++ )
            {
                // perform balancing
                pNew = Dar_ManBalance( pTemp = pNew, 0 );
                Aig_ManStop( pTemp );

                // perform rewriting
                Dar_ManRewrite( pNew, pParsRwr );
                pNew = Aig_ManDupDfs( pTemp = pNew ); 
                Aig_ManStop( pTemp );

                // perform retiming
                nStepsReal = Saig_ManRetimeSteps( pNew, nSteps, 1, fAddBugs ); 
                pNew = Aig_ManDupSimpleDfs( pTemp = pNew ); 
                Aig_ManStop( pTemp );
                printf( "Performed %d retiming moves.\n", nStepsReal );
            }
        }
    }
    else
    {
        for ( k = 0; k < nIters; k++ )
        {
            // perform balancing
            pNew = Dar_ManBalance( pTemp = pNew, 0 );
            Aig_ManStop( pTemp );

            // perform rewriting
            Dar_ManRewrite( pNew, pParsRwr );
            pNew = Aig_ManDupDfs( pTemp = pNew ); 
            Aig_ManStop( pTemp );
        }
    } 
ABC_PRT( "Synthesis time ", clock() - clk );
clkSynth = clock() - clk;

    // use the haig for verification
//    Aig_ManAntiCleanup( pNew->pManHaig );
    Aig_ManSetRegNum( pNew->pManHaig, pNew->pManHaig->nRegs );
//Aig_ManShow( pNew->pManHaig, 0, NULL ); 

    printf( "AIG before: " );
    Aig_ManPrintStats( p );
    printf( "AIG after:  " );
    Aig_ManPrintStats( pNew );
    printf( "HAIG:       " );
    Aig_ManPrintStats( pNew->pManHaig );

    if ( fUseCnf )
    {
        if ( !Aig_ManHaigVerify2( p, pNew, pNew->pManHaig, 1+fSeqHaig ) )
            printf( "Constructing SAT solver has failed.\n" );         
    }
    else
    {
        if ( !Aig_ManHaigVerify( p, pNew, pNew->pManHaig, 1+fSeqHaig, clkSynth ) )
            printf( "Constructing SAT solver has failed.\n" );         
    }

    Saig_ManHaigDump( pNew->pManHaig );
    pNew->pManHaig = NULL;
    return pNew;
/*
    // cleanup
    Vec_IntFree( pNew->pManHaig->vEquPairs );
    Aig_ManStop( pNew->pManHaig );
    pNew->pManHaig = NULL;
    return pNew;
*/
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

