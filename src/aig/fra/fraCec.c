/**CFile****************************************************************

  FileName    [fraCec.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New FRAIG package.]

  Synopsis    [CEC engined based on fraiging.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 30, 2007.]

  Revision    [$Id: fraCec.c,v 1.00 2007/06/30 00:00:00 alanmi Exp $]

***********************************************************************/

#include "fra.h"
#include "cnf.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_FraigSat( Aig_Man_t * pMan, sint64 nConfLimit, sint64 nInsLimit, int fVerbose )
{
    sat_solver * pSat;
    Cnf_Dat_t * pCnf;
    int status, RetValue, clk = clock();
    Vec_Int_t * vCiIds;

    assert( Aig_ManPoNum(pMan) == 1 );
    pMan->pData = NULL;

    // derive CNF
    pCnf = Cnf_Derive( pMan, 0 );
//    pCnf = Cnf_DeriveSimple( pMan, 0 );
    // convert into the SAT solver
    pSat = Cnf_DataWriteIntoSolver( pCnf, 1, 0 );
    vCiIds = Cnf_DataCollectPiSatNums( pCnf, pMan );
    Cnf_DataFree( pCnf );
    // solve SAT
    if ( pSat == NULL )
    {
        Vec_IntFree( vCiIds );
//        printf( "Trivially unsat\n" );
        return 1;
    }


//    printf( "Created SAT problem with %d variable and %d clauses. ", sat_solver_nvars(pSat), sat_solver_nclauses(pSat) );
//    PRT( "Time", clock() - clk );

    // simplify the problem
    clk = clock();
    status = sat_solver_simplify(pSat);
//    printf( "Simplified the problem to %d variables and %d clauses. ", sat_solver_nvars(pSat), sat_solver_nclauses(pSat) );
//    PRT( "Time", clock() - clk );
    if ( status == 0 )
    {
        Vec_IntFree( vCiIds );
        sat_solver_delete( pSat );
//        printf( "The problem is UNSATISFIABLE after simplification.\n" );
        return 1;
    }

    // solve the miter
    clk = clock();
    if ( fVerbose )
        pSat->verbosity = 1;
    status = sat_solver_solve( pSat, NULL, NULL, (sint64)nConfLimit, (sint64)nInsLimit, (sint64)0, (sint64)0 );
    if ( status == l_Undef )
    {
//        printf( "The problem timed out.\n" );
        RetValue = -1;
    }
    else if ( status == l_True )
    {
//        printf( "The problem is SATISFIABLE.\n" );
        RetValue = 0;
    }
    else if ( status == l_False )
    {
//        printf( "The problem is UNSATISFIABLE.\n" );
        RetValue = 1;
    }
    else
        assert( 0 );
//    PRT( "SAT sat_solver time", clock() - clk );
//    printf( "The number of conflicts = %d.\n", (int)pSat->sat_solver_stats.conflicts );
 
    // if the problem is SAT, get the counterexample
    if ( status == l_True )
    {
        pMan->pData = Sat_SolverGetModel( pSat, vCiIds->pArray, vCiIds->nSize );
    }
    // free the sat_solver
    if ( fVerbose )
        Sat_SolverPrintStats( stdout, pSat );
//sat_solver_store_write( pSat, "trace.cnf" );
//sat_solver_store_free( pSat );
    sat_solver_delete( pSat );
    Vec_IntFree( vCiIds );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_FraigCec( Aig_Man_t ** ppAig, int fVerbose )
{
    int nBTLimitStart =     300;  // starting SAT run
    int nBTLimitFirst =       2;  // first fraiging iteration
    int nBTLimitLast  = 1000000;  // the last-gasp SAT run

    Fra_Par_t Params, * pParams = &Params;
    Aig_Man_t * pAig = *ppAig, * pTemp;
    int i, RetValue, clk;

    // report the original miter
    if ( fVerbose )
    {
        printf( "Original miter:   Nodes = %6d.\n", Aig_ManNodeNum(pAig) );
    }
    RetValue = Fra_FraigMiterStatus( pAig );
//    assert( RetValue == -1 );
    if ( RetValue >= 0 )
        return RetValue;

    // if SAT only, solve without iteration
clk = clock();
    RetValue = Fra_FraigSat( pAig, (sint64)2*nBTLimitStart, (sint64)0, 0 );
    if ( fVerbose )
    {
        printf( "Initial SAT:      Nodes = %6d.  ", Aig_ManNodeNum(pAig) );
PRT( "Time", clock() - clk );
    }
    if ( RetValue >= 0 )
        return RetValue;

    // duplicate the AIG
clk = clock();
//    pAig = Aig_ManDupDfs( pTemp = pAig );
    pAig = Dar_ManRwsat( pTemp = pAig, 0, 0 );
    Aig_ManStop( pTemp );
    if ( fVerbose )
    {
        printf( "Rewriting:        Nodes = %6d.  ", Aig_ManNodeNum(pAig) );
PRT( "Time", clock() - clk );
    }

    // perform the loop
    Fra_ParamsDefault( pParams );
    pParams->nBTLimitNode = nBTLimitFirst;
    pParams->nBTLimitMiter = nBTLimitStart;
    pParams->fDontShowBar = 1;
    pParams->fProve = 1;
    for ( i = 0; i < 6; i++ )
    {
//printf( "Running fraiging with %d BTnode and %d BTmiter.\n", pParams->nBTLimitNode, pParams->nBTLimitMiter );
        // run fraiging
clk = clock();
        pAig = Fra_FraigPerform( pTemp = pAig, pParams );
        Aig_ManStop( pTemp );
        if ( fVerbose )
        {
            printf( "Fraiging (i=%d):   Nodes = %6d.  ", i+1, Aig_ManNodeNum(pAig) );
PRT( "Time", clock() - clk );
        }

        // check the miter status
        RetValue = Fra_FraigMiterStatus( pAig );
        if ( RetValue >= 0 )
            break;

        // perform rewriting
clk = clock();
        pAig = Dar_ManRewriteDefault( pTemp = pAig );
        Aig_ManStop( pTemp );
        if ( fVerbose )
        {
            printf( "Rewriting:        Nodes = %6d.  ", Aig_ManNodeNum(pAig) );
PRT( "Time", clock() - clk );
        } 

        // check the miter status
        RetValue = Fra_FraigMiterStatus( pAig );
        if ( RetValue >= 0 )
            break;
        // try simulation

        // set the parameters for the next run
        pParams->nBTLimitNode = 8 * pParams->nBTLimitNode;
        pParams->nBTLimitMiter = 2 * pParams->nBTLimitMiter;
    }

    // if still unsolved try last gasp
    if ( RetValue == -1 )
    {
clk = clock();
        RetValue = Fra_FraigSat( pAig, (sint64)nBTLimitLast, (sint64)0, 0 );
        if ( fVerbose )
        {
            printf( "Final SAT:            Nodes = %6d.  ", Aig_ManNodeNum(pAig) );
PRT( "Time", clock() - clk );
        }
    }

    *ppAig = pAig;
    return RetValue;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_FraigCecPartitioned( Aig_Man_t * pMan1, Aig_Man_t * pMan2, int nPartSize, int fVerbose )
{
    Aig_Man_t * pAig;
    Vec_Ptr_t * vParts;
    int i, RetValue = 1, nOutputs;
    // create partitions
    vParts = Aig_ManMiterPartitioned( pMan1, pMan2, nPartSize );
    // solve the partitions
    nOutputs = -1;
    Vec_PtrForEachEntry( vParts, pAig, i )
    {
        nOutputs++;
        if ( fVerbose )
            printf( "Verifying part %4d  (out of %4d)  PI = %5d. PO = %5d. And = %6d. Lev = %4d.\r", 
                i+1, Vec_PtrSize(vParts), Aig_ManPiNum(pAig), Aig_ManPoNum(pAig), 
                Aig_ManNodeNum(pAig), Aig_ManLevelNum(pAig) );
        RetValue = Fra_FraigMiterStatus( pAig );
        if ( RetValue == 1 )
            continue;
        if ( RetValue == 0 )
            break;
        RetValue = Fra_FraigCec( &pAig, 0 );
        Vec_PtrWriteEntry( vParts, i, pAig );
        if ( RetValue == 1 )
            continue;
        if ( RetValue == 0 )
            break;
        break;
    }
    // clear the result
    if ( fVerbose )
    {
        printf( "                                                                                          \r" );
        fflush( stdout );
    }
    // report the timeout
    if ( RetValue == -1 )
    {
        printf( "Timed out after verifying %d partitions (out of %d).\n", nOutputs, Vec_PtrSize(vParts) );
        fflush( stdout );
    }
    // free intermediate results
    Vec_PtrForEachEntry( vParts, pAig, i )
        Aig_ManStop( pAig );
    Vec_PtrFree( vParts );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_FraigCecTop( Aig_Man_t * pMan1, Aig_Man_t * pMan2, int nConfLimit, int fPartition, int fVerbose )
{
    //Abc_NtkDarCec( pNtk1, pNtk2, fPartition, fVerbose );
    int RetValue, clkTotal = clock();

    if ( Aig_ManPiNum(pMan1) != Aig_ManPiNum(pMan1) )
    {
        printf( "Abc_CommandAbc8Cec(): Miters have different number of PIs.\n" );
        return 0;
    }
    if ( Aig_ManPoNum(pMan1) != Aig_ManPoNum(pMan1) )
    {
        printf( "Abc_CommandAbc8Cec(): Miters have different number of POs.\n" );
        return 0;
    }
    assert( Aig_ManPiNum(pMan1) == Aig_ManPiNum(pMan1) );
    assert( Aig_ManPoNum(pMan1) == Aig_ManPoNum(pMan1) );

    if ( fPartition )
        RetValue = Fra_FraigCecPartitioned( pMan1, pMan2, 100, fVerbose );
    else
        RetValue = Fra_FraigCecPartitioned( pMan1, pMan2, Aig_ManPoNum(pMan1), fVerbose );

    // report the miter
    if ( RetValue == 1 )
    {
        printf( "Networks are equivalent.   " );
PRT( "Time", clock() - clkTotal );
    }
    else if ( RetValue == 0 )
    {
        printf( "Networks are NOT EQUIVALENT.   " );
PRT( "Time", clock() - clkTotal );
    }
    else
    {
        printf( "Networks are UNDECIDED.   " );
PRT( "Time", clock() - clkTotal );
    }
    fflush( stdout );
    return RetValue;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


