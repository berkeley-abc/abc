/**CFile****************************************************************

  FileName    [saigLoc.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [K-step induction for one property only.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: saigLoc.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "saig.h"
#include "cnf.h"
#include "satSolver.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs localization by unrolling timeframes backward.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_ManInduction( Aig_Man_t * p, int nFramesMax, int nConfMax, int fVerbose )
{
    sat_solver * pSat;
    Aig_Man_t * pAigPart;
    Cnf_Dat_t * pCnfPart;
    Vec_Int_t * vTopVarNums;
    Vec_Ptr_t * vTop, * vBot;
    Aig_Obj_t * pObjPi, * pObjPiCopy, * pObjPo;
    int i, f, clk, Lits[2], status, RetValue, nSatVarNum, nConfPrev;
    assert( Saig_ManPoNum(p) == 1 );
    Aig_ManSetPioNumbers( p );

    // start the top by including the PO
    vBot = Vec_PtrAlloc( 100 );
    vTop = Vec_PtrAlloc( 100 );
    Vec_PtrPush( vTop, Aig_ManPo(p, 0) );
    // start the array of CNF variables
    vTopVarNums = Vec_IntAlloc( 100 );
    // start the solver
    pSat = sat_solver_new();
    sat_solver_setnvars( pSat, 1000 );

    // iterate backward unrolling
    RetValue = -1;
    nSatVarNum = 0;
    if ( fVerbose )
        printf( "Localization parameters: FramesMax = %5d. ConflictMax = %6d.\n", nFramesMax, nConfMax );
    for ( f = 0; ; f++ )
    { 
        if ( f > 0 )
        {
            Aig_ManStop( pAigPart );
            Cnf_DataFree( pCnfPart );
        }
        clk = clock();
        // get the bottom
        Aig_SupportNodes( p, (Aig_Obj_t **)Vec_PtrArray(vTop), Vec_PtrSize(vTop), vBot );
        // derive AIG for the part between top and bottom
        pAigPart = Aig_ManDupSimpleDfsPart( p, vBot, vTop );
        // convert it into CNF
        pCnfPart = Cnf_Derive( pAigPart, Aig_ManPoNum(pAigPart) );
        Cnf_DataLift( pCnfPart, nSatVarNum );
        nSatVarNum += pCnfPart->nVars;

        // stitch variables of top and bot
        assert( Aig_ManPoNum(pAigPart)-1 == Vec_IntSize(vTopVarNums) );
        Aig_ManForEachPo( pAigPart, pObjPo, i )
        {
            if ( i == 0 )
            {
                // do not perform inductive strengthening
//                if ( f > 0 )
//                    continue;
                // add topmost literal
                Lits[0] = toLitCond( pCnfPart->pVarNums[pObjPo->Id], f>0 );
                if ( !sat_solver_addclause( pSat, Lits, Lits+1 ) )
                    assert( 0 );
                continue;
            }
            Lits[0] = toLitCond( Vec_IntEntry(vTopVarNums, i-1), 0 );
            Lits[1] = toLitCond( pCnfPart->pVarNums[pObjPo->Id], 1 );
            if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
                assert( 0 );
            Lits[0] = toLitCond( Vec_IntEntry(vTopVarNums, i-1), 1 );
            Lits[1] = toLitCond( pCnfPart->pVarNums[pObjPo->Id], 0 );
            if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
                assert( 0 );
        }
        // add CNF to the SAT solver
        for ( i = 0; i < pCnfPart->nClauses; i++ )
            if ( !sat_solver_addclause( pSat, pCnfPart->pClauses[i], pCnfPart->pClauses[i+1] ) )
                break;
        if ( i < pCnfPart->nClauses )
        {
//            printf( "SAT solver became UNSAT after adding clauses.\n" );
            RetValue = 1;
            break;
        }
        // run the SAT solver
        nConfPrev = pSat->stats.conflicts;
        status = sat_solver_solve( pSat, NULL, NULL, (ABC_INT64_T)nConfMax, 0, 0, 0 );
        if ( fVerbose )
        {
            printf( "%3d : PI = %5d. PO = %5d. AIG = %5d. Var = %6d. Conf = %6d. ",
                f+1, Aig_ManPiNum(pAigPart), Aig_ManPoNum(pAigPart), Aig_ManNodeNum(pAigPart), 
                nSatVarNum, pSat->stats.conflicts-nConfPrev );
            ABC_PRT( "Time", clock() - clk );
        }
        if ( status == l_Undef )
            break;
        if ( status == l_False )
        {
            RetValue = 1;
            break;
        }
        assert( status == l_True );
        if ( f == nFramesMax - 1 )
            break;
        // the problem is SAT - add more clauses
        // create new set of POs to derive new top
        Vec_PtrClear( vTop );
        Vec_PtrPush( vTop, Aig_ManPo(p, 0) );
        Vec_IntClear( vTopVarNums );
        Vec_PtrForEachEntry( vBot, pObjPi, i )
        {
            assert( Aig_ObjIsPi(pObjPi) );
            if ( Saig_ObjIsLo(p, pObjPi) )
            {
                pObjPiCopy = pObjPi->pData;
                assert( pObjPiCopy != NULL );
                Vec_PtrPush( vTop, Saig_ObjLoToLi(p, pObjPi) );
                Vec_IntPush( vTopVarNums, pCnfPart->pVarNums[pObjPiCopy->Id] );
            }
        }
    }
//    printf( "Completed %d interations.\n", f+1 );
    // cleanup
    sat_solver_delete( pSat );
    Aig_ManStop( pAigPart );
    Cnf_DataFree( pCnfPart );
    Vec_IntFree( vTopVarNums );
    Vec_PtrFree( vTop );
    Vec_PtrFree( vBot );
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


