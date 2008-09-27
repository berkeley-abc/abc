/**CFile****************************************************************

  FileName    [saigLoc.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [Localization package.]

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
int Saig_ManLocalization( Aig_Man_t * p, int nFramesMax, int nConfMax, int fVerbose )
{
    sat_solver * pSat;
    Vec_Int_t * vTopVarNums;
    Vec_Ptr_t * vTop, * vBot;
    Cnf_Dat_t * pCnfTop, * pCnfBot;
    Aig_Man_t * pPartTop, * pPartBot;
    Aig_Obj_t * pObj, * pObjBot;
    int i, f, clk, Lits[2], status, RetValue, nSatVarNum, nConfPrev;
    assert( Saig_ManPoNum(p) == 1 );
    Aig_ManSetPioNumbers( p );

    // start the top by including the PO
    vBot = Vec_PtrAlloc( 100 );
    vTop = Vec_PtrAlloc( 100 );
    Vec_PtrPush( vTop, Aig_ManPo(p, 0) );
    // create the manager composed of one PI/PO pair
    pPartTop = Aig_ManStart( 10 );
    Aig_ObjCreatePo( pPartTop, Aig_ObjCreatePi(pPartTop) );
    pCnfTop = Cnf_Derive( pPartTop, 0 );
    // start the array of CNF variables
    vTopVarNums = Vec_IntAlloc( 100 );
    Vec_IntPush( vTopVarNums, pCnfTop->pVarNums[Aig_ManPi(pPartTop,0)->Id] );
    // start the solver
    pSat = Cnf_DataWriteIntoSolver( pCnfTop, 1, 0 );

    // iterate backward unrolling
    RetValue = -1;
    nSatVarNum = pCnfTop->nVars;
    if ( fVerbose )
        printf( "Localization parameters: FramesMax = %5d. ConflictMax = %6d.\n", nFramesMax, nConfMax );
    for ( f = 0; ; f++ )
    { 
        clk = clock();
        // get the bottom
        Aig_SupportNodes( p, (Aig_Obj_t **)Vec_PtrArray(vTop), Vec_PtrSize(vTop), vBot );
        // derive AIG for the part between top and bottom
        pPartBot = Aig_ManDupSimpleDfsPart( p, vBot, vTop );
        // convert it into CNF
        pCnfBot = Cnf_Derive( pPartBot, Aig_ManPoNum(pPartBot) );
        Cnf_DataLift( pCnfBot, nSatVarNum );
        nSatVarNum += pCnfBot->nVars;
        // stitch variables of top and bot
        assert( Aig_ManPoNum(pPartBot) == Vec_IntSize(vTopVarNums) );
        Aig_ManForEachPo( pPartBot, pObjBot, i )
        {
            Lits[0] = toLitCond( Vec_IntEntry(vTopVarNums, i),   0 );
            Lits[1] = toLitCond( pCnfBot->pVarNums[pObjBot->Id], 1 );
            if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
                assert( 0 );
            Lits[0] = toLitCond( Vec_IntEntry(vTopVarNums, i),   1 );
            Lits[1] = toLitCond( pCnfBot->pVarNums[pObjBot->Id], 0 );
            if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
                assert( 0 );
        }
        // add CNF to the SAT solver
        for ( i = 0; i < pCnfBot->nClauses; i++ )
            if ( !sat_solver_addclause( pSat, pCnfBot->pClauses[i], pCnfBot->pClauses[i+1] ) )
                break;
        if ( i < pCnfBot->nClauses )
        {
//            printf( "SAT solver became UNSAT after adding clauses.\n" );
            RetValue = 1;
            break;
        }
        // run the SAT solver
        nConfPrev = pSat->stats.conflicts;
        status = sat_solver_solve( pSat, NULL, NULL, (sint64)nConfMax, 0, 0, 0 );
        if ( fVerbose )
        {
            printf( "%3d : PI = %5d. PO = %5d. AIG = %5d. Var = %6d. Conf = %6d. ",
                f+1, Aig_ManPiNum(pPartBot), Aig_ManPoNum(pPartBot), Aig_ManNodeNum(pPartBot), 
                nSatVarNum, pSat->stats.conflicts-nConfPrev );
            PRT( "Time", clock() - clk );
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
        Vec_IntClear( vTopVarNums );
        Vec_PtrForEachEntry( vBot, pObj, i )
        {
            assert( Aig_ObjIsPi(pObj) );
            if ( Saig_ObjIsLo(p, pObj) )
            {
                pObjBot = pObj->pData;
                assert( pObjBot != NULL );
                Vec_PtrPush( vTop, Saig_ObjLoToLi(p, pObj) );
                Vec_IntPush( vTopVarNums, pCnfBot->pVarNums[pObjBot->Id] );
            }
        }
        // remove old top and replace it by bottom
        Aig_ManStop( pPartTop );
        pPartTop = pPartBot;
        pPartBot = NULL;
        Cnf_DataFree( pCnfTop );
        pCnfTop = pCnfBot;
        pCnfBot = NULL;
    }
//    printf( "Completed %d interations.\n", f+1 );
    // cleanup
    sat_solver_delete( pSat );
    Aig_ManStop( pPartTop );
    Cnf_DataFree( pCnfTop );
    Aig_ManStop( pPartBot );
    Cnf_DataFree( pCnfBot );
    Vec_IntFree( vTopVarNums );
    Vec_PtrFree( vTop );
    Vec_PtrFree( vBot );
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


