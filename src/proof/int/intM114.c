/**CFile****************************************************************

  FileName    [intM114.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Interpolation engine.]

  Synopsis    [Intepolation using ABC's proof generator added to MiniSat-1.14c.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 24, 2008.]

  Revision    [$Id: intM114.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "intInt.h"
#include "formace_ext/fm_camus.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
static int         Inter_ManIsSelected( Vec_Int_t * vSelected, int iLatch );
static Aig_Man_t * Inter_ManExpandSelected( Aig_Man_t * pInter, Vec_Int_t * vSelected, int nRegs );
static Aig_Man_t * Inter_ManDeriveConstInter( Inter_Man_t * p, Vec_Int_t * vSelected, int fUseBackward, abctime nTimeNewOut );
static Fm_CamusMan_t * Inter_ManDeriveCamus( Inter_Man_t * p );
static Vec_Int_t * Inter_ManFindMinimumSelected( Inter_Man_t * p, Vec_Int_t * vCandidates, int fUseBackward, abctime nTimeNewOut, int * pStatus );

///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns the SAT solver for one interpolation run.]

  Description [pInter is the previous interpolant. pAig is one time frame.
  pFrames is the unrolled time frames.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
sat_solver * Inter_ManDeriveSatSolver( 
    Aig_Man_t * pInter, Cnf_Dat_t * pCnfInter, 
    Aig_Man_t * pAig, Cnf_Dat_t * pCnfAig, 
    Aig_Man_t * pFrames, Cnf_Dat_t * pCnfFrames, 
    Vec_Int_t * vVarsAB, Vec_Int_t * vSelected, int fUseBackward, int fAddB )
{
    sat_solver * pSat;
    Aig_Obj_t * pObj, * pObj2;
    int i, Lits[2];

//Aig_ManDumpBlif( pInter,  "out_inter.blif", NULL, NULL );
//Aig_ManDumpBlif( pAig,    "out_aig.blif", NULL, NULL );
//Aig_ManDumpBlif( pFrames, "out_frames.blif", NULL, NULL );

    // sanity checks
    assert( Aig_ManRegNum(pInter) == 0 );
    assert( Aig_ManRegNum(pAig) > 0 );
    assert( Aig_ManRegNum(pFrames) == 0 );
    assert( Aig_ManCoNum(pInter) == 1 );
    assert( Aig_ManCoNum(pFrames) == fUseBackward? Saig_ManRegNum(pAig) : 1 );
    assert( fUseBackward || Aig_ManCiNum(pInter) == Aig_ManRegNum(pAig) );
//    assert( (Aig_ManCiNum(pFrames) - Aig_ManRegNum(pAig)) % Saig_ManPiNum(pAig) == 0 );

    // prepare CNFs
    Cnf_DataLift( pCnfAig,   pCnfFrames->nVars );
    Cnf_DataLift( pCnfInter, pCnfFrames->nVars + pCnfAig->nVars );

    // start the solver
    pSat = sat_solver_new();
    sat_solver_store_alloc( pSat );
    sat_solver_setnvars( pSat, pCnfInter->nVars + pCnfAig->nVars + pCnfFrames->nVars );

    // add clauses of A
    // interpolant
    for ( i = 0; i < pCnfInter->nClauses; i++ )
    {
        if ( !sat_solver_addclause( pSat, pCnfInter->pClauses[i], pCnfInter->pClauses[i+1] ) )
        {
            sat_solver_delete( pSat );
            // return clauses to the original state
            Cnf_DataLift( pCnfAig, -pCnfFrames->nVars );
            Cnf_DataLift( pCnfInter, -pCnfFrames->nVars -pCnfAig->nVars );
            return NULL;
        }
    }
    // connector clauses
    if ( fUseBackward )
    {
        Saig_ManForEachLi( pAig, pObj2, i )
        {
            if ( Saig_ManRegNum(pAig) == Aig_ManCiNum(pInter) )
                pObj = Aig_ManCi( pInter, i );
            else
            {
                assert( Aig_ManCiNum(pAig) == Aig_ManCiNum(pInter) );
                pObj = Aig_ManCi( pInter, Aig_ManCiNum(pAig)-Saig_ManRegNum(pAig) + i );
            }

            Lits[0] = toLitCond( pCnfInter->pVarNums[pObj->Id], 0 );
            Lits[1] = toLitCond( pCnfAig->pVarNums[pObj2->Id], 1 );
            if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
                assert( 0 );
            Lits[0] = toLitCond( pCnfInter->pVarNums[pObj->Id], 1 );
            Lits[1] = toLitCond( pCnfAig->pVarNums[pObj2->Id], 0 );
            if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
                assert( 0 );
        }
    }
    else
    {
        Aig_ManForEachCi( pInter, pObj, i )
        {
            pObj2 = Saig_ManLo( pAig, i );

            Lits[0] = toLitCond( pCnfInter->pVarNums[pObj->Id], 0 );
            Lits[1] = toLitCond( pCnfAig->pVarNums[pObj2->Id], 1 );
            if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
                assert( 0 );
            Lits[0] = toLitCond( pCnfInter->pVarNums[pObj->Id], 1 );
            Lits[1] = toLitCond( pCnfAig->pVarNums[pObj2->Id], 0 );
            if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
                assert( 0 );
        }
    }
    // one timeframe
    for ( i = 0; i < pCnfAig->nClauses; i++ )
    {
        if ( !sat_solver_addclause( pSat, pCnfAig->pClauses[i], pCnfAig->pClauses[i+1] ) )
            assert( 0 );
    }
    // connector clauses
    Vec_IntClear( vVarsAB );
    if ( fUseBackward )
    {
        Aig_ManForEachCo( pFrames, pObj, i )
        {
            assert( pCnfFrames->pVarNums[pObj->Id] >= 0 );
            Vec_IntPush( vVarsAB, pCnfFrames->pVarNums[pObj->Id] );

            pObj2 = Saig_ManLo( pAig, i );
            Lits[0] = toLitCond( pCnfFrames->pVarNums[pObj->Id], 0 );
            Lits[1] = toLitCond( pCnfAig->pVarNums[pObj2->Id], 1 );
            if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
                assert( 0 );
            Lits[0] = toLitCond( pCnfFrames->pVarNums[pObj->Id], 1 );
            Lits[1] = toLitCond( pCnfAig->pVarNums[pObj2->Id], 0 );
            if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
                assert( 0 );
        }
    }
    else
    {
        Aig_ManForEachCi( pFrames, pObj, i )
        {
            if ( i == Aig_ManRegNum(pAig) )
                break;
            if ( !Inter_ManIsSelected(vSelected, i) )
                continue;
            Vec_IntPush( vVarsAB, pCnfFrames->pVarNums[pObj->Id] );

            pObj2 = Saig_ManLi( pAig, i );
            Lits[0] = toLitCond( pCnfFrames->pVarNums[pObj->Id], 0 );
            Lits[1] = toLitCond( pCnfAig->pVarNums[pObj2->Id], 1 );
            if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
                assert( 0 );
            Lits[0] = toLitCond( pCnfFrames->pVarNums[pObj->Id], 1 );
            Lits[1] = toLitCond( pCnfAig->pVarNums[pObj2->Id], 0 );
            if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
                assert( 0 );
        }
    }
    // add clauses of B
    sat_solver_store_mark_clauses_a( pSat );
    for ( i = 0; fAddB && i < pCnfFrames->nClauses; i++ )
    {
        if ( !sat_solver_addclause( pSat, pCnfFrames->pClauses[i], pCnfFrames->pClauses[i+1] ) )
        {
            pSat->fSolved = 1;
            break;
        }
    }
    sat_solver_store_mark_roots( pSat );
    // return clauses to the original state
    Cnf_DataLift( pCnfAig, -pCnfFrames->nVars );
    Cnf_DataLift( pCnfInter, -pCnfFrames->nVars -pCnfAig->nVars );
    return pSat;
}

/**Function*************************************************************

  Synopsis    [Performs one SAT run with interpolation.]

  Description [Returns 1 if proven. 0 if failed. -1 if undecided.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Inter_ManPerformOneStepSelected( Inter_Man_t * p, int fUseBias, int fUseBackward, abctime nTimeNewOut, Vec_Int_t * vSelected )
{
    sat_solver * pSat;
    void * pSatCnf = NULL;
    Inta_Man_t * pManInterA; 
//    Intb_Man_t * pManInterB; 
    int * pGlobalVars;
    int status, RetValue;
    int i, Var;
    abctime clk;
//    assert( p->pInterNew == NULL );

    // derive the SAT solver
    pSat = Inter_ManDeriveSatSolver( p->pInter, p->pCnfInter, p->pAigTrans, p->pCnfAig, p->pFrames, p->pCnfFrames, p->vVarsAB, vSelected, fUseBackward, 1 );
    if ( pSat == NULL )
    {
        p->pInterNew = NULL;
        return 1;
    }

    // set runtime limit
    if ( nTimeNewOut )
        sat_solver_set_runtime_limit( pSat, nTimeNewOut );

    // collect global variables
    pGlobalVars = ABC_CALLOC( int, sat_solver_nvars(pSat) );
    Vec_IntForEachEntry( p->vVarsAB, Var, i )
        pGlobalVars[Var] = 1;
    pSat->pGlobalVars = fUseBias? pGlobalVars : NULL;

    // solve the problem
clk = Abc_Clock();
    status = sat_solver_solve( pSat, NULL, NULL, (ABC_INT64_T)p->nConfLimit, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
    p->nConfCur = pSat->stats.conflicts;
p->timeSat += Abc_Clock() - clk;

    pSat->pGlobalVars = NULL;
    ABC_FREE( pGlobalVars );
    if ( status == l_False )
    {
        if ( vSelected && Vec_IntSize(vSelected) == 0 )
        {
            sat_solver_delete( pSat );
            p->pInterNew = Inter_ManDeriveConstInter( p, vSelected, fUseBackward, nTimeNewOut );
            return p->pInterNew ? 1 : -1;
        }
        pSatCnf = sat_solver_store_release( pSat );
        RetValue = 1;
    }
    else if ( status == l_True )
    {
        RetValue = 0;
    } 
    else
    {
        RetValue = -1;
    }
    sat_solver_delete( pSat );
    if ( pSatCnf == NULL )
        return RetValue;

    // create the resulting manager
clk = Abc_Clock();
/*
    if ( !fUseIp )
    {
        pManInterA = Inta_ManAlloc();
        p->pInterNew = Inta_ManInterpolate( pManInterA, pSatCnf, p->vVarsAB, 0 );
        Inta_ManFree( pManInterA );
    }
    else
    {
        Aig_Man_t * pInterNew2;
        int RetValue;

        pManInterA = Inta_ManAlloc();
        p->pInterNew = Inta_ManInterpolate( pManInterA, pSatCnf, p->vVarsAB, 0 );
//        Inter_ManVerifyInterpolant1( pManInterA, pSatCnf, p->pInterNew );
        Inta_ManFree( pManInterA );

        pManInterB = Intb_ManAlloc();
        pInterNew2 = Intb_ManInterpolate( pManInterB, pSatCnf, p->vVarsAB, 0 );
        Inter_ManVerifyInterpolant2( pManInterB, pSatCnf, pInterNew2 );
        Intb_ManFree( pManInterB );

        // check relationship
        RetValue = Inter_ManCheckEquivalence( pInterNew2, p->pInterNew );
        if ( RetValue )
            printf( "Equivalence \"Ip == Im\" holds\n" );
        else
        {
//            printf( "Equivalence \"Ip == Im\" does not hold\n" );
            RetValue = Inter_ManCheckContainment( pInterNew2, p->pInterNew );
            if ( RetValue )
                printf( "Containment \"Ip -> Im\" holds\n" );
            else
                printf( "Containment \"Ip -> Im\" does not hold\n" );

            RetValue = Inter_ManCheckContainment( p->pInterNew, pInterNew2 );
            if ( RetValue )
                printf( "Containment \"Im -> Ip\" holds\n" );
            else
                printf( "Containment \"Im -> Ip\" does not hold\n" );
        }

        Aig_ManStop( pInterNew2 );
    }
*/

    pManInterA = Inta_ManAlloc();
    p->pInterNew = (Aig_Man_t *)Inta_ManInterpolate( pManInterA, (Sto_Man_t *)pSatCnf, nTimeNewOut, p->vVarsAB, 0 );
    Inta_ManFree( pManInterA );

p->timeInt += Abc_Clock() - clk;
    Sto_ManFree( (Sto_Man_t *)pSatCnf );
    if ( p->pInterNew && vSelected )
    {
        Aig_Man_t * pInterNew = Inter_ManExpandSelected( p->pInterNew, vSelected, Aig_ManRegNum(p->pAig) );
        Aig_ManStop( p->pInterNew );
        p->pInterNew = pInterNew;
    }
    if ( p->pInterNew == NULL )
        RetValue = -1;
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Checks whether a latch connector is selected.]

***********************************************************************/
static int Inter_ManIsSelected( Vec_Int_t * vSelected, int iLatch )
{
    return vSelected == NULL || Vec_IntFind( vSelected, iLatch ) >= 0;
}

/**Function*************************************************************

  Synopsis    [Expands a compact interpolant to the full latch interface.]

***********************************************************************/
static Aig_Man_t * Inter_ManExpandSelected( Aig_Man_t * pInter, Vec_Int_t * vSelected, int nRegs )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pObjNew = NULL;
    int i, iCompact = 0;

    assert( Vec_IntSize(vSelected) == Aig_ManCiNum(pInter) );
    pNew = Aig_ManStart( Aig_ManObjNumMax(pInter) + nRegs );
    pNew->pName = Abc_UtilStrsav( pInter->pName );
    pNew->pSpec = Abc_UtilStrsav( pInter->pSpec );
    Aig_ManCleanData( pInter );
    Aig_ManConst1(pInter)->pData = Aig_ManConst1(pNew);
    for ( i = 0; i < nRegs; i++ )
    {
        pObjNew = Aig_ObjCreateCi( pNew );
        if ( iCompact < Vec_IntSize(vSelected) && Vec_IntEntry(vSelected, iCompact) == i )
            Aig_ManCi(pInter, iCompact++)->pData = pObjNew;
    }
    assert( iCompact == Aig_ManCiNum(pInter) );
    Aig_ManForEachObj( pInter, pObj, i )
        if ( Aig_ObjIsBuf(pObj) )
            pObj->pData = Aig_ObjChild0Copy( pObj );
        else if ( Aig_ObjIsNode(pObj) )
            pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    Aig_ManForEachCo( pInter, pObj, i )
        Aig_ObjCreateCo( pNew, Aig_ObjChild0Copy(pObj) );
    assert( Aig_ManCheck(pNew) );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Derives a constant interpolant when no latch is shared.]

***********************************************************************/
static Aig_Man_t * Inter_ManDeriveConstInter( Inter_Man_t * p, Vec_Int_t * vSelected, int fUseBackward, abctime nTimeNewOut )
{
    Aig_Man_t * pInter, * pInterFull;
    sat_solver * pSat;
    int Status, fOne;

    pSat = Inter_ManDeriveSatSolver( p->pInter, p->pCnfInter, p->pAigTrans, p->pCnfAig, p->pFrames, p->pCnfFrames, p->vVarsAB, vSelected, fUseBackward, 0 );
    if ( pSat == NULL )
        fOne = 0;
    else
    {
        if ( nTimeNewOut )
            sat_solver_set_runtime_limit( pSat, nTimeNewOut );
        Status = sat_solver_solve( pSat, NULL, NULL, (ABC_INT64_T)p->nConfLimit, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
        p->nConfCur = pSat->stats.conflicts;
        sat_solver_delete( pSat );
        if ( Status == l_Undef )
            return NULL;
        fOne = (Status == l_True);
    }
    pInter = Aig_ManStart( 1 );
    Aig_ObjCreateCo( pInter, fOne ? Aig_ManConst1(pInter) : Aig_ManConst0(pInter) );
    pInterFull = Inter_ManExpandSelected( pInter, vSelected, Aig_ManRegNum(p->pAig) );
    Aig_ManStop( pInter );
    return pInterFull;
}

/**Function*************************************************************

  Synopsis    [Builds the fixed background and guarded forward latch groups.]

***********************************************************************/
static Fm_CamusMan_t * Inter_ManDeriveCamus( Inter_Man_t * p )
{
    Fm_CamusMan_t * pCamus = NULL;
    Aig_Obj_t * pObj, * pObj2;
    int i, Lits[2], fLifted = 0;

    assert( Aig_ManRegNum(p->pInter) == 0 );
    assert( Aig_ManRegNum(p->pAigTrans) > 0 );
    assert( Aig_ManRegNum(p->pFrames) == 0 );
    Cnf_DataLift( p->pCnfAig, p->pCnfFrames->nVars );
    Cnf_DataLift( p->pCnfInter, p->pCnfFrames->nVars + p->pCnfAig->nVars );
    fLifted = 1;
    pCamus = Fm_CamusStart( p->pCnfInter->nVars + p->pCnfAig->nVars + p->pCnfFrames->nVars, Aig_ManRegNum(p->pAigTrans) );
    if ( pCamus == NULL )
        goto finish;
    for ( i = 0; i < p->pCnfInter->nClauses; i++ )
        if ( !Fm_CamusAddBackground(pCamus, p->pCnfInter->pClauses[i], p->pCnfInter->pClauses[i+1] - p->pCnfInter->pClauses[i]) )
            goto fail;
    Aig_ManForEachCi( p->pInter, pObj, i )
    {
        pObj2 = Saig_ManLo( p->pAigTrans, i );
        Lits[0] = toLitCond( p->pCnfInter->pVarNums[pObj->Id], 0 );
        Lits[1] = toLitCond( p->pCnfAig->pVarNums[pObj2->Id], 1 );
        if ( !Fm_CamusAddBackground(pCamus, Lits, 2) )
            goto fail;
        Lits[0] = toLitCond( p->pCnfInter->pVarNums[pObj->Id], 1 );
        Lits[1] = toLitCond( p->pCnfAig->pVarNums[pObj2->Id], 0 );
        if ( !Fm_CamusAddBackground(pCamus, Lits, 2) )
            goto fail;
    }
    for ( i = 0; i < p->pCnfAig->nClauses; i++ )
        if ( !Fm_CamusAddBackground(pCamus, p->pCnfAig->pClauses[i], p->pCnfAig->pClauses[i+1] - p->pCnfAig->pClauses[i]) )
            goto fail;
    Aig_ManForEachCi( p->pFrames, pObj, i )
    {
        if ( i == Aig_ManRegNum(p->pAigTrans) )
            break;
        pObj2 = Saig_ManLi( p->pAigTrans, i );
        Lits[0] = toLitCond( p->pCnfFrames->pVarNums[pObj->Id], 0 );
        Lits[1] = toLitCond( p->pCnfAig->pVarNums[pObj2->Id], 1 );
        if ( !Fm_CamusAddGroup(pCamus, i, Lits, 2) )
            goto fail;
        Lits[0] = toLitCond( p->pCnfFrames->pVarNums[pObj->Id], 1 );
        Lits[1] = toLitCond( p->pCnfAig->pVarNums[pObj2->Id], 0 );
        if ( !Fm_CamusAddGroup(pCamus, i, Lits, 2) )
            goto fail;
    }
    for ( i = 0; i < p->pCnfFrames->nClauses; i++ )
        if ( !Fm_CamusAddBackground(pCamus, p->pCnfFrames->pClauses[i], p->pCnfFrames->pClauses[i+1] - p->pCnfFrames->pClauses[i]) )
            goto fail;
    goto finish;

fail:
    Fm_CamusStop( pCamus );
    pCamus = NULL;
finish:
    if ( fLifted )
    {
        Cnf_DataLift( p->pCnfAig, -p->pCnfFrames->nVars );
        Cnf_DataLift( p->pCnfInter, -p->pCnfFrames->nVars - p->pCnfAig->nVars );
    }
    return pCamus;
}

/**Function*************************************************************

  Synopsis    [Finds a minimum UNSAT latch connector set with CAMUS BnB.]

***********************************************************************/
static Vec_Int_t * Inter_ManFindMinimumSelected( Inter_Man_t * p, Vec_Int_t * vCandidates, int fUseBackward, abctime nTimeNewOut, int * pStatus )
{
    Fm_CamusMan_t * pCamus;
    abctime clkMinimumMus;
    int Status;

    if ( fUseBackward || Vec_IntSize(vCandidates) > p->nForMaceVarLimit )
    {
        *pStatus = -1;
        return NULL;
    }
    pCamus = Inter_ManDeriveCamus( p );
    if ( pCamus == NULL )
    {
        *pStatus = -1;
        return NULL;
    }
    Fm_CamusSetLimits( pCamus, (ABC_INT64_T)p->nConfLimit, nTimeNewOut );
    Status = Fm_CamusSolve( pCamus, vCandidates );
    if ( Status == l_False )
    {
        clkMinimumMus = Abc_Clock();
        Vec_Int_t * vResult = Fm_CamusFindMinimumMus( pCamus, vCandidates );
        clkMinimumMus = Abc_Clock() - clkMinimumMus;
        if ( p->fVerbose )
            printf( "ForMACE Fm_CamusFindMinimumMus time %.6f sec.\n", 1.0 * (double)clkMinimumMus / (double)CLOCKS_PER_SEC );
        Fm_CamusStop( pCamus );
        *pStatus = vResult ? 1 : -1;
        return vResult;
    }
    Fm_CamusStop( pCamus );
    *pStatus = (Status == l_True) ? 0 : -1;
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Collects structural state support of an interpolant.]

***********************************************************************/
static Vec_Int_t * Inter_ManCollectSupport( Aig_Man_t * pInter )
{
    Vec_Int_t * vSupport;
    Aig_Obj_t * pObj;
    int i;

    vSupport = Vec_IntAlloc( Aig_ManCiNum(pInter) );
    Aig_ManForEachCi( pInter, pObj, i )
        if ( Aig_ObjRefs(pObj) )
            Vec_IntPush( vSupport, i );
    return vSupport;
}

/**Function*************************************************************

  Synopsis    [Performs one ForMACE-selected interpolation step.]

***********************************************************************/
int Inter_ManPerformOneStep( Inter_Man_t * p, int fUseBias, int fUseBackward, abctime nTimeNewOut )
{
    Vec_Int_t * vCandidates, * vResult;
    int i, Status, RetValue, nCandidates;

    if ( fUseBackward || (!p->fForMaceMinvar && !p->fForMaceHybrid) )
        return Inter_ManPerformOneStepSelected( p, fUseBias, fUseBackward, nTimeNewOut, NULL );

    if ( p->fForMaceMinvar )
    {
        vCandidates = Vec_IntAlloc( Aig_ManRegNum(p->pAig) );
        for ( i = 0; i < Aig_ManRegNum(p->pAig); i++ )
            Vec_IntPush( vCandidates, i );
        vResult = Inter_ManFindMinimumSelected( p, vCandidates, fUseBackward, nTimeNewOut, &Status );
        Vec_IntFree( vCandidates );
        if ( Status != 1 )
        {
            if ( Status == 0 )
                return Inter_ManPerformOneStepSelected( p, fUseBias, fUseBackward, nTimeNewOut, NULL );
            if ( p->fVerbose )
                printf( "ForMACE minvar CAMUS search could not complete.\n" );
            return -1;
        }
        if ( p->fVerbose )
            printf( "ForMACE minvar CAMUS minimum selected %d of %d latch boundaries.\n", Vec_IntSize(vResult), Aig_ManRegNum(p->pAig) );
        RetValue = Inter_ManPerformOneStepSelected( p, fUseBias, fUseBackward, nTimeNewOut, vResult );
        Vec_IntFree( vResult );
        return RetValue;
    }

    RetValue = Inter_ManPerformOneStepSelected( p, fUseBias, fUseBackward, nTimeNewOut, NULL );
    if ( RetValue != 1 || p->pInterNew == NULL )
        return RetValue;
    vCandidates = Inter_ManCollectSupport( p->pInterNew );
    nCandidates = Vec_IntSize(vCandidates);
    if ( Vec_IntSize(vCandidates) > p->nForMaceVarLimit )
    {
        if ( p->fVerbose )
            printf( "ForMACE hybrid support (%d latches) exceeds -L %d.\n", Vec_IntSize(vCandidates), p->nForMaceVarLimit );
        Vec_IntFree( vCandidates );
        Aig_ManStop( p->pInterNew );
        p->pInterNew = NULL;
        return -1;
    }
    vResult = Inter_ManFindMinimumSelected( p, vCandidates, fUseBackward, nTimeNewOut, &Status );
    Vec_IntFree( vCandidates );
    if ( Status != 1 )
    {
        if ( Status == 0 )
        {
            if ( p->fVerbose )
                printf( "ForMACE hybrid support was insufficient; using the baseline interpolant.\n" );
            return 1;
        }
        if ( p->fVerbose )
            printf( "ForMACE hybrid CAMUS search could not complete.\n" );
        Aig_ManStop( p->pInterNew );
        p->pInterNew = NULL;
        return -1;
    }
    if ( p->fVerbose )
        printf( "ForMACE hybrid CAMUS local minimum selected %d of %d baseline-support latch boundaries.\n", Vec_IntSize(vResult), nCandidates );
    Aig_ManStop( p->pInterNew );
    p->pInterNew = NULL;
    RetValue = Inter_ManPerformOneStepSelected( p, fUseBias, fUseBackward, nTimeNewOut, vResult );
    Vec_IntFree( vResult );
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
