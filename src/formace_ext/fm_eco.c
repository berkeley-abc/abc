/**CFile****************************************************************

  FileName    [fm_eco.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ForMACE ECO with proof interpolation.]

  Synopsis    [ECO command and Craig-interpolant patch construction.]

***********************************************************************/

#include "fm_eco.h"
#include "base/main/mainInt.h"
#include "base/acb/acb.h"
#include "misc/extra/extra.h"
#include "aig/aig/aig.h"
#include "aig/gia/giaAig.h"
#include "proof/int/int.h"
#include "sat/bsat/satStore.h"

ABC_NAMESPACE_IMPL_START

/**Function*************************************************************

  Synopsis    [Creates a constant GIA with a stable support interface.]

***********************************************************************/
static Gia_Man_t * Fm_EcoCreateConstGia( int nInputs, int fValue )
{
    Gia_Man_t * pGia = Gia_ManStart( nInputs + 2 );
    int i;
    for ( i = 0; i < nInputs; i++ )
        Gia_ManAppendCi( pGia );
    Gia_ManAppendCo( pGia, fValue );
    return pGia;
}

/**Function*************************************************************

  Synopsis    [Checks one target cofactor of the ECO mismatch formula.]

***********************************************************************/
static int Fm_EcoTargetPartUnsat( Cnf_Dat_t * pCnf, int iTar,
                                  int nTargets, int TargetValue )
{
    sat_solver * pSat = sat_solver_new();
    int i, Lit, Status = l_Undef;
    if ( pSat == NULL )
        return 0;
    sat_solver_setnvars( pSat, pCnf->nVars );
    for ( i = 0; i < pCnf->nClauses; i++ )
        if ( !sat_solver_addclause(pSat, pCnf->pClauses[i], pCnf->pClauses[i+1]) )
        {
            Status = l_False;
            goto finish;
        }
    Lit = Abc_Var2Lit( 1, 0 );
    if ( !sat_solver_addclause(pSat, &Lit, &Lit + 1) )
    {
        Status = l_False;
        goto finish;
    }
    Lit = Abc_Var2Lit( pCnf->nVars - nTargets + iTar, !TargetValue );
    if ( !sat_solver_addclause(pSat, &Lit, &Lit + 1) )
    {
        Status = l_False;
        goto finish;
    }
    Status = sat_solver_solve( pSat, NULL, NULL, 0, 0, 0, 0 );

finish:
    sat_solver_delete( pSat );
    return Status == l_False;
}

/**Function*************************************************************

  Synopsis    [Derives an ECO target function by Craig interpolation.]

  Description [The A partition is a mismatch with the target fixed to 0.
  The B partition is an independent mismatch copy with the target fixed to 1.
  Selected divisor equalities are added to B, making the first-copy divisor
  variables the complete shared vocabulary.  The resulting interpolant is a
  replacement function over precisely the supplied support interface.]

***********************************************************************/
Gia_Man_t * Fm_EcoDeriveInterpolant( Cnf_Dat_t * pCnf, int iTar,
                                     int nTargets, Vec_Int_t * vUsed,
                                     int fVerbose )
{
    extern Gia_Man_t * Abc_GiaSynthesizeInter( Gia_Man_t * p );
    sat_solver * pSat = NULL;
    Inta_Man_t * pManInter = NULL;
    Sto_Man_t * pSatCnf = NULL;
    Aig_Man_t * pAig = NULL;
    Gia_Man_t * pGia = NULL, * pTemp;
    Vec_Int_t * vClause = NULL, * vVarsAB = NULL;
    int nVars, iCoVarBeg = 1, iCiVarBeg;
    int Lits[2], i, k, Lit, iDiv, Status;

    if ( pCnf == NULL || vUsed == NULL || iTar < 0 || iTar >= nTargets )
        return NULL;
    nVars = pCnf->nVars;
    iCiVarBeg = nVars - nTargets;

    if ( Fm_EcoTargetPartUnsat(pCnf, iTar, nTargets, 0) )
    {
        printf( "ForMACE fm_eco selected constant-0 interpolant.\n" );
        return Fm_EcoCreateConstGia( Vec_IntSize(vUsed), 0 );
    }
    if ( Fm_EcoTargetPartUnsat(pCnf, iTar, nTargets, 1) )
    {
        printf( "ForMACE fm_eco selected constant-1 interpolant.\n" );
        return Fm_EcoCreateConstGia( Vec_IntSize(vUsed), 1 );
    }

    pSat = sat_solver_new();
    if ( pSat == NULL )
        goto finish;
    sat_solver_store_alloc( pSat );
    sat_solver_setnvars( pSat, 2 * nVars );
    vClause = Vec_IntAlloc( 16 );
    vVarsAB = Vec_IntAlloc( Vec_IntSize(vUsed) );

    /* A: first mismatch copy, with target fixed to 0. */
    for ( i = 0; i < pCnf->nClauses; i++ )
        if ( !sat_solver_addclause(pSat, pCnf->pClauses[i], pCnf->pClauses[i+1]) )
            goto finish;
    Lit = Abc_Var2Lit( iCoVarBeg, 0 );
    if ( !sat_solver_addclause(pSat, &Lit, &Lit + 1) )
        goto finish;
    Lit = Abc_Var2Lit( iCiVarBeg + iTar, 1 );
    if ( !sat_solver_addclause(pSat, &Lit, &Lit + 1) )
        goto finish;
    sat_solver_store_mark_clauses_a( pSat );

    /* B: independent mismatch copy, with target fixed to 1. */
    for ( i = 0; i < pCnf->nClauses; i++ )
    {
        Vec_IntClear( vClause );
        for ( k = 0; pCnf->pClauses[i] + k < pCnf->pClauses[i+1]; k++ )
        {
            Lit = pCnf->pClauses[i][k];
            Vec_IntPush( vClause,
                Abc_Var2Lit(Abc_Lit2Var(Lit) + nVars, Abc_LitIsCompl(Lit)) );
        }
        if ( !sat_solver_addclause(pSat, Vec_IntArray(vClause), Vec_IntLimit(vClause)) )
            goto finish;
    }
    Lit = Abc_Var2Lit( iCoVarBeg + nVars, 0 );
    if ( !sat_solver_addclause(pSat, &Lit, &Lit + 1) )
        goto finish;
    Lit = Abc_Var2Lit( iCiVarBeg + nVars + iTar, 0 );
    if ( !sat_solver_addclause(pSat, &Lit, &Lit + 1) )
        goto finish;

    /* Selected divisor equality clauses live in B. */
    Vec_IntForEachEntry( vUsed, iDiv, i )
    {
        int iVar0 = iCoVarBeg + 1 + iDiv;
        int iVar1 = iVar0 + nVars;
        Vec_IntPush( vVarsAB, iVar0 );
        Lits[0] = Abc_Var2Lit( iVar0, 0 );
        Lits[1] = Abc_Var2Lit( iVar1, 1 );
        if ( !sat_solver_addclause(pSat, Lits, Lits + 2) )
            goto finish;
        Lits[0] = Abc_Var2Lit( iVar0, 1 );
        Lits[1] = Abc_Var2Lit( iVar1, 0 );
        if ( !sat_solver_addclause(pSat, Lits, Lits + 2) )
            goto finish;
    }

    sat_solver_store_mark_roots( pSat );
    Status = sat_solver_solve( pSat, NULL, NULL, 0, 0, 0, 0 );
    if ( Status != l_False )
    {
        printf( "ForMACE fm_eco interpolation formula is not UNSAT.\n" );
        goto finish;
    }
    pSatCnf = (Sto_Man_t *)sat_solver_store_release( pSat );
    if ( pSatCnf == NULL )
        goto finish;
    pManInter = Inta_ManAlloc();
    pAig = (Aig_Man_t *)Inta_ManInterpolate( pManInter, pSatCnf, 0,
                                             vVarsAB, fVerbose );
    if ( pAig == NULL )
        goto finish;
    pGia = Gia_ManFromAigSimple( pAig );
    if ( pGia == NULL || Gia_ManCiNum(pGia) != Vec_IntSize(vUsed) )
    {
        Gia_ManStopP( &pGia );
        goto finish;
    }
    pGia = Abc_GiaSynthesizeInter( pTemp = pGia );
    Gia_ManStop( pTemp );
    if ( pGia == NULL || Gia_ManCiNum(pGia) != Vec_IntSize(vUsed) )
    {
        Gia_ManStopP( &pGia );
        goto finish;
    }
    printf( "ForMACE fm_eco interpolant: inputs = %d  ands = %d.\n",
        Gia_ManCiNum(pGia), Gia_ManAndNum(pGia) );

finish:
    if ( pSat )
        sat_solver_delete( pSat );
    if ( pManInter )
        Inta_ManFree( pManInter );
    if ( pSatCnf )
        Sto_ManFree( pSatCnf );
    if ( pAig )
        Aig_ManStop( pAig );
    Vec_IntFreeP( &vClause );
    Vec_IntFreeP( &vVarsAB );
    return pGia;
}

/**Function*************************************************************

  Synopsis    [Runs DAC'18 ECO with an interpolant function builder.]

***********************************************************************/
int Fm_CommandEco( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char * pFileNames[4] = { NULL, NULL, NULL, NULL };
    int c, i, nTimeout = 0;
    int fCheck = 0, fRandom = 0, fInputs = 0, fUnitW = 0;
    int fMinUnsat = 0, fAssumpOnly = 0, fVerbose = 0, fVeryVerbose = 0;

    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "T:o:acrimuvwh")) != EOF )
    {
        switch ( c )
        {
        case 'T':
            nTimeout = atoi( globalUtilOptarg );
            if ( nTimeout < 0 )
                goto usage;
            break;
        case 'o': pFileNames[3] = (char *)globalUtilOptarg; break;
        case 'a': fAssumpOnly ^= 1; break;
        case 'c': fCheck ^= 1; break;
        case 'r': fRandom ^= 1; break;
        case 'i': fInputs ^= 1; break;
        case 'm': fMinUnsat ^= 1; break;
        case 'u': fUnitW ^= 1; break;
        case 'v': fVerbose ^= 1; break;
        case 'w': fVeryVerbose ^= 1; break;
        case 'h': goto usage;
        default: goto usage;
        }
    }
    if ( fMinUnsat && fAssumpOnly )
    {
        fprintf( pAbc->Err,
            "fm_eco: -a and -m select different support algorithms and cannot be combined.\n" );
        goto usage;
    }
    if ( argc - globalUtilOptind < 2 || argc - globalUtilOptind > 3 )
        goto usage;
    for ( i = 0; i < argc - globalUtilOptind; i++ )
    {
        FILE * pFile = fopen( argv[globalUtilOptind + i], "rb" );
        if ( pFile == NULL )
        {
            fprintf( pAbc->Err, "fm_eco: cannot open input file \"%s\".\n",
                     argv[globalUtilOptind + i] );
            return 1;
        }
        fclose( pFile );
        pFileNames[i] = argv[globalUtilOptind + i];
    }
    fprintf( pAbc->Out, "ForMACE fm_eco: support=%s function=ITP unit_weights=%s\n",
             fMinUnsat ? "minimum" : (fAssumpOnly ? "assumption-only" : "original"),
             fUnitW ? "yes" : "no" );
    return Acb_NtkRunEco( pFileNames, nTimeout, fCheck, fRandom, fInputs,
                          fUnitW, fMinUnsat, 0, !fAssumpOnly, 1,
                          fVerbose, fVeryVerbose ) ? 0 : 1;

usage:
    fprintf( pAbc->Err,
        "usage: fm_eco [-T seconds] [-o out.v] [-acrimuvwh] <implementation> <specification> [weights]\n" );
    fprintf( pAbc->Err, "\t-a       : use assumption minimization only; skip Acb_FindSupport\n" );
    fprintf( pAbc->Err, "\t-c       : check target-set feasibility before patch construction\n" );
    fprintf( pAbc->Err, "\t-r       : randomly permute targets\n" );
    fprintf( pAbc->Err, "\t-i       : use primary inputs as candidate patch inputs\n" );
    fprintf( pAbc->Err, "\t-u       : replace positive candidate weights by unit weights\n" );
    fprintf( pAbc->Err, "\t-m       : use exact MinUNSAT support instead of original ABC support\n" );
    fprintf( pAbc->Err, "\t-T num   : total target-loop timeout in seconds [default = unlimited]\n" );
    fprintf( pAbc->Err, "\t-o file  : integrated patched output [default = out.v]\n" );
    fprintf( pAbc->Err, "\t-v       : print ECO construction details\n" );
    fprintf( pAbc->Err, "\t-w       : print proof details and audit small -m support instances\n" );
    fprintf( pAbc->Err, "\t-h       : print this usage\n" );
    return 1;
}

ABC_NAMESPACE_IMPL_END
