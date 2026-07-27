/**CFile****************************************************************

  FileName    [cecCorrCert.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [Kissat certificate for the final &scorr2 fixed point.]

  Author      [Xiran Zhao]

  Affiliation [University of Chinese Academy of Sciences (UCAS)]

  Date        [Ver. 1.0. Started - Jun 2026.]

***********************************************************************/

#include "cecInt.h"
#include "sat/cnf/cnf.h"
#include "sat/kissat/kissatSolver.h"

ABC_NAMESPACE_IMPL_START

extern void Cec_ManSatAddToStore( Vec_Int_t * vCexStore, Vec_Int_t * vCex, int Out );

/**Function*************************************************************

  Synopsis    [Certifies all SRM mismatch outputs in one Kissat call.]

  Description [The generated CNF contains one OR clause over all SRM
  outputs.  UNSAT therefore proves every candidate pair simultaneously.
  On SAT, one full CI assignment and one violated output are returned in
  the same format used by the ordinary correspondence refinement loop.

  Return values are 1 (all outputs UNSAT), 0 (SAT counterexample), and
  -1 (UNKNOWN or an inconsistent model/API result).]

  SideEffects [None on pSrm or the host correspondence classes.]

***********************************************************************/
int Cec_ManCorrKissatCertify( Gia_Man_t * pSrm, Vec_Int_t * vOutputs,
    Vec_Int_t ** pvCexStore, Vec_Str_t ** pvStatus, int * piOut, int fVerbose )
{
    Cnf_Dat_t * pCnf;
    kissat_solver * pSat;
    Vec_Int_t * vCexStore = Vec_IntAlloc( 16 );
    Vec_Str_t * vStatus = Vec_StrAlloc( Gia_ManCoNum(pSrm) );
    Gia_Obj_t * pObj;
    unsigned char * pValues = NULL;
    abctime clk = Abc_Clock();
    int i, iVar, * pBeg, * pEnd, Status = -1, iOut = -1;

    assert( Vec_IntSize(vOutputs) == 2 * Gia_ManCoNum(pSrm) );
    *pvCexStore = NULL;
    *pvStatus = NULL;
    *piOut = -1;
    for ( i = 0; i < Gia_ManCoNum(pSrm); i++ )
        Vec_StrPush( vStatus, 1 );
    if ( Gia_ManCoNum(pSrm) == 0 )
    {
        if ( fVerbose )
            Abc_Print( 1, "[scorr2-audit] result=pass pairs=0 reason=structural time_sec=0.00\n" );
        *pvCexStore = vCexStore;
        *pvStatus = vStatus;
        return 1;
    }

    // fAddOrCla=1 asserts that at least one mismatch output is true.
    pCnf = (Cnf_Dat_t *)Mf_ManGenerateCnf( pSrm, 8, 0, 1, 0, 0 );
    pSat = kissat_solver_new();
    kissat_solver_setnvars( pSat, pCnf->nVars );
    Cnf_CnfForClause( pCnf, pBeg, pEnd, i )
        if ( !kissat_solver_addclause(pSat, pBeg, pEnd) )
        {
            // Contradiction during clause loading is already an UNSAT proof.
            Status = -1;
            goto finish;
        }
    Status = kissat_solver_solve( pSat, NULL, NULL, 0, 0, 0, 0 );
    if ( Status == -1 )
        goto finish;
    if ( Status == 0 )
        goto finish;

    // Evaluate the GIA under the Kissat model to identify a violated pair.
    pValues = ABC_CALLOC( unsigned char, Gia_ManObjNum(pSrm) );
    Gia_ManForEachCi( pSrm, pObj, i )
    {
        iVar = pCnf->pVarNums[Gia_ObjId(pSrm, pObj)];
        pValues[Gia_ObjId(pSrm, pObj)] = iVar >= 0 ? kissat_solver_get_var_value(pSat, iVar) : 0;
    }
    Gia_ManForEachAnd( pSrm, pObj, i )
        pValues[Gia_ObjId(pSrm, pObj)] =
            (pValues[Gia_ObjFaninId0p(pSrm, pObj)] ^ Gia_ObjFaninC0(pObj)) &
            (pValues[Gia_ObjFaninId1p(pSrm, pObj)] ^ Gia_ObjFaninC1(pObj));
    Gia_ManForEachCo( pSrm, pObj, i )
        if ( pValues[Gia_ObjFaninId0p(pSrm, pObj)] ^ Gia_ObjFaninC0(pObj) )
        {
            iOut = i;
            break;
        }
    if ( iOut < 0 )
    {
        Status = 0;
        goto finish;
    }
    {
        Vec_Int_t * vCex = Vec_IntAlloc( Gia_ManCiNum(pSrm) );
        Gia_ManForEachCi( pSrm, pObj, i )
            Vec_IntPush( vCex, Abc_Var2Lit(Gia_ObjCioId(pObj), !pValues[Gia_ObjId(pSrm, pObj)]) );
        Vec_StrWriteEntry( vStatus, iOut, 0 );
        Cec_ManSatAddToStore( vCexStore, vCex, iOut );
        Vec_IntFree( vCex );
    }

finish:
    if ( fVerbose )
    {
        if ( Status == -1 )
            Abc_Print( 1, "[scorr2-audit] result=pass pairs=%d vars=%d clauses=%d ", Gia_ManCoNum(pSrm), pCnf->nVars, pCnf->nClauses );
        else if ( Status == 1 && iOut >= 0 )
            Abc_Print( 1, "[scorr2-audit] result=counterexample pair=%d/%d nodes=%d/%d ", iOut, Gia_ManCoNum(pSrm), Vec_IntEntry(vOutputs, 2*iOut), Vec_IntEntry(vOutputs, 2*iOut+1) );
        else
            Abc_Print( -1, "[scorr2-audit] result=unknown pairs=%d ", Gia_ManCoNum(pSrm) );
        Abc_PrintTime( 1, "Kissat", Abc_Clock() - clk );
        if ( Status == 1 && iOut >= 0 && pValues != NULL )
        {
            Abc_Print( -1, "[scorr2-audit] model" );
            Gia_ManForEachCi( pSrm, pObj, i )
            {
                if ( i == 16 )
                {
                    Abc_Print( -1, " ..." );
                    break;
                }
                Abc_Print( -1, " ci%d=%d", Gia_ObjCioId(pObj), pValues[Gia_ObjId(pSrm, pObj)] );
            }
            Abc_Print( -1, "\n" );
        }
    }
    ABC_FREE( pValues );
    kissat_solver_delete( pSat );
    Cnf_DataFree( pCnf );
    *pvCexStore = vCexStore;
    *pvStatus = vStatus;
    *piOut = iOut;
    if ( Status == -1 )
        return 1;
    if ( Status == 1 && iOut >= 0 )
        return 0;
    return -1;
}

ABC_NAMESPACE_IMPL_END
