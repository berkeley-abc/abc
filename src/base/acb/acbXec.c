/**CFile****************************************************************

  FileName    [acbXec.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Hierarchical word-level netlist.]

  Synopsis    [Reusable XEC proof helpers.]

***********************************************************************/

#include "acbXec.h"
#include "aig/gia/giaAig.h"
#include "base/abc/abc.h"
#include "opt/dar/dar.h"
#include "sat/cadical/cadicalSolver.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

typedef enum Acb_SatStatus_t_
{
    ACB_SAT_UNSAT = -1,
    ACB_SAT_UNDEC =  0,
    ACB_SAT_SAT   =  1
} Acb_SatStatus_t;

int Acb_CnfCoDriverLit( Cnf_Dat_t * pCnf, int iCo, int * pLit )
{
    Aig_Obj_t * pCo = Aig_ManCo( pCnf->pMan, iCo );
    Aig_Obj_t * pFan = Aig_ObjFanin0( pCo );
    int fCompl = Aig_ObjFaninC0( pCo );
    int Var;
    if ( Aig_ObjIsConst1(pFan) )
        return fCompl ? -1 : 0;
    Var = pCnf->pVarNums[pFan->Id];
    if ( Var < 0 )
        return -2;
    *pLit = Abc_Var2Lit( Var, fCompl );
    return 1;
}

static int Acb_GiaPoIsConst0( Gia_Man_t * p, int iPo )
{
    Gia_Obj_t * pObj;
    if ( iPo < 0 || iPo >= Gia_ManCoNum(p) )
        return 0;
    pObj = Gia_ManCo( p, iPo );
    return Gia_ObjFanin0(pObj) == Gia_ManConst0(p) && !Gia_ObjFaninC0(pObj);
}

int Acb_GiaAllPosConst0( Gia_Man_t * p )
{
    int i;
    for ( i = 0; i < Gia_ManCoNum(p); i++ )
        if ( !Acb_GiaPoIsConst0(p, i) )
            return 0;
    return 1;
}

static word Acb_XecGiaVarWord( int iVar, ABC_UINT64_T iWord )
{
    static word Truth6[6] = {
        ABC_CONST(0xAAAAAAAAAAAAAAAA),
        ABC_CONST(0xCCCCCCCCCCCCCCCC),
        ABC_CONST(0xF0F0F0F0F0F0F0F0),
        ABC_CONST(0xFF00FF00FF00FF00),
        ABC_CONST(0xFFFF0000FFFF0000),
        ABC_CONST(0xFFFFFFFF00000000)
    };
    if ( iVar < 6 )
        return Truth6[iVar];
    return ((iWord >> (iVar - 6)) & 1) ? ~(word)0 : 0;
}
static inline word Acb_XecGiaLitWord( Vec_Wrd_t * vSims, int nWords, int Lit, int w )
{
    word Res = Vec_WrdEntry( vSims, Abc_Lit2Var(Lit) * nWords + w );
    return Abc_LitIsCompl(Lit) ? ~Res : Res;
}
int * Acb_NtkSolveCadicalLimit( Gia_Man_t * p, int fUseHeavyOpt, int fVerbose, int * pStatus, int nSatTimeLimit, const char * pLabel, int fUseXecOutputClauses )
{
    Aig_Man_t * pMan = NULL;
    Cnf_Dat_t * pCnf = NULL;
    cadical_solver * pSat = NULL;
    Vec_Int_t * vPoLits = NULL;
    Gia_Man_t * pGiaOpt = NULL, * pGiaTemp = NULL;
    Gia_Man_t * pGia = p;
    Aig_Obj_t * pObj;
    int i, Ret, Lit, Status = ACB_SAT_UNDEC, * pBeg, * pEnd, * pModel = NULL;
    int fRunSolve = 0, fSolvedSat = 0;
    abctime clk = Abc_Clock();
    (void)fUseXecOutputClauses;
    if ( pStatus )
        *pStatus = ACB_XEC_UNDEC;
    if ( p == NULL )
        return NULL;
    if ( Gia_ManCoNum(p) == 0 || Acb_GiaAllPosConst0(p) )
    {
        if ( pStatus )
            *pStatus = ACB_XEC_EQ;
        if ( pLabel )
        {
            printf( "The networks are equivalent by %s.  ", pLabel );
            Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
        }
        return NULL;
    }
    if ( fUseHeavyOpt && Gia_ManAndNum(p) > 0 )
    {
        pGiaTemp = Gia_ManCompress2( p, 1, 0 );
        if ( pGiaTemp )
        {
            pGiaOpt = pGiaTemp;
            pGiaTemp = NULL;
            pGia = pGiaOpt;
            assert( Gia_ManCiNum(pGia) == Gia_ManCiNum(p) );
        }
    }
    pMan = Gia_ManToAig( pGia, 0 );
    pCnf = pMan ? Cnf_Derive( pMan, Aig_ManCoNum(pMan) ) : NULL;
    pSat = pCnf ? cadical_solver_new() : NULL;
    if ( pCnf && pSat )
    {
        fRunSolve = 1;
        cadical_solver_setnvars( pSat, pCnf->nVars );
        Cnf_CnfForClause( pCnf, pBeg, pEnd, i )
        {
            if ( !cadical_solver_addclause( pSat, pBeg, pEnd ) )
            {
                Status = ACB_SAT_UNSAT;
                fRunSolve = 0;
                break;
            }
        }
        if ( fRunSolve )
        {
            vPoLits = Vec_IntAlloc( Gia_ManCoNum(pGia) );
            for ( i = 0; i < Gia_ManCoNum(pGia); i++ )
            {
                Ret = Acb_CnfCoDriverLit( pCnf, i, &Lit );
                if ( Ret == -2 )
                {
                    Status = ACB_SAT_UNDEC;
                    fRunSolve = 0;
                    break;
                }
                if ( Ret == -1 )
                    continue;
                if ( Ret == 0 )
                {
                    Status = ACB_SAT_SAT;
                    fRunSolve = 0;
                    break;
                }
                Vec_IntPush( vPoLits, Lit );
            }
        }
        if ( fRunSolve && Vec_IntSize(vPoLits) == 0 )
        {
            Status = ACB_SAT_UNSAT;
            fRunSolve = 0;
        }
        if ( fRunSolve && !cadical_solver_addclause( pSat, Vec_IntArray(vPoLits), Vec_IntArray(vPoLits) + Vec_IntSize(vPoLits) ) )
        {
            Status = ACB_SAT_UNSAT;
            fRunSolve = 0;
        }
        if ( fRunSolve && fVerbose )
        {
            printf( "CaDiCaL CNF: Var = %d. Cla = %d. PO = %d.\n",
                pCnf->nVars, pCnf->nClauses + 1, Gia_ManCoNum(pGia) );
            if ( nSatTimeLimit > 0 )
                printf( "CaDiCaL SAT runtime limit: %d sec.\n", nSatTimeLimit );
        }
        if ( fRunSolve )
        {
            Status = cadical_solver_solve( pSat, NULL, NULL, 0, 0, 0, 0 );
            fSolvedSat = Status == ACB_SAT_SAT;
        }
        if ( fVerbose )
            printf( "CaDiCaL stats: conflicts = %d. learned = %d.\n",
                cadical_solver_nconflicts(pSat), cadical_solver_nlearned(pSat) );
    }
    if ( Status == ACB_SAT_UNSAT )
    {
        if ( pStatus )
            *pStatus = ACB_XEC_EQ;
        if ( pLabel )
        {
            printf( "The networks are equivalent by %s.  ", pLabel );
            Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
        }
    }
    else if ( Status == ACB_SAT_SAT )
    {
        if ( pStatus )
            *pStatus = ACB_XEC_NEQ;
        if ( fSolvedSat )
            pModel = ABC_CALLOC( int, Gia_ManCiNum(pGia) );
        if ( pModel && pSat && pCnf && pMan )
            Aig_ManForEachCi( pMan, pObj, i )
            {
                int Var = pCnf->pVarNums[pObj->Id];
                pModel[i] = Var >= 0 ? cadical_solver_get_var_value( pSat, Var ) : 0;
            }
        if ( pLabel )
        {
            printf( "The networks are NOT equivalent by %s.  ", pLabel );
            Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
        }
    }
    else
    {
        if ( pStatus )
            *pStatus = ACB_XEC_UNDEC;
        if ( fVerbose && pLabel )
        {
            printf( "The networks are UNDECIDED by %s.  ", pLabel );
            Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
        }
    }
    if ( pSat )
        cadical_solver_delete( pSat );
    if ( pCnf )
        Cnf_DataFree( pCnf );
    if ( pMan )
        Aig_ManStop( pMan );
    if ( pGiaOpt )
        Gia_ManStop( pGiaOpt );
    Vec_IntFreeP( &vPoLits );
    return pModel;
}
int Acb_XecGiaSolveSmallConeExhaustive( Gia_Man_t * p, int fVerbose, int nTotalLimit )
{
    Vec_Wrd_t * vSims = NULL;
    Gia_Obj_t * pObj;
    ABC_UINT64_T nWordsTotal, nWordBudget, iWordBase, nWordsDone = 0;
    int i, w, nWords, nWordsChunk, nObjs, nCis, nHiVars, Status = ACB_XEC_EQ, fDone = 0;
    abctime clk = Abc_Clock();
    abctime clkLimit = nTotalLimit > 0 ? clk + nTotalLimit * CLOCKS_PER_SEC : 0;
    if ( Gia_ManCoNum(p) != 1 || Gia_ManAndNum(p) > 5000 )
        return ACB_XEC_UNDEC;
    nCis = Gia_ManCiNum(p);
    nHiVars = Abc_MaxInt( 0, nCis - 6 );
    if ( nHiVars >= 63 )
    {
        if ( fVerbose )
            printf( "Skipping small-cone exhaustive word proof: CI = %d needs more than 2^63 simulation words.\n", nCis );
        return ACB_XEC_UNDEC;
    }
    nWordsChunk = nCis >= 31 ? 4096 : (nCis >= 28 ? 8192 : 16384);
    nWordsTotal = nHiVars ? ((ABC_UINT64_T)1 << nHiVars) : 1;
    nWordBudget = nTotalLimit > 0 ? (ABC_UINT64_T)200000 * nTotalLimit : (ABC_UINT64_T)60000000;
    if ( nWordBudget < (ABC_UINT64_T)8000000 )
        nWordBudget = (ABC_UINT64_T)8000000;
    if ( nWordsTotal > nWordBudget )
    {
        if ( fVerbose )
            printf( "Skipping small-cone exhaustive word proof: CI = %d needs %llu words, budget = %llu words.\n",
                nCis, (unsigned long long)nWordsTotal, (unsigned long long)nWordBudget );
        return ACB_XEC_UNDEC;
    }
    nObjs = Gia_ManObjNum(p);
    vSims = Vec_WrdStart( nObjs * nWordsChunk );
    if ( fVerbose )
        printf( "Trying small-cone exhaustive word proof: CI = %d. AND = %d. chunks = %llu x %d words. limit = %d sec.\n",
            nCis, Gia_ManAndNum(p), (unsigned long long)((nWordsTotal + nWordsChunk - 1) / nWordsChunk), nWordsChunk, nTotalLimit );
    for ( iWordBase = 0; iWordBase < nWordsTotal && !fDone; iWordBase += nWordsChunk )
    {
        ABC_UINT64_T nWordsLeft = nWordsTotal - iWordBase;
        nWords = nWordsLeft < (ABC_UINT64_T)nWordsChunk ? (int)nWordsLeft : nWordsChunk;
        if ( clkLimit && Abc_Clock() >= clkLimit )
        {
            Status = ACB_XEC_UNDEC;
            break;
        }
        /* Only the active words [0..nWords) are consumed in this chunk; other words may retain previous data. */
        for ( w = 0; w < nWords; w++ )
            Vec_WrdWriteEntry( vSims, w, 0 );
        Gia_ManForEachCi( p, pObj, i )
            for ( w = 0; w < nWords; w++ )
                Vec_WrdWriteEntry( vSims, Gia_ObjId(p, pObj) * nWordsChunk + w, Acb_XecGiaVarWord(i, iWordBase + w) );
        Gia_ManForEachAnd( p, pObj, i )
            for ( w = 0; w < nWords; w++ )
                Vec_WrdWriteEntry( vSims, Gia_ObjId(p, pObj) * nWordsChunk + w,
                    Acb_XecGiaLitWord(vSims, nWordsChunk, Gia_ObjFaninLit0p(p, pObj), w) &
                    Acb_XecGiaLitWord(vSims, nWordsChunk, Gia_ObjFaninLit1p(p, pObj), w) );
        pObj = Gia_ManCo( p, 0 );
        for ( w = 0; w < nWords; w++ )
        {
            word Res = Acb_XecGiaLitWord(vSims, nWordsChunk, Gia_ObjFaninLit0p(p, pObj), w);
            if ( iWordBase + w + 1 == nWordsTotal && nCis < 6 )
                Res &= (((word)1) << (1 << nCis)) - 1;
            if ( Res )
            {
                Status = ACB_XEC_UNDEC;
                fDone = 1;
                break;
            }
        }
        nWordsDone += nWords;
    }
    if ( fVerbose )
    {
        printf( "Small-cone exhaustive word proof: %s. checked words = %llu/%llu. ",
            Status == ACB_XEC_EQ ? "UNSAT" : "UNDECIDED",
            (unsigned long long)nWordsDone, (unsigned long long)nWordsTotal );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    }
    Vec_WrdFree( vSims );
    return Status;
}
Gia_Man_t * Acb_XecGiaSmallConeXorRewrite( Gia_Man_t * p, int fVerbose )
{
    Aig_Man_t * pAig = NULL, * pAigTemp = NULL;
    Gia_Man_t * pGia = NULL, * pTemp = NULL;
    int nAndStart = Gia_ManAndNum(p);
    abctime clk = Abc_Clock();
    if ( Gia_ManCoNum(p) != 1 || Gia_ManCiNum(p) > 64 || nAndStart > 8000 )
        return NULL;
    if ( fVerbose )
        printf( "Small-cone XOR structural rewrite: CI = %d. AND = %d.\n",
            Gia_ManCiNum(p), nAndStart );
    pAig = Gia_ManToAig( p, 0 );
    if ( pAig == NULL )
        return NULL;
    pAig = Dar_ManBalanceXor( pAigTemp = pAig, 1, 1, 0 );
    Aig_ManStop( pAigTemp );
    if ( pAig == NULL )
        return NULL;
    pAig = Dar_ManRwsat( pAigTemp = pAig, 1, 0 );
    Aig_ManStop( pAigTemp );
    if ( pAig == NULL )
        return NULL;
    pGia = Gia_ManFromAig( pAig );
    Aig_ManStop( pAig );
    if ( pGia == NULL )
        return NULL;
    pTemp = Gia_ManCompress2( pGia, 1, 0 );
    if ( pTemp )
    {
        Gia_ManStop( pGia );
        pGia = pTemp;
    }
    if ( fVerbose )
    {
        printf( "Small-cone XOR structural rewrite: AND = %d -> %d. Lev = %d -> %d. ",
            nAndStart, Gia_ManAndNum(pGia), Gia_ManLevelNum(p), Gia_ManLevelNum(pGia) );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    }
    if ( Gia_ManCoNum(pGia) != Gia_ManCoNum(p) ||
         (!Acb_GiaAllPosConst0(pGia) && Gia_ManAndNum(pGia) >= nAndStart) )
    {
        Gia_ManStop( pGia );
        return NULL;
    }
    return pGia;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
