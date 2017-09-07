/**CFile****************************************************************

  FileName    [AbcGlucose.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT solver Glucose 3.0.]

  Synopsis    [Interface to Glucose.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 6, 2017.]

  Revision    [$Id: AbcGlucose.cpp,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sat/glucose/System.h"
#include "sat/glucose/ParseUtils.h"
#include "sat/glucose/Options.h"
#include "sat/glucose/Dimacs.h"
#include "sat/glucose/SimpSolver.h"

#include "sat/glucose/AbcGlucose.h"

#include "aig/gia/gia.h"
#include "sat/cnf/cnf.h"

using namespace Gluco;

ABC_NAMESPACE_IMPL_START

extern "C" {

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
Gluco::Solver * glucose_solver_start()
{
    Solver * S = new Solver;
    S->setIncrementalMode();
    return S;
}

void glucose_solver_stop(Gluco::Solver* S)
{
    delete S;
}

int glucose_solver_addclause(Gluco::Solver* S, int * plits, int nlits)
{
    vec<Lit> lits;
    for ( int i = 0; i < nlits; i++,plits++)
    {
        // note: Glucose uses the same var->lit conventiaon as ABC
        while ((*plits)/2 >= S->nVars()) S->newVar();
        assert((*plits)/2 < S->nVars()); // NOTE: since we explicitely use new function bmc_add_var
        Lit p;
        p.x = *plits;
        lits.push(p);
    }
    return S->addClause(lits); // returns 0 if the problem is UNSAT
}

void glucose_solver_setcallback(Gluco::Solver* S, void * pman, int(*pfunc)(void*, int, int*))
{
    S->pCnfMan = pman;
    S->pCnfFunc = pfunc;
    S->nCallConfl = 1000;
}

int glucose_solver_solve(Gluco::Solver* S, int * plits, int nlits)
{
    vec<Lit> lits;
    for (int i=0;i<nlits;i++,plits++)
    {
        Lit p;
        p.x = *plits;
        lits.push(p);
    }
    Gluco::lbool res = S->solveLimited(lits);
    return (res == l_True ? 1 : res == l_False ? -1 : 0);
}

int glucose_solver_addvar(Gluco::Solver* S)
{
    S->newVar();
    return S->nVars() - 1;
}

int glucose_solver_read_cex_varvalue(Gluco::Solver* S, int ivar)
{
    return S->model[ivar] == l_True;
}

void glucose_solver_setstop(Gluco::Solver* S, int * pstop)
{
    S->pstop = pstop;
}

void glucose_print_stats(Solver& s, abctime clk)
{
    double cpu_time = (double)(unsigned)clk / CLOCKS_PER_SEC;
    double mem_used = memUsed();
    printf("c restarts              : %d (%d conflicts on average)\n",         (int)s.starts, s.starts > 0 ? s.conflicts/s.starts : 0);
    printf("c blocked restarts      : %d (multiple: %d) \n",                   (int)s.nbstopsrestarts,s.nbstopsrestartssame);
    printf("c last block at restart : %d\n",                                   (int)s.lastblockatrestart);
    printf("c nb ReduceDB           : %-12d\n",                                (int)s.nbReduceDB);
    printf("c nb removed Clauses    : %-12d\n",                                (int)s.nbRemovedClauses);
    printf("c nb learnts DL2        : %-12d\n",                                (int)s.nbDL2);
    printf("c nb learnts size 2     : %-12d\n",                                (int)s.nbBin);
    printf("c nb learnts size 1     : %-12d\n",                                (int)s.nbUn);
    printf("c conflicts             : %-12d  (%.0f /sec)\n",                   (int)s.conflicts,    s.conflicts   /cpu_time);
    printf("c decisions             : %-12d  (%4.2f %% random) (%.0f /sec)\n", (int)s.decisions,    (float)s.rnd_decisions*100 / (float)s.decisions, s.decisions   /cpu_time);
    printf("c propagations          : %-12d  (%.0f /sec)\n",                   (int)s.propagations, s.propagations/cpu_time);
    printf("c conflict literals     : %-12d  (%4.2f %% deleted)\n",            (int)s.tot_literals, (s.max_literals - s.tot_literals)*100 / (double)s.max_literals);
    printf("c nb reduced Clauses    : %-12d\n", (int)s.nbReducedClauses);
    if (mem_used != 0) printf("Memory used           : %.2f MB\n", mem_used);
    //printf("c CPU time              : %.2f sec\n", cpu_time);
}

/**Function*************************************************************

  Synopsis    [Wrapper APIs to calling from ABC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bmcg_sat_solver * bmcg_sat_solver_start() 
{
    return (bmcg_sat_solver *)glucose_solver_start();
}
void bmcg_sat_solver_stop(bmcg_sat_solver* s)
{
    glucose_solver_stop((Gluco::Solver*)s);
}

int bmcg_sat_solver_addclause(bmcg_sat_solver* s, int * plits, int nlits)
{
    return glucose_solver_addclause((Gluco::Solver*)s,plits,nlits);
}

void bmcg_sat_solver_setcallback(bmcg_sat_solver* s, void * pman, int(*pfunc)(void*, int, int*))
{
    glucose_solver_setcallback((Gluco::Solver*)s,pman,pfunc);
}

int bmcg_sat_solver_solve(bmcg_sat_solver* s, int * plits, int nlits)
{
    return glucose_solver_solve((Gluco::Solver*)s,plits,nlits);
}

int bmcg_sat_solver_addvar(bmcg_sat_solver* s)
{
    return glucose_solver_addvar((Gluco::Solver*)s);
}

int bmcg_sat_solver_read_cex_varvalue(bmcg_sat_solver* s, int ivar)
{
    return glucose_solver_read_cex_varvalue((Gluco::Solver*)s, ivar);
}

void bmcg_sat_solver_setstop(bmcg_sat_solver* s, int * pstop)
{
    glucose_solver_setstop((Gluco::Solver*)s, pstop);
}

abctime bmcg_sat_solver_set_runtime_limit(bmcg_sat_solver* s, abctime Limit)
{
    abctime nRuntimeLimit = ((Gluco::Solver*)s)->nRuntimeLimit;
    ((Gluco::Solver*)s)->nRuntimeLimit = Limit;
    return nRuntimeLimit;
}

void bmcg_sat_solver_set_conflict_budget(bmcg_sat_solver* s, int Limit)
{
    if ( Limit > 0 ) 
        ((Gluco::Solver*)s)->setConfBudget( (int64_t)Limit );
    else 
        ((Gluco::Solver*)s)->budgetOff();
}

int bmcg_sat_solver_varnum(bmcg_sat_solver* s)
{
    return ((Gluco::Solver*)s)->nVars();
}
int bmcg_sat_solver_clausenum(bmcg_sat_solver* s)
{
    return ((Gluco::Solver*)s)->nClauses();
}
int bmcg_sat_solver_learntnum(bmcg_sat_solver* s)
{
    return ((Gluco::Solver*)s)->nLearnts();
}
int bmcg_sat_solver_conflictnum(bmcg_sat_solver* s)
{
    return ((Gluco::Solver*)s)->conflicts;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Glucose_SolveCnf( char * pFilename, Glucose_Pars * pPars )
{
    abctime clk = Abc_Clock();

    SimpSolver  S;
    S.verbosity = pPars->verb;
    S.setConfBudget( pPars->nConfls > 0 ? (int64_t)pPars->nConfls : -1 );

    gzFile in = gzopen(pFilename, "rb");
    parse_DIMACS(in, S);
    gzclose(in);

    if ( pPars->verb )
    {
        printf("c ============================[ Problem Statistics ]=============================\n");
        printf("c |                                                                             |\n");
        printf("c |  Number of variables:  %12d                                         |\n", S.nVars());
        printf("c |  Number of clauses:    %12d                                         |\n", S.nClauses());
    }
    
    if ( pPars->pre ) S.eliminate(true);

    vec<Lit> dummy;
    lbool ret = S.solveLimited(dummy);
    if ( pPars->verb ) glucose_print_stats(S, Abc_Clock() - clk);
    printf(ret == l_True ? "SATISFIABLE" : ret == l_False ? "UNSATISFIABLE" : "INDETERMINATE");
    Abc_PrintTime( 1, "      Time", Abc_Clock() - clk );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Glucose_SolverFromAig( Gia_Man_t * p, SimpSolver& S )
{
    //abctime clk = Abc_Clock();
    int * pLit, * pStop, i;
    Cnf_Dat_t * pCnf = (Cnf_Dat_t *)Mf_ManGenerateCnf( p, 8 /*nLutSize*/, 0 /*fCnfObjIds*/, 1/*fAddOrCla*/, 0, 0/*verbose*/ );
    for ( i = 0; i < pCnf->nClauses; i++ )
    {
        vec<Lit> lits;
        for ( pLit = pCnf->pClauses[i], pStop = pCnf->pClauses[i+1]; pLit < pStop; pLit++ )
        {
            int Lit = *pLit;
            int parsed_lit = (Lit & 1)? -(Lit >> 1)-1 : (Lit >> 1)+1;
            int var = abs(parsed_lit)-1;
            while (var >= S.nVars()) S.newVar();
            lits.push( (parsed_lit > 0) ? mkLit(var) : ~mkLit(var) );
        }
        S.addClause(lits);
    }
    Vec_Int_t * vCnfIds = Vec_IntAllocArrayCopy(pCnf->pVarNums,pCnf->nVars);
    //printf( "CNF stats: Vars = %6d. Clauses = %7d. Literals = %8d. ", pCnf->nVars, pCnf->nClauses, pCnf->nLiterals );
    //Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    Cnf_DataFree(pCnf);
    return vCnfIds;
}

int Glucose_SolveAig(Gia_Man_t * p, Glucose_Pars * pPars)
{  
    abctime clk = Abc_Clock();

    SimpSolver S;
    S.verbosity = pPars->verb;
    S.verbEveryConflicts = 50000;
    S.showModel = false;
    S.setConfBudget( pPars->nConfls > 0 ? (int64_t)pPars->nConfls : -1 );

    S.parsing = 1;
    Vec_Int_t * vCnfIds = Glucose_SolverFromAig(p,S);
    S.parsing = 0;

    if (pPars->verb)
    {
        printf("c ============================[ Problem Statistics ]=============================\n");
        printf("c |                                                                             |\n");
        printf("c |  Number of variables:  %12d                                         |\n", S.nVars());
        printf("c |  Number of clauses:    %12d                                         |\n", S.nClauses());
    }

    if (pPars->pre) 
        S.eliminate(true);
    
    vec<Lit> dummy;
    lbool ret = S.solveLimited(dummy);

    if ( pPars->verb ) glucose_print_stats(S, Abc_Clock() - clk);
    printf(ret == l_True ? "SATISFIABLE" : ret == l_False ? "UNSATISFIABLE" : "INDETERMINATE");
    Abc_PrintTime( 1, "      Time", Abc_Clock() - clk );

    // port counterexample
    if (ret == l_True)
    {
        Gia_Obj_t * pObj;  int i;
        p->pCexComb = Abc_CexAlloc(0,Gia_ManCiNum(p),1);
        Gia_ManForEachCi( p, pObj, i )
        {
            assert(Vec_IntEntry(vCnfIds,Gia_ObjId(p, pObj))!=-1);
            if (S.model[Vec_IntEntry(vCnfIds,Gia_ObjId(p, pObj))] == l_True)
                Abc_InfoSetBit( p->pCexComb->pData, i);
        }
    }
    Vec_IntFree(vCnfIds);
    return (ret == l_True ? 10 : ret == l_False ? 20 : 0);
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

}

ABC_NAMESPACE_IMPL_END
