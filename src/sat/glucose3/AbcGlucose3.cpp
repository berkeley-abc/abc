/**CFile****************************************************************

  FileName    [AbcGlucose3.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT solver Glucose 3.0 by Gilles Audemard and Laurent Simon.]

  Synopsis    [Interface to Glucose.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: AbcGlucose3.cpp,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sat/glucose3/AbcGlucose3.h"
#include "sat/glucose3/SimpSolver.h"

ABC_NAMESPACE_IMPL_START

using namespace Gluco3;

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
SimpSolver * glucose3_solver_start()
{
    SimpSolver * S = new SimpSolver;
    S->setIncrementalMode();
    return S;
}

void glucose3_solver_stop(Gluco3::SimpSolver* S)
{
    delete S;
}

void glucose3_solver_reset(Gluco3::SimpSolver* S)
{
    S->reset();
}

int glucose3_solver_addclause(Gluco3::SimpSolver* S, int * plits, int nlits)
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

void glucose3_solver_setcallback(Gluco3::SimpSolver* S, void * pman, int(*pfunc)(void*, int, int*))
{
    S->pCnfMan = pman;
    S->pCnfFunc = pfunc;
    S->nCallConfl = 1000;
}

int glucose3_solver_solve(Gluco3::SimpSolver* S, int * plits, int nlits)
{
//    vec<Lit> lits;
//    for (int i=0;i<nlits;i++,plits++)
//    {
//        Lit p;
//        p.x = *plits;
//        lits.push(p);
//    }
//    Gluco3::lbool res = S->solveLimited(lits, 0);
//    return (res == G3_l_True ? 1 : res == G3_l_False ? -1 : 0);
    return S->solveLimited(plits, nlits, 0);
}

int glucose3_solver_addvar(Gluco3::SimpSolver* S)
{
    S->newVar();
    return S->nVars() - 1;
}

int * glucose3_solver_read_cex(Gluco3::SimpSolver* S )
{
    return S->getCex();
}

int glucose3_solver_read_cex_varvalue(Gluco3::SimpSolver* S, int ivar)
{
    return S->model[ivar] == G3_l_True;
}

void glucose3_solver_setstop(Gluco3::SimpSolver* S, int * pstop)
{
    S->pstop = pstop;
}

void glucose3_markapprox( Gluco3::SimpSolver* S, int v0, int v1, int nlim )
{
    S->markApprox(v0, v1, nlim);
}

/**Function*************************************************************

  Synopsis    [Wrapper APIs to calling from ABC.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
bmcg3_sat_solver * bmcg3_sat_solver_start()
{
    return (bmcg3_sat_solver *)glucose3_solver_start();
}
void bmcg3_sat_solver_stop(bmcg3_sat_solver* s)
{
    glucose3_solver_stop((Gluco3::SimpSolver*)s);
}
void bmcg3_sat_solver_reset(bmcg3_sat_solver* s)
{
    glucose3_solver_reset((Gluco3::SimpSolver*)s);
}


int bmcg3_sat_solver_addclause(bmcg3_sat_solver* s, int * plits, int nlits)
{
    return glucose3_solver_addclause((Gluco3::SimpSolver*)s,plits,nlits);
}

void bmcg3_sat_solver_setcallback(bmcg3_sat_solver* s, void * pman, int(*pfunc)(void*, int, int*))
{
    glucose3_solver_setcallback((Gluco3::SimpSolver*)s,pman,pfunc);
}

int bmcg3_sat_solver_solve(bmcg3_sat_solver* s, int * plits, int nlits)
{
    return glucose3_solver_solve((Gluco3::SimpSolver*)s,plits,nlits);
}

int bmcg3_sat_solver_final(bmcg3_sat_solver* s, int ** ppArray)
{
    *ppArray = (int *)(Lit *)((Gluco3::SimpSolver*)s)->conflict;
    return ((Gluco3::SimpSolver*)s)->conflict.size();
}

int bmcg3_sat_solver_addvar(bmcg3_sat_solver* s)
{
    return glucose3_solver_addvar((Gluco3::SimpSolver*)s);
}

void bmcg3_sat_solver_set_nvars( bmcg3_sat_solver* s, int nvars )
{
    ((Gluco3::SimpSolver*)s)->addVars(nvars);
}

int bmcg3_sat_solver_eliminate( bmcg3_sat_solver* s, int turn_off_elim )
{
//    return 1;
    return ((Gluco3::SimpSolver*)s)->eliminate(turn_off_elim != 0);
}

int bmcg3_sat_solver_var_is_elim( bmcg3_sat_solver* s, int v )
{
//    return 0;
    return ((Gluco3::SimpSolver*)s)->isEliminated(v);
}

void bmcg3_sat_solver_var_set_frozen( bmcg3_sat_solver* s, int v, int freeze )
{
    ((Gluco3::SimpSolver*)s)->setFrozen(v, freeze != 0);
}

int bmcg3_sat_solver_elim_varnum(bmcg3_sat_solver* s)
{
//    return 0;
    return ((Gluco3::SimpSolver*)s)->eliminated_vars;
}

int * bmcg3_sat_solver_read_cex(bmcg3_sat_solver* s)
{
    return glucose3_solver_read_cex((Gluco3::SimpSolver*)s);
}
int bmcg3_sat_solver_read_cex_varvalue(bmcg3_sat_solver* s, int ivar)
{
    return glucose3_solver_read_cex_varvalue((Gluco3::SimpSolver*)s, ivar);
}

/**Function*************************************************************

  Synopsis    [Returns a permanent literal value, or minus one if unknown.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int bmcg3_sat_solver_read_unit( bmcg3_sat_solver * s, int lit )
{
    Gluco3::SimpSolver * p = (Gluco3::SimpSolver *)s;
    Gluco3::lbool Value = p->value( Gluco3::toLit(lit) );
    return Value == G3_l_Undef || p->level(lit >> 1) != 0 ? -1 : Value == G3_l_True;
}

void bmcg3_sat_solver_set_stop(bmcg3_sat_solver* s, int * pstop)
{
    glucose3_solver_setstop((Gluco3::SimpSolver*)s, pstop);
}

void bmcg3_sat_solver_markapprox(bmcg3_sat_solver* s, int v0, int v1, int nlim)
{
    glucose3_markapprox((Gluco3::SimpSolver*)s, v0, v1, nlim);
}

abctime bmcg3_sat_solver_set_runtime_limit(bmcg3_sat_solver* s, abctime Limit)
{
    abctime nRuntimeLimit = ((Gluco3::SimpSolver*)s)->nRuntimeLimit;
    ((Gluco3::SimpSolver*)s)->nRuntimeLimit = Limit;
    return nRuntimeLimit;
}

void bmcg3_sat_solver_set_conflict_budget(bmcg3_sat_solver* s, int Limit)
{
    if ( Limit > 0 )
        ((Gluco3::SimpSolver*)s)->setConfBudget( (int64_t)Limit );
    else
        ((Gluco3::SimpSolver*)s)->budgetOff();
}

int bmcg3_sat_solver_varnum(bmcg3_sat_solver* s)
{
    return ((Gluco3::SimpSolver*)s)->nVars();
}
int bmcg3_sat_solver_clausenum(bmcg3_sat_solver* s)
{
    return ((Gluco3::SimpSolver*)s)->nClauses();
}
int bmcg3_sat_solver_learntnum(bmcg3_sat_solver* s)
{
    return ((Gluco3::SimpSolver*)s)->nLearnts();
}
int bmcg3_sat_solver_conflictnum(bmcg3_sat_solver* s)
{
    return ((Gluco3::SimpSolver*)s)->conflicts;
}

int bmcg3_sat_solver_minimize_assumptions( bmcg3_sat_solver * s, int * plits, int nlits, int pivot )
{
    vec<int>*array = &((Gluco3::SimpSolver*)s)->user_vec;
    int i, nlitsL, nlitsR, nresL, nresR, status;
    assert( pivot >= 0 );
//    assert( nlits - pivot >= 2 );
    assert( nlits - pivot >= 1 );
    if ( nlits - pivot == 1 )
    {
        // since the problem is UNSAT, we try to solve it without assuming the last literal
        // if the result is UNSAT, the last literal can be dropped; otherwise, it is needed
        status = bmcg3_sat_solver_solve( s, plits, pivot );
        return status != GLUCOSE3_UNSAT; // return 1 if the problem is not UNSAT
    }
    assert( nlits - pivot >= 2 );
    nlitsL = (nlits - pivot) / 2;
    nlitsR = (nlits - pivot) - nlitsL;
    assert( nlitsL + nlitsR == nlits - pivot );
    // solve with these assumptions
    status = bmcg3_sat_solver_solve( s, plits, pivot + nlitsL );
    if ( status == GLUCOSE3_UNSAT ) // these are enough
        return bmcg3_sat_solver_minimize_assumptions( s, plits, pivot + nlitsL, pivot );
    // these are not enough
    // solve for the right lits
//    nResL = nLitsR == 1 ? 1 : sat_solver_minimize_assumptions( s, pLits + nLitsL, nLitsR, nConfLimit );
    nresL = nlitsR == 1 ? 1 : bmcg3_sat_solver_minimize_assumptions( s, plits, nlits, pivot + nlitsL );
    // swap literals
    array->clear();
    for ( i = 0; i < nlitsL; i++ )
        array->push(plits[pivot + i]);
    for ( i = 0; i < nresL; i++ )
        plits[pivot + i] = plits[pivot + nlitsL + i];
    for ( i = 0; i < nlitsL; i++ )
        plits[pivot + nresL + i] = (*array)[i];
    // solve with these assumptions
    status = bmcg3_sat_solver_solve( s, plits, pivot + nresL );
    if ( status == GLUCOSE3_UNSAT ) // these are enough
        return nresL;
    // solve for the left lits
//    nResR = nLitsL == 1 ? 1 : sat_solver_minimize_assumptions( s, pLits + nResL, nLitsL, nConfLimit );
    nresR = nlitsL == 1 ? 1 : bmcg3_sat_solver_minimize_assumptions( s, plits, pivot + nresL + nlitsL, pivot + nresL );
    return nresL + nresR;
}

int bmcg3_sat_solver_add_and( bmcg3_sat_solver * s, int iVar, int iVar0, int iVar1, int fCompl0, int fCompl1, int fCompl )
{
    int Lits[3];

    Lits[0] = Abc_Var2Lit( iVar, !fCompl );
    Lits[1] = Abc_Var2Lit( iVar0, fCompl0 );
    if ( !bmcg3_sat_solver_addclause( s, Lits, 2 ) )
        return 0;

    Lits[0] = Abc_Var2Lit( iVar, !fCompl );
    Lits[1] = Abc_Var2Lit( iVar1, fCompl1 );
    if ( !bmcg3_sat_solver_addclause( s, Lits, 2 ) )
        return 0;

    Lits[0] = Abc_Var2Lit( iVar,   fCompl );
    Lits[1] = Abc_Var2Lit( iVar0, !fCompl0 );
    Lits[2] = Abc_Var2Lit( iVar1, !fCompl1 );
    if ( !bmcg3_sat_solver_addclause( s, Lits, 3 ) )
        return 0;

    return 1;
}

int bmcg3_sat_solver_add_xor( bmcg3_sat_solver * pSat, int iVarA, int iVarB, int iVarC, int fCompl )
{
    int Lits[3];
    int Cid;
    assert( iVarA >= 0 && iVarB >= 0 && iVarC >= 0 );

    Lits[0] = Abc_Var2Lit( iVarA, !fCompl );
    Lits[1] = Abc_Var2Lit( iVarB, 1 );
    Lits[2] = Abc_Var2Lit( iVarC, 1 );
    Cid = bmcg3_sat_solver_addclause( pSat, Lits, 3 );
    assert( Cid );

    Lits[0] = Abc_Var2Lit( iVarA, !fCompl );
    Lits[1] = Abc_Var2Lit( iVarB, 0 );
    Lits[2] = Abc_Var2Lit( iVarC, 0 );
    Cid = bmcg3_sat_solver_addclause( pSat, Lits, 3 );
    assert( Cid );

    Lits[0] = Abc_Var2Lit( iVarA, fCompl );
    Lits[1] = Abc_Var2Lit( iVarB, 1 );
    Lits[2] = Abc_Var2Lit( iVarC, 0 );
    Cid = bmcg3_sat_solver_addclause( pSat, Lits, 3 );
    assert( Cid );

    Lits[0] = Abc_Var2Lit( iVarA, fCompl );
    Lits[1] = Abc_Var2Lit( iVarB, 0 );
    Lits[2] = Abc_Var2Lit( iVarC, 1 );
    Cid = bmcg3_sat_solver_addclause( pSat, Lits, 3 );
    assert( Cid );
    return 4;
}

int bmcg3_sat_solver_jftr(bmcg3_sat_solver* s)
{
    return ((Gluco3::SimpSolver*)s)->jftr;
}

void bmcg3_sat_solver_set_jftr(bmcg3_sat_solver* s, int jftr)
{
    ((Gluco3::SimpSolver*)s)->jftr = jftr;
}

void bmcg3_sat_solver_set_var_fanin_lit(bmcg3_sat_solver* s, int var, int lit0, int lit1)
{
    ((Gluco3::SimpSolver*)s)->sat_solver_set_var_fanin_lit(var, lit0, lit1);
}

void bmcg3_sat_solver_select_cone(bmcg3_sat_solver* s, int v0, int v1)
{
    ((Gluco3::SimpSolver*)s)->selectCone(v0, v1);
}

/**Function*************************************************************

  Synopsis    [Selects the union of the query's circuit cones.]

  Description [Do not mix with the two-root interface until solver reset.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void bmcg3_sat_solver_select_cones( bmcg3_sat_solver * s, const int * roots, int count )
{
    ((Gluco3::SimpSolver *)s)->selectCones( roots, count );
}

/**Function*************************************************************

  Synopsis    [Enables justification of permanent gate units.]

  Description [Disable only when permanent gate units follow from the
  circuit itself. Arbitrary gate constraints must be query assumptions
  or justified units.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void bmcg3_sat_solver_set_unit_justification( bmcg3_sat_solver * s, int enable )
{
    ((Gluco3::SimpSolver *)s)->setUnitJustification( enable != 0 );
}

void bmcg3_sat_solver_start_new_round(bmcg3_sat_solver* s)
{
    ((Gluco3::SimpSolver*)s)->sat_solver_start_new_round();
}

void bmcg3_sat_solver_mark_cone(bmcg3_sat_solver* s, int var)
{
    ((Gluco3::SimpSolver*)s)->sat_solver_mark_cone(var);
}

void bmcg3_sat_solver_prelocate( bmcg3_sat_solver * s, int var_num ){
    ((Gluco3::SimpSolver*)s)->prelocate(var_num);
}

ABC_NAMESPACE_IMPL_END
