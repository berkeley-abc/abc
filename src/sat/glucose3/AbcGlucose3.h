/**CFile****************************************************************

  FileName    [AbcGlucose3.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT solver Glucose 3.0 by Gilles Audemard and Laurent Simon.]

  Synopsis    [Interface to Glucose.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: AbcGlucose3.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC_SAT_GLUCOSE3_H_
#define ABC_SAT_GLUCOSE3_H_

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "misc/util/abc_global.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

#define GLUCOSE3_UNSAT -1
#define GLUCOSE3_SAT    1
#define GLUCOSE3_UNDEC  0


ABC_NAMESPACE_HEADER_START

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef void bmcg3_sat_solver;

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

extern bmcg3_sat_solver * bmcg3_sat_solver_start();
extern void              bmcg3_sat_solver_stop( bmcg3_sat_solver* s );
extern void              bmcg3_sat_solver_reset( bmcg3_sat_solver* s );
extern int               bmcg3_sat_solver_addclause( bmcg3_sat_solver* s, int * plits, int nlits );
extern void              bmcg3_sat_solver_setcallback( bmcg3_sat_solver* s, void * pman, int(*pfunc)(void*, int, int*) );
extern int               bmcg3_sat_solver_solve( bmcg3_sat_solver* s, int * plits, int nlits );
extern int               bmcg3_sat_solver_final( bmcg3_sat_solver* s, int ** ppArray );
extern int               bmcg3_sat_solver_addvar( bmcg3_sat_solver* s );
extern void              bmcg3_sat_solver_set_nvars( bmcg3_sat_solver* s, int nvars );
extern int               bmcg3_sat_solver_eliminate( bmcg3_sat_solver* s, int turn_off_elim );
extern int               bmcg3_sat_solver_var_is_elim( bmcg3_sat_solver* s, int v );
extern void              bmcg3_sat_solver_var_set_frozen( bmcg3_sat_solver* s, int v, int freeze );
extern int               bmcg3_sat_solver_elim_varnum(bmcg3_sat_solver* s);
extern int *             bmcg3_sat_solver_read_cex( bmcg3_sat_solver* s );
extern int               bmcg3_sat_solver_read_cex_varvalue( bmcg3_sat_solver* s, int );
extern int               bmcg3_sat_solver_read_unit( bmcg3_sat_solver * s, int lit );
extern void              bmcg3_sat_solver_set_stop( bmcg3_sat_solver* s, int * pstop );
extern void              bmcg3_sat_solver_markapprox(bmcg3_sat_solver* s, int v0, int v1, int nlim);
extern abctime           bmcg3_sat_solver_set_runtime_limit( bmcg3_sat_solver* s, abctime Limit );
extern void              bmcg3_sat_solver_set_conflict_budget( bmcg3_sat_solver* s, int Limit );
extern int               bmcg3_sat_solver_varnum( bmcg3_sat_solver* s );
extern int               bmcg3_sat_solver_clausenum( bmcg3_sat_solver* s );
extern int               bmcg3_sat_solver_learntnum( bmcg3_sat_solver* s );
extern int               bmcg3_sat_solver_conflictnum( bmcg3_sat_solver* s );
extern int               bmcg3_sat_solver_minimize_assumptions( bmcg3_sat_solver * s, int * plits, int nlits, int pivot );
extern int               bmcg3_sat_solver_add_and( bmcg3_sat_solver * s, int iVar, int iVar0, int iVar1, int fCompl0, int fCompl1, int fCompl );
extern int               bmcg3_sat_solver_add_xor( bmcg3_sat_solver * s, int iVarA, int iVarB, int iVarC, int fCompl );
extern int               bmcg3_sat_solver_jftr( bmcg3_sat_solver * s );
extern void              bmcg3_sat_solver_set_jftr( bmcg3_sat_solver * s, int jftr );
extern void              bmcg3_sat_solver_set_var_fanin_lit( bmcg3_sat_solver * s, int var, int lit0, int lit1 );
extern void              bmcg3_sat_solver_select_cone( bmcg3_sat_solver * s, int v0, int v1 );
// Use either cone-selection interface, without mixing them until reset.
extern void              bmcg3_sat_solver_select_cones( bmcg3_sat_solver * s, const int * roots, int count );
// Disable only when every permanent gate unit is a proved circuit consequence.
extern void              bmcg3_sat_solver_set_unit_justification( bmcg3_sat_solver * s, int enable );
extern void              bmcg3_sat_solver_start_new_round( bmcg3_sat_solver * s );
extern void              bmcg3_sat_solver_mark_cone( bmcg3_sat_solver * s, int var );
extern void              bmcg3_sat_solver_prelocate( bmcg3_sat_solver * s, int var_num );


ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
