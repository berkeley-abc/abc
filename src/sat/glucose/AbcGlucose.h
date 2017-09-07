/**CFile****************************************************************

  FileName    [AbcGlucose.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT solver Glucose 3.0.]

  Synopsis    [Interface to Glucose.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 6, 2017.]

  Revision    [$Id: AbcGlucose.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC_SAT_GLUCOSE_H_
#define ABC_SAT_GLUCOSE_H_

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "aig/gia/gia.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_HEADER_START

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Glucose_Pars_ Glucose_Pars;
struct Glucose_Pars_ {
    int pre;     // preprocessing
    int verb;    // verbosity
    int cust;    // customizable
    int nConfls; // conflict limit (0 = no limit)
};

static inline Glucose_Pars Glucose_CreatePars(int p, int v, int c, int nConfls)
{
    Glucose_Pars pars;
    pars.pre     = p;
    pars.verb    = v;
    pars.cust    = c;
    pars.nConfls = nConfls;
    return pars;
}

typedef void bmcg_sat_solver;

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

extern bmcg_sat_solver * bmcg_sat_solver_start();
extern void              bmcg_sat_solver_stop( bmcg_sat_solver* s );
extern int               bmcg_sat_solver_addclause( bmcg_sat_solver* s, int * plits, int nlits );
extern void              bmcg_sat_solver_setcallback( bmcg_sat_solver* s, void * pman, int(*pfunc)(void*, int, int*) );
extern int               bmcg_sat_solver_solve( bmcg_sat_solver* s, int * plits, int nlits );
extern int               bmcg_sat_solver_addvar( bmcg_sat_solver* s );
extern int               bmcg_sat_solver_read_cex_varvalue( bmcg_sat_solver* s, int );
extern void              bmcg_sat_solver_setstop( bmcg_sat_solver* s, int * );
extern abctime           bmcg_sat_solver_set_runtime_limit(bmcg_sat_solver* s, abctime Limit);
extern void              bmcg_sat_solver_set_conflict_budget(bmcg_sat_solver* s, int Limit);
extern int               bmcg_sat_solver_varnum(bmcg_sat_solver* s);
extern int               bmcg_sat_solver_clausenum(bmcg_sat_solver* s);
extern int               bmcg_sat_solver_learntnum(bmcg_sat_solver* s);
extern int               bmcg_sat_solver_conflictnum(bmcg_sat_solver* s);

extern void              Glucose_SolveCnf( char * pFilename, Glucose_Pars * pPars );
extern int               Glucose_SolveAig( Gia_Man_t * p, Glucose_Pars * pPars );

ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

