/**************************************************************************************************
MiniSat -- Copyright (c) 2005, Niklas Sorensson
http://www.cs.chalmers.se/Cs/Research/FormalMethods/MiniSat/

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/
// Modified to compile with MS Visual Studio 6.0 by Alan Mishchenko

#ifndef solver_h
#define solver_h

#ifdef __cplusplus
extern "C" {
#endif

#ifdef _WIN32
#define inline __inline // compatible with MS VS 6.0
#endif

#include "solver_vec.h"
#include "asatmem.h"

//=================================================================================================
// Simple types:

//typedef int  bool;
#ifndef __cplusplus
#ifndef bool
#define bool int
#endif
#endif

typedef int                lit;
typedef char               lbool;

#ifdef _WIN32
typedef signed __int64     sint64;   // compatible with MS VS 6.0
#else
typedef long long          sint64;
#endif

static const int   var_Undef = -1;
static const lit   lit_Undef = -2;

static const lbool l_Undef   =  0;
static const lbool l_True    =  1;
static const lbool l_False   = -1;

static inline lit neg       (lit l)        { return l ^ 1; }
static inline lit toLit     (int v)        { return v + v; }
static inline lit toLitCond (int v, int c) { return v + v + (int)(c != 0); }

//=================================================================================================
// Public interface:

typedef struct Asat_JMan_t_  Asat_JMan_t;

struct solver_t;
typedef struct solver_t solver;

extern solver* solver_new(void);
extern void    solver_delete(solver* s);

extern bool    solver_addclause(solver* s, lit* begin, lit* end);
extern bool    solver_simplify(solver* s);
extern int     solver_solve(solver* s, lit* begin, lit* end, sint64 nConfLimit, sint64 nInsLimit );
extern int *   solver_get_model( solver * p, int * pVars, int nVars );

extern int     solver_nvars(solver* s);
extern int     solver_nclauses(solver* s);


// additional procedures
extern void    Asat_SolverWriteDimacs( solver * pSat, char * pFileName,
                                       lit* assumptionsBegin, lit* assumptionsEnd,
                                       int incrementVars);
extern void    Asat_SatPrintStats( FILE * pFile, solver * p );
extern void    Asat_SolverSetPrefVars( solver * s, int * pPrefVars, int nPrefVars );

// J-frontier support
extern Asat_JMan_t * Asat_JManStart( solver * pSat, void * vCircuit );
extern void          Asat_JManStop(  solver * pSat );


struct stats_t
{
    sint64   starts, decisions, propagations, inspects, conflicts;
    sint64   clauses, clauses_literals, learnts, learnts_literals, max_literals, tot_literals;
};
typedef struct stats_t stats;

//=================================================================================================
// Solver representation:

struct clause_t;
typedef struct clause_t clause;

struct solver_t
{
    int      size;          // nof variables
    int      cap;           // size of varmaps
    int      qhead;         // Head index of queue.
    int      qtail;         // Tail index of queue.

    // clauses
    vec      clauses;       // List of problem constraints. (contains: clause*)
    vec      learnts;       // List of learnt clauses. (contains: clause*)

    // activities
    double   var_inc;       // Amount to bump next variable with.
    double   var_decay;     // INVERSE decay factor for variable activity: stores 1/decay. 
    float    cla_inc;       // Amount to bump next clause with.
    float    cla_decay;     // INVERSE decay factor for clause activity: stores 1/decay.

    vec*     wlists;        // 
    double*  activity;      // A heuristic measurement of the activity of a variable.
    lbool*   assigns;       // Current values of variables.
    int*     orderpos;      // Index in variable order.
    clause** reasons;       //
    int*     levels;        //
    lit*     trail;

    clause*  binary;        // A temporary binary clause
    lbool*   tags;          //
    veci     tagged;        // (contains: var)
    veci     stack;         // (contains: var)

    veci     order;         // Variable order. (heap) (contains: var)
    veci     trail_lim;     // Separator indices for different decision levels in 'trail'. (contains: int)
    veci     model;         // If problem is solved, this vector contains the model (contains: lbool).

    int      root_level;    // Level of first proper decision.
    int      simpdb_assigns;// Number of top-level assignments at last 'simplifyDB()'.
    int      simpdb_props;  // Number of propagations before next 'simplifyDB()'.
    double   random_seed;
    double   progress_estimate;
    int      verbosity;     // Verbosity level. 0=silent, 1=some progress report, 2=everything

    sint64   nConfLimit;    // external limit on the number of conflicts
    sint64   nInsLimit;     // external limit on the number of implications

    // the memory manager
    Asat_MmStep_t *     pMem;

    // J-frontier
    Asat_JMan_t *       pJMan;

    // for making decisions on some variables first
    int      nPrefDecNum;
    int *    pPrefVars;
    int      nPrefVars;

    // solver statistics
    stats    solver_stats;
    int      timeTotal;
    int      timeSelect;
    int      timeUpdate;
};
 
#ifdef __cplusplus
}
#endif

#endif
