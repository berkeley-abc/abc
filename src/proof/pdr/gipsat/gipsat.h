/**************************************************************************************************
GipSAT -- C port of the GipSAT solver from the rIC3 model checker (https://github.com/gipsyh/rIC3),
ported from rIC3 v1.5.2-60-g4a97bec, src/gipsat/.
Copyright (C) 2023 - Present, Yuheng Su <gipsyh.icu@gmail.com>. All rights reserved.
Ported to C for ABC by Wish, 2026.

rIC3 is distributed under the GNU General Public License v3. This port is distributed as part of
ABC under the ABC license (see copyright.txt in the ABC root) with the explicit permission of the
rIC3 author.
**************************************************************************************************/

#ifndef ABC__proof__pdr__gipsat_h
#define ABC__proof__pdr__gipsat_h

#include "aig/saig/saig.h"
#include "sat/cnf/cnf.h"
#include "misc/vec/vec.h"

ABC_NAMESPACE_HEADER_START

////////////////////////////////////////////////////////////////////////
///                      BASIC TYPES                                 ///
////////////////////////////////////////////////////////////////////////

// Lbool values (var assignment); lit value = pValue[var] ^ compl(lit)
#define GIP_FALSE   0
#define GIP_TRUE    1
#define GIP_NONE    2

// clause reference: offset into the arena; GIP_CREF_NONE = no clause
#define GIP_CREF_NONE  (0x7FFFFFFF)

// solve results (match ABC usage: 1 = SAT, 0 = UNSAT, -1 = undecided)
#define GIP_SAT      1
#define GIP_UNSAT    0
#define GIP_UNDEF   (-1)

// clause kinds
#define GIP_CLA_TRANS      0
#define GIP_CLA_LEMMA      1
#define GIP_CLA_LEARNT     2
#define GIP_CLA_TEMPORARY  3

static inline int Gip_Lit( int Var, int fCompl )  { return 2*Var + (fCompl != 0);  }
static inline int Gip_LitVar( int Lit )           { return Lit >> 1;               }
static inline int Gip_LitCompl( int Lit )         { return Lit & 1;                }
static inline int Gip_LitNot( int Lit )           { return Lit ^ 1;                }

////////////////////////////////////////////////////////////////////////
///                      SMALL CONTAINERS                            ///
////////////////////////////////////////////////////////////////////////

typedef struct Gip_Wat_t_
{
    int          clause;      // CRef
    int          blocker;     // Lit
} Gip_Wat_t;

// per-literal watcher list
typedef struct Gip_WVec_t_
{
    Gip_Wat_t *  pArray;
    int          nSize;
    int          nCap;
} Gip_WVec_t;

// insertion-ordered var set with membership flags
typedef struct Gip_VarSet_t_
{
    Vec_Int_t *  vSet;
    char *       pHas;        // indexed by var
} Gip_VarSet_t;

typedef struct Gip_LitSet_t_
{
    Vec_Int_t *  vSet;
    char *       pHas;        // indexed by lit
} Gip_LitSet_t;

typedef struct Gip_Domain_t_
{
    Gip_VarSet_t Set;
    int          nFixed;
} Gip_Domain_t;

////////////////////////////////////////////////////////////////////////
///                      CLAUSE DATABASE                             ///
////////////////////////////////////////////////////////////////////////

// arena allocator; one clause = [header][lits...][act(f32) if learnt]
// header bits: 0 trans, 1 learnt, 2 reloced, 3 marked, 4 removed, 5..31 len
typedef struct Gip_Alloc_t_
{
    unsigned *   pData;
    unsigned     nSize;       // words used
    unsigned     nCap;        // words allocated
    unsigned     nWasted;     // words freed
} Gip_Alloc_t;

typedef struct Gip_Cdb_t_
{
    Gip_Alloc_t  Alloc;
    Vec_Int_t *  vTrans;      // CRefs of transition clauses
    Vec_Int_t *  vLemmas;     // CRefs of lemma clauses
    Vec_Int_t *  vLearnt;     // CRefs of learnt clauses
    Vec_Int_t *  vTemp;       // CRefs of temporary clauses
    float        actInc;      // clause activity increment (init 1.0)
} Gip_Cdb_t;

////////////////////////////////////////////////////////////////////////
///                      VSIDS                                       ///
////////////////////////////////////////////////////////////////////////

// binary max-heap keyed by activity
typedef struct Gip_Heap_t_
{
    Vec_Int_t *  vHeap;       // vars
    int *        pPos;        // var -> index in vHeap, -1 if absent
} Gip_Heap_t;

// activity values + log-scale bucket table
typedef struct Gip_Act_t_
{
    double *     pAct;        // per var
    double       actInc;      // init 1.0
    Gip_Heap_t   BktHeap;     // heap of all ever-bumped vars, ordered by act
    Vec_Int_t *  vBktTable;   // bucket_table (init: one entry 0)
} Gip_Act_t;

typedef struct Gip_Bucket_t_
{
    Vec_Ptr_t *  vBuckets;    // of Vec_Int_t* (bucket idx -> stack of vars)
    char *       pInBucket;   // per var
    int          head;
} Gip_Bucket_t;

typedef struct Gip_Vsids_t_
{
    Gip_Act_t    Act;
    Gip_Heap_t   Heap;        // exact mode
    Gip_Bucket_t Bucket;      // approximate mode
    int          fEnableBucket; // default 1
    int          nVarsAlloc;  // for activity rescaling
} Gip_Vsids_t;

////////////////////////////////////////////////////////////////////////
///                      STATIC CONTEXT (shared by all frames)       ///
////////////////////////////////////////////////////////////////////////

// Built once from the static CNF of the entire AIG. Cnf_ManWriteCnfOther
// emits literals as 2*ObjId(+1), so solver var == Aig object id and
// nVars == Aig_ManObjNumMax. Never mutated.
#define Gip_ObjVar( pObj )  Aig_ObjId(pObj)
typedef struct Gip_Ctx_t_
{
    Aig_Man_t *  pAig;        // not owned
    Cnf_Dat_t *  pCnf;        // owned by this ctx
    int          nVars;       // pCnf->nVars
    int          varConst;    // var of Aig const1
    // dep table in CSR form: dep(v) = pDepData[pDepOffset[v] .. pDepOffset[v+1])
    int *        pDepOffset;  // size nVars+1
    int *        pDepData;
    int          nDepData;
} Gip_Ctx_t;

////////////////////////////////////////////////////////////////////////
///                      SOLVER                                      ///
////////////////////////////////////////////////////////////////////////

typedef struct Gip_Stats_t_
{
    ABC_INT64_T  nSolves;
    ABC_INT64_T  nConflicts;
    ABC_INT64_T  nDecisions;
    ABC_INT64_T  nPropagations;
    ABC_INT64_T  nSubsume;
    ABC_INT64_T  nSelfSubsume;
    abctime      timeSolve;
    abctime      timeSimplify;   // inside timeSolve: full simplify passes
    abctime      timeCleanL;     // inside timeSolve: CleanLearnt sort+rebuild
} Gip_Stats_t;

typedef struct Gip_Solver_t_
{
    Gip_Ctx_t *  pCtx;            // shared, read-only
    // variable space: vars 0..nVars-1 are CNF vars; constrainAct == nVars;
    // all per-var arrays are sized nVarsAlloc >= nVars+1
    int          nVars;
    int          nVarsAlloc;
    int          constrainAct;
    // core CDCL state
    Gip_Cdb_t    Cdb;
    Gip_WVec_t * pWatchers;       // per lit (2*nVarsAlloc)
    char *       pValue;          // per var: GIP_FALSE/TRUE/NONE
    Vec_Int_t *  vTrail;          // lits
    Vec_Int_t *  vPosInTrail;     // trail start index per decision level
    unsigned *   pLevel;          // per var
    int *        pReason;         // per var: CRef
    int          nPropagated;
    Gip_Vsids_t  Vsids;
    char *       pPhase;          // per var: saved phase (Lbool)
    // analyze
    char *       pMark;           // per var: 0 unseen, 1 seen, 2 removable, 3 failed
    Vec_Int_t *  vClear;          // lits to clear
    Vec_Int_t *  vAnaStack;       // scratch for lit_redundant (pairs)
    Vec_Int_t *  vLearntCls;      // scratch learnt clause
    // unsat core
    Gip_LitSet_t UnsatCore;
    // domain
    Gip_Domain_t Domain;
    int          fTempDomain;
    int          fPreparedVsids;
    // simplify state
    int          nLastNumAssign;
    ABC_INT64_T  nLastSimplify;
    int          nLastNumLemma;   // init 1000
    // status
    int          fTrivialUnsat;
    // limits for the current solve
    ABC_INT64_T  nConfLimit;      // 0 = none; per solve call
    ABC_INT64_T  nConfCounted;    // Stats.nConflicts at solve start
    abctime      TimeLimit;       // 0 = none; absolute deadline
    int          fCanceled;       // set when limit hit
    // scratch
    Vec_Int_t *  vSimpCls;        // simplify_clause output
    Vec_Int_t *  vSeeds;          // domain seeds scratch
    Vec_Int_t *  vAssump;         // current assumption (with constrainAct lit)
    Gip_Stats_t  Stats;
} Gip_Solver_t;

////////////////////////////////////////////////////////////////////////
///                      API                                         ///
////////////////////////////////////////////////////////////////////////

// gipMan.c
extern Gip_Ctx_t *    Gip_CtxCreate( Aig_Man_t * pAig, Cnf_Man_t * pCnfMan );
extern void           Gip_CtxFree( Gip_Ctx_t * p );

// gipMain.c
extern Gip_Solver_t * Gip_SolverNew( Gip_Ctx_t * pCtx );
extern void           Gip_SolverFree( Gip_Solver_t * p );
// add a lemma clause: resets the solver, extends the fixed domain
extern void           Gip_SolverAddLemma( Gip_Solver_t * p, int * pLits, int nLits );
// full query entry. ppCstCls/pnCstLits: nCst constraint clauses; pass
// nCst = 0 for none. nRestartLimit < 0 means no restart limit.
extern int            Gip_SolverSolve( Gip_Solver_t * p,
                                       int * pAssump, int nAssump,
                                       int ** ppCstCls, int * pnCstLits, int nCst,
                                       int nRestartLimit );
extern int            Gip_SolverVarValue( Gip_Solver_t * p, int Var );   // GIP_NONE -> 0
extern int            Gip_SolverUnsatHas( Gip_Solver_t * p, int Lit );
// MIC temporary domain
extern void           Gip_SolverSetDomain( Gip_Solver_t * p, int * pLits, int nLits );
extern void           Gip_SolverUnsetDomain( Gip_Solver_t * p );
// internals shared between gip*.c
extern void           Gip_SolverReset( Gip_Solver_t * p );
extern int            Gip_SolverAddClauseInner( Gip_Solver_t * p, int * pLits, int nLits, int Kind );

// gipCdb.c
extern void           Gip_CdbInit( Gip_Cdb_t * p );
extern void           Gip_CdbFree( Gip_Cdb_t * p );
extern void           Gip_CdbBump( Gip_Cdb_t * p, int Cref );
extern void           Gip_CdbDecay( Gip_Cdb_t * p );
extern int            Gip_SolverAttachClause( Gip_Solver_t * p, int * pLits, int nLits, int Kind );
extern void           Gip_SolverDetachClause( Gip_Solver_t * p, int Cref );
extern void           Gip_SolverCleanTemporary( Gip_Solver_t * p );
extern void           Gip_SolverCleanLearnt( Gip_Solver_t * p, int fFull );
extern void           Gip_SolverStrengthenClause( Gip_Solver_t * p, int Cref, int Lit );
extern void           Gip_SolverGarbageCollect( Gip_Solver_t * p );

// clause accessors (arena layout)
static inline int        Gip_ClaLen( Gip_Alloc_t * p, int Cref )          { return (int)(p->pData[Cref] >> 5);            }
static inline int        Gip_ClaIsTrans( Gip_Alloc_t * p, int Cref )      { return (int)(p->pData[Cref] & 1);             }
static inline int        Gip_ClaIsLearnt( Gip_Alloc_t * p, int Cref )     { return (int)((p->pData[Cref] >> 1) & 1);      }
static inline int        Gip_ClaIsReloced( Gip_Alloc_t * p, int Cref )    { return (int)((p->pData[Cref] >> 2) & 1);      }
static inline int        Gip_ClaIsRemoved( Gip_Alloc_t * p, int Cref )    { return (int)((p->pData[Cref] >> 4) & 1);      }
static inline void       Gip_ClaSetRemoved( Gip_Alloc_t * p, int Cref )   { p->pData[Cref] |= (1u << 4);                  }
static inline void       Gip_ClaSetReloced( Gip_Alloc_t * p, int Cref )   { p->pData[Cref] |= (1u << 2);                  }
static inline void       Gip_ClaSetLen( Gip_Alloc_t * p, int Cref, int n ){ p->pData[Cref] = (p->pData[Cref] & 31u) | (((unsigned)n) << 5); }
static inline int *      Gip_ClaLits( Gip_Alloc_t * p, int Cref )         { return (int *)(p->pData + Cref + 1);          }
static inline float      Gip_ClaAct( Gip_Alloc_t * p, int Cref )          { float f; memcpy( &f, p->pData + Cref + 1 + Gip_ClaLen(p, Cref), 4 ); return f; }
static inline void       Gip_ClaSetAct( Gip_Alloc_t * p, int Cref, float f ) { memcpy( p->pData + Cref + 1 + Gip_ClaLen(p, Cref), &f, 4 ); }

// gipProp.c
extern void           Gip_WatchersAttach( Gip_Solver_t * p, int Cref );
extern void           Gip_WatchersDetach( Gip_Solver_t * p, int Cref );
extern int            Gip_SolverPropagate( Gip_Solver_t * p );        // returns conflict CRef or GIP_CREF_NONE

// gipAnalyze.c
extern int            Gip_SolverAnalyze( Gip_Solver_t * p, int Conflict, Vec_Int_t * vLearnt ); // returns backtrack level; learnt in vLearnt
extern void           Gip_SolverAnalyzeUnsatCore( Gip_Solver_t * p, int Lit );

// gipSearch.c
extern void           Gip_SolverAssign( Gip_Solver_t * p, int Lit, int Reason );
extern void           Gip_SolverNewLevel( Gip_Solver_t * p );
extern void           Gip_SolverBacktrack( Gip_Solver_t * p, int Level, int fVsids );
extern int            Gip_SolverSearchWithRestart( Gip_Solver_t * p, int * pAssump, int nAssump, int nRestartLimit );

// gipVsids.c
extern void           Gip_HeapClear( Gip_Heap_t * p );
extern void           Gip_VsidsInit( Gip_Vsids_t * p, int nVarsAlloc );
extern void           Gip_VsidsFree( Gip_Vsids_t * p );
extern void           Gip_VsidsPush( Gip_Vsids_t * p, int Var );
extern void           Gip_VsidsBump( Gip_Vsids_t * p, int Var );
extern void           Gip_VsidsDecay( Gip_Vsids_t * p );
extern void           Gip_BucketClear( Gip_Bucket_t * p );
extern int            Gip_SolverDecide( Gip_Solver_t * p );

// gipDomain.c
extern void           Gip_DomainInit( Gip_Domain_t * p, int nVarsAlloc, int varConst );
extern void           Gip_DomainFree( Gip_Domain_t * p );
extern void           Gip_DomainReset( Gip_Domain_t * p );
extern int            Gip_DomainHas( Gip_Domain_t * p, int Var );
extern void           Gip_DomainInsert( Gip_Domain_t * p, int Var );
extern void           Gip_DomainEnableLocal( Gip_Solver_t * p, Vec_Int_t * vSeeds ); // BFS closure over ctx dep
extern void           Gip_SolverAddDomain( Gip_Solver_t * p, int Var, int fDeps );   // permanent (fixed prefix)
extern void           Gip_SolverPrepareVsids( Gip_Solver_t * p );

// gipSimp.c
extern void           Gip_SolverSimplify( Gip_Solver_t * p );

// var/lit-set helpers
extern void           Gip_VarSetInit( Gip_VarSet_t * p, int nVarsAlloc );
extern void           Gip_VarSetFree( Gip_VarSet_t * p );
extern void           Gip_LitSetInit( Gip_LitSet_t * p, int nVarsAlloc );
extern void           Gip_LitSetFree( Gip_LitSet_t * p );
static inline int     Gip_VarSetHas( Gip_VarSet_t * p, int Var )  { return p->pHas[Var];  }
static inline void    Gip_VarSetInsert( Gip_VarSet_t * p, int Var ) { if ( !p->pHas[Var] ) { p->pHas[Var] = 1; Vec_IntPush(p->vSet, Var); } }
static inline int     Gip_LitSetHas( Gip_LitSet_t * p, int Lit )  { return p->pHas[Lit];  }
static inline void    Gip_LitSetInsert( Gip_LitSet_t * p, int Lit ) { if ( !p->pHas[Lit] ) { p->pHas[Lit] = 1; Vec_IntPush(p->vSet, Lit); } }
static inline void    Gip_LitSetClear( Gip_LitSet_t * p ) { int i, l; Vec_IntForEachEntry(p->vSet, l, i) p->pHas[l] = 0; Vec_IntClear(p->vSet); }

// solver small helpers
static inline int     Gip_SolverLitValue( Gip_Solver_t * p, int Lit )
{
    char v = p->pValue[Gip_LitVar(Lit)];
    return v == GIP_NONE ? GIP_NONE : (v ^ Gip_LitCompl(Lit));
}
static inline void    Gip_SolverSetLit( Gip_Solver_t * p, int Lit )   { p->pValue[Gip_LitVar(Lit)] = (char)(1 ^ Gip_LitCompl(Lit)); }
static inline void    Gip_SolverSetNone( Gip_Solver_t * p, int Var )  { p->pValue[Var] = GIP_NONE; }
static inline int     Gip_SolverLevelOf( Gip_Solver_t * p )           { return Vec_IntSize(p->vPosInTrail); }

ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
