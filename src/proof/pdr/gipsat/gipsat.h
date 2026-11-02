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

// arena allocator; one clause = [header][lits...][act(f32) if learnt][tag]
// the tag records the frames of the lemmas a clause depends on (see Gip_SolverClaFrame):
// (frame << 1) for a frame value, or (lemma id << 1 | 1) for a lemma clause whose current
// frame is read from the table set by Gip_SolverSetLemFrames; GIP_FRAME_INF = no dependency
#define GIP_FRAME_INF  0x3fffffff
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
    ABC_INT64_T  nCleanL;        // CleanLearnt passes
    ABC_INT64_T  nCleanLNone;    // CleanLearnt passes that removed no clause
    ABC_INT64_T  nCleanLDel;     // learnt clauses removed by CleanLearnt
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
    char *       pLitVal;         // per lit: GIP_FALSE/TRUE/NONE (mirror of pValue for branch-free lookups)
    Vec_Int_t *  vTrail;          // lits
    Vec_Int_t *  vPosInTrail;     // trail start index per decision level
    unsigned *   pLevel;          // per var
    int *        pReason;         // per var: CRef
    int *        pTag0;           // per var: frame tag of a level-0 assignment (the lowest frame it depends on)
    Vec_Int_t *  vLemFrame;       // lemma id -> current frame (owned by the caller), or NULL
    int          iCoreFrame;      // after GIP_UNSAT: the lowest frame used by the proof (GIP_FRAME_INF = none)
    int          iAnaFrame;       // scratch: the lowest frame used by the current conflict analysis
    int          iTrivialFrame;   // frame of a permanent (level-0) contradiction
    int          nPropagated;
    Gip_Vsids_t  Vsids;
    char *       pPhase;          // per var: saved phase (Lbool)
    // analyze
    char *       pMark;           // per var: 0 unseen, 1 seen, 2 removable, 3 failed
    int *        pRemFrame;       // per var marked removable: the lowest frame used to derive it
    Vec_Int_t *  vClear;          // lits to clear
    Vec_Int_t *  vAnaStack;       // scratch for lit_redundant (pairs)
    Vec_Int_t *  vLearntCls;      // scratch learnt clause
    // unsat core
    Gip_LitSet_t UnsatCore;
    // domain
    Gip_Domain_t Domain;
    int          fTempDomain;
    int          fPreparedVsids;
    int          fFastClean;      // learnt-clause cleaning by selection (unordered) instead of a full sort
    int          fCleanSkip;      // skip learnt-clause cleanings that would remove (almost) nothing (the two fields below)
    int          nCleanWait;      // the cleaning in the search waits until the learnt clauses exceed this number
    ABC_INT64_T  nCleanIdle;      // conflict count at the last cleaning that removed nothing (-1 = none)
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
    ABC_INT64_T  nTimeCheck;      // propagation count at which the deadline is checked next
    ABC_INT64_T  nPropLimit;      // 0 = none; absolute propagation count at which the solve is canceled
    int          fCanceled;       // set when limit hit
    // scratch
    Vec_Int_t *  vSimpCls;        // simplify_clause output
    Vec_Int_t *  vSeeds;          // domain seeds scratch
    Vec_Int_t *  vAssump;         // current assumption (with constrainAct lit)
    Gip_Stats_t  Stats;
} Gip_Solver_t;

// the deadline is polled every GIP_TIME_CHECK propagations, independently of the conflicts
#define GIP_TIME_CHECK (1 << 16)
static inline int Gip_SolverTimedOut( Gip_Solver_t * p )
{
    p->nTimeCheck = p->Stats.nPropagations + GIP_TIME_CHECK;
    return Abc_Clock() > p->TimeLimit;
}

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
extern void           Gip_SolverAddLemmaId( Gip_Solver_t * p, int * pLits, int nLits, int Id );
extern void           Gip_SolverSetLemFrames( Gip_Solver_t * p, Vec_Int_t * vLemFrame );
extern int            Gip_SolverAddClauseTag( Gip_Solver_t * p, int * pLits, int nLits, int Kind, unsigned TagWord );
extern int            Gip_SolverAttachClauseTag( Gip_Solver_t * p, int * pLits, int nLits, int Kind, unsigned TagWord );
extern int            Gip_SolverConflictFrame( Gip_Solver_t * p, int Cref );
extern void           Gip_SolverLowerTag( Gip_Solver_t * p, int Cref, int Frame );
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
static inline unsigned   Gip_ClaTagWord( Gip_Alloc_t * p, int Cref )      { return p->pData[Cref + 1 + Gip_ClaLen(p, Cref) + Gip_ClaIsLearnt(p, Cref)]; }
static inline void       Gip_ClaSetTagWord( Gip_Alloc_t * p, int Cref, unsigned w ) { p->pData[Cref + 1 + Gip_ClaLen(p, Cref) + Gip_ClaIsLearnt(p, Cref)] = w; }
static inline void       Gip_ClaSetAct( Gip_Alloc_t * p, int Cref, float f ) { memcpy( p->pData + Cref + 1 + Gip_ClaLen(p, Cref), &f, 4 ); }

// gipProp.c
extern void           Gip_WatchersAttach( Gip_Solver_t * p, int Cref );
extern void           Gip_WatchersDetach( Gip_Solver_t * p, int Cref );
extern int            Gip_SolverPropagate( Gip_Solver_t * p );        // returns conflict CRef or GIP_CREF_NONE
// tries to unassign a decision-level var while keeping all its watched clauses satisfied;
// returns 1 if the var is now unassigned (value was not needed), 0 if it had to be restored
extern int            Gip_SolverFlipToNone( Gip_Solver_t * p, int Var );

// gipAnalyze.c
extern int            Gip_SolverAnalyze( Gip_Solver_t * p, int Conflict, Vec_Int_t * vLearnt ); // returns backtrack level; learnt in vLearnt
extern void           Gip_SolverAnalyzeUnsatCore( Gip_Solver_t * p, int Lit );

// gipSearch.c
extern void           Gip_SolverNewLevel( Gip_Solver_t * p );
extern void           Gip_SolverBacktrack( Gip_Solver_t * p, int Level, int fVsids );
extern int            Gip_SolverSearchWithRestart( Gip_Solver_t * p, int * pAssump, int nAssump, int nRestartLimit );

// gipVsids.c
extern void           Gip_HeapClear( Gip_Heap_t * p );
extern void           Gip_VsidsInit( Gip_Vsids_t * p, int nVarsAlloc );
extern void           Gip_VsidsFree( Gip_Vsids_t * p );
extern void           Gip_BucketClear( Gip_Bucket_t * p );

// gipDomain.c
extern void           Gip_DomainInit( Gip_Domain_t * p, int nVarsAlloc, int varConst );
extern void           Gip_DomainFree( Gip_Domain_t * p );
extern void           Gip_DomainReset( Gip_Domain_t * p );
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
static inline int     Gip_SolverLitValue( Gip_Solver_t * p, int Lit ) { return p->pLitVal[Lit]; }
static inline void    Gip_SolverSetLit( Gip_Solver_t * p, int Lit )
{
    p->pValue[Gip_LitVar(Lit)] = (char)(1 ^ Gip_LitCompl(Lit));
    p->pLitVal[Lit] = GIP_TRUE;
    p->pLitVal[Gip_LitNot(Lit)] = GIP_FALSE;
}
static inline void    Gip_SolverSetNone( Gip_Solver_t * p, int Var )
{
    p->pValue[Var] = GIP_NONE;
    p->pLitVal[2*Var] = p->pLitVal[2*Var+1] = GIP_NONE;
}
static inline int     Gip_SolverLevelOf( Gip_Solver_t * p )           { return Vec_IntSize(p->vPosInTrail); }

////////////////////////////////////////////////////////////////////////
///                      INLINED HOT PATHS                           ///
////////////////////////////////////////////////////////////////////////

// domain membership
static inline int     Gip_DomainHas( Gip_Domain_t * p, int Var )           { return p->Set.pHas[Var];                     }
static inline void    Gip_DomainInsert( Gip_Domain_t * p, int Var )        { Gip_VarSetInsert( &p->Set, Var );            }

// frame tag of a clause (see the clause layout)
static inline int     Gip_SolverClaFrame( Gip_Solver_t * p, int Cref )
{
    unsigned w = Gip_ClaTagWord( &p->Cdb.Alloc, Cref );
    if ( w & 1 )
        return p->vLemFrame ? Vec_IntEntry( p->vLemFrame, (int)(w >> 1) ) : GIP_FRAME_INF;
    return (int)(w >> 1);
}
// assignment
static inline void    Gip_SolverAssign( Gip_Solver_t * p, int Lit, int Reason )
{
    int Var = Gip_LitVar( Lit );
    Vec_IntPush( p->vTrail, Lit );
    Gip_SolverSetLit( p, Lit );
    p->pReason[Var] = Reason;
    p->pLevel[Var] = (unsigned)Gip_SolverLevelOf( p );
}

// clause activity
static inline void    Gip_CdbDecay( Gip_Cdb_t * p )                        { p->actInc *= (float)(1.0 / 0.99);            }
static inline void    Gip_CdbBump( Gip_Cdb_t * p, int Cref )
{
    float act;
    if ( !Gip_ClaIsLearnt(&p->Alloc, Cref) )
        return;
    act = Gip_ClaAct( &p->Alloc, Cref ) + p->actInc;
    Gip_ClaSetAct( &p->Alloc, Cref, act );
    if ( act > (float)1e20 )
    {
        int i, l;
        Vec_IntForEachEntry( p->vLearnt, l, i )
            Gip_ClaSetAct( &p->Alloc, l, Gip_ClaAct(&p->Alloc, l) * (float)1e-20 );
        p->actInc *= (float)1e-20;
    }
}

// activity heap
static inline void    Gip_HeapUp( Gip_Heap_t * p, int Var, Gip_Act_t * pAct )
{
    int * pHeap = Vec_IntArray( p->vHeap );
    int idx = p->pPos[Var], pidx;
    if ( idx == -1 )
        return;
    while ( idx != 0 )
    {
        pidx = (idx - 1) >> 1;
        if ( pAct->pAct[pHeap[pidx]] >= pAct->pAct[Var] )
            break;
        pHeap[idx] = pHeap[pidx];
        p->pPos[pHeap[idx]] = idx;
        idx = pidx;
    }
    pHeap[idx] = Var;
    p->pPos[Var] = idx;
}
static inline void    Gip_HeapDown( Gip_Heap_t * p, int idx, Gip_Act_t * pAct )
{
    int * pHeap = Vec_IntArray( p->vHeap );
    int nSize = Vec_IntSize( p->vHeap );
    int v = pHeap[idx];
    while ( 1 )
    {
        int left = 2*idx + 1, right, child;
        if ( left >= nSize )
            break;
        right = left + 1;
        child = ( right < nSize && pAct->pAct[pHeap[right]] > pAct->pAct[pHeap[left]] ) ? right : left;
        if ( pAct->pAct[v] >= pAct->pAct[pHeap[child]] )
            break;
        pHeap[idx] = pHeap[child];
        p->pPos[pHeap[idx]] = idx;
        idx = child;
    }
    pHeap[idx] = v;
    p->pPos[v] = idx;
}
static inline void    Gip_HeapPush( Gip_Heap_t * p, int Var, Gip_Act_t * pAct )
{
    int idx;
    if ( p->pPos[Var] != -1 )
        return;
    idx = Vec_IntSize( p->vHeap );
    Vec_IntPush( p->vHeap, Var );
    p->pPos[Var] = idx;
    Gip_HeapUp( p, Var, pAct );
}
static inline int     Gip_HeapPop( Gip_Heap_t * p, Gip_Act_t * pAct )
{
    int * pHeap, value;
    if ( Vec_IntSize(p->vHeap) == 0 )
        return -1;
    pHeap = Vec_IntArray( p->vHeap );
    value = pHeap[0];
    pHeap[0] = pHeap[Vec_IntSize(p->vHeap) - 1];
    p->pPos[pHeap[0]] = 0;
    p->pPos[value] = -1;
    Vec_IntPop( p->vHeap );
    if ( Vec_IntSize(p->vHeap) > 1 )
        Gip_HeapDown( p, 0, pAct );
    return value;
}

// number of significant bits of a 64-bit value (0 -> 0)
static inline int     Gip_Bits64( word b )
{
    int n = 0;
    while ( b ) { n++; b >>= 1; }
    return n;
}
// bucket-table maintenance on first bump of a var: bucket_table[pos]
// approximates ceil(log2(pos+1)); one trailing entry (value = last + 1)
// serves vars that were never bumped
static inline void    Gip_ActCheck( Gip_Act_t * p, int Var )
{
    if ( p->BktHeap.pPos[Var] == -1 )
    {
        word b;
        int blog;
        Gip_HeapPush( &p->BktHeap, Var, p );
        b = (word)(Vec_IntSize( p->vBktTable ) - 1);
        blog = Gip_Bits64( b );
        Vec_IntWriteEntry( p->vBktTable, Vec_IntSize(p->vBktTable) - 1, blog );
        Vec_IntPush( p->vBktTable, blog + 1 );
    }
}
static inline int     Gip_ActBucketOf( Gip_Act_t * p, int Var )
{
    int pos = p->BktHeap.pPos[Var];
    if ( pos == -1 )
        return Vec_IntEntryLast( p->vBktTable );
    return Vec_IntEntry( p->vBktTable, pos );
}
static inline void    Gip_ActBump( Gip_Act_t * p, int Var, int nVarsAlloc )
{
    p->pAct[Var] += p->actInc;
    Gip_ActCheck( p, Var );
    Gip_HeapUp( &p->BktHeap, Var, p );
    if ( p->pAct[Var] > 1e100 )
    {
        int i;
        for ( i = 0; i < nVarsAlloc; i++ )
            p->pAct[i] *= 1e-100;
        p->actInc *= 1e-100;
    }
}

// approximate (bucket) decision order
static inline void    Gip_BucketEnsure( Gip_Bucket_t * p, int nBuckets )
{
    while ( Vec_PtrSize(p->vBuckets) < nBuckets )
        Vec_PtrPush( p->vBuckets, Vec_IntAlloc(16) );
}
static inline void    Gip_BucketPush( Gip_Bucket_t * p, int Var, Gip_Act_t * pAct )
{
    int bucket;
    if ( p->pInBucket[Var] )
        return;
    bucket = Gip_ActBucketOf( pAct, Var );
    if ( p->head > bucket )
        p->head = bucket;
    Gip_BucketEnsure( p, bucket + 1 );
    Vec_IntPush( (Vec_Int_t *)Vec_PtrEntry(p->vBuckets, bucket), Var );
    p->pInBucket[Var] = 1;
}
static inline int     Gip_BucketPop( Gip_Bucket_t * p )
{
    while ( p->head < Vec_PtrSize(p->vBuckets) )
    {
        Vec_Int_t * vB = (Vec_Int_t *)Vec_PtrEntry( p->vBuckets, p->head );
        if ( Vec_IntSize(vB) > 0 )
        {
            int Var = Vec_IntPop( vB );
            p->pInBucket[Var] = 0;
            return Var;
        }
        p->head++;
    }
    return -1;
}

// VSIDS
static inline void    Gip_VsidsPush( Gip_Vsids_t * p, int Var )
{
    if ( p->fEnableBucket )
        Gip_BucketPush( &p->Bucket, Var, &p->Act );
    else
        Gip_HeapPush( &p->Heap, Var, &p->Act );
}
static inline int     Gip_VsidsPop( Gip_Vsids_t * p )
{
    if ( p->fEnableBucket )
        return Gip_BucketPop( &p->Bucket );
    return Gip_HeapPop( &p->Heap, &p->Act );
}
static inline void    Gip_VsidsBump( Gip_Vsids_t * p, int Var )
{
    Gip_ActBump( &p->Act, Var, p->nVarsAlloc );
    if ( !p->fEnableBucket )
        Gip_HeapUp( &p->Heap, Var, &p->Act );
    Gip_BucketEnsure( &p->Bucket, Vec_IntEntryLast(p->Act.vBktTable) + 1 );
}
static inline void    Gip_VsidsDecay( Gip_Vsids_t * p )                    { p->Act.actInc *= 1.0 / 0.95;                 }

// picks and assigns the next decision literal; returns 0 if all domain vars are assigned
static inline int     Gip_SolverDecide( Gip_Solver_t * p )
{
    int decide, Lit;
    while ( (decide = Gip_VsidsPop(&p->Vsids)) != -1 )
    {
        if ( p->pValue[decide] != GIP_NONE )
            continue;
        if ( p->pPhase[decide] != GIP_NONE )
            Lit = Gip_Lit( decide, p->pPhase[decide] == GIP_FALSE );
        else
            Lit = Gip_Lit( decide, 1 );
        Vec_IntPush( p->vPosInTrail, Vec_IntSize(p->vTrail) );
        Gip_SolverAssign( p, Lit, GIP_CREF_NONE );
        p->Stats.nDecisions++;
        return 1;
    }
    return 0;
}

ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
