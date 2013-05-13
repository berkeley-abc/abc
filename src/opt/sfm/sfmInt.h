/**CFile****************************************************************

  FileName    [rsbInt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based optimization using internal don't-cares.]

  Synopsis    [Internal declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: rsbInt.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef ABC__opt_sfmInt__h
#define ABC__opt_sfmInt__h


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include "misc/vec/vec.h"
#include "sat/bsat/satSolver.h"
#include "sfm.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_HEADER_START

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

struct Sfm_Ntk_t_
{
    // parameters
    Sfm_Par_t *       pPars;    // parameters
    // objects
    int               nPis;     // PI count (PIs should be first objects)
    int               nPos;     // PO count (POs should be last objects)
    int               nNodes;   // internal nodes
    int               nObjs;    // total objects
    // user data
    Vec_Wec_t *       vFanins;  // fanins
    Vec_Str_t *       vFixed;   // persistent objects
    Vec_Wrd_t *       vTruths;  // truth tables
    // attributes
    Vec_Wec_t *       vFanouts; // fanouts
    Vec_Int_t *       vLevels;  // logic level
    Vec_Int_t         vTravIds; // traversal IDs
    Vec_Int_t         vId2Var;  // ObjId -> SatVar
    Vec_Int_t         vVar2Id;  // SatVar -> ObjId
    Vec_Wec_t *       vCnfs;    // CNFs
    Vec_Int_t *       vCover;   // temporary
    int               nTravIds; // traversal IDs
    // window
    int               iNode;
    Vec_Int_t *       vLeaves;  // leaves 
    Vec_Int_t *       vRoots;   // roots
    Vec_Int_t *       vNodes;   // internal
    Vec_Int_t *       vTfo;     // TFO (excluding iNode)
    // SAT solving
    int               nSatVars; // the number of variables
    sat_solver *      pSat1;    // SAT solver for the on-set
    sat_solver *      pSat0;    // SAT solver for the off-set
    // intermediate data
    Vec_Int_t *       vDivs;    // divisors
    Vec_Int_t *       vLits;    // literals
    Vec_Int_t *       vFani;    // iterator fanins
    Vec_Int_t *       vFano;    // iterator fanouts
    Vec_Wec_t *       vClauses; // CNF clauses for the node
    Vec_Int_t *       vFaninMap;// mapping fanins into their SAT vars
};

#define SFM_SAT_UNDEC 0x1234567812345678
#define SFM_SAT_SAT   0x8765432187654321

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

#define Sfm_NtkForEachNode( p, i )                for ( i = p->nPis; i + p->nPos < p->nObjs; i++ )
#define Sfm_NodeForEachFanin( p, Node, Fan, i )   for ( p->vFani = Vec_WecEntry(p->vFanins,  Node), i = 0; i < Vec_IntSize(p->vFani) && ((Fan = Vec_IntEntry(p->vFani, i)), 1); i++ )
#define Sfm_NodeForEachFanout( p, Node, Fan, i )  for ( p->vFano = Vec_WecEntry(p->vFanouts, Node), i = 0; i < Vec_IntSize(p->vFani) && ((Fan = Vec_IntEntry(p->vFano, i)), 1); i++ )

static inline int  Sfm_ObjIsPi( Sfm_Ntk_t * p, int i )      { return i < p->nPis;                               }
static inline int  Sfm_ObjIsPo( Sfm_Ntk_t * p, int i )      { return i + p->nPos < p->nObjs;                    }
static inline int  Sfm_ObjIsNode( Sfm_Ntk_t * p, int i )    { return i >= p->nPis && i + p->nPos < p->nObjs;    }

static inline int  Sfm_ObjFaninNum( Sfm_Ntk_t * p, int i )  { return Vec_IntSize(Vec_WecEntry(p->vFanins, i));  }
static inline int  Sfm_ObjFanoutNum( Sfm_Ntk_t * p, int i ) { return Vec_IntSize(Vec_WecEntry(p->vFanouts, i)); }

static inline int  Sfm_ObjSatVar( Sfm_Ntk_t * p, int iObj )             { return Vec_IntEntry(&p->vId2Var, iObj);     }
static inline void Sfm_ObjSetSatVar( Sfm_Ntk_t * p, int iObj, int Num ) { assert(Sfm_ObjSatVar(p, iObj) == -1); Vec_IntWriteEntry(&p->vId2Var, iObj, Num);  Vec_IntWriteEntry(&p->vVar2Id, Num, iObj);                            }
static inline void Sfm_ObjCleanSatVar( Sfm_Ntk_t * p, int Num )         { assert(Sfm_ObjSatVar(p, Vec_IntEntry(&p->vVar2Id, Num)) != -1); Vec_IntWriteEntry(&p->vId2Var, Vec_IntEntry(&p->vVar2Id, Num), Num);  Vec_IntWriteEntry(&p->vVar2Id, Num, -1);    }
static inline void Sfm_NtkCleanVars( Sfm_Ntk_t * p, int nSize )         { int i; for ( i = 1; i < nSize; i++ )  Sfm_ObjCleanSatVar( p, i ); }


////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== sfmCnf.c ==========================================================*/
extern void         Sfm_PrintCnf( Vec_Str_t * vCnf );
extern int          Sfm_TruthToCnf( word Truth, int nVars, Vec_Int_t * vCover, Vec_Str_t * vCnf );
extern void         Sfm_TranslateCnf( Vec_Wec_t * vRes, Vec_Str_t * vCnf, Vec_Int_t * vFaninMap );
/*=== sfmCore.c ==========================================================*/
/*=== sfmNtk.c ==========================================================*/
extern Sfm_Ntk_t *  Sfm_ConstructNetwork( Vec_Wec_t * vFanins, int nPis, int nPos );
/*=== sfmSat.c ==========================================================*/
extern word         Sfm_ComputeInterpolant( sat_solver * pSatOn, sat_solver * pSatOff, Vec_Int_t * vDivs, Vec_Int_t * vLits, Vec_Int_t * vDiffs, int nBTLimit );
/*=== sfmWin.c ==========================================================*/
extern int          Sfm_NtkWindow( Sfm_Ntk_t * p, int iNode );
extern void         Sfm_NtkWin2Sat( Sfm_Ntk_t * p );


ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

