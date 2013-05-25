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

#define SFM_FANIN_MAX 6

#define SFM_SAT_UNDEC 0x1234567812345678
#define SFM_SAT_SAT   0x8765432187654321

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

struct Sfm_Ntk_t_
{
    // parameters
    Sfm_Par_t *       pPars;       // parameters
    // objects
    int               nPis;        // PI count (PIs should be first objects)
    int               nPos;        // PO count (POs should be last objects)
    int               nNodes;      // internal nodes
    int               nObjs;       // total objects
    // user data
    Vec_Str_t *       vFixed;      // persistent objects
    Vec_Wrd_t *       vTruths;     // truth tables
    Vec_Wec_t         vFanins;     // fanins
    // attributes
    Vec_Wec_t         vFanouts;    // fanouts
    Vec_Int_t         vLevels;     // logic level
    Vec_Int_t         vCounts;     // fanin counters
    Vec_Int_t         vId2Var;     // ObjId -> SatVar
    Vec_Int_t         vVar2Id;     // SatVar -> ObjId
    Vec_Wec_t *       vCnfs;       // CNFs
    Vec_Int_t *       vCover;      // temporary
    // traversal IDs
    Vec_Int_t         vTravIds;    // traversal IDs
    Vec_Int_t         vTravIds2;   // traversal IDs
    int               nTravIds;    // traversal IDs
    int               nTravIds2;   // traversal IDs
    // window
    int               iNode;
    Vec_Int_t *       vLeaves;     // leaves 
    Vec_Int_t *       vNodes;      // internal
    Vec_Int_t *       vDivs;       // divisors
    Vec_Int_t *       vRoots;      // roots
    Vec_Int_t *       vTfo;        // TFO (excluding iNode)
    // SAT solving
    sat_solver *      pSat0;       // SAT solver for the off-set
    sat_solver *      pSat1;       // SAT solver for the on-set
    int               nSatVars;    // the number of variables
    int               nTryRemoves; // number of fanin removals
    int               nTryResubs;  // number of resubstitutions
    int               nRemoves;    // number of fanin removals
    int               nResubs;     // number of resubstitutions
    // counter-examples
    int               nCexes;      // number of CEXes
    Vec_Wrd_t *       vDivCexes;   // counter-examples
    // intermediate data
//    Vec_Int_t *       vFans;       // current fanins
    Vec_Int_t *       vOrder;      // object order
    Vec_Int_t *       vDivVars;    // divisor SAT variables
    Vec_Int_t *       vDivIds;     // divisors indexes
    Vec_Int_t *       vLits;       // literals
    Vec_Wec_t *       vClauses;    // CNF clauses for the node
    Vec_Int_t *       vFaninMap;   // mapping fanins into their SAT vars
    // nodes
    int               nTotalNodesBeg;
    int               nTotalEdgesBeg;
    int               nTotalNodesEnd;
    int               nTotalEdgesEnd;
    int               nNodesTried;
    int               nTotalDivs;
    int               nSatCalls;
    int               nTimeOuts;
    // runtime
    clock_t           timeWin;
    clock_t           timeDiv;
    clock_t           timeCnf;
    clock_t           timeSat;
    clock_t           timeTotal;
};

static inline int  Sfm_NtkPiNum( Sfm_Ntk_t * p )                        { return p->nPis;                                   }
static inline int  Sfm_NtkPoNum( Sfm_Ntk_t * p )                        { return p->nPos;                                   }
static inline int  Sfm_NtkNodeNum( Sfm_Ntk_t * p )                      { return p->nObjs - p->nPis - p->nPos;              }

static inline int  Sfm_ObjIsPi( Sfm_Ntk_t * p, int i )                  { return i < p->nPis;                               }
static inline int  Sfm_ObjIsPo( Sfm_Ntk_t * p, int i )                  { return i + p->nPos >= p->nObjs;                   }
static inline int  Sfm_ObjIsNode( Sfm_Ntk_t * p, int i )                { return i >= p->nPis && i + p->nPos < p->nObjs;    }
static inline int  Sfm_ObjIsFixed( Sfm_Ntk_t * p, int i )               { return Vec_StrEntry(p->vFixed, i);                }

static inline Vec_Int_t * Sfm_ObjFiArray( Sfm_Ntk_t * p, int i )        { return Vec_WecEntry(&p->vFanins, i);              }
static inline Vec_Int_t * Sfm_ObjFoArray( Sfm_Ntk_t * p, int i )        { return Vec_WecEntry(&p->vFanouts, i);             }

static inline int  Sfm_ObjFaninNum( Sfm_Ntk_t * p, int i )              { return Vec_IntSize(Sfm_ObjFiArray(p, i));         }
static inline int  Sfm_ObjFanoutNum( Sfm_Ntk_t * p, int i )             { return Vec_IntSize(Sfm_ObjFoArray(p, i));         }

static inline int  Sfm_ObjRefIncrement( Sfm_Ntk_t * p, int iObj )       { return ++Sfm_ObjFiArray(p, iObj)->nSize;          } 
static inline int  Sfm_ObjRefDecrement( Sfm_Ntk_t * p, int iObj )       { return --Sfm_ObjFiArray(p, iObj)->nSize;          } 

static inline int  Sfm_ObjFanin( Sfm_Ntk_t * p, int i, int k )          { return Vec_IntEntry(Sfm_ObjFiArray(p, i), k);     }
static inline int  Sfm_ObjFanout( Sfm_Ntk_t * p, int i, int k )         { return Vec_IntEntry(Sfm_ObjFoArray(p, i), k);     }

static inline int  Sfm_ObjSatVar( Sfm_Ntk_t * p, int iObj )             { assert(Vec_IntEntry(&p->vId2Var, iObj) > 0); return Vec_IntEntry(&p->vId2Var, iObj);  }
static inline void Sfm_ObjSetSatVar( Sfm_Ntk_t * p, int iObj, int Num ) { assert(Vec_IntEntry(&p->vId2Var, iObj) == -1); Vec_IntWriteEntry(&p->vId2Var, iObj, Num);  Vec_IntWriteEntry(&p->vVar2Id, Num, iObj);  }
static inline void Sfm_ObjCleanSatVar( Sfm_Ntk_t * p, int Num )         { int iObj = Vec_IntEntry(&p->vVar2Id, Num); assert(Vec_IntEntry(&p->vId2Var, iObj) > 0); Vec_IntWriteEntry(&p->vId2Var, iObj, -1);  Vec_IntWriteEntry(&p->vVar2Id, Num, -1); }
static inline void Sfm_NtkCleanVars( Sfm_Ntk_t * p )                    { int i; for ( i = 1; i < p->nSatVars; i++ )  Sfm_ObjCleanSatVar( p, i ); }

static inline int  Sfm_ObjLevel( Sfm_Ntk_t * p, int iObj )              { return Vec_IntEntry( &p->vLevels, iObj );                         }
static inline void Sfm_ObjSetLevel( Sfm_Ntk_t * p, int iObj, int Lev )  { Vec_IntWriteEntry( &p->vLevels, iObj, Lev );                      }

static inline int  Sfm_ObjUpdateFaninCount( Sfm_Ntk_t * p, int iObj )   { return Vec_IntAddToEntry(&p->vCounts, iObj, -1);                  }
static inline void Sfm_ObjResetFaninCount( Sfm_Ntk_t * p, int iObj )    { Vec_IntWriteEntry(&p->vCounts, iObj, Sfm_ObjFaninNum(p, iObj)-1); }


////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

#define Sfm_NtkForEachNode( p, i )                for ( i = p->nPis; i + p->nPos < p->nObjs; i++ )
#define Sfm_ObjForEachFanin( p, Node, Fan, i )   for ( i = 0; i < Sfm_ObjFaninNum(p, Node)  && ((Fan = Sfm_ObjFanin(p, Node, i)), 1);  i++ )
#define Sfm_ObjForEachFanout( p, Node, Fan, i )  for ( i = 0; i < Sfm_ObjFanoutNum(p, Node) && ((Fan = Sfm_ObjFanout(p, Node, i)), 1); i++ )

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== sfmCnf.c ==========================================================*/
extern void         Sfm_PrintCnf( Vec_Str_t * vCnf );
extern int          Sfm_TruthToCnf( word Truth, int nVars, Vec_Int_t * vCover, Vec_Str_t * vCnf );
extern Vec_Wec_t *  Sfm_CreateCnf( Sfm_Ntk_t * p );
extern void         Sfm_TranslateCnf( Vec_Wec_t * vRes, Vec_Str_t * vCnf, Vec_Int_t * vFaninMap );
/*=== sfmCore.c ==========================================================*/
/*=== sfmNtk.c ==========================================================*/
extern Sfm_Ntk_t *  Sfm_ConstructNetwork( Vec_Wec_t * vFanins, int nPis, int nPos );
extern void         Sfm_NtkPrepare( Sfm_Ntk_t * p );
extern void         Sfm_NtkUpdate( Sfm_Ntk_t * p, int iNode, int f, int iFaninNew, word uTruth );
/*=== sfmSat.c ==========================================================*/
extern void         Sfm_NtkWindowToSolver( Sfm_Ntk_t * p );
extern word         Sfm_ComputeInterpolant( Sfm_Ntk_t * p );
/*=== sfmWin.c ==========================================================*/
extern int          Sfm_ObjMffcSize( Sfm_Ntk_t * p, int iObj );
extern int          Sfm_NtkCreateWindow( Sfm_Ntk_t * p, int iNode, int fVerbose );
extern void         Sfm_NtkPrepareDivisors( Sfm_Ntk_t * p, int iNode );


ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

