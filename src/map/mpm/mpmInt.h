/**CFile****************************************************************

  FileName    [mpmInt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Configurable technology mapper.]

  Synopsis    [Interal declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 1, 2013.]

  Revision    [$Id: mpmInt.h,v 1.00 2013/06/01 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef ABC__map__mpm_Int_h
#define ABC__map__mpm_Int_h


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////
 
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

//#include "misc/tim/tim.h"
#include "misc/vec/vec.h"
#include "misc/mem/mem2.h"
#include "mpmMig.h"
#include "mpm.h"

ABC_NAMESPACE_HEADER_START

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////
 
#define MPM_CUT_MAX      64

#define MPM_UNIT_TIME     1
#define MPM_UNIT_AREA    20
#define MPM_UNIT_EDGE    50
#define MPM_UNIT_REFS   100

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Mpm_Cut_t_ Mpm_Cut_t;  // 8 bytes + NLeaves * 4 bytes
struct Mpm_Cut_t_
{
    int              hNext;                    // next cut
    unsigned         iFunc     : 26;           // function
    unsigned         fUseless  :  1;           // internal flag
    unsigned         nLeaves   :  5;           // leaves
    int              pLeaves[0];               // leaves
};

typedef struct Mpm_Inf_t_ Mpm_Inf_t;  // 32 bytes
struct Mpm_Inf_t_
{
    int              hCut;                     // cut handle
    unsigned         nLeaves   :  6;           // the number of leaves
    unsigned         mCost     : 26;           // area cost of this cut
    int              mTime;                    // arrival time
    int              mArea;                    // area (flow)
    int              mEdge;                    // edge (flow)
    int              mAveRefs;                 // area references
    word             uSign;                    // cut signature
};

typedef struct Mpm_Uni_t_ Mpm_Uni_t;  // 48 bytes
struct Mpm_Uni_t_
{
    Mpm_Inf_t        Inf;                      // information
    unsigned         iFunc     : 26;           // function
    unsigned         fUseless  :  1;           // internal flag
    unsigned         nLeaves   :  5;           // leaves
    int              pLeaves[MPM_VAR_MAX];     // leaves
};

typedef struct Mpm_Man_t_ Mpm_Man_t;
struct Mpm_Man_t_
{
    Mig_Man_t *      pMig;                     // AIG manager
    // mapping parameters
    int              nLutSize;                 // LUT size
    int              nNumCuts;                 // cut count
    Mpm_LibLut_t *   pLibLut;                  // LUT library
    // mapping attributes  
    int              GloRequired;              // global arrival time
    int              GloArea;                  // total area
    int              GloEdge;                  // total edge
    int              fMainRun;                 // after preprocessing is finished
    // cut management
    Mmr_Step_t *     pManCuts;                 // cut memory
    // temporary cut storage
    int              nCutStore;                // number of cuts in storage
    Mpm_Uni_t *      pCutStore[MPM_CUT_MAX+1]; // storage for cuts
    Mpm_Uni_t        pCutUnits[MPM_CUT_MAX+1]; // cut info units
    Vec_Int_t        vFreeUnits;               // free cut info units
    Vec_Ptr_t *      vTemp;                    // storage for cuts
    // object presence
    unsigned char *  pObjPres;                 // object presence
    Mpm_Cut_t *      pCutTemp;                 // temporary cut
    Vec_Str_t        vObjShared;               // object presence
    // cut comparison
    int (* pCutCmp) (Mpm_Inf_t *, Mpm_Inf_t *);// procedure to compare cuts
    // fanin cuts/signatures
    int              nCuts[3];                 // fanin cut counts
    Mpm_Cut_t *      pCuts[3][MPM_CUT_MAX+1];  // fanin cuts
    word             pSigns[3][MPM_CUT_MAX+1]; // fanin cut signatures
    // functionality
//    Dsd_Man_t *      pManDsd;
    void *           pManDsd;
    int              pPerm[MPM_VAR_MAX]; 
    // mapping attributes
    Vec_Int_t        vCutBests;                // cut best
    Vec_Int_t        vCutLists;                // cut list
    Vec_Int_t        vMigRefs;                 // original references
    Vec_Int_t        vMapRefs;                 // exact mapping references
    Vec_Int_t        vEstRefs;                 // estimated mapping references
    Vec_Int_t        vRequireds;               // required time
    Vec_Int_t        vTimes;                   // arrival time
    Vec_Int_t        vAreas;                   // area
    Vec_Int_t        vEdges;                   // edge
    // statistics
    int              nCutsMerged;
    abctime          timeFanin;
    abctime          timeDerive;
    abctime          timeMerge;
    abctime          timeEval;
    abctime          timeCompare;
    abctime          timeStore;
    abctime          timeOther;
    abctime          timeTotal;
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

static inline int         Mpm_ObjCutBest( Mpm_Man_t * p, Mig_Obj_t * pObj )              { return Vec_IntEntry(&p->vCutBests, Mig_ObjId(pObj));            }
static inline void        Mpm_ObjSetCutBest( Mpm_Man_t * p, Mig_Obj_t * pObj, int i )    { Vec_IntWriteEntry(&p->vCutBests, Mig_ObjId(pObj), i);           }

static inline int         Mpm_CutWordNum( int nLeaves )                                  { return (sizeof(Mpm_Cut_t)/sizeof(int) + nLeaves + 1) >> 1;      }
static inline Mpm_Cut_t * Mpm_CutFetch( Mpm_Man_t * p, int h )                           { Mpm_Cut_t * pCut = (Mpm_Cut_t *)Mmr_StepEntry( p->pManCuts, h );  assert( Mpm_CutWordNum(pCut->nLeaves) == (h & p->pManCuts->uMask) ); return pCut; }
static inline Mpm_Cut_t * Mpm_ObjCutBestP( Mpm_Man_t * p, Mig_Obj_t * pObj )             { return Mpm_CutFetch( p, Mpm_ObjCutBest(p, pObj) );              }

static inline int         Mpm_ObjCutList( Mpm_Man_t * p, Mig_Obj_t * pObj )              { return Vec_IntEntry(&p->vCutLists, Mig_ObjId(pObj));            }
static inline int *       Mpm_ObjCutListP( Mpm_Man_t * p, Mig_Obj_t * pObj )             { return Vec_IntEntryP(&p->vCutLists, Mig_ObjId(pObj));           }
static inline void        Mpm_ObjSetCutList( Mpm_Man_t * p, Mig_Obj_t * pObj, int i )    { Vec_IntWriteEntry(&p->vCutLists, Mig_ObjId(pObj), i);           }

static inline void        Mpm_ManSetMigRefs( Mpm_Man_t * p )                             { assert( Vec_IntSize(&p->vMigRefs) == Vec_IntSize(&p->pMig->vRefs) ); memcpy( Vec_IntArray(&p->vMigRefs), Vec_IntArray(&p->pMig->vRefs), sizeof(int) * Mig_ManObjNum(p->pMig) ); }
static inline int         Mig_ObjMigRefNum( Mpm_Man_t * p, Mig_Obj_t * pObj )            { return Vec_IntEntry(&p->vMigRefs, Mig_ObjId(pObj));             }
static inline int         Mig_ObjMigRefDec( Mpm_Man_t * p, Mig_Obj_t * pObj )            { return Vec_IntAddToEntry(&p->vMigRefs, Mig_ObjId(pObj), -1);    }

static inline void        Mpm_ManCleanMapRefs( Mpm_Man_t * p )                           { Vec_IntFill( &p->vMapRefs, Mig_ManObjNum(p->pMig), 0 );         }
static inline int         Mpm_ObjMapRef( Mpm_Man_t * p, Mig_Obj_t * pObj )               { return Vec_IntEntry(&p->vMapRefs, Mig_ObjId(pObj));             }
static inline void        Mpm_ObjSetMapRef( Mpm_Man_t * p, Mig_Obj_t * pObj, int i )     { Vec_IntWriteEntry(&p->vMapRefs, Mig_ObjId(pObj), i);            }
 
static inline int         Mpm_ObjEstRef( Mpm_Man_t * p, Mig_Obj_t * pObj )               { return Vec_IntEntry(&p->vEstRefs, Mig_ObjId(pObj));             }
static inline void        Mpm_ObjSetEstRef( Mpm_Man_t * p, Mig_Obj_t * pObj, int i )     { Vec_IntWriteEntry(&p->vEstRefs, Mig_ObjId(pObj), i);            }

static inline void        Mpm_ManCleanRequired( Mpm_Man_t * p )                          { Vec_IntFill(&p->vRequireds,Mig_ManObjNum(p->pMig),ABC_INFINITY);}
static inline int         Mpm_ObjRequired( Mpm_Man_t * p, Mig_Obj_t * pObj )             { return Vec_IntEntry(&p->vRequireds, Mig_ObjId(pObj));           }
static inline void        Mpm_ObjSetRequired( Mpm_Man_t * p, Mig_Obj_t * pObj, int i )   { Vec_IntWriteEntry(&p->vRequireds, Mig_ObjId(pObj), i);          }

static inline int         Mpm_ObjTime( Mpm_Man_t * p, Mig_Obj_t * pObj )                 { return Vec_IntEntry(&p->vTimes, Mig_ObjId(pObj));               }
static inline void        Mpm_ObjSetTime( Mpm_Man_t * p, Mig_Obj_t * pObj, int i )       { Vec_IntWriteEntry(&p->vTimes, Mig_ObjId(pObj), i);              }

static inline int         Mpm_ObjArea( Mpm_Man_t * p, Mig_Obj_t * pObj )                 { return Vec_IntEntry(&p->vAreas, Mig_ObjId(pObj));               }
static inline void        Mpm_ObjSetArea( Mpm_Man_t * p, Mig_Obj_t * pObj, int i )       { Vec_IntWriteEntry(&p->vAreas, Mig_ObjId(pObj), i);              }

static inline int         Mpm_ObjEdge( Mpm_Man_t * p, Mig_Obj_t * pObj )                 { return Vec_IntEntry(&p->vEdges, Mig_ObjId(pObj));               }
static inline void        Mpm_ObjSetEdge( Mpm_Man_t * p, Mig_Obj_t * pObj, int i )       { Vec_IntWriteEntry(&p->vEdges, Mig_ObjId(pObj), i);              }

// iterators over object cuts
#define Mpm_ObjForEachCut( p, pObj, hCut, pCut )                         \
    for ( hCut = Mpm_ObjCutList(p, pObj); hCut && (pCut = Mpm_CutFetch(p, hCut)); hCut = pCut->hNext )
#define Mpm_ObjForEachCutSafe( p, pObj, hCut, pCut, hNext )              \
    for ( hCut = Mpm_ObjCutList(p, pObj); hCut && (pCut = Mpm_CutFetch(p, hCut)) && ((hNext = pCut->hNext), 1); hCut = hNext )

// iterators over cut leaves
#define Mpm_CutForEachLeafId( pCut, iLeafId, i )                         \
    for ( i = 0; i < (int)pCut->nLeaves && ((iLeafId = Abc_Lit2Var(pCut->pLeaves[i])), 1); i++ )
#define Mpm_CutForEachLeaf( p, pCut, pLeaf, i )                          \
    for ( i = 0; i < (int)pCut->nLeaves && (pLeaf = Mig_ManObj(p, Abc_Lit2Var(pCut->pLeaves[i]))); i++ )

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== mpmAbc.c ===========================================================*/
extern Mig_Man_t *           Mig_ManCreate( void * pGia );
extern void *                Mpm_ManFromIfLogic( Mpm_Man_t * pMan );
/*=== mpmCore.c ===========================================================*/
extern Mpm_Man_t *           Mpm_ManStart( Mig_Man_t * pMig, Mpm_LibLut_t * pLib, int nNumCuts );
extern void                  Mpm_ManStop( Mpm_Man_t * p );
extern void                  Mpm_ManPrintStatsInit( Mpm_Man_t * p );
extern void                  Mpm_ManPrintStats( Mpm_Man_t * p );
/*=== mpmDsd.c ===========================================================*/
/*=== mpmLib.c ===========================================================*/
extern Mpm_LibLut_t *        Mpm_LibLutSetSimple( int nLutSize );
extern void                  Mpm_LibLutFree( Mpm_LibLut_t * pLib );
/*=== mpmMap.c ===========================================================*/
extern void                  Mpm_ManPrepare( Mpm_Man_t * p );
extern void                  Mpm_ManPerform( Mpm_Man_t * p );

ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

