/**CFile****************************************************************

  FileName    [if.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: if.h,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __IF_H__
#define __IF_H__

#ifdef __cplusplus
extern "C" {
#endif

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <time.h>
#include "vec.h"
#include "mem.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

// the maximum size of LUTs used for mapping (should be the same as FPGA_MAX_LUTSIZE defined in "fpga.h"!!!)
#define IF_MAX_LUTSIZE   32

// object types
typedef enum { 
    IF_NONE,     // 0: non-existent object
    IF_CONST1,   // 1: constant 1 
    IF_PI,       // 2: primary input
    IF_PO,       // 3: primary output
    IF_AND,      // 4: AND node
    IF_BI,       // 5: box input
    IF_BO,       // 6: box output
    IF_BOX,      // 7: box
    IF_VOID      // 8: unused object
} If_Type_t;

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct If_Par_t_     If_Par_t;
typedef struct If_Lib_t_     If_Lib_t;
typedef struct If_Man_t_     If_Man_t;
typedef struct If_Obj_t_     If_Obj_t;
typedef struct If_Cut_t_     If_Cut_t;

// parameters
struct If_Par_t_
{
    // user-controlable paramters
    int                Mode;          // the mapping mode
    int                nLutSize;      // the LUT size
    int                nCutsMax;      // the max number of cuts
    float              DelayTarget;   // delay target
    int                fPreprocess;   // preprossing
    int                fArea;         // area-oriented mapping
    int                fFancy;        // a fancy feature
    int                fExpRed;       // expand/reduce of the best cuts
    int                fLatchPaths;   // reset timing on latch paths
    int                fSeq;          // sequential mapping
    int                fVerbose;      // the verbosity flag
    // internal parameters
    int                fTruth;        // truth table computation enabled
    int                fUseBdds;      // sets local BDDs at the nodes
    int                nLatches;      // the number of latches in seq mapping
    If_Lib_t *         pLutLib;       // the LUT library
    float *            pTimesArr;     // arrival times
    float *            pTimesReq;     // required times
    int(*pFuncCost)(unsigned *, int); // procedure the user's cost of a cut
    void *             pReoMan;       // reordering manager
};

// the LUT library
struct If_Lib_t_
{
    char *             pName;         // the name of the LUT library
    int                LutMax;        // the maximum LUT size 
    float              pLutAreas[IF_MAX_LUTSIZE+1]; // the areas of LUTs
    float              pLutDelays[IF_MAX_LUTSIZE+1];// the delays of LUTs
};

// manager
struct If_Man_t_
{
    // mapping parameters
    If_Par_t *         pPars;
    // mapping nodes
    If_Obj_t *         pConst1;       // the constant 1 node
    Vec_Ptr_t *        vPis;          // the primary inputs
    Vec_Ptr_t *        vPos;          // the primary outputs
    Vec_Ptr_t *        vObjs;         // all objects
    Vec_Ptr_t *        vMapped;       // objects used in the mapping
    Vec_Ptr_t *        vTemp;         // temporary array
    int                nObjs[IF_VOID];// the number of objects by type
    // various data
    int                nLevelMax;     // the max number of AIG levels
    float              fEpsilon;      // epsilon used for comparison
    float              RequiredGlo;   // global required times
    float              AreaGlo;       // global area
    int                nCutsUsed;     // the number of cuts currently used
    int                nCutsMerged;   // the total number of cuts merged
    int                nCutsMax;      // the maximum number of cuts at a node
    float              Fi;            // the current value of the clock period (for seq mapping)
    unsigned *         puTemp[4];     // used for the truth table computation
    // memory management
    Mem_Fixed_t *      pMem;          // memory manager
    int                nEntrySize;    // the size of the entry
    int                nEntryBase;    // the size of the entry minus cut leaf arrays
    int                nTruthSize;    // the size of the truth table if allocated
    int                nCutSize;      // the size of the cut
    // temporary cut storage
    int                nCuts;         // the number of cuts used
    If_Cut_t **        ppCuts;        // the storage space for cuts
};

// priority cut
struct If_Cut_t_
{
    float              Delay;         // delay of the cut
    float              Area;          // area (or area-flow) of the cut
    unsigned           uSign;         // cut signature
    unsigned           Cost    : 10;  // the user's cost of the cut
    unsigned           Depth   :  9;  // the user's depth of the cut
    unsigned           fCompl  :  1;  // the complemented attribute 
    unsigned           nLimit  :  6;  // the maximum number of leaves
    unsigned           nLeaves :  6;  // the number of leaves
    int *              pLeaves;       // array of fanins
    unsigned *         pTruth;        // the truth table
};

// node extension
struct If_Obj_t_
{
    unsigned           Type    :  4;  // object
    unsigned           fCompl0 :  1;  // complemented attribute
    unsigned           fCompl1 :  1;  // complemented attribute
    unsigned           fPhase  :  1;  // phase of the node
    unsigned           fMark   :  1;  // multipurpose mark
    unsigned           Level   : 24;  // logic level of the node
    int                Id;            // integer ID
    int                nRefs;         // the number of references
    int                nCuts;         // the number of cuts
    If_Obj_t *         pFanin0;       // the first fanin 
    If_Obj_t *         pFanin1;       // the second fanin
    If_Obj_t *         pEquiv;        // the choice node
    float              EstRefs;       // estimated reference counter
    float              Required;      // required time of the onde
    void *             pCopy;         // used for duplication
    If_Cut_t           Cuts[0];       // the cuts of the node
};

static inline If_Obj_t * If_ManConst1( If_Man_t * p )                        { return p->pConst1;                              }
static inline If_Obj_t * If_ManPi( If_Man_t * p, int i )                     { return (If_Obj_t *)Vec_PtrEntry( p->vPis, i );  }
static inline If_Obj_t * If_ManPo( If_Man_t * p, int i )                     { return (If_Obj_t *)Vec_PtrEntry( p->vPos, i );  }
static inline If_Obj_t * If_ManObj( If_Man_t * p, int i )                    { return (If_Obj_t *)Vec_PtrEntry( p->vObjs, i ); }
static inline If_Cut_t * If_ManCut( If_Man_t * p, int i )                    { return p->ppCuts[i];                            }

static inline int        If_ManPiNum( If_Man_t * p )                         { return p->nObjs[IF_PI];               }
static inline int        If_ManPoNum( If_Man_t * p )                         { return p->nObjs[IF_PO];               }
static inline int        If_ManAndNum( If_Man_t * p )                        { return p->nObjs[IF_AND];              }

static inline int        If_ObjIsConst1( If_Obj_t * pObj )                   { return pObj->Type == IF_CONST1;       }
static inline int        If_ObjIsPi( If_Obj_t * pObj )                       { return pObj->Type == IF_PI;           }
static inline int        If_ObjIsPo( If_Obj_t * pObj )                       { return pObj->Type == IF_PO;           }
static inline int        If_ObjIsAnd( If_Obj_t * pObj )                      { return pObj->Type == IF_AND;          }
static inline int        If_ObjIsBi( If_Obj_t * pObj )                       { return pObj->Type == IF_BI;           }
static inline int        If_ObjIsBo( If_Obj_t * pObj )                       { return pObj->Type == IF_BO;           }
static inline int        If_ObjIsBox( If_Obj_t * pObj )                      { return pObj->Type == IF_BOX;          }

static inline If_Obj_t * If_ObjFanin0( If_Obj_t * pObj )                     { return pObj->pFanin0;                 }
static inline If_Obj_t * If_ObjFanin1( If_Obj_t * pObj )                     { return pObj->pFanin1;                 }
static inline int        If_ObjFaninC0( If_Obj_t * pObj )                    { return pObj->fCompl0;                 }
static inline int        If_ObjFaninC1( If_Obj_t * pObj )                    { return pObj->fCompl1;                 }
static inline void *     If_ObjCopy( If_Obj_t * pObj )                       { return pObj->pCopy;                   }
static inline void       If_ObjSetCopy( If_Obj_t * pObj, void * pCopy )      { pObj->pCopy = pCopy;                  }
static inline void       If_ObjSetChoice( If_Obj_t * pObj, If_Obj_t * pEqu ) { pObj->pEquiv = pEqu;                  }

static inline If_Cut_t * If_ObjCut( If_Obj_t * pObj, int iCut )              { return pObj->Cuts + iCut;             }
static inline If_Cut_t * If_ObjCutTriv( If_Obj_t * pObj )                    { return pObj->Cuts;                    }
static inline If_Cut_t * If_ObjCutBest( If_Obj_t * pObj )                    { return pObj->Cuts + 1;                }
static inline unsigned   If_ObjCutSign( unsigned ObjId )                     { return (1 << (ObjId % 31));           }

static inline void *     If_CutData( If_Cut_t * pCut )                       { return *(void **)pCut;                }
static inline void       If_CutSetData( If_Cut_t * pCut, void * pData )      { *(void **)pCut = pData;               }

static inline int        If_CutTruthWords( int nVarsMax )                    { return nVarsMax <= 5 ? 1 : (1 << (nVarsMax - 5)); }
static inline unsigned * If_CutTruth( If_Cut_t * pCut )                      { return pCut->pTruth;                              }

static inline float      If_CutLutDelay( If_Man_t * p, If_Cut_t * pCut )     { return pCut->Depth? (float)pCut->Depth : (p->pPars->pLutLib? p->pPars->pLutLib->pLutDelays[pCut->nLeaves] : (float)1.0);  }
static inline float      If_CutLutArea( If_Man_t * p, If_Cut_t * pCut )      { return pCut->Cost?  (float)pCut->Cost  : (p->pPars->pLutLib? p->pPars->pLutLib->pLutAreas[pCut->nLeaves]  : (float)1.0);  }

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

#define IF_MIN(a,b)       (((a) < (b))? (a) : (b))
#define IF_MAX(a,b)       (((a) > (b))? (a) : (b))

// the small and large numbers (min/max float are 1.17e-38/3.40e+38)
#define IF_FLOAT_LARGE   ((float)1.0e+20)
#define IF_FLOAT_SMALL   ((float)1.0e-20)
#define IF_INT_LARGE     (10000000)

// iterator over the primary inputs
#define If_ManForEachPi( p, pObj, i )                                          \
    Vec_PtrForEachEntry( p->vPis, pObj, i )
// iterator over the primary outputs
#define If_ManForEachPo( p, pObj, i )                                          \
    Vec_PtrForEachEntry( p->vPos, pObj, i )
// iterator over the latches 
#define If_ManForEachLatch( p, pObj, i )                                       \
    Vec_PtrForEachEntryStart( p->vPos, pObj, i, p->pPars->nLatches )
// iterator over all objects, including those currently not used
#define If_ManForEachObj( p, pObj, i )                                         \
    Vec_PtrForEachEntry( p->vObjs, pObj, i )
// iterator over logic nodes (AND and EXOR gates)
#define If_ManForEachNode( p, pObj, i )                                        \
    If_ManForEachObj( p, pObj, i ) if ( pObj->Type != IF_AND ) {} else
// iterator over cuts of the node
#define If_ObjForEachCut( pObj, pCut, i )                                      \
    for ( i = 0; (i < (int)(pObj)->nCuts) && ((pCut) = (pObj)->Cuts + i); i++ )
// iterator over cuts of the node
#define If_ObjForEachCutStart( pObj, pCut, i, Start )                          \
    for ( i = Start; (i < (int)(pObj)->nCuts) && ((pCut) = (pObj)->Cuts + i); i++ )
// iterator leaves of the cut
#define If_CutForEachLeaf( p, pCut, pLeaf, i )                                 \
    for ( i = 0; (i < (int)(pCut)->nLeaves) && ((pLeaf) = If_ManObj(p, (pCut)->pLeaves[i])); i++ )

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== ifCore.c ==========================================================*/
extern int             If_ManPerformMapping( If_Man_t * p );
extern int             If_ManPerformMappingRound( If_Man_t * p, int nCutsUsed, int Mode, int fRequired );
/*=== ifCut.c ==========================================================*/
extern float           If_CutAreaDerefed( If_Man_t * p, If_Cut_t * pCut, int nLevels );
extern float           If_CutAreaRefed( If_Man_t * p, If_Cut_t * pCut, int nLevels );
extern float           If_CutDeref( If_Man_t * p, If_Cut_t * pCut, int nLevels );
extern float           If_CutRef( If_Man_t * p, If_Cut_t * pCut, int nLevels );
extern void            If_CutPrint( If_Man_t * p, If_Cut_t * pCut );
extern float           If_CutDelay( If_Man_t * p, If_Cut_t * pCut );
extern float           If_CutFlow( If_Man_t * p, If_Cut_t * pCut );
extern int             If_CutFilter( If_Man_t * p, If_Cut_t * pCut );
extern int             If_CutMerge( If_Cut_t * pCut0, If_Cut_t * pCut1, If_Cut_t * pCut );
extern void            If_CutCopy( If_Cut_t * pCutDest, If_Cut_t * pCutSrc );
extern void            If_ManSortCuts( If_Man_t * p, int Mode );
/*=== ifMan.c ==========================================================*/
extern If_Man_t *      If_ManStart( If_Par_t * pPars );
extern void            If_ManStop( If_Man_t * p );
extern If_Obj_t *      If_ManCreatePi( If_Man_t * p );
extern If_Obj_t *      If_ManCreatePo( If_Man_t * p, If_Obj_t * pDriver, int fCompl0 );
extern If_Obj_t *      If_ManCreateAnd( If_Man_t * p, If_Obj_t * pFan0, int fCompl0, If_Obj_t * pFan1, int fCompl1 );
/*=== ifMap.c ==========================================================*/
extern void            If_ObjPerformMapping( If_Man_t * p, If_Obj_t * pObj, int Mode );
/*=== ifPrepro.c ==========================================================*/
extern void            If_ManPerformMappingPreprocess( If_Man_t * p );
/*=== ifReduce.c ==========================================================*/
extern void            If_ManImproveMapping( If_Man_t * p );
/*=== ifSeq.c ==========================================================*/
extern int             If_ManPerformMappingSeq( If_Man_t * p );
/*=== ifTruth.c ==========================================================*/
extern void            If_CutComputeTruth( If_Man_t * p, If_Cut_t * pCut, If_Cut_t * pCut0, If_Cut_t * pCut1, int fCompl0, int fCompl1 );
/*=== ifUtil.c ==========================================================*/
extern float           If_ManDelayMax( If_Man_t * p );
extern void            If_ManCleanNodeCopy( If_Man_t * p );
extern void            If_ManCleanCutData( If_Man_t * p );
extern void            If_ManComputeRequired( If_Man_t * p, int fFirstTime );
extern float           If_ManScanMapping( If_Man_t * p );

#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

