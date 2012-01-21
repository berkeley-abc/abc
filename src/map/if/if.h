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
 
#ifndef ABC__map__if__if_h
#define ABC__map__if__if_h


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////
 
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <time.h>
#include "src/misc/vec/vec.h"
#include "src/misc/mem/mem.h"
#include "src/misc/tim/tim.h"



ABC_NAMESPACE_HEADER_START


////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////
 
// the maximum size of LUTs used for mapping (should be the same as FPGA_MAX_LUTSIZE defined in "fpga.h"!!!)
#define IF_MAX_LUTSIZE       32
// the largest possible number of LUT inputs when funtionality of the LUTs are computed
#define IF_MAX_FUNC_LUTSIZE  15
// a very large number
#define IF_INFINITY          100000000  
// the largest possible user cut cost
#define IF_COST_MAX          8191 // ((1<<13)-1)

// object types
typedef enum { 
    IF_NONE,     // 0: non-existent object
    IF_CONST1,   // 1: constant 1 
    IF_CI,       // 2: combinational input
    IF_CO,       // 3: combinational output
    IF_AND,      // 4: AND node
    IF_VOID      // 5: unused object
} If_Type_t;

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct If_Man_t_     If_Man_t;
typedef struct If_Par_t_     If_Par_t;
typedef struct If_Lib_t_     If_Lib_t;
typedef struct If_Obj_t_     If_Obj_t;
typedef struct If_Cut_t_     If_Cut_t;
typedef struct If_Set_t_     If_Set_t;

// parameters
struct If_Par_t_
{
    // user-controlable parameters
    int                nLutSize;      // the LUT size
    int                nCutsMax;      // the max number of cuts
    int                nFlowIters;    // the number of iterations of area recovery
    int                nAreaIters;    // the number of iterations of area recovery
    float              DelayTarget;   // delay target
    float              Epsilon;       // value used in comparison floating point numbers
    int                fPreprocess;   // preprossing
    int                fArea;         // area-oriented mapping
    int                fFancy;        // a fancy feature
    int                fExpRed;       // expand/reduce of the best cuts
    int                fLatchPaths;   // reset timing on latch paths
    int                fEdge;         // uses edge-based cut selection heuristics
    int                fPower;        // uses power-aware cut selection heuristics
    int                fCutMin;       // performs cut minimization by removing functionally reducdant variables
    int                fSeqMap;       // sequential mapping
    int                fBidec;        // use bi-decomposition
    int                fUseBat;       // use one specialized feature
    int                fUseBuffs;     // use buffers to decouple outputs
    int                fEnableCheck07;// enable additional checking
    int                fEnableCheck08;// enable additional checking
    int                fEnableCheck10;// enable additional checking
    int                fEnableRealPos;// enable additional feature
    int                fVerbose;      // the verbosity flag
    char *             pLutStruct;    // LUT structure
    float              WireDelay;     // wire delay
    // internal parameters
    int                fDelayOpt;     // special delay optimization
    int                fUserRecLib;   // use recorded library
    int                fSkipCutFilter;// skip cut filter
    int                fAreaOnly;     // area only mode
    int                fTruth;        // truth table computation enabled
    int                fUsePerm;      // use permutation (delay info)
    int                fUseBdds;      // use local BDDs as a cost function
    int                fUseSops;      // use local SOPs as a cost function
    int                fUseCnfs;      // use local CNFs as a cost function
    int                fUseMv;        // use local MV-SOPs as a cost function
    int                fUseAdders;    // timing model for adders
    int                nLatches;      // the number of latches in seq mapping
    int                fLiftLeaves;   // shift the leaves for seq mapping
    int                fUseCoAttrs;   // use CO attributes
    If_Lib_t *         pLutLib;       // the LUT library
    float *            pTimesArr;     // arrival times
    float *            pTimesReq;     // required times
    int (* pFuncCost)  (If_Cut_t *);  // procedure to compute the user's cost of a cut
    int (* pFuncUser)  (If_Man_t *, If_Obj_t *, If_Cut_t *); //  procedure called for each cut when cut computation is finished
    int (* pFuncCell)  (If_Man_t *, unsigned *, int, int, char *);       //  procedure called for cut functions
    void *             pReoMan;       // reordering manager
};

// the LUT library
struct If_Lib_t_
{
    char *             pName;         // the name of the LUT library
    int                LutMax;        // the maximum LUT size 
    int                fVarPinDelays; // set to 1 if variable pin delays are specified
    float              pLutAreas[IF_MAX_LUTSIZE+1]; // the areas of LUTs
    float              pLutDelays[IF_MAX_LUTSIZE+1][IF_MAX_LUTSIZE+1];// the delays of LUTs
};

// manager
struct If_Man_t_
{
    // mapping parameters
    If_Par_t *         pPars;
    // mapping nodes
    If_Obj_t *         pConst1;       // the constant 1 node
    Vec_Ptr_t *        vCis;          // the primary inputs
    Vec_Ptr_t *        vCos;          // the primary outputs
    Vec_Ptr_t *        vObjs;         // all objects
    Vec_Ptr_t *        vObjsRev;      // reverse topological order of objects
//    Vec_Ptr_t *        vMapped;       // objects used in the mapping
    Vec_Ptr_t *        vTemp;         // temporary array
    int                nObjs[IF_VOID];// the number of objects by type
    // various data
    int                nLevelMax;     // the max number of AIG levels
    float              fEpsilon;      // epsilon used for comparison
    float              RequiredGlo;   // global required times
    float              RequiredGlo2;  // global required times
    float              AreaGlo;       // global area
    int                nNets;         // the sum total of fanins of all LUTs in the mapping
    float              dPower;        // the sum total of switching activities of all LUTs in the mapping
    int                nCutsUsed;     // the number of cuts currently used
    int                nCutsMerged;   // the total number of cuts merged
    unsigned *         puTemp[4];     // used for the truth table computation
    int                SortMode;      // one of the three sorting modes
    int                fNextRound;    // set to 1 after the first round
    int                nChoices;      // the number of choice nodes
    Vec_Int_t *        vSwitching;    // switching activity of each node
    Vec_Int_t **       pDriverCuts;   // temporary driver cuts
    // SOP balancing
    Vec_Int_t *        vCover;        // used to compute ISOP
    Vec_Wrd_t *        vAnds;         // intermediate storage
    Vec_Wrd_t *        vOrGate;       // intermediate storage
    Vec_Wrd_t *        vAndGate;      // intermediate storage
    // sequential mapping
    Vec_Ptr_t *        vLatchOrder;   // topological ordering of latches
    Vec_Int_t *        vLags;         // sequentail lags of all nodes
    int                nAttempts;     // the number of attempts in binary search
    int                nMaxIters;     // the maximum number of iterations
    int                Period;        // the current value of the clock period (for seq mapping)
    // memory management
    int                nTruthWords;   // the size of the truth table if allocated
    int                nPermWords;    // the size of the permutation array (in words)
    int                nObjBytes;     // the size of the object
    int                nCutBytes;     // the size of the cut
    int                nSetBytes;     // the size of the cut set
    Mem_Fixed_t *      pMemObj;       // memory manager for objects (entrysize = nEntrySize)
    Mem_Fixed_t *      pMemSet;       // memory manager for sets of cuts (entrysize = nCutSize*(nCutsMax+1))
    If_Set_t *         pMemCi;        // memory for CI cutsets
    If_Set_t *         pMemAnd;       // memory for AND cutsets
    If_Set_t *         pFreeList;     // the list of free cutsets
    int                nSmallSupp;    // the small support
    int                nCutsTotal;
    int                nCutsUseless[32];
    int                nCutsCount[32];
    int                nCutsCountAll;
    int                nCutsUselessAll;
    // timing manager
    Tim_Man_t *        pManTim;
    Vec_Int_t *        vCoAttrs;      // CO attributes   0=optimize; 1=keep; 2=relax
    // hash table for functions
    int                nTableSize[2];    // hash table size
    int                nTableEntries[2]; // hash table entries
    void **            pHashTable[2];    // hash table bins
    Mem_Fixed_t *      pMemEntries;      // memory manager for hash table entries
    // statistics 
//    int                timeTruth;
};

// priority cut
struct If_Cut_t_
{
    float              Area;          // area (or area-flow) of the cut
    float              AveRefs;       // the average number of leaf references
    float              Edge;          // the edge flow
    float              Power;         // the power flow
    float              Delay;         // delay of the cut
    unsigned           uSign;         // cut signature
    unsigned           Cost    : 13;  // the user's cost of the cut (related to IF_COST_MAX)
    unsigned           fCompl  :  1;  // the complemented attribute 
    unsigned           fUser   :  1;  // using the user's area and delay
    unsigned           fUseless:  1;  // using the user's area and delay
    unsigned           nLimit  :  8;  // the maximum number of leaves
    unsigned           nLeaves :  8;  // the number of leaves
    int *              pLeaves;       // array of fanins
    char *             pPerm;         // permutation
    unsigned *         pTruth;        // the truth table
};

// set of priority cut
struct If_Set_t_
{
    short              nCutsMax;      // the max number of cuts
    short              nCuts;         // the current number of cuts
    If_Set_t *         pNext;         // next cutset in the free list
    If_Cut_t **        ppCuts;        // the array of pointers to the cuts
};

// node extension
struct If_Obj_t_
{
    unsigned           Type    :  4;  // object
    unsigned           fCompl0 :  1;  // complemented attribute
    unsigned           fCompl1 :  1;  // complemented attribute
    unsigned           fPhase  :  1;  // phase of the node
    unsigned           fRepr   :  1;  // representative of the equivalence class
    unsigned           fMark   :  1;  // multipurpose mark
    unsigned           fVisit  :  1;  // multipurpose mark
    unsigned           fSpec   :  1;  // multipurpose mark
    unsigned           fDriver :  1;  // multipurpose mark
    unsigned           fSkipCut:  1;  // multipurpose mark
    unsigned           Level   : 19;  // logic level of the node
    int                Id;            // integer ID
    int                IdPio;         // integer ID of PIs/POs
    int                nRefs;         // the number of references
    int                nVisits;       // the number of visits to this node
    int                nVisitsCopy;   // the number of visits to this node
    If_Obj_t *         pFanin0;       // the first fanin 
    If_Obj_t *         pFanin1;       // the second fanin
    If_Obj_t *         pEquiv;        // the choice node
    float              EstRefs;       // estimated reference counter
    float              Required;      // required time of the onde
    float              LValue;        // sequential arrival time of the node
    void *             pCopy;         // used for object duplication
    If_Set_t *         pCutSet;       // the pointer to the cutset
    If_Cut_t           CutBest;       // the best cut selected 
};

typedef struct If_And_t_ If_And_t;
struct If_And_t_
{
    unsigned           iFan0   : 15;  // fanin0
    unsigned           fCompl0 :  1;  // compl fanin0
    unsigned           iFan1   : 15;  // fanin1
    unsigned           fCompl1 :  1;  // compl fanin1
    unsigned           Id      : 15;  // Id
    unsigned           fCompl  :  1;  // compl output
    unsigned           Delay   : 16;  // delay 
};

static inline If_Obj_t * If_Regular( If_Obj_t * p )                          { return (If_Obj_t *)((ABC_PTRUINT_T)(p) & ~01);  }
static inline If_Obj_t * If_Not( If_Obj_t * p )                              { return (If_Obj_t *)((ABC_PTRUINT_T)(p) ^  01);  }
static inline If_Obj_t * If_NotCond( If_Obj_t * p, int c )                   { return (If_Obj_t *)((ABC_PTRUINT_T)(p) ^ (c));  }
static inline int        If_IsComplement( If_Obj_t * p )                     { return (int )(((ABC_PTRUINT_T)p) & 01);         }

static inline int        If_ManCiNum( If_Man_t * p )                         { return p->nObjs[IF_CI];               }
static inline int        If_ManCoNum( If_Man_t * p )                         { return p->nObjs[IF_CO];               }
static inline int        If_ManAndNum( If_Man_t * p )                        { return p->nObjs[IF_AND];              }
static inline int        If_ManObjNum( If_Man_t * p )                        { return Vec_PtrSize(p->vObjs);         }

static inline If_Obj_t * If_ManConst1( If_Man_t * p )                        { return p->pConst1;                              }
static inline If_Obj_t * If_ManCi( If_Man_t * p, int i )                     { return (If_Obj_t *)Vec_PtrEntry( p->vCis, i );  }
static inline If_Obj_t * If_ManCo( If_Man_t * p, int i )                     { return (If_Obj_t *)Vec_PtrEntry( p->vCos, i );  }
static inline If_Obj_t * If_ManLi( If_Man_t * p, int i )                     { return (If_Obj_t *)Vec_PtrEntry( p->vCos, If_ManCoNum(p) - p->pPars->nLatches + i );  }
static inline If_Obj_t * If_ManLo( If_Man_t * p, int i )                     { return (If_Obj_t *)Vec_PtrEntry( p->vCis, If_ManCiNum(p) - p->pPars->nLatches + i );  }
static inline If_Obj_t * If_ManObj( If_Man_t * p, int i )                    { return (If_Obj_t *)Vec_PtrEntry( p->vObjs, i ); }

static inline int        If_ObjIsConst1( If_Obj_t * pObj )                   { return pObj->Type == IF_CONST1;       }
static inline int        If_ObjIsCi( If_Obj_t * pObj )                       { return pObj->Type == IF_CI;           }
static inline int        If_ObjIsCo( If_Obj_t * pObj )                       { return pObj->Type == IF_CO;           }
static inline int        If_ObjIsTerm( If_Obj_t * pObj )                     { return pObj->Type == IF_CI || pObj->Type == IF_CO; }
static inline int        If_ObjIsLatch( If_Obj_t * pObj )                    { return If_ObjIsCi(pObj) && pObj->pFanin0 != NULL;  }
static inline int        If_ObjIsAnd( If_Obj_t * pObj )                      { return pObj->Type == IF_AND;          }

static inline int        If_ObjId( If_Obj_t * pObj )                         { return pObj->Id;                      }
static inline If_Obj_t * If_ObjFanin0( If_Obj_t * pObj )                     { return pObj->pFanin0;                 }
static inline If_Obj_t * If_ObjFanin1( If_Obj_t * pObj )                     { return pObj->pFanin1;                 }
static inline int        If_ObjFaninC0( If_Obj_t * pObj )                    { return pObj->fCompl0;                 }
static inline int        If_ObjFaninC1( If_Obj_t * pObj )                    { return pObj->fCompl1;                 }
static inline void *     If_ObjCopy( If_Obj_t * pObj )                       { return pObj->pCopy;                   }
static inline int        If_ObjLevel( If_Obj_t * pObj )                      { return pObj->Level;                   }
static inline void       If_ObjSetLevel( If_Obj_t * pObj, int Level )        { pObj->Level = Level;                  }
static inline void       If_ObjSetCopy( If_Obj_t * pObj, void * pCopy )      { pObj->pCopy = pCopy;                  }
static inline void       If_ObjSetChoice( If_Obj_t * pObj, If_Obj_t * pEqu ) { pObj->pEquiv = pEqu;                  }

static inline If_Cut_t * If_ObjCutBest( If_Obj_t * pObj )                    { return &pObj->CutBest;                }
static inline unsigned   If_ObjCutSign( unsigned ObjId )                     { return (1 << (ObjId % 31));           }

static inline float      If_ObjArrTime( If_Obj_t * pObj )                    { return If_ObjCutBest(pObj)->Delay;    }
static inline void       If_ObjSetArrTime( If_Obj_t * pObj, float ArrTime )  { If_ObjCutBest(pObj)->Delay = ArrTime; }

static inline float      If_ObjLValue( If_Obj_t * pObj )                     { return pObj->LValue;                  }
static inline void       If_ObjSetLValue( If_Obj_t * pObj, float LValue )    { pObj->LValue = LValue;                }

static inline void *     If_CutData( If_Cut_t * pCut )                       { return *(void **)pCut;                }
static inline void       If_CutSetData( If_Cut_t * pCut, void * pData )      { *(void **)pCut = pData;               }

static inline int        If_CutDataInt( If_Cut_t * pCut )                    { return *(int *)pCut;                  }
static inline void       If_CutSetDataInt( If_Cut_t * pCut, int Data )       { *(int *)pCut = Data;                  }

static inline int        If_CutLeaveNum( If_Cut_t * pCut )                   { return pCut->nLeaves;                             }
static inline int *      If_CutLeaves( If_Cut_t * pCut )                     { return pCut->pLeaves;                             }
static inline unsigned * If_CutTruth( If_Cut_t * pCut )                      { return pCut->pTruth;                              }
static inline unsigned   If_CutSuppMask( If_Cut_t * pCut )                   { return (~(unsigned)0) >> (32-pCut->nLeaves);      }
static inline int        If_CutTruthWords( int nVarsMax )                    { return nVarsMax <= 5 ? 1 : (1 << (nVarsMax - 5)); }
static inline int        If_CutPermWords( int nVarsMax )                     { return nVarsMax / sizeof(int) + ((nVarsMax % sizeof(int)) > 0); }

static inline float      If_CutLutArea( If_Man_t * p, If_Cut_t * pCut )      { return pCut->fUser? (float)pCut->Cost : (p->pPars->pLutLib? p->pPars->pLutLib->pLutAreas[pCut->nLeaves] : (float)1.0); }

static inline word       If_AndToWrd( If_And_t m )                           { union { If_And_t x; word y; } v; v.x = m; return v.y;  }
static inline If_And_t   If_WrdToAnd( word m )                               { union { If_And_t x; word y; } v; v.y = m; return v.x;  }
static inline void       If_AndClear( If_And_t * pNode )                     { *pNode = If_WrdToAnd(0);                               }


////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

#define IF_MIN(a,b)      (((a) < (b))? (a) : (b))
#define IF_MAX(a,b)      (((a) > (b))? (a) : (b))

// the small and large numbers (min/max float are 1.17e-38/3.40e+38)
#define IF_FLOAT_LARGE   ((float)1.0e+20)
#define IF_FLOAT_SMALL   ((float)1.0e-20)
#define IF_INT_LARGE     (10000000)

// iterator over the primary inputs
#define If_ManForEachCi( p, pObj, i )                                          \
    Vec_PtrForEachEntry( If_Obj_t *, p->vCis, pObj, i )
// iterator over the primary outputs
#define If_ManForEachCo( p, pObj, i )                                          \
    Vec_PtrForEachEntry( If_Obj_t *, p->vCos, pObj, i )
// iterator over the primary inputs
#define If_ManForEachPi( p, pObj, i )                                          \
    Vec_PtrForEachEntryStop( If_Obj_t *, p->vCis, pObj, i, If_ManCiNum(p) - p->pPars->nLatches )
// iterator over the primary outputs
#define If_ManForEachPo( p, pObj, i )                                          \
    Vec_PtrForEachEntryStop( If_Obj_t *, p->vCos, pObj, i, If_ManCoNum(p) - p->pPars->nLatches )
// iterator over the latches 
#define If_ManForEachLatchInput( p, pObj, i )                                  \
    Vec_PtrForEachEntryStart( If_Obj_t *, p->vCos, pObj, i, If_ManCoNum(p) - p->pPars->nLatches )
#define If_ManForEachLatchOutput( p, pObj, i )                                 \
    Vec_PtrForEachEntryStart( If_Obj_t *, p->vCis, pObj, i, If_ManCiNum(p) - p->pPars->nLatches )
// iterator over all objects in topological order
#define If_ManForEachObj( p, pObj, i )                                         \
    Vec_PtrForEachEntry( If_Obj_t *, p->vObjs, pObj, i )
// iterator over all objects in reverse topological order
#define If_ManForEachObjReverse( p, pObj, i )                                  \
    Vec_PtrForEachEntry( If_Obj_t *, p->vObjsRev, pObj, i )
// iterator over logic nodes 
#define If_ManForEachNode( p, pObj, i )                                        \
    If_ManForEachObj( p, pObj, i ) if ( pObj->Type != IF_AND ) {} else
// iterator over cuts of the node
#define If_ObjForEachCut( pObj, pCut, i )                                      \
    for ( i = 0; (i < (pObj)->pCutSet->nCuts) && ((pCut) = (pObj)->pCutSet->ppCuts[i]); i++ )
// iterator over the leaves of the cut
#define If_CutForEachLeaf( p, pCut, pLeaf, i )                                 \
    for ( i = 0; (i < (int)(pCut)->nLeaves) && ((pLeaf) = If_ManObj(p, (pCut)->pLeaves[i])); i++ )
#define If_CutForEachLeafReverse( p, pCut, pLeaf, i )                                 \
    for ( i = (int)(pCut)->nLeaves - 1; (i >= 0) && ((pLeaf) = If_ManObj(p, (pCut)->pLeaves[i])); i-- )
//#define If_CutForEachLeaf( p, pCut, pLeaf, i )                                 \ \\prevent multiline comment
//    for ( i = 0; (i < (int)(pCut)->nLeaves) && ((pLeaf) = If_ManObj(p, p->pPars->fLiftLeaves? (pCut)->pLeaves[i] >> 8 : (pCut)->pLeaves[i])); i++ )
// iterator over the leaves of the sequential cut
#define If_CutForEachLeafSeq( p, pCut, pLeaf, Shift, i )                       \
    for ( i = 0; (i < (int)(pCut)->nLeaves) && ((pLeaf) = If_ManObj(p, (pCut)->pLeaves[i] >> 8)) && (((Shift) = ((pCut)->pLeaves[i] & 255)) >= 0); i++ )

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== ifCore.c ===========================================================*/
extern int             If_ManPerformMapping( If_Man_t * p );
extern int             If_ManPerformMappingComb( If_Man_t * p );
/*=== ifCut.c ============================================================*/
extern int             If_CutFilter( If_Set_t * pCutSet, If_Cut_t * pCut );
extern void            If_CutSort( If_Man_t * p, If_Set_t * pCutSet, If_Cut_t * pCut );
extern void            If_CutOrder( If_Cut_t * pCut );
extern int             If_CutMerge( If_Cut_t * pCut0, If_Cut_t * pCut1, If_Cut_t * pCut );
extern int             If_CutCheck( If_Cut_t * pCut );
extern void            If_CutPrint( If_Cut_t * pCut );
extern void            If_CutPrintTiming( If_Man_t * p, If_Cut_t * pCut );
extern void            If_CutLift( If_Cut_t * pCut );
extern void            If_CutCopy( If_Man_t * p, If_Cut_t * pCutDest, If_Cut_t * pCutSrc );
extern float           If_CutAreaFlow( If_Man_t * p, If_Cut_t * pCut );
extern float           If_CutEdgeFlow( If_Man_t * p, If_Cut_t * pCut );
extern float           If_CutPowerFlow( If_Man_t * p, If_Cut_t * pCut, If_Obj_t * pRoot );
extern float           If_CutAverageRefs( If_Man_t * p, If_Cut_t * pCut );
extern float           If_CutAreaDeref( If_Man_t * p, If_Cut_t * pCut );
extern float           If_CutAreaRef( If_Man_t * p, If_Cut_t * pCut );
extern float           If_CutAreaDerefed( If_Man_t * p, If_Cut_t * pCut );
extern float           If_CutAreaRefed( If_Man_t * p, If_Cut_t * pCut );
extern float           If_CutEdgeDeref( If_Man_t * p, If_Cut_t * pCut );
extern float           If_CutEdgeRef( If_Man_t * p, If_Cut_t * pCut );
extern float           If_CutEdgeDerefed( If_Man_t * p, If_Cut_t * pCut );
extern float           If_CutEdgeRefed( If_Man_t * p, If_Cut_t * pCut );
extern float           If_CutPowerDeref( If_Man_t * p, If_Cut_t * pCut, If_Obj_t * pRoot );
extern float           If_CutPowerRef( If_Man_t * p, If_Cut_t * pCut, If_Obj_t * pRoot );
extern float           If_CutPowerDerefed( If_Man_t * p, If_Cut_t * pCut, If_Obj_t * pRoot );
extern float           If_CutPowerRefed( If_Man_t * p, If_Cut_t * pCut, If_Obj_t * pRoot );
/*=== ifDec.c =============================================================*/
extern int             If_CutPerformCheck07( If_Man_t * p, unsigned * pTruth, int nVars, int nLeaves, char * pStr );
extern int             If_CutPerformCheck08( If_Man_t * p, unsigned * pTruth, int nVars, int nLeaves, char * pStr );
extern int             If_CutPerformCheck10( If_Man_t * p, unsigned * pTruth, int nVars, int nLeaves, char * pStr );
extern int             If_CutPerformCheck16( If_Man_t * p, unsigned * pTruth, int nVars, int nLeaves, char * pStr );
extern float           If_CutDelayLutStruct( If_Man_t * p, If_Cut_t * pCut, char * pStr, float WireDelay );
extern int             If_CluCheckExt( void * p, word * pTruth, int nVars, int nLutLeaf, int nLutRoot, 
                           char * pLut0, char * pLut1, word * pFunc0, word * pFunc1 );
extern int             If_CluCheckExt3( void * p, word * pTruth, int nVars, int nLutLeaf, int nLutLeaf2, int nLutRoot, 
                           char * pLut0, char * pLut1, char * pLut2, word * pFunc0, word * pFunc1, word * pFunc2 );
/*=== ifLib.c =============================================================*/
extern If_Lib_t *      If_LutLibRead( char * FileName );
extern If_Lib_t *      If_LutLibDup( If_Lib_t * p );
extern void            If_LutLibFree( If_Lib_t * pLutLib );
extern void            If_LutLibPrint( If_Lib_t * pLutLib );
extern int             If_LutLibDelaysAreDiscrete( If_Lib_t * pLutLib );
extern int             If_LutLibDelaysAreDifferent( If_Lib_t * pLutLib );
extern If_Lib_t *      If_SetSimpleLutLib( int nLutSize );
extern float           If_LutLibFastestPinDelay( If_Lib_t * p );
extern float           If_LutLibSlowestPinDelay( If_Lib_t * p );
/*=== ifMan.c =============================================================*/
extern If_Man_t *      If_ManStart( If_Par_t * pPars );
extern void            If_ManRestart( If_Man_t * p );
extern void            If_ManStop( If_Man_t * p );
extern If_Obj_t *      If_ManCreateCi( If_Man_t * p );
extern If_Obj_t *      If_ManCreateCo( If_Man_t * p, If_Obj_t * pDriver );
extern If_Obj_t *      If_ManCreateAnd( If_Man_t * p, If_Obj_t * pFan0, If_Obj_t * pFan1 );
extern If_Obj_t *      If_ManCreateXor( If_Man_t * p, If_Obj_t * pFan0, If_Obj_t * pFan1 );
extern If_Obj_t *      If_ManCreateMux( If_Man_t * p, If_Obj_t * pFan0, If_Obj_t * pFan1, If_Obj_t * pCtrl );
extern void            If_ManCreateChoice( If_Man_t * p, If_Obj_t * pRepr );
extern void            If_ManSetupCutTriv( If_Man_t * p, If_Cut_t * pCut, int ObjId );
extern void            If_ManSetupCiCutSets( If_Man_t * p );
extern If_Set_t *      If_ManSetupNodeCutSet( If_Man_t * p, If_Obj_t * pObj );
extern void            If_ManDerefNodeCutSet( If_Man_t * p, If_Obj_t * pObj );
extern void            If_ManDerefChoiceCutSet( If_Man_t * p, If_Obj_t * pObj );
extern void            If_ManSetupSetAll( If_Man_t * p, int nCrossCut );
/*=== ifMap.c =============================================================*/
extern void            If_ObjPerformMappingAnd( If_Man_t * p, If_Obj_t * pObj, int Mode, int fPreprocess );
extern void            If_ObjPerformMappingChoice( If_Man_t * p, If_Obj_t * pObj, int Mode, int fPreprocess );
extern int             If_ManPerformMappingRound( If_Man_t * p, int nCutsUsed, int Mode, int fPreprocess, char * pLabel );
/*=== ifReduce.c ==========================================================*/
extern void            If_ManImproveMapping( If_Man_t * p );
/*=== ifSeq.c =============================================================*/
extern int             If_ManPerformMappingSeq( If_Man_t * p );
/*=== ifTime.c ============================================================*/
extern int             If_CutDelaySopCost( If_Man_t * p, If_Cut_t * pCut );
extern Vec_Wrd_t *     If_CutDelaySopArray( If_Man_t * p, If_Cut_t * pCut );
extern float           If_CutDelay( If_Man_t * p, If_Obj_t * pObj, If_Cut_t * pCut );
extern void            If_CutPropagateRequired( If_Man_t * p, If_Obj_t * pObj, If_Cut_t * pCut, float Required );
extern void            If_CutRotatePins( If_Man_t * p, If_Cut_t * pCut );
/*=== ifTruth.c ===========================================================*/
extern int             If_CutComputeTruth( If_Man_t * p, If_Cut_t * pCut, If_Cut_t * pCut0, If_Cut_t * pCut1, int fCompl0, int fCompl1 );
extern void            If_CutTruthPermute( unsigned * pOut, unsigned * pIn, int nVars, float * pDelays, int * pVars );
/*=== ifUtil.c ============================================================*/
extern void            If_ManCleanNodeCopy( If_Man_t * p );
extern void            If_ManCleanCutData( If_Man_t * p );
extern void            If_ManCleanMarkV( If_Man_t * p );
extern float           If_ManDelayMax( If_Man_t * p, int fSeq );
extern void            If_ManComputeRequired( If_Man_t * p );
extern float           If_ManScanMapping( If_Man_t * p );
extern float           If_ManScanMappingDirect( If_Man_t * p );
extern float           If_ManScanMappingSeq( If_Man_t * p );
extern void            If_ManResetOriginalRefs( If_Man_t * p );
extern int             If_ManCrossCut( If_Man_t * p );

extern Vec_Ptr_t *     If_ManReverseOrder( If_Man_t * p );
extern void            If_ManMarkMapping( If_Man_t * p );
extern Vec_Ptr_t *     If_ManCollectMappingDirect( If_Man_t * p );
extern Vec_Int_t *     If_ManCollectMappingInt( If_Man_t * p );

extern int             If_ManCountSpecialPos( If_Man_t * p );

/*=== abcRec.c ============================================================*/
extern int             If_CutDelayRecCost(If_Man_t* p, If_Cut_t* pCut, If_Obj_t * pObj);

// othe packages
extern int Bat_ManCellFuncLookup( unsigned * pTruth, int nVars, int nLeaves );

ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

