/**CFile****************************************************************

  FileName    [dar.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: dar.h,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef __DAR_H__
#define __DAR_H__

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

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Dar_Par_t_            Dar_Par_t;
typedef struct Dar_Man_t_            Dar_Man_t;
typedef struct Dar_Obj_t_            Dar_Obj_t;
typedef struct Dar_Cut_t_            Dar_Cut_t;
typedef struct Dar_MmFixed_t_        Dar_MmFixed_t;    
typedef struct Dar_MmFlex_t_         Dar_MmFlex_t;     
typedef struct Dar_MmStep_t_         Dar_MmStep_t;     

// the maximum number of cuts stored at a node
#define DAR_CUT_BASE                 32 

// object types
typedef enum { 
    DAR_AIG_NONE,                    // 0: non-existent object
    DAR_AIG_CONST1,                  // 1: constant 1 
    DAR_AIG_PI,                      // 2: primary input
    DAR_AIG_PO,                      // 3: primary output
    DAR_AIG_BUF,                     // 4: buffer node
    DAR_AIG_AND,                     // 5: AND node
    DAR_AIG_EXOR,                    // 6: EXOR node
    DAR_AIG_LATCH,                   // 7: latch
    DAR_AIG_VOID                     // 8: unused object
} Dar_Type_t;

// the parameters
struct Dar_Par_t_  
{
    int              fUpdateLevel;   
    int              fUseZeros;
    int              fVerbose;
    int              fVeryVerbose;
};

// the AIG 4-cut
struct Dar_Cut_t_  // 8 words
{
    unsigned         uSign;
    unsigned         uTruth  : 16;
    unsigned         nLeaves :  3;
    int              pLeaves[4];
    unsigned char    pIndices[4];
    float            aFlow;
};

// the AIG node
struct Dar_Obj_t_  // 8 words
{
    void *           pData;          // misc (cuts, copy, etc)
    Dar_Obj_t *      pNext;          // strashing table
    Dar_Obj_t *      pFanin0;        // fanin
    Dar_Obj_t *      pFanin1;        // fanin
    unsigned long    Type    :  3;   // object type
    unsigned long    fPhase  :  1;   // value under 000...0 pattern
    unsigned long    fMarkA  :  1;   // multipurpose mask
    unsigned long    fMarkB  :  1;   // multipurpose mask
    unsigned long    nRefs   : 26;   // reference count 
    unsigned         Level   : 24;   // the level of this node
    unsigned         nCuts   :  8;   // the number of cuts
    int              TravId;         // unique ID of last traversal involving the node
    int              Id;             // unique ID of the node
};

// the AIG manager
struct Dar_Man_t_
{
    // parameters governing rewriting
    Dar_Par_t *      pPars; 
    // AIG nodes
    Vec_Ptr_t *      vPis;           // the array of PIs
    Vec_Ptr_t *      vPos;           // the array of POs
    Vec_Ptr_t *      vObjs;          // the array of all nodes (optional)
    Dar_Obj_t *      pConst1;        // the constant 1 node
    Dar_Obj_t        Ghost;          // the ghost node
    // AIG node counters
    int              nObjs[DAR_AIG_VOID];// the number of objects by type
    int              nCreated;       // the number of created objects
    int              nDeleted;       // the number of deleted objects
    // structural hash table
    Dar_Obj_t **     pTable;         // structural hash table
    int              nTableSize;     // structural hash table size
    // 4-input cuts of the nodes
    Dar_Cut_t *      pBaseCuts[DAR_CUT_BASE];
    Dar_Cut_t        BaseCuts[DAR_CUT_BASE];
    int              nBaseCuts;
    int              nCutsUsed;
    // current rewriting step
    Vec_Ptr_t *      vLeavesBest;    // the best set of leaves
    int              OutBest;        // the best output (in the library)
    int              GainBest;       // the best gain
    // various data members
    Dar_MmFixed_t *  pMemObjs;       // memory manager for objects
    Dar_MmFlex_t *   pMemCuts;       // memory manager for cuts
    Vec_Int_t *      vRequired;      // the required times
    void *           pData;          // the temporary data
    int              nTravIds;       // the current traversal ID
    int              fCatchExor;     // enables EXOR nodes
    // rewriting statistics
    int              nCutsBad;
    int              nCutsGood;
    // timing statistics
    int              time1;
    int              time2;
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

#define DAR_MIN(a,b)       (((a) < (b))? (a) : (b))
#define DAR_MAX(a,b)       (((a) > (b))? (a) : (b))

#ifndef PRT
#define PRT(a,t)  printf("%s = ", (a)); printf("%6.2f sec\n", (float)(t)/(float)(CLOCKS_PER_SEC))
#endif

static inline int          Dar_BitWordNum( int nBits )            { return (nBits>>5) + ((nBits&31) > 0);           }
static inline int          Dar_TruthWordNum( int nVars )          { return nVars <= 5 ? 1 : (1 << (nVars - 5));     }
static inline int          Dar_InfoHasBit( unsigned * p, int i )  { return (p[(i)>>5] & (1<<((i) & 31))) > 0;       }
static inline void         Dar_InfoSetBit( unsigned * p, int i )  { p[(i)>>5] |= (1<<((i) & 31));                   }
static inline void         Dar_InfoXorBit( unsigned * p, int i )  { p[(i)>>5] ^= (1<<((i) & 31));                   }

static inline Dar_Obj_t *  Dar_Regular( Dar_Obj_t * p )           { return (Dar_Obj_t *)((unsigned long)(p) & ~01);      }
static inline Dar_Obj_t *  Dar_Not( Dar_Obj_t * p )               { return (Dar_Obj_t *)((unsigned long)(p) ^  01);      }
static inline Dar_Obj_t *  Dar_NotCond( Dar_Obj_t * p, int c )    { return (Dar_Obj_t *)((unsigned long)(p) ^ (c));      }
static inline int          Dar_IsComplement( Dar_Obj_t * p )      { return (int )(((unsigned long)p) & 01);              }

static inline Dar_Obj_t *  Dar_ManConst0( Dar_Man_t * p )         { return Dar_Not(p->pConst1);                     }
static inline Dar_Obj_t *  Dar_ManConst1( Dar_Man_t * p )         { return p->pConst1;                              }
static inline Dar_Obj_t *  Dar_ManGhost( Dar_Man_t * p )          { return &p->Ghost;                               }
static inline Dar_Obj_t *  Dar_ManPi( Dar_Man_t * p, int i )      { return (Dar_Obj_t *)Vec_PtrEntry(p->vPis, i);   }
static inline Dar_Obj_t *  Dar_ManPo( Dar_Man_t * p, int i )      { return (Dar_Obj_t *)Vec_PtrEntry(p->vPos, i);   }
static inline Dar_Obj_t *  Dar_ManObj( Dar_Man_t * p, int i )     { return p->vObjs ? (Dar_Obj_t *)Vec_PtrEntry(p->vObjs, i) : NULL;  }

static inline int          Dar_ManPiNum( Dar_Man_t * p )          { return p->nObjs[DAR_AIG_PI];                    }
static inline int          Dar_ManPoNum( Dar_Man_t * p )          { return p->nObjs[DAR_AIG_PO];                    }
static inline int          Dar_ManBufNum( Dar_Man_t * p )         { return p->nObjs[DAR_AIG_BUF];                   }
static inline int          Dar_ManAndNum( Dar_Man_t * p )         { return p->nObjs[DAR_AIG_AND];                   }
static inline int          Dar_ManExorNum( Dar_Man_t * p )        { return p->nObjs[DAR_AIG_EXOR];                  }
static inline int          Dar_ManLatchNum( Dar_Man_t * p )       { return p->nObjs[DAR_AIG_LATCH];                 }
static inline int          Dar_ManNodeNum( Dar_Man_t * p )        { return p->nObjs[DAR_AIG_AND]+p->nObjs[DAR_AIG_EXOR];   }
static inline int          Dar_ManGetCost( Dar_Man_t * p )        { return p->nObjs[DAR_AIG_AND]+3*p->nObjs[DAR_AIG_EXOR]; }
static inline int          Dar_ManObjNum( Dar_Man_t * p )         { return p->nCreated - p->nDeleted;               }

static inline Dar_Type_t   Dar_ObjType( Dar_Obj_t * pObj )        { return (Dar_Type_t)pObj->Type;               }
static inline int          Dar_ObjIsNone( Dar_Obj_t * pObj )      { return pObj->Type == DAR_AIG_NONE;   }
static inline int          Dar_ObjIsConst1( Dar_Obj_t * pObj )    { assert(!Dar_IsComplement(pObj)); return pObj->Type == DAR_AIG_CONST1; }
static inline int          Dar_ObjIsPi( Dar_Obj_t * pObj )        { return pObj->Type == DAR_AIG_PI;     }
static inline int          Dar_ObjIsPo( Dar_Obj_t * pObj )        { return pObj->Type == DAR_AIG_PO;     }
static inline int          Dar_ObjIsBuf( Dar_Obj_t * pObj )       { return pObj->Type == DAR_AIG_BUF;    }
static inline int          Dar_ObjIsAnd( Dar_Obj_t * pObj )       { return pObj->Type == DAR_AIG_AND;    }
static inline int          Dar_ObjIsExor( Dar_Obj_t * pObj )      { return pObj->Type == DAR_AIG_EXOR;   }
static inline int          Dar_ObjIsLatch( Dar_Obj_t * pObj )     { return pObj->Type == DAR_AIG_LATCH;  }
static inline int          Dar_ObjIsNode( Dar_Obj_t * pObj )      { return pObj->Type == DAR_AIG_AND || pObj->Type == DAR_AIG_EXOR;   }
static inline int          Dar_ObjIsTerm( Dar_Obj_t * pObj )      { return pObj->Type == DAR_AIG_PI  || pObj->Type == DAR_AIG_PO || pObj->Type == DAR_AIG_CONST1;  }
static inline int          Dar_ObjIsHash( Dar_Obj_t * pObj )      { return pObj->Type == DAR_AIG_AND || pObj->Type == DAR_AIG_EXOR || pObj->Type == DAR_AIG_LATCH; }

static inline int          Dar_ObjIsMarkA( Dar_Obj_t * pObj )     { return pObj->fMarkA;  }
static inline void         Dar_ObjSetMarkA( Dar_Obj_t * pObj )    { pObj->fMarkA = 1;     }
static inline void         Dar_ObjClearMarkA( Dar_Obj_t * pObj )  { pObj->fMarkA = 0;     }
 
static inline void         Dar_ObjSetTravId( Dar_Obj_t * pObj, int TravId )                { pObj->TravId = TravId;                         }
static inline void         Dar_ObjSetTravIdCurrent( Dar_Man_t * p, Dar_Obj_t * pObj )      { pObj->TravId = p->nTravIds;                    }
static inline void         Dar_ObjSetTravIdPrevious( Dar_Man_t * p, Dar_Obj_t * pObj )     { pObj->TravId = p->nTravIds - 1;                }
static inline int          Dar_ObjIsTravIdCurrent( Dar_Man_t * p, Dar_Obj_t * pObj )       { return (int)(pObj->TravId == p->nTravIds);     }
static inline int          Dar_ObjIsTravIdPrevious( Dar_Man_t * p, Dar_Obj_t * pObj )      { return (int)(pObj->TravId == p->nTravIds - 1); }

static inline int          Dar_ObjTravId( Dar_Obj_t * pObj )      { return (int)pObj->pData;                       }
static inline int          Dar_ObjPhase( Dar_Obj_t * pObj )       { return pObj->fPhase;                           }
static inline int          Dar_ObjRefs( Dar_Obj_t * pObj )        { return pObj->nRefs;                            }
static inline void         Dar_ObjRef( Dar_Obj_t * pObj )         { pObj->nRefs++;                                 }
static inline void         Dar_ObjDeref( Dar_Obj_t * pObj )       { assert( pObj->nRefs > 0 ); pObj->nRefs--;      }
static inline void         Dar_ObjClearRef( Dar_Obj_t * pObj )    { pObj->nRefs = 0;                               }
static inline int          Dar_ObjFaninC0( Dar_Obj_t * pObj )     { return Dar_IsComplement(pObj->pFanin0);        }
static inline int          Dar_ObjFaninC1( Dar_Obj_t * pObj )     { return Dar_IsComplement(pObj->pFanin1);        }
static inline Dar_Obj_t *  Dar_ObjFanin0( Dar_Obj_t * pObj )      { return Dar_Regular(pObj->pFanin0);             }
static inline Dar_Obj_t *  Dar_ObjFanin1( Dar_Obj_t * pObj )      { return Dar_Regular(pObj->pFanin1);             }
static inline Dar_Obj_t *  Dar_ObjChild0( Dar_Obj_t * pObj )      { return pObj->pFanin0;                          }
static inline Dar_Obj_t *  Dar_ObjChild1( Dar_Obj_t * pObj )      { return pObj->pFanin1;                          }
static inline Dar_Obj_t *  Dar_ObjChild0Copy( Dar_Obj_t * pObj ) { assert( !Dar_IsComplement(pObj) ); return Dar_ObjFanin0(pObj)? Dar_NotCond((Dar_Obj_t *)Dar_ObjFanin0(pObj)->pData, Dar_ObjFaninC0(pObj)) : NULL;  }
static inline Dar_Obj_t *  Dar_ObjChild1Copy( Dar_Obj_t * pObj ) { assert( !Dar_IsComplement(pObj) ); return Dar_ObjFanin1(pObj)? Dar_NotCond((Dar_Obj_t *)Dar_ObjFanin1(pObj)->pData, Dar_ObjFaninC1(pObj)) : NULL;  }
static inline int          Dar_ObjLevel( Dar_Obj_t * pObj )       { return pObj->nRefs;                            }
static inline int          Dar_ObjLevelNew( Dar_Obj_t * pObj )    { return 1 + Dar_ObjIsExor(pObj) + DAR_MAX(Dar_ObjFanin0(pObj)->Level, Dar_ObjFanin1(pObj)->Level);       }
static inline int          Dar_ObjFaninPhase( Dar_Obj_t * pObj )  { return Dar_Regular(pObj)->fPhase ^ Dar_IsComplement(pObj); }
static inline void         Dar_ObjClean( Dar_Obj_t * pObj )       { memset( pObj, 0, sizeof(Dar_Obj_t) ); }
static inline int          Dar_ObjWhatFanin( Dar_Obj_t * pObj, Dar_Obj_t * pFanin )    
{ 
    if ( Dar_ObjFanin0(pObj) == pFanin ) return 0; 
    if ( Dar_ObjFanin1(pObj) == pFanin ) return 1; 
    assert(0); return -1; 
}
static inline int          Dar_ObjFanoutC( Dar_Obj_t * pObj, Dar_Obj_t * pFanout )    
{ 
    if ( Dar_ObjFanin0(pFanout) == pObj ) return Dar_ObjFaninC0(pObj); 
    if ( Dar_ObjFanin1(pFanout) == pObj ) return Dar_ObjFaninC1(pObj); 
    assert(0); return -1; 
}

// create the ghost of the new node
static inline Dar_Obj_t *  Dar_ObjCreateGhost( Dar_Man_t * p, Dar_Obj_t * p0, Dar_Obj_t * p1, Dar_Type_t Type )    
{
    Dar_Obj_t * pGhost;
    assert( Type != DAR_AIG_AND || !Dar_ObjIsConst1(Dar_Regular(p0)) );
    assert( p1 == NULL || !Dar_ObjIsConst1(Dar_Regular(p1)) );
    assert( Type == DAR_AIG_PI || Dar_Regular(p0) != Dar_Regular(p1) );
    pGhost = Dar_ManGhost(p);
    pGhost->Type = Type;
    if ( p1 == NULL || Dar_Regular(p0)->Id < Dar_Regular(p1)->Id )
    {
        pGhost->pFanin0 = p0;
        pGhost->pFanin1 = p1;
    }
    else
    {
        pGhost->pFanin0 = p1;
        pGhost->pFanin1 = p0;
    }
    return pGhost;
}

// internal memory manager
static inline Dar_Obj_t * Dar_ManFetchMemory( Dar_Man_t * p )  
{
    extern char * Dar_MmFixedEntryFetch( Dar_MmFixed_t * p );
    Dar_Obj_t * pTemp;
    pTemp = (Dar_Obj_t *)Dar_MmFixedEntryFetch( p->pMemObjs );
    memset( pTemp, 0, sizeof(Dar_Obj_t) ); 
    Vec_PtrPush( p->vObjs, pTemp );
    pTemp->Id = p->nCreated++;
    return pTemp;
}
static inline void Dar_ManRecycleMemory( Dar_Man_t * p, Dar_Obj_t * pEntry )
{
    extern void Dar_MmFixedEntryRecycle( Dar_MmFixed_t * p, char * pEntry );
    p->nDeleted++;
    pEntry->Type = DAR_AIG_NONE; // distinquishes a dead node from a live node
    Dar_MmFixedEntryRecycle( p->pMemObjs, (char *)pEntry );
}


////////////////////////////////////////////////////////////////////////
///                             ITERATORS                            ///
////////////////////////////////////////////////////////////////////////

// iterator over the primary inputs
#define Dar_ManForEachPi( p, pObj, i )                                          \
    Vec_PtrForEachEntry( p->vPis, pObj, i )
// iterator over the primary outputs
#define Dar_ManForEachPo( p, pObj, i )                                          \
    Vec_PtrForEachEntry( p->vPos, pObj, i )
// iterator over all objects, including those currently not used
#define Dar_ManForEachObj( p, pObj, i )                                         \
    Vec_PtrForEachEntry( p->vObjs, pObj, i ) if ( (pObj) == NULL ) {} else

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== darBalance.c ========================================================*/
extern Dar_Man_t *     Dar_ManBalance( Dar_Man_t * p, int fUpdateLevel );
extern Dar_Obj_t *     Dar_NodeBalanceBuildSuper( Dar_Man_t * p, Vec_Ptr_t * vSuper, Dar_Type_t Type, int fUpdateLevel );
/*=== darCheck.c ========================================================*/
extern int             Dar_ManCheck( Dar_Man_t * p );
/*=== darCore.c ========================================================*/
extern int             Dar_ManRewrite( Dar_Man_t * p );
/*=== darCut.c ========================================================*/
extern void            Dar_ManSetupPis( Dar_Man_t * p );
extern void            Dar_ObjComputeCuts_rec( Dar_Man_t * p, Dar_Obj_t * pObj );
extern void            Dar_ManCutsFree( Dar_Man_t * p );
/*=== darData.c ========================================================*/
extern Vec_Int_t *     Dar_LibReadNodes();
extern Vec_Int_t *     Dar_LibReadOuts();
/*=== darDfs.c ==========================================================*/
extern Vec_Ptr_t *     Dar_ManDfs( Dar_Man_t * p );
extern int             Dar_ManCountLevels( Dar_Man_t * p );
extern void            Dar_ManCreateRefs( Dar_Man_t * p );
extern int             Dar_DagSize( Dar_Obj_t * pObj );
extern void            Dar_ConeUnmark_rec( Dar_Obj_t * pObj );
extern Dar_Obj_t *     Dar_Transfer( Dar_Man_t * pSour, Dar_Man_t * pDest, Dar_Obj_t * pObj, int nVars );
extern Dar_Obj_t *     Dar_Compose( Dar_Man_t * p, Dar_Obj_t * pRoot, Dar_Obj_t * pFunc, int iVar );
/*=== darLib.c ==========================================================*/
extern void            Dar_LibStart();
extern void            Dar_LibStop();
extern int             Dar_LibEval( Dar_Man_t * p, Dar_Obj_t * pRoot, Dar_Cut_t * pCut, int Required );
extern Dar_Obj_t *     Dar_LibBuildBest( Dar_Man_t * p );
/*=== darMan.c ==========================================================*/
extern Dar_Man_t *     Dar_ManStart();
extern Dar_Man_t *     Dar_ManDup( Dar_Man_t * p );
extern void            Dar_ManStop( Dar_Man_t * p );
extern int             Dar_ManCleanup( Dar_Man_t * p );
extern void            Dar_ManPrintStats( Dar_Man_t * p );
/*=== darMem.c ==========================================================*/
extern void            Dar_ManStartMemory( Dar_Man_t * p );
extern void            Dar_ManStopMemory( Dar_Man_t * p );
/*=== darObj.c ==========================================================*/
extern Dar_Obj_t *     Dar_ObjCreatePi( Dar_Man_t * p );
extern Dar_Obj_t *     Dar_ObjCreatePo( Dar_Man_t * p, Dar_Obj_t * pDriver );
extern Dar_Obj_t *     Dar_ObjCreate( Dar_Man_t * p, Dar_Obj_t * pGhost );
extern void            Dar_ObjConnect( Dar_Man_t * p, Dar_Obj_t * pObj, Dar_Obj_t * pFan0, Dar_Obj_t * pFan1 );
extern void            Dar_ObjDisconnect( Dar_Man_t * p, Dar_Obj_t * pObj );
extern void            Dar_ObjDelete( Dar_Man_t * p, Dar_Obj_t * pObj );
extern void            Dar_ObjDelete_rec( Dar_Man_t * p, Dar_Obj_t * pObj, int fFreeTop );
extern void            Dar_ObjPatchFanin0( Dar_Man_t * p, Dar_Obj_t * pObj, Dar_Obj_t * pFaninNew );
extern void            Dar_ObjReplace( Dar_Man_t * p, Dar_Obj_t * pObjOld, Dar_Obj_t * pObjNew, int fNodesOnly );
/*=== darOper.c =========================================================*/
extern Dar_Obj_t *     Dar_IthVar( Dar_Man_t * p, int i );
extern Dar_Obj_t *     Dar_Oper( Dar_Man_t * p, Dar_Obj_t * p0, Dar_Obj_t * p1, Dar_Type_t Type );
extern Dar_Obj_t *     Dar_And( Dar_Man_t * p, Dar_Obj_t * p0, Dar_Obj_t * p1 );
extern Dar_Obj_t *     Dar_Latch( Dar_Man_t * p, Dar_Obj_t * pObj, int fInitOne );
extern Dar_Obj_t *     Dar_Or( Dar_Man_t * p, Dar_Obj_t * p0, Dar_Obj_t * p1 );
extern Dar_Obj_t *     Dar_Exor( Dar_Man_t * p, Dar_Obj_t * p0, Dar_Obj_t * p1 );
extern Dar_Obj_t *     Dar_Mux( Dar_Man_t * p, Dar_Obj_t * pC, Dar_Obj_t * p1, Dar_Obj_t * p0 );
extern Dar_Obj_t *     Dar_Maj( Dar_Man_t * p, Dar_Obj_t * pA, Dar_Obj_t * pB, Dar_Obj_t * pC );
extern Dar_Obj_t *     Dar_Miter( Dar_Man_t * p, Vec_Ptr_t * vPairs );
extern Dar_Obj_t *     Dar_CreateAnd( Dar_Man_t * p, int nVars );
extern Dar_Obj_t *     Dar_CreateOr( Dar_Man_t * p, int nVars );
extern Dar_Obj_t *     Dar_CreateExor( Dar_Man_t * p, int nVars );
/*=== darSeq.c ========================================================*/
extern int             Dar_ManSeqStrash( Dar_Man_t * p, int nLatches, int * pInits );
/*=== darTable.c ========================================================*/
extern Dar_Obj_t *     Dar_TableLookup( Dar_Man_t * p, Dar_Obj_t * pGhost );
extern void            Dar_TableInsert( Dar_Man_t * p, Dar_Obj_t * pObj );
extern void            Dar_TableDelete( Dar_Man_t * p, Dar_Obj_t * pObj );
extern int             Dar_TableCountEntries( Dar_Man_t * p );
extern void            Dar_TableProfile( Dar_Man_t * p );
/*=== darUtil.c =========================================================*/
extern Dar_Par_t *     Dar_ManDefaultParams();
extern void            Dar_ManIncrementTravId( Dar_Man_t * p );
extern void            Dar_ManCleanData( Dar_Man_t * p );
extern void            Dar_ObjCleanData_rec( Dar_Obj_t * pObj );
extern void            Dar_ObjCollectMulti( Dar_Obj_t * pFunc, Vec_Ptr_t * vSuper );
extern int             Dar_ObjIsMuxType( Dar_Obj_t * pObj );
extern int             Dar_ObjRecognizeExor( Dar_Obj_t * pObj, Dar_Obj_t ** ppFan0, Dar_Obj_t ** ppFan1 );
extern Dar_Obj_t *     Dar_ObjRecognizeMux( Dar_Obj_t * pObj, Dar_Obj_t ** ppObjT, Dar_Obj_t ** ppObjE );
extern void            Dar_ObjPrintEqn( FILE * pFile, Dar_Obj_t * pObj, Vec_Vec_t * vLevels, int Level );
extern void            Dar_ObjPrintVerilog( FILE * pFile, Dar_Obj_t * pObj, Vec_Vec_t * vLevels, int Level );
extern void            Dar_ObjPrintVerbose( Dar_Obj_t * pObj, int fHaig );
extern void            Dar_ManPrintVerbose( Dar_Man_t * p, int fHaig );
extern void            Dar_ManDumpBlif( Dar_Man_t * p, char * pFileName );
 
/*=== darMem.c ===========================================================*/
// fixed-size-block memory manager
extern Dar_MmFixed_t * Dar_MmFixedStart( int nEntrySize, int nEntriesMax );
extern void            Dar_MmFixedStop( Dar_MmFixed_t * p, int fVerbose );
extern char *          Dar_MmFixedEntryFetch( Dar_MmFixed_t * p );
extern void            Dar_MmFixedEntryRecycle( Dar_MmFixed_t * p, char * pEntry );
extern void            Dar_MmFixedRestart( Dar_MmFixed_t * p );
extern int             Dar_MmFixedReadMemUsage( Dar_MmFixed_t * p );
extern int             Dar_MmFixedReadMaxEntriesUsed( Dar_MmFixed_t * p );
// flexible-size-block memory manager
extern Dar_MmFlex_t *  Dar_MmFlexStart();
extern void            Dar_MmFlexStop( Dar_MmFlex_t * p, int fVerbose );
extern char *          Dar_MmFlexEntryFetch( Dar_MmFlex_t * p, int nBytes );
extern void            Dar_MmFlexRestart( Dar_MmFlex_t * p );
extern int             Dar_MmFlexReadMemUsage( Dar_MmFlex_t * p );
// hierarchical memory manager
extern Dar_MmStep_t *  Dar_MmStepStart( int nSteps );
extern void            Dar_MmStepStop( Dar_MmStep_t * p, int fVerbose );
extern char *          Dar_MmStepEntryFetch( Dar_MmStep_t * p, int nBytes );
extern void            Dar_MmStepEntryRecycle( Dar_MmStep_t * p, char * pEntry, int nBytes );
extern int             Dar_MmStepReadMemUsage( Dar_MmStep_t * p );

#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

