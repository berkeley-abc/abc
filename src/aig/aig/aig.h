/**CFile****************************************************************

  FileName    [aig.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [AIG package.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: aig.h,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef __AIG_H__
#define __AIG_H__

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

typedef struct Aig_Man_t_            Aig_Man_t;
typedef struct Aig_Obj_t_            Aig_Obj_t;
typedef struct Aig_MmFixed_t_        Aig_MmFixed_t;    
typedef struct Aig_MmFlex_t_         Aig_MmFlex_t;     
typedef struct Aig_MmStep_t_         Aig_MmStep_t;     

// object types
typedef enum { 
    AIG_OBJ_NONE,                    // 0: non-existent object
    AIG_OBJ_CONST1,                  // 1: constant 1 
    AIG_OBJ_PI,                      // 2: primary input
    AIG_OBJ_PO,                      // 3: primary output
    AIG_OBJ_BUF,                     // 4: buffer node
    AIG_OBJ_AND,                     // 5: AND node
    AIG_OBJ_EXOR,                    // 6: EXOR node
    AIG_OBJ_LATCH,                   // 7: latch
    AIG_OBJ_VOID                     // 8: unused object
} Aig_Type_t;

// the AIG node
struct Aig_Obj_t_  // 8 words
{
    void *           pData;          // misc (cuts, copy, etc)
    Aig_Obj_t *      pNext;          // strashing table
    Aig_Obj_t *      pFanin0;        // fanin
    Aig_Obj_t *      pFanin1;        // fanin
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
struct Aig_Man_t_
{
    // AIG nodes
    Vec_Ptr_t *      vPis;           // the array of PIs
    Vec_Ptr_t *      vPos;           // the array of POs
    Vec_Ptr_t *      vObjs;          // the array of all nodes (optional)
    Vec_Ptr_t *      vBufs;          // the array of buffers
    Aig_Obj_t *      pConst1;        // the constant 1 node
    Aig_Obj_t        Ghost;          // the ghost node
    // AIG node counters
    int              nObjs[AIG_OBJ_VOID];// the number of objects by type
    int              nCreated;       // the number of created objects
    int              nDeleted;       // the number of deleted objects
    // structural hash table
    Aig_Obj_t **     pTable;         // structural hash table
    int              nTableSize;     // structural hash table size
    // representation of fanouts
    int *            pFanData;       // the database to store fanout information
    int              nFansAlloc;     // the size of fanout representation
    Vec_Vec_t *      vLevels;        // used to update timing information
    int              nBufReplaces;   // the number of times replacement led to a buffer
    int              nBufFixes;      // the number of times buffers were propagated
    int              nBufMax;        // the maximum number of buffers during computation
    // various data members
    Aig_MmFixed_t *  pMemObjs;       // memory manager for objects
    Vec_Int_t *      vLevelR;        // the reverse level of the nodes
    int              nLevelMax;      // maximum number of levels
    void *           pData;          // the temporary data
    int              nTravIds;       // the current traversal ID
    int              fCatchExor;     // enables EXOR nodes
    // timing statistics
    int              time1;
    int              time2;
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

#define AIG_MIN(a,b)       (((a) < (b))? (a) : (b))
#define AIG_MAX(a,b)       (((a) > (b))? (a) : (b))
#define AIG_INFINITY       (100000000)

#ifndef PRT
#define PRT(a,t)  printf("%s = ", (a)); printf("%6.2f sec\n", (float)(t)/(float)(CLOCKS_PER_SEC))
#endif

static inline int          Aig_BitWordNum( int nBits )            { return (nBits>>5) + ((nBits&31) > 0);           }
static inline int          Aig_TruthWordNum( int nVars )          { return nVars <= 5 ? 1 : (1 << (nVars - 5));     }
static inline int          Aig_InfoHasBit( unsigned * p, int i )  { return (p[(i)>>5] & (1<<((i) & 31))) > 0;       }
static inline void         Aig_InfoSetBit( unsigned * p, int i )  { p[(i)>>5] |= (1<<((i) & 31));                   }
static inline void         Aig_InfoXorBit( unsigned * p, int i )  { p[(i)>>5] ^= (1<<((i) & 31));                   }
static inline unsigned     Aig_ObjCutSign( unsigned ObjId )       { return (1 << (ObjId & 31));                     }

static inline Aig_Obj_t *  Aig_Regular( Aig_Obj_t * p )           { return (Aig_Obj_t *)((unsigned long)(p) & ~01); }
static inline Aig_Obj_t *  Aig_Not( Aig_Obj_t * p )               { return (Aig_Obj_t *)((unsigned long)(p) ^  01); }
static inline Aig_Obj_t *  Aig_NotCond( Aig_Obj_t * p, int c )    { return (Aig_Obj_t *)((unsigned long)(p) ^ (c)); }
static inline int          Aig_IsComplement( Aig_Obj_t * p )      { return (int )(((unsigned long)p) & 01);         }

static inline Aig_Obj_t *  Aig_ManConst0( Aig_Man_t * p )         { return Aig_Not(p->pConst1);                     }
static inline Aig_Obj_t *  Aig_ManConst1( Aig_Man_t * p )         { return p->pConst1;                              }
static inline Aig_Obj_t *  Aig_ManGhost( Aig_Man_t * p )          { return &p->Ghost;                               }
static inline Aig_Obj_t *  Aig_ManPi( Aig_Man_t * p, int i )      { return (Aig_Obj_t *)Vec_PtrEntry(p->vPis, i);   }
static inline Aig_Obj_t *  Aig_ManPo( Aig_Man_t * p, int i )      { return (Aig_Obj_t *)Vec_PtrEntry(p->vPos, i);   }
static inline Aig_Obj_t *  Aig_ManObj( Aig_Man_t * p, int i )     { return p->vObjs ? (Aig_Obj_t *)Vec_PtrEntry(p->vObjs, i) : NULL;  }

static inline int          Aig_ManPiNum( Aig_Man_t * p )          { return p->nObjs[AIG_OBJ_PI];                    }
static inline int          Aig_ManPoNum( Aig_Man_t * p )          { return p->nObjs[AIG_OBJ_PO];                    }
static inline int          Aig_ManBufNum( Aig_Man_t * p )         { return p->nObjs[AIG_OBJ_BUF];                   }
static inline int          Aig_ManAndNum( Aig_Man_t * p )         { return p->nObjs[AIG_OBJ_AND];                   }
static inline int          Aig_ManExorNum( Aig_Man_t * p )        { return p->nObjs[AIG_OBJ_EXOR];                  }
static inline int          Aig_ManLatchNum( Aig_Man_t * p )       { return p->nObjs[AIG_OBJ_LATCH];                 }
static inline int          Aig_ManNodeNum( Aig_Man_t * p )        { return p->nObjs[AIG_OBJ_AND]+p->nObjs[AIG_OBJ_EXOR];   }
static inline int          Aig_ManGetCost( Aig_Man_t * p )        { return p->nObjs[AIG_OBJ_AND]+3*p->nObjs[AIG_OBJ_EXOR]; }
static inline int          Aig_ManObjNum( Aig_Man_t * p )         { return p->nCreated - p->nDeleted;               }
static inline int          Aig_ManObjIdMax( Aig_Man_t * p )       { return Vec_PtrSize(p->vObjs);                   }

static inline Aig_Type_t   Aig_ObjType( Aig_Obj_t * pObj )        { return (Aig_Type_t)pObj->Type;               }
static inline int          Aig_ObjIsNone( Aig_Obj_t * pObj )      { return pObj->Type == AIG_OBJ_NONE;   }
static inline int          Aig_ObjIsConst1( Aig_Obj_t * pObj )    { assert(!Aig_IsComplement(pObj)); return pObj->Type == AIG_OBJ_CONST1; }
static inline int          Aig_ObjIsPi( Aig_Obj_t * pObj )        { return pObj->Type == AIG_OBJ_PI;     }
static inline int          Aig_ObjIsPo( Aig_Obj_t * pObj )        { return pObj->Type == AIG_OBJ_PO;     }
static inline int          Aig_ObjIsBuf( Aig_Obj_t * pObj )       { return pObj->Type == AIG_OBJ_BUF;    }
static inline int          Aig_ObjIsAnd( Aig_Obj_t * pObj )       { return pObj->Type == AIG_OBJ_AND;    }
static inline int          Aig_ObjIsExor( Aig_Obj_t * pObj )      { return pObj->Type == AIG_OBJ_EXOR;   }
static inline int          Aig_ObjIsLatch( Aig_Obj_t * pObj )     { return pObj->Type == AIG_OBJ_LATCH;  }
static inline int          Aig_ObjIsNode( Aig_Obj_t * pObj )      { return pObj->Type == AIG_OBJ_AND || pObj->Type == AIG_OBJ_EXOR;   }
static inline int          Aig_ObjIsTerm( Aig_Obj_t * pObj )      { return pObj->Type == AIG_OBJ_PI  || pObj->Type == AIG_OBJ_PO || pObj->Type == AIG_OBJ_CONST1;  }
static inline int          Aig_ObjIsHash( Aig_Obj_t * pObj )      { return pObj->Type == AIG_OBJ_AND || pObj->Type == AIG_OBJ_EXOR || pObj->Type == AIG_OBJ_LATCH; }

static inline int          Aig_ObjIsMarkA( Aig_Obj_t * pObj )     { return pObj->fMarkA;  }
static inline void         Aig_ObjSetMarkA( Aig_Obj_t * pObj )    { pObj->fMarkA = 1;     }
static inline void         Aig_ObjClearMarkA( Aig_Obj_t * pObj )  { pObj->fMarkA = 0;     }
 
static inline void         Aig_ObjSetTravId( Aig_Obj_t * pObj, int TravId )                { pObj->TravId = TravId;                         }
static inline void         Aig_ObjSetTravIdCurrent( Aig_Man_t * p, Aig_Obj_t * pObj )      { pObj->TravId = p->nTravIds;                    }
static inline void         Aig_ObjSetTravIdPrevious( Aig_Man_t * p, Aig_Obj_t * pObj )     { pObj->TravId = p->nTravIds - 1;                }
static inline int          Aig_ObjIsTravIdCurrent( Aig_Man_t * p, Aig_Obj_t * pObj )       { return (int)(pObj->TravId == p->nTravIds);     }
static inline int          Aig_ObjIsTravIdPrevious( Aig_Man_t * p, Aig_Obj_t * pObj )      { return (int)(pObj->TravId == p->nTravIds - 1); }

static inline int          Aig_ObjTravId( Aig_Obj_t * pObj )      { return (int)pObj->pData;                       }
static inline int          Aig_ObjPhase( Aig_Obj_t * pObj )       { return pObj->fPhase;                           }
static inline int          Aig_ObjRefs( Aig_Obj_t * pObj )        { return pObj->nRefs;                            }
static inline void         Aig_ObjRef( Aig_Obj_t * pObj )         { pObj->nRefs++;                                 }
static inline void         Aig_ObjDeref( Aig_Obj_t * pObj )       { assert( pObj->nRefs > 0 ); pObj->nRefs--;      }
static inline void         Aig_ObjClearRef( Aig_Obj_t * pObj )    { pObj->nRefs = 0;                               }
static inline int          Aig_ObjFaninC0( Aig_Obj_t * pObj )     { return Aig_IsComplement(pObj->pFanin0);        }
static inline int          Aig_ObjFaninC1( Aig_Obj_t * pObj )     { return Aig_IsComplement(pObj->pFanin1);        }
static inline Aig_Obj_t *  Aig_ObjFanin0( Aig_Obj_t * pObj )      { return Aig_Regular(pObj->pFanin0);             }
static inline Aig_Obj_t *  Aig_ObjFanin1( Aig_Obj_t * pObj )      { return Aig_Regular(pObj->pFanin1);             }
static inline Aig_Obj_t *  Aig_ObjChild0( Aig_Obj_t * pObj )      { return pObj->pFanin0;                          }
static inline Aig_Obj_t *  Aig_ObjChild1( Aig_Obj_t * pObj )      { return pObj->pFanin1;                          }
static inline Aig_Obj_t *  Aig_ObjChild0Copy( Aig_Obj_t * pObj ) { assert( !Aig_IsComplement(pObj) ); return Aig_ObjFanin0(pObj)? Aig_NotCond((Aig_Obj_t *)Aig_ObjFanin0(pObj)->pData, Aig_ObjFaninC0(pObj)) : NULL;  }
static inline Aig_Obj_t *  Aig_ObjChild1Copy( Aig_Obj_t * pObj ) { assert( !Aig_IsComplement(pObj) ); return Aig_ObjFanin1(pObj)? Aig_NotCond((Aig_Obj_t *)Aig_ObjFanin1(pObj)->pData, Aig_ObjFaninC1(pObj)) : NULL;  }
static inline int          Aig_ObjLevel( Aig_Obj_t * pObj )       { return pObj->nRefs;                            }
static inline int          Aig_ObjLevelNew( Aig_Obj_t * pObj )    { return Aig_ObjFanin1(pObj)? 1 + Aig_ObjIsExor(pObj) + AIG_MAX(Aig_ObjFanin0(pObj)->Level, Aig_ObjFanin1(pObj)->Level) : Aig_ObjFanin0(pObj)->Level; }
static inline int          Aig_ObjFaninPhase( Aig_Obj_t * pObj )  { return pObj? Aig_Regular(pObj)->fPhase ^ Aig_IsComplement(pObj) : 0;                              }
static inline void         Aig_ObjClean( Aig_Obj_t * pObj )       { memset( pObj, 0, sizeof(Aig_Obj_t) );                                                             }
static inline Aig_Obj_t *  Aig_ObjFanout0( Aig_Man_t * p, Aig_Obj_t * pObj )  { assert(p->pFanData && pObj->Id < p->nFansAlloc); return Aig_ManObj(p, p->pFanData[5*pObj->Id] >> 1); } 
static inline int          Aig_ObjWhatFanin( Aig_Obj_t * pObj, Aig_Obj_t * pFanin )    
{ 
    if ( Aig_ObjFanin0(pObj) == pFanin ) return 0; 
    if ( Aig_ObjFanin1(pObj) == pFanin ) return 1; 
    assert(0); return -1; 
}
static inline int          Aig_ObjFanoutC( Aig_Obj_t * pObj, Aig_Obj_t * pFanout )    
{ 
    if ( Aig_ObjFanin0(pFanout) == pObj ) return Aig_ObjFaninC0(pObj); 
    if ( Aig_ObjFanin1(pFanout) == pObj ) return Aig_ObjFaninC1(pObj); 
    assert(0); return -1; 
}

// create the ghost of the new node
static inline Aig_Obj_t *  Aig_ObjCreateGhost( Aig_Man_t * p, Aig_Obj_t * p0, Aig_Obj_t * p1, Aig_Type_t Type )    
{
    Aig_Obj_t * pGhost;
    assert( Type != AIG_OBJ_AND || !Aig_ObjIsConst1(Aig_Regular(p0)) );
    assert( p1 == NULL || !Aig_ObjIsConst1(Aig_Regular(p1)) );
    assert( Type == AIG_OBJ_PI || Aig_Regular(p0) != Aig_Regular(p1) );
    pGhost = Aig_ManGhost(p);
    pGhost->Type = Type;
    if ( p1 == NULL || Aig_Regular(p0)->Id < Aig_Regular(p1)->Id )
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
static inline Aig_Obj_t * Aig_ManFetchMemory( Aig_Man_t * p )  
{
    extern char * Aig_MmFixedEntryFetch( Aig_MmFixed_t * p );
    Aig_Obj_t * pTemp;
    pTemp = (Aig_Obj_t *)Aig_MmFixedEntryFetch( p->pMemObjs );
    memset( pTemp, 0, sizeof(Aig_Obj_t) ); 
    Vec_PtrPush( p->vObjs, pTemp );
    pTemp->Id = p->nCreated++;
    return pTemp;
}
static inline void Aig_ManRecycleMemory( Aig_Man_t * p, Aig_Obj_t * pEntry )
{
    extern void Aig_MmFixedEntryRecycle( Aig_MmFixed_t * p, char * pEntry );
    assert( pEntry->nRefs == 0 );
    pEntry->Type = AIG_OBJ_NONE; // distinquishes a dead node from a live node
    Aig_MmFixedEntryRecycle( p->pMemObjs, (char *)pEntry );
    p->nDeleted++;
}


////////////////////////////////////////////////////////////////////////
///                             ITERATORS                            ///
////////////////////////////////////////////////////////////////////////

// iterator over the primary inputs
#define Aig_ManForEachPi( p, pObj, i )                                          \
    Vec_PtrForEachEntry( p->vPis, pObj, i )
// iterator over the primary outputs
#define Aig_ManForEachPo( p, pObj, i )                                          \
    Vec_PtrForEachEntry( p->vPos, pObj, i )
// iterator over all objects, including those currently not used
#define Aig_ManForEachObj( p, pObj, i )                                         \
    Vec_PtrForEachEntry( p->vObjs, pObj, i ) if ( (pObj) == NULL ) {} else
// iterator over all nodes
#define Aig_ManForEachNode( p, pObj, i )                                        \
    Vec_PtrForEachEntry( p->vObjs, pObj, i ) if ( (pObj) == NULL || !Aig_ObjIsNode(pObj) ) {} else
// iterator over the nodes whose IDs are stored in the array
#define Aig_ManForEachNodeVec( p, vIds, pObj, i )                               \
    for ( i = 0; i < Vec_IntSize(vIds) && ((pObj) = Aig_ManObj(p, Vec_IntEntry(vIds,i))); i++ )

// these two procedures are only here for the use inside the iterator
static inline int     Aig_ObjFanout0Int( Aig_Man_t * p, int ObjId )  { assert(ObjId < p->nFansAlloc);  return p->pFanData[5*ObjId];                         }
static inline int     Aig_ObjFanoutNext( Aig_Man_t * p, int iFan )   { assert(iFan/2 < p->nFansAlloc); return p->pFanData[5*(iFan >> 1) + 3 + (iFan & 1)];  }
// iterator over the fanouts
#define Aig_ObjForEachFanout( p, pObj, pFanout, iFan, i )                       \
    for ( assert(p->pFanData), i = 0; (i < (int)(pObj)->nRefs) &&               \
          (((iFan) = i? Aig_ObjFanoutNext(p, iFan) : Aig_ObjFanout0Int(p, pObj->Id)), 1) && \
          (((pFanout) = Aig_ManObj(p, iFan>>1)), 1); i++ )

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== aigCheck.c ========================================================*/
extern int             Aig_ManCheck( Aig_Man_t * p );
/*=== aigDfs.c ==========================================================*/
extern Vec_Ptr_t *     Aig_ManDfs( Aig_Man_t * p );
extern Vec_Ptr_t *     Aig_ManDfsNodes( Aig_Man_t * p, Aig_Obj_t ** ppNodes, int nNodes );
extern Vec_Ptr_t *     Aig_ManDfsReverse( Aig_Man_t * p );
extern int             Aig_ManCountLevels( Aig_Man_t * p );
extern int             Aig_DagSize( Aig_Obj_t * pObj );
extern void            Aig_ConeUnmark_rec( Aig_Obj_t * pObj );
extern Aig_Obj_t *     Aig_Transfer( Aig_Man_t * pSour, Aig_Man_t * pDest, Aig_Obj_t * pObj, int nVars );
extern Aig_Obj_t *     Aig_Compose( Aig_Man_t * p, Aig_Obj_t * pRoot, Aig_Obj_t * pFunc, int iVar );
extern void            Aig_ManCollectCut( Aig_Obj_t * pRoot, Vec_Ptr_t * vLeaves, Vec_Ptr_t * vNodes );
/*=== aigFanout.c ==========================================================*/
extern void            Aig_ObjAddFanout( Aig_Man_t * p, Aig_Obj_t * pObj, Aig_Obj_t * pFanout );
extern void            Aig_ObjRemoveFanout( Aig_Man_t * p, Aig_Obj_t * pObj, Aig_Obj_t * pFanout );
extern void            Aig_ManCreateFanout( Aig_Man_t * p );
extern void            Aig_ManDeleteFanout( Aig_Man_t * p );
/*=== aigMan.c ==========================================================*/
extern Aig_Man_t *     Aig_ManStart();
extern Aig_Man_t *     Aig_ManStartFrom( Aig_Man_t * p );
extern Aig_Man_t *     Aig_ManDup( Aig_Man_t * p, int fOrdered );
extern void            Aig_ManStop( Aig_Man_t * p );
extern int             Aig_ManCleanup( Aig_Man_t * p );
extern void            Aig_ManPrintStats( Aig_Man_t * p );
/*=== aigMem.c ==========================================================*/
extern void            Aig_ManStartMemory( Aig_Man_t * p );
extern void            Aig_ManStopMemory( Aig_Man_t * p );
/*=== aigMffc.c ==========================================================*/
extern int             Aig_NodeRef_rec( Aig_Obj_t * pNode, unsigned LevelMin );
extern int             Aig_NodeDeref_rec( Aig_Obj_t * pNode, unsigned LevelMin );
extern int             Aig_NodeMffsSupp( Aig_Man_t * p, Aig_Obj_t * pNode, int LevelMin, Vec_Ptr_t * vSupp );
extern int             Aig_NodeMffsLabel( Aig_Man_t * p, Aig_Obj_t * pNode );
extern int             Aig_NodeMffsLabelCut( Aig_Man_t * p, Aig_Obj_t * pNode, Vec_Ptr_t * vLeaves );
extern int             Aig_NodeMffsExtendCut( Aig_Man_t * p, Aig_Obj_t * pNode, Vec_Ptr_t * vLeaves, Vec_Ptr_t * vResult );
/*=== aigObj.c ==========================================================*/
extern Aig_Obj_t *     Aig_ObjCreatePi( Aig_Man_t * p );
extern Aig_Obj_t *     Aig_ObjCreatePo( Aig_Man_t * p, Aig_Obj_t * pDriver );
extern Aig_Obj_t *     Aig_ObjCreate( Aig_Man_t * p, Aig_Obj_t * pGhost );
extern void            Aig_ObjConnect( Aig_Man_t * p, Aig_Obj_t * pObj, Aig_Obj_t * pFan0, Aig_Obj_t * pFan1 );
extern void            Aig_ObjDisconnect( Aig_Man_t * p, Aig_Obj_t * pObj );
extern void            Aig_ObjDelete( Aig_Man_t * p, Aig_Obj_t * pObj );
extern void            Aig_ObjDelete_rec( Aig_Man_t * p, Aig_Obj_t * pObj, int fFreeTop );
extern void            Aig_ObjPatchFanin0( Aig_Man_t * p, Aig_Obj_t * pObj, Aig_Obj_t * pFaninNew );
extern void            Aig_ObjReplace( Aig_Man_t * p, Aig_Obj_t * pObjOld, Aig_Obj_t * pObjNew, int fNodesOnly, int fUpdateLevel );
/*=== aigOper.c =========================================================*/
extern Aig_Obj_t *     Aig_IthVar( Aig_Man_t * p, int i );
extern Aig_Obj_t *     Aig_Oper( Aig_Man_t * p, Aig_Obj_t * p0, Aig_Obj_t * p1, Aig_Type_t Type );
extern Aig_Obj_t *     Aig_And( Aig_Man_t * p, Aig_Obj_t * p0, Aig_Obj_t * p1 );
extern Aig_Obj_t *     Aig_Latch( Aig_Man_t * p, Aig_Obj_t * pObj, int fInitOne );
extern Aig_Obj_t *     Aig_Or( Aig_Man_t * p, Aig_Obj_t * p0, Aig_Obj_t * p1 );
extern Aig_Obj_t *     Aig_Exor( Aig_Man_t * p, Aig_Obj_t * p0, Aig_Obj_t * p1 );
extern Aig_Obj_t *     Aig_Mux( Aig_Man_t * p, Aig_Obj_t * pC, Aig_Obj_t * p1, Aig_Obj_t * p0 );
extern Aig_Obj_t *     Aig_Maj( Aig_Man_t * p, Aig_Obj_t * pA, Aig_Obj_t * pB, Aig_Obj_t * pC );
extern Aig_Obj_t *     Aig_Miter( Aig_Man_t * p, Vec_Ptr_t * vPairs );
extern Aig_Obj_t *     Aig_CreateAnd( Aig_Man_t * p, int nVars );
extern Aig_Obj_t *     Aig_CreateOr( Aig_Man_t * p, int nVars );
extern Aig_Obj_t *     Aig_CreateExor( Aig_Man_t * p, int nVars );
/*=== aigSeq.c ========================================================*/
extern int             Aig_ManSeqStrash( Aig_Man_t * p, int nLatches, int * pInits );
/*=== aigTable.c ========================================================*/
extern Aig_Obj_t *     Aig_TableLookup( Aig_Man_t * p, Aig_Obj_t * pGhost );
extern Aig_Obj_t *     Aig_TableLookupTwo( Aig_Man_t * p, Aig_Obj_t * pFanin0, Aig_Obj_t * pFanin1 );
extern void            Aig_TableInsert( Aig_Man_t * p, Aig_Obj_t * pObj );
extern void            Aig_TableDelete( Aig_Man_t * p, Aig_Obj_t * pObj );
extern int             Aig_TableCountEntries( Aig_Man_t * p );
extern void            Aig_TableProfile( Aig_Man_t * p );
/*=== aigTiming.c ========================================================*/
extern int             Aig_ObjRequiredLevel( Aig_Man_t * p, Aig_Obj_t * pObj );
extern void            Aig_ManStartReverseLevels( Aig_Man_t * p, int nMaxLevelIncrease );
extern void            Aig_ManStopReverseLevels( Aig_Man_t * p );
extern void            Aig_ManUpdateLevel( Aig_Man_t * p, Aig_Obj_t * pObjNew );
extern void            Aig_ManUpdateReverseLevel( Aig_Man_t * p, Aig_Obj_t * pObjNew );
/*=== aigTruth.c ========================================================*/
extern unsigned *      Aig_ManCutTruth( Aig_Obj_t * pRoot, Vec_Ptr_t * vLeaves, Vec_Ptr_t * vNodes, Vec_Ptr_t * vTruthElem, Vec_Ptr_t * vTruthStore );
/*=== aigUtil.c =========================================================*/
extern unsigned        Aig_PrimeCudd( unsigned p );
extern void            Aig_ManIncrementTravId( Aig_Man_t * p );
extern int             Aig_ManLevels( Aig_Man_t * p );
extern void            Aig_ManCheckMarkA( Aig_Man_t * p );
extern void            Aig_ManCleanData( Aig_Man_t * p );
extern void            Aig_ObjCleanData_rec( Aig_Obj_t * pObj );
extern void            Aig_ObjCollectMulti( Aig_Obj_t * pFunc, Vec_Ptr_t * vSuper );
extern int             Aig_ObjIsMuxType( Aig_Obj_t * pObj );
extern int             Aig_ObjRecognizeExor( Aig_Obj_t * pObj, Aig_Obj_t ** ppFan0, Aig_Obj_t ** ppFan1 );
extern Aig_Obj_t *     Aig_ObjRecognizeMux( Aig_Obj_t * pObj, Aig_Obj_t ** ppObjT, Aig_Obj_t ** ppObjE );
extern Aig_Obj_t *     Aig_ObjReal_rec( Aig_Obj_t * pObj );
extern void            Aig_ObjPrintEqn( FILE * pFile, Aig_Obj_t * pObj, Vec_Vec_t * vLevels, int Level );
extern void            Aig_ObjPrintVerilog( FILE * pFile, Aig_Obj_t * pObj, Vec_Vec_t * vLevels, int Level );
extern void            Aig_ObjPrintVerbose( Aig_Obj_t * pObj, int fHaig );
extern void            Aig_ManPrintVerbose( Aig_Man_t * p, int fHaig );
extern void            Aig_ManDumpBlif( Aig_Man_t * p, char * pFileName );
/*=== aigWin.c =========================================================*/
extern void            Aig_ManFindCut( Aig_Obj_t * pRoot, Vec_Ptr_t * vFront, Vec_Ptr_t * vVisited, int nSizeLimit, int nFanoutLimit );
 
/*=== aigMem.c ===========================================================*/
// fixed-size-block memory manager
extern Aig_MmFixed_t * Aig_MmFixedStart( int nEntrySize, int nEntriesMax );
extern void            Aig_MmFixedStop( Aig_MmFixed_t * p, int fVerbose );
extern char *          Aig_MmFixedEntryFetch( Aig_MmFixed_t * p );
extern void            Aig_MmFixedEntryRecycle( Aig_MmFixed_t * p, char * pEntry );
extern void            Aig_MmFixedRestart( Aig_MmFixed_t * p );
extern int             Aig_MmFixedReadMemUsage( Aig_MmFixed_t * p );
extern int             Aig_MmFixedReadMaxEntriesUsed( Aig_MmFixed_t * p );
// flexible-size-block memory manager
extern Aig_MmFlex_t *  Aig_MmFlexStart();
extern void            Aig_MmFlexStop( Aig_MmFlex_t * p, int fVerbose );
extern char *          Aig_MmFlexEntryFetch( Aig_MmFlex_t * p, int nBytes );
extern void            Aig_MmFlexRestart( Aig_MmFlex_t * p );
extern int             Aig_MmFlexReadMemUsage( Aig_MmFlex_t * p );
// hierarchical memory manager
extern Aig_MmStep_t *  Aig_MmStepStart( int nSteps );
extern void            Aig_MmStepStop( Aig_MmStep_t * p, int fVerbose );
extern char *          Aig_MmStepEntryFetch( Aig_MmStep_t * p, int nBytes );
extern void            Aig_MmStepEntryRecycle( Aig_MmStep_t * p, char * pEntry, int nBytes );
extern int             Aig_MmStepReadMemUsage( Aig_MmStep_t * p );

#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

