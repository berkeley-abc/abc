/**CFile****************************************************************

  FileName    [aig.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Minimalistic And-Inverter Graph package.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: aig.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

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
#include "vec.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Aig_Man_t_            Aig_Man_t;
typedef struct Aig_Obj_t_            Aig_Obj_t;
typedef int                          Aig_Edge_t;

// object types
typedef enum { 
    AIG_NONE,                        // 0: non-existent object
    AIG_CONST1,                      // 1: constant 1 
    AIG_PI,                          // 2: primary input
    AIG_PO,                          // 3: primary output
    AIG_AND,                         // 4: AND node
    AIG_EXOR,                        // 5: EXOR node
    AIG_VOID                         // 6: unused object
} Aig_Type_t;

// the AIG node
struct Aig_Obj_t_  // 4 words
{
    void *           pData;          // misc
    Aig_Obj_t *      pFanin0;        // fanin
    Aig_Obj_t *      pFanin1;        // fanin
    unsigned long    Type    :  3;   // object type
    unsigned long    fPhase  :  1;   // value under 000...0 pattern
    unsigned long    fMarkA  :  1;   // multipurpose mask
    unsigned long    fMarkB  :  1;   // multipurpose mask
    unsigned long    nRefs   : 26;   // reference count (level)
};

// the AIG manager
struct Aig_Man_t_
{
    // AIG nodes
    Vec_Ptr_t *      vPis;           // the array of PIs
    Vec_Ptr_t *      vPos;           // the array of POs
    Aig_Obj_t *      pConst1;        // the constant 1 node
    Aig_Obj_t        Ghost;          // the ghost node
    // AIG node counters
    int              nObjs[AIG_VOID];// the number of objects by type
    int              nCreated;       // the number of created objects
    int              nDeleted;       // the number of deleted objects
    // stuctural hash table
    Aig_Obj_t **     pTable;         // structural hash table
    int              nTableSize;     // structural hash table size
    // various data members
    void *           pData;          // the temporary data
    int              nTravIds;       // the current traversal ID
    int              fRefCount;      // enables reference counting
    int              fCatchExor;     // enables EXOR nodes
    // memory management
    Vec_Ptr_t *      vChunks;        // allocated memory pieces
    Vec_Ptr_t *      vPages;         // memory pages used by nodes
    Aig_Obj_t *      pListFree;      // the list of free nodes 
    // timing statistics
    int              time1;
    int              time2;
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

#define AIG_MIN(a,b)       (((a) < (b))? (a) : (b))
#define AIG_MAX(a,b)       (((a) > (b))? (a) : (b))

static inline int          Aig_BitWordNum( int nBits )            { return (nBits>>5) + ((nBits&31) > 0);           }
static inline int          Aig_TruthWordNum( int nVars )          { return nVars <= 5 ? 1 : (1 << (nVars - 5));     }
static inline int          Aig_InfoHasBit( unsigned * p, int i )  { return (p[(i)>>5] & (1<<((i) & 31))) > 0;       }
static inline void         Aig_InfoSetBit( unsigned * p, int i )  { p[(i)>>5] |= (1<<((i) & 31));                   }
static inline void         Aig_InfoXorBit( unsigned * p, int i )  { p[(i)>>5] ^= (1<<((i) & 31));                   }

static inline Aig_Obj_t *  Aig_Regular( Aig_Obj_t * p )           { return (Aig_Obj_t *)((unsigned)(p) & ~01);      }
static inline Aig_Obj_t *  Aig_Not( Aig_Obj_t * p )               { return (Aig_Obj_t *)((unsigned)(p) ^  01);      }
static inline Aig_Obj_t *  Aig_NotCond( Aig_Obj_t * p, int c )    { return (Aig_Obj_t *)((unsigned)(p) ^ (c));      }
static inline int          Aig_IsComplement( Aig_Obj_t * p )      { return (int )(((unsigned)p) & 01);              }

static inline Aig_Obj_t *  Aig_ManConst0( Aig_Man_t * p )         { return Aig_Not(p->pConst1);                     }
static inline Aig_Obj_t *  Aig_ManConst1( Aig_Man_t * p )         { return p->pConst1;                              }
static inline Aig_Obj_t *  Aig_ManGhost( Aig_Man_t * p )          { return &p->Ghost;                               }
static inline Aig_Obj_t *  Aig_ManPi( Aig_Man_t * p, int i )      { return (Aig_Obj_t *)Vec_PtrEntry(p->vPis, i);   }

static inline Aig_Edge_t   Aig_EdgeCreate( int Id, int fCompl )            { return (Id << 1) | fCompl;             }
static inline int          Aig_EdgeId( Aig_Edge_t Edge )                   { return Edge >> 1;                      }
static inline int          Aig_EdgeIsComplement( Aig_Edge_t Edge )         { return Edge & 1;                       }
static inline Aig_Edge_t   Aig_EdgeRegular( Aig_Edge_t Edge )              { return (Edge >> 1) << 1;               }
static inline Aig_Edge_t   Aig_EdgeNot( Aig_Edge_t Edge )                  { return Edge ^ 1;                       }
static inline Aig_Edge_t   Aig_EdgeNotCond( Aig_Edge_t Edge, int fCond )   { return Edge ^ fCond;                   }

static inline int          Aig_ManPiNum( Aig_Man_t * p )          { return p->nObjs[AIG_PI];                    }
static inline int          Aig_ManPoNum( Aig_Man_t * p )          { return p->nObjs[AIG_PO];                    }
static inline int          Aig_ManAndNum( Aig_Man_t * p )         { return p->nObjs[AIG_AND];                   }
static inline int          Aig_ManExorNum( Aig_Man_t * p )        { return p->nObjs[AIG_EXOR];                  }
static inline int          Aig_ManNodeNum( Aig_Man_t * p )        { return p->nObjs[AIG_AND]+p->nObjs[AIG_EXOR];}
static inline int          Aig_ManGetCost( Aig_Man_t * p )        { return p->nObjs[AIG_AND]+3*p->nObjs[AIG_EXOR]; }
static inline int          Aig_ManObjNum( Aig_Man_t * p )         { return p->nCreated - p->nDeleted;           }

static inline Aig_Type_t   Aig_ObjType( Aig_Obj_t * pObj )        { return pObj->Type;               }
static inline int          Aig_ObjIsNone( Aig_Obj_t * pObj )      { return pObj->Type == AIG_NONE;   }
static inline int          Aig_ObjIsConst1( Aig_Obj_t * pObj )    { assert(!Aig_IsComplement(pObj)); return pObj->Type == AIG_CONST1; }
static inline int          Aig_ObjIsPi( Aig_Obj_t * pObj )        { return pObj->Type == AIG_PI;     }
static inline int          Aig_ObjIsPo( Aig_Obj_t * pObj )        { return pObj->Type == AIG_PO;     }
static inline int          Aig_ObjIsAnd( Aig_Obj_t * pObj )       { return pObj->Type == AIG_AND;    }
static inline int          Aig_ObjIsExor( Aig_Obj_t * pObj )      { return pObj->Type == AIG_EXOR;   }
static inline int          Aig_ObjIsNode( Aig_Obj_t * pObj )      { return pObj->Type == AIG_AND || pObj->Type == AIG_EXOR;   }
static inline int          Aig_ObjIsTerm( Aig_Obj_t * pObj )      { return pObj->Type == AIG_PI  || pObj->Type == AIG_PO || pObj->Type == AIG_CONST1; }
static inline int          Aig_ObjIsHash( Aig_Obj_t * pObj )      { return pObj->Type == AIG_AND || pObj->Type == AIG_EXOR;   }

static inline int          Aig_ObjIsMarkA( Aig_Obj_t * pObj )     { return pObj->fMarkA;  }
static inline void         Aig_ObjSetMarkA( Aig_Obj_t * pObj )    { pObj->fMarkA = 1;     }
static inline void         Aig_ObjClearMarkA( Aig_Obj_t * pObj )  { pObj->fMarkA = 0;     }
 
static inline void         Aig_ObjSetTravId( Aig_Obj_t * pObj, int TravId )                { pObj->pData = (void *)TravId;                       }
static inline void         Aig_ObjSetTravIdCurrent( Aig_Man_t * p, Aig_Obj_t * pObj )      { pObj->pData = (void *)p->nTravIds;                  }
static inline void         Aig_ObjSetTravIdPrevious( Aig_Man_t * p, Aig_Obj_t * pObj )     { pObj->pData = (void *)(p->nTravIds - 1);            }
static inline int          Aig_ObjIsTravIdCurrent( Aig_Man_t * p, Aig_Obj_t * pObj )       { return (int )((int)pObj->pData == p->nTravIds);     }
static inline int          Aig_ObjIsTravIdPrevious( Aig_Man_t * p, Aig_Obj_t * pObj )      { return (int )((int)pObj->pData == p->nTravIds - 1); }

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
static inline Aig_Obj_t *  Aig_ObjChild0Copy( Aig_Obj_t * pObj ) { assert( !Aig_IsComplement(pObj) ); return Aig_ObjFanin0(pObj)? Aig_NotCond(Aig_ObjFanin0(pObj)->pData, Aig_ObjFaninC0(pObj)) : NULL;  }
static inline Aig_Obj_t *  Aig_ObjChild1Copy( Aig_Obj_t * pObj ) { assert( !Aig_IsComplement(pObj) ); return Aig_ObjFanin1(pObj)? Aig_NotCond(Aig_ObjFanin1(pObj)->pData, Aig_ObjFaninC1(pObj)) : NULL;  }
static inline int          Aig_ObjLevel( Aig_Obj_t * pObj )       { return pObj->nRefs;                            }
static inline int          Aig_ObjLevelNew( Aig_Obj_t * pObj )    { return 1 + Aig_ObjIsExor(pObj) + AIG_MAX(Aig_ObjFanin0(pObj)->nRefs, Aig_ObjFanin1(pObj)->nRefs);       }
static inline void         Aig_ObjClean( Aig_Obj_t * pObj )       { memset( pObj, 0, sizeof(Aig_Obj_t) ); }
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
    assert( Type != AIG_AND || !Aig_ObjIsConst1(Aig_Regular(p0)) );
    assert( p1 == NULL || !Aig_ObjIsConst1(Aig_Regular(p1)) );
    assert( Type == AIG_PI || Aig_Regular(p0) != Aig_Regular(p1) );
    pGhost = Aig_ManGhost(p);
    pGhost->Type = Type;
    pGhost->pFanin0 = p0 < p1? p0 : p1;
    pGhost->pFanin1 = p0 < p1? p1 : p0;
    return pGhost;
}

// internal memory manager
static inline Aig_Obj_t * Aig_ManFetchMemory( Aig_Man_t * p )  
{ 
    extern void Aig_ManAddMemory( Aig_Man_t * p );
    Aig_Obj_t * pTemp;
    if ( p->pListFree == NULL )
        Aig_ManAddMemory( p );
    pTemp = p->pListFree;
    p->pListFree = *((Aig_Obj_t **)pTemp);
    memset( pTemp, 0, sizeof(Aig_Obj_t) ); 
    return pTemp;
}
static inline void Aig_ManRecycleMemory( Aig_Man_t * p, Aig_Obj_t * pEntry )
{
    pEntry->Type = AIG_NONE; // distinquishes dead node from live node
    *((Aig_Obj_t **)pEntry) = p->pListFree;
    p->pListFree = pEntry;
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
#define Aig_ManForEachNode( p, pObj, i )                                        \
    for ( i = 0; i < p->nTableSize; i++ )                                       \
        if ( ((pObj) = p->pTable[i]) == NULL ) {} else

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== aigBalance.c ========================================================*/
extern Aig_Man_t *     Aig_ManBalance( Aig_Man_t * p, int fUpdateLevel );
extern Aig_Obj_t *     Aig_NodeBalanceBuildSuper( Aig_Man_t * p, Vec_Ptr_t * vSuper, Aig_Type_t Type, int fUpdateLevel );
/*=== aigCheck.c ========================================================*/
extern int             Aig_ManCheck( Aig_Man_t * p );
/*=== aigDfs.c ==========================================================*/
extern Vec_Ptr_t *     Aig_ManDfs( Aig_Man_t * p );
extern Vec_Ptr_t *     Aig_ManDfsNode( Aig_Man_t * p, Aig_Obj_t * pNode );
extern int             Aig_ManCountLevels( Aig_Man_t * p );
extern void            Aig_ManCreateRefs( Aig_Man_t * p );
extern int             Aig_DagSize( Aig_Obj_t * pObj );
extern void            Aig_ConeUnmark_rec( Aig_Obj_t * pObj );
extern Aig_Obj_t *     Aig_Transfer( Aig_Man_t * pSour, Aig_Man_t * pDest, Aig_Obj_t * pObj, int nVars );
/*=== aigMan.c ==========================================================*/
extern Aig_Man_t *     Aig_ManStart();
extern Aig_Man_t *     Aig_ManDup( Aig_Man_t * p );
extern void            Aig_ManStop( Aig_Man_t * p );
extern int             Aig_ManCleanup( Aig_Man_t * p );
extern void            Aig_ManPrintStats( Aig_Man_t * p );
/*=== aigMem.c ==========================================================*/
extern void            Aig_ManStartMemory( Aig_Man_t * p );
extern void            Aig_ManStopMemory( Aig_Man_t * p );
/*=== aigObj.c ==========================================================*/
extern Aig_Obj_t *     Aig_ObjCreatePi( Aig_Man_t * p );
extern Aig_Obj_t *     Aig_ObjCreatePo( Aig_Man_t * p, Aig_Obj_t * pDriver );
extern Aig_Obj_t *     Aig_ObjCreate( Aig_Man_t * p, Aig_Obj_t * pGhost );
extern void            Aig_ObjConnect( Aig_Man_t * p, Aig_Obj_t * pObj, Aig_Obj_t * pFan0, Aig_Obj_t * pFan1 );
extern void            Aig_ObjDisconnect( Aig_Man_t * p, Aig_Obj_t * pObj );
extern void            Aig_ObjDelete( Aig_Man_t * p, Aig_Obj_t * pObj );
extern void            Aig_ObjDelete_rec( Aig_Man_t * p, Aig_Obj_t * pObj );
/*=== aigOper.c =========================================================*/
extern Aig_Obj_t *     Aig_IthVar( Aig_Man_t * p, int i );
extern Aig_Obj_t *     Aig_Oper( Aig_Man_t * p, Aig_Obj_t * p0, Aig_Obj_t * p1, Aig_Type_t Type );
extern Aig_Obj_t *     Aig_And( Aig_Man_t * p, Aig_Obj_t * p0, Aig_Obj_t * p1 );
extern Aig_Obj_t *     Aig_Or( Aig_Man_t * p, Aig_Obj_t * p0, Aig_Obj_t * p1 );
extern Aig_Obj_t *     Aig_Exor( Aig_Man_t * p, Aig_Obj_t * p0, Aig_Obj_t * p1 );
extern Aig_Obj_t *     Aig_Mux( Aig_Man_t * p, Aig_Obj_t * pC, Aig_Obj_t * p1, Aig_Obj_t * p0 );
extern Aig_Obj_t *     Aig_Maj( Aig_Man_t * p, Aig_Obj_t * pA, Aig_Obj_t * pB, Aig_Obj_t * pC );
extern Aig_Obj_t *     Aig_Miter( Aig_Man_t * p, Vec_Ptr_t * vPairs );
extern Aig_Obj_t *     Aig_CreateAnd( Aig_Man_t * p, int nVars );
extern Aig_Obj_t *     Aig_CreateOr( Aig_Man_t * p, int nVars );
extern Aig_Obj_t *     Aig_CreateExor( Aig_Man_t * p, int nVars );
/*=== aigTable.c ========================================================*/
extern Aig_Obj_t *     Aig_TableLookup( Aig_Man_t * p, Aig_Obj_t * pGhost );
extern void            Aig_TableInsert( Aig_Man_t * p, Aig_Obj_t * pObj );
extern void            Aig_TableDelete( Aig_Man_t * p, Aig_Obj_t * pObj );
extern int             Aig_TableCountEntries( Aig_Man_t * p );
extern void            Aig_TableProfile( Aig_Man_t * p );
/*=== aigUtil.c =========================================================*/
extern void            Aig_ManIncrementTravId( Aig_Man_t * p );
extern void            Aig_ManCleanData( Aig_Man_t * p );
extern void            Aig_ObjCollectMulti( Aig_Obj_t * pFunc, Vec_Ptr_t * vSuper );
extern int             Aig_ObjIsMuxType( Aig_Obj_t * pObj );
extern int             Aig_ObjRecognizeExor( Aig_Obj_t * pObj, Aig_Obj_t ** ppFan0, Aig_Obj_t ** ppFan1 );
extern Aig_Obj_t *     Aig_ObjRecognizeMux( Aig_Obj_t * pObj, Aig_Obj_t ** ppObjT, Aig_Obj_t ** ppObjE );
extern void            Aig_ObjPrintVerilog( FILE * pFile, Aig_Obj_t * pObj, Vec_Vec_t * vLevels, int Level );
extern void            Aig_ObjPrintVerbose( Aig_Obj_t * pObj, int fHaig );
extern void            Aig_ManPrintVerbose( Aig_Man_t * p, int fHaig );

#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

