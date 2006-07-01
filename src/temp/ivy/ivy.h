/**CFile****************************************************************

  FileName    [ivy.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: ivy.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef __IVY_H__
#define __IVY_H__

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

typedef struct Ivy_Man_t_            Ivy_Man_t;
typedef struct Ivy_Obj_t_            Ivy_Obj_t;
typedef int                          Ivy_Edge_t;

// constant edges
#define IVY_CONST0                   1
#define IVY_CONST1                   0

// object types
typedef enum { 
    IVY_NONE,                        // 0: unused node
    IVY_PI,                          // 1: primary input (and constant 1 node)
    IVY_PO,                          // 2: primary output
    IVY_ASSERT,                      // 3: assertion
    IVY_LATCH,                       // 4: sequential element
    IVY_AND,                         // 5: internal AND node
    IVY_EXOR,                        // 6: internal EXOR node
    IVY_BUF,                         // 7: internal buffer (temporary)
    IVY_ANDM,                        // 8: multi-input AND (logic network only)
    IVY_EXORM,                       // 9: multi-input EXOR (logic network only)
    IVY_LUT                          // 10: multi-input LUT (logic network only)
} Ivy_Type_t;

// latch initial values
typedef enum { 
    IVY_INIT_NONE,                   // 0: not a latch
    IVY_INIT_0,                      // 1: zero
    IVY_INIT_1,                      // 2: one
    IVY_INIT_DC                      // 3: don't-care
} Ivy_Init_t;

// the AIG node
struct Ivy_Obj_t_  // 6 words
{
    int              Id;             // integer ID
    int              TravId;         // traversal ID
    int              Fanin0;         // fanin ID
    int              Fanin1;         // fanin ID
    int              nRefs;          // reference counter
    unsigned         Type    :  4;   // object type
    unsigned         fPhase  :  1;   // value under 000...0 pattern
    unsigned         fMarkA  :  1;   // multipurpose mask
    unsigned         fMarkB  :  1;   // multipurpose mask
    unsigned         fExFan  :  1;   // set to 1 if last fanout added is EXOR
    unsigned         fComp0  :  1;   // complemented attribute
    unsigned         fComp1  :  1;   // complemented attribute
    unsigned         Init    :  2;   // latch initial value
    unsigned         LevelR  :  8;   // reverse logic level
    unsigned         Level   : 12;   // logic level
};

// the AIG manager
struct Ivy_Man_t_
{
    // AIG nodes
    int              nObjs[12];      // the number of objects by type
    int              nCreated;       // the number of created objects
    int              nDeleted;       // the number of deleted objects
    int              ObjIdNext;      // the next free obj ID to assign
    int              nObjsAlloc;     // the allocated number of nodes
    Ivy_Obj_t *      pObjs;          // the array of all nodes
    Vec_Int_t *      vPis;           // the array of PIs
    Vec_Int_t *      vPos;           // the array of POs
    // stuctural hash table
    int *            pTable;         // structural hash table
    int              nTableSize;     // structural hash table size
    // various data members
    int              fCatchExor;     // set to 1 to detect EXORs
    int              fExtended;      // set to 1 in extended mode
    int              nTravIds;       // the traversal ID
    int              nLevelMax;      // the maximum level
    void *           pData;          // the temporary data
    Vec_Int_t *      vRequired;      // required times
    // truth table of the 8-LUTs
    unsigned *       pMemory;        // memory for truth tables
    Vec_Int_t *      vTruths;        // offset for truth table of each node
    // storage for the undo operation
    Vec_Int_t *      vFree;          // storage for all deleted entries
    Ivy_Obj_t *      pUndos;         // description of recently deleted nodes
    int              nUndos;         // the number of recently deleted nodes
    int              nUndosAlloc;    // the number of allocated cells
    int              fRecording;     // shows that recording goes on
};


#define IVY_CUT_LIMIT     256
#define IVY_CUT_INPUT       6

typedef struct Ivy_Cut_t_ Ivy_Cut_t;
struct Ivy_Cut_t_
{
    short       nSize;
    short       nSizeMax;
    int         pArray[IVY_CUT_INPUT];
    unsigned    uHash;
};

typedef struct Ivy_Store_t_ Ivy_Store_t;
struct Ivy_Store_t_
{
    int         nCuts;
    int         nCutsMax;
    Ivy_Cut_t   pCuts[IVY_CUT_LIMIT]; // storage for cuts
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

#define IVY_SANDBOX_SIZE   1

#define IVY_MIN(a,b)       (((a) < (b))? (a) : (b))
#define IVY_MAX(a,b)       (((a) > (b))? (a) : (b))

static inline int          Ivy_BitWordNum( int nBits )            { return (nBits>>5) + ((nBits&31) > 0);       }
static inline int          Ivy_TruthWordNum( int nVars )          { return nVars <= 5 ? 1 : (1 << (nVars - 5)); }
static inline int          Ivy_InfoHasBit( unsigned * p, int i )  { return (p[(i)>>5] & (1<<((i) & 31))) > 0;   }
static inline void         Ivy_InfoSetBit( unsigned * p, int i )  { p[(i)>>5] |= (1<<((i) & 31));               }
static inline void         Ivy_InfoXorBit( unsigned * p, int i )  { p[(i)>>5] ^= (1<<((i) & 31));               }

static inline Ivy_Obj_t *  Ivy_Regular( Ivy_Obj_t * p )           { return (Ivy_Obj_t *)((unsigned)(p) & ~01);  }
static inline Ivy_Obj_t *  Ivy_Not( Ivy_Obj_t * p )               { return (Ivy_Obj_t *)((unsigned)(p) ^  01);  }
static inline Ivy_Obj_t *  Ivy_NotCond( Ivy_Obj_t * p, int c )    { return (Ivy_Obj_t *)((unsigned)(p) ^ (c));  }
static inline int          Ivy_IsComplement( Ivy_Obj_t * p )      { return (int )(((unsigned)p) & 01);          }

static inline Ivy_Obj_t *  Ivy_ManConst0( Ivy_Man_t * p )         { return Ivy_Not(p->pObjs);                   }
static inline Ivy_Obj_t *  Ivy_ManConst1( Ivy_Man_t * p )         { return p->pObjs;                            }
static inline Ivy_Obj_t *  Ivy_ManGhost( Ivy_Man_t * p )          { return p->pObjs - IVY_SANDBOX_SIZE;         }
static inline Ivy_Obj_t *  Ivy_ManPi( Ivy_Man_t * p, int i )      { return p->pObjs + Vec_IntEntry(p->vPis,i);  }
static inline Ivy_Obj_t *  Ivy_ManPo( Ivy_Man_t * p, int i )      { return p->pObjs + Vec_IntEntry(p->vPos,i);  }
static inline Ivy_Obj_t *  Ivy_ManObj( Ivy_Man_t * p, int i )     { return p->pObjs + i;                        }

static inline Ivy_Edge_t   Ivy_EdgeCreate( int Id, int fCompl )            { return (Id << 1) | fCompl;                  }
static inline int          Ivy_EdgeId( Ivy_Edge_t Edge )                   { return Edge >> 1;                           }
static inline int          Ivy_EdgeIsComplement( Ivy_Edge_t Edge )         { return Edge & 1;                            }
static inline Ivy_Edge_t   Ivy_EdgeRegular( Ivy_Edge_t Edge )              { return (Edge >> 1) << 1;                    }
static inline Ivy_Edge_t   Ivy_EdgeNot( Ivy_Edge_t Edge )                  { return Edge ^ 1;                            }
static inline Ivy_Edge_t   Ivy_EdgeNotCond( Ivy_Edge_t Edge, int fCond )   { return Edge ^ fCond;                        }
static inline Ivy_Edge_t   Ivy_EdgeFromNode( Ivy_Obj_t * pNode )           { return Ivy_EdgeCreate( Ivy_Regular(pNode)->Id, Ivy_IsComplement(pNode) );          }
static inline Ivy_Obj_t *  Ivy_EdgeToNode( Ivy_Man_t * p, Ivy_Edge_t Edge ){ return Ivy_NotCond( Ivy_ManObj(p, Ivy_EdgeId(Edge)), Ivy_EdgeIsComplement(Edge) ); }

static inline int          Ivy_LeafCreate( int Id, int Lat )      { return (Id << 4) | Lat;                     }
static inline int          Ivy_LeafId( int Leaf )                 { return Leaf >> 4;                           }
static inline int          Ivy_LeafLat( int Leaf )                { return Leaf & 15;                           }

static inline int          Ivy_ManPiNum( Ivy_Man_t * p )          { return p->nObjs[IVY_PI];                    }
static inline int          Ivy_ManPoNum( Ivy_Man_t * p )          { return p->nObjs[IVY_PO];                    }
static inline int          Ivy_ManAssertNum( Ivy_Man_t * p )      { return p->nObjs[IVY_ASSERT];                }
static inline int          Ivy_ManLatchNum( Ivy_Man_t * p )       { return p->nObjs[IVY_LATCH];                 }
static inline int          Ivy_ManAndNum( Ivy_Man_t * p )         { return p->nObjs[IVY_AND];                   }
static inline int          Ivy_ManExorNum( Ivy_Man_t * p )        { return p->nObjs[IVY_EXOR];                  }
static inline int          Ivy_ManBufNum( Ivy_Man_t * p )         { return p->nObjs[IVY_BUF];                   }
static inline int          Ivy_ManAndMultiNum( Ivy_Man_t * p )    { return p->nObjs[IVY_ANDM];                  }
static inline int          Ivy_ManExorMultiNum( Ivy_Man_t * p )   { return p->nObjs[IVY_EXORM];                 }
static inline int          Ivy_ManLutNum( Ivy_Man_t * p )         { return p->nObjs[IVY_LUT];                   }
static inline int          Ivy_ManObjNum( Ivy_Man_t * p )         { return p->nCreated - p->nDeleted;           }
static inline int          Ivy_ManObjIdNext( Ivy_Man_t * p )      { return p->ObjIdNext;                        }
static inline int          Ivy_ManObjAllocNum( Ivy_Man_t * p )    { return p->nObjsAlloc;                       }
static inline int          Ivy_ManNodeNum( Ivy_Man_t * p )        { return p->fExtended? p->nObjs[IVY_ANDM]+p->nObjs[IVY_EXORM]+p->nObjs[IVY_LUT] : p->nObjs[IVY_AND]+p->nObjs[IVY_EXOR]; }
static inline int          Ivy_ManHashObjNum( Ivy_Man_t * p )     { return p->nObjs[IVY_AND]+p->nObjs[IVY_EXOR]+p->nObjs[IVY_LATCH];     }
static inline int          Ivy_ManGetCost( Ivy_Man_t * p )        { return p->nObjs[IVY_AND]+3*p->nObjs[IVY_EXOR]+8*p->nObjs[IVY_LATCH]; }

static inline Ivy_Type_t   Ivy_ObjType( Ivy_Obj_t * pObj )        { assert( !Ivy_IsComplement(pObj) ); return pObj->Type;               }
static inline Ivy_Init_t   Ivy_ObjInit( Ivy_Obj_t * pObj )        { assert( !Ivy_IsComplement(pObj) ); return pObj->Init;               }
static inline int          Ivy_ObjIsConst1( Ivy_Obj_t * pObj )    { assert( !Ivy_IsComplement(pObj) ); return pObj->Id == 0;            }
static inline int          Ivy_ObjIsGhost( Ivy_Obj_t * pObj )     { assert( !Ivy_IsComplement(pObj) ); return pObj->Id < 0;             }
static inline int          Ivy_ObjIsNone( Ivy_Obj_t * pObj )      { assert( !Ivy_IsComplement(pObj) ); return pObj->Type == IVY_NONE;   }
static inline int          Ivy_ObjIsPi( Ivy_Obj_t * pObj )        { assert( !Ivy_IsComplement(pObj) ); return pObj->Type == IVY_PI;     }
static inline int          Ivy_ObjIsPo( Ivy_Obj_t * pObj )        { assert( !Ivy_IsComplement(pObj) ); return pObj->Type == IVY_PO;     }
static inline int          Ivy_ObjIsCi( Ivy_Obj_t * pObj )        { assert( !Ivy_IsComplement(pObj) ); return pObj->Type == IVY_PI || pObj->Type == IVY_LATCH; }
static inline int          Ivy_ObjIsCo( Ivy_Obj_t * pObj )        { assert( !Ivy_IsComplement(pObj) ); return pObj->Type == IVY_PO || pObj->Type == IVY_LATCH; }
static inline int          Ivy_ObjIsAssert( Ivy_Obj_t * pObj )    { assert( !Ivy_IsComplement(pObj) ); return pObj->Type == IVY_ASSERT; }
static inline int          Ivy_ObjIsLatch( Ivy_Obj_t * pObj )     { assert( !Ivy_IsComplement(pObj) ); return pObj->Type == IVY_LATCH;  }
static inline int          Ivy_ObjIsAnd( Ivy_Obj_t * pObj )       { assert( !Ivy_IsComplement(pObj) ); return pObj->Type == IVY_AND;    }
static inline int          Ivy_ObjIsExor( Ivy_Obj_t * pObj )      { assert( !Ivy_IsComplement(pObj) ); return pObj->Type == IVY_EXOR;   }
static inline int          Ivy_ObjIsBuf( Ivy_Obj_t * pObj )       { assert( !Ivy_IsComplement(pObj) ); return pObj->Type == IVY_BUF;    }
static inline int          Ivy_ObjIsNode( Ivy_Obj_t * pObj )      { assert( !Ivy_IsComplement(pObj) ); return pObj->Type == IVY_AND || pObj->Type == IVY_EXOR; }
static inline int          Ivy_ObjIsTerm( Ivy_Obj_t * pObj )      { assert( !Ivy_IsComplement(pObj) ); return pObj->Type == IVY_PI  || pObj->Type == IVY_PO || pObj->Type == IVY_ASSERT; }
static inline int          Ivy_ObjIsHash( Ivy_Obj_t * pObj )      { assert( !Ivy_IsComplement(pObj) ); return pObj->Type == IVY_AND || pObj->Type == IVY_EXOR || pObj->Type == IVY_LATCH; }
static inline int          Ivy_ObjIsOneFanin( Ivy_Obj_t * pObj )  { assert( !Ivy_IsComplement(pObj) ); return pObj->Type == IVY_PO  || pObj->Type == IVY_ASSERT || pObj->Type == IVY_BUF || pObj->Type == IVY_LATCH; }

static inline int          Ivy_ObjIsAndMulti( Ivy_Obj_t * pObj )  { assert( !Ivy_IsComplement(pObj) ); return pObj->Type == IVY_ANDM;   }
static inline int          Ivy_ObjIsExorMulti( Ivy_Obj_t * pObj ) { assert( !Ivy_IsComplement(pObj) ); return pObj->Type == IVY_EXORM;  }
static inline int          Ivy_ObjIsLut( Ivy_Obj_t * pObj )       { assert( !Ivy_IsComplement(pObj) ); return pObj->Type == IVY_LUT;    }
static inline int          Ivy_ObjIsNodeExt( Ivy_Obj_t * pObj )   { assert( !Ivy_IsComplement(pObj) ); return pObj->Type >= IVY_ANDM;   }

static inline int          Ivy_ObjIsMarkA( Ivy_Obj_t * pObj )     { assert( !Ivy_IsComplement(pObj) ); return pObj->fMarkA;  }
static inline void         Ivy_ObjSetMarkA( Ivy_Obj_t * pObj )    { assert( !Ivy_IsComplement(pObj) ); pObj->fMarkA = 1;     }
static inline void         Ivy_ObjClearMarkA( Ivy_Obj_t * pObj )  { assert( !Ivy_IsComplement(pObj) ); pObj->fMarkA = 0;     }

static inline Ivy_Man_t *  Ivy_ObjMan( Ivy_Obj_t * pObj )         { assert( !Ivy_IsComplement(pObj) ); return *((Ivy_Man_t **)(pObj - pObj->Id - IVY_SANDBOX_SIZE - 1)); }
static inline Ivy_Obj_t *  Ivy_ObjConst0( Ivy_Obj_t * pObj )      { assert( !Ivy_IsComplement(pObj) ); return Ivy_Not(pObj - pObj->Id);           }
static inline Ivy_Obj_t *  Ivy_ObjConst1( Ivy_Obj_t * pObj )      { assert( !Ivy_IsComplement(pObj) ); return pObj - pObj->Id;                    }
static inline Ivy_Obj_t *  Ivy_ObjGhost( Ivy_Obj_t * pObj )       { assert( !Ivy_IsComplement(pObj) ); return pObj - pObj->Id - IVY_SANDBOX_SIZE; }
static inline Ivy_Obj_t *  Ivy_ObjObj( Ivy_Obj_t * pObj, int n )  { assert( !Ivy_IsComplement(pObj) ); return pObj - pObj->Id + n;                }
static inline Ivy_Obj_t *  Ivy_ObjNext( Ivy_Obj_t * pObj )        { assert( !Ivy_IsComplement(pObj) ); return pObj - pObj->Id + pObj->TravId;     }
 
static inline void         Ivy_ObjSetTravId( Ivy_Obj_t * pObj, int TravId ) { assert( !Ivy_IsComplement(pObj) ); pObj->TravId = TravId;                                              }
static inline void         Ivy_ObjSetTravIdCurrent( Ivy_Obj_t * pObj )      { assert( !Ivy_IsComplement(pObj) ); pObj->TravId = Ivy_ObjMan(pObj)->nTravIds;                          }
static inline void         Ivy_ObjSetTravIdPrevious( Ivy_Obj_t * pObj )     { assert( !Ivy_IsComplement(pObj) ); pObj->TravId = Ivy_ObjMan(pObj)->nTravIds - 1;                      }
static inline int          Ivy_ObjIsTravIdCurrent( Ivy_Obj_t * pObj )       { assert( !Ivy_IsComplement(pObj) ); return (int )((int)pObj->TravId == Ivy_ObjMan(pObj)->nTravIds);     }
static inline int          Ivy_ObjIsTravIdPrevious( Ivy_Obj_t * pObj )      { assert( !Ivy_IsComplement(pObj) ); return (int )((int)pObj->TravId == Ivy_ObjMan(pObj)->nTravIds - 1); }

static inline int          Ivy_ObjId( Ivy_Obj_t * pObj )          { assert( !Ivy_IsComplement(pObj) ); return pObj->Id;                               }
static inline int          Ivy_ObjPhase( Ivy_Obj_t * pObj )       { assert( !Ivy_IsComplement(pObj) ); return pObj->fPhase;                           }
static inline int          Ivy_ObjExorFanout( Ivy_Obj_t * pObj )  { assert( !Ivy_IsComplement(pObj) ); return pObj->fExFan;                           }
static inline int          Ivy_ObjRefs( Ivy_Obj_t * pObj )        { assert( !Ivy_IsComplement(pObj) ); return pObj->nRefs;                            }
static inline void         Ivy_ObjRefsInc( Ivy_Obj_t * pObj )     { assert( !Ivy_IsComplement(pObj) ); pObj->nRefs++;                                 }
static inline void         Ivy_ObjRefsDec( Ivy_Obj_t * pObj )     { assert( !Ivy_IsComplement(pObj) ); assert( pObj->nRefs > 0 ); pObj->nRefs--;      }
static inline int          Ivy_ObjFaninId0( Ivy_Obj_t * pObj )    { assert( !Ivy_IsComplement(pObj) ); return pObj->Fanin0;                           }
static inline int          Ivy_ObjFaninId1( Ivy_Obj_t * pObj )    { assert( !Ivy_IsComplement(pObj) ); return pObj->Fanin1;                           }
static inline int          Ivy_ObjFaninC0( Ivy_Obj_t * pObj )     { assert( !Ivy_IsComplement(pObj) ); return pObj->fComp0;                           }
static inline int          Ivy_ObjFaninC1( Ivy_Obj_t * pObj )     { assert( !Ivy_IsComplement(pObj) ); return pObj->fComp1;                           }
static inline Ivy_Obj_t *  Ivy_ObjFanin0( Ivy_Obj_t * pObj )      { assert( !Ivy_IsComplement(pObj) ); return Ivy_ObjObj(pObj, pObj->Fanin0);         }
static inline Ivy_Obj_t *  Ivy_ObjFanin1( Ivy_Obj_t * pObj )      { assert( !Ivy_IsComplement(pObj) ); return Ivy_ObjObj(pObj, pObj->Fanin1);         }
static inline Ivy_Obj_t *  Ivy_ObjChild0( Ivy_Obj_t * pObj )      { assert( !Ivy_IsComplement(pObj) ); return Ivy_NotCond( Ivy_ObjFanin0(pObj), Ivy_ObjFaninC0(pObj) );   }
static inline Ivy_Obj_t *  Ivy_ObjChild1( Ivy_Obj_t * pObj )      { assert( !Ivy_IsComplement(pObj) ); return Ivy_NotCond( Ivy_ObjFanin1(pObj), Ivy_ObjFaninC1(pObj) );   }
static inline int          Ivy_ObjLevelR( Ivy_Obj_t * pObj )      { assert( !Ivy_IsComplement(pObj) ); return pObj->LevelR;                           }
static inline int          Ivy_ObjLevel( Ivy_Obj_t * pObj )       { assert( !Ivy_IsComplement(pObj) ); return pObj->Level;                            }
static inline int          Ivy_ObjLevelNew( Ivy_Obj_t * pObj )    { assert( !Ivy_IsComplement(pObj) ); return 1 + Ivy_ObjIsExor(pObj) + IVY_MAX(Ivy_ObjFanin0(pObj)->Level, Ivy_ObjFanin1(pObj)->Level);       }
static inline void         Ivy_ObjClean( Ivy_Obj_t * pObj )       { 
    int IdSaved = pObj->Id; 
    memset( pObj, 0, sizeof(Ivy_Obj_t) ); 
    pObj->Id = IdSaved; 
}
static inline void         Ivy_ObjOverwrite( Ivy_Obj_t * pBase, Ivy_Obj_t * pData )   { int IdSaved = pBase->Id; memcpy( pBase, pData, sizeof(Ivy_Obj_t) ); pBase->Id = IdSaved;         }
static inline int          Ivy_ObjWhatFanin( Ivy_Obj_t * pObj, Ivy_Obj_t * pFanin )    
{ 
    if ( Ivy_ObjFaninId0(pObj) == Ivy_ObjId(pFanin) ) return 0; 
    if ( Ivy_ObjFaninId1(pObj) == Ivy_ObjId(pFanin) ) return 1; 
    assert(0); return -1; 
}
static inline int          Ivy_ObjFanoutC( Ivy_Obj_t * pObj, Ivy_Obj_t * pFanout )    
{ 
    if ( Ivy_ObjFaninId0(pFanout) == Ivy_ObjId(pObj) ) return Ivy_ObjFaninC0(pObj); 
    if ( Ivy_ObjFaninId1(pFanout) == Ivy_ObjId(pObj) ) return Ivy_ObjFaninC1(pObj); 
    assert(0); return -1; 
}

// create the ghost of the new node
static inline Ivy_Obj_t *  Ivy_ObjCreateGhost( Ivy_Obj_t * p0, Ivy_Obj_t * p1, Ivy_Type_t Type, Ivy_Init_t Init )    
{
    Ivy_Obj_t * pGhost;
    int Temp;
    pGhost = Ivy_ObjGhost(Ivy_Regular(p0));
    pGhost->Type = Type;
    pGhost->Init = Init;
    pGhost->fComp0 = Ivy_IsComplement(p0);
    pGhost->fComp1 = Ivy_IsComplement(p1);
    pGhost->Fanin0 = Ivy_ObjId(Ivy_Regular(p0));
    pGhost->Fanin1 = Ivy_ObjId(Ivy_Regular(p1));
    if ( pGhost->Fanin0 < pGhost->Fanin1 )
    {
        Temp = pGhost->Fanin0, pGhost->Fanin0 = pGhost->Fanin1, pGhost->Fanin1 = Temp;
        Temp = pGhost->fComp0, pGhost->fComp0 = pGhost->fComp1, pGhost->fComp1 = Temp;
    }
    assert( Ivy_ObjIsOneFanin(pGhost) || pGhost->Fanin0 > pGhost->Fanin1 );
    return pGhost;
}

// create the ghost of the new node
static inline Ivy_Obj_t *  Ivy_ObjCreateGhost2( Ivy_Man_t * p, Ivy_Obj_t * pObjDead )    
{
    Ivy_Obj_t * pGhost;
    pGhost = Ivy_ManGhost(p);
    pGhost->Type   = pObjDead->Type;
    pGhost->Init   = pObjDead->Init;
    pGhost->fComp0 = pObjDead->fComp0;
    pGhost->fComp1 = pObjDead->fComp1;
    pGhost->Fanin0 = pObjDead->Fanin0;
    pGhost->Fanin1 = pObjDead->Fanin1;
    assert( Ivy_ObjIsOneFanin(pGhost) || pGhost->Fanin0 > pGhost->Fanin1 );
    return pGhost;
}

// get the complemented initial state
static Ivy_Init_t Ivy_InitNotCond( Ivy_Init_t Init, int fCompl )
{
    assert( Init != IVY_INIT_NONE );
    if ( fCompl == 0 )
        return Init;
    if ( Init == IVY_INIT_0 )
        return IVY_INIT_1;
    if ( Init == IVY_INIT_1 )
        return IVY_INIT_0;
    return IVY_INIT_DC;
}

// get the initial state after forward retiming over AND gate
static Ivy_Init_t Ivy_InitAnd( Ivy_Init_t InitA, Ivy_Init_t InitB )
{
    assert( InitA != IVY_INIT_NONE && InitB != IVY_INIT_NONE );
    if ( InitA == IVY_INIT_0 || InitB == IVY_INIT_0 )
        return IVY_INIT_0;
    if ( InitA == IVY_INIT_DC || InitB == IVY_INIT_DC )
        return IVY_INIT_DC;
    return IVY_INIT_1;
}

// get the initial state after forward retiming over EXOR gate
static Ivy_Init_t Ivy_InitExor( Ivy_Init_t InitA, Ivy_Init_t InitB )
{
    assert( InitA != IVY_INIT_NONE && InitB != IVY_INIT_NONE );
    if ( InitA == IVY_INIT_DC || InitB == IVY_INIT_DC )
        return IVY_INIT_DC;
    if ( InitA == IVY_INIT_0 && InitB == IVY_INIT_1 )
        return IVY_INIT_1;
    if ( InitA == IVY_INIT_1 && InitB == IVY_INIT_0 )
        return IVY_INIT_1;
    return IVY_INIT_0;
}

// extended fanins
static inline Vec_Int_t *  Ivy_ObjGetFanins( Ivy_Obj_t * pObj )                      { assert(Ivy_ObjMan(pObj)->fExtended); return (Vec_Int_t *)*(((int*)pObj)+2);            }
static inline void         Ivy_ObjSetFanins( Ivy_Obj_t * pObj, Vec_Int_t * vFanins ) { assert(Ivy_ObjMan(pObj)->fExtended); assert(Ivy_ObjGetFanins(pObj)==NULL); *(Vec_Int_t **)(((int*)pObj)+2) = vFanins; }
static inline void         Ivy_ObjStartFanins( Ivy_Obj_t * pObj, int nFanins )       { assert(Ivy_ObjMan(pObj)->fExtended); Ivy_ObjSetFanins( pObj, Vec_IntAlloc(nFanins) );  }
static inline void         Ivy_ObjAddFanin( Ivy_Obj_t * pObj, int Fanin )            { assert(Ivy_ObjMan(pObj)->fExtended); Vec_IntPush( Ivy_ObjGetFanins(pObj), Fanin );     }
static inline int          Ivy_ObjReadFanin( Ivy_Obj_t * pObj, int i )               { assert(Ivy_ObjMan(pObj)->fExtended); return Vec_IntEntry( Ivy_ObjGetFanins(pObj), i ); }
static inline int          Ivy_ObjFaninNum( Ivy_Obj_t * pObj )                       { assert(Ivy_ObjMan(pObj)->fExtended); return Vec_IntSize( Ivy_ObjGetFanins(pObj) );     }

////////////////////////////////////////////////////////////////////////
///                             ITERATORS                            ///
////////////////////////////////////////////////////////////////////////

// iterator over all objects, including those currently not used
#define Ivy_ManForEachObj( p, pObj, i )                                                  \
    for ( i = 0, pObj = p->pObjs; i < p->ObjIdNext; i++, pObj++ )
#define Ivy_ManForEachObjReverse( p, pObj, i )                                           \
    for ( i = p->ObjIdNext - 1, pObj = p->pObjs + i; i >= 0; i--, pObj-- )
// iterator over the primary inputs
#define Ivy_ManForEachPi( p, pObj, i )                                                   \
    for ( i = 0; i < Vec_IntSize(p->vPis) && ((pObj) = Ivy_ManPi(p, i)); i++ )
// iterator over the primary outputs
#define Ivy_ManForEachPo( p, pObj, i )                                                   \
    for ( i = 0; i < Vec_IntSize(p->vPos) && ((pObj) = Ivy_ManPo(p, i)); i++ )
// iterator over the combinational inputs
#define Ivy_ManForEachCi( p, pObj, i )                                                   \
    for ( i = 0, pObj = p->pObjs; i < p->ObjIdNext; i++, pObj++ )                        \
        if ( !Ivy_ObjIsCi(pObj) ) {} else
// iterator over the combinational outputs
#define Ivy_ManForEachCo( p, pObj, i )                                                   \
    for ( i = 0, pObj = p->pObjs; i < p->ObjIdNext; i++, pObj++ )                        \
        if ( !Ivy_ObjIsCo(pObj) ) {} else
// iterator over logic nodes (AND and EXOR gates)
#define Ivy_ManForEachNode( p, pObj, i )                                                 \
    for ( i = 1, pObj = p->pObjs+i; i < p->ObjIdNext; i++, pObj++ )                      \
        if ( !Ivy_ObjIsNode(pObj) ) {} else
// iterator over logic latches
#define Ivy_ManForEachLatch( p, pObj, i )                                                \
    for ( i = 1, pObj = p->pObjs+i; i < p->ObjIdNext; i++, pObj++ )                      \
        if ( !Ivy_ObjIsLatch(pObj) ) {} else
// iterator over the nodes whose IDs are stored in the array
#define Ivy_ManForEachNodeVec( p, vIds, pObj, i )                                        \
    for ( i = 0; i < Vec_IntSize(vIds) && ((pObj) = Ivy_ManObj(p, Vec_IntEntry(vIds,i))); i++ )

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== ivyBalance.c ========================================================*/
extern Ivy_Man_t *     Ivy_ManBalance( Ivy_Man_t * p, int fUpdateLevel );
extern Ivy_Obj_t *     Ivy_NodeBalanceBuildSuper( Vec_Ptr_t * vSuper, Ivy_Type_t Type, int fUpdateLevel );
/*=== ivyCanon.c ========================================================*/
extern Ivy_Obj_t *     Ivy_CanonAnd( Ivy_Obj_t * p0, Ivy_Obj_t * p1 );
extern Ivy_Obj_t *     Ivy_CanonExor( Ivy_Obj_t * p0, Ivy_Obj_t * p1 );
extern Ivy_Obj_t *     Ivy_CanonLatch( Ivy_Obj_t * pObj, Ivy_Init_t Init );
/*=== ivyCheck.c ========================================================*/
extern int             Ivy_ManCheck( Ivy_Man_t * p );
/*=== ivyCut.c ==========================================================*/
extern void            Ivy_ManSeqFindCut( Ivy_Obj_t * pNode, Vec_Int_t * vFront, Vec_Int_t * vInside, int nSize );
extern Ivy_Store_t *   Ivy_NodeFindCutsAll( Ivy_Obj_t * pObj, int nLeaves );
/*=== ivyDfs.c ==========================================================*/
extern Vec_Int_t *     Ivy_ManDfs( Ivy_Man_t * p );
extern Vec_Int_t *     Ivy_ManDfsExt( Ivy_Man_t * p );
extern void            Ivy_ManCollectCone( Ivy_Obj_t * pObj, Vec_Ptr_t * vFront, Vec_Ptr_t * vCone );
extern Vec_Vec_t *     Ivy_ManLevelize( Ivy_Man_t * p );
extern Vec_Int_t *     Ivy_ManRequiredLevels( Ivy_Man_t * p );
/*=== ivyDsd.c ==========================================================*/
extern int             Ivy_TruthDsd( unsigned uTruth, Vec_Int_t * vTree );
extern void            Ivy_TruthDsdPrint( FILE * pFile, Vec_Int_t * vTree );
extern unsigned        Ivy_TruthDsdCompute( Vec_Int_t * vTree );
extern void            Ivy_TruthDsdComputePrint( unsigned uTruth );
extern Ivy_Obj_t *     Ivy_ManDsdConstruct( Ivy_Man_t * p, Vec_Int_t * vFront, Vec_Int_t * vTree );
/*=== ivyMan.c ==========================================================*/
extern Ivy_Man_t *     Ivy_ManStart( int nPis, int nPos, int nNodesMax );
extern void            Ivy_ManStop( Ivy_Man_t * p );
extern void            Ivy_ManGrow( Ivy_Man_t * p );
extern int             Ivy_ManCleanup( Ivy_Man_t * p );
extern void            Ivy_ManPrintStats( Ivy_Man_t * p );
/*=== ivyMulti.c ==========================================================*/
extern Ivy_Obj_t *     Ivy_Multi( Ivy_Obj_t ** pArgs, int nArgs, Ivy_Type_t Type );
extern Ivy_Obj_t *     Ivy_Multi1( Ivy_Obj_t ** pArgs, int nArgs, Ivy_Type_t Type );
extern Ivy_Obj_t *     Ivy_Multi_rec( Ivy_Obj_t ** ppObjs, int nObjs, Ivy_Type_t Type );
extern Ivy_Obj_t *     Ivy_MultiBalance_rec( Ivy_Obj_t ** pArgs, int nArgs, Ivy_Type_t Type );
extern int             Ivy_MultiPlus( Vec_Ptr_t * vLeaves, Vec_Ptr_t * vCone, Ivy_Type_t Type, int nLimit, Vec_Ptr_t * vSol );
/*=== ivyObj.c ==========================================================*/
extern Ivy_Obj_t *     Ivy_ObjCreate( Ivy_Obj_t * pGhost );
extern Ivy_Obj_t *     Ivy_ObjCreateExt( Ivy_Man_t * p, Ivy_Type_t Type );
extern void            Ivy_ObjConnect( Ivy_Obj_t * pObj, Ivy_Obj_t * pFanin );
extern void            Ivy_ObjDelete( Ivy_Obj_t * pObj, int fFreeTop );
extern void            Ivy_ObjDelete_rec( Ivy_Obj_t * pObj, int fFreeTop );
extern void            Ivy_ObjReplace( Ivy_Obj_t * pObjOld, Ivy_Obj_t * pObjNew, int fDeleteOld, int fFreeTop );
extern void            Ivy_NodeFixBufferFanins( Ivy_Obj_t * pNode );
/*=== ivyOper.c =========================================================*/
extern Ivy_Obj_t *     Ivy_Oper( Ivy_Obj_t * p0, Ivy_Obj_t * p1, Ivy_Type_t Type );
extern Ivy_Obj_t *     Ivy_And( Ivy_Obj_t * p0, Ivy_Obj_t * p1 );
extern Ivy_Obj_t *     Ivy_Or( Ivy_Obj_t * p0, Ivy_Obj_t * p1 );
extern Ivy_Obj_t *     Ivy_Exor( Ivy_Obj_t * p0, Ivy_Obj_t * p1 );
extern Ivy_Obj_t *     Ivy_Mux( Ivy_Obj_t * pC, Ivy_Obj_t * p1, Ivy_Obj_t * p0 );
extern Ivy_Obj_t *     Ivy_Maj( Ivy_Obj_t * pA, Ivy_Obj_t * pB, Ivy_Obj_t * pC );
extern Ivy_Obj_t *     Ivy_Miter( Vec_Ptr_t * vPairs );
/*=== ivyResyn.c =========================================================*/
extern Ivy_Man_t *     Ivy_ManResyn( Ivy_Man_t * p, int fUpdateLevel );
/*=== ivyRewrite.c =========================================================*/
extern int             Ivy_ManSeqRewrite( Ivy_Man_t * p, int fUpdateLevel, int fUseZeroCost );
extern int             Ivy_ManRewriteAlg( Ivy_Man_t * p, int fUpdateLevel, int fUseZeroCost );
extern int             Ivy_ManRewritePre( Ivy_Man_t * p, int fUpdateLevel, int fUseZeroCost, int fVerbose );
/*=== ivyTable.c ========================================================*/
extern Ivy_Obj_t *     Ivy_TableLookup( Ivy_Obj_t * pObj );
extern void            Ivy_TableInsert( Ivy_Obj_t * pObj );
extern void            Ivy_TableDelete( Ivy_Obj_t * pObj );
extern void            Ivy_TableUpdate( Ivy_Obj_t * pObj, int ObjIdNew );
extern int             Ivy_TableCountEntries( Ivy_Man_t * p );
extern void            Ivy_TableResize( Ivy_Man_t * p );
/*=== ivyUndo.c =========================================================*/
extern void            Ivy_ManUndoStart( Ivy_Man_t * p );
extern void            Ivy_ManUndoStop( Ivy_Man_t * p );
extern void            Ivy_ManUndoRecord( Ivy_Man_t * p, Ivy_Obj_t * pObj );
extern void            Ivy_ManUndoPerform( Ivy_Man_t * p, Ivy_Obj_t * pRoot );
/*=== ivyUtil.c =========================================================*/
extern void            Ivy_ManIncrementTravId( Ivy_Man_t * p );
extern void            Ivy_ManCleanTravId( Ivy_Man_t * p );
extern int             Ivy_ObjIsMuxType( Ivy_Obj_t * pObj );
extern Ivy_Obj_t *     Ivy_ObjRecognizeMux( Ivy_Obj_t * pObj, Ivy_Obj_t ** ppObjT, Ivy_Obj_t ** ppObjE );
extern unsigned *      Ivy_ManCutTruth( Ivy_Obj_t * pRoot, Vec_Int_t * vLeaves, Vec_Int_t * vNodes, Vec_Int_t * vTruth );
extern Ivy_Obj_t *     Ivy_NodeRealFanin_rec( Ivy_Obj_t * pNode, int iFanin );
extern Vec_Int_t *     Ivy_ManLatches( Ivy_Man_t * p );
extern int             Ivy_ManReadLevels( Ivy_Man_t * p );
extern Ivy_Obj_t *     Ivy_ObjReal( Ivy_Obj_t * pObj );

#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

