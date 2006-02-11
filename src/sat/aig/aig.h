/**CFile****************************************************************

  FileName    [aig.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: aig.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __AIG_H__
#define __AIG_H__

/*
    AIG is an And-Inv Graph with structural hashing.
    It is always structurally hashed. It means that at any time:
    - for each AND gate, there are no other AND gates with the same children
    - the constants are propagated
    - there is no single-input nodes (inverters/buffers)
    Additionally the following invariants are satisfied:
    - there are no dangling nodes (the nodes without fanout)
    - the level of each AND gate reflects the levels of this fanins
    - the AND nodes are in the topological order
    - the constant 1 node has always number 0 in the object list
    The operations that are performed on AIGs:
    - building new nodes (Aig_And)
    - performing elementary Boolean operations (Aig_Or, Aig_Xor, etc)
    - replacing one node by another (Abc_AigReplace)
    - propagating constants (Abc_AigReplace)
    - deleting dangling nodes (Abc_AigDelete)
    When AIG is duplicated, the new graph is structurally hashed too.
    If this repeated hashing leads to fewer nodes, it means the original
    AIG was not strictly hashed (one of the conditions above is violated).
*/

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include "solver.h"
#include "vec.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

//typedef int                   bool;
#ifndef bool
#define bool int
#endif

typedef struct Aig_Param_t_     Aig_Param_t;
typedef struct Aig_Man_t_       Aig_Man_t;
typedef struct Aig_Node_t_      Aig_Node_t;
typedef struct Aig_Edge_t_      Aig_Edge_t;
typedef struct Aig_MemFixed_t_  Aig_MemFixed_t;
typedef struct Aig_SimInfo_t_   Aig_SimInfo_t;
typedef struct Aig_Table_t_     Aig_Table_t;
typedef struct Aig_Pattern_t_   Aig_Pattern_t;

// network types
typedef enum { 
    AIG_NONE = 0,  // 0: unknown
    AIG_PI,        // 1: primary input
    AIG_PO,        // 2: primary output
    AIG_AND        // 3: internal node
} Aig_NodeType_t;

// proof outcomes
typedef enum { 
    AIG_PROOF_NONE = 0,  // 0: unknown
    AIG_PROOF_SAT,       // 1: primary input
    AIG_PROOF_UNSAT,     // 2: primary output
    AIG_PROOF_TIMEOUT,   // 3: primary output
    AIG_PROOF_FAIL       // 4: internal node
} Aig_ProofType_t;



// the AIG parameters
struct Aig_Param_t_
{
    int              nPatsRand;     // the number of random patterns
    int              nBTLimit;      // backtrack limit at the intermediate nodes
    int              nSeconds;      // the runtime limit at the final miter
    int              fVerbose;      // verbosity
    int              fSatVerbose;   // verbosity of SAT
};

// the AIG edge 
struct Aig_Edge_t_ 
{
    unsigned         iNode   : 31;  // the node
    unsigned         fComp   :  1;  // the complemented attribute
};

// the AIG node
struct Aig_Node_t_  // 8 words
{
    // various numbers associated with the node
    int              Id;            // the unique number (SAT var number) of this node 
    int              nRefs;         // the reference counter
    unsigned         Type    :  2;  // the node type
    unsigned         fPhase  :  1;  // the phase of this node
    unsigned         fMarkA  :  1;  // the mask
    unsigned         fMarkB  :  1;  // the mask
    unsigned         fMarkC  :  1;  // the mask
    unsigned         TravId  : 26;  // the traversal ID
    unsigned         Level   : 16;  // the direct level of the node
    unsigned         LevelR  : 16;  // the reverse level of the node
    Aig_Edge_t       Fans[2];       // the fanins
    int              NextH;         // next node in the hash table          
    int              Data;          // miscelleneous data
    Aig_Man_t *      pMan;          // the parent manager
};

// the AIG manager
struct Aig_Man_t_
{
    // the AIG parameters
    Aig_Param_t      Param;         // the full set of AIG parameters
    Aig_Param_t *    pParam;        // the pointer to the above set
    // the nodes
    Aig_Node_t *     pConst1;       // the constant 1 node (ID=0)
    Vec_Ptr_t *      vNodes;        // all nodes by ID
    Vec_Ptr_t *      vPis;          // all PIs
    Vec_Ptr_t *      vPos;          // all POs
    Aig_Table_t *    pTable;        // structural hash table
    int              nLevelMax;     // the maximum level
    // SAT solver and related structures
    solver *         pSat;
    Vec_Int_t *      vVar2Sat;      // mapping of nodes into their SAT var numbers (for each node num)
    Vec_Int_t *      vSat2Var;      // mapping of the SAT var numbers into nodes (for each SAT var)
    Vec_Int_t *      vPiSatNums;    // the SAT variable numbers (for each PI)
    int *            pModel;        // the satisfying assignment (for each PI)
    int              nMuxes;        // the number of MUXes
    // fanout representation
    Vec_Ptr_t *      vFanPivots;    // fanout pivots
    Vec_Ptr_t *      vFanFans0;     // the next fanout of the first fanin
    Vec_Ptr_t *      vFanFans1;     // the next fanout of the second fanin 
    // the memory managers
    Aig_MemFixed_t * mmNodes;       // the memory manager for nodes
    int              nTravIds;      // the traversal ID
    // simulation info
    Aig_SimInfo_t *  pInfo;         // random and systematic sim info for PIs
    Aig_SimInfo_t *  pInfoPi;       // temporary sim info for the PI nodes
    Aig_SimInfo_t *  pInfoTemp;     // temporary sim info for all nodes
    Aig_Pattern_t *  pPatMask;      // the mask which shows what patterns are used
    // simulation patterns
    int              nPiWords;      // the number of words in the PI info
    int              nPatsMax;      // the max number of patterns 
    Vec_Ptr_t *      vPats;         // simulation patterns to try
    // equivalence classes
    Vec_Vec_t *      vClasses;      // the non-trival equivalence classes of nodes
    // temporary data
    Vec_Ptr_t *      vFanouts;      // temporary storage for fanouts of a node
    Vec_Ptr_t *      vToReplace;    // the nodes to replace
    Vec_Int_t *      vClassTemp;    // temporary class representatives
};

// the simulation patter
struct Aig_Pattern_t_  
{
    int              nBits;
    int              nWords;
    unsigned *       pData;
};

// the AIG simulation info
struct Aig_SimInfo_t_  
{
    int              Type;          // the type (0 = PI, 1 = all)
    int              nNodes;        // the number of nodes for which allocated
    int              nWords;        // the number of words for each node
    int              nPatsMax;      // the maximum number of patterns
    int              nPatsCur;      // the current number of patterns
    unsigned *       pData;         // the simulation data
};

// iterators over nodes, PIs, POs, ANDs
#define Aig_ManForEachNode( pMan, pNode, i )                                                  \
    for ( i = 0; (i < Aig_ManNodeNum(pMan)) && (((pNode) = Aig_ManNode(pMan, i)), 1); i++ )
#define Aig_ManForEachPi( pMan, pNode, i )                                                    \
    for ( i = 0; (i < Aig_ManPiNum(pMan)) && (((pNode) = Aig_ManPi(pMan, i)), 1); i++ )
#define Aig_ManForEachPo( pMan, pNode, i )                                                    \
    for ( i = 0; (i < Aig_ManPoNum(pMan)) && (((pNode) = Aig_ManPo(pMan, i)), 1); i++ )
#define Aig_ManForEachAnd( pMan, pNode, i )                                                   \
    for ( i = 0; (i < Aig_ManNodeNum(pMan)) && (((pNode) = Aig_ManNode(pMan, i)), 1); i++ )   \
        if ( !Aig_NodeIsAnd(pNode) ) {} else

// maximum/minimum operators
#define AIG_MIN(a,b)  (((a) < (b))? (a) : (b))
#define AIG_MAX(a,b)  (((a) > (b))? (a) : (b))

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

static inline int          Aig_BitWordNum( int nBits )            { return nBits/32 + ((nBits%32) > 0);       }
static inline int          Aig_InfoHasBit( unsigned * p, int i )  { return (p[(i)>>5] & (1<<((i) & 31))) > 0; }
static inline void         Aig_InfoSetBit( unsigned * p, int i )  { p[(i)>>5] |= (1<<((i) & 31));             }
static inline void         Aig_InfoXorBit( unsigned * p, int i )  { p[(i)>>5] ^= (1<<((i) & 31));             }

static inline Aig_Node_t * Aig_ManConst1( Aig_Man_t * pMan )      { return pMan->pConst1;                  }
static inline Aig_Node_t * Aig_ManNode( Aig_Man_t * pMan, int i ) { return Vec_PtrEntry(pMan->vNodes, i);  }
static inline Aig_Node_t * Aig_ManPi( Aig_Man_t * pMan, int i )   { return Vec_PtrEntry(pMan->vPis, i);    }
static inline Aig_Node_t * Aig_ManPo( Aig_Man_t * pMan, int i )   { return Vec_PtrEntry(pMan->vPos, i);    }

static inline int          Aig_ManNodeNum( Aig_Man_t * pMan )     { return Vec_PtrSize(pMan->vNodes);      }
static inline int          Aig_ManPiNum( Aig_Man_t * pMan )       { return Vec_PtrSize(pMan->vPis);        }
static inline int          Aig_ManPoNum( Aig_Man_t * pMan )       { return Vec_PtrSize(pMan->vPos);        }
static inline int          Aig_ManAndNum( Aig_Man_t * pMan )      { return Aig_ManNodeNum(pMan)-Aig_ManPiNum(pMan)-Aig_ManPoNum(pMan)-1;  }

static inline Aig_Node_t * Aig_Regular( Aig_Node_t * p )          { return (Aig_Node_t *)((unsigned)(p) & ~01);  }
static inline Aig_Node_t * Aig_Not( Aig_Node_t * p )              { return (Aig_Node_t *)((unsigned)(p) ^  01);  }
static inline Aig_Node_t * Aig_NotCond( Aig_Node_t * p, int c )   { return (Aig_Node_t *)((unsigned)(p) ^ (c));  }
static inline bool         Aig_IsComplement( Aig_Node_t * p )     { return (bool)(((unsigned)p) & 01);           }

static inline bool         Aig_NodeIsConst( Aig_Node_t * pNode )  { return Aig_Regular(pNode)->Id == 0;          }
static inline bool         Aig_NodeIsPi( Aig_Node_t * pNode )     { return Aig_Regular(pNode)->Type == AIG_PI;   }
static inline bool         Aig_NodeIsPo( Aig_Node_t * pNode )     { return Aig_Regular(pNode)->Type == AIG_PO;   }
static inline bool         Aig_NodeIsAnd( Aig_Node_t * pNode )    { return Aig_Regular(pNode)->Type == AIG_AND;  }

static inline int          Aig_NodeId( Aig_Node_t * pNode )       { assert( !Aig_IsComplement(pNode) ); return pNode->Id;                      }
static inline int          Aig_NodeRefs( Aig_Node_t * pNode )     { assert( !Aig_IsComplement(pNode) ); return pNode->nRefs;                   }
static inline bool         Aig_NodePhase( Aig_Node_t * pNode )    { assert( !Aig_IsComplement(pNode) ); return pNode->fPhase;                  }
static inline int          Aig_NodeLevel( Aig_Node_t * pNode )    { assert( !Aig_IsComplement(pNode) ); return pNode->Level;                   }
static inline int          Aig_NodeLevelR( Aig_Node_t * pNode )   { assert( !Aig_IsComplement(pNode) ); return pNode->LevelR;                  }
static inline int          Aig_NodeData( Aig_Node_t * pNode )     { assert( !Aig_IsComplement(pNode) ); return pNode->Data;                    }
static inline Aig_Man_t *  Aig_NodeMan( Aig_Node_t * pNode )      { assert( !Aig_IsComplement(pNode) ); return pNode->pMan;                    }
static inline int          Aig_NodeFaninId0( Aig_Node_t * pNode ) { assert( !Aig_IsComplement(pNode) ); return pNode->Fans[0].iNode;           }
static inline int          Aig_NodeFaninId1( Aig_Node_t * pNode ) { assert( !Aig_IsComplement(pNode) ); return pNode->Fans[1].iNode;           }
static inline bool         Aig_NodeFaninC0( Aig_Node_t * pNode )  { assert( !Aig_IsComplement(pNode) ); return pNode->Fans[0].fComp;           }
static inline bool         Aig_NodeFaninC1( Aig_Node_t * pNode )  { assert( !Aig_IsComplement(pNode) ); return pNode->Fans[1].fComp;           }
static inline Aig_Node_t * Aig_NodeFanin0( Aig_Node_t * pNode )   { return Aig_ManNode( Aig_NodeMan(pNode), Aig_NodeFaninId0(pNode) );   }
static inline Aig_Node_t * Aig_NodeFanin1( Aig_Node_t * pNode )   { return Aig_ManNode( Aig_NodeMan(pNode), Aig_NodeFaninId1(pNode) );   }
static inline Aig_Node_t * Aig_NodeChild0( Aig_Node_t * pNode )   { return Aig_NotCond( Aig_NodeFanin0(pNode), Aig_NodeFaninC0(pNode) ); }
static inline Aig_Node_t * Aig_NodeChild1( Aig_Node_t * pNode )   { return Aig_NotCond( Aig_NodeFanin1(pNode), Aig_NodeFaninC1(pNode) ); }
static inline Aig_Node_t * Aig_NodeNextH( Aig_Node_t * pNode )    { return pNode->NextH? Aig_ManNode(pNode->pMan, pNode->NextH) : NULL;  }
static inline int          Aig_NodeWhatFanin( Aig_Node_t * pNode, Aig_Node_t * pFanin )    { if ( Aig_NodeFaninId0(pNode) == pFanin->Id ) return 0; if ( Aig_NodeFaninId1(pNode) == pFanin->Id ) return 1; assert(0); return -1; }
static inline int          Aig_NodeGetLevelNew( Aig_Node_t * pNode )   { return 1 + AIG_MAX(Aig_NodeFanin0(pNode)->Level, Aig_NodeFanin1(pNode)->Level); }
static inline int          Aig_NodeRequiredLevel( Aig_Node_t * pNode ) { return pNode->pMan->nLevelMax + 1 - pNode->LevelR; }

static inline unsigned *   Aig_SimInfoForNodeId( Aig_SimInfo_t * p, int NodeId )        { assert(  p->Type ); return p->pData + p->nWords * NodeId;    }
static inline unsigned *   Aig_SimInfoForNode( Aig_SimInfo_t * p, Aig_Node_t * pNode )  { assert(  p->Type ); return p->pData + p->nWords * pNode->Id; }
static inline unsigned *   Aig_SimInfoForPi( Aig_SimInfo_t * p, int Num )               { assert( !p->Type ); return p->pData + p->nWords * Num;       }

static inline void         Aig_NodeSetTravId( Aig_Node_t * pNode, int TravId ) { pNode->TravId = TravId;                                    }
static inline void         Aig_NodeSetTravIdCurrent( Aig_Node_t * pNode )      { pNode->TravId = pNode->pMan->nTravIds;                     }
static inline void         Aig_NodeSetTravIdPrevious( Aig_Node_t * pNode )     { pNode->TravId = pNode->pMan->nTravIds - 1;                 }
static inline bool         Aig_NodeIsTravIdCurrent( Aig_Node_t * pNode )       { return (bool)((int)pNode->TravId == pNode->pMan->nTravIds);     }
static inline bool         Aig_NodeIsTravIdPrevious( Aig_Node_t * pNode )      { return (bool)((int)pNode->TravId == pNode->pMan->nTravIds - 1); }


////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== aigCheck.c ==========================================================*/
extern bool                Aig_ManCheck( Aig_Man_t * pMan );
extern bool                Aig_NodeIsAcyclic( Aig_Node_t * pNode, Aig_Node_t * pRoot );
/*=== aigFanout.c ==========================================================*/
extern void                Aig_ManCreateFanouts( Aig_Man_t * p );
extern void                Aig_NodeAddFaninFanout( Aig_Node_t * pFanin, Aig_Node_t * pFanout );
extern void                Aig_NodeRemoveFaninFanout( Aig_Node_t * pFanin, Aig_Node_t * pFanoutToRemove );
extern int                 Aig_NodeGetFanoutNum( Aig_Node_t * pNode );
extern Vec_Ptr_t *         Aig_NodeGetFanouts( Aig_Node_t * pNode );
extern int                 Aig_NodeGetLevelRNew( Aig_Node_t * pNode );
extern int                 Aig_ManSetLevelR( Aig_Man_t * pMan );
extern int                 Aig_ManGetLevelMax( Aig_Man_t * pMan );
extern int                 Aig_NodeUpdateLevel_int( Aig_Node_t * pNode );
extern int                 Aig_NodeUpdateLevelR_int( Aig_Node_t * pNode );
/*=== aigMem.c =============================================================*/
extern Aig_MemFixed_t *    Aig_MemFixedStart( int nEntrySize );
extern void                Aig_MemFixedStop( Aig_MemFixed_t * p, int fVerbose );
extern char *              Aig_MemFixedEntryFetch( Aig_MemFixed_t * p );
extern void                Aig_MemFixedEntryRecycle( Aig_MemFixed_t * p, char * pEntry );
extern void                Aig_MemFixedRestart( Aig_MemFixed_t * p );
extern int                 Aig_MemFixedReadMemUsage( Aig_MemFixed_t * p );
/*=== aigMan.c =============================================================*/
extern void                Aig_ManSetDefaultParams( Aig_Param_t * pParam );
extern Aig_Man_t *         Aig_ManStart( Aig_Param_t * pParam );
extern int                 Aig_ManCleanup( Aig_Man_t * pMan );
extern void                Aig_ManStop( Aig_Man_t * p );
/*=== aigNode.c =============================================================*/
extern Aig_Node_t *        Aig_NodeCreateConst( Aig_Man_t * p );
extern Aig_Node_t *        Aig_NodeCreatePi( Aig_Man_t * p );
extern Aig_Node_t *        Aig_NodeCreatePo( Aig_Man_t * p, Aig_Node_t * pFanin );
extern Aig_Node_t *        Aig_NodeCreateAnd( Aig_Man_t * p, Aig_Node_t * pFanin0, Aig_Node_t * pFanin1 );
extern void                Aig_NodeConnectAnd( Aig_Node_t * pFanin0, Aig_Node_t * pFanin1, Aig_Node_t * pNode );
extern void                Aig_NodeDisconnectAnd( Aig_Node_t * pNode );
extern void                Aig_NodeDeleteAnd_rec( Aig_Man_t * pMan, Aig_Node_t * pRoot );
extern void                Aig_NodePrint( Aig_Node_t * pNode );
extern char *              Aig_NodeName( Aig_Node_t * pNode );
extern void                Aig_PrintNode( Aig_Node_t * pNode );
/*=== aigOper.c ==========================================================*/
extern Aig_Node_t *        Aig_And( Aig_Man_t * pMan, Aig_Node_t * p0, Aig_Node_t * p1 );
extern Aig_Node_t *        Aig_Or( Aig_Man_t * pMan, Aig_Node_t * p0, Aig_Node_t * p1 );
extern Aig_Node_t *        Aig_Xor( Aig_Man_t * pMan, Aig_Node_t * p0, Aig_Node_t * p1 );
extern Aig_Node_t *        Aig_Mux( Aig_Man_t * pMan, Aig_Node_t * pC, Aig_Node_t * p1, Aig_Node_t * p0 );
extern Aig_Node_t *        Aig_Miter( Aig_Man_t * pMan, Vec_Ptr_t * vPairs );
/*=== aigReplace.c ==========================================================*/
extern void                Aig_ManReplaceNode( Aig_Man_t * pMan, Aig_Node_t * pOld, Aig_Node_t * pNew, int fUpdateLevel );
/*=== aigTable.c ==========================================================*/
extern Aig_Table_t *       Aig_TableCreate( int nSize );
extern void                Aig_TableFree( Aig_Table_t * p );
extern int                 Aig_TableNumNodes( Aig_Table_t * p );
extern Aig_Node_t *        Aig_TableLookupNode( Aig_Man_t * pMan, Aig_Node_t * p0, Aig_Node_t * p1 );
extern Aig_Node_t *        Aig_TableInsertNode( Aig_Man_t * pMan, Aig_Node_t * p0, Aig_Node_t * p1, Aig_Node_t * pAnd );
extern void                Aig_TableDeleteNode( Aig_Man_t * pMan, Aig_Node_t * pThis );
extern void                Aig_TableResize( Aig_Man_t * pMan );
extern void                Aig_TableRehash( Aig_Man_t * pMan );
/*=== aigUtil.c ==========================================================*/
extern void                Aig_ManIncrementTravId( Aig_Man_t * pMan );
extern bool                Aig_NodeIsMuxType( Aig_Node_t * pNode );
extern Aig_Node_t *        Aig_NodeRecognizeMux( Aig_Node_t * pNode, Aig_Node_t ** ppNodeT, Aig_Node_t ** ppNodeE );


/*=== fraigCore.c ==========================================================*/
extern Aig_ProofType_t     Aig_FraigProve( Aig_Man_t * pMan );
/*=== fraigClasses.c ==========================================================*/
extern Vec_Vec_t *         Aig_ManDeriveClassesFirst( Aig_Man_t * p, Aig_SimInfo_t * pInfoAll );
extern int                 Aig_ManUpdateClasses( Aig_Man_t * p, Aig_SimInfo_t * pInfo, Vec_Vec_t * vClasses, Aig_Pattern_t * pPatMask );
extern void                Aig_ManCollectPatterns( Aig_Man_t * p, Aig_SimInfo_t * pInfo, Aig_Pattern_t * pMask, Vec_Ptr_t * vPats );
/*=== fraigCnf.c ==========================================================*/
extern Aig_ProofType_t     Aig_ClauseSolverStart( Aig_Man_t * pMan );
/*=== fraigEngine.c ==========================================================*/
extern void                Aig_EngineSimulateRandomFirst( Aig_Man_t * p );
extern void                Aig_EngineSimulateFirst( Aig_Man_t * p );
extern int                 Aig_EngineSimulate( Aig_Man_t * p );
/*=== fraigSim.c ==========================================================*/
extern Aig_SimInfo_t *     Aig_SimInfoAlloc( int nNodes, int nBits, int Type );
extern void                Aig_SimInfoClean( Aig_SimInfo_t * p );
extern void                Aig_SimInfoRandom( Aig_SimInfo_t * p );
extern void                Aig_SimInfoFromPattern( Aig_SimInfo_t * p, Aig_Pattern_t * pPat );
extern void                Aig_SimInfoResize( Aig_SimInfo_t * p );
extern void                Aig_SimInfoFree( Aig_SimInfo_t * p );
extern void                Aig_ManSimulateInfo( Aig_Man_t * p, Aig_SimInfo_t * pInfoPi, Aig_SimInfo_t * pInfoAll );
extern Aig_Pattern_t *     Aig_PatternAlloc( int nBits );
extern void                Aig_PatternClean( Aig_Pattern_t * pPat );
extern void                Aig_PatternFill( Aig_Pattern_t * pPat );
extern int                 Aig_PatternCount( Aig_Pattern_t * pPat );
extern void                Aig_PatternRandom( Aig_Pattern_t * pPat );
extern void                Aig_PatternFree( Aig_Pattern_t * pPat );

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

#endif

