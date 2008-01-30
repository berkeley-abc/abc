/**CFile****************************************************************

  FileName    [abc.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abc.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef __ABC_H__
#define __ABC_H__

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <time.h>

#include "cuddInt.h"
#include "extra.h"
#include "solver.h"
#include "vec.h"
#include "stmm.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

// network types
typedef enum { 
    ABC_TYPE_NONE,      // 0:  unknown
    ABC_TYPE_NETLIST,   // 1:  network with PIs/POs, latches, nodes, and nets
    ABC_TYPE_LOGIC,     // 2:  network with PIs/POs, latches, and nodes
    ABC_TYPE_STRASH,    // 3:  structurally hashed AIG (two input AND gates with c-attributes on edges)
    ABC_TYPE_SEQ,       // 4:  sequential AIG (two input AND gates with c- and latch-attributes on edges)
    ABC_TYPE_OTHER      // 5:  unused
} Abc_NtkType_t;

// network functionality
typedef enum { 
    ABC_FUNC_NONE,      // 0:  unknown
    ABC_FUNC_SOP,       // 1:  sum-of-products
    ABC_FUNC_BDD,       // 2:  binary decision diagrams
    ABC_FUNC_AIG,       // 3:  and-inverter graphs
    ABC_FUNC_MAP,       // 4:  standard cell library
    ABC_FUNC_OTHER      // 5:  unused
} Abc_NtkFunc_t;

// Supported type/functionality combinations:
/*------------------------------------------|
|           |  SOP  |  BDD  |  AIG  |  Map  |
|-----------|-------|-------|-------|-------|
|  Netlist  |   x   |       |       |   x   |
|-----------|-------|-------|-------|-------|
|  Logic    |   x   |   x   |       |   x   |
|-----------|-------|-------|-------|-------|
|  Strash   |       |       |   x   |       |
|-----------|-------|-------|-------|-------|
|  Seq      |       |       |   x   |       | 
--------------------------------------------|*/

// object types
typedef enum { 
    ABC_OBJ_NONE,       // 0:  unknown
    ABC_OBJ_NET,        // 1:  net
    ABC_OBJ_NODE,       // 2:  node
    ABC_OBJ_LATCH,      // 3:  latch
    ABC_OBJ_PI,         // 4:  primary input terminal
    ABC_OBJ_PO,         // 5:  primary output terminal
    ABC_OBJ_OTHER       // 6:  unused
} Abc_ObjType_t;

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

//typedef int                   bool;
#ifndef bool
#define bool int
#endif

typedef struct Abc_Obj_t_     Abc_Obj_t;
typedef struct Abc_Ntk_t_     Abc_Ntk_t;
typedef struct Abc_Aig_t_     Abc_Aig_t;
typedef struct Abc_ManTime_t_ Abc_ManTime_t;
typedef struct Abc_ManCut_t_  Abc_ManCut_t;
typedef struct Abc_Time_t_    Abc_Time_t;

struct Abc_Time_t_
{
    float            Rise;
    float            Fall;
    float            Worst;
};

struct Abc_Obj_t_ // 12 words
{
    // high-level information
    Abc_Ntk_t *      pNtk;          // the host network
    unsigned         Type    :  4;  // the object type
    unsigned         fExor   :  1;  // marks AIG node that is a root of EXOR
    unsigned         Id      : 27;  // the ID of the object
    // internal information
    unsigned         fMarkA  :  1;  // the multipurpose mark
    unsigned         fMarkB  :  1;  // the multipurpose mark
    unsigned         fMarkC  :  1;  // the multipurpose mark
    unsigned         fPhase  :  1;  // the flag to mark the phase of equivalent node
    unsigned         TravId  : 12;  // the traversal ID
    unsigned         Level   : 16;  // the level of the node
    // connectivity
    Vec_Fan_t        vFanins;       // the array of fanins
    Vec_Fan_t        vFanouts;      // the array of fanouts
    // miscellaneous
    void *           pData;         // the network specific data (SOP, BDD, gate, equiv class, etc)
    Abc_Obj_t *      pNext;         // the next pointer in the hash table
    Abc_Obj_t *      pCopy;         // the copy of this object
};

struct Abc_Ntk_t_ 
{
    // general information 
    Abc_NtkType_t    ntkType;       // type of the network
    Abc_NtkFunc_t    ntkFunc;       // functionality of the network
    char *           pName;         // the network name
    char *           pSpec;         // the name of the spec file if present
    // name representation 
    stmm_table *     tName2Net;     // the table hashing net names into net pointer
    stmm_table *     tObj2Name;     // the table hashing PI/PO/latch pointers into names
    // components of the network
    Vec_Ptr_t *      vObjs;         // the array of all objects (net, nodes, latches)
    Vec_Ptr_t *      vCis;          // the array of combinational inputs  (PIs followed by latches)
    Vec_Ptr_t *      vCos;          // the array of combinational outputs (POs followed by latches)
    Vec_Ptr_t *      vLats;         // the array of latches (or the cutset in the sequential network)
    // the stats about the number of living objects
    int              nObjs;         // the number of living objs
    int              nNets;         // the number of living nets
    int              nNodes;        // the number of living nodes
    int              nLatches;      // the number of latches
    int              nPis;          // the number of primary inputs
    int              nPos;          // the number of primary outputs
    // the functionality manager 
    void *           pManFunc;      // AIG manager, BDD manager, or memory manager for SOPs
    // the global functions (BDDs)
    void *           pManGlob;      // the BDD manager
    Vec_Ptr_t *      vFuncsGlob;    // the BDDs of CO functions
    // the timing manager (for mapped networks)
    Abc_ManTime_t *  pManTime;      // stores arrival/required times for all nodes
    // the cut manager (for AIGs)
    void *           pManCut;       // stores information about the cuts computed for the nodes
    // level information (for AIGs)
    int              LevelMax;      // maximum number of levels
    Vec_Int_t *      vLevelsR;      // level in the reverse topological order 
    // support information
    Vec_Ptr_t *      vSupps;
    // the external don't-care if given
    Abc_Ntk_t *      pExdc;         // the EXDC network
    // miscellaneous data members
    unsigned         nTravIds;      // the unique traversal IDs of nodes
    Vec_Ptr_t *      vPtrTemp;      // the temporary array
    Vec_Int_t *      vIntTemp;      // the temporary array
    Vec_Str_t *      vStrTemp;      // the temporary array
    void *           pData;         // the temporary pointer
    // the backup network and the step number
    Abc_Ntk_t *      pNetBackup;    // the pointer to the previous backup network
    int              iStep;         // the generation number for the given network
    // memory management
    Extra_MmFlex_t * pMmNames;      // memory manager for net names
    Extra_MmFixed_t* pMmObj;        // memory manager for objects
    Extra_MmStep_t * pMmStep;       // memory manager for arrays
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFITIONS                             ///
////////////////////////////////////////////////////////////////////////

// maximum/minimum operators
#define ABC_MIN(a,b)      (((a) < (b))? (a) : (b))
#define ABC_MAX(a,b)      (((a) > (b))? (a) : (b))
#define ABC_INFINITY      (10000000)

// checking the network type
static inline bool        Abc_NtkIsNetlist( Abc_Ntk_t * pNtk )       { return pNtk->ntkType == ABC_TYPE_NETLIST; }
static inline bool        Abc_NtkIsLogic( Abc_Ntk_t * pNtk )         { return pNtk->ntkType == ABC_TYPE_LOGIC;   }
static inline bool        Abc_NtkIsStrash( Abc_Ntk_t * pNtk )        { return pNtk->ntkType == ABC_TYPE_STRASH;  }
static inline bool        Abc_NtkIsSeq( Abc_Ntk_t * pNtk )           { return pNtk->ntkType == ABC_TYPE_SEQ;     }

static inline bool        Abc_NtkHasSop( Abc_Ntk_t * pNtk )          { return pNtk->ntkFunc == ABC_FUNC_SOP;    }
static inline bool        Abc_NtkHasBdd( Abc_Ntk_t * pNtk )          { return pNtk->ntkFunc == ABC_FUNC_BDD;    }
static inline bool        Abc_NtkHasAig( Abc_Ntk_t * pNtk )          { return pNtk->ntkFunc == ABC_FUNC_AIG;    }
static inline bool        Abc_NtkHasMapping( Abc_Ntk_t * pNtk )      { return pNtk->ntkFunc == ABC_FUNC_MAP;    }

static inline bool        Abc_NtkIsSopNetlist( Abc_Ntk_t * pNtk )    { return pNtk->ntkFunc == ABC_FUNC_SOP && pNtk->ntkType == ABC_TYPE_NETLIST;  }
static inline bool        Abc_NtkIsMappedNetlist( Abc_Ntk_t * pNtk ) { return pNtk->ntkFunc == ABC_FUNC_MAP && pNtk->ntkType == ABC_TYPE_NETLIST;  }
static inline bool        Abc_NtkIsSopLogic( Abc_Ntk_t * pNtk )      { return pNtk->ntkFunc == ABC_FUNC_SOP && pNtk->ntkType == ABC_TYPE_LOGIC  ;  }
static inline bool        Abc_NtkIsBddLogic( Abc_Ntk_t * pNtk )      { return pNtk->ntkFunc == ABC_FUNC_BDD && pNtk->ntkType == ABC_TYPE_LOGIC  ;  }
static inline bool        Abc_NtkIsMappedLogic( Abc_Ntk_t * pNtk )   { return pNtk->ntkFunc == ABC_FUNC_MAP && pNtk->ntkType == ABC_TYPE_LOGIC  ;  }
static inline bool        Abc_NtkIsComb( Abc_Ntk_t * pNtk )          { return pNtk->nLatches == 0;      }

// reading data members of the network
static inline char *      Abc_NtkName( Abc_Ntk_t * pNtk )            { return pNtk->pName;           }
static inline char *      Abc_NtkSpec( Abc_Ntk_t * pNtk )            { return pNtk->pSpec;           }
static inline int         Abc_NtkTravId( Abc_Ntk_t * pNtk )          { return pNtk->nTravIds;        }    
static inline Abc_Ntk_t * Abc_NtkExdc( Abc_Ntk_t * pNtk )            { return pNtk->pExdc;           }
static inline Abc_Ntk_t * Abc_NtkBackup( Abc_Ntk_t * pNtk )          { return pNtk->pNetBackup;      }
static inline int         Abc_NtkStep  ( Abc_Ntk_t * pNtk )          { return pNtk->iStep;           }

// setting data members of the network
static inline void        Abc_NtkSetName  ( Abc_Ntk_t * pNtk, char * pName )           { pNtk->pName      = pName;      } 
static inline void        Abc_NtkSetSpec  ( Abc_Ntk_t * pNtk, char * pName )           { pNtk->pSpec      = pName;      } 
static inline void        Abc_NtkSetBackup( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNetBackup ) { pNtk->pNetBackup = pNetBackup; }
static inline void        Abc_NtkSetStep  ( Abc_Ntk_t * pNtk, int iStep )              { pNtk->iStep      = iStep;      }

// getting the number of objects 
static inline int         Abc_NtkObjNumMax( Abc_Ntk_t * pNtk )       { return pNtk->vObjs->nSize;         }
static inline int         Abc_NtkObjNum( Abc_Ntk_t * pNtk )          { return pNtk->nObjs;                }
static inline int         Abc_NtkNetNum( Abc_Ntk_t * pNtk )          { return pNtk->nNets;                }
static inline int         Abc_NtkNodeNum( Abc_Ntk_t * pNtk )         { return pNtk->nNodes;               }
static inline int         Abc_NtkLatchNum( Abc_Ntk_t * pNtk )        { return pNtk->nLatches;             }
static inline int         Abc_NtkPiNum( Abc_Ntk_t * pNtk )           { return pNtk->nPis;                 }
static inline int         Abc_NtkPoNum( Abc_Ntk_t * pNtk )           { return pNtk->nPos;                 }
static inline int         Abc_NtkCiNum( Abc_Ntk_t * pNtk )           { return pNtk->vCis->nSize;          }
static inline int         Abc_NtkCoNum( Abc_Ntk_t * pNtk )           { return pNtk->vCos->nSize;          }

// reading objects
static inline Abc_Obj_t * Abc_NtkObj( Abc_Ntk_t * pNtk, int i )      { assert( i < Vec_PtrSize(pNtk->vObjs) ); return pNtk->vObjs->pArray[i];  }
static inline Abc_Obj_t * Abc_NtkLatch( Abc_Ntk_t * pNtk, int i )    { assert( i < Vec_PtrSize(pNtk->vLats) ); return pNtk->vLats->pArray[i];  }
static inline Abc_Obj_t * Abc_NtkPi( Abc_Ntk_t * pNtk, int i )       { assert( i < Abc_NtkPiNum(pNtk) ); return pNtk->vCis->pArray[i];      }
static inline Abc_Obj_t * Abc_NtkPo( Abc_Ntk_t * pNtk, int i )       { assert( i < Abc_NtkPoNum(pNtk) ); return pNtk->vCos->pArray[i];      }
static inline Abc_Obj_t * Abc_NtkCi( Abc_Ntk_t * pNtk, int i )       { assert( i < Abc_NtkCiNum(pNtk) ); return pNtk->vCis->pArray[i];      }
static inline Abc_Obj_t * Abc_NtkCo( Abc_Ntk_t * pNtk, int i )       { assert( i < Abc_NtkCoNum(pNtk) ); return pNtk->vCos->pArray[i];      }

// reading data members of the object
static inline unsigned    Abc_ObjType( Abc_Obj_t * pObj )            { return pObj->Type;               }
static inline unsigned    Abc_ObjId( Abc_Obj_t * pObj )              { return pObj->Id;                 }
static inline int         Abc_ObjTravId( Abc_Obj_t * pObj )          { return pObj->TravId;             }
static inline Vec_Fan_t * Abc_ObjFaninVec( Abc_Obj_t * pObj )        { return &pObj->vFanins;           }
static inline Vec_Fan_t * Abc_ObjFanoutVec( Abc_Obj_t * pObj )       { return &pObj->vFanouts;          }
static inline Abc_Obj_t * Abc_ObjCopy( Abc_Obj_t * pObj )            { return pObj->pCopy;              }
static inline Abc_Ntk_t * Abc_ObjNtk( Abc_Obj_t * pObj )             { return pObj->pNtk;               }
static inline void *      Abc_ObjData( Abc_Obj_t * pObj )            { return pObj->pData;              }

// setting data members of the network
static inline void        Abc_ObjSetCopy( Abc_Obj_t * pObj, Abc_Obj_t * pCopy )  { pObj->pCopy    =  pCopy;    } 
static inline void        Abc_ObjSetData( Abc_Obj_t * pObj, void * pData )       { pObj->pData    =  pData;    } 

// working with complemented attributes of objects
static inline bool        Abc_ObjIsComplement( Abc_Obj_t * p )       { return (bool)(((unsigned)p) & 01);           }
static inline Abc_Obj_t * Abc_ObjRegular( Abc_Obj_t * p )            { return (Abc_Obj_t *)((unsigned)(p) & ~01);  }
static inline Abc_Obj_t * Abc_ObjNot( Abc_Obj_t * p )                { return (Abc_Obj_t *)((unsigned)(p) ^  01);  }
static inline Abc_Obj_t * Abc_ObjNotCond( Abc_Obj_t * p, int c )     { return (Abc_Obj_t *)((unsigned)(p) ^ (c));  }

// checking the object type
static inline bool        Abc_ObjIsNode( Abc_Obj_t * pObj )          { return pObj->Type == ABC_OBJ_NODE;   }
static inline bool        Abc_ObjIsNet( Abc_Obj_t * pObj )           { return pObj->Type == ABC_OBJ_NET;    }
static inline bool        Abc_ObjIsLatch( Abc_Obj_t * pObj )         { return pObj->Type == ABC_OBJ_LATCH;  }
static inline bool        Abc_ObjIsPi( Abc_Obj_t * pObj )            { return pObj->Type == ABC_OBJ_PI;     }
static inline bool        Abc_ObjIsPo( Abc_Obj_t * pObj )            { return pObj->Type == ABC_OBJ_PO;     }
static inline bool        Abc_ObjIsPio( Abc_Obj_t * pObj )           { return pObj->Type == ABC_OBJ_PI || pObj->Type == ABC_OBJ_PO;    }
static inline bool        Abc_ObjIsCi( Abc_Obj_t * pObj )            { return pObj->Type == ABC_OBJ_PI || pObj->Type == ABC_OBJ_LATCH; }
static inline bool        Abc_ObjIsCo( Abc_Obj_t * pObj )            { return pObj->Type == ABC_OBJ_PO || pObj->Type == ABC_OBJ_LATCH; }
static inline bool        Abc_ObjIsCio( Abc_Obj_t * pObj )           { return pObj->Type == ABC_OBJ_PI || pObj->Type == ABC_OBJ_PO || pObj->Type == ABC_OBJ_LATCH; }

// working with fanin/fanout edges
static inline int         Abc_ObjFaninNum( Abc_Obj_t * pObj )        { return pObj->vFanins.nSize;      }
static inline int         Abc_ObjFanoutNum( Abc_Obj_t * pObj )       { return pObj->vFanouts.nSize;     }
static inline int         Abc_ObjFaninId( Abc_Obj_t * pObj, int i)   { return pObj->vFanins.pArray[i].iFan; }
static inline int         Abc_ObjFaninId0( Abc_Obj_t * pObj )        { return pObj->vFanins.pArray[0].iFan; }
static inline int         Abc_ObjFaninId1( Abc_Obj_t * pObj )        { return pObj->vFanins.pArray[1].iFan; }
static inline Abc_Obj_t * Abc_ObjFanout( Abc_Obj_t * pObj, int i )   { return pObj->pNtk->vObjs->pArray[ pObj->vFanouts.pArray[i].iFan ];   }
static inline Abc_Obj_t * Abc_ObjFanout0( Abc_Obj_t * pObj )         { return pObj->pNtk->vObjs->pArray[ pObj->vFanouts.pArray[0].iFan ];   }
static inline Abc_Obj_t * Abc_ObjFanin( Abc_Obj_t * pObj, int i )    { return pObj->pNtk->vObjs->pArray[ pObj->vFanins.pArray[i].iFan  ];   }
static inline Abc_Obj_t * Abc_ObjFanin0( Abc_Obj_t * pObj )          { return pObj->pNtk->vObjs->pArray[ pObj->vFanins.pArray[0].iFan  ];   }
static inline Abc_Obj_t * Abc_ObjFanin1( Abc_Obj_t * pObj )          { return pObj->pNtk->vObjs->pArray[ pObj->vFanins.pArray[1].iFan  ];   }
static inline Abc_Obj_t * Abc_ObjFanin0Ntk( Abc_Obj_t * pObj )       { return Abc_NtkIsNetlist(pObj->pNtk)? Abc_ObjFanin0(pObj) : pObj;     }
static inline Abc_Obj_t * Abc_ObjFanout0Ntk( Abc_Obj_t * pObj )      { return Abc_NtkIsNetlist(pObj->pNtk)? Abc_ObjFanout0(pObj) : pObj;    }
static inline bool        Abc_ObjFaninC( Abc_Obj_t * pObj, int i )   { return pObj->vFanins.pArray[i].fCompl;                               }
static inline bool        Abc_ObjFaninC0( Abc_Obj_t * pObj )         { return pObj->vFanins.pArray[0].fCompl;                               }
static inline bool        Abc_ObjFaninC1( Abc_Obj_t * pObj )         { return pObj->vFanins.pArray[1].fCompl;                               }
static inline bool        Abc_ObjFanoutC( Abc_Obj_t * pObj, Abc_Obj_t * pFanout ) {  assert( !Abc_NtkIsLogic(pObj->pNtk) ); return (Abc_ObjFaninId0(pFanout) == (int)pObj->Id)? Abc_ObjFaninC0(pFanout) : Abc_ObjFaninC1(pFanout);  }
static inline int         Abc_ObjFaninL( Abc_Obj_t * pObj, int i )   { return pObj->vFanins.pArray[i].nLats;                                }
static inline int         Abc_ObjFaninL0( Abc_Obj_t * pObj )         { return pObj->vFanins.pArray[0].nLats;                                }
static inline int         Abc_ObjFaninL1( Abc_Obj_t * pObj )         { return pObj->vFanins.pArray[1].nLats;                                }
static inline int         Abc_ObjFaninLMin( Abc_Obj_t * pObj )       {  assert( Abc_ObjIsNode(pObj) ); return ABC_MIN( Abc_ObjFaninL0(pObj), Abc_ObjFaninL1(pObj) ); }
static inline int         Abc_ObjFaninLMax( Abc_Obj_t * pObj )       {  assert( Abc_ObjIsNode(pObj) ); return ABC_MAX( Abc_ObjFaninL0(pObj), Abc_ObjFaninL1(pObj) ); }
static inline Abc_Obj_t * Abc_ObjChild( Abc_Obj_t * pObj, int i )    { return Abc_ObjNotCond( Abc_ObjFanin(pObj,i), Abc_ObjFaninC(pObj,i) );}
static inline Abc_Obj_t * Abc_ObjChild0( Abc_Obj_t * pObj )          { return Abc_ObjNotCond( Abc_ObjFanin0(pObj), Abc_ObjFaninC0(pObj) );  }
static inline Abc_Obj_t * Abc_ObjChild1( Abc_Obj_t * pObj )          { return Abc_ObjNotCond( Abc_ObjFanin1(pObj), Abc_ObjFaninC1(pObj) );  }
static inline Abc_Obj_t * Abc_ObjChildCopy( Abc_Obj_t * pObj, int i ){ return Abc_ObjNotCond( Abc_ObjFanin(pObj,i)->pCopy, Abc_ObjFaninC(pObj,i) );}
static inline Abc_Obj_t * Abc_ObjChild0Copy( Abc_Obj_t * pObj )      { return Abc_ObjNotCond( Abc_ObjFanin0(pObj)->pCopy, Abc_ObjFaninC0(pObj) );  }
static inline Abc_Obj_t * Abc_ObjChild1Copy( Abc_Obj_t * pObj )      { return Abc_ObjNotCond( Abc_ObjFanin1(pObj)->pCopy, Abc_ObjFaninC1(pObj) );  }
static inline Abc_Obj_t * Abc_ObjFanoutFanin( Abc_Obj_t * pObj, Abc_Obj_t * pFanout ) {  assert( !Abc_NtkIsLogic(pObj->pNtk) ); return (Abc_ObjFaninId0(pFanout) == (int)pObj->Id)? Abc_ObjChild0(pFanout) : Abc_ObjChild1(pFanout);  }
static inline void        Abc_ObjSetFaninC( Abc_Obj_t * pObj, int i ){ pObj->vFanins.pArray[i].fCompl = 1;                               }
static inline void        Abc_ObjXorFaninC( Abc_Obj_t * pObj, int i ){ pObj->vFanins.pArray[i].fCompl ^= 1;                              }
static inline void        Abc_ObjSetFaninL( Abc_Obj_t * pObj, int i, int nLats )  { pObj->vFanins.pArray[i].nLats = nLats;               }
static inline void        Abc_ObjSetFaninL0( Abc_Obj_t * pObj, int nLats )        { pObj->vFanins.pArray[0].nLats = nLats;               }
static inline void        Abc_ObjSetFaninL1( Abc_Obj_t * pObj, int nLats )        { pObj->vFanins.pArray[1].nLats = nLats;               }
static inline void        Abc_ObjAddFaninL( Abc_Obj_t * pObj, int i, int nLats )  { pObj->vFanins.pArray[i].nLats += nLats;              }
static inline void        Abc_ObjAddFaninL0( Abc_Obj_t * pObj, int nLats )        { pObj->vFanins.pArray[0].nLats += nLats;              }
static inline void        Abc_ObjAddFaninL1( Abc_Obj_t * pObj, int nLats )        { pObj->vFanins.pArray[1].nLats += nLats;              }
extern int                Abc_ObjFanoutL( Abc_Obj_t * pObj, Abc_Obj_t * pFanout );
extern void               Abc_ObjSetFanoutL( Abc_Obj_t * pObj, Abc_Obj_t * pFanout, int nLats );
extern void               Abc_ObjAddFanoutL( Abc_Obj_t * pObj, Abc_Obj_t * pFanout, int nLats );  
extern int                Abc_ObjFanoutLMin( Abc_Obj_t * pObj );
extern int                Abc_ObjFanoutLMax( Abc_Obj_t * pObj );

// checking the node type
static inline bool        Abc_NodeIsAigAnd( Abc_Obj_t * pNode )      { assert(Abc_NtkHasAig(pNode->pNtk));           return Abc_ObjFaninNum(pNode) == 2;                         }
static inline bool        Abc_NodeIsAigChoice( Abc_Obj_t * pNode )   { assert(Abc_NtkHasAig(pNode->pNtk));           return pNode->pData != NULL && Abc_ObjFanoutNum(pNode) > 0; }
static inline bool        Abc_NodeIsConst( Abc_Obj_t * pNode )       { assert(Abc_ObjIsNode(Abc_ObjRegular(pNode))); return Abc_ObjFaninNum(Abc_ObjRegular(pNode)) == 0;         }
extern        bool        Abc_NodeIsConst0( Abc_Obj_t * pNode );    
extern        bool        Abc_NodeIsConst1( Abc_Obj_t * pNode );    
extern        bool        Abc_NodeIsBuf( Abc_Obj_t * pNode );    
extern        bool        Abc_NodeIsInv( Abc_Obj_t * pNode );    

// working with the traversal ID
static inline void        Abc_NodeSetTravId( Abc_Obj_t * pNode, int TravId ) { pNode->TravId = TravId;                                    }
static inline void        Abc_NodeSetTravIdCurrent( Abc_Obj_t * pNode )      { pNode->TravId = pNode->pNtk->nTravIds;                     }
static inline void        Abc_NodeSetTravIdPrevious( Abc_Obj_t * pNode )     { pNode->TravId = pNode->pNtk->nTravIds - 1;                 }
static inline bool        Abc_NodeIsTravIdCurrent( Abc_Obj_t * pNode )       { return (bool)(pNode->TravId == pNode->pNtk->nTravIds);     }
static inline bool        Abc_NodeIsTravIdPrevious( Abc_Obj_t * pNode )      { return (bool)(pNode->TravId == pNode->pNtk->nTravIds - 1); }

// checking initial state of the latches
static inline void        Abc_LatchSetInit0( Abc_Obj_t * pLatch )   { assert(Abc_ObjIsLatch(pLatch)); pLatch->pData = (void *)0;   }
static inline void        Abc_LatchSetInit1( Abc_Obj_t * pLatch )   { assert(Abc_ObjIsLatch(pLatch)); pLatch->pData = (void *)1;   }
static inline void        Abc_LatchSetInitDc( Abc_Obj_t * pLatch )  { assert(Abc_ObjIsLatch(pLatch)); pLatch->pData = (void *)2;   }
static inline bool        Abc_LatchIsInit0( Abc_Obj_t * pLatch )    { assert(Abc_ObjIsLatch(pLatch)); return pLatch->pData == (void *)0;  }
static inline bool        Abc_LatchIsInit1( Abc_Obj_t * pLatch )    { assert(Abc_ObjIsLatch(pLatch)); return pLatch->pData == (void *)1;  }
static inline bool        Abc_LatchIsInitDc( Abc_Obj_t * pLatch )   { assert(Abc_ObjIsLatch(pLatch)); return pLatch->pData == (void *)2;  }

// outputs the runtime in seconds
#define PRT(a,t)  printf("%s = ", (a)); printf("%6.2f sec\n", (float)(t)/(float)(CLOCKS_PER_SEC))

////////////////////////////////////////////////////////////////////////
///                        ITERATORS                                 ///
////////////////////////////////////////////////////////////////////////

// objects of the network
#define Abc_NtkForEachObj( pNtk, pObj, i )                               \
    for ( i = 0; i < Vec_PtrSize(pNtk->vObjs); i++ )                     \
        if ( pObj = Abc_NtkObj(pNtk, i) )
#define Abc_NtkForEachNet( pNtk, pNet, i )                               \
    for ( i = 0; i < Vec_PtrSize(pNtk->vObjs); i++ )                     \
        if ( (pNet = Abc_NtkObj(pNtk, i)) && Abc_ObjIsNet(pNet) )
#define Abc_NtkForEachNode( pNtk, pNode, i )                             \
    for ( i = 0; i < Vec_PtrSize(pNtk->vObjs); i++ )                     \
        if ( (pNode = Abc_NtkObj(pNtk, i)) && Abc_ObjIsNode(pNode) )
#define Abc_NtkForEachLatch( pNtk, pObj, i )                             \
    for ( i = 0; i < Vec_PtrSize(pNtk->vLats); i++ )                     \
        if ( pObj = Abc_NtkLatch(pNtk, i) )
// inputs and outputs
#define Abc_NtkForEachPi( pNtk, pPi, i )                                 \
    for ( i = 0; (i < Abc_NtkPiNum(pNtk)) && (((pPi) = Abc_NtkPi(pNtk, i)), 1); i++ )
#define Abc_NtkForEachPo( pNtk, pPo, i )                                 \
    for ( i = 0; (i < Abc_NtkPoNum(pNtk)) && (((pPo) = Abc_NtkPo(pNtk, i)), 1); i++ )
#define Abc_NtkForEachCi( pNtk, pCi, i )                                 \
    for ( i = 0; (i < Abc_NtkCiNum(pNtk)) && (((pCi) = Abc_NtkCi(pNtk, i)), 1); i++ )
#define Abc_NtkForEachCo( pNtk, pCo, i )                                 \
    for ( i = 0; (i < Abc_NtkCoNum(pNtk)) && (((pCo) = Abc_NtkCo(pNtk, i)), 1); i++ )
// fanin and fanouts
#define Abc_ObjForEachFanin( pObj, pFanin, i )                           \
    for ( i = 0; (i < Abc_ObjFaninNum(pObj)) && (((pFanin) = Abc_ObjFanin(pObj, i)), 1); i++ )
#define Abc_ObjForEachFanout( pObj, pFanout, i )                         \
    for ( i = 0; (i < Abc_ObjFanoutNum(pObj)) && (((pFanout) = Abc_ObjFanout(pObj, i)), 1); i++ )
// cubes and literals
#define Abc_SopForEachCube( pSop, nFanins, pCube )                       \
    for ( pCube = (pSop); *pCube; pCube += (nFanins) + 3 )
#define Abc_CubeForEachVar( pCube, Value, i )                            \
    for ( i = 0; (pCube[i] != ' ') && (Value = pCube[i]); i++ )           


////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== abcAig.c ==========================================================*/
extern Abc_Aig_t *        Abc_AigAlloc( Abc_Ntk_t * pNtk );
extern Abc_Aig_t *        Abc_AigDup( Abc_Aig_t * pMan, Abc_Aig_t * pManNew );
extern void               Abc_AigFree( Abc_Aig_t * pMan );
extern int                Abc_AigCleanup( Abc_Aig_t * pMan );
extern bool               Abc_AigCheck( Abc_Aig_t * pMan );
extern int                Abc_AigGetLevelNum( Abc_Ntk_t * pNtk );
extern Abc_Obj_t *        Abc_AigConst1( Abc_Aig_t * pMan );
extern Abc_Obj_t *        Abc_AigReset( Abc_Aig_t * pMan );
extern Abc_Obj_t *        Abc_AigAnd( Abc_Aig_t * pMan, Abc_Obj_t * p0, Abc_Obj_t * p1 );
extern Abc_Obj_t *        Abc_AigAndLookup( Abc_Aig_t * pMan, Abc_Obj_t * p0, Abc_Obj_t * p1 );
extern Abc_Obj_t *        Abc_AigOr( Abc_Aig_t * pMan, Abc_Obj_t * p0, Abc_Obj_t * p1 );
extern Abc_Obj_t *        Abc_AigXor( Abc_Aig_t * pMan, Abc_Obj_t * p0, Abc_Obj_t * p1 );
extern Abc_Obj_t *        Abc_AigMiter( Abc_Aig_t * pMan, Vec_Ptr_t * vPairs );
extern void               Abc_AigReplace( Abc_Aig_t * pMan, Abc_Obj_t * pOld, Abc_Obj_t * pNew );
extern void               Abc_AigDeleteNode( Abc_Aig_t * pMan, Abc_Obj_t * pOld );
extern bool               Abc_AigNodeHasComplFanoutEdge( Abc_Obj_t * pNode );
extern bool               Abc_AigNodeHasComplFanoutEdgeTrav( Abc_Obj_t * pNode );
extern void               Abc_AigPrintNode( Abc_Obj_t * pNode );
extern bool               Abc_AigNodeIsAcyclic( Abc_Obj_t * pNode, Abc_Obj_t * pRoot );
/*=== abcAttach.c ==========================================================*/
extern int                Abc_NtkAttach( Abc_Ntk_t * pNtk );
/*=== abcBalance.c ==========================================================*/
extern Abc_Ntk_t *        Abc_NtkBalance( Abc_Ntk_t * pNtk, bool fDuplicate );
/*=== abcCheck.c ==========================================================*/
extern bool               Abc_NtkCheck( Abc_Ntk_t * pNtk );
extern bool               Abc_NtkCheckRead( Abc_Ntk_t * pNtk );
extern bool               Abc_NtkCheckObj( Abc_Ntk_t * pNtk, Abc_Obj_t * pObj );
extern bool               Abc_NtkCompareSignals( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int fComb );
/*=== abcCollapse.c ==========================================================*/
extern Abc_Ntk_t *        Abc_NtkCollapse( Abc_Ntk_t * pNtk, int fVerbose );
/*=== abcCut.c ==========================================================*/
extern void *             Abc_NodeGetCutsRecursive( void * p, Abc_Obj_t * pObj );
extern void *             Abc_NodeGetCuts( void * p, Abc_Obj_t * pObj );
extern void *             Abc_NodeReadCuts( void * p, Abc_Obj_t * pObj );
extern void               Abc_NodeFreeCuts( void * p, Abc_Obj_t * pObj );
/*=== abcDfs.c ==========================================================*/
extern Vec_Ptr_t *        Abc_NtkDfs( Abc_Ntk_t * pNtk, int fCollectAll );
extern Vec_Ptr_t *        Abc_NtkDfsNodes( Abc_Ntk_t * pNtk, Abc_Obj_t ** ppNodes, int nNodes );
extern Vec_Ptr_t *        Abc_NtkDfsReverse( Abc_Ntk_t * pNtk );
extern Vec_Ptr_t *        Abc_AigDfs( Abc_Ntk_t * pNtk, int fCollectAll, int fCollectCos );
extern Vec_Vec_t *        Abc_DfsLevelized( Abc_Obj_t * pNode, bool fTfi );
extern int                Abc_NtkGetLevelNum( Abc_Ntk_t * pNtk );
extern bool               Abc_NtkIsAcyclic( Abc_Ntk_t * pNtk );
/*=== abcFanio.c ==========================================================*/
extern void               Abc_ObjAddFanin( Abc_Obj_t * pObj, Abc_Obj_t * pFanin );
extern void               Abc_ObjDeleteFanin( Abc_Obj_t * pObj, Abc_Obj_t * pFanin );
extern void               Abc_ObjRemoveFanins( Abc_Obj_t * pObj );
extern void               Abc_ObjPatchFanin( Abc_Obj_t * pObj, Abc_Obj_t * pFaninOld, Abc_Obj_t * pFaninNew );
extern void               Abc_ObjTransferFanout( Abc_Obj_t * pObjOld, Abc_Obj_t * pObjNew );
extern void               Abc_ObjReplace( Abc_Obj_t * pObjOld, Abc_Obj_t * pObjNew );
/*=== abcFraig.c ==========================================================*/
extern Abc_Ntk_t *        Abc_NtkFraig( Abc_Ntk_t * pNtk, void * pParams, int fAllNodes );
extern Abc_Ntk_t *        Abc_NtkFraigTrust( Abc_Ntk_t * pNtk );
extern int                Abc_NtkFraigStore( Abc_Ntk_t * pNtk );
extern Abc_Ntk_t *        Abc_NtkFraigRestore();
extern void               Abc_NtkFraigStoreClean();
/*=== abcFunc.c ==========================================================*/
extern int                Abc_NtkSopToBdd( Abc_Ntk_t * pNtk );
extern DdNode *           Abc_ConvertSopToBdd( DdManager * dd, char * pSop );
extern char *             Abc_ConvertBddToSop( Extra_MmFlex_t * pMan, DdManager * dd, DdNode * bFuncOn, DdNode * bFuncOnDc, int nFanins, Vec_Str_t * vCube, int fMode );
extern int                Abc_NtkBddToSop( Abc_Ntk_t * pNtk );
extern void               Abc_NodeBddToCnf( Abc_Obj_t * pNode, Extra_MmFlex_t * pMmMan, Vec_Str_t * vCube, char ** ppSop0, char ** ppSop1 );
extern int                Abc_CountZddCubes( DdManager * dd, DdNode * zCover );
extern void               Abc_NtkLogicMakeDirectSops( Abc_Ntk_t * pNtk );
/*=== abcLatch.c ==========================================================*/
extern bool               Abc_NtkLatchIsSelfFeed( Abc_Obj_t * pLatch );
extern int                Abc_NtkCountSelfFeedLatches( Abc_Ntk_t * pNtk );
/*=== abcMap.c ==========================================================*/
extern int                Abc_NtkUnmap( Abc_Ntk_t * pNtk );
/*=== abcMiter.c ==========================================================*/
extern int                Abc_NtkMinimumBase( Abc_Ntk_t * pNtk );
extern int                Abc_NodeMinimumBase( Abc_Obj_t * pNode );
extern int                Abc_NtkRemoveDupFanins( Abc_Ntk_t * pNtk );
extern int                Abc_NodeRemoveDupFanins( Abc_Obj_t * pNode );
/*=== abcMiter.c ==========================================================*/
extern Abc_Ntk_t *        Abc_NtkMiter( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int fComb );
extern Abc_Ntk_t *        Abc_NtkMiterForCofactors( Abc_Ntk_t * pNtk, int Out, int In1, int In2 );
extern int                Abc_NtkMiterIsConstant( Abc_Ntk_t * pMiter );
extern void               Abc_NtkMiterReport( Abc_Ntk_t * pMiter );
extern int                Abc_NtkAppend( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2 );
extern Abc_Ntk_t *        Abc_NtkFrames( Abc_Ntk_t * pNtk, int nFrames, int fInitial );
/*=== abcObj.c ==========================================================*/
extern Abc_Obj_t *        Abc_ObjAlloc( Abc_Ntk_t * pNtk, Abc_ObjType_t Type );
extern void               Abc_ObjRecycle( Abc_Obj_t * pObj );
extern void               Abc_ObjAdd( Abc_Obj_t * pObj );
extern Abc_Obj_t *        Abc_NtkDupObj( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pObj );
extern Abc_Obj_t *        Abc_NtkDupConst1( Abc_Ntk_t * pNtkAig, Abc_Ntk_t * pNtkNew );
extern Abc_Obj_t *        Abc_NtkDupReset( Abc_Ntk_t * pNtkAig, Abc_Ntk_t * pNtkNew );
extern void               Abc_NtkDeleteObj( Abc_Obj_t * pObj );
extern Abc_Obj_t *        Abc_NtkFindNode( Abc_Ntk_t * pNtk, char * pName );
extern Abc_Obj_t *        Abc_NtkFindCo( Abc_Ntk_t * pNtk, char * pName );
extern Abc_Obj_t *        Abc_NtkFindNet( Abc_Ntk_t * pNtk, char * pName );
extern Abc_Obj_t *        Abc_NtkFindOrCreateNet( Abc_Ntk_t * pNtk, char * pName );
extern Abc_Obj_t *        Abc_NtkCreateNode( Abc_Ntk_t * pNtk );
extern Abc_Obj_t *        Abc_NtkCreatePi( Abc_Ntk_t * pNtk );
extern Abc_Obj_t *        Abc_NtkCreatePo( Abc_Ntk_t * pNtk );
extern Abc_Obj_t *        Abc_NtkCreateLatch( Abc_Ntk_t * pNtk );
extern Abc_Obj_t *        Abc_NodeCreateConst0( Abc_Ntk_t * pNtk );
extern Abc_Obj_t *        Abc_NodeCreateConst1( Abc_Ntk_t * pNtk );
extern Abc_Obj_t *        Abc_NodeCreateInv( Abc_Ntk_t * pNtk, Abc_Obj_t * pFanin );
extern Abc_Obj_t *        Abc_NodeCreateBuf( Abc_Ntk_t * pNtk, Abc_Obj_t * pFanin );
extern Abc_Obj_t *        Abc_NodeCreateAnd( Abc_Ntk_t * pNtk, Vec_Ptr_t * vFanins );
extern Abc_Obj_t *        Abc_NodeCreateOr( Abc_Ntk_t * pNtk, Vec_Ptr_t * vFanins );
extern Abc_Obj_t *        Abc_NodeCreateMux( Abc_Ntk_t * pNtk, Abc_Obj_t * pNodeC, Abc_Obj_t * pNode1, Abc_Obj_t * pNode0 );
extern Abc_Obj_t *        Abc_NodeClone( Abc_Obj_t * pNode );
/*=== abcNames.c ====================================================*/
extern char *             Abc_NtkRegisterName( Abc_Ntk_t * pNtk, char * pName );
extern char *             Abc_NtkRegisterNamePlus( Abc_Ntk_t * pNtk, char * pName, char * pSuffix );
extern char *             Abc_ObjName( Abc_Obj_t * pNode );
extern char *             Abc_ObjNameSuffix( Abc_Obj_t * pObj, char * pSuffix );
extern char *             Abc_ObjNameUnique( Abc_Ntk_t * pNtk, char * pName );
extern char *             Abc_NtkLogicStoreName( Abc_Obj_t * pNodeNew, char * pNameOld );
extern char *             Abc_NtkLogicStoreNamePlus( Abc_Obj_t * pNodeNew, char * pNameOld, char * pSuffix );
extern void               Abc_NtkCreateCioNamesTable( Abc_Ntk_t * pNtk );
extern void               Abc_NtkDupCioNamesTable( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkNew );
extern Vec_Ptr_t *        Abc_NodeGetFaninNames( Abc_Obj_t * pNode );
extern Vec_Ptr_t *        Abc_NodeGetFakeNames( int nNames );
extern void               Abc_NodeFreeNames( Vec_Ptr_t * vNames );
extern char **            Abc_NtkCollectCioNames( Abc_Ntk_t * pNtk, int fCollectCos );
extern int                Abc_NodeCompareNames( Abc_Obj_t ** pp1, Abc_Obj_t ** pp2 );
extern void               Abc_NtkOrderObjsByName( Abc_Ntk_t * pNtk, int fComb );
extern void               Abc_NtkShortNames( Abc_Ntk_t * pNtk );
/*=== abcNetlist.c ==========================================================*/
extern Abc_Ntk_t *        Abc_NtkNetlistToLogic( Abc_Ntk_t * pNtk );
extern Abc_Ntk_t *        Abc_NtkLogicToNetlist( Abc_Ntk_t * pNtk );
extern Abc_Ntk_t *        Abc_NtkLogicToNetlistBench( Abc_Ntk_t * pNtk );
extern Abc_Ntk_t *        Abc_NtkLogicSopToNetlist( Abc_Ntk_t * pNtk );
extern Abc_Ntk_t *        Abc_NtkAigToLogicSop( Abc_Ntk_t * pNtk );
extern Abc_Ntk_t *        Abc_NtkAigToLogicSopBench( Abc_Ntk_t * pNtk );
/*=== abcNtbdd.c ==========================================================*/
extern Abc_Ntk_t *        Abc_NtkDeriveFromBdd( DdManager * dd, DdNode * bFunc, char * pNamePo, Vec_Ptr_t * vNamesPi );
extern Abc_Ntk_t *        Abc_NtkBddToMuxes( Abc_Ntk_t * pNtk );
extern DdManager *        Abc_NtkGlobalBdds( Abc_Ntk_t * pNtk, int fLatchOnly );
extern void               Abc_NtkFreeGlobalBdds( Abc_Ntk_t * pNtk );
/*=== abcNtk.c ==========================================================*/
extern Abc_Ntk_t *        Abc_NtkAlloc( Abc_NtkType_t Type, Abc_NtkFunc_t Func );
extern Abc_Ntk_t *        Abc_NtkStartFrom( Abc_Ntk_t * pNtk, Abc_NtkType_t Type, Abc_NtkFunc_t Func );
extern void               Abc_NtkFinalize( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkNew );
extern void               Abc_NtkFinalizeRegular( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkNew );
extern void               Abc_NtkFinalizeLatches( Abc_Ntk_t * pNtk );
extern Abc_Ntk_t *        Abc_NtkStartRead( char * pName );
extern void               Abc_NtkFinalizeRead( Abc_Ntk_t * pNtk );
extern Abc_Ntk_t *        Abc_NtkDup( Abc_Ntk_t * pNtk );
extern Abc_Ntk_t *        Abc_NtkSplitOutput( Abc_Ntk_t * pNtk, Abc_Obj_t * pNode, int fUseAllCis );
extern Abc_Ntk_t *        Abc_NtkCreateCone( Abc_Ntk_t * pNtk, Vec_Ptr_t * vRoots, Vec_Int_t * vValues );
extern Abc_Ntk_t *        Abc_NtkSplitNode( Abc_Ntk_t * pNtk, Abc_Obj_t * pNode );
extern void               Abc_NtkDelete( Abc_Ntk_t * pNtk );
extern void               Abc_NtkFixNonDrivenNets( Abc_Ntk_t * pNtk );
/*=== abcPrint.c ==========================================================*/
extern void               Abc_NtkPrintStats( FILE * pFile, Abc_Ntk_t * pNtk, int fFactored );
extern void               Abc_NtkPrintIo( FILE * pFile, Abc_Ntk_t * pNtk );
extern void               Abc_NtkPrintLatch( FILE * pFile, Abc_Ntk_t * pNtk );
extern void               Abc_NtkPrintFanio( FILE * pFile, Abc_Ntk_t * pNtk );
extern void               Abc_NodePrintFanio( FILE * pFile, Abc_Obj_t * pNode );
extern void               Abc_NtkPrintFactor( FILE * pFile, Abc_Ntk_t * pNtk, int fUseRealNames );
extern void               Abc_NodePrintFactor( FILE * pFile, Abc_Obj_t * pNode, int fUseRealNames );
extern void               Abc_NtkPrintLevel( FILE * pFile, Abc_Ntk_t * pNtk, int fProfile );
extern void               Abc_NodePrintLevel( FILE * pFile, Abc_Obj_t * pNode );
/*=== abcReconv.c ==========================================================*/
extern Abc_ManCut_t *     Abc_NtkManCutStart( int nNodeSizeMax, int nConeSizeMax, int nNodeFanStop, int nConeFanStop );
extern void               Abc_NtkManCutStop( Abc_ManCut_t * p );
extern Vec_Ptr_t *        Abc_NtkManCutReadCutLarge( Abc_ManCut_t * p );
extern Vec_Ptr_t *        Abc_NtkManCutReadVisited( Abc_ManCut_t * p );
extern Vec_Ptr_t *        Abc_NodeFindCut( Abc_ManCut_t * p, Abc_Obj_t * pRoot, bool fContain );
extern void               Abc_NodeConeCollect( Abc_Obj_t ** ppRoots, int nRoots, Vec_Ptr_t * vFanins, Vec_Ptr_t * vVisited, int fIncludeFanins );
extern DdNode *           Abc_NodeConeBdd( DdManager * dd, DdNode ** pbVars, Abc_Obj_t * pNode, Vec_Ptr_t * vFanins, Vec_Ptr_t * vVisited );
extern DdNode *           Abc_NodeConeDcs( DdManager * dd, DdNode ** pbVarsX, DdNode ** pbVarsY, Vec_Ptr_t * vLeaves, Vec_Ptr_t * vRoots, Vec_Ptr_t * vVisited );
extern Vec_Ptr_t *        Abc_NodeCollectTfoCands( Abc_ManCut_t * p, Abc_Obj_t * pRoot, Vec_Ptr_t * vFanins, int LevelMax );
/*=== abcRefs.c ==========================================================*/
extern int                Abc_NodeMffcSize( Abc_Obj_t * pNode );
extern int                Abc_NodeMffcSizeStop( Abc_Obj_t * pNode );
extern int                Abc_NodeMffcLabel( Abc_Obj_t * pNode );
extern Vec_Ptr_t *        Abc_NodeMffcCollect( Abc_Obj_t * pNode );
/*=== abcRenode.c ==========================================================*/
extern Abc_Ntk_t *        Abc_NtkRenode( Abc_Ntk_t * pNtk, int nThresh, int nFaninMax, int fCnf, int fMulti, int fSimple );
extern DdNode *           Abc_NtkRenodeDeriveBdd( DdManager * dd, Abc_Obj_t * pNodeOld, Vec_Ptr_t * vFaninsOld );
/*=== abcSat.c ==========================================================*/
extern bool               Abc_NtkMiterSat( Abc_Ntk_t * pNtk, int fVerbose );
extern solver *           Abc_NtkMiterSatCreate( Abc_Ntk_t * pNtk );
/*=== abcSeq.c ==========================================================*/
extern Abc_Ntk_t *        Abc_NtkAigToSeq( Abc_Ntk_t * pNtk );
extern Abc_Ntk_t *        Abc_NtkSeqToLogicSop( Abc_Ntk_t * pNtk );
extern int                Abc_NtkSeqLatchNum( Abc_Ntk_t * pNtk );
extern void               Abc_NtkSeqRetimeForward( Abc_Ntk_t * pNtk );
extern void               Abc_NtkSeqRetimeBackward( Abc_Ntk_t * pNtk );
extern void               Abc_NtkSeqRetimeDelay( Abc_Ntk_t * pNtk );
/*=== abcSop.c ==========================================================*/
extern char *             Abc_SopRegister( Extra_MmFlex_t * pMan, char * pName );
extern char *             Abc_SopStart( Extra_MmFlex_t * pMan, int nCubes, int nVars );
extern char *             Abc_SopCreateConst0( Extra_MmFlex_t * pMan );
extern char *             Abc_SopCreateConst1( Extra_MmFlex_t * pMan );
extern char *             Abc_SopCreateAnd2( Extra_MmFlex_t * pMan, int fCompl0, int fCompl1 );
extern char *             Abc_SopCreateAnd( Extra_MmFlex_t * pMan, int nVars );
extern char *             Abc_SopCreateNand( Extra_MmFlex_t * pMan, int nVars );
extern char *             Abc_SopCreateOr( Extra_MmFlex_t * pMan, int nVars, int * pfCompl );
extern char *             Abc_SopCreateOrMultiCube( Extra_MmFlex_t * pMan, int nVars, int * pfCompl );
extern char *             Abc_SopCreateNor( Extra_MmFlex_t * pMan, int nVars );
extern char *             Abc_SopCreateXor( Extra_MmFlex_t * pMan, int nVars );
extern char *             Abc_SopCreateNxor( Extra_MmFlex_t * pMan, int nVars );
extern char *             Abc_SopCreateInv( Extra_MmFlex_t * pMan );
extern char *             Abc_SopCreateBuf( Extra_MmFlex_t * pMan );
extern int                Abc_SopGetCubeNum( char * pSop );
extern int                Abc_SopGetLitNum( char * pSop );
extern int                Abc_SopGetVarNum( char * pSop );
extern int                Abc_SopGetPhase( char * pSop );
extern int                Abc_SopGetIthCareLit( char * pSop, int i );
extern void               Abc_SopComplement( char * pSop );
extern bool               Abc_SopIsComplement( char * pSop );
extern bool               Abc_SopIsConst0( char * pSop );
extern bool               Abc_SopIsConst1( char * pSop );
extern bool               Abc_SopIsBuf( char * pSop );
extern bool               Abc_SopIsInv( char * pSop );
extern bool               Abc_SopIsAndType( char * pSop );
extern bool               Abc_SopIsOrType( char * pSop );
extern bool               Abc_SopCheck( char * pSop, int nFanins );
extern void               Abc_SopWriteCnf( FILE * pFile, char * pClauses, Vec_Int_t * vVars );
extern void               Abc_SopAddCnfToSolver( solver * pSat, char * pClauses, Vec_Int_t * vVars, Vec_Int_t * vTemp );
/*=== abcStrash.c ==========================================================*/
extern Abc_Ntk_t *        Abc_NtkStrash( Abc_Ntk_t * pNtk, bool fAllNodes, bool fCleanup );
extern Abc_Obj_t *        Abc_NodeStrash( Abc_Aig_t * pMan, Abc_Obj_t * pNode );
extern int                Abc_NtkAppend( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2 );
/*=== abcSweep.c ==========================================================*/
extern bool               Abc_NtkFraigSweep( Abc_Ntk_t * pNtk, int fUseInv, int fVerbose );
extern int                Abc_NtkCleanup( Abc_Ntk_t * pNtk, int fVerbose );
extern int                Abc_NtkSweep( Abc_Ntk_t * pNtk, int fVerbose );
/*=== abcTiming.c ==========================================================*/
extern Abc_Time_t *       Abc_NodeReadArrival( Abc_Obj_t * pNode );
extern Abc_Time_t *       Abc_NodeReadRequired( Abc_Obj_t * pNode );
extern Abc_Time_t *       Abc_NtkReadDefaultArrival( Abc_Ntk_t * pNtk );
extern Abc_Time_t *       Abc_NtkReadDefaultRequired( Abc_Ntk_t * pNtk );
extern void               Abc_NtkTimeSetDefaultArrival( Abc_Ntk_t * pNtk, float Rise, float Fall );
extern void               Abc_NtkTimeSetDefaultRequired( Abc_Ntk_t * pNtk, float Rise, float Fall );
extern void               Abc_NtkTimeSetArrival( Abc_Ntk_t * pNtk, int ObjId, float Rise, float Fall );
extern void               Abc_NtkTimeSetRequired( Abc_Ntk_t * pNtk, int ObjId, float Rise, float Fall );
extern void               Abc_NtkTimeInitialize( Abc_Ntk_t * pNtk );
extern void               Abc_ManTimeStop( Abc_ManTime_t * p );
extern void               Abc_ManTimeDup( Abc_Ntk_t * pNtkOld, Abc_Ntk_t * pNtkNew );
extern void               Abc_NtkSetNodeLevelsArrival( Abc_Ntk_t * pNtk );
extern float *            Abc_NtkGetCiArrivalFloats( Abc_Ntk_t * pNtk );
extern Abc_Time_t *       Abc_NtkGetCiArrivalTimes( Abc_Ntk_t * pNtk );
extern float              Abc_NtkDelayTrace( Abc_Ntk_t * pNtk );
extern void               Abc_NtkStartReverseLevels( Abc_Ntk_t * pNtk );
extern void               Abc_NtkStopReverseLevels( Abc_Ntk_t * pNtk );
extern void               Abc_NodeSetReverseLevel( Abc_Obj_t * pObj, int LevelR );
extern int                Abc_NodeReadReverseLevel( Abc_Obj_t * pObj );
extern int                Abc_NodeReadRequiredLevel( Abc_Obj_t * pObj );
/*=== abcUtil.c ==========================================================*/
extern void               Abc_NtkIncrementTravId( Abc_Ntk_t * pNtk );
extern int                Abc_NtkGetCubeNum( Abc_Ntk_t * pNtk );
extern int                Abc_NtkGetLitNum( Abc_Ntk_t * pNtk );
extern int                Abc_NtkGetLitFactNum( Abc_Ntk_t * pNtk );
extern int                Abc_NtkGetBddNodeNum( Abc_Ntk_t * pNtk );
extern int                Abc_NtkGetClauseNum( Abc_Ntk_t * pNtk );
extern double             Abc_NtkGetMappedArea( Abc_Ntk_t * pNtk );
extern int                Abc_NtkGetExorNum( Abc_Ntk_t * pNtk );
extern int                Abc_NtkGetChoiceNum( Abc_Ntk_t * pNtk );
extern int                Abc_NtkGetFaninMax( Abc_Ntk_t * pNtk );
extern void               Abc_NtkCleanCopy( Abc_Ntk_t * pNtk );
extern Abc_Obj_t *        Abc_NodeHasUniqueCoFanout( Abc_Obj_t * pNode );
extern bool               Abc_NtkLogicHasSimpleCos( Abc_Ntk_t * pNtk );
extern int                Abc_NtkLogicMakeSimpleCos( Abc_Ntk_t * pNtk, bool fDuplicate );
extern void               Abc_VecObjPushUniqueOrderByLevel( Vec_Ptr_t * p, Abc_Obj_t * pNode );
extern bool               Abc_NodeIsExorType( Abc_Obj_t * pNode );
extern bool               Abc_NodeIsMuxType( Abc_Obj_t * pNode );
extern Abc_Obj_t *        Abc_NodeRecognizeMux( Abc_Obj_t * pNode, Abc_Obj_t ** ppNodeT, Abc_Obj_t ** ppNodeE );
extern int                Abc_NtkPrepareTwoNtks( FILE * pErr, Abc_Ntk_t * pNtk, char ** argv, int argc, Abc_Ntk_t ** ppNtk1, Abc_Ntk_t ** ppNtk2, int * pfDelete1, int * pfDelete2 );
extern void               Abc_NodeCollectFanins( Abc_Obj_t * pNode, Vec_Ptr_t * vNodes );
extern void               Abc_NodeCollectFanouts( Abc_Obj_t * pNode, Vec_Ptr_t * vNodes );
extern int                Abc_NodeCompareLevelsIncrease( Abc_Obj_t ** pp1, Abc_Obj_t ** pp2 );
extern int                Abc_NodeCompareLevelsDecrease( Abc_Obj_t ** pp1, Abc_Obj_t ** pp2 );
extern Vec_Int_t *        Abc_NtkFanoutCounts( Abc_Ntk_t * pNtk );
extern Vec_Ptr_t *        Abc_NtkCollectObjects( Abc_Ntk_t * pNtk );

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

#endif

