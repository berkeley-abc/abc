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
    ABC_NTK_NONE,              // unknown
    ABC_NTK_NETLIST,           // net and node list as in the input file
    ABC_NTK_LOGIC_SOP,         // only SOP logic nodes (similar to SIS network)
    ABC_NTK_LOGIC_BDD,         // only BDD logic nodes (similar to BDS network)
    ABC_NTK_LOGIC_MAP,         // only mapped logic nodes (similar to mapped SIS network)
    ABC_NTK_AIG,               // AIG or FRAIG (two input gates with c-attributes on edges)
    ABC_NTK_SEQ,               // sequential AIG (two input gates with c- and latch-attributes on edges)
    ABC_NTK_OTHER              // unused
} Abc_NtkType_t;

// object types
typedef enum { 
    ABC_OBJ_TYPE_NONE,         // unknown
    ABC_OBJ_TYPE_NET,          // net
    ABC_OBJ_TYPE_NODE,         // node
    ABC_OBJ_TYPE_LATCH,        // latch
    ABC_OBJ_TYPE_TERM,         // terminal
    ABC_OBJ_TYPE_OTHER         // unused
} Abc_ObjType_t;

// object subtypes
typedef enum { 
    ABC_OBJ_SUBTYPE_PI = 0x01, // primary input
    ABC_OBJ_SUBTYPE_PO = 0x02, // primary output
    ABC_OBJ_SUBTYPE_LI = 0x04, // primary latch input
    ABC_OBJ_SUBTYPE_LO = 0x08  // primary latch output
} Abc_ObjSubtype_t;

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
typedef struct Abc_ManRes_t_  Abc_ManRes_t;
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
    unsigned         Type    :  4;  // the object type
    unsigned         Subtype :  4;  // the object subtype
    unsigned         Id      : 24;  // the ID of the object
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
    Abc_Ntk_t *      pNtk;          // the host network
    void *           pData;         // the network specific data (SOP, BDD, gate, equiv class, etc)
    Abc_Obj_t *      pNext;         // the next pointer in the hash table
    Abc_Obj_t *      pCopy;         // the copy of this object
};

struct Abc_Ntk_t_ 
{
    // general information about the network
    Abc_NtkType_t    Type;          // type of the network
    char *           pName;         // the network name
    char *           pSpec;         // the name of the spec file if present
    // name representation in the netlist
    stmm_table *     tName2Net;     // the table hashing net names into net pointer
    // name representation in the logic network
    Vec_Ptr_t *      vNamesPi;      // the array of PI node names
    Vec_Ptr_t *      vNamesLatch;   // the array of latch names names
    Vec_Ptr_t *      vNamesPo;      // the array of PO node names
    // components of the network
    Vec_Ptr_t *      vObjs;         // the array of all objects (net, nodes, latches)
    Vec_Ptr_t *      vPis;          // the array of PIs
    Vec_Ptr_t *      vPos;          // the array of POs
    Vec_Ptr_t *      vLatches;      // the array of latches (or the cutset in the sequential network)
    // the stats about the number of living objects
    int              nObjs;         // the number of living objs
    int              nNets;         // the number of living nets
    int              nNodes;        // the number of living nodes
    int              nLatches;      // the number of latches
    int              nPis;          // the number of primary inputs
    int              nPos;          // the number of primary outputs
    // the functionality manager 
    void *           pManFunc;      // AIG manager, BDD manager, or memory manager for SOPs
    // the timing manager
    Abc_ManTime_t *  pManTime;      // stores arrival/required times for all nodes
    // the external don't-care if given
    Abc_Ntk_t *      pExdc;         // the EXDC network
    // miscellaneous data members
    Vec_Ptr_t *      vLatches2;     // the temporary array of latches
    int              nPisOld;       // the number of old PIs
    int              nPosOld;       // the number of old PIs
    unsigned         nTravIds;      // the unique traversal IDs of nodes
    Vec_Ptr_t *      vPtrTemp;      // the temporary array
    Vec_Int_t *      vIntTemp;      // the temporary array
    Vec_Str_t *      vStrTemp;      // the temporary array
    // the backup network and the step number
    Abc_Ntk_t *      pNetBackup;    // the pointer to the previous backup network
    int              iStep;         // the generation number for the given network
    // memory management
    Extra_MmFlex_t * pMmNames;      // memory manager for net names
    Extra_MmFixed_t* pMmObj;        // memory manager for objects
    Extra_MmStep_t * pMmStep;       // memory manager for arrays
};

struct Abc_ManRes_t_
{
    // user specified parameters
    int              nNodeSizeMax;  // the limit on the size of the supernode
    int              nConeSizeMax;  // the limit on the size of the containing cone
    int              fVerbose;      // the verbosity flag
    // internal parameters
    DdManager *      dd;            // the BDD manager
    DdNode *         bCubeX;        // the cube of PI variables
    Abc_Obj_t *      pNode;         // the node currently considered
    Vec_Ptr_t *      vFaninsNode;   // fanins of the supernode
    Vec_Ptr_t *      vInsideNode;   // inside of the supernode
    Vec_Ptr_t *      vFaninsCone;   // fanins of the containing cone
    Vec_Ptr_t *      vInsideCone;   // inside of the containing cone
    Vec_Ptr_t *      vVisited;      // the visited nodes
    Vec_Str_t *      vCube;         // temporary cube for generating covers
    Vec_Int_t *      vForm;         // the factored form (temporary)
    // runtime statistics
    int              time1;
    int              time2;
    int              time3;
    int              time4;
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFITIONS                             ///
////////////////////////////////////////////////////////////////////////

// reading data members of the network
static inline char *      Abc_NtkName( Abc_Ntk_t * pNtk )          { return pNtk->pName;           }
static inline char *      Abc_NtkSpec( Abc_Ntk_t * pNtk )          { return pNtk->pSpec;           }
static inline int         Abc_NtkTravId( Abc_Ntk_t * pNtk )        { return pNtk->nTravIds;        }    
static inline Abc_Ntk_t * Abc_NtkExdc( Abc_Ntk_t * pNtk )          { return pNtk->pExdc;           }
static inline Abc_Ntk_t * Abc_NtkBackup( Abc_Ntk_t * pNtk )        { return pNtk->pNetBackup;      }
static inline int         Abc_NtkStep  ( Abc_Ntk_t * pNtk )        { return pNtk->iStep;           }

static inline Vec_Ptr_t * Abc_NtkObjVec( Abc_Ntk_t * pNtk )        { return pNtk->vObjs;           }
static inline Vec_Ptr_t * Abc_NtkLatchVec( Abc_Ntk_t * pNtk )      { return pNtk->vLatches;        }
static inline Vec_Ptr_t * Abc_NtkPiVec( Abc_Ntk_t * pNtk )         { return pNtk->vPis;            }
static inline Vec_Ptr_t * Abc_NtkPoVec( Abc_Ntk_t * pNtk )         { return pNtk->vPos;            }

static inline Abc_Obj_t * Abc_NtkObj( Abc_Ntk_t * pNtk, int i )    { return pNtk->vObjs->pArray[i];     }
static inline Abc_Obj_t * Abc_NtkLatch( Abc_Ntk_t * pNtk, int i )  { return pNtk->vLatches->pArray[i];  }
static inline Abc_Obj_t * Abc_NtkPi( Abc_Ntk_t * pNtk, int i )     { return pNtk->vPis->pArray[i];      }
static inline Abc_Obj_t * Abc_NtkPo( Abc_Ntk_t * pNtk, int i )     { return pNtk->vPos->pArray[i];      }
static inline Abc_Obj_t * Abc_NtkCi( Abc_Ntk_t * pNtk, int i )     { return pNtk->vPis->pArray[i];      }
static inline Abc_Obj_t * Abc_NtkCo( Abc_Ntk_t * pNtk, int i )     { return pNtk->vPos->pArray[i];      }

// setting data members of the network
static inline void        Abc_NtkSetName  ( Abc_Ntk_t * pNtk, char * pName )           { pNtk->pName      = pName;      } 
static inline void        Abc_NtkSetSpec  ( Abc_Ntk_t * pNtk, char * pName )           { pNtk->pSpec      = pName;      } 
static inline void        Abc_NtkSetBackup( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNetBackup ) { pNtk->pNetBackup = pNetBackup; }
static inline void        Abc_NtkSetStep  ( Abc_Ntk_t * pNtk, int iStep )              { pNtk->iStep      = iStep;      }

// checking the network type
static inline bool        Abc_NtkIsNetlist( Abc_Ntk_t * pNtk )    {  return pNtk->Type == ABC_NTK_NETLIST;   }
static inline bool        Abc_NtkIsLogicSop( Abc_Ntk_t * pNtk )   {  return pNtk->Type == ABC_NTK_LOGIC_SOP; }
static inline bool        Abc_NtkIsLogicBdd( Abc_Ntk_t * pNtk )   {  return pNtk->Type == ABC_NTK_LOGIC_BDD; }
static inline bool        Abc_NtkIsLogicMap( Abc_Ntk_t * pNtk )   {  return pNtk->Type == ABC_NTK_LOGIC_MAP; }
static inline bool        Abc_NtkIsLogic( Abc_Ntk_t * pNtk )      {  return pNtk->Type == ABC_NTK_LOGIC_SOP || pNtk->Type == ABC_NTK_LOGIC_BDD || pNtk->Type == ABC_NTK_LOGIC_MAP; }
static inline bool        Abc_NtkIsAig( Abc_Ntk_t * pNtk )        {  return pNtk->Type == ABC_NTK_AIG;       }
static inline bool        Abc_NtkIsSeq( Abc_Ntk_t * pNtk )        {  return pNtk->Type == ABC_NTK_SEQ;       }

// getting the number of different objects in the network
static inline int         Abc_NtkObjNum( Abc_Ntk_t * pNtk )        { return pNtk->nObjs;         }
static inline int         Abc_NtkNetNum( Abc_Ntk_t * pNtk )        { return pNtk->nNets;         }
static inline int         Abc_NtkNodeNum( Abc_Ntk_t * pNtk )       { return pNtk->nNodes;        }
static inline int         Abc_NtkLatchNum( Abc_Ntk_t * pNtk )      { return pNtk->nLatches;      }
static inline int         Abc_NtkPiNum( Abc_Ntk_t * pNtk )         { return pNtk->nPis;          }
static inline int         Abc_NtkPoNum( Abc_Ntk_t * pNtk )         { return pNtk->nPos;          }
static inline int         Abc_NtkCiNum( Abc_Ntk_t * pNtk )         { return pNtk->vPis->nSize;   }
static inline int         Abc_NtkCoNum( Abc_Ntk_t * pNtk )         { return pNtk->vPos->nSize;   }

// getting hold of the names of the PIs/POs/latches
static inline char *      Abc_NtkNameLatch(Abc_Ntk_t * pNtk, int i){ return pNtk->vNamesLatch->pArray[i];  }
static inline char *      Abc_NtkNamePi( Abc_Ntk_t * pNtk, int i ) { return pNtk->vNamesPi->pArray[i];     }
static inline char *      Abc_NtkNamePo( Abc_Ntk_t * pNtk, int i ) { return pNtk->vNamesPo->pArray[i];     }
static inline char *      Abc_NtkNameCi( Abc_Ntk_t * pNtk, int i ) { return pNtk->vNamesPi->pArray[i];     }
static inline char *      Abc_NtkNameCo( Abc_Ntk_t * pNtk, int i ) { return pNtk->vNamesPo->pArray[i];     }

// working with complemented attributes of objects
static inline bool        Abc_ObjIsComplement( Abc_Obj_t * p )    { return (bool)(((unsigned)p) & 01);           }
static inline Abc_Obj_t * Abc_ObjRegular( Abc_Obj_t * p )         { return (Abc_Obj_t *)((unsigned)(p) & ~01);  }
static inline Abc_Obj_t * Abc_ObjNot( Abc_Obj_t * p )             { return (Abc_Obj_t *)((unsigned)(p) ^  01);  }
static inline Abc_Obj_t * Abc_ObjNotCond( Abc_Obj_t * p, int c )  { return (Abc_Obj_t *)((unsigned)(p) ^ (c));  }

// reading data members of the object
static inline unsigned    Abc_ObjType( Abc_Obj_t * pObj )         { return pObj->Type;               }
static inline unsigned    Abc_ObjSubtype( Abc_Obj_t * pObj )      { return pObj->Subtype;            }
static inline unsigned    Abc_ObjId( Abc_Obj_t * pObj )           { return pObj->Id;                 }
static inline int         Abc_ObjTravId( Abc_Obj_t * pObj )       { return pObj->TravId;             }
static inline Vec_Fan_t * Abc_ObjFaninVec( Abc_Obj_t * pObj )     { return &pObj->vFanins;           }
static inline Vec_Fan_t * Abc_ObjFanoutVec( Abc_Obj_t * pObj )    { return &pObj->vFanouts;          }
static inline Abc_Obj_t * Abc_ObjCopy( Abc_Obj_t * pObj )         { return pObj->pCopy;              }
static inline Abc_Ntk_t * Abc_ObjNtk( Abc_Obj_t * pObj )          { return pObj->pNtk;               }
static inline void *      Abc_ObjData( Abc_Obj_t * pObj )         { return pObj->pData;              }

static inline int         Abc_ObjFaninNum( Abc_Obj_t * pObj )     { return pObj->vFanins.nSize;      }
static inline int         Abc_ObjFanoutNum( Abc_Obj_t * pObj )    { return pObj->vFanouts.nSize;     }
static inline Abc_Obj_t * Abc_ObjFanout( Abc_Obj_t * pObj, int i ){ return pObj->pNtk->vObjs->pArray[ pObj->vFanouts.pArray[i].iFan ]; }
static inline Abc_Obj_t * Abc_ObjFanout0( Abc_Obj_t * pObj )      { return pObj->pNtk->vObjs->pArray[ pObj->vFanouts.pArray[0].iFan ]; }
static inline Abc_Obj_t * Abc_ObjFanin( Abc_Obj_t * pObj, int i ) { return pObj->pNtk->vObjs->pArray[ pObj->vFanins.pArray[i].iFan  ]; }
static inline Abc_Obj_t * Abc_ObjFanin0( Abc_Obj_t * pObj )       { return pObj->pNtk->vObjs->pArray[ pObj->vFanins.pArray[0].iFan  ]; }
static inline Abc_Obj_t * Abc_ObjFanin1( Abc_Obj_t * pObj )       { return pObj->pNtk->vObjs->pArray[ pObj->vFanins.pArray[1].iFan  ]; }
static inline int         Abc_ObjFaninId( Abc_Obj_t * pObj, int i){ return pObj->vFanins.pArray[i].iFan; }
static inline int         Abc_ObjFaninId0( Abc_Obj_t * pObj )     { return pObj->vFanins.pArray[0].iFan; }
static inline int         Abc_ObjFaninId1( Abc_Obj_t * pObj )     { return pObj->vFanins.pArray[1].iFan; }
static inline bool        Abc_ObjFaninC( Abc_Obj_t * pObj, int i ){ return pObj->vFanins.pArray[i].fCompl;                             }
static inline bool        Abc_ObjFaninC0( Abc_Obj_t * pObj )      { return pObj->vFanins.pArray[0].fCompl;                             }
static inline bool        Abc_ObjFaninC1( Abc_Obj_t * pObj )      { return pObj->vFanins.pArray[1].fCompl;                             }
static inline Abc_Obj_t * Abc_ObjChild0( Abc_Obj_t * pObj )       { return Abc_ObjNotCond( Abc_ObjFanin0(pObj), Abc_ObjFaninC0(pObj) );}
static inline Abc_Obj_t * Abc_ObjChild1( Abc_Obj_t * pObj )       { return Abc_ObjNotCond( Abc_ObjFanin1(pObj), Abc_ObjFaninC1(pObj) );}
static inline void        Abc_ObjSetFaninC( Abc_Obj_t * pObj, int i ){ pObj->vFanins.pArray[i].fCompl = 1;                             }
static inline void        Abc_ObjXorFaninC( Abc_Obj_t * pObj, int i ){ pObj->vFanins.pArray[i].fCompl ^= 1;                             }

// setting data members of the network
static inline void        Abc_ObjSetCopy( Abc_Obj_t * pObj, Abc_Obj_t * pCopy )             { pObj->pCopy    =  pCopy;    } 
static inline void        Abc_ObjSetData( Abc_Obj_t * pObj, void * pData )                  { pObj->pData    =  pData;    } 
static inline void        Abc_ObjSetSubtype( Abc_Obj_t * pObj, Abc_ObjSubtype_t Subtype )   { pObj->Subtype |=  Subtype;  }
static inline void        Abc_ObjUnsetSubtype( Abc_Obj_t * pObj, Abc_ObjSubtype_t Subtype ) { pObj->Subtype &= ~Subtype;  }

// checking the object type
static inline bool        Abc_ObjIsNode( Abc_Obj_t * pObj )       { return pObj->Type == ABC_OBJ_TYPE_NODE;   }
static inline bool        Abc_ObjIsNet( Abc_Obj_t * pObj )        { return pObj->Type == ABC_OBJ_TYPE_NET;    }
static inline bool        Abc_ObjIsLatch( Abc_Obj_t * pObj )      { return pObj->Type == ABC_OBJ_TYPE_LATCH;  }
static inline bool        Abc_ObjIsTerm( Abc_Obj_t * pObj )       { return pObj->Type == ABC_OBJ_TYPE_TERM;   }
 
static inline bool        Abc_ObjIsPi( Abc_Obj_t * pObj )         { return ((pObj->Subtype & ABC_OBJ_SUBTYPE_PI) > 0);  }
static inline bool        Abc_ObjIsPo( Abc_Obj_t * pObj )         { return ((pObj->Subtype & ABC_OBJ_SUBTYPE_PO) > 0);  }
static inline bool        Abc_ObjIsLi( Abc_Obj_t * pObj )         { return ((pObj->Subtype & ABC_OBJ_SUBTYPE_LI) > 0);  }
static inline bool        Abc_ObjIsLo( Abc_Obj_t * pObj )         { return ((pObj->Subtype & ABC_OBJ_SUBTYPE_LO) > 0);  }
static inline bool        Abc_ObjIsCi( Abc_Obj_t * pObj )         { if ( Abc_NtkIsNetlist(pObj->pNtk) ) return ((pObj->Subtype & (ABC_OBJ_SUBTYPE_PI | ABC_OBJ_SUBTYPE_LO)) > 0); else return (Abc_ObjIsPi(pObj) || Abc_ObjIsLatch(pObj)); }
static inline bool        Abc_ObjIsCo( Abc_Obj_t * pObj )         { if ( Abc_NtkIsNetlist(pObj->pNtk) ) return ((pObj->Subtype & (ABC_OBJ_SUBTYPE_PO | ABC_OBJ_SUBTYPE_LI)) > 0); else return (Abc_ObjIsPo(pObj) || Abc_ObjIsLatch(pObj)); }

// checking the node type
static inline bool        Abc_NodeIsAnd( Abc_Obj_t * pNode )      { assert(Abc_ObjIsNode(Abc_ObjRegular(pNode))); assert(Abc_NtkIsAig(Abc_ObjRegular(pNode)->pNtk)); return Abc_ObjFaninNum(Abc_ObjRegular(pNode)) == 2; }
static inline bool        Abc_NodeIsChoice( Abc_Obj_t * pNode )   { assert(Abc_ObjIsNode(Abc_ObjRegular(pNode))); assert(Abc_NtkIsAig(Abc_ObjRegular(pNode)->pNtk)); return Abc_ObjRegular(pNode)->pData != NULL && Abc_ObjFanoutNum(Abc_ObjRegular(pNode)) > 0;  }
static inline bool        Abc_NodeIsConst( Abc_Obj_t * pNode )    { assert(Abc_ObjIsNode(Abc_ObjRegular(pNode))); return Abc_ObjFaninNum(Abc_ObjRegular(pNode)) == 0; }
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

// maximum/minimum operators
#define ABC_MIN(a,b)      (((a) < (b))? (a) : (b))
#define ABC_MAX(a,b)      (((a) > (b))? (a) : (b))
#define ABC_INFINITY      (10000000)

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
    for ( i = 0; i < Vec_PtrSize(pNtk->vLatches); i++ )                  \
        if ( pObj = Abc_NtkLatch(pNtk, i) )
// inputs and outputs
#define Abc_NtkForEachPi( pNtk, pPi, i )                                 \
    for ( i = 0; i < Abc_NtkPiNum(pNtk); i++ )                           \
        if ( pPi = Abc_NtkPi(pNtk, i) )
#define Abc_NtkForEachPo( pNtk, pPo, i )                                 \
    for ( i = 0; i < Abc_NtkPoNum(pNtk); i++ )                           \
        if ( pPo = Abc_NtkPo(pNtk, i) )
#define Abc_NtkForEachCi( pNtk, pPi, i )                                 \
    for ( i = 0; i < Abc_NtkCiNum(pNtk); i++ )                           \
        if ( pPi = Abc_NtkPi(pNtk, i) )
#define Abc_NtkForEachCo( pNtk, pPo, i )                                 \
    for ( i = 0; i < Abc_NtkCoNum(pNtk); i++ )                           \
        if ( pPo = Abc_NtkPo(pNtk, i) )
// fanin and fanouts
#define Abc_ObjForEachFanin( pObj, pFanin, i )                           \
    for ( i = 0; i < Abc_ObjFaninNum(pObj); i++ )                        \
        if ( pFanin = Abc_ObjFanin(pObj, i) )
#define Abc_ObjForEachFanout( pObj, pFanout, i )                         \
    for ( i = 0; i < Abc_ObjFanoutNum(pObj); i++ )                       \
        if ( pFanout = Abc_ObjFanout(pObj, i) )
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
extern void               Abc_AigFree( Abc_Aig_t * pMan );
extern Abc_Obj_t *        Abc_AigConst1( Abc_Aig_t * pMan );
extern Abc_Obj_t *        Abc_AigAnd( Abc_Aig_t * pMan, Abc_Obj_t * p0, Abc_Obj_t * p1 );
extern Abc_Obj_t *        Abc_AigOr( Abc_Aig_t * pMan, Abc_Obj_t * p0, Abc_Obj_t * p1 );
extern Abc_Obj_t *        Abc_AigXor( Abc_Aig_t * pMan, Abc_Obj_t * p0, Abc_Obj_t * p1 );
extern Abc_Obj_t *        Abc_AigMiter( Abc_Aig_t * pMan, Vec_Ptr_t * vPairs );
extern bool               Abc_AigNodeIsUsedCompl( Abc_Obj_t * pNode );
/*=== abcAttach.c ==========================================================*/
extern int                Abc_NtkAttach( Abc_Ntk_t * pNtk );
/*=== abcCheck.c ==========================================================*/
extern bool               Abc_NtkCheck( Abc_Ntk_t * pNtk );
extern bool               Abc_NtkCompareSignals( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int fComb );
/*=== abcCollapse.c ==========================================================*/
extern Abc_Ntk_t *        Abc_NtkCollapse( Abc_Ntk_t * pNtk, int fVerbose );
extern DdManager *        Abc_NtkGlobalBdds( Abc_Ntk_t * pNtk, int fLatchOnly );
extern void               Abc_NtkFreeGlobalBdds( DdManager * dd, Abc_Ntk_t * pNtk );
/*=== abcCreate.c ==========================================================*/
extern Abc_Ntk_t *        Abc_NtkAlloc( Abc_NtkType_t Type );
extern Abc_Ntk_t *        Abc_NtkStartFrom( Abc_Ntk_t * pNtk, Abc_NtkType_t Type );
extern void               Abc_NtkFinalize( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkNew );
extern Abc_Ntk_t *        Abc_NtkDup( Abc_Ntk_t * pNtk );
extern Abc_Ntk_t *        Abc_NtkSplitOutput( Abc_Ntk_t * pNtk, Abc_Obj_t * pNode, int fUseAllCis );
extern void               Abc_NtkDelete( Abc_Ntk_t * pNtk );
extern Abc_Obj_t *        Abc_NtkDupObj( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pObj );
extern void               Abc_NtkDeleteObj( Abc_Obj_t * pObj );
extern void               Abc_NtkMarkNetPi( Abc_Obj_t * pObj );
extern void               Abc_NtkMarkNetPo( Abc_Obj_t * pObj );
extern Abc_Obj_t *        Abc_NtkAddPoNode( Abc_Obj_t * pObj );
extern void               Abc_NtkRemovePoNode( Abc_Obj_t * pNode );
extern Abc_Obj_t *        Abc_NtkFindNode( Abc_Ntk_t * pNtk, char * pName );
extern Abc_Obj_t *        Abc_NtkFindCo( Abc_Ntk_t * pNtk, char * pName );
extern Abc_Obj_t *        Abc_NtkFindNet( Abc_Ntk_t * pNtk, char * pName );
extern Abc_Obj_t *        Abc_NtkFindOrCreateNet( Abc_Ntk_t * pNtk, char * pName );
extern Abc_Obj_t *        Abc_NtkCreateNode( Abc_Ntk_t * pNtk );
extern Abc_Obj_t *        Abc_NtkCreateTermPi( Abc_Ntk_t * pNtk );
extern Abc_Obj_t *        Abc_NtkCreateTermPo( Abc_Ntk_t * pNtk );
extern Abc_Obj_t *        Abc_NtkCreateLatch( Abc_Ntk_t * pNtk );
extern Abc_Obj_t *        Abc_NodeCreateConst0( Abc_Ntk_t * pNtk );
extern Abc_Obj_t *        Abc_NodeCreateConst1( Abc_Ntk_t * pNtk );
extern Abc_Obj_t *        Abc_NodeCreateInv( Abc_Ntk_t * pNtk, Abc_Obj_t * pFanin );
extern Abc_Obj_t *        Abc_NodeCreateBuf( Abc_Ntk_t * pNtk, Abc_Obj_t * pFanin );
extern Abc_Obj_t *        Abc_NodeCreateAnd( Abc_Ntk_t * pNtk, Vec_Ptr_t * vFanins );
extern Abc_Obj_t *        Abc_NodeCreateOr( Abc_Ntk_t * pNtk, Vec_Ptr_t * vFanins );
extern Abc_Obj_t *        Abc_NodeCreateMux( Abc_Ntk_t * pNtk, Abc_Obj_t * pNodeC, Abc_Obj_t * pNode1, Abc_Obj_t * pNode0 );
extern Abc_Obj_t *        Abc_NodeClone( Abc_Obj_t * pNode );
/*=== abcDfs.c ==========================================================*/
extern Vec_Ptr_t *        Abc_NtkDfs( Abc_Ntk_t * pNtk );
extern Vec_Ptr_t *        Abc_NtkDfsNodes( Abc_Ntk_t * pNtk, Abc_Obj_t ** ppNodes, int nNodes );
extern Vec_Ptr_t *        Abc_AigDfs( Abc_Ntk_t * pNtk );
extern Vec_Ptr_t *        Abc_DfsLevelized( Abc_Obj_t * pNode, bool fTfi );
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
extern char *             Abc_ConvertBddToSop( Extra_MmFlex_t * pMan, DdManager * dd, DdNode * bFuncOn, DdNode * bFuncOnDc, int nFanins, Vec_Str_t * vCube, int fMode );
extern int                Abc_NtkBddToSop( Abc_Ntk_t * pNtk );
extern void               Abc_NodeBddToCnf( Abc_Obj_t * pNode, Extra_MmFlex_t * pMmMan, Vec_Str_t * vCube, char ** ppSop0, char ** ppSop1 );
extern int                Abc_CountZddCubes( DdManager * dd, DdNode * zCover );
/*=== abcLatch.c ==========================================================*/
extern bool               Abc_NtkIsComb( Abc_Ntk_t * pNtk );
extern bool               Abc_NtkMakeComb( Abc_Ntk_t * pNtk );
extern bool               Abc_NtkMakeSeq( Abc_Ntk_t * pNtk );
extern bool               Abc_NtkLatchIsSelfFeed( Abc_Obj_t * pLatch );
extern int                Abc_NtkCountSelfFeedLatches( Abc_Ntk_t * pNtk );
/*=== abcMap.c ==========================================================*/
extern Abc_Ntk_t *        Abc_NtkMap( Abc_Ntk_t * pNtk, double DelayTarget, int fRecovery, int fVerbose );
extern int                Abc_NtkUnmap( Abc_Ntk_t * pNtk );
/*=== abcMiter.c ==========================================================*/
extern int                Abc_NtkMinimumBase( Abc_Ntk_t * pNtk );
extern int                Abc_NodeMinimumBase( Abc_Obj_t * pNode );
/*=== abcMiter.c ==========================================================*/
extern Abc_Ntk_t *        Abc_NtkMiter( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int fComb );
extern int                Abc_NtkMiterIsConstant( Abc_Ntk_t * pMiter );
extern void               Abc_NtkMiterReport( Abc_Ntk_t * pMiter );
extern int                Abc_NtkAppend( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2 );
extern Abc_Ntk_t *        Abc_NtkFrames( Abc_Ntk_t * pNtk, int nFrames, int fInitial );
/*=== abcNames.c ====================================================*/
extern char *             Abc_NtkRegisterName( Abc_Ntk_t * pNtk, char * pName );
extern char *             Abc_NtkRegisterNamePlus( Abc_Ntk_t * pNtk, char * pName, char * pSuffix );
extern stmm_table *       Abc_NtkLogicHashNames( Abc_Ntk_t * pNtk, int Type, int fComb );
extern void               Abc_NtkLogicTransferNames( Abc_Ntk_t * pNtk );
extern char *             Abc_NtkNameLatchInput( Abc_Ntk_t * pNtk, int i );
extern char *             Abc_ObjName( Abc_Obj_t * pNode );
extern char *             Abc_ObjNameUnique( Abc_Ntk_t * pNtk, char * pName );
extern char *             Abc_NtkLogicStoreName( Abc_Obj_t * pNodeNew, char * pNameOld );
extern char *             Abc_NtkLogicStoreNamePlus( Abc_Obj_t * pNodeNew, char * pNameOld, char * pSuffix );
extern void               Abc_NtkDupNameArrays( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkNew );
extern void               Abc_NtkCreateNameArrays( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkNew );
/*=== abcNetlist.c ==========================================================*/
extern Abc_Ntk_t *        Abc_NtkLogic( Abc_Ntk_t * pNtk );
/*=== abcPrint.c ==========================================================*/
extern void               Abc_NtkPrintStats( FILE * pFile, Abc_Ntk_t * pNtk );
extern void               Abc_NtkPrintIo( FILE * pFile, Abc_Ntk_t * pNtk );
extern void               Abc_NtkPrintFanio( FILE * pFile, Abc_Ntk_t * pNtk );
extern void               Abc_NodePrintFanio( FILE * pFile, Abc_Obj_t * pNode );
extern void               Abc_NtkPrintFactor( FILE * pFile, Abc_Ntk_t * pNtk );
extern void               Abc_NodePrintFactor( FILE * pFile, Abc_Obj_t * pNode );
/*=== abcRefs.c ==========================================================*/
extern int                Abc_NodeMffcSize( Abc_Obj_t * pNode );
extern int                Abc_NodeMffcRemove( Abc_Obj_t * pNode );
/*=== abcRenode.c ==========================================================*/
extern Abc_Ntk_t *        Abc_NtkRenode( Abc_Ntk_t * pNtk, int nThresh, int nFaninMax, int fCnf, int fMulti, int fSimple );
extern DdNode *           Abc_NtkRenodeDeriveBdd( DdManager * dd, Abc_Obj_t * pNodeOld, Vec_Ptr_t * vFaninsOld );
/*=== abcRes.c ==========================================================*/
extern Abc_ManRes_t *     Abc_NtkManResStart();
extern void               Abc_NtkManResStop( Abc_ManRes_t * p );
/*=== abcSat.c ==========================================================*/
extern bool               Abc_NtkMiterSat( Abc_Ntk_t * pNtk, int fVerbose );
extern solver *           Abc_NtkMiterSatCreate( Abc_Ntk_t * pNtk );
/*=== abcSop.c ==========================================================*/
extern char *             Abc_SopRegister( Extra_MmFlex_t * pMan, char * pName );
extern char *             Abc_SopStart( Extra_MmFlex_t * pMan, int nCubes, int nVars );
extern int                Abc_SopGetCubeNum( char * pSop );
extern int                Abc_SopGetLitNum( char * pSop );
extern int                Abc_SopGetVarNum( char * pSop );
extern int                Abc_SopGetPhase( char * pSop );
extern bool               Abc_SopIsConst0( char * pSop );
extern bool               Abc_SopIsConst1( char * pSop );
extern bool               Abc_SopIsBuf( char * pSop );
extern bool               Abc_SopIsInv( char * pSop );
extern bool               Abc_SopIsAndType( char * pSop );
extern bool               Abc_SopIsOrType( char * pSop );
extern int                Abc_SopGetIthCareLit( char * pSop, int i );
extern void               Abc_SopComplement( char * pSop );
extern bool               Abc_SopCheck( char * pSop, int nFanins );
extern void               Abc_SopWriteCnf( FILE * pFile, char * pClauses, Vec_Int_t * vVars );
extern void               Abc_SopAddCnfToSolver( solver * pSat, char * pClauses, Vec_Int_t * vVars, Vec_Int_t * vTemp );
/*=== abcStrash.c ==========================================================*/
extern Abc_Ntk_t *        Abc_NtkStrash( Abc_Ntk_t * pNtk, bool fAllNodes );
extern int                Abc_NtkAppend( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2 );
extern Abc_Ntk_t *        Abc_NtkBalance( Abc_Ntk_t * pNtk, bool fDuplicate );
/*=== abcSweep.c ==========================================================*/
extern bool               Abc_NtkFraigSweep( Abc_Ntk_t * pNtk, int fUseInv, int fVerbose );
extern int                Abc_NtkCleanup( Abc_Ntk_t * pNtk, int fVerbose );
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
/*=== abcTravId.c ==========================================================*/
extern void               Abc_NtkIncrementTravId( Abc_Ntk_t * pNtk );
extern void               Abc_NodeSetTravId( Abc_Obj_t * pObj, int TravId );
extern void               Abc_NodeSetTravIdCurrent( Abc_Obj_t * pObj );
extern void               Abc_NodeSetTravIdPrevious( Abc_Obj_t * pObj );
extern bool               Abc_NodeIsTravIdCurrent( Abc_Obj_t * pObj );
extern bool               Abc_NodeIsTravIdPrevious( Abc_Obj_t * pObj );
/*=== abcUtil.c ==========================================================*/
extern void               Abc_NtkIncrementTravId( Abc_Ntk_t * pNtk );
extern int                Abc_NtkGetCubeNum( Abc_Ntk_t * pNtk );
extern int                Abc_NtkGetLitNum( Abc_Ntk_t * pNtk );
extern int                Abc_NtkGetLitFactNum( Abc_Ntk_t * pNtk );
extern int                Abc_NtkGetBddNodeNum( Abc_Ntk_t * pNtk );
extern int                Abc_NtkGetClauseNum( Abc_Ntk_t * pNtk );
extern double             Abc_NtkGetMappedArea( Abc_Ntk_t * pNtk );
extern int                Abc_NtkGetFaninMax( Abc_Ntk_t * pNtk );
extern void               Abc_NtkCleanCopy( Abc_Ntk_t * pNtk );
extern Abc_Obj_t *        Abc_NodeHasUniqueNamedFanout( Abc_Obj_t * pNode );
extern bool               Abc_NtkLogicHasSimplePos( Abc_Ntk_t * pNtk );
extern int                Abc_NtkLogicMakeSimplePos( Abc_Ntk_t * pNtk );
extern void               Abc_VecObjPushUniqueOrderByLevel( Vec_Ptr_t * p, Abc_Obj_t * pNode );
extern bool               Abc_NodeIsMuxType( Abc_Obj_t * pNode );
extern Abc_Obj_t *        Abc_NodeRecognizeMux( Abc_Obj_t * pNode, Abc_Obj_t ** ppNodeT, Abc_Obj_t ** ppNodeE );
extern int                Abc_NtkCountChoiceNodes( Abc_Ntk_t * pNtk );
extern int                Abc_NtkPrepareCommand( FILE * pErr, Abc_Ntk_t * pNtk, char ** argv, int argc, Abc_Ntk_t ** ppNtk1, Abc_Ntk_t ** ppNtk2, int * pfDelete1, int * pfDelete2 );
extern void               Abc_NodeCollectFanins( Abc_Obj_t * pNode, Vec_Ptr_t * vNodes );
extern void               Abc_NodeCollectFanouts( Abc_Obj_t * pNode, Vec_Ptr_t * vNodes );
extern int                Abc_NodeCompareLevelsIncrease( Abc_Obj_t ** pp1, Abc_Obj_t ** pp2 );
extern int                Abc_NodeCompareLevelsDecrease( Abc_Obj_t ** pp1, Abc_Obj_t ** pp2 );
extern Vec_Ptr_t *        Abc_AigCollectAll( Abc_Ntk_t * pNtk );
extern Vec_Ptr_t *        Abc_NodeGetFaninNames( Abc_Obj_t * pNode );
extern void               Abc_NodeFreeFaninNames( Vec_Ptr_t * vNames );


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

#endif

