/**CFile****************************************************************

  FileName    [ntk.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntk.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __NTK_H__
#define __NTK_H__

#ifdef __cplusplus
extern "C" {
#endif

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "aig.h"
#include "hop.h"
#include "tim.h"
#include "if.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Ntk_Man_t_    Ntk_Man_t;
typedef struct Ntk_Obj_t_    Ntk_Obj_t;

// object types
typedef enum { 
    NTK_OBJ_NONE,                      // 0: non-existant object
    NTK_OBJ_CI,                        // 1: combinational input
    NTK_OBJ_CO,                        // 2: combinational output
    NTK_OBJ_NODE,                      // 3: logic node
    NTK_OBJ_BOX,                       // 4: white box
    NTK_OBJ_LATCH,                     // 5: register
    NTK_OBJ_VOID                       // 6: unused object
} Ntk_Type_t;

struct Ntk_Man_t_
{
    // models of this design
    char *             pName;          // the name of this design
    char *             pSpec;          // the name of input file
    // node representation
    Vec_Ptr_t *        vCis;           // the primary inputs of the extracted part
    Vec_Ptr_t *        vCos;           // the primary outputs of the extracted part 
    Vec_Ptr_t *        vObjs;          // the objects in the topological order
    int                nObjs[NTK_OBJ_VOID]; // counter of objects of each type
    int                nFanioPlus;     // the number of extra fanins/fanouts alloc by default
    // functionality, timing, memory, etc
    Hop_Man_t *        pManHop;        // the functionality representation
    Tim_Man_t *        pManTime;       // the timing manager
    Aig_MmFlex_t *     pMemObjs;       // memory for objects
    Vec_Ptr_t *        vTemp;          // array used for incremental updates
    unsigned           nTravIds;       // the counter of traversal IDs
};

struct Ntk_Obj_t_
{
    Ntk_Man_t *        pMan;           // the manager  
    void *             pCopy;          // temporary pointer
    Hop_Obj_t *        pFunc;          // functionality
    // node information
    int                Id;             // unique ID
    int                PioId;          // number of this node in the PI/PO list
    unsigned           Type     :  3;  // object type
    unsigned           fCompl   :  1;  // complemented attribute
    unsigned           MarkA    :  1;  // temporary mark  
    unsigned           MarkB    :  1;  // temporary mark
    unsigned           TravId   : 26;  // traversal ID
    // timing information
    float              tArrival;       // the arrival time
    float              tRequired;      // the required time
    float              tSlack;         // the slack
    // fanin/fanout representation
    unsigned           nFanins  :  6;  // the number of fanins
    unsigned           nFanouts : 26;  // the number of fanouts
    int                nFanioAlloc;    // the number of allocated fanins/fanouts
    Ntk_Obj_t *        pFanio[0];      // fanins/fanouts
};


////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////
///                      INLINED FUNCTIONS                           ///
////////////////////////////////////////////////////////////////////////

static inline int         Ntk_ManCiNum( Ntk_Man_t * p )           { return p->nObjs[NTK_OBJ_CI];                } 
static inline int         Ntk_ManCoNum( Ntk_Man_t * p )           { return p->nObjs[NTK_OBJ_CO];                } 
static inline int         Ntk_ManNodeNum( Ntk_Man_t * p )         { return p->nObjs[NTK_OBJ_NODE];              } 
static inline int         Ntk_ManLatchNum( Ntk_Man_t * p )        { return p->nObjs[NTK_OBJ_LATCH];             } 
static inline int         Ntk_ManBoxNum( Ntk_Man_t * p )          { return p->nObjs[NTK_OBJ_BOX];               } 
static inline int         Ntk_ManObjNumMax( Ntk_Man_t * p )       { return Vec_PtrSize(p->vObjs);               }

static inline Ntk_Obj_t * Ntk_ManCi( Ntk_Man_t * p, int i )       { return Vec_PtrEntry( p->vCis, i );          } 
static inline Ntk_Obj_t * Ntk_ManCo( Ntk_Man_t * p, int i )       { return Vec_PtrEntry( p->vCos, i );          } 
static inline Ntk_Obj_t * Ntk_ManObj( Ntk_Man_t * p, int i )      { return Vec_PtrEntry( p->vObjs, i );         } 

static inline int         Ntk_ObjFaninNum( Ntk_Obj_t * p )        { return p->nFanins;                          } 
static inline int         Ntk_ObjFanoutNum( Ntk_Obj_t * p )       { return p->nFanouts;                         } 

static inline Ntk_Obj_t * Ntk_ObjFanin0( Ntk_Obj_t * p )          { return p->pFanio[0];                        } 
static inline Ntk_Obj_t * Ntk_ObjFanout0( Ntk_Obj_t * p )         { return p->pFanio[p->nFanins];               } 
static inline Ntk_Obj_t * Ntk_ObjFanin( Ntk_Obj_t * p, int i )    { return p->pFanio[i];                        } 
static inline Ntk_Obj_t * Ntk_ObjFanout( Ntk_Obj_t * p, int i )   { return p->pFanio[p->nFanins+1];             } 

static inline int         Ntk_ObjIsCi( Ntk_Obj_t * p )            { return p->Type == NTK_OBJ_CI;               } 
static inline int         Ntk_ObjIsCo( Ntk_Obj_t * p )            { return p->Type == NTK_OBJ_CO;               } 
static inline int         Ntk_ObjIsNode( Ntk_Obj_t * p )          { return p->Type == NTK_OBJ_NODE;             } 
static inline int         Ntk_ObjIsLatch( Ntk_Obj_t * p )         { return p->Type == NTK_OBJ_LATCH;            } 
static inline int         Ntk_ObjIsBox( Ntk_Obj_t * p )           { return p->Type == NTK_OBJ_BOX;              } 
static inline int         Ntk_ObjIsPi( Ntk_Obj_t * p )            { return Ntk_ObjIsCi(p) && Tim_ManBoxForCi(p->pMan->pManTime, p->PioId) == -1; } 
static inline int         Ntk_ObjIsPo( Ntk_Obj_t * p )            { return Ntk_ObjIsCo(p) && Tim_ManBoxForCo(p->pMan->pManTime, p->PioId) == -1;  }

static inline float       Ntk_ObjArrival( Ntk_Obj_t * pObj )                 { return pObj->tArrival;           }
static inline float       Ntk_ObjRequired( Ntk_Obj_t * pObj )                { return pObj->tRequired;          }
static inline float       Ntk_ObjSlack( Ntk_Obj_t * pObj )                   { return pObj->tSlack;             }
static inline void        Ntk_ObjSetArrival( Ntk_Obj_t * pObj, float Time )  { pObj->tArrival   = Time;         }
static inline void        Ntk_ObjSetRequired( Ntk_Obj_t * pObj, float Time ) { pObj->tRequired  = Time;         }
static inline void        Ntk_ObjSetSlack( Ntk_Obj_t * pObj, float Time )    { pObj->tSlack     = Time;         }

static inline int         Ntk_ObjLevel( Ntk_Obj_t * pObj )                   { return (int)pObj->tArrival;      }
static inline void        Ntk_ObjSetLevel( Ntk_Obj_t * pObj, int Lev )       { pObj->tArrival = (float)Lev;     }

static inline void        Ntk_ObjSetTravId( Ntk_Obj_t * pObj, int TravId )   { pObj->TravId = TravId;                           }
static inline void        Ntk_ObjSetTravIdCurrent( Ntk_Obj_t * pObj )        { pObj->TravId = pObj->pMan->nTravIds;             }
static inline void        Ntk_ObjSetTravIdPrevious( Ntk_Obj_t * pObj )       { pObj->TravId = pObj->pMan->nTravIds - 1;         }
static inline int         Ntk_ObjIsTravIdCurrent( Ntk_Obj_t * pObj )         { return pObj->TravId == pObj->pMan->nTravIds;     }
static inline int         Ntk_ObjIsTravIdPrevious( Ntk_Obj_t * pObj )        { return pObj->TravId == pObj->pMan->nTravIds - 1; }

////////////////////////////////////////////////////////////////////////
///                         ITERATORS                                ///
////////////////////////////////////////////////////////////////////////

#define Ntk_ManForEachCi( p, pObj, i )                                     \
    Vec_PtrForEachEntry( p->vCis, pObj, i )
#define Ntk_ManForEachCo( p, pObj, i )                                     \
    Vec_PtrForEachEntry( p->vCos, pObj, i )
#define Ntk_ManForEachPi( p, pObj, i )                                     \
    Vec_PtrForEachEntry( p->vCis, pObj, i )                                \
        if ( !Ntk_ObjIsPi(pObj) ) {} else
#define Ntk_ManForEachPo( p, pObj, i )                                     \
    Vec_PtrForEachEntry( p->vCos, pObj, i )                                \
        if ( !Ntk_ObjIsPo(pObj) ) {} else
#define Ntk_ManForEachObj( p, pObj, i )                                    \
    for ( i = 0; (i < Vec_PtrSize(p->vObjs)) && (((pObj) = Vec_PtrEntry(p->vObjs, i)), 1); i++ ) \
        if ( pObj == NULL ) {} else
#define Ntk_ManForEachNode( p, pObj, i )                                   \
    for ( i = 0; (i < Vec_PtrSize(p->vObjs)) && (((pObj) = Vec_PtrEntry(p->vObjs, i)), 1); i++ ) \
        if ( !Ntk_ObjIsNode(pObj) ) {} else
#define Ntk_ManForEachBox( p, pObj, i )                                    \
    for ( i = 0; (i < Vec_PtrSize(p->vObjs)) && (((pObj) = Vec_PtrEntry(p->vObjs, i)), 1); i++ ) \
        if ( !Ntk_ObjIsBox(pObj) ) {} else
#define Ntk_ManForEachLatch( p, pObj, i )                                  \
    for ( i = 0; (i < Vec_PtrSize(p->vObjs)) && (((pObj) = Vec_PtrEntry(p->vObjs, i)), 1); i++ ) \
        if ( !Ntk_ObjIsLatch(pObj) ) {} else

#define Ntk_ObjForEachFanin( pObj, pFanin, i )                                  \
    for ( i = 0; (i < (int)(pObj)->nFanins) && ((pFanin) = (pObj)->pFanio[i]); i++ )
#define Ntk_ObjForEachFanout( pObj, pFanout, i )                                \
    for ( i = 0; (i < (int)(pObj)->nFanouts) && ((pFanout) = (pObj)->pFanio[(pObj)->nFanins+i]); i++ )

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== ntkDfs.c ==========================================================*/
extern int             Ntk_ManLevel( Ntk_Man_t * pNtk );
extern int             Ntk_ManLevel2( Ntk_Man_t * pNtk );
extern Vec_Ptr_t *     Ntk_ManDfs( Ntk_Man_t * pNtk );
extern Vec_Ptr_t *     Ntk_ManDfsReverse( Ntk_Man_t * pNtk );
/*=== ntkFanio.c ==========================================================*/
extern void            Ntk_ObjCollectFanins( Ntk_Obj_t * pNode, Vec_Ptr_t * vNodes );
extern void            Ntk_ObjCollectFanouts( Ntk_Obj_t * pNode, Vec_Ptr_t * vNodes );
extern void            Ntk_ObjAddFanin( Ntk_Obj_t * pObj, Ntk_Obj_t * pFanin );
extern void            Ntk_ObjDeleteFanin( Ntk_Obj_t * pObj, Ntk_Obj_t * pFanin );
extern void            Ntk_ObjPatchFanin( Ntk_Obj_t * pObj, Ntk_Obj_t * pFaninOld, Ntk_Obj_t * pFaninNew );
extern void            Ntk_ObjReplace( Ntk_Obj_t * pNodeOld, Ntk_Obj_t * pNodeNew );
/*=== ntkMan.c ============================================================*/
extern Ntk_Man_t *     Ntk_ManAlloc();
extern void            Ntk_ManFree( Ntk_Man_t * p );
extern void            Ntk_ManPrintStats( Ntk_Man_t * p, If_Lib_t * pLutLib );
/*=== ntkMap.c ============================================================*/
/*=== ntkObj.c ============================================================*/
extern Ntk_Obj_t *     Ntk_ManCreateCi( Ntk_Man_t * pMan, int nFanouts );
extern Ntk_Obj_t *     Ntk_ManCreateCo( Ntk_Man_t * pMan );
extern Ntk_Obj_t *     Ntk_ManCreateNode( Ntk_Man_t * pMan, int nFanins, int nFanouts );
extern Ntk_Obj_t *     Ntk_ManCreateBox( Ntk_Man_t * pMan, int nFanins, int nFanouts );
extern Ntk_Obj_t *     Ntk_ManCreateLatch( Ntk_Man_t * pMan );
extern void            Ntk_ManDeleteNode( Ntk_Obj_t * pObj );
extern void            Ntk_ManDeleteNode_rec( Ntk_Obj_t * pObj );
/*=== ntkTiming.c ============================================================*/
extern float           Ntk_ManDelayTraceLut( Ntk_Man_t * pNtk, If_Lib_t * pLutLib );
extern void            Ntk_ManDelayTracePrint( Ntk_Man_t * pNtk, If_Lib_t * pLutLib );
/*=== ntkUtil.c ============================================================*/
extern void            Ntk_ManIncrementTravId( Ntk_Man_t * pNtk );
extern int             Ntk_ManGetFaninMax( Ntk_Man_t * pNtk );
extern int             Ntk_ManGetTotalFanins( Ntk_Man_t * pNtk );
extern int             Ntk_ManPiNum( Ntk_Man_t * pNtk );
extern int             Ntk_ManPoNum( Ntk_Man_t * pNtk );
extern int             Ntk_ManGetAigNodeNum( Ntk_Man_t * pNtk );

#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

