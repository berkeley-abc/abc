/**CFile****************************************************************

  FileName    [nwk.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Logic network representation.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: nwk.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __NWK_H__
#define __NWK_H__

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
#include "bdc.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Nwk_Man_t_    Nwk_Man_t;
typedef struct Nwk_Obj_t_    Nwk_Obj_t;

// object types
typedef enum { 
    NWK_OBJ_NONE,                      // 0: non-existant object
    NWK_OBJ_CI,                        // 1: combinational input
    NWK_OBJ_CO,                        // 2: combinational output
    NWK_OBJ_NODE,                      // 3: logic node
    NWK_OBJ_LATCH,                     // 4: register
    NWK_OBJ_VOID                       // 5: unused object
} Nwk_Type_t;

struct Nwk_Man_t_
{
    // models of this design
    char *             pName;          // the name of this design
    char *             pSpec;          // the name of input file
    // node representation
    Vec_Ptr_t *        vCis;           // the primary inputs of the extracted part
    Vec_Ptr_t *        vCos;           // the primary outputs of the extracted part 
    Vec_Ptr_t *        vObjs;          // the objects in the topological order
    int                nObjs[NWK_OBJ_VOID]; // counter of objects of each type
    int                nFanioPlus;     // the number of extra fanins/fanouts alloc by default
    // functionality, timing, memory, etc
    Hop_Man_t *        pManHop;        // the functionality representation
    Tim_Man_t *        pManTime;       // the timing manager
    If_Lib_t *         pLutLib;        // the LUT library
    Aig_MmFlex_t *     pMemObjs;       // memory for objects
    Vec_Ptr_t *        vTemp;          // array used for incremental updates
    int                nTravIds;       // the counter of traversal IDs
    int                nRealloced;     // the number of realloced nodes
};

struct Nwk_Obj_t_
{
    Nwk_Man_t *        pMan;           // the manager  
    Hop_Obj_t *        pFunc;          // functionality
    void *             pCopy;          // temporary pointer
    void *             pNext;          // temporary pointer
    // node information
    unsigned           Type     :  3;  // object type
    unsigned           fCompl   :  1;  // complemented attribute
    unsigned           MarkA    :  1;  // temporary mark  
    unsigned           MarkB    :  1;  // temporary mark
    unsigned           PioId    : 26;  // number of this node in the PI/PO list
    int                Id;             // unique ID
    int                TravId;         // traversal ID
    // timing information
    int                Level;          // the topological level
    float              tArrival;       // the arrival time
    float              tRequired;      // the required time
    float              tSlack;         // the slack
    // fanin/fanout representation
    int                nFanins;        // the number of fanins
    int                nFanouts;       // the number of fanouts
    int                nFanioAlloc;    // the number of allocated fanins/fanouts
    Nwk_Obj_t **       pFanio;         // fanins/fanouts
};


////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////
///                      INLINED FUNCTIONS                           ///
////////////////////////////////////////////////////////////////////////

static inline int         Nwk_ManCiNum( Nwk_Man_t * p )           { return p->nObjs[NWK_OBJ_CI];                } 
static inline int         Nwk_ManCoNum( Nwk_Man_t * p )           { return p->nObjs[NWK_OBJ_CO];                } 
static inline int         Nwk_ManNodeNum( Nwk_Man_t * p )         { return p->nObjs[NWK_OBJ_NODE];              } 
static inline int         Nwk_ManLatchNum( Nwk_Man_t * p )        { return p->nObjs[NWK_OBJ_LATCH];             } 
static inline int         Nwk_ManObjNumMax( Nwk_Man_t * p )       { return Vec_PtrSize(p->vObjs);               }

static inline Nwk_Obj_t * Nwk_ManCi( Nwk_Man_t * p, int i )       { return Vec_PtrEntry( p->vCis, i );          } 
static inline Nwk_Obj_t * Nwk_ManCo( Nwk_Man_t * p, int i )       { return Vec_PtrEntry( p->vCos, i );          } 
static inline Nwk_Obj_t * Nwk_ManObj( Nwk_Man_t * p, int i )      { return Vec_PtrEntry( p->vObjs, i );         } 

static inline int         Nwk_ObjFaninNum( Nwk_Obj_t * p )        { return p->nFanins;                          } 
static inline int         Nwk_ObjFanoutNum( Nwk_Obj_t * p )       { return p->nFanouts;                         } 

static inline Nwk_Obj_t * Nwk_ObjFanin0( Nwk_Obj_t * p )          { return p->pFanio[0];                        } 
static inline Nwk_Obj_t * Nwk_ObjFanout0( Nwk_Obj_t * p )         { return p->pFanio[p->nFanins];               } 
static inline Nwk_Obj_t * Nwk_ObjFanin( Nwk_Obj_t * p, int i )    { return p->pFanio[i];                        } 
static inline Nwk_Obj_t * Nwk_ObjFanout( Nwk_Obj_t * p, int i )   { return p->pFanio[p->nFanins+1];             } 

static inline int         Nwk_ObjIsCi( Nwk_Obj_t * p )            { return p->Type == NWK_OBJ_CI;               } 
static inline int         Nwk_ObjIsCo( Nwk_Obj_t * p )            { return p->Type == NWK_OBJ_CO;               } 
static inline int         Nwk_ObjIsNode( Nwk_Obj_t * p )          { return p->Type == NWK_OBJ_NODE;             } 
static inline int         Nwk_ObjIsLatch( Nwk_Obj_t * p )         { return p->Type == NWK_OBJ_LATCH;            } 
static inline int         Nwk_ObjIsPi( Nwk_Obj_t * p )            { return Nwk_ObjIsCi(p) && (p->pMan->pManTime == NULL || Tim_ManBoxForCi(p->pMan->pManTime, p->PioId) == -1); } 
static inline int         Nwk_ObjIsPo( Nwk_Obj_t * p )            { return Nwk_ObjIsCo(p) && (p->pMan->pManTime == NULL || Tim_ManBoxForCo(p->pMan->pManTime, p->PioId) == -1);  }

static inline float       Nwk_ObjArrival( Nwk_Obj_t * pObj )                 { return pObj->tArrival;           }
static inline float       Nwk_ObjRequired( Nwk_Obj_t * pObj )                { return pObj->tRequired;          }
static inline float       Nwk_ObjSlack( Nwk_Obj_t * pObj )                   { return pObj->tSlack;             }
static inline void        Nwk_ObjSetArrival( Nwk_Obj_t * pObj, float Time )  { pObj->tArrival   = Time;         }
static inline void        Nwk_ObjSetRequired( Nwk_Obj_t * pObj, float Time ) { pObj->tRequired  = Time;         }
static inline void        Nwk_ObjSetSlack( Nwk_Obj_t * pObj, float Time )    { pObj->tSlack     = Time;         }

static inline int         Nwk_ObjLevel( Nwk_Obj_t * pObj )                   { return pObj->Level;              }
static inline void        Nwk_ObjSetLevel( Nwk_Obj_t * pObj, int Level )     { pObj->Level = Level;             }

static inline void        Nwk_ObjSetTravId( Nwk_Obj_t * pObj, int TravId )   { pObj->TravId = TravId;                           }
static inline void        Nwk_ObjSetTravIdCurrent( Nwk_Obj_t * pObj )        { pObj->TravId = pObj->pMan->nTravIds;             }
static inline void        Nwk_ObjSetTravIdPrevious( Nwk_Obj_t * pObj )       { pObj->TravId = pObj->pMan->nTravIds - 1;         }
static inline int         Nwk_ObjIsTravIdCurrent( Nwk_Obj_t * pObj )         { return pObj->TravId == pObj->pMan->nTravIds;     }
static inline int         Nwk_ObjIsTravIdPrevious( Nwk_Obj_t * pObj )        { return pObj->TravId == pObj->pMan->nTravIds - 1; }

////////////////////////////////////////////////////////////////////////
///                         ITERATORS                                ///
////////////////////////////////////////////////////////////////////////

#define Nwk_ManForEachCi( p, pObj, i )                                     \
    Vec_PtrForEachEntry( p->vCis, pObj, i )
#define Nwk_ManForEachCo( p, pObj, i )                                     \
    Vec_PtrForEachEntry( p->vCos, pObj, i )
#define Nwk_ManForEachPi( p, pObj, i )                                     \
    Vec_PtrForEachEntry( p->vCis, pObj, i )                                \
        if ( !Nwk_ObjIsPi(pObj) ) {} else
#define Nwk_ManForEachPo( p, pObj, i )                                     \
    Vec_PtrForEachEntry( p->vCos, pObj, i )                                \
        if ( !Nwk_ObjIsPo(pObj) ) {} else
#define Nwk_ManForEachObj( p, pObj, i )                                    \
    for ( i = 0; (i < Vec_PtrSize(p->vObjs)) && (((pObj) = Vec_PtrEntry(p->vObjs, i)), 1); i++ ) \
        if ( pObj == NULL ) {} else
#define Nwk_ManForEachNode( p, pObj, i )                                   \
    for ( i = 0; (i < Vec_PtrSize(p->vObjs)) && (((pObj) = Vec_PtrEntry(p->vObjs, i)), 1); i++ ) \
        if ( (pObj) == NULL || !Nwk_ObjIsNode(pObj) ) {} else
#define Nwk_ManForEachLatch( p, pObj, i )                                  \
    for ( i = 0; (i < Vec_PtrSize(p->vObjs)) && (((pObj) = Vec_PtrEntry(p->vObjs, i)), 1); i++ ) \
        if ( (pObj) == NULL || !Nwk_ObjIsLatch(pObj) ) {} else

#define Nwk_ObjForEachFanin( pObj, pFanin, i )                                  \
    for ( i = 0; (i < (int)(pObj)->nFanins) && ((pFanin) = (pObj)->pFanio[i]); i++ )
#define Nwk_ObjForEachFanout( pObj, pFanout, i )                                \
    for ( i = 0; (i < (int)(pObj)->nFanouts) && ((pFanout) = (pObj)->pFanio[(pObj)->nFanins+i]); i++ )

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== nwkBidec.c ==========================================================*/
extern void            Nwk_ManBidecResyn( Nwk_Man_t * pNtk, int fVerbose );
extern Hop_Obj_t *     Nwk_NodeIfNodeResyn( Bdc_Man_t * p, Hop_Man_t * pHop, Hop_Obj_t * pRoot, int nVars, Vec_Int_t * vTruth, unsigned * puCare );
/*=== nwkDfs.c ==========================================================*/
extern int             Nwk_ManLevel( Nwk_Man_t * pNtk );
extern int             Nwk_ManLevel2( Nwk_Man_t * pNtk );
extern Vec_Vec_t *     Nwk_ManLevelize( Nwk_Man_t * pNtk );
extern Vec_Ptr_t *     Nwk_ManDfs( Nwk_Man_t * pNtk );
extern Vec_Ptr_t *     Nwk_ManDfsNodes( Nwk_Man_t * pNtk, Nwk_Obj_t ** ppNodes, int nNodes );
extern Vec_Ptr_t *     Nwk_ManDfsReverse( Nwk_Man_t * pNtk );
extern Vec_Ptr_t *     Nwk_ManSupportNodes( Nwk_Man_t * pNtk, Nwk_Obj_t ** ppNodes, int nNodes );
extern void            Nwk_ManSupportSum( Nwk_Man_t * pNtk );
extern int             Nwk_ObjMffcLabel( Nwk_Obj_t * pNode );
/*=== nwkFanio.c ==========================================================*/
extern void            Nwk_ObjCollectFanins( Nwk_Obj_t * pNode, Vec_Ptr_t * vNodes );
extern void            Nwk_ObjCollectFanouts( Nwk_Obj_t * pNode, Vec_Ptr_t * vNodes );
extern void            Nwk_ObjAddFanin( Nwk_Obj_t * pObj, Nwk_Obj_t * pFanin );
extern void            Nwk_ObjDeleteFanin( Nwk_Obj_t * pObj, Nwk_Obj_t * pFanin );
extern void            Nwk_ObjPatchFanin( Nwk_Obj_t * pObj, Nwk_Obj_t * pFaninOld, Nwk_Obj_t * pFaninNew );
extern void            Nwk_ObjReplace( Nwk_Obj_t * pNodeOld, Nwk_Obj_t * pNodeNew );
/*=== nwkMan.c ============================================================*/
extern Nwk_Man_t *     Nwk_ManAlloc();
extern void            Nwk_ManFree( Nwk_Man_t * p );
extern void            Nwk_ManPrintStats( Nwk_Man_t * p, If_Lib_t * pLutLib );
/*=== nwkMap.c ============================================================*/
extern Nwk_Man_t *     Nwk_MappingIf( Aig_Man_t * p, Tim_Man_t * pManTime, If_Par_t * pPars );
/*=== nwkObj.c ============================================================*/
extern Nwk_Obj_t *     Nwk_ManCreateCi( Nwk_Man_t * pMan, int nFanouts );
extern Nwk_Obj_t *     Nwk_ManCreateCo( Nwk_Man_t * pMan );
extern Nwk_Obj_t *     Nwk_ManCreateNode( Nwk_Man_t * pMan, int nFanins, int nFanouts );
extern Nwk_Obj_t *     Nwk_ManCreateBox( Nwk_Man_t * pMan, int nFanins, int nFanouts );
extern Nwk_Obj_t *     Nwk_ManCreateLatch( Nwk_Man_t * pMan );
extern void            Nwk_ManDeleteNode( Nwk_Obj_t * pObj );
extern void            Nwk_ManDeleteNode_rec( Nwk_Obj_t * pObj );
/*=== nwkTiming.c ============================================================*/
extern float           Nwk_ManDelayTraceLut( Nwk_Man_t * pNtk, If_Lib_t * pLutLib );
extern void            Nwk_ManDelayTracePrint( Nwk_Man_t * pNtk, If_Lib_t * pLutLib );
extern void            Nwk_ManUpdate( Nwk_Obj_t * pObj, Nwk_Obj_t * pObjNew, Vec_Vec_t * vLevels );
extern void            Nwk_ManVerifyLevel( Nwk_Man_t * pNtk );
/*=== nwkUtil.c ============================================================*/
extern void            Nwk_ManIncrementTravId( Nwk_Man_t * pNtk );
extern int             Nwk_ManGetFaninMax( Nwk_Man_t * pNtk );
extern int             Nwk_ManGetTotalFanins( Nwk_Man_t * pNtk );
extern int             Nwk_ManPiNum( Nwk_Man_t * pNtk );
extern int             Nwk_ManPoNum( Nwk_Man_t * pNtk );
extern int             Nwk_ManGetAigNodeNum( Nwk_Man_t * pNtk );
extern int             Nwk_NodeCompareLevelsIncrease( Nwk_Obj_t ** pp1, Nwk_Obj_t ** pp2 );
extern int             Nwk_NodeCompareLevelsDecrease( Nwk_Obj_t ** pp1, Nwk_Obj_t ** pp2 );

#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

