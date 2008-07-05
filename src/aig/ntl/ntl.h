/**CFile****************************************************************

  FileName    [ntl.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntl.h,v 1.1 2008/05/14 22:13:09 wudenni Exp $]

***********************************************************************/
 
#ifndef __NTL_H__
#define __NTL_H__

#ifdef __cplusplus
extern "C" {
#endif

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "aig.h"
#include "tim.h"
#include "nwk.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Ntl_Man_t_    Ntl_Man_t;
typedef struct Ntl_Mod_t_    Ntl_Mod_t;
typedef struct Ntl_Reg_t_    Ntl_Reg_t;
typedef struct Ntl_Obj_t_    Ntl_Obj_t;
typedef struct Ntl_Net_t_    Ntl_Net_t;
typedef struct Ntl_Lut_t_    Ntl_Lut_t;

// object types
typedef enum { 
    NTL_OBJ_NONE,                      // 0: non-existent object
    NTL_OBJ_PI,                        // 1: primary input
    NTL_OBJ_PO,                        // 2: primary output
    NTL_OBJ_LATCH,                     // 3: latch 
    NTL_OBJ_NODE,                      // 4: logic node
    NTL_OBJ_LUT1,                      // 5: inverter/buffer
    NTL_OBJ_BOX,                       // 6: white box or black box
    NTL_OBJ_VOID                       // 7: unused object
} Ntl_Type_t;

struct Ntl_Man_t_
{
    // models of this design
    char *             pName;          // the name of this design
    char *             pSpec;          // the name of input file
    Vec_Ptr_t *        vModels;        // the array of all models used to represent boxes
    int                BoxTypes[15];   // the array of box types among the models
    // memory managers
    Aig_MmFlex_t *     pMemObjs;       // memory for objects
    Aig_MmFlex_t *     pMemSops;       // memory for SOPs
    // extracted representation
    Vec_Ptr_t *        vCis;           // the primary inputs of the extracted part
    Vec_Ptr_t *        vCos;           // the primary outputs of the extracted part 
    Vec_Ptr_t *        vVisNodes;      // the nodes of the abstracted part
    Vec_Int_t *        vBox1Cios;      // the first COs of the boxes
    Vec_Int_t *        vRegClasses;    // the classes of registers in the AIG
    Aig_Man_t *        pAig;           // the extracted AIG
    Tim_Man_t *        pManTime;       // the timing manager
    int                iLastCi;        // the last true CI
    // hashing names into models
    Ntl_Mod_t **       pModTable;      // the hash table of names into models
    int                nModTableSize;  // the allocated table size
    int                nModEntries;    // the number of entries in the hash table
};

struct Ntl_Mod_t_
{
    // model description
    Ntl_Man_t *        pMan;           // the model manager 
    char *             pName;          // the model name
    Vec_Ptr_t *        vObjs;          // the array of all objects
    Vec_Ptr_t *        vPis;           // the array of PI objects
    Vec_Ptr_t *        vPos;           // the array of PO objects
    int                nObjs[NTL_OBJ_VOID]; // counter of objects of each type
    // box attributes
    unsigned int       attrWhite   :1; // box has known logic
    unsigned int       attrBox     :1; // box is to remain unmapped
    unsigned int       attrComb    :1; // box is combinational
    unsigned int       attrKeep    :1; // box cannot be removed by structural sweep
    unsigned int       attrNoMerge :1; // box outputs cannot be merged
    // hashing names into nets
    Ntl_Net_t **       pTable;         // the hash table of names into nets
    int                nTableSize;     // the allocated table size
    int                nEntries;       // the number of entries in the hash table
    // delay information
    Vec_Int_t *        vDelays;
    Vec_Int_t *        vTimeInputs;
    Vec_Int_t *        vTimeOutputs;
    float *            pDelayTable;   
    // other data members
    Ntl_Mod_t *        pNext;
    void *             pCopy;
    int                nUsed, nRems;
}; 

struct Ntl_Reg_t_
{
    unsigned int       regInit   :  2; // register initial value
    unsigned int       regType   :  3; // register type
    unsigned int       regClass  : 28; // register class
};

struct Ntl_Obj_t_
{
    Ntl_Mod_t *        pModel;         // the model  
    void *             pCopy;          // the copy of this object
    unsigned           Type   :  3;    // object type
    unsigned           fMark  :  1;    // temporary mark  
    unsigned           Id     : 28;    // object ID
    int                nFanins;        // the number of fanins
    int                nFanouts;       // the number of fanouts
    union {                            // functionality
        Ntl_Mod_t *    pImplem;        // model (for boxes)
        char *         pSop;           // SOP (for logic nodes)
        Ntl_Reg_t      LatchId;        // init state + register class (for latches) 
    };
    union {                            // clock / other data
        Ntl_Net_t *    pClock;         // clock (for registers)
        void *         pTemp;          // other data 
    };
    Ntl_Net_t *        pFanio[0];      // fanins/fanouts
};

struct Ntl_Net_t_
{
    Ntl_Net_t *        pNext;          // next net in the hash table
    void *             pCopy;          // the copy of this object
    union {
        void *         pCopy2;         // the copy of this object
        int            iTemp;          // other data
        float          dTemp;          // other data
    };
    Ntl_Obj_t *        pDriver;        // driver of the net
    char               nVisits;        // the number of times the net is visited
    char               fMark;          // temporary mark
    char               pName[0];       // the name of this net
};

struct Ntl_Lut_t_
{
    int                Id;             // the ID of the root AIG node
    int                nFanins;        // the number of fanins
    int *              pFanins;        // the array of fanins
    unsigned *         pTruth;         // the truth table
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////
///                      INLINED FUNCTIONS                           ///
////////////////////////////////////////////////////////////////////////
#ifdef WIN32
#define DLLEXPORT __declspec(dllexport)
#define DLLIMPORT __declspec(dllimport)
#else  /* defined(WIN32) */
#define DLLIMPORT
#endif /* defined(WIN32) */

#ifndef ABC_DLL
#define ABC_DLL DLLIMPORT
#endif

static inline Ntl_Mod_t * Ntl_ManRootModel( Ntl_Man_t * p )       { return (Ntl_Mod_t *)Vec_PtrEntry( p->vModels, 0 );       } 

static inline int         Ntl_ModelPiNum( Ntl_Mod_t * p )         { return p->nObjs[NTL_OBJ_PI];                } 
static inline int         Ntl_ModelPoNum( Ntl_Mod_t * p )         { return p->nObjs[NTL_OBJ_PO];                } 
static inline int         Ntl_ModelNodeNum( Ntl_Mod_t * p )       { return p->nObjs[NTL_OBJ_NODE];              } 
static inline int         Ntl_ModelLut1Num( Ntl_Mod_t * p )       { return p->nObjs[NTL_OBJ_LUT1];              } 
static inline int         Ntl_ModelLatchNum( Ntl_Mod_t * p )      { return p->nObjs[NTL_OBJ_LATCH];             } 
static inline int         Ntl_ModelBoxNum( Ntl_Mod_t * p )        { return p->nObjs[NTL_OBJ_BOX];               } 

static inline Ntl_Obj_t * Ntl_ModelPi( Ntl_Mod_t * p, int i )     { return (Ntl_Obj_t *)Vec_PtrEntry(p->vPis, i);            } 
static inline Ntl_Obj_t * Ntl_ModelPo( Ntl_Mod_t * p, int i )     { return (Ntl_Obj_t *)Vec_PtrEntry(p->vPos, i);            } 

static inline char *      Ntl_ModelPiName( Ntl_Mod_t * p, int i ) { return Ntl_ModelPi(p, i)->pFanio[0]->pName; } 
static inline char *      Ntl_ModelPoName( Ntl_Mod_t * p, int i ) { return Ntl_ModelPo(p, i)->pFanio[0]->pName; } 

static inline int         Ntl_ObjFaninNum( Ntl_Obj_t * p )        { return p->nFanins;                          } 
static inline int         Ntl_ObjFanoutNum( Ntl_Obj_t * p )       { return p->nFanouts;                         } 

static inline int         Ntl_ObjIsPi( Ntl_Obj_t * p )            { return p->Type == NTL_OBJ_PI;               } 
static inline int         Ntl_ObjIsPo( Ntl_Obj_t * p )            { return p->Type == NTL_OBJ_PO;               } 
static inline int         Ntl_ObjIsNode( Ntl_Obj_t * p )          { return p->Type == NTL_OBJ_NODE;             } 
static inline int         Ntl_ObjIsLatch( Ntl_Obj_t * p )         { return p->Type == NTL_OBJ_LATCH;            } 
static inline int         Ntl_ObjIsBox( Ntl_Obj_t * p )           { return p->Type == NTL_OBJ_BOX;              } 

static inline Ntl_Net_t * Ntl_ObjFanin0( Ntl_Obj_t * p )          { return p->pFanio[0];                        } 
static inline Ntl_Net_t * Ntl_ObjFanout0( Ntl_Obj_t * p )         { return p->pFanio[p->nFanins];               } 

static inline Ntl_Net_t * Ntl_ObjFanin( Ntl_Obj_t * p, int i )    { return p->pFanio[i];                        } 
static inline Ntl_Net_t * Ntl_ObjFanout( Ntl_Obj_t * p, int i )   { return p->pFanio[p->nFanins+i];             } 

static inline void        Ntl_ObjSetFanin( Ntl_Obj_t * p, Ntl_Net_t * pNet, int i )    { p->pFanio[i] = pNet;   } 
static inline void        Ntl_ObjSetFanout( Ntl_Obj_t * p, Ntl_Net_t * pNet, int i )   { p->pFanio[p->nFanins+i] = pNet; pNet->pDriver = p; } 

static inline int         Ntl_ObjIsInit1( Ntl_Obj_t * p )         { assert( Ntl_ObjIsLatch(p) ); return p->LatchId.regInit == 1;   } 
static inline void        Ntl_ObjSetInit0( Ntl_Obj_t * p )        { assert( Ntl_ObjIsLatch(p) ); p->LatchId.regInit = 0;           } 

static inline int         Ntl_BoxIsWhite( Ntl_Obj_t * p )         { assert( Ntl_ObjIsBox(p) ); return p->pImplem->attrWhite;    } 
static inline int         Ntl_BoxIsBlack( Ntl_Obj_t * p )         { assert( Ntl_ObjIsBox(p) ); return !p->pImplem->attrWhite;   } 
static inline int         Ntl_BoxIsComb( Ntl_Obj_t * p )          { assert( Ntl_ObjIsBox(p) ); return p->pImplem->attrComb;     } 
static inline int         Ntl_BoxIsSeq( Ntl_Obj_t * p )           { assert( Ntl_ObjIsBox(p) ); return !p->pImplem->attrComb;    } 

static inline int         Ntl_ObjIsMapLeaf( Ntl_Obj_t * p )       { return Ntl_ObjIsPi(p) || (Ntl_ObjIsBox(p) && Ntl_BoxIsSeq(p));   } 
static inline int         Ntl_ObjIsMapRoot( Ntl_Obj_t * p )       { return Ntl_ObjIsPo(p) || (Ntl_ObjIsBox(p) && Ntl_BoxIsSeq(p));   } 

static inline int         Ntl_ObjIsCombLeaf( Ntl_Obj_t * p )      { return Ntl_ObjIsPi(p) || (Ntl_ObjIsBox(p) && (Ntl_BoxIsSeq(p) || Ntl_BoxIsBlack(p)));   } 
static inline int         Ntl_ObjIsCombRoot( Ntl_Obj_t * p )      { return Ntl_ObjIsPo(p) || (Ntl_ObjIsBox(p) && (Ntl_BoxIsSeq(p) || Ntl_BoxIsBlack(p)));   } 

static inline int         Ntl_ObjIsSeqLeaf( Ntl_Obj_t * p )       { return Ntl_ObjIsPi(p) || (Ntl_ObjIsBox(p) && Ntl_BoxIsBlack(p));   } 
static inline int         Ntl_ObjIsSeqRoot( Ntl_Obj_t * p )       { return Ntl_ObjIsPo(p) || (Ntl_ObjIsBox(p) && Ntl_BoxIsBlack(p));   } 

////////////////////////////////////////////////////////////////////////
///                         ITERATORS                                ///
////////////////////////////////////////////////////////////////////////

#define Ntl_ManForEachModel( p, pMod, i )                                       \
    for ( i = 0; (i < Vec_PtrSize(p->vModels)) && (((pMod) = (Ntl_Mod_t*)Vec_PtrEntry(p->vModels, i)), 1); i++ )
#define Ntl_ManForEachCiNet( p, pNet, i )                                       \
    Vec_PtrForEachEntry( p->vCis, pNet, i )
#define Ntl_ManForEachCoNet( p, pNet, i )                                       \
    Vec_PtrForEachEntry( p->vCos, pNet, i )

#define Ntl_ModelForEachPi( pNwk, pObj, i )                                     \
    for ( i = 0; (i < Vec_PtrSize(pNwk->vPis)) && (((pObj) = (Ntl_Obj_t*)Vec_PtrEntry(pNwk->vPis, i)), 1); i++ )
#define Ntl_ModelForEachPo( pNwk, pObj, i )                                     \
    for ( i = 0; (i < Vec_PtrSize(pNwk->vPos)) && (((pObj) = (Ntl_Obj_t*)Vec_PtrEntry(pNwk->vPos, i)), 1); i++ )
#define Ntl_ModelForEachNet( pNwk, pNet, i )                                    \
    for ( i = 0; i < pNwk->nTableSize; i++ )                                    \
        for ( pNet = pNwk->pTable[i]; pNet; pNet = pNet->pNext ) 
#define Ntl_ModelForEachObj( pNwk, pObj, i )                                    \
    for ( i = 0; (i < Vec_PtrSize(pNwk->vObjs)) && (((pObj) = (Ntl_Obj_t*)Vec_PtrEntry(pNwk->vObjs, i)), 1); i++ ) \
        if ( pObj == NULL ) {} else
#define Ntl_ModelForEachLatch( pNwk, pObj, i )                                  \
    for ( i = 0; (i < Vec_PtrSize(pNwk->vObjs)) && (((pObj) = (Ntl_Obj_t*)Vec_PtrEntry(pNwk->vObjs, i)), 1); i++ ) \
        if ( (pObj) == NULL || !Ntl_ObjIsLatch((Ntl_Obj_t*)pObj) ) {} else
#define Ntl_ModelForEachNode( pNwk, pObj, i )                                   \
    for ( i = 0; (i < Vec_PtrSize(pNwk->vObjs)) && (((pObj) = (Ntl_Obj_t*)Vec_PtrEntry(pNwk->vObjs, i)), 1); i++ ) \
        if ( (pObj) == NULL || !Ntl_ObjIsNode(pObj) ) {} else
#define Ntl_ModelForEachBox( pNwk, pObj, i )                                    \
    for ( i = 0; (i < Vec_PtrSize(pNwk->vObjs)) && (((pObj) = (Ntl_Obj_t*)Vec_PtrEntry(pNwk->vObjs, i)), 1); i++ ) \
        if ( (pObj) == NULL || !Ntl_ObjIsBox(pObj) ) {} else

#define Ntl_ObjForEachFanin( pObj, pFanin, i )                                  \
    for ( i = 0; (i < (pObj)->nFanins) && (((pFanin) = (pObj)->pFanio[i]), 1); i++ )
#define Ntl_ObjForEachFanout( pObj, pFanout, i )                                \
    for ( i = 0; (i < (pObj)->nFanouts) && (((pFanout) = (pObj)->pFanio[(pObj)->nFanins+i]), 1); i++ )

#define Ntl_ModelForEachMapLeaf( pNwk, pObj, i )                                \
    for ( i = 0; (i < Vec_PtrSize(pNwk->vObjs)) && (((pObj) = (Ntl_Obj_t*)Vec_PtrEntry(pNwk->vObjs, i)), 1); i++ ) \
        if ( (pObj) == NULL || !Ntl_ObjIsMapLeaf(pObj) ) {} else
#define Ntl_ModelForEachMapRoot( pNwk, pObj, i )                                \
    for ( i = 0; (i < Vec_PtrSize(pNwk->vObjs)) && (((pObj) = (Ntl_Obj_t*)Vec_PtrEntry(pNwk->vObjs, i)), 1); i++ ) \
        if ( (pObj) == NULL || !Ntl_ObjIsMapRoot(pObj) ) {} else
#define Ntl_ModelForEachCombLeaf( pNwk, pObj, i )                                \
    for ( i = 0; (i < Vec_PtrSize(pNwk->vObjs)) && (((pObj) = (Ntl_Obj_t*)Vec_PtrEntry(pNwk->vObjs, i)), 1); i++ ) \
        if ( (pObj) == NULL || !Ntl_ObjIsCombLeaf(pObj) ) {} else
#define Ntl_ModelForEachCombRoot( pNwk, pObj, i )                                \
    for ( i = 0; (i < Vec_PtrSize(pNwk->vObjs)) && (((pObj) = (Ntl_Obj_t*)Vec_PtrEntry(pNwk->vObjs, i)), 1); i++ ) \
        if ( (pObj) == NULL || !Ntl_ObjIsCombRoot(pObj) ) {} else
#define Ntl_ModelForEachSeqLeaf( pNwk, pObj, i )                                \
    for ( i = 0; (i < Vec_PtrSize(pNwk->vObjs)) && (((pObj) = (Ntl_Obj_t*)Vec_PtrEntry(pNwk->vObjs, i)), 1); i++ ) \
        if ( (pObj) == NULL || !Ntl_ObjIsSeqLeaf(pObj) ) {} else
#define Ntl_ModelForEachSeqRoot( pNwk, pObj, i )                                \
    for ( i = 0; (i < Vec_PtrSize(pNwk->vObjs)) && (((pObj) = (Ntl_Obj_t*)Vec_PtrEntry(pNwk->vObjs, i)), 1); i++ ) \
        if ( (pObj) == NULL || !Ntl_ObjIsSeqRoot(pObj) ) {} else

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== ntlCore.c ==========================================================*/
extern ABC_DLL int             Ntl_ManInsertTest( Ntl_Man_t * p, Aig_Man_t * pAig );
extern ABC_DLL int             Ntl_ManInsertTestIf( Ntl_Man_t * p, Aig_Man_t * pAig );
/*=== ntlEc.c ==========================================================*/
extern ABC_DLL void            Ntl_ManPrepareCecMans( Ntl_Man_t * pMan1, Ntl_Man_t * pMan2, Aig_Man_t ** ppAig1, Aig_Man_t ** ppAig2 );
extern ABC_DLL void            Ntl_ManPrepareCec( char * pFileName1, char * pFileName2, Aig_Man_t ** ppAig1, Aig_Man_t ** ppAig2 );
extern ABC_DLL Aig_Man_t *     Ntl_ManPrepareSec( char * pFileName1, char * pFileName2 );
/*=== ntlExtract.c ==========================================================*/
extern ABC_DLL Aig_Man_t *     Ntl_ManExtract( Ntl_Man_t * p );
extern ABC_DLL Aig_Man_t *     Ntl_ManCollapse( Ntl_Man_t * p, int fSeq );
extern ABC_DLL Aig_Man_t *     Ntl_ManCollapseComb( Ntl_Man_t * p );
extern ABC_DLL Aig_Man_t *     Ntl_ManCollapseSeq( Ntl_Man_t * p, int nMinDomSize );
/*=== ntlInsert.c ==========================================================*/
extern ABC_DLL Ntl_Man_t *     Ntl_ManInsertMapping( Ntl_Man_t * p, Vec_Ptr_t * vMapping, Aig_Man_t * pAig );
extern ABC_DLL Ntl_Man_t *     Ntl_ManInsertAig( Ntl_Man_t * p, Aig_Man_t * pAig );
extern ABC_DLL Ntl_Man_t *     Ntl_ManInsertNtk( Ntl_Man_t * p, Nwk_Man_t * pNtk );
/*=== ntlCheck.c ==========================================================*/
extern ABC_DLL int             Ntl_ManCheck( Ntl_Man_t * pMan );
extern ABC_DLL int             Ntl_ModelCheck( Ntl_Mod_t * pModel, int fMain );
extern ABC_DLL void            Ntl_ModelFixNonDrivenNets( Ntl_Mod_t * pModel );
extern ABC_DLL void            Ntl_ModelTransformLatches( Ntl_Mod_t * pModel );
/*=== ntlMan.c ============================================================*/
extern ABC_DLL Ntl_Man_t *     Ntl_ManAlloc();
extern ABC_DLL void            Ntl_ManCleanup( Ntl_Man_t * p );
extern ABC_DLL Ntl_Man_t *     Ntl_ManStartFrom( Ntl_Man_t * p );
extern ABC_DLL Ntl_Man_t *     Ntl_ManDup( Ntl_Man_t * p );
extern ABC_DLL void            Ntl_ManFree( Ntl_Man_t * p );
extern ABC_DLL Ntl_Mod_t *     Ntl_ManFindModel( Ntl_Man_t * p, char * pName );
extern ABC_DLL void            Ntl_ManPrintStats( Ntl_Man_t * p );
extern ABC_DLL Tim_Man_t *     Ntl_ManReadTimeMan( Ntl_Man_t * p );
extern ABC_DLL void            Ntl_ManPrintTypes( Ntl_Man_t * p );
extern ABC_DLL Ntl_Mod_t *     Ntl_ModelAlloc( Ntl_Man_t * pMan, char * pName );
extern ABC_DLL Ntl_Mod_t *     Ntl_ModelStartFrom( Ntl_Man_t * pManNew, Ntl_Mod_t * pModelOld );
extern ABC_DLL Ntl_Mod_t *     Ntl_ModelDup( Ntl_Man_t * pManNew, Ntl_Mod_t * pModelOld );
extern ABC_DLL void            Ntl_ModelFree( Ntl_Mod_t * p );
extern ABC_DLL Ntl_Mod_t *     Ntl_ManCreateLatchModel( Ntl_Man_t * pMan, int Init );
/*=== ntlMap.c ============================================================*/
extern ABC_DLL Vec_Ptr_t *     Ntl_MappingAlloc( int nLuts, int nVars );
extern ABC_DLL Vec_Ptr_t *     Ntl_MappingFromAig( Aig_Man_t * p );
extern ABC_DLL Vec_Ptr_t *     Ntl_MappingFpga( Aig_Man_t * p );
extern ABC_DLL Vec_Ptr_t *     Ntl_MappingIf( Ntl_Man_t * pMan, Aig_Man_t * p );
/*=== ntlObj.c ============================================================*/
extern ABC_DLL Ntl_Obj_t *     Ntl_ModelCreatePi( Ntl_Mod_t * pModel );
extern ABC_DLL Ntl_Obj_t *     Ntl_ModelCreatePo( Ntl_Mod_t * pModel, Ntl_Net_t * pNet );
extern ABC_DLL Ntl_Obj_t *     Ntl_ModelCreateLatch( Ntl_Mod_t * pModel );
extern ABC_DLL Ntl_Obj_t *     Ntl_ModelCreateNode( Ntl_Mod_t * pModel, int nFanins );
extern ABC_DLL Ntl_Obj_t *     Ntl_ModelCreateBox( Ntl_Mod_t * pModel, int nFanins, int nFanouts );
extern ABC_DLL Ntl_Obj_t *     Ntl_ModelDupObj( Ntl_Mod_t * pModel, Ntl_Obj_t * pOld );
extern ABC_DLL Ntl_Obj_t *     Ntl_ModelCreatePiWithName( Ntl_Mod_t * pModel, char * pName );
extern ABC_DLL char *          Ntl_ManStoreName( Ntl_Man_t * p, char * pName );
extern ABC_DLL char *          Ntl_ManStoreSop( Aig_MmFlex_t * pMan, char * pSop );
extern ABC_DLL char *          Ntl_ManStoreFileName( Ntl_Man_t * p, char * pFileName );
/*=== ntlSweep.c ==========================================================*/
extern ABC_DLL int             Ntl_ManSweep( Ntl_Man_t * p, int fVerbose );
/*=== ntlTable.c ==========================================================*/
extern ABC_DLL Ntl_Net_t *     Ntl_ModelFindNet( Ntl_Mod_t * p, char * pName );
extern ABC_DLL Ntl_Net_t *     Ntl_ModelFindOrCreateNet( Ntl_Mod_t * p, char * pName );
extern ABC_DLL int             Ntl_ModelFindPioNumber( Ntl_Mod_t * p, int fPiOnly, int fPoOnly, char * pName, int * pNumber );
extern ABC_DLL int             Ntl_ModelSetNetDriver( Ntl_Obj_t * pObj, Ntl_Net_t * pNet );
extern ABC_DLL int             Ntl_ModelClearNetDriver( Ntl_Obj_t * pObj, Ntl_Net_t * pNet );
extern ABC_DLL void            Ntl_ModelDeleteNet( Ntl_Mod_t * p, Ntl_Net_t * pNet );
extern ABC_DLL int             Ntl_ModelCountNets( Ntl_Mod_t * p );
extern ABC_DLL int             Ntl_ManAddModel( Ntl_Man_t * p, Ntl_Mod_t * pModel );
extern ABC_DLL Ntl_Mod_t *     Ntl_ManFindModel( Ntl_Man_t * p, char * pName );
/*=== ntlTime.c ==========================================================*/
extern ABC_DLL Tim_Man_t *     Ntl_ManCreateTiming( Ntl_Man_t * p );
/*=== ntlReadBlif.c ==========================================================*/
extern ABC_DLL Ntl_Man_t *     Ioa_ReadBlif( char * pFileName, int fCheck );
/*=== ntlWriteBlif.c ==========================================================*/
extern ABC_DLL void            Ioa_WriteBlif( Ntl_Man_t * p, char * pFileName );
extern ABC_DLL void            Ioa_WriteBlifLogic( Nwk_Man_t * pNtk, Ntl_Man_t * p, char * pFileName );
/*=== ntlUtil.c ==========================================================*/
extern ABC_DLL int             Ntl_ModelCountLut1( Ntl_Mod_t * pRoot );
extern ABC_DLL int             Ntl_ModelGetFaninMax( Ntl_Mod_t * pRoot );
extern ABC_DLL Ntl_Net_t *     Ntl_ModelFindSimpleNet( Ntl_Net_t * pNetCo );
extern ABC_DLL int             Ntl_ManCountSimpleCoDrivers( Ntl_Man_t * p );
extern ABC_DLL Vec_Ptr_t *     Ntl_ManCollectCiNames( Ntl_Man_t * p );
extern ABC_DLL Vec_Ptr_t *     Ntl_ManCollectCoNames( Ntl_Man_t * p );
extern ABC_DLL void            Ntl_ManMarkCiCoNets( Ntl_Man_t * p );
extern ABC_DLL void            Ntl_ManUnmarkCiCoNets( Ntl_Man_t * p );
extern ABC_DLL void            Ntl_ManSetZeroInitValues( Ntl_Man_t * p );
extern ABC_DLL void            Ntl_ManTransformInitValues( Ntl_Man_t * p );
extern ABC_DLL Vec_Vec_t *     Ntl_ManTransformRegClasses( Ntl_Man_t * pMan, int nSizeMax, int fVerbose );
extern ABC_DLL void            Ntl_ManFilterRegisterClasses( Aig_Man_t * pAig, Vec_Int_t * vRegClasses, int fVerbose );
extern ABC_DLL int             Ntl_ManLatchNum( Ntl_Man_t * p );
extern ABC_DLL int             Ntl_ManIsComb( Ntl_Man_t * p );
extern ABC_DLL int             Ntl_ModelCombLeafNum( Ntl_Mod_t * p );
extern ABC_DLL int             Ntl_ModelCombRootNum( Ntl_Mod_t * p );
extern ABC_DLL int             Ntl_ModelSeqLeafNum( Ntl_Mod_t * p );
extern ABC_DLL int             Ntl_ModelSeqRootNum( Ntl_Mod_t * p );
extern ABC_DLL int             Ntl_ModelCheckNetsAreNotMarked( Ntl_Mod_t * pModel );
extern ABC_DLL void            Ntl_ModelClearNets( Ntl_Mod_t * pModel );

#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

