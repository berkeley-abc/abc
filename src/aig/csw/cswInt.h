/**CFile****************************************************************

  FileName    [cswInt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Cut sweeping.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - July 11, 2007.]

  Revision    [$Id: cswInt.h,v 1.00 2007/07/11 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __CSW_INT_H__
#define __CSW_INT_H__

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

#include "dar.h"
#include "kit.h"
#include "csw.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Csw_Man_t_            Csw_Man_t;
typedef struct Csw_Cut_t_            Csw_Cut_t;

// the cut used to represent node in the AIG
struct Csw_Cut_t_
{
    Csw_Cut_t *     pNext;           // the next cut in the table 
    int             Cost;            // the cost of the cut
    unsigned        uSign;           // cut signature
    int             iNode;           // the node, for which it is the cut
    int             nFanins;         // the number of words in truth table
    int             pFanins[0];      // the fanins (followed by the truth table)
};

// the CNF computation manager
struct Csw_Man_t_
{
    // AIG manager
    Dar_Man_t *     pManAig;         // the input AIG manager
    Dar_Man_t *     pManRes;         // the output AIG manager
    Dar_Obj_t **    pEquiv;          // the equivalent nodes in the resulting manager
    Csw_Cut_t **    pCuts;           // the cuts for each node in the output manager
    // hash table for cuts
    Csw_Cut_t **    pTable;          // the table composed of cuts 
    int             nTableSize;      // the size of hash table
    // parameters
    int             nCutsMax;        // the max number of cuts at the node
    int             nLeafMax;        // the max number of leaves of a cut
    int             fVerbose;        // enables verbose output
    // internal variables
    int             nCutSize;        // the number of bytes needed to store one cut
    int             nTruthWords;     // the number of truth table words
    Dar_MmFixed_t * pMemCuts;        // memory manager for cuts
    unsigned *      puTemp[4];       // used for the truth table computation
};

static inline unsigned     Csw_ObjCutSign( unsigned ObjId )                 { return (1 << (ObjId % 31));                         }

static inline int          Csw_CutLeaveNum( Csw_Cut_t * pCut )              { return pCut->nFanins;                               }
static inline int *        Csw_CutLeaves( Csw_Cut_t * pCut )                { return pCut->pFanins;                               }
static inline unsigned *   Csw_CutTruth( Csw_Cut_t * pCut )                 { return (unsigned *)(pCut->pFanins + pCut->nFanins); }
static inline Csw_Cut_t *  Csw_CutNext( Csw_Man_t * p, Csw_Cut_t * pCut )   { return (Csw_Cut_t *)(((char *)pCut) + p->nCutSize); }

static inline Csw_Cut_t *  Csw_ObjCuts( Csw_Man_t * p, Dar_Obj_t * pObj )                         { return p->pCuts[pObj->Id];    }
static inline void         Csw_ObjSetCuts( Csw_Man_t * p, Dar_Obj_t * pObj, Csw_Cut_t * pCuts )   { p->pCuts[pObj->Id] = pCuts;   }

static inline Dar_Obj_t *  Csw_ObjEquiv( Csw_Man_t * p, Dar_Obj_t * pObj )                        { return p->pEquiv[pObj->Id];   }
static inline void         Csw_ObjSetEquiv( Csw_Man_t * p, Dar_Obj_t * pObj, Dar_Obj_t * pEquiv ) { p->pEquiv[pObj->Id] = pEquiv; }

static inline Dar_Obj_t *  Csw_ObjChild0Equiv( Csw_Man_t * p, Dar_Obj_t * pObj ) { assert( !Dar_IsComplement(pObj) ); return Dar_ObjFanin0(pObj)? Dar_NotCond(Csw_ObjEquiv(p, Dar_ObjFanin0(pObj)), Dar_ObjFaninC0(pObj)) : NULL;  }
static inline Dar_Obj_t *  Csw_ObjChild1Equiv( Csw_Man_t * p, Dar_Obj_t * pObj ) { assert( !Dar_IsComplement(pObj) ); return Dar_ObjFanin1(pObj)? Dar_NotCond(Csw_ObjEquiv(p, Dar_ObjFanin1(pObj)), Dar_ObjFaninC1(pObj)) : NULL;  }

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                           ITERATORS                              ///
////////////////////////////////////////////////////////////////////////

// iterator over cuts of the node
#define Csw_ObjForEachCut( p, pObj, pCut, i )                           \
    for ( i = 0, pCut = Csw_ObjCuts(p, pObj); i < p->nCutsMax; i++, pCut = Csw_CutNext(p, pCut) ) 
// iterator over leaves of the cut
#define Csw_CutForEachLeaf( p, pCut, pLeaf, i )                         \
    for ( i = 0; (i < (int)(pCut)->nFanins) && ((pLeaf) = Dar_ManObj(p, (pCut)->pFanins[i])); i++ )

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== cnfCut.c ========================================================*/
extern Csw_Cut_t *    Csw_ObjPrepareCuts( Csw_Man_t * p, Dar_Obj_t * pObj, int fTriv );
extern Dar_Obj_t *    Csw_ObjSweep( Csw_Man_t * p, Dar_Obj_t * pObj, int fTriv );
/*=== cnfMan.c ========================================================*/
extern Csw_Man_t *    Csw_ManStart( Dar_Man_t * pMan, int nCutsMax, int nLeafMax, int fVerbose );
extern void           Csw_ManStop( Csw_Man_t * p );
/*=== cnfTable.c ========================================================*/
extern void           Csw_TableCutInsert( Csw_Man_t * p, Csw_Cut_t * pCut );
extern Dar_Obj_t *    Csw_TableCutLookup( Csw_Man_t * p, Csw_Cut_t * pCut );
extern unsigned int   Cudd_PrimeCws( unsigned int p );

#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

