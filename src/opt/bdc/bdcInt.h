/**CFile****************************************************************

  FileName    [bdcInt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Truth-table-based bi-decomposition engine.]

  Synopsis    [Internal declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - January 15, 2007.]

  Revision    [$Id: resInt.h,v 1.00 2007/01/15 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __BDC_INT_H__
#define __BDC_INT_H__

#ifdef __cplusplus
extern "C" {
#endif

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "dec.h"
#include "bdc.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

// network types
typedef enum { 
    BDC_TYPE_NONE = 0,  // 0:  unknown
    BDC_TYPE_CONST1,    // 1:  constant 1
    BDC_TYPE_PI,        // 2:  primary input
    BDC_TYPE_AND,       // 4:  AND-gate
    BDC_TYPE_XOR,       // 5:  XOR-gate
    BDC_TYPE_MUX,       // 6:  MUX-gate
    BDC_TYPE_OTHER      // 7:  unused
} Bdc_Type_t;

typedef struct Bdc_Fun_t_ Bdc_Fun_t;
struct Bdc_Fun_t_
{
    int              Type;         // Const1, PI, AND, XOR, MUX
    Bdc_Fun_t *      pFan0;        // next function with same support
    Bdc_Fun_t *      pFan1;        // next function with same support
    Bdc_Fun_t *      pFan2;        // next function with same support
    unsigned         uSupp;        // bit mask of current support
    unsigned *       puFunc;       // the function of the node
    Bdc_Fun_t *      pNext;        // next function with same support
    void *           pCopy;        // the copy field
};

typedef struct Bdc_Isf_t_ Bdc_Isf_t;
struct Bdc_Isf_t_
{
    unsigned         uSupp;        // bit mask of current support
    unsigned         uUnique;      // bit mask of unique support
    unsigned *       puOn;         // on-set
    unsigned *       puOff;        // off-set
    int              Cost;         // cost of this component
};

typedef struct Bdc_Man_t_ Bdc_Man_t;
struct Bdc_Man_t_
{
    // external parameters
    Bdc_Par_t *      pPars;        // parameter set
    int              nVars;        // the number of variables
    int              nWords;       // the number of words 
    int              nNodeLimit;   // the limit on the number of new nodes
    // internal nodes
    Bdc_Fun_t *      pNodes;       // storage for decomposition nodes
    int              nNodes;       // the number of nodes used
    int              nNodesAlloc;  // the number of nodes allocated  
    Bdc_Fun_t *      pRoot;        // the root node
    // resub candidates
    Bdc_Fun_t **     pTable;       // hash table of candidates
    int              nTableSize;   // hash table size (1 << nVarsMax)
    // internal memory manager
    Vec_Int_t *      vMemory;      // memory for internal truth tables
    int              nMemStart;    // the starting memory size
};

// working with complemented attributes of objects
static inline bool        Bdc_IsComplement( Bdc_Fun_t * p )       { return (bool)((unsigned long)p & (unsigned long)01);             }
static inline Bdc_Fun_t * Bdc_Regular( Bdc_Fun_t * p )            { return (Bdc_Fun_t *)((unsigned long)p & ~(unsigned long)01);     }
static inline Bdc_Fun_t * Bdc_Not( Bdc_Fun_t * p )                { return (Bdc_Fun_t *)((unsigned long)p ^  (unsigned long)01);     }
static inline Bdc_Fun_t * Bdc_NotCond( Bdc_Fun_t * p, int c )     { return (Bdc_Fun_t *)((unsigned long)p ^  (unsigned long)(c!=0)); }

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== bdcSupp.c ==========================================================*/
extern int              Bdc_SuppMinimize( Bdc_Man_t * p, Bdc_Isf_t * pIsf );
/*=== bdcTable.c ==========================================================*/
extern Bdc_Fun_t *      Bdc_TableLookup( Bdc_Man_t * p, Bdc_Isf_t * pIsf );


#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

