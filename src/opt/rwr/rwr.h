/**CFile****************************************************************

  FileName    [rwr.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting package.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: rwr.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __RWR_H__
#define __RWR_H__

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////
 
#define RWR_LIMIT  1048576/4  // ((1 << 20) 

typedef struct Rwr_Node_t_  Rwr_Node_t;
struct Rwr_Node_t_ // 24 bytes
{
    int                Id;               // ID 
    int                TravId;           // traversal ID
    unsigned           uTruth : 16;      // truth table
    unsigned           Volume :  8;      // volume
    unsigned           Level  :  5;      // level
    unsigned           fMark  :  1;      // mark
    unsigned           fUsed  :  1;      // mark
    unsigned           fExor  :  1;      // mark
    Rwr_Node_t *       p0;               // first child
    Rwr_Node_t *       p1;               // second child
    Rwr_Node_t *       pNext;            // next in the table
};

typedef struct Rwr_Cut_t_  Rwr_Cut_t;
struct Rwr_Cut_t_ // 24 bytes
{
    unsigned           nLeaves : 3;      // the number of leaves
    unsigned           fTime  :  1;      // set to 1 if meets the required times
    unsigned           fGain  :  1;      // set to 1 if does not increase nodes
    unsigned           Volume : 11;      // the gain in the number of nodes
    unsigned           uTruth : 16;      // the truth table
    Abc_Obj_t *        ppLeaves[4];      // the leaves
    Rwr_Cut_t *        pNext;            // the next cut in the list
};

struct Abc_ManRwr_t_
{
    // internal lookups
    int                nFuncs;           // the number of four var functions
    unsigned short *   puCanons;         // canonical forms
    char *             puPhases;         // canonical phases
    char *             pPractical;       // practical classes
    unsigned short     puPerms[256][16]; // permutations for three var functions
    // node space
    Vec_Ptr_t *        vForest;          // all the nodes
    Rwr_Node_t **      pTable;           // the hash table of nodes by their canonical form
    Extra_MmFixed_t *  pMmNode;          // memory for nodes and cuts
    int                nTravIds;         // the counter of traversal IDs
    int                nConsidered;      // the number of nodes considered
    int                nAdded;           // the number of nodes added to lists
    int                nClasses;         // the number of NN classes
    // intermediate data
    Vec_Int_t *        vFanNums;         // the number of fanouts of each node (used to free cuts)
    Vec_Int_t *        vReqTimes;        // the required times for each node (used for delay-driven evalution)
    // the result of resynthesis
    Vec_Int_t *        vForm;            // the decomposition tree (temporary)
    Vec_Ptr_t *        vFanins;          // the fanins array (temporary)
    Vec_Ptr_t *        vTfo;             // the TFO node array (temporary)
    Vec_Vec_t *        vLevels;          // the levelized structure (temporary)
    int                nGainMax;
    // runtime statistics
    int                time1;
    int                time2;
    int                time3;
    int                time4;
};

// manipulation of complemented attributes
static inline bool         Rwr_IsComplement( Rwr_Node_t * p )    { return (bool)(((unsigned)p) & 01);           }
static inline Rwr_Node_t * Rwr_Regular( Rwr_Node_t * p )         { return (Rwr_Node_t *)((unsigned)(p) & ~01);  }
static inline Rwr_Node_t * Rwr_Not( Rwr_Node_t * p )             { return (Rwr_Node_t *)((unsigned)(p) ^  01);  }
static inline Rwr_Node_t * Rwr_NotCond( Rwr_Node_t * p, int c )  { return (Rwr_Node_t *)((unsigned)(p) ^ (c));  }

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFITIONS                             ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== rwrLib.c ==========================================================*/
extern void                Rwr_ManPrecompute( Abc_ManRwr_t * p );
extern void                Rwr_ManWriteToFile( Abc_ManRwr_t * p, char * pFileName );
extern void                Rwr_ManLoadFromFile( Abc_ManRwr_t * p, char * pFileName );
extern void                Rwr_ManPrint( Abc_ManRwr_t * p );
extern Rwr_Node_t *        Rwr_ManAddVar( Abc_ManRwr_t * p, unsigned uTruth );
/*=== rwrMan.c ==========================================================*/
extern unsigned short      Rwr_FunctionPhase( unsigned uTruth, unsigned uPhase );
/*=== rwrUtil.c ==========================================================*/
extern Vec_Int_t *         Rwt_NtkFanoutCounters( Abc_Ntk_t * pNtk );
extern Vec_Int_t *         Rwt_NtkRequiredLevels( Abc_Ntk_t * pNtk );

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

#endif

