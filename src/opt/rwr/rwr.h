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

typedef struct Rwr_Man_t_   Rwr_Man_t;
typedef struct Rwr_Node_t_  Rwr_Node_t;
typedef struct Rwr_Cut_t_   Rwr_Cut_t;

struct Rwr_Man_t_
{
    // internal lookups
    int                nFuncs;           // number of four var functions
    unsigned short *   puCanons;         // canonical forms
    char *             pPhases;          // canonical phases
    char *             pPerms;           // canonical permutations
    unsigned char *    pMap;             // mapping of functions into class numbers
    char *             pPractical;       // practical NPN classes
    unsigned short **  puPerms43;        // four-var permutations for three var functions
    // node space
    Vec_Ptr_t *        vForest;          // all the nodes
    Rwr_Node_t **      pTable;           // the hash table of nodes by their canonical form
    Vec_Vec_t *        vClasses;         // the nodes of the equivalence classes
    Extra_MmFixed_t *  pMmNode;          // memory for nodes and cuts
    // statistical variables
    int                nTravIds;         // the counter of traversal IDs
    int                nConsidered;      // the number of nodes considered
    int                nAdded;           // the number of nodes added to lists
    int                nClasses;         // the number of NN classes
    // intermediate data
    Vec_Int_t *        vFanNums;         // the number of fanouts of each node (used to free cuts)
    Vec_Int_t *        vReqTimes;        // the required times for each node (used for delay-driven evalution)
    // the result of resynthesis
    Vec_Int_t *        vForm;            // the decomposition tree (temporary)
    Vec_Int_t *        vLevNums;         // the array of levels (temporary)
    Vec_Ptr_t *        vFanins;          // the fanins array (temporary)
    int                nGainMax;
    // runtime statistics
    int                time1;
    int                time2;
    int                time3;
    int                time4;
};

struct Rwr_Node_t_ // 24 bytes
{
    int                Id;               // ID 
    int                TravId;           // traversal ID
    unsigned           uTruth : 16;      // truth table
    unsigned           Volume :  8;      // volume
    unsigned           Level  :  6;      // level
    unsigned           fUsed  :  1;      // mark
    unsigned           fExor  :  1;      // mark
    Rwr_Node_t *       p0;               // first child
    Rwr_Node_t *       p1;               // second child
    Rwr_Node_t *       pNext;            // next in the table
};

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

/*=== rwrCut.c ========================================================*/
extern void              Rwr_NtkStartCuts( Rwr_Man_t * p, Abc_Ntk_t * pNtk );
extern void              Rwr_NodeComputeCuts( Rwr_Man_t * p, Abc_Obj_t * pNode );
/*=== rwrEva.c ========================================================*/
extern int               Rwr_NodeRewrite( Rwr_Man_t * p, Abc_Obj_t * pNode );
extern void              Rwr_ManPreprocess( Rwr_Man_t * p );
/*=== rwrLib.c ========================================================*/
extern void              Rwr_ManPrecompute( Rwr_Man_t * p );
extern Rwr_Node_t *      Rwr_ManAddVar( Rwr_Man_t * p, unsigned uTruth, int fPrecompute );
extern Rwr_Node_t *      Rwr_ManAddNode( Rwr_Man_t * p, Rwr_Node_t * p0, Rwr_Node_t * p1, int fExor, int Level, int Volume );
extern int               Rwr_ManNodeVolume( Rwr_Man_t * p, Rwr_Node_t * p0, Rwr_Node_t * p1 );
extern void              Rwr_ManIncTravId( Rwr_Man_t * p );
/*=== rwrMan.c ========================================================*/
extern Rwr_Man_t *       Rwr_ManStart( bool fPrecompute );
extern void              Rwr_ManStop( Rwr_Man_t * p );
extern void              Rwr_ManPrepareNetwork( Rwr_Man_t * p, Abc_Ntk_t * pNtk );
extern Vec_Ptr_t *       Rwr_ManReadFanins( Rwr_Man_t * p );
extern Vec_Int_t *       Rwr_ManReadDecs( Rwr_Man_t * p );
/*=== rwrPrint.c ========================================================*/
extern void              Rwr_ManPrint( Rwr_Man_t * p );
/*=== rwrUtil.c ========================================================*/
extern void              Rwr_ManWriteToArray( Rwr_Man_t * p );
extern void              Rwr_ManLoadFromArray( Rwr_Man_t * p );
extern void              Rwr_ManWriteToFile( Rwr_Man_t * p, char * pFileName );
extern void              Rwr_ManLoadFromFile( Rwr_Man_t * p, char * pFileName );
extern Vec_Int_t *       Rwt_NtkFanoutCounters( Abc_Ntk_t * pNtk );
extern void              Rwr_ListAddToTail( Rwr_Node_t ** ppList, Rwr_Node_t * pNode );
extern char *            Rwr_ManGetPractical( Rwr_Man_t * p );

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

#endif

