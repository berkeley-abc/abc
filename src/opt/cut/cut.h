/**CFile****************************************************************

  FileName    [cut.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [K-feasible cut computation package.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: .h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef __CUT_H__
#define __CUT_H__

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Cut_ManStruct_t_         Cut_Man_t;
typedef struct Cut_CutStruct_t_         Cut_Cut_t;
typedef struct Cut_ParamsStruct_t_      Cut_Params_t;

struct Cut_ParamsStruct_t_
{
    int  nVarsMax;      // the max cut size ("k" of the k-feasible cuts)
    int  nKeepMax;      // the max number of cuts kept at a node
    int  nIdsMax;       // the max number of IDs of cut objects
    int  fTruth;        // compute truth tables
    int  fHash;         // hash cuts to detect unique
    int  fFilter;       // filter dominated cuts
    int  fSeq;          // compute sequential cuts
    int  fDrop;         // drop cuts on the fly
    int  fVerbose;      // the verbosiness flag
};

struct Cut_CutStruct_t_
{
    unsigned           uTruth     : 16;   // truth table for 4-input cuts
    unsigned           uPhase     :  7;   // the phase when mapping into a canonical form
    unsigned           fSimul     :  1;   // the value of cut's output at 000.. pattern
    unsigned           fCompl     :  1;   // the cut is complemented
    unsigned           fSeq       :  1;   // the cut is sequential
    unsigned           nVarsMax   :  3;   // the max number of vars [4-6]
    unsigned           nLeaves    :  3;   // the number of leaves [4-6]
    Cut_Cut_t *        pNext;             // the next cut in the list
    void *             pData;             // the user data
    int                pLeaves[0];        // the array of leaves
};

static inline unsigned * Cut_CutReadTruth( Cut_Cut_t * p )     {  if ( p->nVarsMax == 4 )  return (unsigned *)p;  return (unsigned *)(p->pLeaves + p->nVarsMax + p->fSeq); }
static inline unsigned   Cut_CutReadPhase( Cut_Cut_t * p )     {  return p->uPhase;    }
static inline int        Cut_CutReadLeaveNum( Cut_Cut_t * p )  {  return p->nLeaves;   }
static inline int *      Cut_CutReadLeaves( Cut_Cut_t * p )    {  return p->pLeaves;   }
static inline void *     Cut_CutReadData( Cut_Cut_t * p )      {  return p->pData;     }

static inline void       Cut_CutWriteData( Cut_Cut_t * p, void * pData )  { p->pData = pData;  }
static inline void       Cut_CutWriteTruth( Cut_Cut_t * p, unsigned * puTruth )  { 
    if ( p->nVarsMax == 4 )  { p->uTruth = *puTruth;  return; }
    p->pLeaves[p->nVarsMax + p->fSeq] = (int)puTruth[0];
    if ( p->nVarsMax == 6 )  p->pLeaves[p->nVarsMax + p->fSeq + 1] = (int)puTruth[1];
}

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFITIONS                             ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== cutMan.c ==========================================================*/
extern Cut_Man_t *      Cut_ManStart( Cut_Params_t * pParams );
extern void             Cut_ManStop( Cut_Man_t * p );
extern void             Cut_ManPrintStats( Cut_Man_t * p );
extern void             Cut_ManSetFanoutCounts( Cut_Man_t * p, Vec_Int_t * vFanCounts );
/*=== cutNode.c ==========================================================*/
extern void             Cut_NodeSetTriv( Cut_Man_t * p, int Node );
extern Cut_Cut_t *      Cut_NodeComputeCuts( Cut_Man_t * p, int Node, int Node0, int Node1, int fCompl0, int fCompl1 ); 
extern Cut_Cut_t *      Cut_NodeUnionCuts( Cut_Man_t * p, Vec_Int_t * vNodes );
extern Cut_Cut_t *      Cut_NodeReadCuts( Cut_Man_t * p, int Node ); 
extern void             Cut_NodeWriteCuts( Cut_Man_t * p, int Node, Cut_Cut_t * pList );
extern void             Cut_NodeFreeCuts( Cut_Man_t * p, int Node );
extern void             Cut_NodeSetComputedAsNew( Cut_Man_t * p, int Node );
extern void             Cut_NodeTryDroppingCuts( Cut_Man_t * p, int Node );
extern void             Cut_CutPrint( Cut_Cut_t * pCut );

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

#endif

