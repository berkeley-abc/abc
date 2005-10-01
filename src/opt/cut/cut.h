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
    int  nCutSet;       // the number of nodes in the cut set
    int  fTruth;        // compute truth tables
    int  fFilter;       // filter dominated cuts
    int  fSeq;          // compute sequential cuts
    int  fDrop;         // drop cuts on the fly
    int  fMulti;        // compute cuts in multi-input AND gate graph
    int  fVerbose;      // the verbosiness flag
};

struct Cut_CutStruct_t_
{
    unsigned           uTruth     : 16;   // truth table for 4-input cuts
    unsigned           uPhase     :  6;   // the phase when mapping into a canonical form
    unsigned           fSimul     :  1;   // the value of cut's output at 000.. pattern
    unsigned           fCompl     :  1;   // the cut is complemented
    unsigned           nVarsMax   :  4;   // the max number of vars [4-6]
    unsigned           nLeaves    :  4;   // the number of leaves [4-6]
    unsigned           uSign;             // the signature
    Cut_Cut_t *        pNext;             // the next cut in the list
    int                pLeaves[0];        // the array of leaves
};

static inline unsigned * Cut_CutReadTruth( Cut_Cut_t * p )     {  if ( p->nVarsMax == 4 )  return (unsigned *)p;  return (unsigned *)(p->pLeaves + p->nVarsMax); }
static inline unsigned   Cut_CutReadPhase( Cut_Cut_t * p )     {  return p->uPhase;    }
static inline int        Cut_CutReadLeaveNum( Cut_Cut_t * p )  {  return p->nLeaves;   }
static inline int *      Cut_CutReadLeaves( Cut_Cut_t * p )    {  return p->pLeaves;   }

static inline void       Cut_CutWriteTruth( Cut_Cut_t * p, unsigned * puTruth )  { 
    if ( p->nVarsMax == 4 )  { p->uTruth = *puTruth;  return; }
    p->pLeaves[p->nVarsMax] = (int)puTruth[0];
    if ( p->nVarsMax == 6 )  p->pLeaves[p->nVarsMax + 1] = (int)puTruth[1];
}

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFITIONS                             ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== cutApi.c ==========================================================*/
extern Cut_Cut_t *      Cut_NodeReadCutsNew( Cut_Man_t * p, int Node );
extern Cut_Cut_t *      Cut_NodeReadCutsOld( Cut_Man_t * p, int Node );
extern Cut_Cut_t *      Cut_NodeReadCutsTemp( Cut_Man_t * p, int Node );
extern void             Cut_NodeWriteCutsNew( Cut_Man_t * p, int Node, Cut_Cut_t * pList );
extern void             Cut_NodeWriteCutsOld( Cut_Man_t * p, int Node, Cut_Cut_t * pList );
extern void             Cut_NodeWriteCutsTemp( Cut_Man_t * p, int Node, Cut_Cut_t * pList );
extern void             Cut_NodeSetTriv( Cut_Man_t * p, int Node );
extern void             Cut_NodeTryDroppingCuts( Cut_Man_t * p, int Node );
extern void             Cut_NodeFreeCuts( Cut_Man_t * p, int Node );
/*=== cutCut.c ==========================================================*/
extern void             Cut_CutPrint( Cut_Cut_t * pCut, int fSeq );
extern void             Cut_CutPrintList( Cut_Cut_t * pList, int fSeq );
/*=== cutMan.c ==========================================================*/
extern Cut_Man_t *      Cut_ManStart( Cut_Params_t * pParams );
extern void             Cut_ManStop( Cut_Man_t * p );
extern void             Cut_ManPrintStats( Cut_Man_t * p );
extern void             Cut_ManPrintStatsToFile( Cut_Man_t * p, char * pFileName, int TimeTotal );
extern void             Cut_ManSetFanoutCounts( Cut_Man_t * p, Vec_Int_t * vFanCounts );
extern int              Cut_ManReadVarsMax( Cut_Man_t * p );
/*=== cutNode.c ==========================================================*/
extern Cut_Cut_t *      Cut_NodeComputeCuts( Cut_Man_t * p, int Node, int Node0, int Node1, int fCompl0, int fCompl1, int fNew0, int fNew1, int fTriv ); 
extern Cut_Cut_t *      Cut_NodeDoComputeCuts( Cut_Man_t * p, int Node, int Node0, int Node1, int fCompl0, int fCompl1, int fNew0, int fNew1, int fTriv ); 
extern Cut_Cut_t *      Cut_NodeUnionCuts( Cut_Man_t * p, Vec_Int_t * vNodes );
/*=== cutSeq.c ==========================================================*/
extern void             Cut_NodeComputeCutsSeq( Cut_Man_t * p, int Node, int Node0, int Node1, int fCompl0, int fCompl1, int nLat0, int nLat1, int fTriv, int CutSetNum );
extern void             Cut_NodeNewMergeWithOld( Cut_Man_t * p, int Node );
extern int              Cut_NodeTempTransferToNew( Cut_Man_t * p, int Node, int CutSetNum );
extern void             Cut_NodeOldTransferToNew( Cut_Man_t * p, int Node );

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

#endif

