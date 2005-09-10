/**CFile****************************************************************

  FileName    [cutInt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [K-feasible cut computation package.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cutInt.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef __CUT_INT_H__
#define __CUT_INT_H__

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include "extra.h"
#include "vec.h"
#include "cut.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Cut_HashTableStruct_t_ Cut_HashTable_t;

struct Cut_ManStruct_t_
{
    // user preferences
    Cut_Params_t *     pParams;          // computation parameters
    Vec_Int_t *        vFanCounts;       // the array of fanout counters
    // storage for cuts
    Vec_Ptr_t *        vCuts;            // cuts by ID
    Vec_Ptr_t *        vCutsNew;         // cuts by ID
    // memory management
    Extra_MmFixed_t *  pMmCuts;
    int                EntrySize;
    // temporary variables
    Cut_Cut_t *        pReady;
    Vec_Ptr_t *        vTemp;
    int                fCompl0;
    int                fCompl1;
    int                fSimul;
    int                nNodeCuts;
    // precomputations
    unsigned           uTruthVars[6][2];
    unsigned short **  pPerms43;
    unsigned **        pPerms53;
    unsigned **        pPerms54;
    // statistics
    int                nCutsCur;
    int                nCutsAlloc;
    int                nCutsDealloc;
    int                nCutsPeak;
    int                nCutsTriv;
    int                nCutsFilter;
    int                nCutsLimit;
    int                nNodes;
    // runtime
    int                timeMerge;
    int                timeUnion;
    int                timeTruth;
    int                timeFilter;
    int                timeHash;
};

// iterator through all the cuts of the list
#define Cut_ListForEachCut( pList, pCut )                 \
    for ( pCut = pList;                                   \
          pCut;                                           \
          pCut = pCut->pNext )
#define Cut_ListForEachCutStop( pList, pCut, pStop )      \
    for ( pCut = pList;                                   \
          pCut != pStop;                                  \
          pCut = pCut->pNext )
#define Cut_ListForEachCutSafe( pList, pCut, pCut2 )      \
    for ( pCut = pList,                                   \
          pCut2 = pCut? pCut->pNext: NULL;                \
          pCut;                                           \
          pCut = pCut2,                                   \
          pCut2 = pCut? pCut->pNext: NULL )

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFITIONS                             ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== cutCut.c ==========================================================*/
extern Cut_Cut_t *         Cut_CutAlloc( Cut_Man_t * p );
extern Cut_Cut_t *         Cut_CutCreateTriv( Cut_Man_t * p, int Node );
extern void                Cut_CutRecycle( Cut_Man_t * p, Cut_Cut_t * pCut );
extern void                Cut_CutPrint( Cut_Cut_t * pCut );
extern void                Cut_CutPrintMerge( Cut_Cut_t * pCut, Cut_Cut_t * pCut0, Cut_Cut_t * pCut1 );
/*=== cutMerge.c ==========================================================*/
extern Cut_Cut_t *         Cut_CutMergeTwo( Cut_Man_t * p, Cut_Cut_t * pCut0, Cut_Cut_t * pCut1 );
/*=== cutTable.c ==========================================================*/
extern Cut_HashTable_t *   Cut_TableStart( int Size );
extern void                Cut_TableStop( Cut_HashTable_t * pTable );
extern int                 Cut_TableLookup( Cut_HashTable_t * pTable, Cut_Cut_t * pCut, int fStore );
extern void                Cut_TableClear( Cut_HashTable_t * pTable );
extern int                 Cut_TableReadTime( Cut_HashTable_t * pTable );
/*=== cutTruth.c ==========================================================*/
extern void                Cut_TruthCompute( Cut_Man_t * p, Cut_Cut_t * pCut, Cut_Cut_t * pCut0, Cut_Cut_t * pCut1 );

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

#endif

