/**CFile****************************************************************

  FileName    [pgaInt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapper.]

  Synopsis    [Internal declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: pgaInt.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef __PGA_INT_H__
#define __PGA_INT_H__

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include "abc.h"
#include "fraig.h"
#include "fpga.h"
#include "cut.h"
#include "pga.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Pga_NodeStruct_t_     Pga_Node_t;
typedef struct Pga_MatchStruct_t_    Pga_Match_t;

struct Pga_ManStruct_t_
{
    // mapping parameters
    Pga_Params_t *     pParams;       // input data
    // mapping structures
    Pga_Node_t *       pMemory;       // the memory for all mapping structures
    Vec_Ptr_t *        vStructs;      // mapping structures one-to-one with ABC nodes
    Vec_Ptr_t *        vOrdering;     // mapping nodes ordered by level
    // k-feasible cuts
    int                nVarsMax;      // the "k" of k-feasible cuts
    Cut_Man_t *        pManCut;       // the cut manager
    // LUT library
    float *            pLutDelays;    // the delay of the LUTs
    float *            pLutAreas;     // the areas of the LUTs
    float              Epsilon;
    // global parameters
    float              AreaGlobal;    // the total area of this mapping
    float              ArrivalGlobal; // the largest delay of any path
    float              RequiredGlobal;// the global required time (may be different from largest delay)
    float              RequiredUser;  // the required time given by the user
    // runtime stats
    int                timeToMap;     // the time to start the mapper
    int                timeCuts;      // the time to compute the cuts
    int                timeDelay;     // the time to compute delay
    int                timeAreaFlow;  // the time to perform area flow optimization
    int                timeArea;      // the time to perform area flow optimization
    int                timeToNet;     // the time to transform back to network
    int                timeTotal;     // the total time
    int                time1;         // temporary
    int                time2;         // temporary
};

struct Pga_MatchStruct_t_
{
    Cut_Cut_t *        pCut;          // the best cut
    float              Delay;         // the arrival time of this cut
    float              Area;          // the area of this cut
};

struct Pga_NodeStruct_t_
{
    int                Id;            // ID of the node 
    int                nRefs;         // the number of references
    float              EstRefs;       // the estimated reference counter
    float              Required;      // the required time
    float              Switching;     // the switching activity
    Pga_Match_t        Match;         // the best match at the node
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFITIONS                             ///
////////////////////////////////////////////////////////////////////////

static inline Pga_Node_t * Pga_Node( Pga_Man_t * p, int Id )  { return p->vStructs->pArray[Id]; }

// iterator through the CIs
#define Pga_ManForEachCi( p, pCi, i )                                    \
    for ( i = 0; (i < Abc_NtkCiNum(p->pParams->pNtk)) && (((pCi) = Pga_Node(p, Abc_NtkCi(p->pParams->pNtk,i)->Id)), 1); i++ )
// iterator through the CO derivers
#define Pga_ManForEachCoDriver( p, pCo, i )                              \
    for ( i = 0; (i < Abc_NtkCoNum(p->pParams->pNtk)) && (((pCo) = Pga_Node(p, Abc_ObjFaninId0(Abc_NtkCo(p->pParams->pNtk,i)))), 1); i++ )
// iterators through the CIs and internal nodes
#define Pga_ManForEachObjDirect( p, pNode, i )                           \
    Vec_PtrForEachEntry( p->vOrdering, pNode, i )
#define Pga_ManForEachObjReverse( p, pNode, i )                           \
    Vec_PtrForEachEntryReverse( p->vOrdering, pNode, i )

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== pgaMatch.c ==========================================================*/
extern void        Pga_MappingMatches( Pga_Man_t * p, int Mode );
/*=== pgaUtil.c ==========================================================*/
extern Vec_Ptr_t * Pga_MappingResults( Pga_Man_t * p );
extern float       Pga_TimeComputeArrivalMax( Pga_Man_t * p );
extern void        Pga_MappingComputeRequired( Pga_Man_t * p );
extern float       Pga_MappingSetRefsAndArea( Pga_Man_t * p );
extern float       Pga_MappingGetSwitching( Pga_Man_t * p );
extern void        Pga_MappingPrintOutputArrivals( Pga_Man_t * p );

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

#endif

