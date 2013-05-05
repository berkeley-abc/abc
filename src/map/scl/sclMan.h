/**CFile****************************************************************

  FileName    [sclMan.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Standard-cell library representation.]

  Synopsis    [Timing/gate-sizing manager.]

  Author      [Alan Mishchenko, Niklas Een]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 24, 2012.]

  Revision    [$Id: sclMan.h,v 1.0 2012/08/24 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__map__scl__sclMan_h
#define ABC__map__scl__sclMan_h


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "misc/vec/vecQue.h"

ABC_NAMESPACE_HEADER_START

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    STRUCTURE DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

typedef struct SC_Pair_         SC_Pair;
typedef struct SC_Man_          SC_Man;

struct SC_Pair_ 
{
    float          rise;
    float          fall;
};

struct SC_Man_ 
{
    SC_Lib *       pLib;          // library
    Abc_Ntk_t *    pNtk;          // network
    int            nObjs;         // allocated size
    // get assignment
    Vec_Int_t *    vGates;        // mapping of objId into gateId
    Vec_Int_t *    vGatesBest;    // best gate sizes found so far
    Vec_Int_t *    vUpdates;      // sizing updates in this round
    // timing information
    SC_Pair *      pLoads;        // loads for each gate
    SC_Pair *      pLoads2;       // loads for each gate
    SC_Pair *      pDepts;        // departures for each gate
    SC_Pair *      pTimes;        // arrivals for each gate
    SC_Pair *      pSlews;        // slews for each gate
    SC_Pair *      pTimes2;       // arrivals for each gate
    SC_Pair *      pSlews2;       // slews for each gate
    float *        pSlack;        // slacks for each gate
    Vec_Flt_t *    vTimesOut;     // output arrival times
    Vec_Que_t *    vQue;          // outputs by their time
    SC_WireLoad *  pWLoadUsed;    // name of the used WireLoad model
    // intermediate data
    Vec_Que_t *    vNodeByGain;   // nodes by gain
    Vec_Flt_t *    vNode2Gain;    // mapping node into its gain
    Vec_Int_t *    vNode2Gate;    // mapping node into its best gate
    Vec_Int_t *    vNodeIter;     // the last iteration the node was upsized
    // optimization parameters
    float          SumArea;       // total area
    float          MaxDelay;      // max delay
    float          SumArea0;      // total area at the begining 
    float          MaxDelay0;     // max delay at the begining
    float          BestDelay;     // best delay in the middle
    // runtime statistics
    clock_t        timeTotal;     // starting/total time
    clock_t        timeCone;      // critical path selection 
    clock_t        timeSize;      // incremental sizing
    clock_t        timeTime;      // timing update
    clock_t        timeOther;     // everything else
};

////////////////////////////////////////////////////////////////////////
///                       GLOBAL VARIABLES                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                       MACRO DEFINITIONS                          ///
////////////////////////////////////////////////////////////////////////

static inline SC_Cell * Abc_SclObjCell( SC_Man * p, Abc_Obj_t * pObj )              { return SC_LibCell( p->pLib, Vec_IntEntry(p->vGates, Abc_ObjId(pObj)) );       }
static inline void      Abc_SclObjSetCell( SC_Man * p, Abc_Obj_t * pObj, SC_Cell * pCell ) { Vec_IntWriteEntry( p->vGates, Abc_ObjId(pObj), pCell->Id );    }

static inline SC_Pair * Abc_SclObjLoad( SC_Man * p, Abc_Obj_t * pObj )              { return p->pLoads + Abc_ObjId(pObj);  }
static inline SC_Pair * Abc_SclObjLoad2( SC_Man * p, Abc_Obj_t * pObj )             { return p->pLoads2 + Abc_ObjId(pObj); }
static inline SC_Pair * Abc_SclObjDept( SC_Man * p, Abc_Obj_t * pObj )              { return p->pDepts + Abc_ObjId(pObj);  }
static inline SC_Pair * Abc_SclObjTime( SC_Man * p, Abc_Obj_t * pObj )              { return p->pTimes + Abc_ObjId(pObj);  }
static inline SC_Pair * Abc_SclObjSlew( SC_Man * p, Abc_Obj_t * pObj )              { return p->pSlews + Abc_ObjId(pObj);  }
static inline SC_Pair * Abc_SclObjTime2( SC_Man * p, Abc_Obj_t * pObj )             { return p->pTimes2 + Abc_ObjId(pObj); }
static inline SC_Pair * Abc_SclObjSlew2( SC_Man * p, Abc_Obj_t * pObj )             { return p->pSlews2 + Abc_ObjId(pObj); }

static inline float     Abc_SclObjTimeMax( SC_Man * p, Abc_Obj_t * pObj )           { return Abc_MaxFloat(Abc_SclObjTime(p, pObj)->rise, Abc_SclObjTime(p, pObj)->fall);  }
static inline float     Abc_SclObjDepthMax( SC_Man * p, Abc_Obj_t * pObj )          { return Abc_MaxFloat(Abc_SclObjDept(p, pObj)->rise, Abc_SclObjDept(p, pObj)->fall);  }
static inline float     Abc_SclObjGetSlack( SC_Man * p, Abc_Obj_t * pObj, float D ) { return D - Abc_MaxFloat(Abc_SclObjTime(p, pObj)->rise + Abc_SclObjDept(p, pObj)->rise, Abc_SclObjTime(p, pObj)->fall + Abc_SclObjDept(p, pObj)->fall);  }
static inline float     Abc_SclObjSlack( SC_Man * p, Abc_Obj_t * pObj )             { return p->pSlack[Abc_ObjId(pObj)];   }

static inline void      Abc_SclObjDupFanin( SC_Man * p, Abc_Obj_t * pObj )          { assert( Abc_ObjIsCo(pObj) ); *Abc_SclObjTime(p, pObj) = *Abc_SclObjTime(p, Abc_ObjFanin0(pObj));  }
static inline float     Abc_SclObjGain( SC_Man * p, Abc_Obj_t * pObj )              { return (Abc_SclObjTime2(p, pObj)->rise - Abc_SclObjTime(p, pObj)->rise) + (Abc_SclObjTime2(p, pObj)->fall - Abc_SclObjTime(p, pObj)->fall); }

static inline double    Abc_SclObjLoadFf( SC_Man * p, Abc_Obj_t * pObj, int fRise ) { return SC_LibCapFf( p->pLib, fRise ? Abc_SclObjLoad(p, pObj)->rise : Abc_SclObjLoad(p, pObj)->fall); }
static inline double    Abc_SclObjTimePs( SC_Man * p, Abc_Obj_t * pObj, int fRise ) { return SC_LibTimePs(p->pLib, fRise ? Abc_SclObjTime(p, pObj)->rise : Abc_SclObjTime(p, pObj)->fall); }
static inline double    Abc_SclObjSlewPs( SC_Man * p, Abc_Obj_t * pObj, int fRise ) { return SC_LibTimePs(p->pLib, fRise ? Abc_SclObjSlew(p, pObj)->rise : Abc_SclObjSlew(p, pObj)->fall); }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Constructor/destructor of STA manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline SC_Man * Abc_SclManAlloc( SC_Lib * pLib, Abc_Ntk_t * pNtk )
{
    SC_Man * p;
    int i;
    assert( Abc_NtkHasMapping(pNtk) );
    p = ABC_CALLOC( SC_Man, 1 );
    p->pLib      = pLib;
    p->pNtk      = pNtk;
    p->nObjs     = Abc_NtkObjNumMax(pNtk);
    p->pLoads    = ABC_CALLOC( SC_Pair, p->nObjs );
    p->pLoads2   = ABC_CALLOC( SC_Pair, p->nObjs );
    p->pDepts    = ABC_CALLOC( SC_Pair, p->nObjs );
    p->pTimes    = ABC_CALLOC( SC_Pair, p->nObjs );
    p->pSlews    = ABC_CALLOC( SC_Pair, p->nObjs );
    p->pTimes2   = ABC_CALLOC( SC_Pair, p->nObjs );
    p->pSlews2   = ABC_CALLOC( SC_Pair, p->nObjs );
    p->pSlack    = ABC_FALLOC( float, p->nObjs );
    p->vTimesOut = Vec_FltStart( Abc_NtkCoNum(pNtk) );
    p->vQue      = Vec_QueAlloc( Abc_NtkCoNum(pNtk) );
    Vec_QueSetCosts( p->vQue, Vec_FltArrayP(p->vTimesOut) );
    for ( i = 0; i < Abc_NtkCoNum(pNtk); i++ )
        Vec_QuePush( p->vQue, i );
    p->vUpdates  = Vec_IntAlloc( 1000 );
    // intermediate data
    p->vNode2Gain  = Vec_FltStart( p->nObjs );
    p->vNode2Gate  = Vec_IntStart( p->nObjs );
    p->vNodeByGain = Vec_QueAlloc( p->nObjs );
    Vec_QueSetCosts( p->vNodeByGain, Vec_FltArrayP(p->vNode2Gain) );
    p->vNodeIter   = Vec_IntStartFull( p->nObjs );
    return p;
}
static inline void Abc_SclManFree( SC_Man * p )
{
    Vec_IntFreeP( &p->vNodeIter );
    Vec_QueFreeP( &p->vNodeByGain );
    Vec_FltFreeP( &p->vNode2Gain );
    Vec_IntFreeP( &p->vNode2Gate );
    // intermediate data
    Vec_IntFreeP( &p->vUpdates );
    Vec_IntFreeP( &p->vGatesBest );
//    Vec_QuePrint( p->vQue );
    Vec_QueCheck( p->vQue );
    Vec_QueFreeP( &p->vQue );
    Vec_FltFreeP( &p->vTimesOut );
    Vec_IntFreeP( &p->vGates );
    ABC_FREE( p->pLoads );
    ABC_FREE( p->pLoads2 );
    ABC_FREE( p->pDepts );
    ABC_FREE( p->pTimes );
    ABC_FREE( p->pSlews );
    ABC_FREE( p->pTimes2 );
    ABC_FREE( p->pSlews2 );
    ABC_FREE( p->pSlack );
    ABC_FREE( p );
}
static inline void Abc_SclManCleanTime( SC_Man * p )
{
    memset( p->pDepts, 0, sizeof(SC_Pair) * p->nObjs );
    memset( p->pTimes, 0, sizeof(SC_Pair) * p->nObjs );
    memset( p->pSlews, 0, sizeof(SC_Pair) * p->nObjs );
}


/**Function*************************************************************

  Synopsis    [Stores/retrivies timing information for the logic cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_SclConeStore( SC_Man * p, Vec_Int_t * vCone )
{
    Abc_Obj_t * pObj;
    int i;
    Abc_NtkForEachObjVec( vCone, p->pNtk, pObj, i )
    {
        *Abc_SclObjTime2(p, pObj) = *Abc_SclObjTime(p, pObj);
        *Abc_SclObjSlew2(p, pObj) = *Abc_SclObjSlew(p, pObj);
    }
}
static inline void Abc_SclConeRestore( SC_Man * p, Vec_Int_t * vCone )
{
    Abc_Obj_t * pObj;
    int i;
    Abc_NtkForEachObjVec( vCone, p->pNtk, pObj, i )
    {
        *Abc_SclObjTime(p, pObj) = *Abc_SclObjTime2(p, pObj);
        *Abc_SclObjSlew(p, pObj) = *Abc_SclObjSlew2(p, pObj);
    }
}
static inline void Abc_SclConeClear( SC_Man * p, Vec_Int_t * vCone )
{
    SC_Pair Zero = { 0.0, 0.0 };
    Abc_Obj_t * pObj;
    int i;
    Abc_NtkForEachObjVec( vCone, p->pNtk, pObj, i )
    {
        *Abc_SclObjTime(p, pObj) = Zero;
        *Abc_SclObjSlew(p, pObj) = Zero;
    }
}

/**Function*************************************************************

  Synopsis    [Stores/retrivies load information.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_SclLoadStore( SC_Man * p, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanin;
    int i;
    Abc_ObjForEachFanin( pObj, pFanin, i )
        *Abc_SclObjLoad2(p, pFanin) = *Abc_SclObjLoad(p, pFanin);
}
static inline void Abc_SclLoadRestore( SC_Man * p, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanin;
    int i;
    Abc_ObjForEachFanin( pObj, pFanin, i )
        *Abc_SclObjLoad(p, pFanin) = *Abc_SclObjLoad2(p, pFanin);
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline float Abc_SclGetTotalArea( SC_Man * p )
{
    double Area = 0;
    Abc_Obj_t * pObj;
    int i;
    Abc_NtkForEachNode1( p->pNtk, pObj, i )
        Area += Abc_SclObjCell( p, pObj )->area;
    return Area;
}
static inline float Abc_SclGetMaxDelay( SC_Man * p )
{
    float fMaxArr = 0;
    Abc_Obj_t * pObj;
    int i;
    Abc_NtkForEachCo( p->pNtk, pObj, i )
        fMaxArr = Abc_MaxFloat( fMaxArr, Abc_SclObjTimeMax(p, pObj) );
    return fMaxArr;
}
static inline float Abc_SclGetMaxDelayNodeFanins( SC_Man * p, Abc_Obj_t * pNode )
{
    float fMaxArr = 0;
    Abc_Obj_t * pObj;
    int i;
    assert( Abc_ObjIsNode(pNode) );
    Abc_ObjForEachFanin( pNode, pObj, i )
        fMaxArr = Abc_MaxFloat( fMaxArr, Abc_SclObjTimeMax(p, pObj) );
    return fMaxArr;
}
static inline float Abc_SclReadMaxDelay( SC_Man * p )
{
    return Abc_SclObjTimeMax( p, Abc_NtkPo(p->pNtk, Vec_QueTop(p->vQue)) );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline SC_Cell * Abc_SclObjResiable( SC_Man * p, Abc_Obj_t * pObj, int fUpsize )
{
    SC_Cell * pOld = Abc_SclObjCell( p, pObj );
    if ( fUpsize )
        return pOld->pNext->Order > pOld->Order ? pOld->pNext : NULL;
    else
        return pOld->pPrev->Order < pOld->Order ? pOld->pPrev : NULL;
}

/**Function*************************************************************

  Synopsis    [Dumps timing results into a file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_SclDumpStats( SC_Man * p, char * pFileName, clock_t Time )
{
    FILE * pTable;
    pTable = fopen( pFileName, "a+" );
    fprintf( pTable, "%s ", p->pNtk->pName );
    fprintf( pTable, "%d ", Abc_NtkPiNum(p->pNtk) );
    fprintf( pTable, "%d ", Abc_NtkPoNum(p->pNtk) );
    fprintf( pTable, "%d ", Abc_NtkNodeNum(p->pNtk) );
    fprintf( pTable, "%d ", (int)p->SumArea );
    fprintf( pTable, "%d ", (int)SC_LibTimePs(p->pLib, p->MaxDelay) );
    fprintf( pTable, "%.2f ", 1.0*Time/CLOCKS_PER_SEC );
    fprintf( pTable, "\n" );
    fclose( pTable );
}


/*=== sclTime.c =============================================================*/
extern Abc_Obj_t * Abc_SclFindCriticalCo( SC_Man * p, int * pfRise );
extern Abc_Obj_t * Abc_SclFindMostCriticalFanin( SC_Man * p, int * pfRise, Abc_Obj_t * pNode );
extern void        Abc_SclTimeNtkPrint( SC_Man * p, int fShowAll, int fShort );
extern SC_Man *    Abc_SclManStart( SC_Lib * pLib, Abc_Ntk_t * pNtk, int fUseWireLoads, int fDept );
extern void        Abc_SclTimeCone( SC_Man * p, Vec_Int_t * vCone );
extern void        Abc_SclTimeNtkRecompute( SC_Man * p, float * pArea, float * pDelay, int fReverse );
/*=== sclTime.c =============================================================*/
extern void        Abc_SclComputeLoad( SC_Man * p );
extern void        Abc_SclUpdateLoad( SC_Man * p, Abc_Obj_t * pObj, SC_Cell * pOld, SC_Cell * pNew );


ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
