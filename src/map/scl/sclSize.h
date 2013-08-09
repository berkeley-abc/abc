/**CFile****************************************************************

  FileName    [sclSize.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Standard-cell library representation.]

  Synopsis    [Timing/gate-sizing manager.]

  Author      [Alan Mishchenko, Niklas Een]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 24, 2012.]

  Revision    [$Id: sclSize.h,v 1.0 2012/08/24 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__map__scl__sclSize_h
#define ABC__map__scl__sclSize_h


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "base/abc/abc.h"
#include "misc/vec/vecQue.h"
#include "sclLib.h"

ABC_NAMESPACE_HEADER_START

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    STRUCTURE DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

typedef struct SC_Man_          SC_Man;
struct SC_Man_ 
{
    SC_Lib *       pLib;          // library
    Abc_Ntk_t *    pNtk;          // network
    int            nObjs;         // allocated size
    // get assignment
//    Vec_Int_t *    vGates;        // mapping of objId into gateId
    Vec_Int_t *    vGatesBest;    // best gate sizes found so far
    Vec_Int_t *    vUpdates;      // sizing updates in this round
    Vec_Int_t *    vUpdates2;     // sizing updates in this round
    // timing information
    SC_Pair *      pLoads;        // loads for each gate
    SC_Pair *      pDepts;        // departures for each gate
    SC_Pair *      pTimes;        // arrivals for each gate
    SC_Pair *      pSlews;        // slews for each gate
    SC_Pair *      pTimes2;       // arrivals for each gate
    SC_Pair *      pSlews2;       // slews for each gate
    Vec_Flt_t *    vLoads2;       // backup storage for loads
    Vec_Flt_t *    vLoads3;       // backup storage for loads
    float *        pSlack;        // slacks for each gatt
    float *        pInDrive;      // maximum input drive strength
    Vec_Int_t *    vBestFans;     // best fanouts
    Vec_Flt_t *    vTimesOut;     // output arrival times
    Vec_Que_t *    vQue;          // outputs by their time
    SC_WireLoad *  pWLoadUsed;    // name of the used WireLoad model
    // buffer trees
    float          EstLoadMax;    // max ratio of Cout/Cin when this kicks in
    float          EstLoadAve;    // average load of the gate
    float          EstLinear;     // linear coefficient
    int            nEstNodes;     // the number of estimations
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
    float          ReportDelay;   // delay to report
    // runtime statistics
    abctime        timeTotal;     // starting/total time
    abctime        timeCone;      // critical path selection 
    abctime        timeSize;      // incremental sizing
    abctime        timeTime;      // timing update
    abctime        timeOther;     // everything else
};

////////////////////////////////////////////////////////////////////////
///                       GLOBAL VARIABLES                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                       MACRO DEFINITIONS                          ///
////////////////////////////////////////////////////////////////////////

static inline SC_Lib  * Abc_SclObjLib( Abc_Obj_t * p )                              { return (SC_Lib *)p->pNtk->pSCLib;    }
static inline SC_Cell * Abc_SclObjCell( Abc_Obj_t * p )                             { return SC_LibCell( Abc_SclObjLib(p), Vec_IntEntry(p->pNtk->vGates, Abc_ObjId(p)) ); }
static inline void      Abc_SclObjSetCell( Abc_Obj_t * p, SC_Cell * pCell )         { Vec_IntWriteEntry( p->pNtk->vGates, Abc_ObjId(p), pCell->Id );                      }

static inline SC_Pair * Abc_SclObjLoad( SC_Man * p, Abc_Obj_t * pObj )              { return p->pLoads + Abc_ObjId(pObj);  }
static inline SC_Pair * Abc_SclObjDept( SC_Man * p, Abc_Obj_t * pObj )              { return p->pDepts + Abc_ObjId(pObj);  }
static inline SC_Pair * Abc_SclObjTime( SC_Man * p, Abc_Obj_t * pObj )              { return p->pTimes + Abc_ObjId(pObj);  }
static inline SC_Pair * Abc_SclObjSlew( SC_Man * p, Abc_Obj_t * pObj )              { return p->pSlews + Abc_ObjId(pObj);  }
static inline SC_Pair * Abc_SclObjTime2( SC_Man * p, Abc_Obj_t * pObj )             { return p->pTimes2 + Abc_ObjId(pObj); }
static inline SC_Pair * Abc_SclObjSlew2( SC_Man * p, Abc_Obj_t * pObj )             { return p->pSlews2 + Abc_ObjId(pObj); }

static inline float     Abc_SclObjTimeMax( SC_Man * p, Abc_Obj_t * pObj )           { return Abc_MaxFloat(Abc_SclObjTime(p, pObj)->rise, Abc_SclObjTime(p, pObj)->fall);  }
static inline float     Abc_SclObjDepthMax( SC_Man * p, Abc_Obj_t * pObj )          { return Abc_MaxFloat(Abc_SclObjDept(p, pObj)->rise, Abc_SclObjDept(p, pObj)->fall);  }
static inline float     Abc_SclObjGetSlack( SC_Man * p, Abc_Obj_t * pObj, float D ) { return D - Abc_MaxFloat(Abc_SclObjTime(p, pObj)->rise + Abc_SclObjDept(p, pObj)->rise, Abc_SclObjTime(p, pObj)->fall + Abc_SclObjDept(p, pObj)->fall);  }
static inline float     Abc_SclObjGetSlackR( SC_Man * p, Abc_Obj_t * pObj, float D ){ return D - (Abc_SclObjTime(p, pObj)->rise + Abc_SclObjDept(p, pObj)->rise);  }
static inline float     Abc_SclObjGetSlackF( SC_Man * p, Abc_Obj_t * pObj, float D ){ return D - (Abc_SclObjTime(p, pObj)->fall + Abc_SclObjDept(p, pObj)->fall);  }
static inline float     Abc_SclObjSlack( SC_Man * p, Abc_Obj_t * pObj )             { return p->pSlack[Abc_ObjId(pObj)];   }
static inline float     Abc_SclObjLoadAve( SC_Man * p, Abc_Obj_t * pObj )           { return 0.5 * (Abc_SclObjLoad(p, pObj)->rise + Abc_SclObjLoad(p, pObj)->fall); }

static inline void      Abc_SclObjDupFanin( SC_Man * p, Abc_Obj_t * pObj )          { assert( Abc_ObjIsCo(pObj) ); *Abc_SclObjTime(p, pObj) = *Abc_SclObjTime(p, Abc_ObjFanin0(pObj));  }
static inline float     Abc_SclObjGain( SC_Man * p, Abc_Obj_t * pObj )              { return 0.5*((Abc_SclObjTime2(p, pObj)->rise - Abc_SclObjTime(p, pObj)->rise) + (Abc_SclObjTime2(p, pObj)->fall - Abc_SclObjTime(p, pObj)->fall)); }
static inline int       Abc_SclObjLegal( SC_Man * p, Abc_Obj_t * pObj, float D )    { return Abc_SclObjTime(p, pObj)->rise <= Abc_SclObjTime2(p, pObj)->rise + Abc_SclObjGetSlackR(p, pObj, D) && Abc_SclObjTime(p, pObj)->fall <= Abc_SclObjTime2(p, pObj)->fall + Abc_SclObjGetSlackF(p, pObj, D); }

static inline double    Abc_SclObjLoadFf( SC_Man * p, Abc_Obj_t * pObj, int fRise ) { return SC_LibCapFf( p->pLib, fRise ? Abc_SclObjLoad(p, pObj)->rise : Abc_SclObjLoad(p, pObj)->fall); }
static inline double    Abc_SclObjTimePs( SC_Man * p, Abc_Obj_t * pObj, int fRise ) { return SC_LibTimePs(p->pLib, fRise ? Abc_SclObjTime(p, pObj)->rise : Abc_SclObjTime(p, pObj)->fall); }
static inline double    Abc_SclObjSlewPs( SC_Man * p, Abc_Obj_t * pObj, int fRise ) { return SC_LibTimePs(p->pLib, fRise ? Abc_SclObjSlew(p, pObj)->rise : Abc_SclObjSlew(p, pObj)->fall); }
static inline double    Abc_SclObjSlackPs( SC_Man * p, Abc_Obj_t * pObj )           { return SC_LibTimePs(p->pLib, Abc_SclObjSlack(p, pObj));                        }

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
    p->pDepts    = ABC_CALLOC( SC_Pair, p->nObjs );
    p->pTimes    = ABC_CALLOC( SC_Pair, p->nObjs );
    p->pSlews    = ABC_CALLOC( SC_Pair, p->nObjs );
    p->pTimes2   = ABC_CALLOC( SC_Pair, p->nObjs );
    p->pSlews2   = ABC_CALLOC( SC_Pair, p->nObjs );
    p->pSlack    = ABC_FALLOC( float, p->nObjs );
    p->vBestFans = Vec_IntStart( p->nObjs );
    p->vTimesOut = Vec_FltStart( Abc_NtkCoNum(pNtk) );
    p->vQue      = Vec_QueAlloc( Abc_NtkCoNum(pNtk) );
    Vec_QueSetCosts( p->vQue, Vec_FltArrayP(p->vTimesOut) );
    for ( i = 0; i < Abc_NtkCoNum(pNtk); i++ )
        Vec_QuePush( p->vQue, i );
    p->vUpdates  = Vec_IntAlloc( 1000 );
    p->vUpdates2 = Vec_IntAlloc( 1000 );
    p->vLoads2   = Vec_FltAlloc( 1000 );
    p->vLoads3   = Vec_FltAlloc( 1000 );
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
    p->pNtk->pSCLib = NULL;
    Vec_IntFreeP( &p->pNtk->vGates );
    Vec_IntFreeP( &p->vNodeIter );
    Vec_QueFreeP( &p->vNodeByGain );
    Vec_FltFreeP( &p->vNode2Gain );
    Vec_IntFreeP( &p->vNode2Gate );
    // intermediate data
    Vec_FltFreeP( &p->vLoads2 );
    Vec_FltFreeP( &p->vLoads3 );
    Vec_IntFreeP( &p->vUpdates );
    Vec_IntFreeP( &p->vUpdates2 );
    Vec_IntFreeP( &p->vGatesBest );
//    Vec_QuePrint( p->vQue );
    Vec_QueCheck( p->vQue );
    Vec_QueFreeP( &p->vQue );
    Vec_FltFreeP( &p->vTimesOut );
//    Vec_IntFreeP( &p->vGates );
    Vec_IntFreeP( &p->vBestFans );
    ABC_FREE( p->pLoads );
    ABC_FREE( p->pDepts );
    ABC_FREE( p->pTimes );
    ABC_FREE( p->pSlews );
    ABC_FREE( p->pTimes2 );
    ABC_FREE( p->pSlews2 );
    ABC_FREE( p->pSlack );
    ABC_FREE( p->pInDrive );
    ABC_FREE( p );
}
static inline void Abc_SclManCleanTime( SC_Man * p )
{
    Vec_Flt_t * vSlews;
    Abc_Obj_t * pObj;
    int i;
    vSlews = Vec_FltAlloc( 2 * Abc_NtkPiNum(p->pNtk) );
    Abc_NtkForEachPi( p->pNtk, pObj, i )
    {
        SC_Pair * pSlew = Abc_SclObjSlew( p, pObj );
        Vec_FltPush( vSlews, pSlew->rise );
        Vec_FltPush( vSlews, pSlew->fall );
    }
    memset( p->pDepts, 0, sizeof(SC_Pair) * p->nObjs );
    memset( p->pTimes, 0, sizeof(SC_Pair) * p->nObjs );
    memset( p->pSlews, 0, sizeof(SC_Pair) * p->nObjs );
    Abc_NtkForEachPi( p->pNtk, pObj, i )
    {
        SC_Pair * pSlew = Abc_SclObjSlew( p, pObj );
        pSlew->rise = Vec_FltEntry( vSlews, 2 * i + 0 );
        pSlew->fall = Vec_FltEntry( vSlews, 2 * i + 1 );
    }
    Vec_FltFree( vSlews );
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
    Vec_FltClear( p->vLoads2 );
    Abc_ObjForEachFanin( pObj, pFanin, i )
    {
        Vec_FltPush( p->vLoads2, Abc_SclObjLoad(p, pFanin)->rise );
        Vec_FltPush( p->vLoads2, Abc_SclObjLoad(p, pFanin)->fall );
    }
}
static inline void Abc_SclLoadRestore( SC_Man * p, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanin;
    int i;
    assert( Vec_FltSize(p->vLoads2) == 2 * Abc_ObjFaninNum(pObj) );
    Abc_ObjForEachFanin( pObj, pFanin, i )
    {
        Abc_SclObjLoad(p, pFanin)->rise = Vec_FltEntry(p->vLoads2, 2*i);
        Abc_SclObjLoad(p, pFanin)->fall = Vec_FltEntry(p->vLoads2, 2*i+1);
    }
}

static inline void Abc_SclLoadStore3( SC_Man * p, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanin;
    int i;
    Vec_FltClear( p->vLoads3 );
    Abc_ObjForEachFanin( pObj, pFanin, i )
    {
        Vec_FltPush( p->vLoads3, Abc_SclObjLoad(p, pFanin)->rise );
        Vec_FltPush( p->vLoads3, Abc_SclObjLoad(p, pFanin)->fall );
    }
    Vec_FltPush( p->vLoads3, Abc_SclObjLoad(p, pObj)->rise );
    Vec_FltPush( p->vLoads3, Abc_SclObjLoad(p, pObj)->fall );
}
static inline void Abc_SclLoadRestore3( SC_Man * p, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanin;
    int i;
    assert( Vec_FltSize(p->vLoads3) == 2 * Abc_ObjFaninNum(pObj) + 2 );
    Abc_ObjForEachFanin( pObj, pFanin, i )
    {
        Abc_SclObjLoad(p, pFanin)->rise = Vec_FltEntry(p->vLoads3, 2*i);
        Abc_SclObjLoad(p, pFanin)->fall = Vec_FltEntry(p->vLoads3, 2*i+1);
    }
    Abc_SclObjLoad(p, pObj)->rise = Vec_FltEntry(p->vLoads3, 2*i);
    Abc_SclObjLoad(p, pObj)->fall = Vec_FltEntry(p->vLoads3, 2*i+1);
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
        Area += Abc_SclObjCell(pObj)->area;
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
    return Abc_SclObjTimeMax( p, Abc_NtkCo(p->pNtk, Vec_QueTop(p->vQue)) );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline SC_Cell * Abc_SclObjResiable( SC_Man * p, Abc_Obj_t * pObj, int fUpsize )
{
    SC_Cell * pOld = Abc_SclObjCell(pObj);
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
static inline void Abc_SclDumpStats( SC_Man * p, char * pFileName, abctime Time )
{
    static char FileNameOld[1000] = {0};
    static int nNodesOld, nAreaOld, nDelayOld;
    FILE * pTable;
    pTable = fopen( pFileName, "a+" );
    if ( strcmp( FileNameOld, p->pNtk->pName ) )
    {
        sprintf( FileNameOld, "%s", p->pNtk->pName );
        fprintf( pTable, "\n" );
        fprintf( pTable, "%s ", p->pNtk->pName );
        fprintf( pTable, "%d ", Abc_NtkPiNum(p->pNtk) );
        fprintf( pTable, "%d ", Abc_NtkPoNum(p->pNtk) );
        fprintf( pTable, "%d ", (nNodesOld = Abc_NtkNodeNum(p->pNtk)) );
        fprintf( pTable, "%d ", (nAreaOld  = (int)p->SumArea)         );
        fprintf( pTable, "%d ", (nDelayOld = (int)p->ReportDelay)     );
    }
    else
    {
        fprintf( pTable, " " );
        fprintf( pTable, "%.1f ", 100.0 * Abc_NtkNodeNum(p->pNtk) / nNodesOld );
        fprintf( pTable, "%.1f ", 100.0 * (int)p->SumArea         / nAreaOld  );
        fprintf( pTable, "%.1f ", 100.0 * (int)p->ReportDelay     / nDelayOld );
    }
    //    fprintf( pTable, "%.2f ", 1.0*Time/CLOCKS_PER_SEC );
    fclose( pTable );
}

/*=== sclBufSize.c ===============================================================*/
extern Abc_Ntk_t *   Abc_SclBufSizePerform( Abc_Ntk_t * pNtk, SC_Lib * pLib, int GainRatio, int nDegree, int fAddBufs, int fBufPis, int fVerbose );
/*=== sclBuffer.c ===============================================================*/
extern int           Abc_SclIsInv( Abc_Obj_t * pObj );
extern void          Abc_NodeInvUpdateFanPolarity( Abc_Obj_t * pObj );
extern void          Abc_NodeInvUpdateObjFanoutPolarity( Abc_Obj_t * pObj, Abc_Obj_t * pFanout );
extern void          Abc_SclReportDupFanins( Abc_Ntk_t * pNtk );
extern Abc_Ntk_t *   Abc_SclUnBufferPerform( Abc_Ntk_t * pNtk, int fVerbose );
extern Abc_Ntk_t *   Abc_SclUnBufferPhase( Abc_Ntk_t * pNtk, int fVerbose );
extern Abc_Ntk_t *   Abc_SclBufferPhase( Abc_Ntk_t * pNtk, int fVerbose );
extern int           Abc_SclCheckNtk( Abc_Ntk_t * p, int fVerbose );
extern Abc_Ntk_t *   Abc_SclPerformBuffering( Abc_Ntk_t * p, int DegreeR, int Degree, int fUseInvs, int fVerbose );
extern Abc_Ntk_t *   Abc_SclBufPerform( Abc_Ntk_t * pNtk, int FanMin, int FanMax, int fBufPis, int fVerbose );
/*=== sclDnsize.c ===============================================================*/
extern void          Abc_SclDnsizePerform( SC_Lib * pLib, Abc_Ntk_t * pNtk, SC_SizePars * pPars );
/*=== sclLoad.c ===============================================================*/
extern void          Abc_SclComputeLoad( SC_Man * p );
extern void          Abc_SclUpdateLoad( SC_Man * p, Abc_Obj_t * pObj, SC_Cell * pOld, SC_Cell * pNew );
extern void          Abc_SclUpdateLoadSplit( SC_Man * p, Abc_Obj_t * pBuffer, Abc_Obj_t * pFanout );
/*=== sclSize.c ===============================================================*/
extern Abc_Obj_t *   Abc_SclFindCriticalCo( SC_Man * p, int * pfRise );
extern Abc_Obj_t *   Abc_SclFindMostCriticalFanin( SC_Man * p, int * pfRise, Abc_Obj_t * pNode );
extern void          Abc_SclTimeNtkPrint( SC_Man * p, int fShowAll, int fPrintPath );
extern SC_Man *      Abc_SclManStart( SC_Lib * pLib, Abc_Ntk_t * pNtk, int fUseWireLoads, int fDept, float DUser, int nTreeCRatio );
extern void          Abc_SclTimeCone( SC_Man * p, Vec_Int_t * vCone );
extern void          Abc_SclTimeNtkRecompute( SC_Man * p, float * pArea, float * pDelay, int fReverse, float DUser );
extern void          Abc_SclTimePerform( SC_Lib * pLib, Abc_Ntk_t * pNtk, int nTreeCRatio, int fUseWireLoads, int fShowAll, int fPrintPath, int fDumpStats );
extern void          Abc_SclPrintBuffers( SC_Lib * pLib, Abc_Ntk_t * pNtk, int fVerbose );
extern int           Abc_SclInputDriveOk( SC_Man * p, Abc_Obj_t * pObj, SC_Cell * pCell );
/*=== sclUpsize.c ===============================================================*/
extern int           Abc_SclCountNearCriticalNodes( SC_Man * p );
extern void          Abc_SclUpsizePerform( SC_Lib * pLib, Abc_Ntk_t * pNtk, SC_SizePars * pPars );
/*=== sclUtil.c ===============================================================*/
extern void          Abc_SclMioGates2SclGates( SC_Lib * pLib, Abc_Ntk_t * p );
extern void          Abc_SclSclGates2MioGates( SC_Lib * pLib, Abc_Ntk_t * p );
extern void          Abc_SclPrintGateSizes( SC_Lib * pLib, Abc_Ntk_t * p );
extern void          Abc_SclMinsizePerform( SC_Lib * pLib, Abc_Ntk_t * p, int fUseMax, int fVerbose );
extern int           Abc_SclCountMinSize( SC_Lib * pLib, Abc_Ntk_t * p, int fUseMax );


ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
