/**CFile****************************************************************

  FileName    [giaAbsRef.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Refinement manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaAbsRef.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "giaAbsRef.h"

ABC_NAMESPACE_IMPL_START

/*
    Description of the refinement manager

    This refinement manager should be 
    * started by calling Rnm_ManStart()
       this procedure takes one argument, the user's seq miter as a GIA manager
       - the manager should have only one property output
       - this manager should not change while the refinement manager is alive
       - it cannot be used by external applications for any purpose
       - when the refinement manager stop, GIA manager is the same as at the beginning
       - in the meantime, it will have some data-structures attached to its nodes...
    * stopped by calling Rnm_ManStop()
    * between starting and stopping, refinements are obtained by calling Rnm_ManRefine()

    Procedure Rnm_ManRefine() takes the following arguments:
    * the refinement manager previously started by Rnm_ManStart()
    * counter-example (CEX) obtained by abstracting some logic of GIA
    * mapping (vMap) of inputs of the CEX into the object IDs of the GIA manager
       - only PI, flop outputs, and internal AND nodes can be used in vMap
       - the ordering of objects in vMap is not important
       - however, the index of a non-PI object in vMap is used as its priority
         (the smaller the index, the more likely this non-PI object apears in a refinement)
       - only the logic between PO and the objects listed in vMap is traversed by the manager
         (as a result, GIA can be arbitrarily large, but only objects used in the abstraction
         and the pseudo-PI, that is, objects in the cut, will be visited by the manager)
    * flag fPropFanout defines whether value propagation is done through the fanout
       - it this flag is enabled, theoretically refinement should be better (the result smaller)
    * flag fVerbose may print some statistics

    The refinement manager returns a minimal-size array of integer IDs of GIA objects
    which should be added to the abstraction to possibly prevent the given counter-example
       - only flop output and internal AND nodes from vMap may appear in the resulting array
       - if the resulting array is empty, the CEX is a true CEX 
         (in other words, non-PI objects are not needed to set the PO value to 1)

    Verification of the selected refinement is performed by 
       - initializing all PI objects in vMap to value 0 or 1 they have in the CEX
       - initializing all remaining objects in vMap to value X
       - initializing objects used in the refiment to value 0 or 1 they have in the CEX
       - simulating through as many timeframes as required by the CEX
       - if the PO value in the last frame is 1, the refinement is correct
         (however, the minimality of the refinement is not currently checked)
        
*/

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Rnm_Obj_t_ Rnm_Obj_t; // refinement object
struct Rnm_Obj_t_
{
    unsigned       Value     :  1;  // binary value
    unsigned       fVisit    :  1;  // visited object
    unsigned       fVisit0   :  1;  // visited object
    unsigned       fPPi      :  1;  // PPI object
    unsigned       Prio      : 24;  // priority (0 - highest)
};

struct Rnm_Man_t_
{
    // user data
    Gia_Man_t *    pGia;            // working AIG manager (it is completely owned by this package)
    Abc_Cex_t *    pCex;            // counter-example
    Vec_Int_t *    vMap;            // mapping of CEX inputs into objects (PI + PPI, in any order)
    int            fPropFanout;     // propagate fanouts
    int            fVerbose;        // verbose flag
    // traversing data
    Vec_Int_t *    vObjs;           // internal objects used in value propagation
    Vec_Str_t *    vCounts;         // fanin counters
    Vec_Int_t *    vFanins;         // fanins
    // internal data
    Rnm_Obj_t *    pObjs;           // refinement objects
    int            nObjs;           // the number of used objects
    int            nObjsAlloc;      // the number of allocated objects
    int            nObjsFrame;      // the number of used objects in each frame
    int            nCalls;          // total number of calls
    int            nRefines;        // total refined objects
    int            nVisited;        // visited during justification
    // statistics  
    clock_t        timeFwd;         // forward propagation
    clock_t        timeBwd;         // backward propagation
    clock_t        timeVer;         // ternary simulation
    clock_t        timeTotal;       // other time
};

// accessing the refinement object
static inline Rnm_Obj_t * Rnm_ManObj( Rnm_Man_t * p, Gia_Obj_t * pObj, int f )  
{ 
    assert( Gia_ObjIsConst0(pObj) || pObj->Value );
    assert( (int)pObj->Value < p->nObjsFrame );
    assert( f >= 0 && f <= p->pCex->iFrame ); 
    return p->pObjs + f * p->nObjsFrame + pObj->Value;  
}

static inline int         Ga2_ObjOffset( Gia_Man_t * p, Gia_Obj_t * pObj )          { return Vec_IntEntry(p->vMapping, Gia_ObjId(p, pObj));                                                    }
static inline int         Ga2_ObjLeaveNum( Gia_Man_t * p, Gia_Obj_t * pObj )        { return Vec_IntEntry(p->vMapping, Ga2_ObjOffset(p, pObj));                                                }
static inline int *       Ga2_ObjLeavePtr( Gia_Man_t * p, Gia_Obj_t * pObj )        { return Vec_IntEntryP(p->vMapping, Ga2_ObjOffset(p, pObj) + 1);                                           }
static inline unsigned    Ga2_ObjTruth( Gia_Man_t * p, Gia_Obj_t * pObj )           { return (unsigned)Vec_IntEntry(p->vMapping, Ga2_ObjOffset(p, pObj) + Ga2_ObjLeaveNum(p, pObj) + 1);       }
static inline int         Ga2_ObjRefNum( Gia_Man_t * p, Gia_Obj_t * pObj )          { return (unsigned)Vec_IntEntry(p->vMapping, Ga2_ObjOffset(p, pObj) + Ga2_ObjLeaveNum(p, pObj) + 2);       }
static inline Vec_Int_t * Ga2_ObjLeaves( Gia_Man_t * p, Gia_Obj_t * pObj )          { static Vec_Int_t v; v.nSize = Ga2_ObjLeaveNum(p, pObj), v.pArray = Ga2_ObjLeavePtr(p, pObj); return &v;  }

static inline int         Rnm_ObjCount( Rnm_Man_t * p, Gia_Obj_t * pObj )           { return Vec_StrEntry( p->vCounts, Gia_ObjId(p->pGia, pObj) );                            }
static inline void        Rnm_ObjSetCount( Rnm_Man_t * p, Gia_Obj_t * pObj, int c ) { Vec_StrWriteEntry( p->vCounts, Gia_ObjId(p->pGia, pObj), (char)c );                     }
static inline int         Rnm_ObjAddToCount( Rnm_Man_t * p, Gia_Obj_t * pObj )      { int c = Rnm_ObjCount(p, pObj); if ( c < 16 )  Rnm_ObjSetCount(p, pObj, c+1); return c;  }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates a new manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Rnm_Man_t * Rnm_ManStart( Gia_Man_t * pGia )
{
    Rnm_Man_t * p;
    assert( Gia_ManPoNum(pGia) == 1 );
    p = ABC_CALLOC( Rnm_Man_t, 1 );
    p->pGia = pGia;
    p->vObjs = Vec_IntAlloc( 100 );
    p->vCounts = Vec_StrStart( Gia_ManObjNum(pGia) );
    p->vFanins = Vec_IntAlloc( 100 );
    p->nObjsAlloc = 10000;
    p->pObjs = ABC_ALLOC( Rnm_Obj_t, p->nObjsAlloc );
    if ( p->pGia->vFanout == NULL )
        Gia_ManStaticFanoutStart( p->pGia );
    Gia_ManCleanValue(pGia);
    Gia_ManCleanMark0(pGia);
    Gia_ManCleanMark1(pGia);
    return p;
}
void Rnm_ManStop( Rnm_Man_t * p, int fProfile )
{
    if ( !p ) return;
    // print runtime statistics
    if ( fProfile && p->nCalls )
    {
        double MemGia = sizeof(Gia_Man_t) + sizeof(Gia_Obj_t) * p->pGia->nObjsAlloc + sizeof(int) * p->pGia->nTravIdsAlloc;
        double MemOther = sizeof(Rnm_Man_t) + sizeof(Rnm_Obj_t) * p->nObjsAlloc + sizeof(int) * Vec_IntCap(p->vObjs);
        clock_t timeOther = p->timeTotal - p->timeFwd - p->timeBwd - p->timeVer;
        printf( "Abstraction refinement runtime statistics:\n" );
        ABC_PRTP( "Sensetization", p->timeFwd,   p->timeTotal );
        ABC_PRTP( "Justification", p->timeBwd,   p->timeTotal );
        ABC_PRTP( "Verification ", p->timeVer,   p->timeTotal );
        ABC_PRTP( "Other        ", timeOther,    p->timeTotal );
        ABC_PRTP( "TOTAL        ", p->timeTotal, p->timeTotal );
        printf( "Total calls = %d.  Average refine = %.1f. GIA mem = %.3f MB.  Other mem = %.3f MB.\n", 
            p->nCalls, 1.0*p->nRefines/p->nCalls, MemGia/(1<<20), MemOther/(1<<20) );
    }

    Gia_ManCleanMark0(p->pGia);
    Gia_ManCleanMark1(p->pGia);
    Gia_ManStaticFanoutStop(p->pGia);
//    Gia_ManSetPhase(p->pGia);
    Vec_StrFree( p->vCounts );
    Vec_IntFree( p->vFanins );
    Vec_IntFree( p->vObjs );
    ABC_FREE( p->pObjs );
    ABC_FREE( p );
}
double Rnm_ManMemoryUsage( Rnm_Man_t * p )
{
    return (double)(sizeof(Rnm_Man_t) + sizeof(Rnm_Obj_t) * p->nObjsAlloc + sizeof(int) * Vec_IntCap(p->vObjs));
}


/**Function*************************************************************

  Synopsis    [Collect internal objects to be used in value propagation.]

  Description [Resulting array vObjs contains RO, AND, PO/RI in a topo order.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rnm_ManCollect_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vObjs, int nAddOn )
{
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return;
    Gia_ObjSetTravIdCurrent(p, pObj);
    if ( Gia_ObjIsCo(pObj) )
        Rnm_ManCollect_rec( p, Gia_ObjFanin0(pObj), vObjs, nAddOn );
    else if ( Gia_ObjIsAnd(pObj) )
    {
        Rnm_ManCollect_rec( p, Gia_ObjFanin0(pObj), vObjs, nAddOn );
        Rnm_ManCollect_rec( p, Gia_ObjFanin1(pObj), vObjs, nAddOn );
    }
    else if ( !Gia_ObjIsRo(p, pObj) )
        assert( 0 );
    pObj->Value = Vec_IntSize(vObjs) + nAddOn;
    Vec_IntPush( vObjs, Gia_ObjId(p, pObj) );
}
void Rnm_ManCollect( Rnm_Man_t * p )
{
    Gia_Obj_t * pObj = NULL;
    int i;
    // mark const/PIs/PPIs
    Gia_ManIncrementTravId( p->pGia );
    Gia_ObjSetTravIdCurrent( p->pGia, Gia_ManConst0(p->pGia) );
    Gia_ManConst0(p->pGia)->Value = 0;
    Gia_ManForEachObjVec( p->vMap, p->pGia, pObj, i )
    {
        assert( Gia_ObjIsCi(pObj) || Gia_ObjIsAnd(pObj) );
        Gia_ObjSetTravIdCurrent( p->pGia, pObj );
        pObj->Value = 1 + i;
    }
    // collect objects
    Vec_IntClear( p->vObjs );
    Rnm_ManCollect_rec( p->pGia, Gia_ManPo(p->pGia, 0), p->vObjs, 1 + Vec_IntSize(p->vMap) );
    Gia_ManForEachObjVec( p->vObjs, p->pGia, pObj, i )
        if ( Gia_ObjIsRo(p->pGia, pObj) )
            Rnm_ManCollect_rec( p->pGia, Gia_ObjRoToRi(p->pGia, pObj), p->vObjs, 1 + Vec_IntSize(p->vMap) );
    // the last object should be a CO
    assert( Gia_ObjIsCo(pObj) );
    assert( (int)pObj->Value == Vec_IntSize(p->vMap) + Vec_IntSize(p->vObjs) );
}
void Rnm_ManCleanValues( Rnm_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i;
    Gia_ManForEachObjVec( p->vMap, p->pGia, pObj, i )
        pObj->Value = 0;
    Gia_ManForEachObjVec( p->vObjs, p->pGia, pObj, i )
        pObj->Value = 0;
}

/**Function*************************************************************

  Synopsis    [Performs sensitization analysis.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Rnm_ManSensitize( Rnm_Man_t * p )
{
    Rnm_Obj_t * pRnm, * pRnm0, * pRnm1;
    Gia_Obj_t * pObj;
    int f, i, iBit = p->pCex->nRegs;
    // const0 is initialized automatically in all timeframes
    for ( f = 0; f <= p->pCex->iFrame; f++, iBit += p->pCex->nPis )
    {
        Gia_ManForEachObjVec( p->vMap, p->pGia, pObj, i )
        {
            assert( Gia_ObjIsCi(pObj) || Gia_ObjIsAnd(pObj) );
            pRnm = Rnm_ManObj( p, pObj, f );
            pRnm->Value = Abc_InfoHasBit( p->pCex->pData, iBit + i );
            if ( !Gia_ObjIsPi(p->pGia, pObj) ) // this is PPI
            {
                assert( pObj->Value > 0 );
                pRnm->Prio = pObj->Value;
                pRnm->fPPi = 1;
            }
        }
        Gia_ManForEachObjVec( p->vObjs, p->pGia, pObj, i )
        {
            assert( Gia_ObjIsRo(p->pGia, pObj) || Gia_ObjIsAnd(pObj) || Gia_ObjIsCo(pObj) );
            pRnm = Rnm_ManObj( p, pObj, f );
            assert( !pRnm->fPPi );
            if ( Gia_ObjIsRo(p->pGia, pObj) )
            {
                if ( f == 0 )
                    continue;
                pRnm0 = Rnm_ManObj( p, Gia_ObjRoToRi(p->pGia, pObj), f-1 );
                pRnm->Value = pRnm0->Value;
                pRnm->Prio  = pRnm0->Prio;
                continue;
            }
            if ( Gia_ObjIsCo(pObj) )
            {
                pRnm0 = Rnm_ManObj( p, Gia_ObjFanin0(pObj), f );
                pRnm->Value = (pRnm0->Value ^ Gia_ObjFaninC0(pObj));
                pRnm->Prio  = pRnm0->Prio;
                continue;
            }
            assert( Gia_ObjIsAnd(pObj) );
            pRnm0 = Rnm_ManObj( p, Gia_ObjFanin0(pObj), f );
            pRnm1 = Rnm_ManObj( p, Gia_ObjFanin1(pObj), f );
            pRnm->Value = (pRnm0->Value ^ Gia_ObjFaninC0(pObj)) & (pRnm1->Value ^ Gia_ObjFaninC1(pObj));
            if ( pRnm->Value == 1 )
                pRnm->Prio  = Abc_MaxInt( pRnm0->Prio, pRnm1->Prio );
            else if ( (pRnm0->Value ^ Gia_ObjFaninC0(pObj)) == 0 && (pRnm1->Value ^ Gia_ObjFaninC1(pObj)) == 0 )
                pRnm->Prio  = Abc_MinInt( pRnm0->Prio, pRnm1->Prio ); // choice
            else if ( (pRnm0->Value ^ Gia_ObjFaninC0(pObj)) == 0 )
                pRnm->Prio  = pRnm0->Prio;
            else 
                pRnm->Prio  = pRnm1->Prio;
        }
    }
    assert( iBit == p->pCex->nBits );
    pRnm = Rnm_ManObj( p, Gia_ManPo(p->pGia, 0), p->pCex->iFrame );
    if ( pRnm->Value != 1 )
        printf( "Output value is incorrect.\n" );
    return pRnm->Prio;
}


/**Function*************************************************************

  Synopsis    [Drive implications of the given node towards primary outputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rnm_ManJustifyPropFanout_rec( Rnm_Man_t * p, Gia_Obj_t * pObj, int f, Vec_Int_t * vSelect )
{
    Rnm_Obj_t * pRnm0, * pRnm1, * pRnm = Rnm_ManObj( p, pObj, f );
    Gia_Obj_t * pFanout = NULL;
    int i, k;//, Id = Gia_ObjId(p->pGia, pObj);
    assert( pRnm->fVisit == 0 );
    pRnm->fVisit = 1;
    if ( Rnm_ManObj( p, pObj, 0 )->fVisit0 == 0 )
    {
        Rnm_ManObj( p, pObj, 0 )->fVisit0 = 1;
        p->nVisited++;
    }
    if ( pRnm->fPPi )
    {
        assert( (int)pRnm->Prio > 0 );
        for ( i = p->pCex->iFrame; i >= 0; i-- )
            if ( !Rnm_ManObj(p, pObj, i)->fVisit )
                Rnm_ManJustifyPropFanout_rec( p, pObj, i, vSelect );
        Vec_IntPush( vSelect, Gia_ObjId(p->pGia, pObj) );
        return;
    }
    if ( (Gia_ObjIsCo(pObj) && f == p->pCex->iFrame) || Gia_ObjIsPo(p->pGia, pObj) )
        return;
    if ( Gia_ObjIsRi(p->pGia, pObj) )
    {
        pFanout = Gia_ObjRiToRo(p->pGia, pObj);
        if ( !Rnm_ManObj(p, pFanout, f+1)->fVisit )
            Rnm_ManJustifyPropFanout_rec( p, pFanout, f+1, vSelect );
        return;
    }
    assert( Gia_ObjIsRo(p->pGia, pObj) || Gia_ObjIsAnd(pObj) );
    Gia_ObjForEachFanoutStatic( p->pGia, pObj, pFanout, k )
    {
        Rnm_Obj_t * pRnmF;
        if ( pFanout->Value == 0 )
            continue;
        pRnmF = Rnm_ManObj(p, pFanout, f);
        if ( pRnmF->fPPi || pRnmF->fVisit )
            continue;
        if ( Gia_ObjIsCo(pFanout) )
        {
            Rnm_ManJustifyPropFanout_rec( p, pFanout, f, vSelect );
            continue;
        } 
        assert( Gia_ObjIsAnd(pFanout) );
        pRnm0 = Rnm_ManObj( p, Gia_ObjFanin0(pFanout), f );
        pRnm1 = Rnm_ManObj( p, Gia_ObjFanin1(pFanout), f );
        if ( ((pRnm0->Value ^ Gia_ObjFaninC0(pFanout)) == 0 && pRnm0->fVisit) ||
             ((pRnm1->Value ^ Gia_ObjFaninC1(pFanout)) == 0 && pRnm1->fVisit) || 
           ( ((pRnm0->Value ^ Gia_ObjFaninC0(pFanout)) == 1 && pRnm0->fVisit) && 
             ((pRnm1->Value ^ Gia_ObjFaninC1(pFanout)) == 1 && pRnm1->fVisit) ) )
           Rnm_ManJustifyPropFanout_rec( p, pFanout, f, vSelect );
    }
}
void Rnm_ManJustify_rec( Rnm_Man_t * p, Gia_Obj_t * pObj, int f, Vec_Int_t * vSelect )
{ 
    Rnm_Obj_t * pRnm = Rnm_ManObj( p, pObj, f );
    int i;//, Id = Gia_ObjId(p->pGia, pObj);
    if ( pRnm->fVisit )
        return;
    if ( p->fPropFanout )
        Rnm_ManJustifyPropFanout_rec( p, pObj, f, vSelect );
    else
    {
        pRnm->fVisit = 1;
        if ( Rnm_ManObj( p, pObj, 0 )->fVisit0 == 0 )
        {
            Rnm_ManObj( p, pObj, 0 )->fVisit0 = 1;
            p->nVisited++;
        }
    }
    if ( pRnm->fPPi )
    {
        assert( (int)pRnm->Prio > 0 );
        if ( p->fPropFanout )
        {
            for ( i = p->pCex->iFrame; i >= 0; i-- )
                if ( !Rnm_ManObj(p, pObj, i)->fVisit )
                    Rnm_ManJustifyPropFanout_rec( p, pObj, i, vSelect );
        }
        else
        {
            Vec_IntPush( vSelect, Gia_ObjId(p->pGia, pObj) );
//            for ( i = p->pCex->iFrame; i >= 0; i-- )
//                Rnm_ManObj(p, pObj, i)->fVisit = 1;
        }
        return;
    }
    if ( Gia_ObjIsPi(p->pGia, pObj) || Gia_ObjIsConst0(pObj) )
        return;
    if ( Gia_ObjIsRo(p->pGia, pObj) )
    {
        if ( f > 0 )
            Rnm_ManJustify_rec( p, Gia_ObjFanin0(Gia_ObjRoToRi(p->pGia, pObj)), f-1, vSelect );
        return;
    }
    if ( Gia_ObjIsAnd(pObj) )
    {
        Rnm_Obj_t * pRnm0 = Rnm_ManObj( p, Gia_ObjFanin0(pObj), f );
        Rnm_Obj_t * pRnm1 = Rnm_ManObj( p, Gia_ObjFanin1(pObj), f );
        if ( pRnm->Value == 1 )
        {
            if ( pRnm0->Prio > 0 )
                Rnm_ManJustify_rec( p, Gia_ObjFanin0(pObj), f, vSelect );
            if ( pRnm1->Prio > 0 )
                Rnm_ManJustify_rec( p, Gia_ObjFanin1(pObj), f, vSelect );
        }
        else // select one value
        {
            if ( (pRnm0->Value ^ Gia_ObjFaninC0(pObj)) == 0 && (pRnm1->Value ^ Gia_ObjFaninC1(pObj)) == 0 )
            {
                if ( pRnm0->Prio <= pRnm1->Prio ) // choice
                {
                    if ( pRnm0->Prio > 0 )
                        Rnm_ManJustify_rec( p, Gia_ObjFanin0(pObj), f, vSelect );
                }
                else
                {
                    if ( pRnm1->Prio > 0 )
                        Rnm_ManJustify_rec( p, Gia_ObjFanin1(pObj), f, vSelect );
                }
            }
            else if ( (pRnm0->Value ^ Gia_ObjFaninC0(pObj)) == 0 )
            {
                if ( pRnm0->Prio > 0 )
                    Rnm_ManJustify_rec( p, Gia_ObjFanin0(pObj), f, vSelect );
            }
            else if ( (pRnm1->Value ^ Gia_ObjFaninC1(pObj)) == 0 )
            {
                if ( pRnm1->Prio > 0 )
                    Rnm_ManJustify_rec( p, Gia_ObjFanin1(pObj), f, vSelect );
            }
            else assert( 0 );
        }
    }
    else assert( 0 );
}

/**Function*************************************************************

  Synopsis    [Performs refinement.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rnm_ManVerifyUsingTerSim( Gia_Man_t * p, Abc_Cex_t * pCex, Vec_Int_t * vMap, Vec_Int_t * vObjs, Vec_Int_t * vRes )
{
    Gia_Obj_t * pObj;
    int i, f, iBit = pCex->nRegs;
    Gia_ObjTerSimSet0( Gia_ManConst0(p) );
    for ( f = 0; f <= pCex->iFrame; f++, iBit += pCex->nPis )
    {
        Gia_ManForEachObjVec( vMap, p, pObj, i )
        {
            pObj->Value = Abc_InfoHasBit( pCex->pData, iBit + i );
            if ( !Gia_ObjIsPi(p, pObj) )
                Gia_ObjTerSimSetX( pObj );
            else if ( pObj->Value )
                Gia_ObjTerSimSet1( pObj );
            else
                Gia_ObjTerSimSet0( pObj );
        }
        Gia_ManForEachObjVec( vRes, p, pObj, i ) // vRes is subset of vMap
        {
            if ( pObj->Value )
                Gia_ObjTerSimSet1( pObj );
            else
                Gia_ObjTerSimSet0( pObj );
        }
        Gia_ManForEachObjVec( vObjs, p, pObj, i )
        {
            if ( Gia_ObjIsCo(pObj) )
                Gia_ObjTerSimCo( pObj );
            else if ( Gia_ObjIsAnd(pObj) )
                Gia_ObjTerSimAnd( pObj );
            else if ( f == 0 )
                Gia_ObjTerSimSet0( pObj );
            else
                Gia_ObjTerSimRo( p, pObj );
        }
    }
    Gia_ManForEachObjVec( vMap, p, pObj, i )
        pObj->Value = 0;
    pObj = Gia_ManPo( p, 0 );
    if ( !Gia_ObjTerSimGet1(pObj) )
        Abc_Print( 1, "\nRefinement verification has failed!!!\n" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rnm_ManPrintSelected( Rnm_Man_t * p, Vec_Int_t * vSelected )
{
    Gia_Obj_t * pObj;
    int i, Counter = 0;
    Gia_ManForEachObjVec( p->vMap, p->pGia, pObj, i )
    {
        if ( !Gia_ObjIsPi(p->pGia, pObj) ) // this is PPI
        {
            if ( Vec_IntFind(vSelected, Gia_ObjId(p->pGia, pObj)) >= 0 )
                printf( "1" ), Counter++;
            else
                printf( "0" );
        }
        else
            printf( "-" );
    }
    printf( " %3d\n", Counter );
}





/**Function*************************************************************

  Synopsis    [Perform structural analysis.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ga2_StructAnalize( Gia_Man_t * p, Vec_Int_t * vFront, Vec_Int_t * vInter, Vec_Int_t * vSelect )
{
    Vec_Int_t * vLeaves;
    Gia_Obj_t * pObj, * pFanin;
    int i, k;
    // clean labels
    Gia_ManForEachObj( p, pObj, i )
        pObj->fMark0 = pObj->fMark1 = 0;
    // label frontier
    Gia_ManForEachObjVec( vFront, p, pObj, i )
        pObj->fMark0 = 1, pObj->fMark1 = 0;
    // label objects
    Gia_ManForEachObjVec( vInter, p, pObj, i )
        pObj->fMark1 = 0, pObj->fMark1 = 1;
    // label selected
    Gia_ManForEachObjVec( vSelect, p, pObj, i )
        pObj->fMark1 = 1, pObj->fMark1 = 1;
    // explore selected
    printf( "\n" );
    Gia_ManForEachObjVec( vSelect, p, pObj, i )
    {
        printf( "Selected %6d : ", Gia_ObjId(p, pObj) );
        printf( "\n" );
        vLeaves = Ga2_ObjLeaves( p, pObj );
        Gia_ManForEachObjVec( vLeaves, p, pFanin, k )
        {
            printf( "    " );
            printf( "%6d ", Gia_ObjId(p, pFanin) );
            if ( pFanin->fMark0 && pFanin->fMark1 )
                printf( "select" );
            else if ( pFanin->fMark0 && !pFanin->fMark1 )
                printf( "front" );
            else if ( !pFanin->fMark0 &&  pFanin->fMark1 )
                printf( "internal" );
            else if ( !pFanin->fMark0 && !pFanin->fMark1 )
                printf( "new" );
            printf( "\n" );
        }
    }
}


/**Function*************************************************************

  Synopsis    [Finds essential objects.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Ga2_FilterSelected( Rnm_Man_t * p, Vec_Int_t * vSelect )
{
    Vec_Int_t * vNew, * vLeaves;
    Gia_Obj_t * pObj, * pFanin;
    int i, k, RetValue;//, Counters[3] = {0};
/*
    // check that selected are not visited
    Gia_ManForEachObjVec( vSelect, p->pGia, pObj, i )
        assert( Rnm_ManObj( p, pObj, 0 )->fVisit0 == 1 );
    Gia_ManForEachObjVec( p->vMap, p->pGia, pObj, i )
        if ( Vec_IntFind(vSelect, Gia_ObjId(p->pGia, pObj)) == -1 )
            assert( Rnm_ManObj( p, pObj, 0 )->fVisit0 == 0 );
*/

    // verify
//    Gia_ManForEachObj( p->pGia, pObj, i )
//        assert( Rnm_ObjCount(p, pObj) == 0 );

    // increment fanin counters
    Vec_IntClear( p->vFanins );
    Gia_ManForEachObjVec( vSelect, p->pGia, pObj, i )
    {
        vLeaves = Ga2_ObjLeaves( p->pGia, pObj );
        Gia_ManForEachObjVec( vLeaves, p->pGia, pFanin, k )
            if ( Rnm_ObjAddToCount(p, pFanin) == 0 )
                Vec_IntPush( p->vFanins, Gia_ObjId(p->pGia, pFanin) );
    }

    // find selected objects, which create potential constraints
    // - flop objects
    // - objects whose fanin belongs to the justified area
    // - objects whose fanins overlap
    // (these do not guantee reconvergence, but may potentially have it)
    // (other objects cannot have reconvergence, even if they are added)
    vNew = Vec_IntAlloc( 100 );
    Gia_ManForEachObjVec( vSelect, p->pGia, pObj, i )
    {
        if ( Gia_ObjIsRo(p->pGia, pObj) )
        {
            Vec_IntPush( vNew, Gia_ObjId(p->pGia, pObj) );
            continue;
        }
        vLeaves = Ga2_ObjLeaves( p->pGia, pObj );
        Gia_ManForEachObjVec( vLeaves, p->pGia, pFanin, k )
        {
            if ( Gia_ObjIsConst0(pFanin)
                 || (pFanin->Value && Rnm_ManObj(p, pFanin, 0)->fVisit0 == 1)
                 || Rnm_ObjCount(p, pFanin) > 1
               )
            {
                Vec_IntPush( vNew, Gia_ObjId(p->pGia, pObj) );
                break;
            }
        }
//        Gia_ManForEachObjVec( vLeaves, p->pGia, pFanin, k )
//        {
//            Counters[1] += (pFanin->Value && Rnm_ManObj( p, pFanin, 0 )->fVisit0 == 1);
//            Counters[2] += (Rnm_ObjCount(p, pFanin) > 1);
//        }
    }
    RetValue = Vec_IntUniqify( vNew );
    assert( RetValue == 0 );

//    printf( "\n*** Select = %5d. New = %5d.   Flops = %5d.  Visited = %5d.  Fanins = %5d.\n", 
//        Vec_IntSize(vSelect), Vec_IntSize(vNew), Counters[0], Counters[1], Counters[2] );

    // clear fanin counters
    Gia_ManForEachObjVec( p->vFanins, p->pGia, pObj, i )
        Rnm_ObjSetCount( p, pObj, 0 );
    return vNew;
}


/**Function*************************************************************

  Synopsis    [Computes the refinement for a given counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Rnm_ManRefine( Rnm_Man_t * p, Abc_Cex_t * pCex, Vec_Int_t * vMap, int fPropFanout, int fVerbose )
{
    int fVerify = 0;
    Vec_Int_t * vSelected = Vec_IntAlloc( 100 );
    Vec_Int_t * vNew;
    clock_t clk, clk2 = clock();
    int RetValue;
    p->nCalls++;
//    Gia_ManCleanValue( p->pGia );
    // initialize
    p->pCex = pCex;
    p->vMap = vMap;
    p->fPropFanout = fPropFanout;
    p->fVerbose    = fVerbose;
    // collects used objects
    Rnm_ManCollect( p );
    // initialize datastructure
    p->nObjsFrame = 1 + Vec_IntSize(vMap) + Vec_IntSize(p->vObjs);
    p->nObjs = p->nObjsFrame * (pCex->iFrame + 1);
    if ( p->nObjs > p->nObjsAlloc )
        p->pObjs = ABC_REALLOC( Rnm_Obj_t, p->pObjs, (p->nObjsAlloc = p->nObjs + 10000) );
    memset( p->pObjs, 0, sizeof(Rnm_Obj_t) * p->nObjs );
    // propagate priorities
    clk = clock();
    if ( Rnm_ManSensitize( p ) ) // the CEX is not a true CEX
    {
        p->timeFwd += clock() - clk;
        // select refinement
        clk = clock();
        p->nVisited = 0;
        Rnm_ManJustify_rec( p, Gia_ObjFanin0(Gia_ManPo(p->pGia, 0)), pCex->iFrame, vSelected );
        RetValue = Vec_IntUniqify( vSelected );
//        assert( RetValue == 0 );
        p->timeBwd += clock() - clk;
    }

    vNew = Ga2_FilterSelected( p, vSelected );
    if ( Vec_IntSize(vNew) > 0 )
    {
        Vec_IntFree( vSelected );
        vSelected = vNew;
    }
    else
    {
        Vec_IntFree( vNew );
//        printf( "\nBig refinement.\n" );
    }

    // clean values
    Rnm_ManCleanValues( p );

    // verify (empty) refinement
    if ( fVerify )
    {
        clk = clock();
        Rnm_ManVerifyUsingTerSim( p->pGia, p->pCex, p->vMap, p->vObjs, vSelected );
        p->timeVer += clock() - clk;
    }

//    printf( "\nOriginal (%d): \n", Vec_IntSize(p->vMap) );
//    Rnm_ManPrintSelected( p, vSelected );
        
//    Ga2_StructAnalize( p->pGia, vMap, p->vObjs, vSelected );
//    printf( "\nObjects = %5d.  Visited = %5d.\n", Vec_IntSize(p->vObjs), p->nVisited );

//    Vec_IntReverseOrder( vSelected );
    p->timeTotal += clock() - clk2;
    p->nRefines += Vec_IntSize(vSelected);
    return vSelected;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

