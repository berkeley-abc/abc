/**CFile****************************************************************

  FileName    [giaSweeper.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Incremental SAT sweeper.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaSweeper.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "sat/bsat/satSolver.h"

ABC_NAMESPACE_IMPL_START

/*

SAT sweeping/equivalence checking requires the following steps:
- Creating probes
  These APIs should be called for all internal points in the logic, which may be used as
      - nodes representing conditions to be used as constraints
      - nodes representing functions to be equivalence checked
      - nodes representing functions needed by the user at the end of SAT sweeping
  Creating new probe using Gia_ManCreateProbe():  int Gia_ManCreateProbe( Gia_Man_t * p, int iLit );
  Find existing probe using Gia_ManFindProbe():   int Gia_ManFindProbe( Gia_Man_t * p, int iLit );
      If probe with this literal (iLit) exists, this procedure increments its reference counter and returns it.
      If probe with this literal does not exist, it creates new probe and sets is reference counter to 1.
  Dereference probe using Gia_ManDerefProbe():    void Gia_ManDerefProbe( Gia_Man_t * p, int ProbeId );
      Dereferences probe with the given ID. If ref counter become 0, recycles the logic cone of the given probe.
      Recycling of probe IDs can be added later.
  Comments:
      - a probe is identified by its 0-based ID, which is returned by above procedures
- Adding/removing conditions on the current path by calling Gia_ManCondPush() and Gia_ManCondPop()
      extern void Gia_ManCondPush( Gia_Man_t * p, int ProbeId );
      extern void Gia_ManCondPop( Gia_Man_t * p );
- Performing equivalence checking by calling Gia_ManCheckConst() and Gia_ManCheckEquiv()
      extern int Gia_ManCheckConst( Gia_Man_t * p, int ProbeId, int Const1 ); // Const1 can be 0 or 1
      extern int Gia_ManCheckEquiv( Gia_Man_t * p, int ProbeId1, int ProbeId2 );
      (resource limits, such as the number of conflicts, will be controllable by dedicated GIA APIs)
- Extracting the resulting AIG to be returned to the user by calling Gia_ManExtractUserLogic()
      extern Gia_Man_t * Gia_ManExtractUserLogic( Gia_Man_t * p, int * ProbeIds, int nProbeIds );

*/

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Swp_Man_t_ Swp_Man_t;
struct Swp_Man_t_
{
    Gia_Man_t *    pGia;
    int            nBTLimit;
    Vec_Int_t *    vProbes;     // probes
    Vec_Int_t *    vProbRefs;   // probe reference counters
    Vec_Int_t *    vLit2Prob;   // mapping of literal into its probe
//    Vec_Int_t *    vFreeProb;   // recycled probe IDs
    Vec_Int_t *    vCondProbes; // conditions as probes
    Vec_Int_t *    vCondLits;   // conditions as literals
    // equivalence checking
    int            nSatVars;    // counter of SAT variables
    Vec_Int_t *    vId2Sat;     // mapping of Obj IDs into SAT vars
    sat_solver *   pSat;        // SAT solver 
    // statistics
    int            nSatCalls;
    int            nSatCallsSat;
    int            nSatCallsUnsat;
    int            nSatFails;
    int            nSatProofs;


};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////
    
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Swp_Man_t * Swp_ManStart( Gia_Man_t * pGia )
{
    Swp_Man_t * p;
    p = ABC_CALLOC( Swp_Man_t, 1 );
    p->pGia        = pGia;
    p->nBTLimit    = 1000;
    p->vProbes     = Vec_IntAlloc( 100 );
    p->vProbRefs   = Vec_IntAlloc( 100 );
    p->vLit2Prob   = Vec_IntStartFull( 10000 );
    p->vCondProbes = Vec_IntAlloc( 100 );
    p->vCondLits   = Vec_IntAlloc( 100 );
    pGia->pData    = p;
    return p;
}
static inline void Swp_ManStop( Gia_Man_t * pGia )
{
    Swp_Man_t * p = (Swp_Man_t *)pGia->pData;
    Vec_IntFree( p->vProbes );
    Vec_IntFree( p->vProbRefs );
    Vec_IntFree( p->vLit2Prob );
    Vec_IntFree( p->vCondProbes );
    Vec_IntFree( p->vCondLits );
    ABC_FREE( p );
    pGia->pData = NULL;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
// returns literal of the probe
int Gia_ManProbeLit( Gia_Man_t * p, int ProbeId )
{
    Swp_Man_t * pSwp = (Swp_Man_t *)p->pData;
    return Vec_IntEntry( pSwp->vProbes, ProbeId );
}
// create new probe
int Gia_ManCreateProbe( Gia_Man_t * p, int iLit )
{
    Swp_Man_t * pSwp = (Swp_Man_t *)p->pData;
    int ProbeId = Vec_IntSize(pSwp->vProbes);
    Vec_IntPush( pSwp->vProbes, iLit );
    Vec_IntPush( pSwp->vProbRefs, 1 );
    Vec_IntSetEntryFull( pSwp->vLit2Prob, iLit, ProbeId );
    return ProbeId;
}
// if probe with this literal (iLit) exists, this procedure increments its reference counter and returns it.
// if probe with this literal does not exist, it creates new probe and sets is reference counter to 1.
int Gia_ManFindProbe( Gia_Man_t * p, int iLit )
{
    Swp_Man_t * pSwp = (Swp_Man_t *)p->pData;
    if ( iLit >= Vec_IntSize(pSwp->vLit2Prob) || Vec_IntEntry(pSwp->vLit2Prob, iLit) >= 0 )
        return Vec_IntEntry(pSwp->vLit2Prob, iLit);
    return Gia_ManCreateProbe( p, iLit );
}
// dereferences the probe
void Gia_ManDerefProbe( Gia_Man_t * p, int ProbeId )
{
    Swp_Man_t * pSwp = (Swp_Man_t *)p->pData;
    assert( Vec_IntEntry(pSwp->vProbRefs, ProbeId) > 0 );
    Vec_IntAddToEntry( pSwp->vProbRefs, ProbeId, -1 );
    if ( Vec_IntEntry(pSwp->vProbRefs, ProbeId) == 0 )
    {
        int iLit = Gia_ManProbeLit( p, ProbeId );
        Vec_IntWriteEntry( pSwp->vLit2Prob, iLit, -1 );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCondPush( Gia_Man_t * p, int ProbeId )
{
    Swp_Man_t * pSwp = (Swp_Man_t *)p->pData;
    Vec_IntPush( pSwp->vCondProbes, ProbeId );
    Vec_IntPush( pSwp->vCondLits, Gia_ManProbeLit(p, ProbeId) );
}
int Gia_ManCondPop( Gia_Man_t * p )
{
    Swp_Man_t * pSwp = (Swp_Man_t *)p->pData;
    int ProbId = Vec_IntPop( pSwp->vCondProbes );
    Vec_IntPop( pSwp->vCondLits );
    return ProbId;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManExtract_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vObjIds )
{
    if ( !Gia_ObjIsAnd(pObj) )
        return;
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return;
    Gia_ObjSetTravIdCurrent(p, pObj);
    Gia_ManExtract_rec( p, Gia_ObjFanin0(pObj), vObjIds );
    Gia_ManExtract_rec( p, Gia_ObjFanin1(pObj), vObjIds );
    Vec_IntPush( vObjIds, Gia_ObjId(p, pObj) );
}
Gia_Man_t * Gia_ManExtractUserLogic( Gia_Man_t * p, int * pProbeIds, int nProbeIds )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    Vec_Int_t * vObjIds;
    int i;
    vObjIds = Vec_IntAlloc( 1000 );
    Gia_ManIncrementTravId( p );
    for ( i = 0; i < nProbeIds; i++ )
    {
        pObj = Gia_Lit2Obj( p, Gia_ManProbeLit(p, pProbeIds[i]) );
        Gia_ManExtract_rec( p, Gia_Regular(pObj), vObjIds );
    }
    // create new manager
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachPi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);
    Gia_ManForEachObjVec( vObjIds, p, pObj, i )
        pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Vec_IntFree( vObjIds );
    for ( i = 0; i < nProbeIds; i++ )
    {
        pObj = Gia_Lit2Obj( p, Gia_ManProbeLit(p, pProbeIds[i]) );
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(Gia_Regular(pObj)) ^ Gia_IsComplement(pObj) );
    }
    return pNew;
}




/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManCheckConst( Gia_Man_t * p, int ProbeId, int Const1 )
{
    return -1;
}

int Gia_ManCheckEquiv( Gia_Man_t * p, int ProbeId1, int ProbeId2 )
{
    return -1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END

