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
  Creating new probe using  Gia_SweeperProbeCreate(): int Gia_SweeperProbeCreate( Gia_Man_t * p, int iLit );
  Find existing probe using Gia_SweeperProbeFind():   int Gia_SweeperProbeFind( Gia_Man_t * p, int iLit );
      If probe with this literal (iLit) exists, this procedure increments its reference counter and returns it.
      If probe with this literal does not exist, it creates new probe and sets is reference counter to 1.
  Dereference probe using Gia_SweeperProbeDeref():    void Gia_SweeperProbeDeref( Gia_Man_t * p, int ProbeId );
      Dereferences probe with the given ID. If ref counter become 0, recycles the logic cone of the given probe.
      Recycling of probe IDs can be added later.
  Comments:
      - a probe is identified by its 0-based ID, which is returned by above procedures
      - GIA literal of the probe is returned by       int Gia_SweeperProbeLit( Gia_Man_t * p, int ProbeId )
- Adding/removing conditions on the current path by calling Gia_SweeperCondPush() and Gia_SweeperCondPop()
      extern void Gia_SweeperCondPush( Gia_Man_t * p, int ProbeId );
      extern void Gia_SweeperCondPop( Gia_Man_t * p );
- Performing equivalence checking by calling     int Gia_SweeperCheckEquiv( Gia_Man_t * pGia, int Probe1, int Probe2 )
      (resource limits, such as the number of conflicts, will be controllable by dedicated GIA APIs)
- The resulting AIG to be returned to the user by calling Gia_SweeperExtractUserLogic()
      Gia_Man_t * Gia_SweeperExtractUserLogic( Gia_Man_t * p, Vec_Int_t * vProbeIds, Vec_Ptr_t * vOutNames )

*/

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Swp_Man_t_ Swp_Man_t;
struct Swp_Man_t_
{
    Gia_Man_t *    pGia;        // GIA manager under construction
    int            nConfMax;    // conflict limit in seconds
    int            nTimeOut;    // runtime limit in seconds
    Vec_Int_t *    vProbes;     // probes
    Vec_Int_t *    vProbRefs;   // probe reference counters
    Vec_Int_t *    vLit2Prob;   // mapping of literal into its probe
//    Vec_Int_t *    vFreeProb;   // recycled probe IDs
    Vec_Int_t *    vCondProbes; // conditions as probes
    Vec_Int_t *    vCondAssump; // conditions as SAT solver literals
    // equivalence checking
    sat_solver *   pSat;        // SAT solver 
    Vec_Int_t *    vId2Lit;     // mapping of Obj IDs into SAT literal
    Vec_Int_t *    vFront;      // temporary frontier
    Vec_Int_t *    vFanins;     // temporary fanins
    Vec_Int_t *    vCexSwp;     // sweeper counter-example
    Vec_Int_t *    vCexUser;    // user-visible counter-example
    int            nSatVars;    // counter of SAT variables
    // statistics
    int            nSatCalls;
    int            nSatCallsSat;
    int            nSatCallsUnsat;
    int            nSatCallsUndec;
    int            nSatProofs;
    clock_t        timeStart;
    clock_t        timeTotal;
    clock_t        timeCnf;
    clock_t        timeSat;
    clock_t        timeSatSat;
    clock_t        timeSatUnsat;
    clock_t        timeSatUndec;
};

static inline int  Swp_ManObj2Lit( Swp_Man_t * p, int Id )              { return Vec_IntGetEntry( p->vId2Lit, Id );              }
static inline int  Swp_ManLit2Lit( Swp_Man_t * p, int Lit )             { assert( Vec_IntEntry(p->vId2Lit, Abc_Lit2Var(Lit)) ); return Abc_Lit2LitL( Vec_IntArray(p->vId2Lit), Lit );  }
static inline void Swp_ManSetObj2Lit( Swp_Man_t * p, int Id, int Lit )  { assert( Lit > 0 ); Vec_IntSetEntry( p->vId2Lit, Id, Lit );                }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////
    
/**Function*************************************************************

  Synopsis    [Creating/deleting the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Swp_Man_t * Swp_ManStart( Gia_Man_t * pGia )
{
    Swp_Man_t * p;
    int Lit;
    assert( pGia->pHTable != NULL );
    pGia->pData = p = ABC_CALLOC( Swp_Man_t, 1 );
    p->pGia         = pGia;
    p->nConfMax     = 1000;
    p->vProbes      = Vec_IntAlloc( 100 );
    p->vProbRefs    = Vec_IntAlloc( 100 );
    p->vLit2Prob    = Vec_IntStartFull( 10000 );
    p->vCondProbes  = Vec_IntAlloc( 100 );
    p->vCondAssump  = Vec_IntAlloc( 100 );
    p->vId2Lit      = Vec_IntAlloc( 10000 );
    p->vFront       = Vec_IntAlloc( 100 );
    p->vFanins      = Vec_IntAlloc( 100 );
    p->vCexSwp      = Vec_IntAlloc( 100 );
    p->pSat         = sat_solver_new();
    p->nSatVars     = 1;
    sat_solver_setnvars( p->pSat, 1000 );
    Swp_ManSetObj2Lit( p, 0, (Lit = Abc_Var2Lit(p->nSatVars++, 0)) );
    Lit = Abc_LitNot(Lit);
    sat_solver_addclause( p->pSat, &Lit, &Lit + 1 );
    p->timeStart    = clock();
    return p;
}
static inline void Swp_ManStop( Gia_Man_t * pGia )
{
    Swp_Man_t * p = (Swp_Man_t *)pGia->pData;
    sat_solver_delete( p->pSat );
    Vec_IntFree( p->vFanins );
    Vec_IntFree( p->vCexSwp );
    Vec_IntFree( p->vId2Lit );
    Vec_IntFree( p->vFront );
    Vec_IntFree( p->vProbes );
    Vec_IntFree( p->vProbRefs );
    Vec_IntFree( p->vLit2Prob );
    Vec_IntFree( p->vCondProbes );
    Vec_IntFree( p->vCondAssump );
    ABC_FREE( p );
    pGia->pData = NULL;
}
Gia_Man_t * Gia_SweeperStart( Gia_Man_t * pGia )
{
    if ( pGia == NULL )
        pGia = Gia_ManStart( 10000 );
    if ( pGia->pHTable == NULL )
        Gia_ManHashStart( pGia );
    Swp_ManStart( pGia );
    pGia->fSweeper = 1;
    return pGia;
}
void Gia_SweeperStop( Gia_Man_t * pGia )
{
    pGia->fSweeper = 0;
    Swp_ManStop( pGia );
    Gia_ManHashStop( pGia );
//    Gia_ManStop( pGia );
}
int Gia_SweeperIsRunning( Gia_Man_t * pGia )
{
    return (pGia->pData != NULL);
}
double Gia_SweeperMemUsage( Gia_Man_t * pGia )
{
    Swp_Man_t * p = (Swp_Man_t *)pGia->pData;
    double nMem = sizeof(Swp_Man_t);
    nMem += Vec_IntCap(p->vProbes);
    nMem += Vec_IntCap(p->vProbRefs);
    nMem += Vec_IntCap(p->vLit2Prob);
    nMem += Vec_IntCap(p->vCondProbes);
    nMem += Vec_IntCap(p->vCondAssump);
    nMem += Vec_IntCap(p->vId2Lit);
    nMem += Vec_IntCap(p->vFront);
    nMem += Vec_IntCap(p->vFanins);
    nMem += Vec_IntCap(p->vCexSwp);
    return 4.0 * nMem;
}
void Gia_SweeperPrintStats( Gia_Man_t * pGia )
{
    Swp_Man_t * p = (Swp_Man_t *)pGia->pData;
    double nMemSwp = Gia_SweeperMemUsage(pGia);
    double nMemGia = (double)Gia_ManObjNum(pGia)*(sizeof(Gia_Obj_t) + sizeof(int));
    double nMemSat = sat_solver_memory(p->pSat);
    double nMemTot = nMemSwp + nMemGia + nMemSat;
    printf( "SAT sweeper statistics:\n" );
    printf( "Memory usage:\n" );
    ABC_PRMP( "Sweeper         ", nMemSwp, nMemTot );
    ABC_PRMP( "AIG manager     ", nMemGia, nMemTot );
    ABC_PRMP( "SAT solver      ", nMemSat, nMemTot );
    ABC_PRMP( "TOTAL           ", nMemTot, nMemTot );
    printf( "Runtime usage:\n" );
    p->timeTotal = clock() - p->timeStart;
    ABC_PRTP( "CNF construction", p->timeCnf,      p->timeTotal );
    ABC_PRTP( "SAT solving     ", p->timeSat,      p->timeTotal );
    ABC_PRTP( "    Sat         ", p->timeSatSat,   p->timeTotal );
    ABC_PRTP( "    Unsat       ", p->timeSatUnsat, p->timeTotal );
    ABC_PRTP( "    Undecided   ", p->timeSatUndec, p->timeTotal );
    ABC_PRTP( "TOTAL RUNTIME   ", p->timeTotal,    p->timeTotal );
    printf( "GIA: " );
    Gia_ManPrintStats( pGia, 0, 0, 0 );
    printf( "SAT calls = %d. Sat = %d. Unsat = %d. Undecided = %d.  Proofs = %d.\n", 
        p->nSatCalls, p->nSatCallsSat, p->nSatCallsUnsat, p->nSatCallsUndec, p->nSatProofs );
    Sat_SolverPrintStats( stdout, p->pSat );
}

/**Function*************************************************************

  Synopsis    [Setting resource limits.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_SweeperSetConflictLimit( Gia_Man_t * p, int nConfMax )
{
    Swp_Man_t * pSwp = (Swp_Man_t *)p->pData;
    pSwp->nConfMax = nConfMax;
}

void Gia_SweeperSetRuntimeLimit( Gia_Man_t * p, int nSeconds )
{
    Swp_Man_t * pSwp = (Swp_Man_t *)p->pData;
    pSwp->nTimeOut = nSeconds;
}
Vec_Int_t * Gia_SweeperGetCex( Gia_Man_t * p )
{
    Swp_Man_t * pSwp = (Swp_Man_t *)p->pData;
    assert( pSwp->vCexUser == NULL || Vec_IntSize(pSwp->vCexUser) == Gia_ManPiNum(p) );
    return pSwp->vCexUser;
}
    
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
// create new probe
int Gia_SweeperProbeCreate( Gia_Man_t * p, int iLit )
{
    Swp_Man_t * pSwp = (Swp_Man_t *)p->pData;
    int ProbeId = Vec_IntSize(pSwp->vProbes);
    Vec_IntPush( pSwp->vProbes, iLit );
    Vec_IntPush( pSwp->vProbRefs, 1 );
    Vec_IntSetEntryFull( pSwp->vLit2Prob, iLit, ProbeId ); // consider hash table in the future
//printf( "Creating probe %d with literal %d.\n", ProbeId, iLit );
    return ProbeId;
}
// if probe with this literal (iLit) exists, this procedure increments its reference counter and returns it.
// if probe with this literal does not exist, it creates new probe and sets is reference counter to 1.
int Gia_SweeperProbeFind( Gia_Man_t * p, int iLit )
{
    Swp_Man_t * pSwp = (Swp_Man_t *)p->pData;
    if ( iLit < Vec_IntSize(pSwp->vLit2Prob) && Vec_IntEntry(pSwp->vLit2Prob, iLit) >= 0 )
        return Vec_IntEntry(pSwp->vLit2Prob, iLit);
    return Gia_SweeperProbeCreate( p, iLit );
}
// dereferences the probe
void Gia_SweeperProbeDeref( Gia_Man_t * p, int ProbeId )
{
    Swp_Man_t * pSwp = (Swp_Man_t *)p->pData;
    assert( Vec_IntEntry(pSwp->vProbRefs, ProbeId) > 0 );
    if ( Vec_IntAddToEntry( pSwp->vProbRefs, ProbeId, -1 ) == 0 )
    {
        int iLit = Gia_SweeperProbeLit( p, ProbeId );
        Vec_IntWriteEntry( pSwp->vLit2Prob, iLit, -1 );
        Vec_IntWriteEntry( pSwp->vProbes, ProbeId, 0 );
        // TODO: recycle probe ID
//printf( "Deleteing probe %d with literal %d.\n", ProbeId, iLit );
    }
}
// returns literal associated with the probe
int Gia_SweeperProbeLit( Gia_Man_t * p, int ProbeId )
{
    Swp_Man_t * pSwp = (Swp_Man_t *)p->pData;
    return Vec_IntEntry( pSwp->vProbes, ProbeId );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_SweeperCondPush( Gia_Man_t * p, int ProbeId )
{
    Swp_Man_t * pSwp = (Swp_Man_t *)p->pData;
    Vec_IntPush( pSwp->vCondProbes, ProbeId );
}
int Gia_SweeperCondPop( Gia_Man_t * p )
{
    Swp_Man_t * pSwp = (Swp_Man_t *)p->pData;
    return Vec_IntPop( pSwp->vCondProbes );
}
Vec_Int_t * Gia_SweeperCondVector( Gia_Man_t * p )
{
    Swp_Man_t * pSwp = (Swp_Man_t *)p->pData;
    return pSwp->vCondProbes;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Gia_ManExtract_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vObjIds )
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
Gia_Man_t * Gia_SweeperExtractUserLogic( Gia_Man_t * p, Vec_Int_t * vProbeIds, Vec_Ptr_t * vInNames, Vec_Ptr_t * vOutNames )
{
    Vec_Int_t * vObjIds, * vValues;
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    int i, ProbeId;
    assert( vInNames  == NULL || Gia_ManPiNum(p) == Vec_PtrSize(vInNames) );
    assert( vOutNames == NULL || Vec_IntSize(vProbeIds) == Vec_PtrSize(vOutNames) );
    // create new
    Gia_ManIncrementTravId( p );
    vObjIds = Vec_IntAlloc( 1000 );
    Vec_IntForEachEntry( vProbeIds, ProbeId, i )
    {
        pObj = Gia_Lit2Obj( p, Gia_SweeperProbeLit(p, ProbeId) );
        Gia_ManExtract_rec( p, Gia_Regular(pObj), vObjIds );
    }
    // create new manager
    pNew = Gia_ManStart( 1 + Gia_ManPiNum(p) + Vec_IntSize(vObjIds) + Vec_IntSize(vProbeIds) + 100 );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachPi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);
    // create internal nodes
    Gia_ManHashStart( pNew );
    vValues = Vec_IntAlloc( Vec_IntSize(vObjIds) );
    Gia_ManForEachObjVec( vObjIds, p, pObj, i )
    {
        Vec_IntPush( vValues, pObj->Value );
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    }
    Gia_ManHashStop( pNew );
    // create outputs
    Vec_IntForEachEntry( vProbeIds, ProbeId, i )
    {
        pObj = Gia_Lit2Obj( p, Gia_SweeperProbeLit(p, ProbeId) );
        Gia_ManAppendCo( pNew, Gia_Regular(pObj)->Value ^ Gia_IsComplement(pObj) );
    }
    // return the values back
    Gia_ManForEachPi( p, pObj, i )
        pObj->Value = 0;
    Gia_ManForEachObjVec( vObjIds, p, pObj, i )
        pObj->Value = Vec_IntEntry( vValues, i );
    Vec_IntFree( vObjIds );
    Vec_IntFree( vValues );
    // duplicated if needed
    if ( Gia_ManHasDangling(pNew) )
    {
        pNew = Gia_ManCleanup( pTemp = pNew );
        Gia_ManStop( pTemp );
    }
    // copy names if present
    if ( vInNames )
        pNew->vNamesIn = Vec_PtrDupStr( vInNames );
    if ( vOutNames )
        pNew->vNamesOut = Vec_PtrDupStr( vOutNames );
    return pNew;
}


/**Function*************************************************************

  Synopsis    [Addes clauses to the solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Gia_ManAddClausesMux( Swp_Man_t * p, Gia_Obj_t * pNode )
{
    Gia_Obj_t * pNodeI, * pNodeT, * pNodeE;
    int pLits[4], LitF, LitI, LitT, LitE, RetValue;
    assert( !Gia_IsComplement( pNode ) );
    assert( Gia_ObjIsMuxType( pNode ) );
    // get nodes (I = if, T = then, E = else)
    pNodeI = Gia_ObjRecognizeMux( pNode, &pNodeT, &pNodeE );
    // get the Litiable numbers
    LitF = Swp_ManLit2Lit( p, Gia_Obj2Lit(p->pGia,pNode) );
    LitI = Swp_ManLit2Lit( p, Gia_Obj2Lit(p->pGia,pNodeI) );
    LitT = Swp_ManLit2Lit( p, Gia_Obj2Lit(p->pGia,pNodeT) );
    LitE = Swp_ManLit2Lit( p, Gia_Obj2Lit(p->pGia,pNodeE) );

    // f = ITE(i, t, e)

    // i' + t' + f
    // i' + t  + f'
    // i  + e' + f
    // i  + e  + f'

    // create four clauses
    pLits[0] = Abc_LitNotCond(LitI, 1);
    pLits[1] = Abc_LitNotCond(LitT, 1);
    pLits[2] = Abc_LitNotCond(LitF, 0);
    RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 3 );
    assert( RetValue );
    pLits[0] = Abc_LitNotCond(LitI, 1);
    pLits[1] = Abc_LitNotCond(LitT, 0);
    pLits[2] = Abc_LitNotCond(LitF, 1);
    RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 3 );
    assert( RetValue );
    pLits[0] = Abc_LitNotCond(LitI, 0);
    pLits[1] = Abc_LitNotCond(LitE, 1);
    pLits[2] = Abc_LitNotCond(LitF, 0);
    RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 3 );
    assert( RetValue );
    pLits[0] = Abc_LitNotCond(LitI, 0);
    pLits[1] = Abc_LitNotCond(LitE, 0);
    pLits[2] = Abc_LitNotCond(LitF, 1);
    RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 3 );
    assert( RetValue );

    // two additional clauses
    // t' & e' -> f'
    // t  & e  -> f

    // t  + e   + f'
    // t' + e'  + f

    if ( LitT == LitE )
    {
//        assert( fCompT == !fCompE );
        return;
    }

    pLits[0] = Abc_LitNotCond(LitT, 0);
    pLits[1] = Abc_LitNotCond(LitE, 0);
    pLits[2] = Abc_LitNotCond(LitF, 1);
    RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 3 );
    assert( RetValue );
    pLits[0] = Abc_LitNotCond(LitT, 1);
    pLits[1] = Abc_LitNotCond(LitE, 1);
    pLits[2] = Abc_LitNotCond(LitF, 0);
    RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 3 );
    assert( RetValue );
}

/**Function*************************************************************

  Synopsis    [Addes clauses to the solver.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Gia_ManAddClausesSuper( Swp_Man_t * p, Gia_Obj_t * pNode, Vec_Int_t * vSuper )
{
    int i, RetValue, Lit, LitNode, pLits[2];
    assert( !Gia_IsComplement(pNode) );
    assert( Gia_ObjIsAnd( pNode ) );
    // suppose AND-gate is A & B = C
    // add !A => !C   or   A + !C
    // add !B => !C   or   B + !C
    LitNode = Swp_ManLit2Lit( p, Gia_Obj2Lit(p->pGia,pNode) );
    Vec_IntForEachEntry( vSuper, Lit, i )
    {
        pLits[0] = Swp_ManLit2Lit( p, Lit );
        pLits[1] = Abc_LitNot( LitNode );
        RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 2 );
        assert( RetValue );
        // update literals
        Vec_IntWriteEntry( vSuper, i, Abc_LitNot(pLits[0]) );
    }
    // add A & B => C   or   !A + !B + C
    Vec_IntPush( vSuper, LitNode );
    RetValue = sat_solver_addclause( p->pSat, Vec_IntArray(vSuper), Vec_IntArray(vSuper) + Vec_IntSize(vSuper) );
    assert( RetValue );
    (void) RetValue;
}


/**Function*************************************************************

  Synopsis    [Collects the supergate.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Gia_ManCollectSuper_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vSuper )
{
    // stop at complements, shared, PIs, and MUXes
    if ( Gia_IsComplement(pObj) || pObj->fMark1 || Gia_ObjIsCi(pObj) || Gia_ObjIsMuxType(pObj) )
    {
        Vec_IntPushUnique( vSuper, Gia_Obj2Lit(p, pObj) );
        return;
    }
    Gia_ManCollectSuper_rec( p, Gia_ObjChild0(pObj), vSuper );
    Gia_ManCollectSuper_rec( p, Gia_ObjChild1(pObj), vSuper );
}
static void Gia_ManCollectSuper( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vSuper )
{
    assert( !Gia_IsComplement(pObj) );
    assert( Gia_ObjIsAnd(pObj) );
    Vec_IntClear( vSuper );
    Gia_ManCollectSuper_rec( p, Gia_ObjChild0(pObj), vSuper );
    Gia_ManCollectSuper_rec( p, Gia_ObjChild1(pObj), vSuper );
}

/**Function*************************************************************

  Synopsis    [Updates the solver clause database.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Gia_ManObjAddToFrontier( Swp_Man_t * p, int Id, Vec_Int_t * vFront )
{
    Gia_Obj_t * pObj;
    if ( Id == 0 || Swp_ManObj2Lit(p, Id) )
        return;
    pObj = Gia_ManObj( p->pGia, Id );
    Swp_ManSetObj2Lit( p, Id, Abc_Var2Lit(p->nSatVars++, pObj->fPhase) );
    sat_solver_setnvars( p->pSat, p->nSatVars + 100 );
    if ( Gia_ObjIsAnd(pObj) )
        Vec_IntPush( vFront, Id );
}
static void Gia_ManCnfNodeAddToSolver( Swp_Man_t * p, int NodeId )
{
    Gia_Obj_t * pNode;
    int i, k, Id, Lit;
    clock_t clk;
    // quit if CNF is ready
    if ( NodeId == 0 || Swp_ManObj2Lit(p, NodeId) )
        return;
clk = clock();
    // start the frontier
    Vec_IntClear( p->vFront );
    Gia_ManObjAddToFrontier( p, NodeId, p->vFront );
    // explore nodes in the frontier
    Gia_ManForEachObjVec( p->vFront, p->pGia, pNode, i )
    {
        // create the supergate
        assert( Swp_ManObj2Lit(p, Gia_ObjId(p->pGia, pNode)) );
        if ( Gia_ObjIsMuxType(pNode) )
        {
            Vec_IntClear( p->vFanins );
            Vec_IntPushUnique( p->vFanins, Gia_ObjFaninId0p( p->pGia, Gia_ObjFanin0(pNode) ) );
            Vec_IntPushUnique( p->vFanins, Gia_ObjFaninId0p( p->pGia, Gia_ObjFanin1(pNode) ) );
            Vec_IntPushUnique( p->vFanins, Gia_ObjFaninId1p( p->pGia, Gia_ObjFanin0(pNode) ) );
            Vec_IntPushUnique( p->vFanins, Gia_ObjFaninId1p( p->pGia, Gia_ObjFanin1(pNode) ) );
            Vec_IntForEachEntry( p->vFanins, Id, k )
                Gia_ManObjAddToFrontier( p, Id, p->vFront );
            Gia_ManAddClausesMux( p, pNode );
        }
        else
        {
            Gia_ManCollectSuper( p->pGia, pNode, p->vFanins );
            Vec_IntForEachEntry( p->vFanins, Lit, k )
                Gia_ManObjAddToFrontier( p, Abc_Lit2Var(Lit), p->vFront );
            Gia_ManAddClausesSuper( p, pNode, p->vFanins );
        }
        assert( Vec_IntSize(p->vFanins) > 1 );
    }
p->timeCnf += clock() - clk;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Gia_ManGetCex( Gia_Man_t * pGia, Vec_Int_t * vId2Lit, sat_solver * pSat, Vec_Int_t * vCex )
{
    Gia_Obj_t * pObj;
    int i, LitSat, Value;
    Vec_IntClear( vCex );
    Gia_ManForEachPi( pGia, pObj, i )
    {
        LitSat = Vec_IntEntry( vId2Lit, Gia_ObjId(pGia, pObj) );
        if ( LitSat == 0 )
        {
            Vec_IntPush( vCex, 2 );
            continue;
        }
        assert( LitSat > 0 );
        Value = sat_solver_var_value(pSat, Abc_Lit2Var(LitSat)) ^ Abc_LitIsCompl(LitSat);
        Vec_IntPush( vCex, Value );
    }
    return vCex;
}

/**Function*************************************************************

  Synopsis    [Runs equivalence test for probes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_SweeperCheckEquiv( Gia_Man_t * pGia, int Probe1, int Probe2 )
{
    Swp_Man_t * p = (Swp_Man_t *)pGia->pData;
    int iLitOld, iLitNew, iLitAig, pLitsSat[2], RetValue, RetValue1, ProbeId, i;
    clock_t clk;
    p->nSatCalls++;
    assert( p->pSat != NULL );
    p->vCexUser = NULL;

    // get the literals
    iLitOld = Gia_SweeperProbeLit( pGia, Probe1 );
    iLitNew = Gia_SweeperProbeLit( pGia, Probe2 );
    // if the literals are identical, the probes are equivalent
    if ( iLitOld == iLitNew )
        return 1;
    // if the literals are opposites, the probes are not equivalent
    if ( Abc_LitRegular(iLitOld) == Abc_LitRegular(iLitNew) )
    {
        Vec_IntFill( p->vCexSwp, Gia_ManPiNum(pGia), 2 );
        p->vCexUser = p->vCexSwp;
        return 0;
    }
    // order the literals
    if ( iLitOld < iLitNew )
        ABC_SWAP( int, iLitOld, iLitNew );
    assert( iLitOld > iLitNew );

    // create logic cones and the array of assumptions
    Vec_IntClear( p->vCondAssump );
    Vec_IntForEachEntry( p->vCondProbes, ProbeId, i )
    {
        iLitAig = Gia_SweeperProbeLit( pGia, ProbeId );
        Gia_ManCnfNodeAddToSolver( p, Abc_Lit2Var(iLitAig) );
        Vec_IntPush( p->vCondAssump, Swp_ManLit2Lit(p, iLitAig) );
    }
    Gia_ManCnfNodeAddToSolver( p, Abc_Lit2Var(iLitOld) );
    Gia_ManCnfNodeAddToSolver( p, Abc_Lit2Var(iLitNew) );
    sat_solver_compress( p->pSat );

    // set the SAT literals
    pLitsSat[0] = Swp_ManLit2Lit( p, iLitOld );
    pLitsSat[1] = Swp_ManLit2Lit( p, iLitNew );

    // solve under assumptions
    // A = 1; B = 0     OR     A = 1; B = 1 
    Vec_IntPush( p->vCondAssump, pLitsSat[0] );
    Vec_IntPush( p->vCondAssump, Abc_LitNot(pLitsSat[1]) );

    // set runtime limit for this call
    if ( p->nTimeOut )
        sat_solver_set_runtime_limit( p->pSat, p->nTimeOut * CLOCKS_PER_SEC + clock() );

clk = clock();
    RetValue1 = sat_solver_solve( p->pSat, Vec_IntArray(p->vCondAssump), Vec_IntArray(p->vCondAssump) + Vec_IntSize(p->vCondAssump), 
        (ABC_INT64_T)p->nConfMax, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
    Vec_IntShrink( p->vCondAssump, Vec_IntSize(p->vCondAssump) - 2 );
p->timeSat += clock() - clk;
    if ( RetValue1 == l_False )
    {
        pLitsSat[0] = Abc_LitNot( pLitsSat[0] );
        RetValue = sat_solver_addclause( p->pSat, pLitsSat, pLitsSat + 2 );
        assert( RetValue );
        pLitsSat[0] = Abc_LitNot( pLitsSat[0] );
p->timeSatUnsat += clock() - clk;
        p->nSatCallsUnsat++;
    }
    else if ( RetValue1 == l_True )
    {
        p->vCexUser = Gia_ManGetCex( p->pGia, p->vId2Lit, p->pSat, p->vCexSwp );
p->timeSatSat += clock() - clk;
        p->nSatCallsSat++;
        return 0;
    }
    else // if ( RetValue1 == l_Undef )
    {
p->timeSatUndec += clock() - clk;
        p->nSatCallsUndec++;
        return -1;
    }

    // if the old node was constant 0, we already know the answer
    if ( Gia_ManIsConstLit(iLitNew) )
    {
        p->nSatProofs++;
        return 1;
    }

    // solve under assumptions
    // A = 0; B = 1     OR     A = 0; B = 0 
    Vec_IntPush( p->vCondAssump, Abc_LitNot(pLitsSat[0]) );
    Vec_IntPush( p->vCondAssump, pLitsSat[1] );

clk = clock();
    RetValue1 = sat_solver_solve( p->pSat, Vec_IntArray(p->vCondAssump), Vec_IntArray(p->vCondAssump) + Vec_IntSize(p->vCondAssump), 
        (ABC_INT64_T)p->nConfMax, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
    Vec_IntShrink( p->vCondAssump, Vec_IntSize(p->vCondAssump) - 2 );
p->timeSat += clock() - clk;
    if ( RetValue1 == l_False )
    {
        pLitsSat[1] = Abc_LitNot( pLitsSat[1] );
        RetValue = sat_solver_addclause( p->pSat, pLitsSat, pLitsSat + 2 );
        assert( RetValue );
        pLitsSat[1] = Abc_LitNot( pLitsSat[1] );
p->timeSatUnsat += clock() - clk;
        p->nSatCallsUnsat++;
    }
    else if ( RetValue1 == l_True )
    {
        p->vCexUser = Gia_ManGetCex( p->pGia, p->vId2Lit, p->pSat, p->vCexSwp );
p->timeSatSat += clock() - clk;
        p->nSatCallsSat++;
        return 0;
    }
    else // if ( RetValue1 == l_Undef )
    {
p->timeSatUndec += clock() - clk;
        p->nSatCallsUndec++;
        return -1;
    }
    // return SAT proof
    p->nSatProofs++;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the set of conditions is UNSAT (0 if SAT; -1 if undecided).]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_SweeperCondCheckUnsat( Gia_Man_t * pGia )
{
    Swp_Man_t * p = (Swp_Man_t *)pGia->pData;
    int RetValue, ProbeId, iLitAig, i;
    clock_t clk;
    assert( p->pSat != NULL );
    p->nSatCalls++;
    p->vCexUser = NULL;

    // create logic cones and the array of assumptions
    Vec_IntClear( p->vCondAssump );
    Vec_IntForEachEntry( p->vCondProbes, ProbeId, i )
    {
        iLitAig = Gia_SweeperProbeLit( pGia, ProbeId );
        Gia_ManCnfNodeAddToSolver( p, Abc_Lit2Var(iLitAig) );
        Vec_IntPush( p->vCondAssump, Swp_ManLit2Lit(p, iLitAig) );
    }
    sat_solver_compress( p->pSat );

    // set runtime limit for this call
    if ( p->nTimeOut )
        sat_solver_set_runtime_limit( p->pSat, p->nTimeOut * CLOCKS_PER_SEC + clock() );

clk = clock();
    RetValue = sat_solver_solve( p->pSat, Vec_IntArray(p->vCondAssump), Vec_IntArray(p->vCondAssump) + Vec_IntSize(p->vCondAssump), 
        (ABC_INT64_T)p->nConfMax, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
p->timeSat += clock() - clk;
    if ( RetValue == l_False )
    {
        assert( Vec_IntSize(p->vCondProbes) > 0 );
p->timeSatUnsat += clock() - clk;
        p->nSatCallsUnsat++;
        p->nSatProofs++;
        return 1;
    }
    else if ( RetValue == l_True )
    {
        p->vCexUser = Gia_ManGetCex( p->pGia, p->vId2Lit, p->pSat, p->vCexSwp );
p->timeSatSat += clock() - clk;
        p->nSatCallsSat++;
        return 0;
    }
    else // if ( RetValue1 == l_Undef )
    {
p->timeSatUndec += clock() - clk;
        p->nSatCallsUndec++;
        return -1;
    }
}

/**Function*************************************************************

  Synopsis    [Performs grafting from another manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_SweeperGraft( Gia_Man_t * pDst, Vec_Int_t * vProbes, Gia_Man_t * pSrc )
{
    Vec_Int_t * vOutLits;
    Gia_Obj_t * pObj;
    int i;
    assert( Gia_SweeperIsRunning(pDst) );
    if ( vProbes )
        assert( Vec_IntSize(vProbes) == Gia_ManPiNum(pSrc) );
    else
        assert( Gia_ManPiNum(pDst) == Gia_ManPiNum(pSrc) );
    Gia_ManForEachPi( pSrc, pObj, i )
        pObj->Value = Gia_SweeperProbeLit( pDst, vProbes ? Vec_IntEntry(vProbes, i) : Gia_Obj2Lit(pDst,Gia_ManPi(pDst, i)) );
    Gia_ManForEachAnd( pSrc, pObj, i )
        pObj->Value = Gia_ManHashAnd( pDst, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    vOutLits = Vec_IntAlloc( Gia_ManPoNum(pSrc) );
    Gia_ManForEachPo( pSrc, pObj, i )
        Vec_IntPush( vOutLits, Gia_ObjFanin0Copy(pObj) );
    return vOutLits;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_SweeperGen64Patterns( Gia_Man_t * pGiaCond, Vec_Wrd_t * vSim )
{
    Vec_Int_t * vCex;
    int i, k;
    for ( i = 0; i < 64; i++ )
    {
        if ( Gia_SweeperCondCheckUnsat( pGiaCond ) != 0 )
            return 0;
        vCex = Gia_SweeperGetCex( pGiaCond );
        for ( k = 0; k < Gia_ManPiNum(pGiaCond); k++ )
        {
            if ( Vec_IntEntry(vCex, k) )
                Abc_InfoXorBit( (unsigned *)Vec_WrdEntryP(vSim, i), k );
            printf( "%d", Vec_IntEntry(vCex, k) );
        }
        printf( "\n" );
    }
    return 1;
}
int Gia_SweeperSimulate( Gia_Man_t * p, Vec_Wrd_t * vSim )
{
    Gia_Obj_t * pObj;
    word Sim, Sim0, Sim1;
    int i, Count = 0;
    assert( Vec_WrdEntry(vSim, 0) == 0 );
//    assert( Vec_WrdEntry(vSim, 1) != 0 ); // may not hold
    Gia_ManForEachAnd( p, pObj, i )
    {
        Sim0 = Vec_WrdEntry( vSim, Gia_ObjFaninId0p( p, pObj ) );
        Sim1 = Vec_WrdEntry( vSim, Gia_ObjFaninId1p( p, pObj ) );
        Sim  = (Gia_ObjFaninC0(pObj) ? ~Sim0 : Sim0) & (Gia_ObjFaninC1(pObj) ? ~Sim1 : Sim1);
        Vec_WrdWriteEntry( vSim, i, Sim );
        if ( pObj->fMark0 == 1 ) // considered
            continue;
        if ( pObj->fMark1 == 1 ) // non-constant
            continue;
        if ( (pObj->fPhase ? ~Sim : Sim) != 0 )
        {
            pObj->fMark1 = 1;
            Count++;
        }
    }
    return Count;
}

/**Function*************************************************************

  Synopsis    [Performs conditional sweeping of the cone.]

  Description [Returns the result as a new GIA manager with as many inputs 
  as the original manager and as many outputs as there are logic cones.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_SweeperSweepInt( Gia_Man_t * pGiaCond, Gia_Man_t * pGiaOuts, Vec_Wrd_t * vSim )
{
}
Gia_Man_t * Gia_SweeperSweep( Gia_Man_t * p, Vec_Int_t * vProbeOuts )
{
    Gia_Man_t * pGiaCond, * pGiaOuts;
    Vec_Int_t * vProbeConds;
    Vec_Wrd_t * vSim;
    Gia_Obj_t * pObj;
    int i, Count;
    // sweeper is running
    assert( Gia_SweeperIsRunning(p) );
    // extract conditions and logic cones
    vProbeConds = Gia_SweeperCondVector( p );
    pGiaCond = Gia_SweeperExtractUserLogic( p, vProbeConds, NULL, NULL );
    pGiaOuts = Gia_SweeperExtractUserLogic( p, vProbeOuts, NULL, NULL );
    Gia_ManSetPhase( pGiaOuts );
    // start the sweeper for the conditions
    Gia_SweeperStart( pGiaCond );
    Gia_ManForEachPo( pGiaCond, pObj, i )
        Gia_SweeperCondPush( pGiaCond, Gia_SweeperProbeCreate(pGiaCond, Gia_ObjFaninLit0p(pGiaCond, pObj)) );
    // generate 64 patterns that satisfy the conditions
    vSim = Vec_WrdStart( Gia_ManObjNum(pGiaOuts) );
    Gia_SweeperGen64Patterns( pGiaCond, vSim );
    Count = Gia_SweeperSimulate( pGiaOuts, vSim );
    printf( "Disproved %d nodes.\n", Count );

    // consider the remaining ones
//    Gia_SweeperSweepInt( pGiaCond, pGiaOuts, vSim );
    Vec_WrdFree( vSim );
    Gia_ManStop( pGiaOuts );
    Gia_SweeperStop( pGiaCond );
    return pGiaCond;
}

/**Function*************************************************************

  Synopsis    [Procedure to perform conditional fraig sweeping on separate logic cones..]

  Description [The procedure takes GIA with the sweeper defined. The sweeper
  is assumed to have some conditions currently pushed, which will be used
  as constraints for fraig sweeping. The second argument (vProbes) contains
  the array of probe IDs pointing to the user's logic cones to be SAT swept.
  Finally, the optional command line (pCommLine) is an ABC command line
  to be applied to the resulting GIA after SAT sweeping before it is 
  grafted back into the original GIA manager. The return value is the array
  of literals in the original GIA manager, corresponding to the user's
  logic cones after sweeping, synthesis and grafting.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_SweeperFraig( Gia_Man_t * p, Vec_Int_t * vProbes, char * pCommLime )
{
    Gia_Man_t * pNew;
    Vec_Int_t * vLits;
    // sweeper is running
    assert( Gia_SweeperIsRunning(p) );
    // sweep the logic
    pNew = Gia_SweeperSweep( p, vProbes );
    // execute command line
    if ( pCommLime )
    {
    // set pNew to be current GIA in ABC
    // execute command line pCommLine using Abc_CmdCommandExecute()
    // get pNew to be current GIA in ABC     
    }
    vLits = Gia_SweeperGraft( p, NULL, pNew );
    Gia_ManStop( pNew );
    return vLits;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManCreateAndGate( Gia_Man_t * p, Vec_Int_t * vLits )
{
    if ( Vec_IntSize(vLits) == 0 )
        return 0;
    while ( Vec_IntSize(vLits) > 1 )
    {
        int i, k = 0, Lit1, Lit2, LitRes;
        Vec_IntForEachEntryDouble( vLits, Lit1, Lit2, i )
        {
            LitRes = Gia_ManHashAnd( p, Lit1, Lit2 );
            Vec_IntWriteEntry( vLits, k++, LitRes );
        }
        if ( Vec_IntSize(vLits) & 1 )
            Vec_IntWriteEntry( vLits, k++, Vec_IntEntryLast(vLits) );
        Vec_IntShrink( vLits, k );
    }
    assert( Vec_IntSize(vLits) == 1 );
    return Vec_IntEntry(vLits, 0);
}

/**Function*************************************************************

  Synopsis    [Sweeper sweeper test.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_SweeperFraigTest( Gia_Man_t * p, int nWords, int nConfs, int fVerbose )
{
    Gia_Man_t * pGia;
    Gia_Obj_t * pObj;
    Vec_Int_t * vLits, * vOuts;
    int i, k, Lit;

    // create sweeper
    Gia_SweeperStart( p );

    // create 1-hot constraint
    vLits = Vec_IntAlloc( 1000 );
    for ( i = 0; i < Gia_ManPiNum(p); i++ )
        for ( k = i+1; k < Gia_ManPiNum(p); k++ )
        {
            int Lit0 = Gia_Obj2Lit(p, Gia_ManPi(p, i));
            int Lit1 = Gia_Obj2Lit(p, Gia_ManPi(p, k));
            Vec_IntPush( vLits, Abc_LitNot(Gia_ManHashAnd(p, Lit0, Lit1)) );
        }
    Lit = 0;
    for ( i = 0; i < Gia_ManPiNum(p); i++ )
        Lit = Gia_ManHashOr( p, Lit, Gia_Obj2Lit(p, Gia_ManPi(p, i)) );
    Vec_IntPush( vLits, Lit );
    Gia_SweeperCondPush( p, Gia_SweeperProbeCreate( p, Gia_ManCreateAndGate( p, vLits ) ) );
    Vec_IntFree( vLits );
//Gia_ManPrint( p );

    // create outputs
    vOuts = Vec_IntAlloc( Gia_ManPoNum(p) );
    Gia_ManForEachPo( p, pObj, i )
        Vec_IntPush( vOuts, Gia_SweeperProbeCreate( p,  Gia_ObjFaninLit0p(p, pObj) ) );

    // perform the sweeping
    pGia = Gia_SweeperSweep( p, vOuts );
    Vec_IntFree( vOuts );

    Gia_SweeperStop( p );
    return pGia;
}

/**Function*************************************************************

  Synopsis    [Sweeper cleanup.]

  Description [Returns new GIA with sweeper defined, which is the same
  as the original sweeper, with all the dangling logic removed and SAT 
  solver restarted. The probe IDs are guaranteed to have the same logic
  functions as in the original manager.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_SweeperCleanup( Gia_Man_t * p, char * pCommLime )
{
    return NULL;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END

