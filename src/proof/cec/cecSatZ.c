/**CFile****************************************************************

  FileName    [cecSatZ.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [SAT sweeping with cached local proofs.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cecSatZ.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig/gia/gia.h"
#include "misc/util/utilTruth.h"
#include "cec.h"
#include "base/abc/abc.h"
#include <limits.h>

#include "sat/glucose3/AbcGlucose3.h"

#define sat_solver                         bmcg3_sat_solver
#define sat_solver_start                   bmcg3_sat_solver_start
#define sat_solver_stop                    bmcg3_sat_solver_stop
#define sat_solver_addclause               bmcg3_sat_solver_addclause
#define sat_solver_add_and                 bmcg3_sat_solver_add_and
#define sat_solver_add_xor                 bmcg3_sat_solver_add_xor
#define sat_solver_addvar                  bmcg3_sat_solver_addvar
#define sat_solver_read_cex_varvalue       bmcg3_sat_solver_read_cex_varvalue
#define sat_solver_reset                   bmcg3_sat_solver_reset
#define sat_solver_set_conflict_budget     bmcg3_sat_solver_set_conflict_budget
#define sat_solver_conflictnum             bmcg3_sat_solver_conflictnum
#define sat_solver_solve                   bmcg3_sat_solver_solve
#define sat_solver_read_cex                bmcg3_sat_solver_read_cex
#define sat_solver_jftr                    bmcg3_sat_solver_jftr
#define sat_solver_set_jftr                bmcg3_sat_solver_set_jftr
#define sat_solver_set_var_fanin_lit       bmcg3_sat_solver_set_var_fanin_lit
#define sat_solver_start_new_round         bmcg3_sat_solver_start_new_round
#define sat_solver_mark_cone               bmcg3_sat_solver_mark_cone

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// Derived from cecSatG2.c: simulation/refinement and circuit SAT encoding.
// Canonical cone programs retain reconvergence and input polarity. Cache hits
// compare the entire program, so hashes alone never justify a merge. SAT models
// are reused only for complete cones; UNSAT abstractions are valid for any
// boundary interpretation. An exhausted budget is a scheduling hint, not a proof.
// Sparse construction visits the transitive fanin of all remaining candidates;
// export copies every other node in the original topological order.

enum { CECZ_PROBE_DEPTH = 8, CECZ_CONE_DEPTH = 4096, CECZ_CONE_LIMIT = 65536,
       CECZ_CONE_CAPACITY = CECZ_CONE_LIMIT + 2*CECZ_CONE_DEPTH + 2,
       CECZ_RECYCLE_CONFLICTS = 500,
       CECZ_BATCH_SIZE = 8, CECZ_BATCH_WORK = 8,
       CECZ_SIM_MIN_SPLITS = 16, CECZ_SIM_SPLIT_RATIO = 100000,
       CECZ_PATTERN_LARGE = 512, CECZ_HASH_CLASS_MAX = 4,
       CECZ_PATTERN_BACKTRACKS = 4, CECZ_PATTERN_YIELD = 32,
       CECZ_PATTERN_WORK_RATIO = 128, CECZ_PATTERN_ROUND_WORK = 32,
       CECZ_PATTERN_MIN_TRIES = 256 };

// Shared state for one guided justification, including bounded branch retries.
typedef struct CecZ_Gen_t_ CecZ_Gen_t;
struct CecZ_Gen_t_
{
    Gia_Man_t * pAig;
    Vec_Int_t * vPat;
    Vec_Int_t * vVisit;
    int nBacktracks;
    word nDiscarded;
};

// SAT solving manager
typedef struct CecZ_Man_t_ CecZ_Man_t;
struct CecZ_Man_t_
{
    Cec_ParFra_t *   pPars;          // parameters
    Gia_Man_t *      pAig;           // user's AIG
    Gia_Man_t *      pNew;           // internal AIG
    // SAT solving
    sat_solver *     pSat;           // SAT solver
    Vec_Int_t *      vCexStamps;     // time stamps
    Vec_Int_t *      vCands;
    Vec_Int_t *      vVisit;
    Vec_Int_t *      vPat;
    Vec_Int_t *      vPendingPats;   // counterexamples not yet exposed to replay
    int              iSimPat;        // last exposed pattern in the current batch
    int              nBatchSize;
    word             nResimNodes;
    Vec_Bit_t *      vCoDrivers;
    int              iPosRead;       // candidate reading position
    int              iPosWrite;      // candidate writing position
    // refinement
    Vec_Int_t *      vRefClasses;
    Vec_Int_t *      vRefNodes;
    Vec_Int_t *      vRefBins;
    int *            pTable;
    int              nTableSize;
    int              nCandidates;   // non-representatives; -1 before guided simulation
    int              nRefined;      // new classes created in the last simulation
    int              fSimPhase;     // derive phases from the first all-zero simulation bit
    int              nGenBacktracks; // bounded retries selected by the previous round
    int              nGenPatSize;   // largest round-average successful justification
    // statistics
    int              nItersSim;
    int              nItersSat;
    int              nAndNodes;
    int              nSatSat;
    int              nSatUnsat;
    int              nSatUndec;
    int              nCallsSince;
    int              nSimulates;
    int              nRecycles;
    int              nMainConflictsMax; // lifetime maximum; retains learned clauses after a hard query
    int              nConflicts[2][3];
    int              nGates[2];
    abctime          timeCnf;
    abctime          timeGenPats;
    abctime          timeSatSat0;
    abctime          timeSatUnsat0;
    abctime          timeSatSat;
    abctime          timeSatUnsat;
    abctime          timeSatUndec;
    abctime          timeSim;
    abctime          timeRefine;
    abctime          timeResimGlo;
    abctime          timeResimLoc;
    abctime          timeStart;
    sat_solver *     pLocal;
    int *            pHashClasses;  // frozen representative+1, or negative bucket head
    unsigned         LocalHash;     // hash of the current canonical cone program
    int *            pLocalMap;
    Vec_Int_t *      vLocalIds;
    Vec_Int_t *      vLocalGates;
    Vec_Int_t *      vLocalCache;
    int *            pLocalBins;
    int              nLocalProved;
    int              nLocalHit;
    int              nLocalCalls;
    int              fLocalFull;
    int              fLocalCex;
    Vec_Int_t *      vLocalCex;
    abctime          timeLocal;
    Vec_Int_t *      vSimAnds;
    Vec_Int_t *      vSweepCis;    // compact swept-CI index to original object ID
    Vec_Int_t *      vSimCis;
    int              fSparse;
    Vec_Ptr_t *      vModels;
    Vec_Wrd_t *      vModelPis;
    Vec_Wrd_t *      vModelSim;
    int              fModelHit;
    int              nModelHits;
    int *            pGainRefs;        // fanout counts for the bounded gain estimate
    int              iCurObj;
    int              nLocalFailedLimit;
    int              nFailedHit;
    int              nEffort;          // zero keeps the full per-query conflict limit
    Vec_Int_t *      vOrigins;         // borrowed, proved classes accumulate snapshot masks
    int              nConfsChoice;     // cross-snapshot limit; zero means unlimited
    int              nOriginCalls[2][3]; // primary/secondary: proved, disproved, unresolved
    abctime          timeOrigin[2];
};

static inline int    CecZ_ObjSatId( Gia_Man_t * p, Gia_Obj_t * pObj )             { return Gia_ObjCopy2Array(p, Gia_ObjId(p, pObj));                                                     }
static inline int    CecZ_ObjSetSatId( Gia_Man_t * p, Gia_Obj_t * pObj, int Num ) { assert(CecZ_ObjSatId(p, pObj) == -1); Gia_ObjSetCopy2Array(p, Gia_ObjId(p, pObj), Num); Vec_IntPush(&p->vSuppVars, Gia_ObjId(p, pObj)); if ( Gia_ObjIsCi(pObj) ) Vec_IntPushTwo(&p->vCopiesTwo, Gia_ObjId(p, pObj), Num); assert(Vec_IntSize(&p->vVarMap) == Num); Vec_IntPush(&p->vVarMap, Gia_ObjId(p, pObj)); return Num;  }
static inline void   CecZ_ObjCleanSatId( Gia_Man_t * p, Gia_Obj_t * pObj )        { assert(CecZ_ObjSatId(p, pObj) != -1); Gia_ObjSetCopy2Array(p, Gia_ObjId(p, pObj), -1);               }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Allocates one invocation of the SAT sweeper.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static CecZ_Man_t * CecZ_ManCreate( Gia_Man_t * pAig, Cec_ParFra_t * pPars )
{
    CecZ_Man_t * p = ABC_CALLOC( CecZ_Man_t, 1 );
    p->timeStart     = Abc_Clock();
    p->nCandidates   = -1;
    p->pPars         = pPars;
    p->pAig          = pAig;
    p->pSat          = sat_solver_start();
    sat_solver_set_jftr( p->pSat, pPars->jType );
    p->vCexStamps    = Vec_IntStart( Gia_ManObjNum(pAig) );
    p->vCands        = Vec_IntAlloc( 100 );
    p->vVisit        = Vec_IntAlloc( 100 );
    p->vPat          = Vec_IntAlloc( 100 );
    p->vPendingPats  = Vec_IntAlloc( 100 );
    p->nBatchSize    = 1;
    p->pLocal        = sat_solver_start();
    sat_solver_set_jftr( p->pLocal, 2 );
    // Local circuit queries never invoke CNF variable elimination.
    bmcg3_sat_solver_eliminate( p->pLocal, 1 );
    // At the size limit, each pending ancestor can still append its other
    // boundary fanin and itself. Reserve these nodes and the three root fields.
    p->vLocalIds     = Vec_IntAlloc( CECZ_CONE_CAPACITY );
    p->vLocalGates   = Vec_IntAlloc( 2*CECZ_CONE_CAPACITY + 3 );
    p->vLocalCex     = Vec_IntAlloc( 100 );
    p->vModels       = Vec_PtrStart(513);
    p->vModelPis     = Vec_WrdAlloc(512);
    p->vModelSim     = Vec_WrdAlloc(1024);
    p->vLocalCache   = Vec_IntAlloc( 10000 );
    p->pLocalBins    = ABC_CALLOC( int, 65536 );
    Vec_IntPush( p->vLocalCache, 0 );
    if ( pPars->nBTLimitPo )
    {
        int i, Driver;
        p->vCoDrivers = Vec_BitStart( Gia_ManObjNum(pAig) );
        Gia_ManForEachCoDriverId( pAig, Driver, i )
            Vec_BitWriteEntry( p->vCoDrivers, Driver, 1 );
    }
    return p;
}
/**Function*************************************************************

  Synopsis    [Releases solver state, simulation data, and local caches.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void CecZ_ManDestroy( CecZ_Man_t * p )
{
    if ( p->pPars->fVerbose )
    {
        abctime timeTotal = Abc_Clock() - p->timeStart;
        abctime timeSat   = p->timeSatSat0 + p->timeSatSat + p->timeSatUnsat0 + p->timeSatUnsat + p->timeSatUndec;
        abctime timeOther = timeTotal - timeSat - p->timeSim - p->timeRefine - p->timeResimLoc - p->timeGenPats;// - p->timeResimGlo;
        ABC_PRTP( "SAT solving  ", timeSat,          timeTotal );
        ABC_PRTP( "  sat(easy)  ", p->timeSatSat0,   timeTotal );
        ABC_PRTP( "  sat        ", p->timeSatSat,    timeTotal );
        ABC_PRTP( "  unsat(easy)", p->timeSatUnsat0, timeTotal );
        ABC_PRTP( "  unsat      ", p->timeSatUnsat,  timeTotal );
        ABC_PRTP( "  fail       ", p->timeSatUndec,  timeTotal );
        ABC_PRTP( "Generate CNF ", p->timeCnf,       timeTotal );
        ABC_PRTP( "Generate pats", p->timeGenPats,   timeTotal );
        ABC_PRTP( "Simulation   ", p->timeSim,       timeTotal );
        ABC_PRTP( "Refinement   ", p->timeRefine,    timeTotal );
        ABC_PRTP( "Resim global ", p->timeResimGlo,  timeTotal );
        ABC_PRTP( "Resim local  ", p->timeResimLoc,  timeTotal );
        ABC_PRTP( "Other        ", timeOther,        timeTotal );
        ABC_PRTP( "TOTAL        ", timeTotal,        timeTotal );
        printf( "Local proofs = %d  cache hits = %d  calls = %d  time = %.3f\n",
            p->nLocalProved, p->nLocalHit, p->nLocalCalls, (double)p->timeLocal/CLOCKS_PER_SEC );
        printf("Transferred counterexamples = %d  cached limits = %d\n", p->nModelHits, p->nFailedHit);
        fflush( stdout );
    }
    //    p->pAig->nBitPats, Vec_IntSize(p->pAig->vPats) - 2*p->pAig->nBitPats, 1.0*Vec_IntSize(p->pAig->vPats)/Abc_MaxInt(1, p->pAig->nBitPats)-2 );
    Vec_WrdFreeP( &p->pAig->vSims );
    Vec_WrdFreeP( &p->pAig->vSimsPi );
    Gia_ManCleanMark01( p->pAig );
    sat_solver_stop( p->pSat );
    Gia_ManStopP( &p->pNew );
    Vec_IntFreeP( &p->vCexStamps );
    Vec_IntFreeP( &p->vCands );
    Vec_IntFreeP( &p->vVisit );
    Vec_IntFreeP( &p->vPat );
    Vec_IntFreeP( &p->vPendingPats );
    Vec_BitFreeP( &p->vCoDrivers );
    Vec_IntFreeP( &p->vRefClasses );
    Vec_IntFreeP( &p->vRefNodes );
    Vec_IntFreeP( &p->vRefBins );
    ABC_FREE( p->pTable );
    {
        int i; void *Bank;
        Vec_PtrForEachEntry(void *, p->vModels, Bank, i) ABC_FREE(Bank);
        Vec_PtrFree(p->vModels);
        Vec_WrdFree(p->vModelPis); Vec_WrdFree(p->vModelSim);
    }
    sat_solver_stop( p->pLocal );
    ABC_FREE( p->pHashClasses );
    ABC_FREE( p->pLocalMap );
    ABC_FREE( p->pGainRefs );
    ABC_FREE( p->pLocalBins );
    Vec_IntFree( p->vLocalIds );
    Vec_IntFree( p->vLocalGates );
    Vec_IntFree( p->vLocalCex );
    Vec_IntFree( p->vLocalCache );
    Vec_IntFreeP( &p->vSimAnds );
    Vec_IntFreeP( &p->vSweepCis );
    Vec_IntFreeP( &p->vSimCis );
    ABC_FREE( p );
}
/**Function*************************************************************

  Synopsis    [Freezes simulation classes for structural lookup.]

  Description [Structural equality implies membership in the same
  simulation class. Small classes therefore need only a short list of
  exact fanin pairs. Later refinement does not change these buckets.
  Large classes use the ordinary GIA hash table. Level-limited sweeping
  keeps ordinary hashing because excluded nodes have no class.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void CecZ_ManHashClasses( CecZ_Man_t * p )
{
    Gia_Man_t * g = p->pAig;
    Gia_Obj_t * pObj;
    int Id, Repr, Member, Size;
    if ( p->pPars->nLevelMax )
        return;
    p->pHashClasses = ABC_CALLOC( int, Gia_ManObjNum(g) );
    Gia_ManForEachObj( g, pObj, Id )
    {
        Repr = Gia_ObjRepr(g, Id);
        if ( Repr != GIA_VOID )
            p->pHashClasses[Id] = Repr+1;
        else if ( Gia_ObjNext(g, Id) > 0 )
        {
            Size = 1;
            Gia_ClassForEachObj1( g, Id, Member )
                if ( ++Size > CECZ_HASH_CLASS_MAX )
                    break;
            if ( Size > CECZ_HASH_CLASS_MAX )
                p->pHashClasses[Id] = INT_MIN;
        }
    }
}
/**Function*************************************************************

  Synopsis    [Looks up an exact fanin pair within its simulation class.]

  Description [The small-class lists share GIA's per-node hash links
  with the global table, but their nodes are not in that table. The table
  is sized for the entire sweep, so it never needs to resize and rehash
  this mixture of global and class-local links.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int CecZ_ManHashNode( CecZ_Man_t * p, int ObjId, int Lit0, int Lit1, int fXor )
{
    Gia_Man_t * g = p->pNew;
    Gia_Obj_t * pObj;
    int Head, Id, Compl = 0;
    if ( !p->pHashClasses )
        return fXor ? Gia_ManHashXorReal(g, Lit0, Lit1) : Gia_ManHashAnd(g, Lit0, Lit1);
    Head = p->pHashClasses[ObjId] > 0 ? p->pHashClasses[ObjId]-1 : ObjId;
    assert( p->pHashClasses[Head] <= 0 );
    assert( Gia_ManObjNum(g) <= Vec_IntSize(&g->vHTable) );
    if ( p->pHashClasses[Head] == INT_MIN )
        return fXor ? Gia_ManHashXorReal(g, Lit0, Lit1) : Gia_ManHashAnd(g, Lit0, Lit1);
    if ( fXor )
    {
        if ( Lit0 < 2 ) return Lit1 ^ Lit0;
        if ( Lit1 < 2 ) return Lit0 ^ Lit1;
        if ( (Lit0 >> 1) == (Lit1 >> 1) ) return (Lit0 ^ Lit1) & 1;
        Compl = (Lit0 ^ Lit1) & 1;
        Lit0 &= ~1;
        Lit1 &= ~1;
    }
    else
    {
        if ( Lit0 < 2 ) return Lit0 ? Lit1 : 0;
        if ( Lit1 < 2 ) return Lit1 ? Lit0 : 0;
        if ( Lit0 == Lit1 ) return Lit0;
        if ( (Lit0 >> 1) == (Lit1 >> 1) ) return 0;
    }
    if ( (Lit0 > Lit1) ^ fXor )
        ABC_SWAP( int, Lit0, Lit1 );
    for ( Id = -p->pHashClasses[Head]; Id; Id = Vec_IntEntry(&g->vHash, Id) )
    {
        pObj = Gia_ManObj(g, Id);
        if ( Gia_ObjFaninLit0(pObj, Id) == Lit0 && Gia_ObjFaninLit1(pObj, Id) == Lit1 )
            return Abc_Var2Lit(Id, Compl);
    }
    Id = Abc_Lit2Var(fXor ? Gia_ManAppendXorReal(g, Lit0, Lit1) : Gia_ManAppendAnd(g, Lit0, Lit1));
    Vec_IntWriteEntry( &g->vHash, Id, -p->pHashClasses[Head] );
    p->pHashClasses[Head] = -Id;
    return Abc_Var2Lit(Id, Compl);
}
static Gia_Man_t * CecZ_ManStartNew( Gia_Man_t * pAig, int Capacity, Vec_Int_t * vCis )
{
    Gia_Obj_t * pObj; int i;
    Gia_Man_t * pNew = Gia_ManStart( Capacity );
    pNew->pName = Abc_UtilStrsav( pAig->pName );
    pNew->pSpec = Abc_UtilStrsav( pAig->pSpec );
    if ( pAig->pMuxes )
        pNew->pMuxes = ABC_CALLOC( unsigned, pNew->nObjsAlloc );
    Gia_ManFillValue( pAig );
    Gia_ManConst0(pAig)->Value = 0;
    if ( vCis )
    {
        Gia_ManForEachObjVec( vCis, pAig, pObj, i )
            pObj->Value = Gia_ManAppendCi( pNew );
    }
    else
    {
        Gia_ManForEachCi( pAig, pObj, i )
            pObj->Value = Gia_ManAppendCi( pNew );
    }
    Gia_ManHashAlloc( pNew );
    Vec_IntFill( &pNew->vCopies2, Capacity, -1 );
    // The compact temporary graph has only the CIs needed by the SAT sweep.
    // Export restores every original CI, CO, and register in its original order.
    Gia_ManSetRegNum( pNew, vCis ? 0 : Gia_ManRegNum(pAig) );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Creates the circuit encoding of a cone in modified Glucose.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int CecZ_ObjGetCnfVar( CecZ_Man_t * p, int iObj )
{
    Gia_Obj_t * pObj = Gia_ManObj(p->pNew, iObj);
    // quit if CNF is ready
    if ( CecZ_ObjSatId(p->pNew,pObj) >= 0 )
        return CecZ_ObjSatId(p->pNew,pObj);
    assert( iObj > 0 );
    if ( Gia_ObjIsCi(pObj) )
        return CecZ_ObjSetSatId( p->pNew, pObj, sat_solver_addvar(p->pSat) );
    assert( Gia_ObjIsAnd(pObj) );
    Gia_Obj_t * pFan0, * pFan1;
    if ( p->pNew->pMuxes == NULL && Gia_ObjRecognizeExor(pObj, &pFan0, &pFan1) )
    {
        int iVar0 = CecZ_ObjGetCnfVar( p, Gia_ObjId(p->pNew, Gia_Regular(pFan0)) );
        int iVar1 = CecZ_ObjGetCnfVar( p, Gia_ObjId(p->pNew, Gia_Regular(pFan1)) );
        int iVar  = CecZ_ObjSetSatId( p->pNew, pObj, sat_solver_addvar(p->pSat) );
        if ( p->pPars->jType < 2 )
            sat_solver_add_xor( p->pSat, iVar, iVar0, iVar1, Gia_IsComplement(pFan0) ^ Gia_IsComplement(pFan1) );
        if ( p->pPars->jType > 0 )
        {
            int Lit0 = Abc_Var2Lit( iVar0, Gia_IsComplement(pFan0) );
            int Lit1 = Abc_Var2Lit( iVar1, Gia_IsComplement(pFan1) );
            if ( Lit0 < Lit1 )
                 Lit1 ^= Lit0, Lit0 ^= Lit1, Lit1 ^= Lit0;
            assert( Lit0 > Lit1 );
            sat_solver_set_var_fanin_lit( p->pSat, iVar, Lit0, Lit1 );
            p->nGates[1]++;
        }
    }
    else
    {
        int iVar0 = CecZ_ObjGetCnfVar( p, Gia_ObjFaninId0(pObj, iObj) );
        int iVar1 = CecZ_ObjGetCnfVar( p, Gia_ObjFaninId1(pObj, iObj) );
        int iVar  = CecZ_ObjSetSatId( p->pNew, pObj, sat_solver_addvar(p->pSat) );
        if ( p->pPars->jType < 2 )
        {
            if ( Gia_ObjIsXor(pObj) )
                sat_solver_add_xor( p->pSat, iVar, iVar0, iVar1, Gia_ObjFaninC0(pObj) ^ Gia_ObjFaninC1(pObj) );
            else
                sat_solver_add_and( p->pSat, iVar, iVar0, iVar1, Gia_ObjFaninC0(pObj), Gia_ObjFaninC1(pObj), 0 );
        }
        if ( p->pPars->jType > 0 )
        {
            int Lit0 = Abc_Var2Lit( iVar0, Gia_ObjFaninC0(pObj) );
            int Lit1 = Abc_Var2Lit( iVar1, Gia_ObjFaninC1(pObj) );
            if ( (Lit0 > Lit1) ^ Gia_ObjIsXor(pObj) )
                 Lit1 ^= Lit0, Lit0 ^= Lit1, Lit1 ^= Lit0;
            sat_solver_set_var_fanin_lit( p->pSat, iVar, Lit0, Lit1 );
            p->nGates[Gia_ObjIsXor(pObj)]++;
        }
    }
    return CecZ_ObjSatId( p->pNew, pObj );
}

/**Function*************************************************************

  Synopsis    [Refinement of equivalence classes.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline word * CecZ_ObjSim( Gia_Man_t * p, int iObj )
{
    return Vec_WrdEntryP( p->vSims, p->nSimWords * iObj );
}
static inline int CecZ_ObjSimEqual( Gia_Man_t * p, int iObj0, int iObj1 )
{
    int w;
    word * pSim0 = CecZ_ObjSim( p, iObj0 );
    word * pSim1 = CecZ_ObjSim( p, iObj1 );
    if ( (pSim0[0] & 1) == (pSim1[0] & 1) )
    {
        for ( w = 0; w < p->nSimWords; w++ )
            if ( pSim0[w] != pSim1[w] )
                return 0;
        return 1;
    }
    else
    {
        for ( w = 0; w < p->nSimWords; w++ )
            if ( pSim0[w] != ~pSim1[w] )
                return 0;
        return 1;
    }
}
static int CecZ_ManSimHashKey( word * pSim, int nSims, int nTableSize )
{
    static const unsigned Primes[16] = {
        1291, 1699, 1999, 2357, 2953, 3313, 3907, 4177,
        4831, 5147, 5647, 6343, 6899, 7103, 7873, 8147 };
    unsigned Hash = 0, Phase = -(unsigned)(pSim[0] & 1);
    int i;
    for ( i = 0; i < nSims; i++ )
    {
        Hash ^= ((unsigned)pSim[i] ^ Phase) * Primes[(2*i) & 15];
        Hash ^= ((unsigned)(pSim[i] >> 32) ^ Phase) * Primes[(2*i+1) & 15];
    }
    return (int)(Hash % (unsigned)nTableSize);
}

static int CecZ_RefineOneClassIter( Gia_Man_t * p, int iRepr )
{
    int iObj, iPrev = iRepr, iPrev2, iRepr2;
    assert( Gia_ObjRepr(p, iRepr) == GIA_VOID );
    assert( Gia_ObjNext(p, iRepr) > 0 );
    Gia_ClassForEachObj1( p, iRepr, iRepr2 )
        if ( CecZ_ObjSimEqual(p, iRepr, iRepr2) )
            iPrev = iRepr2;
        else
            break;
    if ( iRepr2 <= 0 ) // no refinement
        return 0;
    // relink remaining nodes of the class
    // nodes that are equal to iRepr, remain in the class of iRepr
    // nodes that are not equal to iRepr, move to the class of iRepr2
    Gia_ObjSetRepr( p, iRepr2, GIA_VOID );
    iPrev2 = iRepr2;
    for ( iObj = Gia_ObjNext(p, iRepr2); iObj > 0; iObj = Gia_ObjNext(p, iObj) )
    {
        if ( CecZ_ObjSimEqual(p, iRepr, iObj) ) // remains with iRepr
        {
            Gia_ObjSetNext( p, iPrev, iObj );
            iPrev = iObj;
        }
        else // moves to iRepr2
        {
            Gia_ObjSetRepr( p, iObj, iRepr2 );
            Gia_ObjSetNext( p, iPrev2, iObj );
            iPrev2 = iObj;
        }
    }
    Gia_ObjSetNext( p, iPrev, -1 );
    Gia_ObjSetNext( p, iPrev2, -1 );
    // refine incrementally
    if ( Gia_ObjNext(p, iRepr2) > 0 )
        return 1 + CecZ_RefineOneClassIter( p, iRepr2 );
    return 1;
}
/**Function*************************************************************

  Synopsis    [Partitions initial signatures by a stable radix sort.]

  Description [The signature hash is only a filter. Exact simulation
  comparisons resolve every collision before a candidate class is used.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void CecZ_RefineInitial( Gia_Man_t * p, Vec_Int_t * vNodes, int fSimPhase )
{
    int nNodes = Vec_IntSize(vNodes), Counts[2048], Offsets[2048];
    word * pData = ABC_ALLOC( word, nNodes ), * pTemp = ABC_ALLOC( word, nNodes );
    int i, k, Shift, Id, Prev, Repr, Start, Stop;
    Vec_IntForEachEntry( vNodes, Id, i )
    {
        unsigned Hash = (unsigned)CecZ_ManSimHashKey(CecZ_ObjSim(p, Id), p->nSimWords, 2147483647);
        if ( fSimPhase )
            Gia_ManObj(p, Id)->fPhase = (unsigned)(CecZ_ObjSim(p, Id)[0] & 1);
        pData[i] = ((word)Hash << 32) | (unsigned)Id;
    }
    for ( Shift = 32; Shift < 64; Shift += 11 )
    {
        memset( Counts, 0, sizeof(Counts) );
        for ( i = 0; i < nNodes; i++ )
            Counts[(pData[i] >> Shift) & 2047]++;
        Offsets[0] = 0;
        for ( k = 1; k < 2048; k++ )
            Offsets[k] = Offsets[k-1] + Counts[k-1];
        for ( i = 0; i < nNodes; i++ )
            pTemp[Offsets[(pData[i] >> Shift) & 2047]++] = pData[i];
        ABC_SWAP( word *, pData, pTemp );
    }
    for ( Start = 0; Start < nNodes; Start = Stop )
    {
        Repr = Prev = (int)(unsigned)pData[Start];
        for ( Stop = Start+1; Stop < nNodes && (pData[Stop] >> 32) == (pData[Start] >> 32); Stop++ )
        {
            Id = (int)(unsigned)pData[Stop];
            Gia_ObjSetNext( p, Prev, Id );
            Gia_ObjSetRepr( p, Id, Repr );
            Prev = Id;
        }
        Gia_ObjSetNext( p, Prev, -1 );
    }
    ABC_FREE( pData );
    ABC_FREE( pTemp );
    // Compare signatures in object order to avoid scattered accesses after
    // the hash sort. Independent classes retain the same members and order.
    Vec_IntForEachEntry( vNodes, Id, i )
        if ( Gia_ObjRepr(p, Id) == GIA_VOID && Gia_ObjNext(p, Id) > 0 )
            CecZ_RefineOneClassIter( p, Id );
}
static int CecZ_RefineOneClass( Gia_Man_t * p, CecZ_Man_t * pMan, Vec_Int_t * vNodes )
{
    int k, iObj, Bin, nClasses;
    Vec_IntClear( pMan->vRefBins );
    Vec_IntForEachEntryReverse( vNodes, iObj, k )
    {
        int Key = CecZ_ManSimHashKey( CecZ_ObjSim(p, iObj), p->nSimWords, pMan->nTableSize );
        assert( Key >= 0 && Key < pMan->nTableSize );
        if ( pMan->pTable[Key] == -1 )
            Vec_IntPush( pMan->vRefBins, Key );
        p->pNexts[iObj] = pMan->pTable[Key];
        pMan->pTable[Key] = iObj;
    }
    nClasses = Vec_IntSize(pMan->vRefBins);
    Vec_IntForEachEntry( pMan->vRefBins, Bin, k )
    {
        int iRepr = pMan->pTable[Bin];
        pMan->pTable[Bin] = -1;
        assert( p->pReprs[iRepr].iRepr == GIA_VOID );
        assert( p->pNexts[iRepr] != 0 );
        if ( p->pNexts[iRepr] == -1 )
            continue;
        for ( iObj = p->pNexts[iRepr]; iObj > 0; iObj = p->pNexts[iObj] )
            p->pReprs[iObj].iRepr = iRepr;
        nClasses += CecZ_RefineOneClassIter( p, iRepr );
    }
    Vec_IntClear( pMan->vRefBins );
    return nClasses - 1;
}
static void CecZ_RefineClasses( Gia_Man_t * p, CecZ_Man_t * pMan )
{
    pMan->nRefined = 0;
    if ( Vec_IntSize(pMan->vRefClasses) == 0 )
        return;
    if ( Vec_IntSize(pMan->vRefNodes) > 0 )
        CecZ_RefineInitial( p, pMan->vRefNodes, pMan->fSimPhase );
    else
    {
        int i, k, iObj, iRepr;
        Vec_IntForEachEntry( pMan->vRefClasses, iRepr, i )
        {
            assert( p->pReprs[iRepr].fColorA );
            p->pReprs[iRepr].fColorA = 0;
            Vec_IntClear( pMan->vRefNodes );
            Vec_IntPush( pMan->vRefNodes, iRepr );
            Gia_ClassForEachObj1( p, iRepr, k )
                Vec_IntPush( pMan->vRefNodes, k );
            Vec_IntForEachEntry( pMan->vRefNodes, iObj, k )
            {
                p->pReprs[iObj].iRepr = GIA_VOID;
                p->pNexts[iObj] = -1;
            }
            {
                // Count new representatives while partitioning, without a second scan.
                int nNew = CecZ_RefineOneClass( p, pMan, pMan->vRefNodes );
                pMan->nRefined += nNew;
                if ( pMan->nCandidates >= 0 )
                {
                    pMan->nCandidates -= nNew;
                    assert( pMan->nCandidates >= 0 );
                }
            }
        }
    }
    Vec_IntClear( pMan->vRefClasses );
    Vec_IntClear( pMan->vRefNodes );
}
static void CecZ_RefineInit( Gia_Man_t * p, CecZ_Man_t * pMan )
{
    Gia_Obj_t * pObj; int i;
    ABC_FREE( p->pReprs );
    ABC_FREE( p->pNexts );
    p->pReprs = ABC_CALLOC( Gia_Rpr_t, Gia_ManObjNum(p) );
    p->pNexts = ABC_FALLOC( int, Gia_ManObjNum(p) );
    pMan->nTableSize  = Abc_PrimeCudd( Abc_MinInt(Gia_ManObjNum(p), 65536) );
    pMan->pTable      = ABC_FALLOC( int, pMan->nTableSize );
    pMan->vRefNodes   = Vec_IntAlloc( Gia_ManObjNum(p) );
    Gia_ManForEachObj( p, pObj, i )
    {
        p->pReprs[i].iRepr = GIA_VOID;
        if ( !Gia_ObjIsCo(pObj) && (!pMan->pPars->nLevelMax || Gia_ObjLevel(p, pObj) <= pMan->pPars->nLevelMax) )
            Vec_IntPush( pMan->vRefNodes, i );
    }
    pMan->vRefBins    = Vec_IntAlloc( 256 );
    pMan->vRefClasses = Vec_IntAlloc( 256 );
    Vec_IntPush( pMan->vRefClasses, 0 );
}

static inline void CecZ_ObjSimSetInputBit( Gia_Man_t * p, int iObj, int Bit )
{
    word * pSim = CecZ_ObjSim( p, iObj );
    if ( Abc_InfoHasBit( (unsigned*)pSim, p->iPatsPi ) != Bit )
        Abc_InfoXorBit( (unsigned*)pSim, p->iPatsPi );
}
static inline void CecZ_ObjSimCo( Gia_Man_t * p, int iObj )
{
    int w;
    Gia_Obj_t * pObj = Gia_ManObj( p, iObj );
    word * pSimCo  = CecZ_ObjSim( p, iObj );
    word * pSimDri = CecZ_ObjSim( p, Gia_ObjFaninId0(pObj, iObj) );
    if ( Gia_ObjFaninC0(pObj) )
        for ( w = 0; w < p->nSimWords; w++ )
            pSimCo[w] = ~pSimDri[w];
    else
        for ( w = 0; w < p->nSimWords; w++ )
            pSimCo[w] =  pSimDri[w];
}
static inline void CecZ_ObjSimAndRange( Gia_Man_t * p, int iObj, int Begin, int End )
{
    int w;
    Gia_Obj_t * pObj = Gia_ManObj( p, iObj );
    word * pSim  = CecZ_ObjSim( p, iObj );
    word * pSim0 = CecZ_ObjSim( p, Gia_ObjFaninId0(pObj, iObj) );
    word * pSim1 = CecZ_ObjSim( p, Gia_ObjFaninId1(pObj, iObj) );
    if ( Gia_ObjFaninC0(pObj) && Gia_ObjFaninC1(pObj) )
        for ( w = Begin; w < End; w++ )
            pSim[w] = ~pSim0[w] & ~pSim1[w];
    else if ( Gia_ObjFaninC0(pObj) && !Gia_ObjFaninC1(pObj) )
        for ( w = Begin; w < End; w++ )
            pSim[w] = ~pSim0[w] & pSim1[w];
    else if ( !Gia_ObjFaninC0(pObj) && Gia_ObjFaninC1(pObj) )
        for ( w = Begin; w < End; w++ )
            pSim[w] = pSim0[w] & ~pSim1[w];
    else
        for ( w = Begin; w < End; w++ )
            pSim[w] = pSim0[w] & pSim1[w];
}
static inline void CecZ_ObjSimXorRange( Gia_Man_t * p, int iObj, int Begin, int End )
{
    int w;
    Gia_Obj_t * pObj = Gia_ManObj( p, iObj );
    word * pSim  = CecZ_ObjSim( p, iObj );
    word * pSim0 = CecZ_ObjSim( p, Gia_ObjFaninId0(pObj, iObj) );
    word * pSim1 = CecZ_ObjSim( p, Gia_ObjFaninId1(pObj, iObj) );
    if ( Gia_ObjFaninC0(pObj) ^ Gia_ObjFaninC1(pObj) )
        for ( w = Begin; w < End; w++ )
            pSim[w] = ~pSim0[w] ^ pSim1[w];
    else
        for ( w = Begin; w < End; w++ )
            pSim[w] =  pSim0[w] ^ pSim1[w];
}
static inline void CecZ_ObjSimAnd( Gia_Man_t * p, int iObj )
{
    CecZ_ObjSimAndRange( p, iObj, 0, p->nSimWords );
}
static inline void CecZ_ObjSimXor( Gia_Man_t * p, int iObj )
{
    CecZ_ObjSimXorRange( p, iObj, 0, p->nSimWords );
}
static inline word CecZ_RandomWord( void )
{
    unsigned Hi = Abc_Random(0);
    unsigned Lo = Abc_Random(0);
    return ((word)Hi << 32) | Lo;
}
static inline void CecZ_ObjSimCi( Gia_Man_t * p, int iObj, int Round )
{
    int w;
    word * pSim = CecZ_ObjSim( p, iObj );
    for ( w = 0; w < p->nSimWords; w++ )
    {
        // Keep uniform patterns alongside the sparse/dense input patterns.
        int k, Bias = Round && w == 0 ? Round%14 : 0;
        int Count = Bias < 7 ? Bias+1 : 14-Bias;
        pSim[w] = CecZ_RandomWord();
        for ( k = 1; k < Count; k++ ) pSim[w] &= CecZ_RandomWord();
        if ( Bias >= 7 ) pSim[w] = ~pSim[w];
    }
    pSim[0] <<= 1;
}
/**Function*************************************************************

  Synopsis    [Restricts repeated simulation to candidate fanin cones.]

  Description [Classes only split, so the original union remains a
  sufficient simulation region throughout sweeping.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void CecZ_SimSelect( CecZ_Man_t * pMan )
{
    Gia_Man_t * p = pMan->pAig;
    Vec_Bit_t * vSeen = Vec_BitStart( Gia_ManObjNum(p) );
    Vec_Int_t * vOldAnds = pMan->vSimAnds, * vOldCis = pMan->vSimCis;
    Gia_Obj_t * pObj;
    int i, Id, nSize = vOldAnds ? Vec_IntSize(vOldAnds) : Gia_ManObjNum(p);
    pMan->vSimAnds = Vec_IntAlloc( 1000 );
    pMan->vSimCis = Vec_IntAlloc( 1000 );
    // Reverse topological marking needs no DFS stack. Classes only split, so
    // subsequent selections need visit only the previous fanin union.
    for ( i = nSize - 1; i >= 0; i-- )
    {
        Id = vOldAnds ? Vec_IntEntry(vOldAnds, i) : i;
        pObj = Gia_ManObj(p, Id);
        if ( !Gia_ObjIsAnd(pObj) )
            continue;
        if ( !Vec_BitEntry(vSeen, Id) && Gia_ObjRepr(p, Id) == GIA_VOID && Gia_ObjNext(p, Id) <= 0 )
            continue;
        Vec_IntPush( pMan->vSimAnds, Id );
        Vec_BitWriteEntry( vSeen, Gia_ObjFaninId0(pObj, Id), 1 );
        Vec_BitWriteEntry( vSeen, Gia_ObjFaninId1(pObj, Id), 1 );
    }
    Vec_IntReverseOrder( pMan->vSimAnds );
    nSize = vOldCis ? Vec_IntSize(vOldCis) : Gia_ManCiNum(p);
    for ( i = 0; i < nSize; i++ )
    {
        Id = Vec_IntEntry(vOldCis ? vOldCis : p->vCis, i);
        if ( Vec_BitEntry(vSeen, Id) || Gia_ObjRepr(p, Id) != GIA_VOID || Gia_ObjNext(p, Id) > 0 )
            Vec_IntPush( pMan->vSimCis, Id );
    }
    Vec_BitFree( vSeen );
    Vec_IntFreeP( &vOldAnds );
    Vec_IntFreeP( &vOldCis );
    if ( pMan->pPars->fVerbose )
        printf( "Simulation region: %d ANDs and %d CIs.\n", Vec_IntSize(pMan->vSimAnds), Vec_IntSize(pMan->vSimCis) );
}
static void CecZ_ManSimulateCis( Gia_Man_t * p, CecZ_Man_t * pMan )
{
    int i, Id;
    if ( pMan->vSimCis )
    {
        Vec_IntForEachEntry( pMan->vSimCis, Id, i )
            CecZ_ObjSimCi( p, Id, pMan->vSimAnds && Vec_IntSize(pMan->vSimAnds) < Gia_ManAndNum(p)/4 ? 0 : pMan->nSimulates );
    }
    else
        Gia_ManForEachCiId( p, Id, i )
            CecZ_ObjSimCi( p, Id, pMan->vSimAnds && Vec_IntSize(pMan->vSimAnds) < Gia_ManAndNum(p)/4 ? 0 : pMan->nSimulates );
    p->iPatsPi = 0;
}
static Abc_Cex_t * CecZ_ManDeriveCex( Gia_Man_t * p, int iOut, int iPat )
{
    Abc_Cex_t * pCex;
    int i, Id;
    pCex = Abc_CexAlloc( 0, Gia_ManCiNum(p), 1 );
    pCex->iPo = iOut;
    if ( iPat == -1 )
        return pCex;
    Gia_ManForEachCiId( p, Id, i )
        if ( Abc_InfoHasBit((unsigned *)CecZ_ObjSim(p, Id), iPat) )
            Abc_InfoSetBit( pCex->pData, i );
    return pCex;
}
static int CecZ_ManSimulateCos( Gia_Man_t * p )
{
    int i, Id;
    // check outputs and generate CEX if they fail
    Gia_ManForEachCoId( p, Id, i )
    {
        CecZ_ObjSimCo( p, Id );
        if ( CecZ_ObjSimEqual(p, Id, 0) )
            continue;
        p->pCexSeq = CecZ_ManDeriveCex( p, i, Abc_TtFindFirstBit2(CecZ_ObjSim(p, Id), p->nSimWords) );
        return 0;
    }
    return 1;
}
static void CecZ_ManSimulate( Gia_Man_t * p, CecZ_Man_t * pMan )
{
    abctime clk = Abc_Clock();
    Gia_Obj_t * pObj; int i, k, nSize;
    pMan->nSimulates++;
    if ( pMan->pTable == NULL )
        CecZ_RefineInit( p, pMan );
    else
        assert( Vec_IntSize(pMan->vRefClasses) == 0 );
    nSize = pMan->vSimAnds ? Vec_IntSize(pMan->vSimAnds) : Gia_ManObjNum(p);
    for ( k = 0; k < nSize; k++ )
    {
        i = pMan->vSimAnds ? Vec_IntEntry(pMan->vSimAnds, k) : k;
        pObj = Gia_ManObj(p, i);
        if ( !Gia_ObjIsAnd(pObj) )
            continue;
        int iRepr = Gia_ObjRepr( p, i );
        if ( Gia_ObjIsXor(pObj) )
            CecZ_ObjSimXor( p, i );
        else
            CecZ_ObjSimAnd( p, i );
        if ( iRepr == GIA_VOID || p->pReprs[iRepr].fColorA || CecZ_ObjSimEqual(p, iRepr, i) )
            continue;
        p->pReprs[iRepr].fColorA = 1;
        Vec_IntPush( pMan->vRefClasses, iRepr );
    }
    pMan->timeSim += Abc_Clock() - clk;
    clk = Abc_Clock();
    CecZ_RefineClasses( p, pMan );
    pMan->timeRefine += Abc_Clock() - clk;
}
static void CecZ_ManSimulate_rec( Gia_Man_t * p, CecZ_Man_t * pMan, int iObj )
{
    int Begin = Vec_IntEntry(pMan->vCexStamps, iObj)/64;
    Gia_Obj_t * pObj;
    if ( !iObj || Vec_IntEntry(pMan->vCexStamps, iObj) == pMan->iSimPat )
        return;
    Vec_IntWriteEntry( pMan->vCexStamps, iObj, pMan->iSimPat );
    pObj = Gia_ManObj(p, iObj);
    if ( Gia_ObjIsCi(pObj) )
        return;
    assert( Gia_ObjIsAnd(pObj) );
    pMan->nResimNodes++;
    CecZ_ManSimulate_rec( p, pMan, Gia_ObjFaninId0(pObj, iObj) );
    CecZ_ManSimulate_rec( p, pMan, Gia_ObjFaninId1(pObj, iObj) );
    if ( Gia_ObjIsXor(pObj) )
        CecZ_ObjSimXorRange( p, iObj, Begin, pMan->iSimPat/64+1 );
    else
        CecZ_ObjSimAndRange( p, iObj, Begin, pMan->iSimPat/64+1 );
}
static void CecZ_ManSimAlloc( Gia_Man_t * p, int nWords )
{
    Vec_WrdFreeP( &p->vSims );
    Vec_WrdFreeP( &p->vSimsPi );
    // Only the current simulation region and its CIs have valid signatures.
    // Its fanins are closed under reachability and written before first read;
    // outside entries deliberately remain uninitialized and must not be read.
    // Miter mode simulates the whole graph and writes COs before checking them.
    // Only the constant needs initialization here.
    p->vSims = Vec_WrdAllocArray( ABC_ALLOC(word,(size_t)Gia_ManObjNum(p)*nWords), Gia_ManObjNum(p)*nWords );
    memset( Vec_WrdArray(p->vSims), 0, sizeof(word)*nWords );
    p->vSimsPi   = Vec_WrdStart( (Gia_ManCiNum(p) + 1) * nWords );
    p->nSimWords = nWords;
}

static void CecZ_ManPrintStats( Gia_Man_t * p, Cec_ParFra_t * pPars, CecZ_Man_t * pMan, int fSim )
{
    static ABC_THREAD_LOCAL abctime clk = 0;
    abctime clkThis = 0;
    int i, nLits, Counter = 0, Counter0 = 0, CounterX = 0;
    if ( !pPars->fVerbose )
        return;
    if ( pMan->nItersSim + pMan->nItersSat )
        clkThis = Abc_Clock() - clk;
    clk = Abc_Clock();
    for ( i = 0; i < Gia_ManObjNum(p); i++ )
    {
        if ( Gia_ObjIsHead(p, i) )
            Counter++;
        else if ( Gia_ObjIsConst(p, i) )
            Counter0++;
        else if ( Gia_ObjIsNone(p, i) )
            CounterX++;
    }
    nLits = Gia_ManObjNum(p) - Counter - CounterX;
    if ( fSim )
    {
        printf( "Sim %4d : ",     pMan->nItersSim++ + pMan->nItersSat );
        printf( "%6.2f %%  ", 100.0*nLits/Gia_ManCandNum(p) );
    }
    else
    {
        printf( "SAT %4d : ",     pMan->nItersSim + pMan->nItersSat++ );
        printf( "%6.2f %%  ", 100.0*pMan->nAndNodes/Abc_MaxInt(1, pMan->fSparse ? Vec_IntSize(pMan->vSimAnds) : Gia_ManAndNum(p)) );
    }
    printf( "P =%7d  ",   pMan ? pMan->nSatUnsat : 0 );
    printf( "D =%7d  ",   pMan ? pMan->nSatSat   : 0 );
    printf( "F =%8d  ",   pMan ? pMan->nSatUndec : 0 );
    Abc_Print( 1, "cst =%9d  cls =%8d  lit =%9d   ",  Counter0, Counter, nLits );
    Abc_PrintTime( 1, "Time", clkThis );
}
/**Function*************************************************************

  Synopsis    [Packs simulation patterns into array of simulation info.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void CecZ_ManPackAddPatterns( Gia_Man_t * p, int iBit, Vec_Int_t * vLits )
{
    int i, w, Lit, Limit = Abc_MinInt( Vec_IntSize(vLits), 64 * p->nSimWords - 1 );
    int Last = Limit >> 6;
    // All neighboring patterns use the same input value except the one
    // flipping this input. Update whole words, preserving occupied bits.
    Vec_IntForEachEntry( vLits, Lit, i )
    {
        word * pInfo = Vec_WrdEntryP( p->vSims,   p->nSimWords * Abc_Lit2Var(Lit) );
        word * pPres = Vec_WrdEntryP( p->vSimsPi, p->nSimWords * Abc_Lit2Var(Lit) );
        int Bit = i < Limit ? (iBit + i + 1) % Limit + 1 : -1;
        for ( w = 0; w <= Last; w++ )
        {
            word Mask = w == 0 ? ~(word)1 : ~(word)0;
            word Value = -(word)Abc_LitIsCompl(Lit);
            if ( w == Last && (Limit & 63) != 63 )
                Mask &= ((word)1 << ((Limit & 63) + 1)) - 1;
            if ( Bit >= 0 && w == (Bit >> 6) )
                Value ^= (word)1 << (Bit & 63);
            Mask &= ~pPres[w];
            pInfo[w] = (pInfo[w] & ~Mask) | (Value & Mask);
        }
    }
}
static int CecZ_ManPackAddPatternTry( Gia_Man_t * p, int iBit, Vec_Int_t * vLits )
{
    int i, Lit;
    assert( p->iPatsPi > 0 && p->iPatsPi < 64 * p->nSimWords );
    Vec_IntForEachEntry( vLits, Lit, i )
    {
        word * pInfo = Vec_WrdEntryP( p->vSims,   p->nSimWords * Abc_Lit2Var(Lit) );
        word * pPres = Vec_WrdEntryP( p->vSimsPi, p->nSimWords * Abc_Lit2Var(Lit) );
        if ( Abc_InfoHasBit( (unsigned *)pPres, iBit ) &&
             Abc_InfoHasBit( (unsigned *)pInfo, iBit ) != Abc_LitIsCompl(Lit) )
             return 0;
    }
    Vec_IntForEachEntry( vLits, Lit, i )
    {
        word * pInfo = Vec_WrdEntryP( p->vSims,   p->nSimWords * Abc_Lit2Var(Lit) );
        word * pPres = Vec_WrdEntryP( p->vSimsPi, p->nSimWords * Abc_Lit2Var(Lit) );
        Abc_InfoSetBit( (unsigned *)pPres, iBit );
        if ( Abc_InfoHasBit( (unsigned *)pInfo, iBit ) != Abc_LitIsCompl(Lit) )
             Abc_InfoXorBit( (unsigned *)pInfo, iBit );
    }
    return 1;
}
static int CecZ_ManPackAddPattern( Gia_Man_t * p, Vec_Int_t * vLits, int fExtend )
{
    int k;
    for ( k = 1; k < 64 * p->nSimWords - 1; k++ )
    {
        if ( ++p->iPatsPi == 64 * p->nSimWords - 1 )
            p->iPatsPi = 1;
        if ( CecZ_ManPackAddPatternTry( p, p->iPatsPi, vLits ) )
        {
            if ( fExtend )
                CecZ_ManPackAddPatterns( p, p->iPatsPi, vLits );
            break;
        }
    }
    if ( k == 64 * p->nSimWords - 1 )
    {
        p->iPatsPi = k;
        if ( !CecZ_ManPackAddPatternTry( p, p->iPatsPi, vLits ) )
            printf( "Internal error.\n" );
        else if ( fExtend )
            CecZ_ManPackAddPatterns( p, p->iPatsPi, vLits );
        return 64 * p->nSimWords;
    }
    return k;
}

/**Function*************************************************************

  Synopsis    [Generates counter-examples to refine the candidate equivalences.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int CecZ_ObjFan0IsAssigned( Gia_Obj_t * pObj )
{
    return Gia_ObjFanin0(pObj)->fMark0 || Gia_ObjFanin0(pObj)->fMark1;
}
static inline int CecZ_ObjFan1IsAssigned( Gia_Obj_t * pObj )
{
    return Gia_ObjFanin1(pObj)->fMark0 || Gia_ObjFanin1(pObj)->fMark1;
}
static inline int CecZ_ObjFan0HasValue( Gia_Obj_t * pObj, int v )
{
    return (v ^ Gia_ObjFaninC0(pObj)) ? Gia_ObjFanin0(pObj)->fMark1 : Gia_ObjFanin0(pObj)->fMark0;
}
static inline int CecZ_ObjFan1HasValue( Gia_Obj_t * pObj, int v )
{
    return (v ^ Gia_ObjFaninC1(pObj)) ? Gia_ObjFanin1(pObj)->fMark1 : Gia_ObjFanin1(pObj)->fMark0;
}
static inline int CecZ_ObjObjIsImpliedValue( Gia_Obj_t * pObj, int v )
{
    assert( !pObj->fMark0 && !pObj->fMark1 ); // not visited
    if ( Gia_ObjIsXor(pObj) )
        return CecZ_ObjFan0IsAssigned(pObj) && CecZ_ObjFan1IsAssigned(pObj) &&
            v == (CecZ_ObjFan0HasValue(pObj, 1) ^ CecZ_ObjFan1HasValue(pObj, 1));
    if ( v )
    return CecZ_ObjFan0HasValue(pObj, 1) && CecZ_ObjFan1HasValue(pObj, 1);
    return CecZ_ObjFan0HasValue(pObj, 0) || CecZ_ObjFan1HasValue(pObj, 0);
}
static inline int CecZ_ObjFan0IsImpliedValue( Gia_Obj_t * pObj, int v )
{
    return Gia_ObjIsAnd(Gia_ObjFanin0(pObj)) && CecZ_ObjObjIsImpliedValue( Gia_ObjFanin0(pObj), v ^ Gia_ObjFaninC0(pObj) );
}
static inline int CecZ_ObjFan1IsImpliedValue( Gia_Obj_t * pObj, int v )
{
    return Gia_ObjIsAnd(Gia_ObjFanin1(pObj)) && CecZ_ObjObjIsImpliedValue( Gia_ObjFanin1(pObj), v ^ Gia_ObjFaninC1(pObj) );
}
/**Function*************************************************************

  Synopsis    [Justifies a node value with bounded retries and tail iteration.]

  Description [The traversal order and random choices are unchanged by tail
  iteration. Recursion is needed only when a sibling or retry is pending.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int CecZ_ManGeneratePatterns_rec( CecZ_Gen_t * pCtx, Gia_Obj_t * pObj, int Value )
{
    Gia_Man_t * p = pCtx->pAig;
    Vec_Int_t * vPat = pCtx->vPat, * vVisit = pCtx->vVisit;
    Gia_Obj_t * pFan0, * pFan1, * pNext;
    int NextValue, Choice, nVisit, nPat;
    // Reuse this frame when only one child remains to be justified.
again:
    assert( !pObj->fMark0 && !pObj->fMark1 );
    if ( Value )
        pObj->fMark1 = 1;
    else
        pObj->fMark0 = 1;
    Vec_IntPush( vVisit, Gia_ObjId(p, pObj) );
    if ( Gia_ObjIsCi(pObj) )
    {
        Vec_IntPush( vPat, Abc_Var2Lit(Gia_ObjId(p, pObj), Value) );
        return 1;
    }
    assert( Gia_ObjIsAnd(pObj) );
    pFan0 = Gia_ObjFanin0(pObj);
    pFan1 = Gia_ObjFanin1(pObj);
    if ( Gia_ObjIsXor(pObj) )
    {
        int Ass0 = CecZ_ObjFan0IsAssigned(pObj), Ass1 = CecZ_ObjFan1IsAssigned(pObj);
        if ( Ass0 && Ass1 )
            return Value == (CecZ_ObjFan0HasValue(pObj, 1) ^ CecZ_ObjFan1HasValue(pObj, 1));
        if ( Ass0 )
        {
            Value ^= CecZ_ObjFan0HasValue(pObj, 1) ^ Gia_ObjFaninC1(pObj);
            pObj = pFan1;
            goto again;
        }
        if ( Ass1 )
        {
            Value ^= CecZ_ObjFan1HasValue(pObj, 1) ^ Gia_ObjFaninC0(pObj);
            pObj = pFan0;
            goto again;
        }
        Choice = !(Abc_Random(0) & 1);
        if ( !CecZ_ManGeneratePatterns_rec(pCtx, pFan0, Choice ^ Gia_ObjFaninC0(pObj)) )
            return 0;
        NextValue = Value ^ Choice;
        if ( CecZ_ObjFan1HasValue(pObj, !NextValue) )
            return 0;
        if ( CecZ_ObjFan1HasValue(pObj, NextValue) )
            return 1;
        Value = NextValue ^ Gia_ObjFaninC1(pObj);
        pObj = pFan1;
        goto again;
    }
    if ( Value )
    {
        if ( CecZ_ObjFan0HasValue(pObj, 0) || CecZ_ObjFan1HasValue(pObj, 0) )
            return 0;
        if ( !CecZ_ObjFan0HasValue(pObj, 1) && !CecZ_ManGeneratePatterns_rec(pCtx, pFan0, !Gia_ObjFaninC0(pObj)) )
            return 0;
        if ( CecZ_ObjFan1HasValue(pObj, 0) )
            return 0;
        if ( CecZ_ObjFan1HasValue(pObj, 1) )
            return 1;
        Value = !Gia_ObjFaninC1(pObj);
        pObj = pFan1;
        goto again;
    }
    if ( CecZ_ObjFan0HasValue(pObj, 1) && CecZ_ObjFan1HasValue(pObj, 1) )
        return 0;
    if ( CecZ_ObjFan0HasValue(pObj, 0) || CecZ_ObjFan1HasValue(pObj, 0) )
        return 1;
    if ( CecZ_ObjFan0HasValue(pObj, 1) ) Choice = 1;
    else if ( CecZ_ObjFan1HasValue(pObj, 1) ) Choice = 0;
    else if ( CecZ_ObjFan0IsImpliedValue(pObj, 0) ) Choice = 0;
    else if ( CecZ_ObjFan1IsImpliedValue(pObj, 0) ) Choice = 1;
    else if ( CecZ_ObjFan0IsImpliedValue(pObj, 1) ) Choice = 1;
    else if ( CecZ_ObjFan1IsImpliedValue(pObj, 1) ) Choice = 0;
    else
    {
        Choice = Abc_Random(0) & 1;
        if ( pCtx->nBacktracks )
        {
            nVisit = Vec_IntSize(vVisit);
            nPat = Vec_IntSize(vPat);
            pNext = Choice ? pFan1 : pFan0;
            NextValue = Choice ? Gia_ObjFaninC1(pObj) : Gia_ObjFaninC0(pObj);
            if ( CecZ_ManGeneratePatterns_rec(pCtx, pNext, NextValue) )
                return 1;
            if ( !pCtx->nBacktracks )
                return 0;
            // Undo only this failed branch; earlier assignments remain.
            --pCtx->nBacktracks;
            pCtx->nDiscarded += Vec_IntSize(vVisit) - nVisit;
            while ( Vec_IntSize(vVisit) > nVisit )
            {
                Gia_Obj_t * pUndo = Gia_ManObj(p, Vec_IntPop(vVisit));
                pUndo->fMark0 = pUndo->fMark1 = 0;
            }
            Vec_IntShrink( vPat, nPat );
            Choice ^= 1;
        }
    }
    Value = Choice ? Gia_ObjFaninC1(pObj) : Gia_ObjFaninC0(pObj);
    pObj = Choice ? pFan1 : pFan0;
    goto again;
}

static int CecZ_ManGeneratePatternOne( Gia_Man_t * p, int iRepr, int iReprVal, int iCand, int iCandVal, Vec_Int_t * vPat, Vec_Int_t * vVisit, int nBacktracks, word * pnDiscarded )
{
    CecZ_Gen_t Context;
    int Res, k;
    Gia_Obj_t * pObj;
    assert( iCand > 0 );
    if ( !iRepr && iReprVal )
        return 0;
    Context.pAig = p;
    Context.vPat = vPat;
    Context.vVisit = vVisit;
    Context.nBacktracks = nBacktracks;
    Context.nDiscarded = 0;
    Vec_IntClear( vPat );
    Vec_IntClear( vVisit );
    Res = (!iRepr || CecZ_ManGeneratePatterns_rec(&Context, Gia_ManObj(p, iRepr), iReprVal)) &&
        CecZ_ManGeneratePatterns_rec(&Context, Gia_ManObj(p, iCand), iCandVal);
    Gia_ManForEachObjVec( vVisit, p, pObj, k )
        pObj->fMark0 = pObj->fMark1 = 0;
    *pnDiscarded += Context.nDiscarded;
    return Res;
}
static void CecZ_ManCandIterStart( CecZ_Man_t * p )
{
    int i, * pArray;
    assert( p->iPosWrite == 0 );
    assert( p->iPosRead == 0 );
    assert( Vec_IntSize(p->vCands) == 0 );
    for ( i = 1; i < Gia_ManObjNum(p->pAig); i++ )
        if ( Gia_ObjRepr(p->pAig, i) != GIA_VOID )
            Vec_IntPush( p->vCands, i );
    p->nCandidates = Vec_IntSize(p->vCands);
    pArray = Vec_IntArray( p->vCands );
    for ( i = 0; i < Vec_IntSize(p->vCands); i++ )
    {
        int iNew = Abc_Random(0) % Vec_IntSize(p->vCands);
        ABC_SWAP( int, pArray[i], pArray[iNew] );
    }
}
static int CecZ_ManCandIterNext( CecZ_Man_t * p )
{
    while ( Vec_IntSize(p->vCands) > 0 )
    {
        int fStop, iCand = Vec_IntEntry( p->vCands, p->iPosRead );
        if ( (fStop = (Gia_ObjRepr(p->pAig, iCand) != GIA_VOID)) )
            Vec_IntWriteEntry( p->vCands, p->iPosWrite++, iCand );
        if ( ++p->iPosRead == Vec_IntSize(p->vCands) )
        {
            Vec_IntShrink( p->vCands, p->iPosWrite );
            p->iPosWrite = 0;
            p->iPosRead = 0;
        }
        if ( fStop )
            return iCand;
    }
    return 0;
}
static int CecZ_ManGeneratePatterns( CecZ_Man_t * p )
{
    abctime clk = Abc_Clock();
    int i, iCand, nPats = 100 * 64 * p->pAig->nSimWords, CountPat = 0;
    word SuccessSize = 0, FailedSize = 0;
    int nSuccess = 0, fWorkStop = 0;
    word WorkLimit = (word)CECZ_PATTERN_ROUND_WORK * Abc_MaxInt(1, p->vSimAnds ? Vec_IntSize(p->vSimAnds) : Gia_ManAndNum(p->pAig));
    p->pAig->iPatsPi = 0;
    Vec_WrdFill( p->pAig->vSimsPi, Vec_WrdSize(p->pAig->vSimsPi), 0 );
    for ( i = 0; i < nPats; i++ )
        if ( (iCand = CecZ_ManCandIterNext(p)) )
        {
            int iRepr    = Gia_ObjRepr( p->pAig, iCand );
            int iCandVal = Gia_ManObj(p->pAig, iCand)->fPhase;
            int iReprVal = Gia_ManObj(p->pAig, iRepr)->fPhase;
            int Res = CecZ_ManGeneratePatternOne( p->pAig, iRepr,  iReprVal, iCand, !iCandVal, p->vPat, p->vVisit, p->nGenBacktracks, &FailedSize );
            if ( !Res )
            {
                FailedSize += Vec_IntSize(p->vVisit);
                if ( iRepr )
                {
                    Res = CecZ_ManGeneratePatternOne( p->pAig, iRepr, !iReprVal, iCand,  iCandVal, p->vPat, p->vVisit, p->nGenBacktracks, &FailedSize );
                    if ( !Res ) FailedSize += Vec_IntSize(p->vVisit);
                }
            }
            if ( Res )
            {
                int Ret = CecZ_ManPackAddPattern( p->pAig, p->vPat, 1 );
                SuccessSize += Vec_IntSize(p->vVisit);
                nSuccess++;
                if ( p->pAig->vPats )
                {
                    Vec_IntPush( p->pAig->vPats, Vec_IntSize(p->vPat)+2 );
                    Vec_IntAppend( p->pAig->vPats, p->vPat );
                    Vec_IntPush( p->pAig->vPats, -1 );
                }
                if ( Ret == 64 * p->pAig->nSimWords )
                    break;
                if ( ++CountPat == 8 * 64 * p->pAig->nSimWords )
                    break;
            }
            // Stop an overwhelmingly unproductive round after enough attempts.
            // Simulate the patterns already packed, then leave all unresolved
            // candidates to SAT. The bound depends on work, not wall time.
            if ( !p->pPars->fCheckMiter && i >= CECZ_PATTERN_MIN_TRIES && FailedSize > WorkLimit &&
                 FailedSize > CECZ_PATTERN_WORK_RATIO * SuccessSize )
            {
                fWorkStop = 1;
                break;
            }
        }
        else
            break;
    // Start with ordinary justifications. Pattern count alone can hide
    // costly failures; use visited-node totals as a second work estimate.
    p->nGenBacktracks = (word)CountPat * CECZ_PATTERN_YIELD >= (word)Abc_MaxInt(i, 1) &&
        SuccessSize * CECZ_PATTERN_WORK_RATIO >= FailedSize ? CECZ_PATTERN_BACKTRACKS : 0;
    p->timeGenPats += Abc_Clock() - clk;
    p->nSatSat += CountPat;
    if ( nSuccess )
        p->nGenPatSize = Abc_MaxInt(p->nGenPatSize, (int)(SuccessSize/nSuccess));
    // Few short justifications rarely repay another full simulation pass.
    // Leave these candidates to SAT. Retain the search if an earlier round
    // found large justifications, whose counterexamples can be costly for SAT.
    return !fWorkStop && CountPat > 0 && CountPat >= i / p->pPars->nItersMax &&
        (p->pPars->fCheckMiter || CountPat >= 64*p->pAig->nSimWords ||
         p->nGenPatSize >= CECZ_PATTERN_LARGE);
}

/**Function*************************************************************

  Synopsis    [Internal simulation APIs.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
/**Function*************************************************************

  Synopsis    [Builds a bounded cone with unconstrained boundary nodes.]

  Description [Node sharing is retained. An UNSAT proof over this
  abstraction also proves the original cone. The encoding is independent
  of the original object IDs, allowing exact reuse of local proofs.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int CecZ_LocalBuild( CecZ_Man_t * p, int Id, int Depth )
{
    Gia_Obj_t * pObj = Gia_ManObj( p->pNew, Id );
    int Var, Lit0 = -1, Lit1 = -1;
    if ( p->pLocalMap[Id] >= 0 )
        return p->pLocalMap[Id];
    if ( Depth && Vec_IntSize(p->vLocalIds) < CECZ_CONE_LIMIT && Gia_ObjIsAnd(pObj) )
    {
        Lit0 = Abc_Var2Lit( CecZ_LocalBuild(p, Gia_ObjFaninId0(pObj, Id), Depth-1), Gia_ObjFaninC0(pObj) );
        Lit1 = Abc_Var2Lit( CecZ_LocalBuild(p, Gia_ObjFaninId1(pObj, Id), Depth-1), Gia_ObjFaninC1(pObj) );
        if ( (Lit0 > Lit1) ^ Gia_ObjIsXor(pObj) )
            ABC_SWAP( int, Lit0, Lit1 );
    }
    if ( Lit0 == -1 && Gia_ObjIsAnd(pObj) )
        p->fLocalFull = 0;
    Var = Vec_IntSize(p->vLocalIds);
    assert( Var < p->vLocalIds->nCap && 2*Var+1 < p->vLocalGates->nCap );
    p->pLocalMap[Id] = Var;
    p->vLocalIds->pArray[p->vLocalIds->nSize++] = Id;
    p->vLocalGates->pArray[p->vLocalGates->nSize++] = Lit0;
    p->vLocalGates->pArray[p->vLocalGates->nSize++] = Lit1;
    return Var;
}
/**Function*************************************************************

  Synopsis    [Hashes a canonical cone program; hits require an exact comparison.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static unsigned CecZ_LocalHash( CecZ_Man_t * p )
{
    unsigned Hash = 2166136261u;
    int i, Entry;
    Vec_IntForEachEntry( p->vLocalGates, Entry, i )
        Hash = (Hash ^ (unsigned)Entry) * 16777619u;
    return Hash & 65535;
}
/**Function*************************************************************

  Synopsis    [Simulates counterexamples transferred between equally sized supports.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int CecZ_ModelTry( CecZ_Man_t * p, int Var0, int Var1, int Phase )
{
    int i, N, A, B, Pos;
    word Entry, *Bank, *Sim, Values;
    Vec_WrdClear(p->vModelPis);
    p->fModelHit = 0;
    if ( !p->fLocalFull ) return 0;
    for ( i = 1; i < Vec_IntSize(p->vLocalIds); i++ )
        if ( Vec_IntEntry(p->vLocalGates, 2*i) < 0 )
            Vec_WrdPush(p->vModelPis, ((word)(unsigned)Vec_IntEntry(p->vLocalIds, i) << 32) | (unsigned)i);
    N = Vec_WrdSize(p->vModelPis);
    if ( N < 8 || N > 512 ) { Vec_WrdClear(p->vModelPis); return 0; }
    Vec_WrdSort(p->vModelPis, 0);
    Bank = (word *)Vec_PtrEntry(p->vModels, N);
    if ( !Bank ) return 0;
    Vec_WrdFill(p->vModelSim, Vec_IntSize(p->vLocalIds), 0);
    Sim = Vec_WrdArray(p->vModelSim);
    Vec_WrdForEachEntry(p->vModelPis, Entry, i)
        Sim[(unsigned)Entry] = Bank[i+2];
    for ( i = 1; i < Vec_IntSize(p->vLocalIds); i++ )
    {
        A = Vec_IntEntry(p->vLocalGates, 2*i); B = Vec_IntEntry(p->vLocalGates, 2*i+1);
        if ( A < 0 ) continue;
        Sim[i] = A > B ? (Sim[A>>1] ^ -(word)(A&1)) ^ (Sim[B>>1] ^ -(word)(B&1)) :
                        (Sim[A>>1] ^ -(word)(A&1)) & (Sim[B>>1] ^ -(word)(B&1));
    }
    Values = (Sim[Var0] ^ Sim[Var1] ^ -(word)Phase) & Bank[1];
    if ( !Values ) return 0;
    Pos = Abc_Tt6FirstBit(Values);
    Vec_IntClear(p->vLocalCex);
    Vec_WrdForEachEntry(p->vModelPis, Entry, i)
        Vec_IntPush(p->vLocalCex, Abc_Var2Lit((unsigned)Entry, (int)((Sim[(unsigned)Entry] >> Pos)&1)));
    p->fLocalCex = p->fModelHit = 1;
    p->nModelHits++;
    return 1;
}
/**Function*************************************************************

  Synopsis    [Stores two completions of a newly discovered partial counterexample.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void CecZ_ModelSave( CecZ_Man_t * p )
{
    int i, k, Lit, N = Vec_WrdSize(p->vModelPis), Pos;
    word Entry, Bit, *Bank, *Sim;
    if ( !N || p->fModelHit ) return;
    Bank = (word *)Vec_PtrEntry(p->vModels, N);
    if ( !Bank )
    {
        Bank = ABC_CALLOC(word, N+2);
        Vec_PtrWriteEntry(p->vModels, N, Bank);
    }
    Vec_WrdFill(p->vModelSim, Vec_IntSize(p->vLocalIds), 2);
    Sim = Vec_WrdArray(p->vModelSim);
    Vec_IntForEachEntry(p->vLocalCex, Lit, i) Sim[Abc_Lit2Var(Lit)] = Abc_LitIsCompl(Lit);
    for ( k = 0; k < 2; k++ )
    {
        Pos = Bank[0]++ & 63;
        Bit = (word)1 << Pos;
        Bank[1] |= Bit;
        Vec_WrdForEachEntry(p->vModelPis, Entry, i)
        {
            word Val = Sim[(unsigned)Entry];
            Bank[i+2] &= ~Bit;
            if ( Val == 1 || (Val == 2 && k) ) Bank[i+2] |= Bit;
        }
    }
}
/**Function*************************************************************

  Synopsis    [Caches a proof, full-cone counterexample, or exhausted search budget.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void CecZ_LocalSave( CecZ_Man_t * p, int Result, int FailedLimit )
{
    // Neither solver changes the program used by the preceding lookup.
    int Entry, Hash = p->LocalHash;
    if ( Result == GLUCOSE3_UNDEC && !FailedLimit )
        return;
    if ( Result == GLUCOSE3_SAT ) CecZ_ModelSave(p);
    if ( Vec_IntSize(p->vLocalCache) > 4000000 )
    {
        Vec_IntFill( p->vLocalCache, 1, 0 );
        memset( p->pLocalBins, 0, sizeof(int)*65536 );
    }
    Entry = Vec_IntSize(p->vLocalCache);
    Vec_IntPushTwo( p->vLocalCache, p->pLocalBins[Hash], Vec_IntSize(p->vLocalGates) );
    Vec_IntPushTwo( p->vLocalCache, Result, Result == GLUCOSE3_SAT ? Vec_IntSize(p->vLocalCex) : FailedLimit );
    Vec_IntAppend( p->vLocalCache, p->vLocalGates );
    if ( Result == GLUCOSE3_SAT )
        Vec_IntAppend( p->vLocalCache, p->vLocalCex );
    p->pLocalBins[Hash] = Entry;
}
/**Function*************************************************************

  Synopsis    [Checks the exact cache and performs a bounded local SAT probe.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int CecZ_LocalProveInt( CecZ_Man_t * p, int Id0, int Id1, int Phase, int Limit, int Depth, int fSolve )
{
    int i, Id, Var0, Var1, Lits[2], Size, Entry, Status, Result = GLUCOSE3_UNDEC;
    unsigned Hash;
    abctime clk = Abc_Clock();
    p->fLocalFull = 1;
    p->fLocalCex = 0;
    p->nLocalFailedLimit = 0;
    Vec_IntClear( p->vLocalGates );
    Vec_IntClear( p->vLocalIds );
    Vec_IntClear( p->vLocalCex );
    CecZ_LocalBuild( p, 0, 0 );
    Var0 = CecZ_LocalBuild( p, Id0, Depth );
    Var1 = CecZ_LocalBuild( p, Id1, Depth );
    Size = Vec_IntSize(p->vLocalGates);
    Vec_IntPushThree( p->vLocalGates, Var0, Var1, Phase );
    Hash = p->LocalHash = CecZ_LocalHash(p);
    for ( Entry = p->pLocalBins[Hash]; Entry; Entry = Vec_IntEntry(p->vLocalCache, Entry) )
        if ( Vec_IntEntry(p->vLocalCache, Entry+1) == Size+3 &&
             !memcmp(Vec_IntEntryP(p->vLocalCache, Entry+4), Vec_IntArray(p->vLocalGates), sizeof(int)*(Size+3)) )
        {
            Result = Vec_IntEntry(p->vLocalCache, Entry+2);
            if ( Result == GLUCOSE3_UNDEC )
            {
                if ( p->fLocalFull ) p->nLocalFailedLimit = Vec_IntEntry(p->vLocalCache,Entry+3);
                break;
            }
            if ( Result == GLUCOSE3_SAT )
            {
                int nCex = Vec_IntEntry(p->vLocalCache, Entry+3);
                if ( !p->fLocalFull )
                    continue;
                for ( i = 0; i < nCex; i++ )
                    Vec_IntPush( p->vLocalCex, Vec_IntEntry(p->vLocalCache, Entry+4+Size+3+i) );
                p->fLocalCex = 1;
            }
            p->nLocalHit++;
            goto finish;
        }
    if ( CecZ_ModelTry(p, Var0, Var1, Phase) )
    {
        Result = GLUCOSE3_SAT;
        CecZ_LocalSave(p, Result, 0);
        goto finish;
    }
    Result = GLUCOSE3_UNDEC;
    // An identical full cone already exhausted at least this probe budget.
    // Keep the main solver eligible when its requested budget is larger.
    if ( !fSolve || p->nLocalFailedLimit >= (Limit ? Abc_MinInt(100, Limit) : 100) )
        goto finish;
    p->nLocalCalls++;
    sat_solver_reset( p->pLocal );
    bmcg3_sat_solver_set_nvars( p->pLocal, Vec_IntSize(p->vLocalIds) );
    for ( i = 2; i < Size; i += 2 )
        if ( Vec_IntEntry(p->vLocalGates, i) >= 0 )
            sat_solver_set_var_fanin_lit( p->pLocal, i/2, Vec_IntEntry(p->vLocalGates, i), Vec_IntEntry(p->vLocalGates, i+1) );
    Lits[0] = 1;
    sat_solver_addclause( p->pLocal, Lits, 1 );
    sat_solver_start_new_round( p->pLocal );
    sat_solver_mark_cone( p->pLocal, Var0 );
    sat_solver_mark_cone( p->pLocal, Var1 );
    Lits[0] = Abc_Var2Lit( Var0, 1 );
    Lits[1] = Abc_Var2Lit( Var1, Phase );
    sat_solver_set_conflict_budget( p->pLocal, Limit ? Abc_MinInt(100, Limit) : 100 );
    Status = sat_solver_solve( p->pLocal, Lits, 2 );
    if ( Status == GLUCOSE3_UNSAT && Var0 )
    {
        Lits[0] ^= 1;
        Lits[1] ^= 1;
        sat_solver_set_conflict_budget( p->pLocal, Limit ? Abc_MinInt(100, Limit) : 100 );
        Status = sat_solver_solve( p->pLocal, Lits, 2 );
    }
    if ( Status == GLUCOSE3_UNSAT )
    {
        p->nLocalProved++;
        Result = GLUCOSE3_UNSAT;
    }
    else if ( Status == GLUCOSE3_SAT && p->fLocalFull )
    {
        int * pCex = sat_solver_read_cex(p->pLocal);
        for ( i = 1; i <= pCex[0]; i++ )
            if ( Abc_Lit2Var(pCex[i]) )
                Vec_IntPush( p->vLocalCex, Abc_LitNot(pCex[i]) );
        Result = GLUCOSE3_SAT;
        p->fLocalCex = 1;
    }
    CecZ_LocalSave( p, Result, 0 );
finish:
    Vec_IntForEachEntry( p->vLocalIds, Id, i )
        p->pLocalMap[Id] = -1;
    p->timeLocal += Abc_Clock() - clk;
    return Result;
}
/**Function*************************************************************

  Synopsis    [Probes a small window before consulting full-cone proofs.]

  Description [An UNSAT window proves the relation for every boundary
  assignment. An unresolved window expands for cache lookup, but its
  uncached full cone is solved by the persistent main solver. Sparse
  regions retain full local probes, which amortize well across repeated
  logic. Only complete cones supply reusable counterexamples.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int CecZ_LocalProve( CecZ_Man_t * p, int Id0, int Id1, int Phase, int Limit )
{
    int Depth = p->fSparse ? CECZ_CONE_DEPTH : CECZ_PROBE_DEPTH;
    int Res = CecZ_LocalProveInt( p, Id0, Id1, Phase, Limit, Depth, 1 );
    if ( Res != GLUCOSE3_UNDEC || p->fLocalFull || p->fSparse )
        return Res;
    return CecZ_LocalProveInt( p, Id0, Id1, Phase, Limit, CECZ_CONE_DEPTH, 0 );
}
static void CecZ_ManSatSolverRecycle( CecZ_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i;
    // A query above this threshold disables recycling for this invocation.
    // The lifetime maximum is intentionally not reset by later easy queries.
    // Otherwise recycling remains useful for streams of easy, unrelated queries.
    if ( p->nMainConflictsMax > CECZ_RECYCLE_CONFLICTS )
        return;
    p->nRecycles++;
    p->nCallsSince = 0;
    sat_solver_reset( p->pSat );
    // clean mapping of AigIds into SatIds
    Gia_ManForEachObjVec( &p->pNew->vSuppVars, p->pNew, pObj, i )
        CecZ_ObjCleanSatId( p->pNew, pObj );
    Vec_IntClear( &p->pNew->vSuppVars  );  // AigIds for which SatId is defined
    Vec_IntClear( &p->pNew->vCopiesTwo );  // pairs (CiAigId, SatId)
    Vec_IntClear( &p->pNew->vVarMap    );  // mapping of SatId into AigId
}
/**Function*************************************************************

  Synopsis    [Estimates removable nodes with a bounded, reversible MFFC traversal.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int CecZ_ProofGain( CecZ_Man_t * p )
{
    Gia_Man_t * g = p->pAig;
    Gia_Obj_t * Obj;
    int i, Id, A, B, Count = 0, Top = 0, nEdges = 0;
    int Stack[128], Edges[128];
    if ( !p->pGainRefs )
    {
        p->pGainRefs = ABC_CALLOC(int, Gia_ManObjNum(g));
        Gia_ManForEachAnd(g, Obj, i)
        {
            p->pGainRefs[Gia_ObjFaninId0(Obj,i)]++;
            p->pGainRefs[Gia_ObjFaninId1(Obj,i)]++;
        }
        Gia_ManForEachCo(g, Obj, i) p->pGainRefs[Gia_ObjFaninId0p(g,Obj)]++;
    }
    Stack[Top++] = p->iCurObj;
    while ( Top && Count < 64 )
    {
        Id = Stack[--Top];
        Obj = Gia_ManObj(g,Id);
        if ( !Gia_ObjIsAnd(Obj) ) continue;
        Count++;
        A = Gia_ObjFaninId0(Obj,Id); B = Gia_ObjFaninId1(Obj,Id);
        Edges[nEdges++] = A; Edges[nEdges++] = B;
        if ( !--p->pGainRefs[A] ) Stack[Top++] = A;
        if ( !--p->pGainRefs[B] ) Stack[Top++] = B;
    }
    for ( i = 0; i < nEdges; i++ ) p->pGainRefs[Edges[i]]++;
    return Count;
}
/**Function*************************************************************

  Synopsis    [Checks candidate equivalence and caches reusable results.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int CecZ_ManSolveTwo( CecZ_Man_t * p, int iObj0, int iObj1, int fPhase, int * pfEasy, int fEffort, int Limit )
{
    int Vars[2], Lits[2];
    int Used[2] = { 0, 0 }, Beg, Res = GLUCOSE3_UNDEC;
    abctime clk;
    if ( iObj1 < iObj0 )
        ABC_SWAP( int, iObj0, iObj1 );
    assert( iObj0 < iObj1 );
    *pfEasy = 0;
    Res = CecZ_LocalProve(p, iObj0, iObj1, fPhase, Limit);
    if ( Res != GLUCOSE3_UNDEC )
    {
        *pfEasy = 1;
        p->nConflicts[Res == GLUCOSE3_UNSAT][0]++;
        return Res;
    }
    // Spend more effort on large MFFCs. Constants retain the full budget:
    // their propagation can simplify fanouts beyond the immediate MFFC.
    // Miter verification and explicitly unlimited solving also keep full effort.
    // With default E=25000 and C=1000000, gain >= 7 reaches the C ceiling.
    if ( iObj0 && !p->pPars->fCheckMiter && !fEffort && Limit && p->nEffort )
    {
        int Gain = CecZ_ProofGain(p);
        word Effort = (word)(unsigned)p->nEffort * Gain * Gain;
        if ( Effort < (word)(unsigned)Limit ) Limit = (int)Effort;
    }
    // Repeating the same exhausted search cannot justify a merge. Leave the
    // relation unresolved; a larger gain budget can still retry it later.
    if ( Limit && p->nLocalFailedLimit >= Limit )
    {
        p->nFailedHit++;
        return GLUCOSE3_UNDEC;
    }
    p->nCallsSince++;
    if ( p->nCallsSince > p->pPars->nCallsRecycle &&
         Vec_IntSize(&p->pNew->vSuppVars) > p->pPars->nSatVarMax && p->pPars->nSatVarMax )
        CecZ_ManSatSolverRecycle( p );
    clk = Abc_Clock();
    Vars[0] = iObj0 ? CecZ_ObjGetCnfVar( p, iObj0 ) : -1;
    Vars[1] = CecZ_ObjGetCnfVar( p, iObj1 );
    if ( p->pPars->jType > 0 )
        bmcg3_sat_solver_select_cone( p->pSat, iObj0 ? Vars[0] : -1, Vars[1] );
    p->timeCnf += Abc_Clock() - clk;
    clk = Abc_Clock();
    // Check both mismatch polarities without accumulating query-only gates.
    Lits[0] = Abc_Var2Lit( Vars[1], fPhase );
    if ( iObj0 )
    {
        Lits[1] = Lits[0];
        Lits[0] = Abc_Var2Lit( Vars[0], 1 );
    }
    sat_solver_set_conflict_budget( p->pSat, Limit );
    Beg = sat_solver_conflictnum(p->pSat);
    Res = sat_solver_solve( p->pSat, Lits, iObj0 ? 2 : 1 );
    Used[0] = sat_solver_conflictnum(p->pSat) - Beg;
    if ( Res == GLUCOSE3_UNSAT && iObj0 )
    {
        Lits[0] ^= 1;
        Lits[1] ^= 1;
        sat_solver_set_conflict_budget( p->pSat, Limit );
        Beg = sat_solver_conflictnum(p->pSat);
        Res = sat_solver_solve( p->pSat, Lits, 2 );
        Used[1] = sat_solver_conflictnum(p->pSat) - Beg;
    }
    p->nMainConflictsMax = Abc_MaxInt( p->nMainConflictsMax, Abc_MaxInt(Used[0], Used[1]) );

    if ( p->fLocalFull && Res == GLUCOSE3_UNDEC && Limit ) CecZ_LocalSave(p,Res,Limit);
    if ( p->fLocalFull && Res != GLUCOSE3_UNDEC )
    {
        int i, Id;
        if ( Res == GLUCOSE3_SAT && p->pPars->jType )
        {
            int * pCex = sat_solver_read_cex(p->pSat);
            Vec_IntForEachEntry( p->vLocalIds, Id, i )
                p->pLocalMap[Id] = i;
            Vec_IntClear( p->vLocalCex );
            for ( i = 1; i <= pCex[0]; i++ )
            {
                Id = Vec_IntEntry( &p->pNew->vVarMap, Abc_Lit2Var(pCex[i]) );
                if ( Id > 0 && p->pLocalMap[Id] >= 0 )
                    Vec_IntPush( p->vLocalCex, Abc_Var2Lit(p->pLocalMap[Id], !Abc_LitIsCompl(pCex[i])) );
            }
            Vec_IntForEachEntry( p->vLocalIds, Id, i )
                p->pLocalMap[Id] = -1;
        }
        if ( Res == GLUCOSE3_UNSAT || p->pPars->jType )
            CecZ_LocalSave( p, Res, 0 );
    }
    *pfEasy = Used[0] + Used[1] == 0;
    if ( Res != GLUCOSE3_UNDEC )
    {
        int k = Res == GLUCOSE3_UNSAT;
        p->nConflicts[k][0] += *pfEasy;
        p->nConflicts[k][1] += Used[0]+Used[1];
        p->nConflicts[k][2] = Abc_MaxInt(p->nConflicts[k][2], Used[0]+Used[1]);
    }
    if ( p->pPars->fVeryVerbose && Abc_Clock()-clk > CLOCKS_PER_SEC/10 )
        printf( "Hard pair %d %d phase %d status %d conflicts %d %d time %.3f full %d size %d\n", iObj0, iObj1, fPhase, Res, Used[0], Used[1], (double)(Abc_Clock()-clk)/CLOCKS_PER_SEC, p->fLocalFull, Vec_IntSize(p->vLocalIds) );
    return Res;
}
/**Function*************************************************************

  Synopsis    [Exposes queued counterexamples to lazy simulation together.]

  Description [CI values and replay stamps advance together. Until this
  point, both describe the previous batch, so a partially updated pattern
  cannot influence representative selection.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void CecZ_ManFlushPatterns( CecZ_Man_t * p )
{
    int i, Lit, Last = p->pAig->iPatsPi;
    if ( !Vec_IntSize(p->vPendingPats) )
        return;
    p->pAig->iPatsPi = p->iSimPat + 1;
    Vec_IntForEachEntry( p->vPendingPats, Lit, i )
        if ( Lit == -1 )
            p->pAig->iPatsPi++;
        else
            CecZ_ObjSimSetInputBit( p->pAig, Abc_Lit2Var(Lit), Abc_LitIsCompl(Lit) );
    assert( p->pAig->iPatsPi == Last + 1 );
    p->pAig->iPatsPi = p->iSimPat = Last;
    Vec_IntClear( p->vPendingPats );
}
/**Function*************************************************************

  Synopsis    [Batches counterexamples when dense replay becomes expensive.]

  Description [Sparse regions keep immediate replay. Dense regions start
  batching after replay has performed the work of several full scans.
  Batching changes candidate selection only; every merge still requires
  a proof. Full simulation and final refinement always flush the queue.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void CecZ_ManSavePattern( CecZ_Man_t * p )
{
    int i, Lit;
    if ( p->nBatchSize == 1 && !p->fSparse &&
         p->nResimNodes > (word)CECZ_BATCH_WORK * (p->vSimAnds ? Vec_IntSize(p->vSimAnds) : Gia_ManAndNum(p->pAig)) )
        p->nBatchSize = CECZ_BATCH_SIZE;
    if ( p->nBatchSize == 1 )
    {
        Vec_IntForEachEntry( p->vPat, Lit, i )
            CecZ_ObjSimSetInputBit( p->pAig, Abc_Lit2Var(Lit), Abc_LitIsCompl(Lit) );
        p->iSimPat = p->pAig->iPatsPi;
        return;
    }
    Vec_IntAppend( p->vPendingPats, p->vPat );
    Vec_IntPush( p->vPendingPats, -1 );
    if ( p->pAig->iPatsPi % p->nBatchSize == 0 )
        CecZ_ManFlushPatterns( p );
}
static int CecZ_ManSweepNode( CecZ_Man_t * p, int iObj, int iRepr )
{
    abctime clk = Abc_Clock();
    int i, IdAig, IdSat, status, fEasy, RetValue = 1;
    Gia_Obj_t * pObj = Gia_ManObj( p->pAig, iObj );
    Gia_Obj_t * pRepr = Gia_ManObj( p->pAig, iRepr );
    int fCompl = Abc_LitIsCompl(pObj->Value) ^ Abc_LitIsCompl(pRepr->Value) ^ pObj->fPhase ^ pRepr->fPhase;
    int fEffort = p->vCoDrivers ? Vec_BitEntry(p->vCoDrivers, iObj) || Vec_BitEntry(p->vCoDrivers, iRepr) : 0;
    // Only proved aliases contribute origins. A shared snapshot makes this
    // a primary query, including constant candidates in every snapshot.
    int fSecondary = p->vOrigins && !(Vec_IntEntry(p->vOrigins, iObj) & Vec_IntEntry(p->vOrigins, iRepr));
    int Limit = fSecondary ? p->nConfsChoice : (fEffort ? p->pPars->nBTLimitPo : p->pPars->nBTLimit);
    p->iCurObj = iObj;
    status = CecZ_ManSolveTwo( p, Abc_Lit2Var(pRepr->Value), Abc_Lit2Var(pObj->Value), fCompl, &fEasy, fEffort, Limit );
    if ( p->vOrigins )
    {
        p->nOriginCalls[fSecondary][status == GLUCOSE3_UNSAT ? 0 : status == GLUCOSE3_SAT ? 1 : 2]++;
        p->timeOrigin[fSecondary] += Abc_Clock() - clk;
    }
    if ( status == GLUCOSE3_SAT )
    {
        p->nSatSat++;
        Vec_IntClear( p->vPat );
        if ( p->fLocalCex )
        {
            int Lit;
            Vec_IntForEachEntry( p->vLocalCex, Lit, i )
            {
                IdAig = Vec_IntEntry( p->vLocalIds, Abc_Lit2Var(Lit) );
                assert( Gia_ObjIsCi(Gia_ManObj(p->pNew, IdAig)) );
                Vec_IntPush( p->vPat, Abc_Var2Lit(IdAig, Abc_LitIsCompl(Lit)) );
            }
        }
        else if ( p->pPars->jType == 0 )
        {
            Vec_IntForEachEntryDouble( &p->pNew->vCopiesTwo, IdAig, IdSat, i )
                Vec_IntPush( p->vPat, Abc_Var2Lit(IdAig, sat_solver_read_cex_varvalue(p->pSat, IdSat)) );
        }
        else
        {
            int * pCex = sat_solver_read_cex( p->pSat );
            int * pMap = Vec_IntArray(&p->pNew->vVarMap);
            for ( i = 0; i < pCex[0]; )
                Vec_IntPush( p->vPat, Abc_Lit2LitV(pMap, Abc_LitNot(pCex[++i])) );
        }
        if ( p->vSweepCis )
        {
            int Lit;
            Vec_IntForEachEntry( p->vPat, Lit, i )
            {
                assert(Gia_ObjIsCi(Gia_ManObj(p->pNew,Abc_Lit2Var(Lit))));
                Vec_IntWriteEntry(p->vPat,i,Abc_Var2Lit(Vec_IntEntry(p->vSweepCis,Abc_Lit2Var(Lit)-1),Abc_LitIsCompl(Lit)));
            }
        }
        assert( p->pAig->iPatsPi >= 0 && p->pAig->iPatsPi < 64 * p->pAig->nSimWords - 1 );
        p->pAig->iPatsPi++;
        CecZ_ManSavePattern( p );
        if ( p->pAig->vPats )
        {
            Vec_IntPush( p->pAig->vPats, Vec_IntSize(p->vPat)+2 );
            Vec_IntAppend( p->pAig->vPats, p->vPat );
            Vec_IntPush( p->pAig->vPats, -1 );
        }
        if ( fEasy )
            p->timeSatSat0 += Abc_Clock() - clk;
        else
            p->timeSatSat += Abc_Clock() - clk;
        RetValue = 0;
        // Refine the classes when the counterexample batch is full.
        if ( p->pAig->iPatsPi == 64 * p->pAig->nSimWords - 2 )
        {
            abctime clk2 = Abc_Clock();
            CecZ_ManFlushPatterns( p );
            CecZ_ManSimulate( p->pAig, p );
            Vec_IntFill( p->vCexStamps, Gia_ManObjNum(p->pAig), 0 );
            p->pAig->iPatsPi = p->iSimPat = 0;
            Vec_WrdFill( p->pAig->vSimsPi, Vec_WrdSize(p->pAig->vSimsPi), 0 );
            p->timeResimGlo += Abc_Clock() - clk2;
        }
    }
    else if ( status == GLUCOSE3_UNSAT )
    {
        p->nSatUnsat++;
        pObj->Value = Abc_LitNotCond( pRepr->Value, pObj->fPhase ^ pRepr->fPhase );
        Gia_ObjSetProved( p->pAig, iObj );
        if ( p->vOrigins )
            *Vec_IntEntryP(p->vOrigins, iRepr) |= Vec_IntEntry(p->vOrigins, iObj);
        if ( fEasy )
            p->timeSatUnsat0 += Abc_Clock() - clk;
        else
            p->timeSatUnsat += Abc_Clock() - clk;
        RetValue = 1;
    }
    else
    {
        p->nSatUndec++;
        assert( status == GLUCOSE3_UNDEC );
        Gia_ObjSetFailed( p->pAig, iObj );
        p->timeSatUndec += Abc_Clock() - clk;
        RetValue = 2;
    }
    return RetValue;
}
static Gia_Obj_t * CecZ_ManFindRepr( Gia_Man_t * p, CecZ_Man_t * pMan, int iObj )
{
    abctime clk = Abc_Clock();
    int iMem, iRepr;
    assert( Gia_ObjHasRepr(p, iObj) );
    assert( !Gia_ObjProved(p, iObj) );
    iRepr = Gia_ObjRepr(p, iObj);
    assert( iRepr != iObj );
    assert( !Gia_ObjProved(p, iRepr) );
    CecZ_ManSimulate_rec( p, pMan, iObj );
    CecZ_ManSimulate_rec( p, pMan, iRepr );
    if ( CecZ_ObjSimEqual(p, iObj, iRepr) )
    {
        pMan->timeResimLoc += Abc_Clock() - clk;
        return Gia_ManObj(p, iRepr);
    }
    Gia_ClassForEachObj1( p, iRepr, iMem )
    {
        if ( iObj == iMem )
            break;
        if ( Gia_ObjProved(p, iMem) || Gia_ObjFailed(p, iMem) )
            continue;
        CecZ_ManSimulate_rec( p, pMan, iMem );
        if ( CecZ_ObjSimEqual(p, iObj, iMem) )
        {
            pMan->timeResimLoc += Abc_Clock() - clk;
            return Gia_ManObj(p, iMem);
        }
    }
    pMan->timeResimLoc += Abc_Clock() - clk;
    return NULL;
}
static void CecZ_ManRemoveWrongChoices( Gia_Man_t * p )
{
    int i = 0, iObj, iPrev;
    for ( iPrev = i, iObj = Gia_ObjNext(p, i); -1 < iObj; iObj = Gia_ObjNext(p, iPrev) )
    {
        Gia_Obj_t * pRepr = Gia_ObjReprObj(p, iObj);
        assert( pRepr == Gia_ManConst0(p) );
        if( !Gia_ObjFailed(p,iObj) && Abc_Lit2Var(Gia_ManObj(p,iObj)->Value) == Abc_Lit2Var(pRepr->Value) )
        {
            iPrev = iObj;
            continue;
        }
        Gia_ObjSetRepr( p, iObj, GIA_VOID );
        Gia_ObjSetNext( p, iPrev, Gia_ObjNext(p, iObj) );
        Gia_ObjSetNext( p, iObj, 0 );
    }
    Gia_ManForEachClass( p, i )
    {
        for ( iPrev = i, iObj = Gia_ObjNext(p, i); -1 < iObj; iObj = Gia_ObjNext(p, iPrev) )
        {
            Gia_Obj_t * pRepr = Gia_ObjReprObj(p, iObj);
            if( !Gia_ObjFailed(p,iObj) && Abc_Lit2Var(Gia_ManObj(p,iObj)->Value) == Abc_Lit2Var(pRepr->Value) )
            {
                iPrev = iObj;
                continue;
            }
            Gia_ObjSetRepr( p, iObj, GIA_VOID );
            Gia_ObjSetNext( p, iPrev, Gia_ObjNext(p, iObj) );
            Gia_ObjSetNext( p, iObj, 0 );
            }
    }
}

static void CecZ_ManSimulateDumpInfo( CecZ_Man_t * pMan )
{
    Gia_Obj_t * pObj; int i, k, nWords = pMan->pAig->nSimWords, nOuts[2] = {0};
    Vec_Wrd_t * vSims = NULL, * vSimsPi = NULL;
    FILE * pFile = fopen( pMan->pPars->pDumpName, "wb" );
    if ( pFile == NULL ) {
        printf( "Cannot open file \"%s\" for writing primary output information.\n", pMan->pPars->pDumpName );
        return;
    }
    // A trivial miter failure can reach this point before simulation allocation.
    if ( nWords <= 0 )
        nWords = pMan->pPars->nWords;
    if ( Gia_ManCiNum(pMan->pAig) )
    {
        vSimsPi = Vec_WrdStart( Gia_ManCiNum(pMan->pAig) * nWords );
        if ( pMan->pAig->vSimsPi )
        {
            assert( Vec_WrdSize(pMan->pAig->vSimsPi) == (Gia_ManCiNum(pMan->pAig) + 1) * nWords );
            memcpy( Vec_WrdArray(vSimsPi), Vec_WrdArray(pMan->pAig->vSimsPi) + nWords, sizeof(word) * Vec_WrdSize(vSimsPi) );
        }
        if ( Abc_TtIsConst0(Vec_WrdArray(vSimsPi), Gia_ManCiNum(pMan->pAig) * nWords) )
        {
            Vec_WrdFree( vSimsPi );
            vSimsPi = Vec_WrdStartRandom( Gia_ManCiNum(pMan->pAig) * nWords );
        }
        vSims = Gia_ManSimPatSimOut( pMan->pAig, vSimsPi, 1 );
    }
    else
    {
        // With no inputs, the previously computed phases are exact constants.
        // The shared simulator infers its word count by dividing by CI count.
        vSimsPi = Vec_WrdAlloc( 1 );
        vSims = Vec_WrdAlloc( 1 );
        Vec_WrdFill( vSims, Gia_ManCoNum(pMan->pAig) * nWords, 0 );
        Gia_ManForEachCo( pMan->pAig, pObj, i )
            if ( Gia_ObjFanin0(pObj)->fPhase ^ Gia_ObjFaninC0(pObj) )
                Abc_TtFill( Vec_WrdEntryP(vSims, nWords*i), nWords );
    }
    assert( nWords * Gia_ManCiNum(pMan->pAig) == Vec_WrdSize(vSimsPi) );
    Gia_ManForEachCo( pMan->pAig, pObj, i )
    {
        void Extra_PrintHex2( FILE * pFile, unsigned * pTruth, int nVars );
        word * pSims = Vec_WrdEntryP( vSims, nWords*i );
        //Extra_PrintHex2( stdout, (unsigned *)pSims, 8 ); printf( "\n" );
        fprintf( pFile, "%d ", i );
        if ( pMan->pNew && Gia_ObjFanin0Copy(pObj) == 0 )
            nOuts[0]++;
        else if ( Abc_TtIsConst0(pSims, nWords) )
            fprintf( pFile, "-" );
        else {
            int iPat = Abc_TtFindFirstBit2(pSims, nWords);
            for ( k = 0; k < Gia_ManPiNum(pMan->pAig); k++ )
                fprintf( pFile, "%d", Abc_TtGetBit(Vec_WrdEntryP(vSimsPi, nWords*k), iPat) );
            nOuts[1]++;
        }
        fprintf( pFile, "\n" );
    }
    printf( "Information about %d sat, %d unsat, and %d undecided primary outputs was written into file \"%s\".\n",
        nOuts[1], nOuts[0], Gia_ManCoNum(pMan->pAig)-nOuts[1]-nOuts[0], pMan->pPars->pDumpName );
    fclose( pFile );
    Vec_WrdFree( vSims );
    Vec_WrdFree( vSimsPi );
}
/**Function*************************************************************

  Synopsis    [Combines the swept candidate region with the untouched remainder.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * CecZ_ExportSparse( CecZ_Man_t * p )
{
    Gia_Man_t * q, * g = p->pAig;
    Gia_Obj_t * pObj, * pNewObj;
    int * pAlias = ABC_ALLOC(int,Gia_ManObjNum(g));
    int i, a, b, Lit, First, nLive = 1 + Gia_ManCiNum(g) + Gia_ManCoNum(g);
    // Translate proved/hash merges back to original IDs. The first owner of
    // each swept literal precedes its users, including unswept fanouts.
    Gia_ManFillValue(p->pNew);
    Gia_ManConst0(p->pNew)->Value = 0;
    Gia_ManForEachObj( g, pObj, i )
    {
        pObj->fMark0 = 0;
        pAlias[i] = Abc_Var2Lit(i,0);
        if ( pObj->Value != ~0u )
        {
            Lit = pObj->Value;
            pNewObj = Gia_ManObj(p->pNew,Abc_Lit2Var(Lit));
            if ( pNewObj->Value == ~0u )
                pNewObj->Value = Abc_Var2Lit(i,Abc_LitIsCompl(Lit));
            First = pNewObj->Value ^ Abc_LitIsCompl(Lit);
            if ( Abc_Lit2Var(First) < i )
            {
                pAlias[i] = pAlias[Abc_Lit2Var(First)] ^ Abc_LitIsCompl(First);
                continue;
            }
        }
        if ( !Gia_ObjIsAnd(pObj) ) continue;
        a = pAlias[Gia_ObjFaninId0(pObj,i)] ^ Gia_ObjFaninC0(pObj);
        b = pAlias[Gia_ObjFaninId1(pObj,i)] ^ Gia_ObjFaninC1(pObj);
        if ( Gia_ObjIsXor(pObj) )
        {
            if ( a < 2 ) pAlias[i] = b ^ a;
            else if ( b < 2 ) pAlias[i] = a ^ b;
            else if ( (a >> 1) == (b >> 1) ) pAlias[i] = a ^ b;
        }
        else
        {
            if ( a < 2 ) pAlias[i] = a ? b : 0;
            else if ( b < 2 ) pAlias[i] = b ? a : 0;
            else if ( a == b ) pAlias[i] = a;
            else if ( a == (b ^ 1) ) pAlias[i] = 0;
        }
    }
    Gia_ManForEachCo( g, pObj, i )
        Gia_ManObj(g,Abc_Lit2Var(pAlias[Gia_ObjFaninId0p(g,pObj)]))->fMark0 = 1;
    Gia_ManForEachAndReverse( g, pObj, i )
        if ( pObj->fMark0 )
        {
            assert(pAlias[i] == Abc_Var2Lit(i,0));
            Gia_ManObj(g,Abc_Lit2Var(pAlias[Gia_ObjFaninId0(pObj,i)]))->fMark0 = 1;
            Gia_ManObj(g,Abc_Lit2Var(pAlias[Gia_ObjFaninId1(pObj,i)]))->fMark0 = 1;
            nLive++;
        }
    q = Gia_ManStart(nLive);
    q->pName = Abc_UtilStrsav(p->pAig->pName);
    q->pSpec = Abc_UtilStrsav(p->pAig->pSpec);
    if ( p->pAig->pMuxes )
        q->pMuxes = ABC_CALLOC( unsigned, q->nObjsAlloc );
    Gia_ManConst0(g)->Value = 0;
    Gia_ManForEachCi(g, pObj, i)
        pObj->Value = Gia_ManAppendCi(q);
    Gia_ManForEachAnd(g, pObj, i)
        if ( pObj->fMark0 )
        {
            a = pAlias[Gia_ObjFaninId0(pObj,i)] ^ Gia_ObjFaninC0(pObj);
            b = pAlias[Gia_ObjFaninId1(pObj,i)] ^ Gia_ObjFaninC1(pObj);
            a = Gia_ManObj(g,Abc_Lit2Var(a))->Value ^ Abc_LitIsCompl(a);
            b = Gia_ManObj(g,Abc_Lit2Var(b))->Value ^ Abc_LitIsCompl(b);
            pObj->Value = Gia_ObjIsXor(pObj) ?
                Gia_ManAppendXorReal2(q,Abc_LitRegular(a),Abc_LitRegular(b)) ^ ((a ^ b) & 1) : Gia_ManAppendAnd(q,a,b);
        }
    Gia_ManForEachCo(g, pObj, i)
    {
        a = pAlias[Gia_ObjFaninId0p(g,pObj)] ^ Gia_ObjFaninC0(pObj);
        Gia_ManAppendCo(q,Gia_ManObj(g,Abc_Lit2Var(a))->Value ^ Abc_LitIsCompl(a));
    }
    assert(Gia_ManObjNum(q) == nLive);
    Gia_ManSetRegNum(q, Gia_ManRegNum(p->pAig));
    // Class cleanup still compares proved identities, including dangling
    // objects. Keep these canonical identities distinct from export literals.
    Gia_ManForEachObj(g, pObj, i) pObj->Value = pAlias[i];
    Gia_ManCleanMark0(g);
    ABC_FREE(pAlias);
    return q;
}
/**Function*************************************************************

  Synopsis    [Saves proof and hash merges as literals of the original graph.]

  Description [Internal Values are valid only after the swept graph is started.
  Unvisited objects, including nodes outside a sparse sweep, remain singleton
  classes. Candidate representatives and flags are deliberately ignored.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void CecZ_ManSaveEquivs( CecZ_Man_t * p, Vec_Int_t * vEquivs )
{
    Vec_Int_t * vFirst = p->pNew ? Vec_IntStartFull(Gia_ManObjNum(p->pNew)) : NULL;
    Gia_Obj_t * pObj;
    int i, Lit, First;
    Vec_IntClear( vEquivs );
    Gia_ManForEachObj( p->pAig, pObj, i )
    {
        Lit = 2 * i;
        if ( vFirst && !Gia_ObjIsCo(pObj) && ~pObj->Value )
        {
            assert( Abc_Lit2Var(pObj->Value) < Vec_IntSize(vFirst) );
            First = Vec_IntEntry( vFirst, Abc_Lit2Var(pObj->Value) );
            if ( First < 0 )
                Vec_IntWriteEntry( vFirst, Abc_Lit2Var(pObj->Value), Lit ^ (pObj->Value & 1) );
            else
                Lit = First ^ (pObj->Value & 1);
        }
        Vec_IntPush( vEquivs, Lit );
    }
    Vec_IntFreeP( &vFirst );
}

/**Function*************************************************************

  Synopsis    [Simulates, refines, and proves candidate equivalences.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int CecZ_ManPerformSweeping( Gia_Man_t * p, Cec_ParFra_t * pPars, Gia_Man_t ** ppNew, int nEffort, Vec_Int_t * vOrigins, int nConfsChoice, Vec_Int_t * vEquivs )
{

    CecZ_Man_t * pMan = CecZ_ManCreate( p, pPars );
    Gia_Obj_t * pObj, * pRepr;
    int i = 0, fSimulate = 1, Id, Pos, Count, Capacity, nLastCandidates;
    pMan->nEffort = nEffort;
    pMan->vOrigins = vOrigins;
    pMan->nConfsChoice = nConfsChoice;
    if ( pPars->fVerbose )
        printf( "Solver type = %d. Simulate %d words in %d rounds. SAT with %d confs. Recycle after %d SAT calls.\n",
            pPars->jType, pPars->nWords, pPars->nRounds, pPars->nBTLimit, pPars->nCallsRecycle );

    // this is currently needed to have a correct mapping
    Gia_ManForEachCi( p, pObj, i )
        assert( Gia_ObjId(p, pObj) == i+1 );

    // Supplied patterns use CI indices; replay uses object IDs, including zero.
    if ( p->vSimsPi && p->nSimWords > 0 )
    {
        int nEntries = Gia_ManCiNum(p) * p->nSimWords;
        Vec_WrdFillExtra( p->vSimsPi, nEntries + p->nSimWords, 0 );
        memmove( Vec_WrdArray(p->vSimsPi) + p->nSimWords, Vec_WrdArray(p->vSimsPi), sizeof(word) * nEntries );
        memset( Vec_WrdArray(p->vSimsPi), 0, sizeof(word) * p->nSimWords );
    }

    // check if any output trivially fails under all-0 pattern
    Abc_Random( 1 );
    // Ordinary initial simulation includes the all-zero input as bit zero.
    // Supplied patterns, level-limited sweeping, and early miter checks need
    // phases independently of the nodes/signatures in that first round.
    pMan->fSimPhase = !pPars->fCheckMiter && !pPars->nLevelMax &&
        !(p->vSimsPi && p->nSimWords > 0);
    if ( !pMan->fSimPhase )
        Gia_ManSetPhase( p );
    if ( pPars->nLevelMax )
        Gia_ManLevelNum(p);
    if ( pPars->fCheckMiter )
    {
        Gia_ManForEachCo( p, pObj, i )
            if ( pObj->fPhase )
            {
                p->pCexSeq = CecZ_ManDeriveCex( p, i, -1 );
                goto finalize;
            }
    }

    if( p->vSimsPi && p->nSimWords > 0){ // if the simulation pis are already set, do not generate new ones
        pPars->nWords = p->nSimWords;
        Vec_WrdFreeP( &p->vSims );
        p->vSims     = Vec_WrdStart( Gia_ManObjNum(p) *  pPars->nWords);
        assert( Vec_WrdSize(p->vSimsPi) == (Gia_ManCiNum(p) + 1) * p->nSimWords );
        Gia_ManForEachCiId(p, Id, i){
          memcpy( Vec_WrdEntryP(p->vSims, Id*p->nSimWords), Vec_WrdEntryP(p->vSimsPi, Id*p->nSimWords), sizeof(word)*p->nSimWords );
        }
        CecZ_ManSimulate( p, pMan );
        if ( pPars->fCheckMiter && !CecZ_ManSimulateCos(p) ) // cex detected
          goto finalize;
        goto execute_sat;
    }

    // simulate one round and create classes
    // A narrow first signature identifies the candidate fanin union. Allocate
    // the requested wider signatures only after this often much smaller union
    // is known. Supplied-pattern and early-miter paths retain their semantics.
    CecZ_ManSimAlloc( p, pPars->fCheckMiter ? pPars->nWords : Abc_MinInt(pPars->nWords, 2) );
    CecZ_ManSimulateCis( p, pMan );
    CecZ_ManSimulate( p, pMan );
    if ( pPars->fCheckMiter && !CecZ_ManSimulateCos(p) ) // cex detected
        goto finalize;
    if ( pPars->fVerbose )
        CecZ_ManPrintStats( p, pPars, pMan, 1 );

    if ( !pPars->fCheckMiter )
        CecZ_SimSelect( pMan );
    if ( p->nSimWords != pPars->nWords )
    {
        CecZ_ManSimAlloc( p, pPars->nWords );
        CecZ_ManSimulateCis( p, pMan );
        CecZ_ManSimulate( p, pMan );
    }
    // perform simulation
    for ( i = 0; i < pPars->nRounds; i++ )
    {
        CecZ_ManSimulateCis( p, pMan );
        CecZ_ManSimulate( p, pMan );
        if ( pPars->fCheckMiter && !CecZ_ManSimulateCos(p) ) // cex detected
            goto finalize;
        if ( i && i % Abc_MaxInt(1, pPars->nRounds / 5) == 0 && pPars->fVerbose )
            CecZ_ManPrintStats( p, pPars, pMan, 1 );
        // After at least two additional rounds, let guided patterns and SAT
        // handle classes that uniform and biased random patterns rarely split.
        if ( !pPars->fCheckMiter && i >= 1 &&
             pMan->nRefined < Abc_MaxInt(CECZ_SIM_MIN_SPLITS, Gia_ManAndNum(p)/CECZ_SIM_SPLIT_RATIO) )
            break;
    }

    // perform additional simulation
    if ( !pPars->fCheckMiter )
        CecZ_SimSelect( pMan );
    CecZ_ManCandIterStart( pMan );
    nLastCandidates = pMan->nCandidates;
    for ( i = 0; fSimulate && i < pPars->nGenIters; i++ )
    {
        int Before = pMan->nCandidates, After;
        CecZ_ManSimulateCis( p, pMan );
        fSimulate = CecZ_ManGeneratePatterns( pMan );
        CecZ_ManSimulate( p, pMan );
        After = pMan->nCandidates;
        // Classes only split. Refresh their fanin union after a large reduction.
        if ( !pPars->fCheckMiter && After < nLastCandidates/2 )
        {
            CecZ_SimSelect( pMan );
            nLastCandidates = After;
        }
        if ( pMan->vSimAnds && Vec_IntSize(pMan->vSimAnds) < Gia_ManAndNum(p)/4 &&
             Before - After < Abc_MaxInt(16, Before/100) )
            fSimulate = 0;
        if ( pPars->fCheckMiter && !CecZ_ManSimulateCos(p) ) // cex detected
            goto finalize;
        if ( i && i % 5 == 0 && pPars->fVerbose )
            CecZ_ManPrintStats( p, pPars, pMan, 1 );
    }
    execute_sat:
    if ( !pPars->fCheckMiter ) CecZ_SimSelect(pMan);
    if ( i && i % 5 && pPars->fVerbose )
        CecZ_ManPrintStats( p, pPars, pMan, 1 );

    p->iPatsPi = 0;
    Vec_WrdFill( p->vSimsPi, Vec_WrdSize(p->vSimsPi), 0 );
    pMan->nSatSat = 0;
    pMan->fSparse = pMan->vSimAnds && Vec_IntSize(pMan->vSimAnds) < Gia_ManAndNum(p)/2;
    if ( pMan->fSparse ) pMan->vSweepCis = Vec_IntDup(pMan->vSimCis);
    Capacity = pMan->fSparse ? Vec_IntSize(pMan->vSweepCis)+Vec_IntSize(pMan->vSimAnds)+1 : Gia_ManObjNum(p);
    pMan->pNew = CecZ_ManStartNew( p, Capacity, pMan->vSweepCis );
    CecZ_ManHashClasses( pMan );
    pMan->pLocalMap = ABC_FALLOC( int, Capacity );
    Count = pMan->fSparse ? Vec_IntSize(pMan->vSimAnds) : Gia_ManObjNum(p);
    for ( Pos = 0; Pos < Count; Pos++ )
    {
        int id_obj, id_repr;
        i = pMan->fSparse ? Vec_IntEntry(pMan->vSimAnds, Pos) : Pos;
        pObj = Gia_ManObj(p, i);
        if ( !Gia_ObjIsAnd(pObj) ) continue;
        pMan->nAndNodes++;
        pObj->Value = CecZ_ManHashNode( pMan, i, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj), Gia_ObjIsXor(pObj) );
        if ( pPars->nLevelMax && Gia_ObjLevel(p, pObj) > pPars->nLevelMax )
            continue;
        // select representative based on candidate equivalence classes
        pRepr = Gia_ObjReprObj( p, i );
        if ( pRepr == NULL )
            continue;
        if ( 1 ) // select representative based on recent counter-examples
        {
            pRepr = CecZ_ManFindRepr( p, pMan, i );
            if ( pRepr == NULL )
                continue;
        }
        id_obj = Gia_ObjId( p, pObj );
        id_repr = Gia_ObjId( p, pRepr );

        if ( Abc_Lit2Var(pObj->Value) == Abc_Lit2Var(pRepr->Value) )
        {
            if ( pPars->fBMiterInfo )
            {
                Bnd_ManMerge( id_repr, id_obj, pObj->fPhase ^ pRepr->fPhase );
            }

            assert( (pObj->Value ^ pRepr->Value) == (pObj->fPhase ^ pRepr->fPhase) );
            Gia_ObjSetProved( p, i );
            if ( vOrigins )
                *Vec_IntEntryP(vOrigins, id_repr) |= Vec_IntEntry(vOrigins, id_obj);
            continue;
        }
        if ( CecZ_ManSweepNode(pMan, i, Gia_ObjId(p, pRepr)) && Gia_ObjProved(p, i) )
        {
            if (pPars->fBMiterInfo){

                Bnd_ManMerge( id_repr, id_obj, pObj->fPhase ^ pRepr->fPhase );

            }
            pObj->Value = Abc_LitNotCond( pRepr->Value, pObj->fPhase ^ pRepr->fPhase );

        }
    }

    if ( pPars->fBMiterInfo )
    {
        // print
        Bnd_ManFinalizeMappings();
        // Bnd_ManPrintMappings();
    }

    if ( p->iPatsPi > 0 )
    {
        abctime clk2 = Abc_Clock();
        CecZ_ManFlushPatterns( pMan );
        CecZ_ManSimulate( p, pMan );
        p->iPatsPi = pMan->iSimPat = 0;
        Vec_IntFill( pMan->vCexStamps, Gia_ManObjNum(p), 0 );
        pMan->timeResimGlo += Abc_Clock() - clk2;
    }
    if ( pPars->fVerbose )
        CecZ_ManPrintStats( p, pPars, pMan, 0 );
    // Export reuses input Values for output literals (or original-ID aliases).
    // Save proved internal identities before either export changes their domain.
    if ( vEquivs )
    {
        CecZ_ManSaveEquivs( pMan, vEquivs );
        vEquivs = NULL;
    }
    if ( ppNew && pMan->fSparse )
        *ppNew = CecZ_ExportSparse(pMan);
    else if ( ppNew )
    {
        Gia_ManForEachCo( p, pObj, i )
            pObj->Value = Gia_ManAppendCo( pMan->pNew, Gia_ObjFanin0Copy(pObj) );
        *ppNew = Gia_ManCleanup( pMan->pNew );
    }
finalize:
    if ( vEquivs )
        CecZ_ManSaveEquivs( pMan, vEquivs );
    if ( pPars->fVerbose && vOrigins )
        for ( i = 0; i < 2; i++ )
            printf( "%s equivalences: limit %d  proved %d  disproved %d  unresolved %d  query time %.3f sec\n",
                i ? "Secondary" : "Primary", i ? nConfsChoice : pPars->nBTLimit,
                pMan->nOriginCalls[i][0], pMan->nOriginCalls[i][1], pMan->nOriginCalls[i][2],
                (double)pMan->timeOrigin[i] / CLOCKS_PER_SEC );
    if ( pPars->fVerbose )
        printf( "SAT calls = %d:  P = %d (0=%d a=%.2f m=%d)  D = %d (0=%d a=%.2f m=%d)  F = %d   Sim = %d  Recyc = %d  Xor = %.2f %%\n",
            pMan->nSatUnsat + pMan->nSatSat + pMan->nSatUndec,
            pMan->nSatUnsat, pMan->nConflicts[1][0], (float)pMan->nConflicts[1][1]/Abc_MaxInt(1, pMan->nSatUnsat-pMan->nConflicts[1][0]), pMan->nConflicts[1][2],
            pMan->nSatSat,   pMan->nConflicts[0][0], (float)pMan->nConflicts[0][1]/Abc_MaxInt(1, pMan->nSatSat  -pMan->nConflicts[0][0]), pMan->nConflicts[0][2],
            pMan->nSatUndec,
            pMan->nSimulates, pMan->nRecycles, 100.0*pMan->nGates[1]/Abc_MaxInt(1, pMan->nGates[0]+pMan->nGates[1]) );
    if ( pPars->pDumpName )
        CecZ_ManSimulateDumpInfo( pMan );
    CecZ_ManDestroy( pMan );
    if ( ppNew && *ppNew == NULL )
    {
        // Early miter exits must preserve explicit XORs as well.
        *ppNew = p->pMuxes ? Gia_ManDupMarked(p) : Gia_ManDup(p);
        if ( p->pMuxes && p->pCexSeq )
            (*ppNew)->pCexSeq = Abc_CexDup( p->pCexSeq, Gia_ManRegNum(p) );
    }
    if ( p->pNexts ) CecZ_ManRemoveWrongChoices( p );
    return p->pCexSeq ? 0 : 1;
}
/**Function*************************************************************

  Synopsis    [Runs proof-cached SAT sweeping on a GIA with CIs first.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * CecZ_ManSimulateTest( Gia_Man_t * p, Cec_ParFra_t * pPars, int nEffort )
{
    Gia_Man_t * pNew = NULL;
    int i, Id;
    int nWords = p->vSimsPi && p->nSimWords > 0 ? p->nSimWords : pPars->nWords;
    if ( pPars->fUseCones || pPars->fDualOut || pPars->fRunCSat || pPars->fRewriting )
    {
        Abc_Print( -1, "&fraig -z does not support -k, -d, -c, or -r.\n" );
        return NULL;
    }
    if ( Gia_ManBufNum(p) || Gia_ManMuxNum(p) || p->pManTime )
    {
        Abc_Print( -1, "&fraig -z requires an AIG without buffers, explicit MUXes, or timing boxes.\n" );
        return NULL;
    }
    Gia_ManForEachCiId( p, Id, i )
        if ( Id != i+1 )
        {
            Abc_Print( -1, "&fraig -z requires CIs to precede all other objects.\n" );
            return NULL;
        }
    if ( pPars->jType < 0 || pPars->jType > 2 || nWords < 1 ||
         nWords > INT_MAX/6400 || nWords > INT_MAX/Gia_ManObjNum(p) ||
         pPars->nBTLimit < 0 || pPars->nItersMax < 1 || nEffort < 0 )
    {
        Abc_Print( -1, "&fraig -z: invalid solver, simulation size, or conflict budget.\n" );
        return NULL;
    }
    if ( p->vSimsPi && p->nSimWords > 0 && Vec_WrdSize(p->vSimsPi) != Gia_ManCiNum(p)*nWords )
    {
        Abc_Print( -1, "&fraig -z: the supplied simulation vector has the wrong size.\n" );
        return NULL;
    }
    CecZ_ManPerformSweeping( p, pPars, &pNew, nEffort, NULL, 0, NULL );

    return pNew;
}

/**Function*************************************************************

  Synopsis    [Proves equivalence classes without exporting a reduced graph.]

  Description [The caller supplies a plain snapshot miter with CIs first.
  vEquivs maps each input object to a literal of the input graph. Only merges
  in the swept graph establish these relations, not candidate classes or their
  Proved flags. Unvisited objects retain their own literal. The vector is saved
  before the internal graph is destroyed and includes complemented relations.
  Snapshot masks are updated only by proved equivalences. Overlapping masks
  receive the primary budget; disjoint masks receive the secondary budget.
  These settings are local to choices; standalone -z keeps its defaults.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int CecZ_ManComputeEquivs( Gia_Man_t * p, Vec_Int_t * vOrigins, Vec_Int_t * vEquivs, int nConfs, int nConfsChoice, int fVerbose )
{
    extern void Cec4_ManSetParams( Cec_ParFra_t * pPars );
    Cec_ParFra_t Pars;
    Cec4_ManSetParams( &Pars );
    Pars.nGenIters = 0;
    Pars.jType = 1;
    Pars.nBTLimit = nConfs;
    Pars.fVerbose = fVerbose;
    if ( nConfs < 0 || nConfsChoice < 0 || Gia_ManObjNum(p) > INT_MAX / Pars.nWords ||
         !vEquivs || !vOrigins || Vec_IntSize(vOrigins) != Gia_ManObjNum(p) ) return 0;
    return CecZ_ManPerformSweeping( p, &Pars, NULL, 0, vOrigins, nConfsChoice, vEquivs );
}

ABC_NAMESPACE_IMPL_END
