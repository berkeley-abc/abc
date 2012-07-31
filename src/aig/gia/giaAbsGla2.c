/**CFile****************************************************************

  FileName    [gia.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Scalable gate-level abstraction.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: gia.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "giaAbsRef.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver2.h"
#include "base/main/main.h"

ABC_NAMESPACE_IMPL_START

//#if 0

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define GA2_BIG_NUM 0x3FFFFFFF

typedef struct Ga2_Man_t_ Ga2_Man_t; // manager
struct Ga2_Man_t_
{
    // user data
    Gia_Man_t *    pGia;         // working AIG manager
    Gia_ParVta_t * pPars;        // parameters
    // markings 
    Vec_Ptr_t *    vCnfs;        // for each object: CNF0, CNF1
    // abstraction
    Vec_Int_t *    vIds;         // abstraction ID for each GIA object
    Vec_Int_t *    vProofIds;    // mapping of GIA objects into their proof IDs
    Vec_Int_t *    vAbs;         // array of abstracted objects
    Vec_Int_t *    vValues;      // array of objects with abstraction ID assigned
    int            nProofIds;    // the counter of proof IDs
    int            LimAbs;       // limit value for starting abstraction objects
    int            LimPpi;       // limit value for starting PPI objects
    int            nMarked;      // total number of marked nodes and flops
    // refinement
    Rnm_Man_t *    pRnm;         // refinement manager
    // SAT solver and variables
    Vec_Ptr_t *    vId2Lit;      // mapping, for each timeframe, of object ID into SAT literal
    sat_solver2 *  pSat;         // incremental SAT solver
    int            nSatVars;     // the number of SAT variables
    int            nCexes;       // the number of counter-examples
    int            nObjAdded;    // objs added during refinement
    // temporaries
    Vec_Int_t *    vLits;
    Vec_Int_t *    vIsopMem;
    char * pSopSizes, ** pSops;  // CNF representation
    // statistics  
    clock_t        timeStart;
    clock_t        timeInit;
    clock_t        timeSat;
    clock_t        timeUnsat;
    clock_t        timeCex;
    clock_t        timeOther;
};

static inline int         Ga2_ObjOffset( Gia_Man_t * p, Gia_Obj_t * pObj )       { return Vec_IntEntry(p->vMapping, Gia_ObjId(p, pObj));                                                    }
static inline int         Ga2_ObjLeaveNum( Gia_Man_t * p, Gia_Obj_t * pObj )     { return Vec_IntEntry(p->vMapping, Ga2_ObjOffset(p, pObj));                                                }
static inline int *       Ga2_ObjLeavePtr( Gia_Man_t * p, Gia_Obj_t * pObj )     { return Vec_IntEntryP(p->vMapping, Ga2_ObjOffset(p, pObj) + 1);                                           }
static inline unsigned    Ga2_ObjTruth( Gia_Man_t * p, Gia_Obj_t * pObj )        { return (unsigned)Vec_IntEntry(p->vMapping, Ga2_ObjOffset(p, pObj) + Ga2_ObjLeaveNum(p, pObj) + 1);       }
static inline int         Ga2_ObjRefNum( Gia_Man_t * p, Gia_Obj_t * pObj )       { return (unsigned)Vec_IntEntry(p->vMapping, Ga2_ObjOffset(p, pObj) + Ga2_ObjLeaveNum(p, pObj) + 2);       }
static inline Vec_Int_t * Ga2_ObjLeaves( Gia_Man_t * p, Gia_Obj_t * pObj )       { static Vec_Int_t v; v.nSize = Ga2_ObjLeaveNum(p, pObj), v.pArray = Ga2_ObjLeavePtr(p, pObj); return &v;  }

static inline int         Ga2_ObjId( Ga2_Man_t * p, Gia_Obj_t * pObj )           { return Vec_IntEntry(p->vIds, Gia_ObjId(p->pGia, pObj));                                                  }
static inline void        Ga2_ObjSetId( Ga2_Man_t * p, Gia_Obj_t * pObj, int i ) { Vec_IntWriteEntry(p->vIds, Gia_ObjId(p->pGia, pObj), i);                                                 }

static inline Vec_Int_t * Ga2_ObjCnf0( Ga2_Man_t * p, Gia_Obj_t * pObj )         { assert(Ga2_ObjId(p,pObj) >= 0); return Vec_PtrEntry( p->vCnfs, 2*Ga2_ObjId(p,pObj)   );                  }
static inline Vec_Int_t * Ga2_ObjCnf1( Ga2_Man_t * p, Gia_Obj_t * pObj )         { assert(Ga2_ObjId(p,pObj) >= 0); return Vec_PtrEntry( p->vCnfs, 2*Ga2_ObjId(p,pObj)+1 );                  }

static inline int         Ga2_ObjIsAbs0( Ga2_Man_t * p, Gia_Obj_t * pObj )       { assert(Ga2_ObjId(p,pObj) >= 0); return Ga2_ObjId(p,pObj) >= 0         && Ga2_ObjId(p,pObj) < p->LimAbs;  }
static inline int         Ga2_ObjIsLeaf0( Ga2_Man_t * p, Gia_Obj_t * pObj )      { assert(Ga2_ObjId(p,pObj) >= 0); return Ga2_ObjId(p,pObj) >= p->LimAbs && Ga2_ObjId(p,pObj) < p->LimPpi;  }
static inline int         Ga2_ObjIsAbs( Ga2_Man_t * p, Gia_Obj_t * pObj )        { return Ga2_ObjId(p,pObj) >= 0 &&  Ga2_ObjCnf0(p,pObj);                                                   }
static inline int         Ga2_ObjIsLeaf( Ga2_Man_t * p, Gia_Obj_t * pObj )       { return Ga2_ObjId(p,pObj) >= 0 && !Ga2_ObjCnf0(p,pObj);                                                   }

static inline Vec_Int_t * Ga2_MapFrameMap( Ga2_Man_t * p, int f )                { return (Vec_Int_t *)Vec_PtrEntry( p->vId2Lit, f );                                                       }

// returns literal of this object, or -1 if SAT variable of the object is not assigned
static inline int Ga2_ObjFindLit( Ga2_Man_t * p, Gia_Obj_t * pObj, int f )  
{ 
    int Id = Ga2_ObjId(p,pObj);
    assert( Ga2_ObjId(p,pObj) >= 0 && Ga2_ObjId(p,pObj) < Vec_IntSize(p->vValues) );
    return Vec_IntEntry( Ga2_MapFrameMap(p, f), Ga2_ObjId(p,pObj) );
}
// inserts literal of this object
static inline void Ga2_ObjAddLit( Ga2_Man_t * p, Gia_Obj_t * pObj, int f, int Lit )  
{ 
    assert( Lit > 1 );
    assert( Ga2_ObjFindLit(p, pObj, f) == -1 );
    Vec_IntSetEntry( Ga2_MapFrameMap(p, f), Ga2_ObjId(p,pObj), Lit );
}
// returns or inserts-and-returns literal of this object
static inline int Ga2_ObjFindOrAddLit( Ga2_Man_t * p, Gia_Obj_t * pObj, int f )  
{ 
    int Lit = Ga2_ObjFindLit( p, pObj, f );
    if ( Lit == -1 )
    {
        Lit = toLitCond( p->nSatVars++, 0 );
        Ga2_ObjAddLit( p, pObj, f, Lit );
    }
    assert( Lit > 1 );
    return Lit;
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computes truth table for the marked node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned Ga2_ObjComputeTruth_rec( Gia_Man_t * p, Gia_Obj_t * pObj, int fFirst )
{
    unsigned Val0, Val1;
    if ( pObj->fPhase && !fFirst )
        return pObj->Value;
    assert( Gia_ObjIsAnd(pObj) );
    Val0 = Ga2_ObjComputeTruth_rec( p, Gia_ObjFanin0(pObj), 0 );
    Val1 = Ga2_ObjComputeTruth_rec( p, Gia_ObjFanin1(pObj), 0 );
    return (Gia_ObjFaninC0(pObj) ? ~Val0 : Val0) & (Gia_ObjFaninC1(pObj) ? ~Val1 : Val1);
}
unsigned Ga2_ManComputeTruth( Gia_Man_t * p, Gia_Obj_t * pRoot, Vec_Int_t * vLeaves )
{
    static unsigned uTruth5[5] = { 0xAAAAAAAA, 0xCCCCCCCC, 0xF0F0F0F0, 0xFF00FF00, 0xFFFF0000 };
    Gia_Obj_t * pObj;
    int i;
    Gia_ManForEachObjVec( vLeaves, p, pObj, i )
        pObj->Value = uTruth5[i];
    return Ga2_ObjComputeTruth_rec( p, pRoot, 1 );
}

/**Function*************************************************************

  Synopsis    [Returns AIG marked for CNF generation.]

  Description [The marking satisfies the following requirements:
  Each marked node has the number of marked fanins no more than N.]
               
  SideEffects [Uses pObj->fPhase to store the markings.]

  SeeAlso     []

***********************************************************************/
int Ga2_ManBreakTree_rec( Gia_Man_t * p, Gia_Obj_t * pObj, int fFirst, int N )
{   // breaks a tree rooted at the node into N-feasible subtrees
    int Val0, Val1;
    if ( pObj->fPhase && !fFirst )
        return 1;
    Val0 = Ga2_ManBreakTree_rec( p, Gia_ObjFanin0(pObj), 0, N );
    Val1 = Ga2_ManBreakTree_rec( p, Gia_ObjFanin1(pObj), 0, N );
    if ( Val0 + Val1 < N )
        return Val0 + Val1;
    if ( Val0 + Val1 == N )
    {
        pObj->fPhase = 1;
        return 1;
    }
    assert( Val0 + Val1 > N );
    assert( Val0 < N && Val1 < N );
    if ( Val0 >= Val1 )
    {
        Gia_ObjFanin0(pObj)->fPhase = 1;
        Val0 = 1;
    }
    else 
    {
        Gia_ObjFanin1(pObj)->fPhase = 1;
        Val1 = 1;
    }
    if ( Val0 + Val1 < N )
        return Val0 + Val1;
    if ( Val0 + Val1 == N )
    {
        pObj->fPhase = 1;
        return 1;
    }
    assert( 0 );
    return -1;
}
int Ga2_ManCheckNodesAnd( Gia_Man_t * p, Vec_Int_t * vNodes )
{
    Gia_Obj_t * pObj;
    int i;
    Gia_ManForEachObjVec( vNodes, p, pObj, i )
        if ( (!Gia_ObjFanin0(pObj)->fPhase && Gia_ObjFaninC0(pObj)) || 
             (!Gia_ObjFanin1(pObj)->fPhase && Gia_ObjFaninC1(pObj)) )
            return 0;
    return 1;
}
void Ga2_ManCollectNodes_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vNodes, int fFirst )
{
    if ( pObj->fPhase && !fFirst )
        return;
    assert( Gia_ObjIsAnd(pObj) );
    Ga2_ManCollectNodes_rec( p, Gia_ObjFanin0(pObj), vNodes, 0 );
    Ga2_ManCollectNodes_rec( p, Gia_ObjFanin1(pObj), vNodes, 0 );
    Vec_IntPush( vNodes, Gia_ObjId(p, pObj) );

}
void Ga2_ManCollectLeaves_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vLeaves, int fFirst )
{
    if ( pObj->fPhase && !fFirst )
    {
        Vec_IntPushUnique( vLeaves, Gia_ObjId(p, pObj) );
        return;
    }
    assert( Gia_ObjIsAnd(pObj) );
    Ga2_ManCollectLeaves_rec( p, Gia_ObjFanin0(pObj), vLeaves, 0 );
    Ga2_ManCollectLeaves_rec( p, Gia_ObjFanin1(pObj), vLeaves, 0 );
}
int Ga2_ManMarkup( Gia_Man_t * p, int N )
{
    static unsigned uTruth5[5] = { 0xAAAAAAAA, 0xCCCCCCCC, 0xF0F0F0F0, 0xFF00FF00, 0xFFFF0000 };
    clock_t clk = clock();
    Vec_Int_t * vLeaves;
    Gia_Obj_t * pObj;
    int i, k, Leaf, CountMarks;
    vLeaves = Vec_IntAlloc( 100 );

/*
    // label nodes with multiple fanouts and inputs MUXes
    Gia_ManForEachObj( p, pObj, i )
    {
        pObj->Value = 0;
        if ( !Gia_ObjIsAnd(pObj) )
            continue;
        Gia_ObjFanin0(pObj)->Value++;
        Gia_ObjFanin1(pObj)->Value++;
        if ( !Gia_ObjIsMuxType(pObj) )
            continue;
        Gia_ObjFanin0(Gia_ObjFanin0(pObj))->Value++;
        Gia_ObjFanin1(Gia_ObjFanin0(pObj))->Value++;
        Gia_ObjFanin0(Gia_ObjFanin1(pObj))->Value++;
        Gia_ObjFanin1(Gia_ObjFanin1(pObj))->Value++;
    }
    Gia_ManForEachObj( p, pObj, i )
    {
        pObj->fPhase = 0;
        if ( Gia_ObjIsAnd(pObj) )
            pObj->fPhase = (pObj->Value > 1);
        else if ( Gia_ObjIsCo(pObj) )
            Gia_ObjFanin0(pObj)->fPhase = 1;
        else 
            pObj->fPhase = 1;
    } 
    // add marks when needed
    Gia_ManForEachAnd( p, pObj, i )
    {
        if ( !pObj->fPhase )
            continue;
        Vec_IntClear( vLeaves );
        Ga2_ManCollectLeaves_rec( p, pObj, vLeaves, 1 );
        if ( Vec_IntSize(vLeaves) > N )
            Ga2_ManBreakTree_rec( p, pObj, 1, N );
    }
*/
    Gia_ManForEachObj( p, pObj, i )
        pObj->fPhase = !Gia_ObjIsCo(pObj);

    // verify that the tree is split correctly
    Vec_IntFreeP( &p->vMapping );
    p->vMapping = Vec_IntStart( Gia_ManObjNum(p) );
    Gia_ManForEachRo( p, pObj, i )
    {
        Gia_Obj_t * pObjRi = Gia_ObjRoToRi(p, pObj);
        assert( pObj->fPhase );
        assert( Gia_ObjFanin0(pObjRi)->fPhase );
        // create map
        Vec_IntWriteEntry( p->vMapping, Gia_ObjId(p, pObj), Vec_IntSize(p->vMapping) );
        Vec_IntPush( p->vMapping, 1 );
        Vec_IntPush( p->vMapping, Gia_ObjFaninId0p(p, pObjRi) );
        Vec_IntPush( p->vMapping, Gia_ObjFaninC0(pObjRi) ? 0x55555555 : 0xAAAAAAAA );
        Vec_IntPush( p->vMapping, -1 );  // placeholder for ref counter
    }
    CountMarks = Gia_ManRegNum(p);
    Gia_ManForEachAnd( p, pObj, i )
    {
        if ( !pObj->fPhase )
            continue;
        Vec_IntClear( vLeaves );
        Ga2_ManCollectLeaves_rec( p, pObj, vLeaves, 1 );
//        printf( "%d ", Vec_IntSize(vLeaves) );
        assert( Vec_IntSize(vLeaves) <= N );
        // create map
        Vec_IntWriteEntry( p->vMapping, i, Vec_IntSize(p->vMapping) );
        Vec_IntPush( p->vMapping, Vec_IntSize(vLeaves) );
        Vec_IntForEachEntry( vLeaves, Leaf, k )
        {            
            Vec_IntPush( p->vMapping, Leaf );
            Gia_ManObj(p, Leaf)->Value = uTruth5[k];
            assert( Gia_ManObj(p, Leaf)->fPhase );
        }
        Vec_IntPush( p->vMapping,  (int)Ga2_ObjComputeTruth_rec( p, pObj, 1 ) );
        Vec_IntPush( p->vMapping, -1 );  // placeholder for ref counter
        CountMarks++;
    }
//    printf( "Internal nodes = %d.   ", CountMarks );
    Abc_PrintTime( 1, "Time", clock() - clk );
    Vec_IntFree( vLeaves );
    return CountMarks;
}
void Ga2_ManComputeTest( Gia_Man_t * p )
{
    clock_t clk;
//    unsigned uTruth;
    Gia_Obj_t * pObj;
    int i, Counter = 0;
    clk = clock();
    Ga2_ManMarkup( p, 5 );
    Abc_PrintTime( 1, "Time", clock() - clk );
    Gia_ManForEachAnd( p, pObj, i )
    {
        if ( !pObj->fPhase )
            continue;
//        uTruth = Ga2_ObjTruth( p, pObj );
//        printf( "%6d : ", Counter );
//        Kit_DsdPrintFromTruth( &uTruth, Ga2_ObjLeaveNum(p, pObj) ); 
//        printf( "\n" );
        Counter++;
    }
    printf( "Marked AND nodes = %6d.  ", Counter );
    Abc_PrintTime( 1, "Time", clock() - clk );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ga2_Man_t * Ga2_ManStart( Gia_Man_t * pGia, Gia_ParVta_t * pPars )
{
    Ga2_Man_t * p;
    p = ABC_CALLOC( Ga2_Man_t, 1 );
    p->timeStart = clock();
    // user data
    p->pGia      = pGia;
    p->pPars     = pPars;
    // markings 
    p->nMarked   = Ga2_ManMarkup( pGia, 5 );
    p->vCnfs     = Vec_PtrAlloc( 1000 );
    Vec_PtrPush( p->vCnfs, Vec_IntAlloc(0) );
    Vec_PtrPush( p->vCnfs, Vec_IntAlloc(0) );
    // abstraction
    p->vIds      = Vec_IntStartFull( Gia_ManObjNum(pGia) );
    p->vProofIds = Vec_IntAlloc( 0 );
    p->vAbs      = Vec_IntAlloc( 1000 );
    p->vValues   = Vec_IntAlloc( 1000 );
    // add constant node to abstraction
    Ga2_ObjSetId( p, Gia_ManConst0(pGia), 0 );
    Vec_IntPush( p->vValues, 0 );
    Vec_IntPush( p->vAbs, 0 );
    // refinement
    p->pRnm      = Rnm_ManStart( pGia );
    // SAT solver and variables
    p->vId2Lit   = Vec_PtrAlloc( 1000 );
    // temporaries
    p->vLits     = Vec_IntAlloc( 100 );
    p->vIsopMem  = Vec_IntAlloc( 100 );
    Cnf_ReadMsops( &p->pSopSizes, &p->pSops );
    return p;
}
void Ga2_ManReportMemory( Ga2_Man_t * p )
{
    double memTot = 0;
    double memAig = 1.0 * p->pGia->nObjsAlloc * sizeof(Gia_Obj_t) + Vec_IntMemory(p->pGia->vMapping);
    double memSat = sat_solver2_memory( p->pSat, 1 );
    double memPro = sat_solver2_memory_proof( p->pSat );
    double memMap = Vec_VecMemoryInt( (Vec_Vec_t *)p->vId2Lit );
    double memRef = Rnm_ManMemoryUsage( p->pRnm );
    double memOth = sizeof(Ga2_Man_t);
    memOth += Vec_VecMemoryInt( (Vec_Vec_t *)p->vCnfs );
    memOth += Vec_IntMemory( p->vIds );
    memOth += Vec_IntMemory( p->vProofIds );
    memOth += Vec_IntMemory( p->vAbs );
    memOth += Vec_IntMemory( p->vValues );
    memOth += Vec_IntMemory( p->vLits );
    memOth += Vec_IntMemory( p->vIsopMem );
    memOth += 336450 + (sizeof(char) + sizeof(char*)) * 65536;
    memTot = memAig + memSat + memPro + memMap + memRef + memOth;
    ABC_PRMP( "Memory: AIG      ", memAig, memTot );
    ABC_PRMP( "Memory: SAT      ", memSat, memTot );
    ABC_PRMP( "Memory: Proof    ", memPro, memTot );
    ABC_PRMP( "Memory: Map      ", memMap, memTot );
    ABC_PRMP( "Memory: Refine   ", memRef, memTot );
    ABC_PRMP( "Memory: Other    ", memOth, memTot );
    ABC_PRMP( "Memory: TOTAL    ", memTot, memTot );
}
void Ga2_ManStop( Ga2_Man_t * p )
{
    Vec_IntFreeP( &p->pGia->vMapping );
    Gia_ManSetPhase( p->pGia );
//    if ( p->pPars->fVerbose )
        Abc_Print( 1, "SAT solver:  Var = %d  Cla = %d  Conf = %d  Lrn = %d  Reduce = %d  Cex = %d  ObjsAdded = %d\n", 
            sat_solver2_nvars(p->pSat), sat_solver2_nclauses(p->pSat), 
            sat_solver2_nconflicts(p->pSat), sat_solver2_nlearnts(p->pSat), 
            p->pSat->nDBreduces, p->nCexes, p->nObjAdded );
    if( p->pSat ) sat_solver2_delete( p->pSat );
    Vec_VecFree( (Vec_Vec_t *)p->vCnfs );
    Vec_VecFree( (Vec_Vec_t *)p->vId2Lit );
    Vec_IntFree( p->vIds );
    Vec_IntFree( p->vProofIds );
    Vec_IntFree( p->vAbs );
    Vec_IntFree( p->vValues );
    Vec_IntFree( p->vLits );
    Vec_IntFree( p->vIsopMem );
    Rnm_ManStop( p->pRnm, 1 );
    ABC_FREE( p->pSopSizes );
    ABC_FREE( p->pSops[1] );
    ABC_FREE( p->pSops );
    ABC_FREE( p );
}


/**Function*************************************************************

  Synopsis    [Computes a minimized truth table.]

  Description [Input literals can be 0/1 (const 0/1), non-trivial literals 
  (integers that are more than 1) and unassigned literals (large integers).
  This procedure computes the truth table that essentially depends on input
  variables ordered in the increasing order of their positive literals.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned Ga2_ObjTruthDepends( unsigned t, int v )
{
    static unsigned uInvTruth5[5] = { 0x55555555, 0x33333333, 0x0F0F0F0F, 0x00FF00FF, 0x0000FFFF };
    assert( v >= 0 && v <= 4 );
    return ((t ^ (t >> (1 << v))) & uInvTruth5[v]);
}
unsigned Ga2_ObjComputeTruthSpecial( Gia_Man_t * p, Gia_Obj_t * pRoot, Vec_Int_t * vLeaves, Vec_Int_t * vLits )
{
    static unsigned uTruth5[5] = { 0xAAAAAAAA, 0xCCCCCCCC, 0xF0F0F0F0, 0xFF00FF00, 0xFFFF0000 };
    Gia_Obj_t * pObj;
    int i, Entry;
    unsigned Res;
    // assign elementary truth tables
    Gia_ManForEachObjVec( vLeaves, p, pObj, i )
    {
        Entry = Vec_IntEntry( vLits, i );
        assert( Entry >= 0 );
        if ( Entry == 0 )
            pObj->Value = 0;
        else if ( Entry == 1 )
            pObj->Value = ~0;
        else // non-trivial literal
            pObj->Value = uTruth5[i];
    }
    // compute truth table
    Res = Ga2_ObjComputeTruth_rec( p, pRoot, 1 );
    if ( Res != 0 && Res != ~0 )
    {
        // find essential variables
        int nUsed = 0, pUsed[5];
        for ( i = 0; i < Vec_IntSize(vLeaves); i++ )
            if ( Ga2_ObjTruthDepends( Res, i ) )
                pUsed[nUsed++] = i;
        assert( nUsed > 0 );
        // order the by literal value
        Vec_IntSelectSortCost( pUsed, nUsed, vLits );
        assert( Vec_IntEntry(vLits, pUsed[0]) <= Vec_IntEntry(vLits, pUsed[nUsed-1]) );
        // assign elementary truth tables to the leaves
        Gia_ManForEachObjVec( vLeaves, p, pObj, i )
            pObj->Value = 0;
        for ( i = 0; i < nUsed; i++ )
        {
            Entry = Vec_IntEntry( vLits, pUsed[i] );
            assert( Entry > 1 );
            pObj = Gia_ManObj( p, Vec_IntEntry(vLeaves, pUsed[i]) );
            pObj->Value = Abc_LitIsCompl(Entry) ? ~uTruth5[i] : uTruth5[i];
            // remember this literal
            pUsed[i] = Abc_LitRegular(Entry);
        }
        // compute truth table
        Res = Ga2_ObjComputeTruth_rec( p, pRoot, 1 );
        // reload the literals
        Vec_IntClear( vLits );
        for ( i = 0; i < nUsed; i++ )
        {
            Vec_IntPush( vLits, pUsed[i] );
            assert( Ga2_ObjTruthDepends(Res, i) );
        }
    }
    else
        Vec_IntClear( vLits );
    return Res;
}

/**Function*************************************************************

  Synopsis    [Returns CNF of the function.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Ga2_ManCnfCompute( unsigned uTruth, int nVars, Vec_Int_t * vCover )
{
    extern int Kit_TruthIsop( unsigned * puTruth, int nVars, Vec_Int_t * vMemory, int fTryBoth );
    int RetValue;
    assert( nVars <= 5 );
    // transform truth table into the SOP
    RetValue = Kit_TruthIsop( &uTruth, nVars, vCover, 0 );
    assert( RetValue == 0 );
    // check the case of constant cover
    return Vec_IntDup( vCover );
}

/**Function*************************************************************

  Synopsis    [Derives CNF for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Ga2_ManCnfAddDynamic( Ga2_Man_t * p, int uTruth, int Lits[], int iLitOut, int ProofId )
{
    int i, k, b, Cube, nClaLits, ClaLits[6];
    assert( uTruth > 0 && uTruth < 0xffff );
    // write positive/negative polarity
    for ( i = 0; i < 2; i++ )
    {
        if ( i )
            uTruth = 0xffff & ~uTruth;
//        Extra_PrintBinary( stdout, &uTruth, 16 ); printf( "\n" );
        for ( k = 0; k < p->pSopSizes[uTruth]; k++ )
        {
            nClaLits = 0;
            ClaLits[nClaLits++] = i ? lit_neg(iLitOut) : iLitOut;
            Cube = p->pSops[uTruth][k];
            for ( b = 3; b >= 0; b-- )
            {
                if ( Cube % 3 == 0 ) // value 0 --> add positive literal
                {
                    assert( Lits[b] > 1 );
                    ClaLits[nClaLits++] = Lits[b];
                }
                else if ( Cube % 3 == 1 ) // value 1 --> add negative literal
                {
                    assert( Lits[b] > 1 );
                    ClaLits[nClaLits++] = lit_neg(Lits[b]);
                }
                Cube = Cube / 3;
            }
            sat_solver2_addclause( p->pSat, ClaLits, ClaLits+nClaLits, ProofId );
        }
    }
}
static inline void Ga2_ManCnfAddStatic( Ga2_Man_t * p, Vec_Int_t * vCnf0, Vec_Int_t * vCnf1, int Lits[], int iLitOut, int ProofId )
{
    Vec_Int_t * vCnf;
    int i, k, b, Cube, Literal, nClaLits, ClaLits[6];
    // write positive/negative polarity
    for ( i = 0; i < 2; i++ )
    {
        vCnf = i ? vCnf1 : vCnf0;
//        for ( k = 0; k < p->pSopSizes[uTruth]; k++ )
        Vec_IntForEachEntry( vCnf, Cube, k )
        {
            nClaLits = 0;
            ClaLits[nClaLits++] = i ? lit_neg(iLitOut) : iLitOut;
//            Cube = p->pSops[uTruth][k];
//            for ( b = 3; b >= 0; b-- )
            for ( b = 0; b < 5; b++ )
            {
                Literal = 3 & (Cube >> (b << 1));
                if ( Literal == 1 ) // value 0 --> add positive literal
                {
//                    pCube[b] = '0';
                    assert( Lits[b] > 1 );
                    ClaLits[nClaLits++] = Lits[b];
                }
                else if ( Literal == 2 ) // value 1 --> add negative literal
                {
//                    pCube[b] = '1';
                    assert( Lits[b] > 1 );
                    ClaLits[nClaLits++] = lit_neg(Lits[b]);
                }
                else if ( Literal != 0 )
                    assert( 0 );
            }
//            for ( b = 0; b < nClaLits; b++ )
//                printf( "%d ", ClaLits[b] );
//            printf( "\n" );
            sat_solver2_addclause( p->pSat, ClaLits, ClaLits+nClaLits, ProofId );
        }
    }
    b = 0;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ga2_ManSetupNode( Ga2_Man_t * p, Gia_Obj_t * pObj, int fAbs )
{
    unsigned uTruth;
    int nLeaves;
    int Id = Gia_ObjId(p->pGia, pObj);
    assert( pObj->fPhase );
    assert( Vec_PtrSize(p->vCnfs) == 2 * Vec_IntSize(p->vValues) );
    if ( Gia_ObjId(p->pGia,pObj) == 4950 )
    {
        int s = 0;
    }
    // assign abstraction ID to the node
    if ( Ga2_ObjId(p,pObj) == -1 )
    {
        Ga2_ObjSetId( p, pObj, Vec_IntSize(p->vValues) );
        Vec_IntPush( p->vValues, Gia_ObjId(p->pGia, pObj) );
        Vec_PtrPush( p->vCnfs, NULL );
        Vec_PtrPush( p->vCnfs, NULL );
    }
    assert( Ga2_ObjCnf0(p, pObj) == NULL );
    if ( !fAbs )
        return;
//    assert( Vec_IntFind(p->vAbs, Gia_ObjId(p->pGia, pObj)) == -1 );
    Vec_IntPush( p->vAbs, Gia_ObjId(p->pGia, pObj) );
    assert( Gia_ObjIsAnd(pObj) || Gia_ObjIsRo(p->pGia, pObj) );
    // compute parameters
    nLeaves = Ga2_ObjLeaveNum(p->pGia, pObj);
    uTruth = Ga2_ObjTruth( p->pGia, pObj );
    // create CNF for pos/neg phases
    Vec_PtrWriteEntry( p->vCnfs, 2 * Ga2_ObjId(p,pObj),     Ga2_ManCnfCompute( uTruth, nLeaves, p->vIsopMem) );    
    Vec_PtrWriteEntry( p->vCnfs, 2 * Ga2_ObjId(p,pObj) + 1, Ga2_ManCnfCompute(~uTruth, nLeaves, p->vIsopMem) );
}

void Ga2_ManAddToAbsOneStatic( Ga2_Man_t * p, Gia_Obj_t * pObj, int f )
{
    Vec_Int_t * vLeaves;
    Gia_Obj_t * pFanin;
    int k, iLitOut = Ga2_ObjFindOrAddLit( p, pObj, f );
    assert( !Gia_ObjIsConst0(pObj) );
    assert( iLitOut > 1 );
    assert( Gia_ObjIsAnd(pObj) || Gia_ObjIsRo(p->pGia, pObj) );
    if ( f == 0 && Gia_ObjIsRo(p->pGia, pObj) )
    {
        iLitOut = Abc_LitNot( iLitOut );
        sat_solver2_addclause( p->pSat, &iLitOut, &iLitOut + 1, Gia_ObjId(p->pGia, pObj) );
    }
    else
    {
        vLeaves = Ga2_ObjLeaves( p->pGia, pObj );
        Vec_IntClear( p->vLits );
        Gia_ManForEachObjVec( vLeaves, p->pGia, pFanin, k )
            Vec_IntPush( p->vLits, Ga2_ObjFindOrAddLit( p, pFanin, f - Gia_ObjIsRo(p->pGia, pObj) ) );
        Ga2_ManCnfAddStatic( p, Ga2_ObjCnf0(p, pObj), Ga2_ObjCnf1(p, pObj), Vec_IntArray(p->vLits), iLitOut, Gia_ObjId(p->pGia, pObj) );
    }
}

void Ga2_ManAddAbsClauses( Ga2_Man_t * p, int f )
{
    int fSimple = 1;
    Gia_Obj_t * pObj;
    int i, Lit;
/*
    Vec_Int_t * vMap = (f < Vec_PtrSize(p->vId2Lit) ? Ga2_MapFrameMap( p, f ) : NULL);
//    Ga2_ObjAddLit( p, Gia_ManConst0(p->pGia), f, 0 );
    if ( f == 5 )
    {
        int s = 0;
    }
*/
    if ( fSimple )
    {
        Lit = Ga2_ObjFindOrAddLit( p, Gia_ManConst0(p->pGia), f );
        Lit = Abc_LitNot( Lit );
        sat_solver2_addclause( p->pSat, &Lit, &Lit + 1, 0 );
    }
    Gia_ManForEachObjVec( p->vAbs, p->pGia, pObj, i )
        if ( i >= p->LimAbs )
            Ga2_ManAddToAbsOneStatic( p, pObj, f );
}

void Ga2_ManAddToAbs( Ga2_Man_t * p, Vec_Int_t * vToAdd )
{
    Vec_Int_t * vLeaves;
    Gia_Obj_t * pObj, * pFanin;
    int f, i, k;
    // add abstraction objects
    Gia_ManForEachObjVec( vToAdd, p->pGia, pObj, i )
    {
        Ga2_ManSetupNode( p, pObj, 1 );
        if ( p->pSat->pPrf2 )
            Vec_IntWriteEntry( p->vProofIds, Gia_ObjId(p->pGia, pObj), p->nProofIds++ );
    }
    // add PPI objects
    Gia_ManForEachObjVec( vToAdd, p->pGia, pObj, i )
    {
        vLeaves = Ga2_ObjLeaves( p->pGia, pObj );
        Gia_ManForEachObjVec( vLeaves, p->pGia, pFanin, k )
            if ( Ga2_ObjId( p, pFanin ) == -1 )
                Ga2_ManSetupNode( p, pFanin, 0 );
    }
    // add new clauses to the timeframes
    for ( f = 0; f <= p->pPars->iFrame; f++ )
    {
        Vec_IntFillExtra( Ga2_MapFrameMap(p, f), Vec_IntSize(p->vValues), -1 );
        Gia_ManForEachObjVec( vToAdd, p->pGia, pObj, i )
            Ga2_ManAddToAbsOneStatic( p, pObj, f );
    }
}

void Ga2_ManShrinkAbs( Ga2_Man_t * p, int nAbs, int nValues, int nSatVars )
{
    Vec_Int_t * vMap;
    Gia_Obj_t * pObj;
    int i;
    assert( nAbs > 0 );
    assert( nValues > 0 );
    assert( nSatVars > 0 );
    // shrink abstraction
    Gia_ManForEachObjVec( p->vAbs, p->pGia, pObj, i )
    {
        if ( !i ) continue;
        assert( Ga2_ObjCnf0(p, pObj) != NULL );
        assert( Ga2_ObjCnf1(p, pObj) != NULL );
        if ( i < nAbs )
            continue;
        Vec_IntFree( Ga2_ObjCnf0(p, pObj) );
        Vec_IntFree( Ga2_ObjCnf1(p, pObj) );
        Vec_PtrWriteEntry( p->vCnfs, 2 * Ga2_ObjId(p,pObj),     NULL );    
        Vec_PtrWriteEntry( p->vCnfs, 2 * Ga2_ObjId(p,pObj) + 1, NULL );
    }
    Vec_IntShrink( p->vAbs, nAbs );
    // shrink values
    Gia_ManForEachObjVec( p->vValues, p->pGia, pObj, i )
    {
        assert( Ga2_ObjId(p,pObj) >= 0 );
        if ( i < nValues )
            continue;
        Ga2_ObjSetId( p, pObj, -1 );
    }
    Vec_IntShrink( p->vValues, nValues );
    Vec_PtrShrink( p->vCnfs, 2 * nValues );
    // clean mapping for each timeframe
    Vec_PtrForEachEntry( Vec_Int_t *, p->vId2Lit, vMap, i )
        Vec_IntClear( vMap );
    // shrink SAT variables
    p->nSatVars = nSatVars;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ga2_ManAbsTranslate_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vClasses, int fFirst )
{
    if ( pObj->fPhase && !fFirst )
        return;
    assert( Gia_ObjIsAnd(pObj) );
    Ga2_ManAbsTranslate_rec( p, Gia_ObjFanin0(pObj), vClasses, 0 );
    Ga2_ManAbsTranslate_rec( p, Gia_ObjFanin1(pObj), vClasses, 0 );
    Vec_IntWriteEntry( vClasses, Gia_ObjId(p, pObj), 1 );
}

Vec_Int_t * Ga2_ManAbsTranslate( Ga2_Man_t * p )
{
    Vec_Int_t * vGateClasses;
    Gia_Obj_t * pObj;
    int i;
    vGateClasses = Vec_IntStart( Gia_ManObjNum(p->pGia) );
    Vec_IntWriteEntry( vGateClasses, 0, 1 );
    Gia_ManForEachObjVec( p->vAbs, p->pGia, pObj, i )
    {
        if ( Gia_ObjIsAnd(pObj) )
            Ga2_ManAbsTranslate_rec( p->pGia, pObj, vGateClasses, 1 );
        else if ( Gia_ObjIsRo(p->pGia, pObj) )
        {
            Vec_IntWriteEntry( vGateClasses, Gia_ObjId(p->pGia, pObj), 1 );
            pObj = Gia_ObjRoToRi( p->pGia, pObj );
            Vec_IntWriteEntry( vGateClasses, Gia_ObjFaninId0p(p->pGia, pObj), 1 );
        }
        else if ( !Gia_ObjIsConst0(pObj) )
            assert( 0 );
    }
    return vGateClasses;
}

Vec_Int_t * Ga2_ManAbsDerive( Gia_Man_t * p )
{
    Vec_Int_t * vToAdd;
    Gia_Obj_t * pObj;
    int i;
    vToAdd = Vec_IntAlloc( 1000 );
//    Vec_IntPush( vToAdd, 0 ); // const 0
    Gia_ManForEachRo( p, pObj, i )
        if ( pObj->fPhase && Vec_IntEntry(p->vGateClasses, Gia_ObjId(p, pObj)) )
            Vec_IntPush( vToAdd, Gia_ObjId(p, pObj) );
    Gia_ManForEachAnd( p, pObj, i )
        if ( pObj->fPhase && Vec_IntEntry(p->vGateClasses, i) )
            Vec_IntPush( vToAdd, i );
    return vToAdd;
}

void Ga2_ManRestart( Ga2_Man_t * p )
{
    Vec_Int_t * vToAdd;
    int Lit = 1;
    assert( p->pGia != NULL && p->pGia->vGateClasses != NULL );
    assert( Gia_ManPi(p->pGia, 0)->fPhase ); // marks are set
    // clear SAT variable numbers (begin with 1)
    if ( p->pSat ) sat_solver2_delete( p->pSat );
    p->pSat      = sat_solver2_new();
    // add clause x0 = 0  (lit0 = 1; lit1 = 0)
    sat_solver2_addclause( p->pSat, &Lit, &Lit + 1, 0 );
    // remove previous abstraction
    Ga2_ManShrinkAbs( p, 1, 1, 1 );
    // start new abstraction
    vToAdd = Ga2_ManAbsDerive( p->pGia );
    assert( p->pSat->pPrf2 == NULL );
    assert( p->pPars->iFrame < 0 );
    Ga2_ManAddToAbs( p, vToAdd );
    Vec_IntFree( vToAdd );
    p->LimAbs = Vec_IntSize(p->vAbs);
    p->LimPpi = Vec_IntSize(p->vValues);
    // set runtime limit
    if ( p->pPars->nTimeOut )
        sat_solver2_set_runtime_limit( p->pSat, p->pPars->nTimeOut * CLOCKS_PER_SEC + p->timeStart );
}

/**Function*************************************************************

  Synopsis    [Unrolls one timeframe.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ga2_ManUnroll_rec( Ga2_Man_t * p, Gia_Obj_t * pObj, int f )
{
    int fSimple = 1;
    int Id = Gia_ObjId(p->pGia, pObj);
    unsigned uTruth;
    Gia_Obj_t * pLeaf;
    int nLeaves, * pLeaves;
    int i, Lit, pLits[5];
    if ( Gia_ObjIsConst0(pObj) || (f==0 && Gia_ObjIsRo(p->pGia, pObj)) )
    {
        if ( fSimple )
        {
            Lit = Ga2_ObjFindOrAddLit( p, pObj, f );
            Lit = Abc_LitNot(Lit);
            assert( Lit > 1 );
            sat_solver2_addclause( p->pSat, &Lit, &Lit + 1, Gia_ObjId(p->pGia, pObj) );
            return Lit;
        }
        return 0;
    }
    if ( Gia_ObjIsCo(pObj) )
        return Abc_LitNotCond( Ga2_ManUnroll_rec(p, Gia_ObjFanin0(pObj), f), Gia_ObjFaninC0(pObj) );
    assert( pObj->fPhase );
    if ( Ga2_ObjIsLeaf0(p, pObj) )
        return Ga2_ObjFindOrAddLit( p, pObj, f );
    assert( !Gia_ObjIsPi(p->pGia, pObj) );
    Lit = Ga2_ObjFindLit( p, pObj, f );
    if ( Lit >= 0 )
        return Lit;
    if ( Gia_ObjIsRo(p->pGia, pObj) )
    {
        assert( f > 0 );
        Lit = Ga2_ManUnroll_rec( p, Gia_ObjRoToRi(p->pGia, pObj), f-1 );
        Ga2_ObjAddLit( p, pObj, f, Lit );
        return Lit;
    }
    assert( Gia_ObjIsAnd(pObj) );
    nLeaves = Ga2_ObjLeaveNum( p->pGia, pObj );
    pLeaves = Ga2_ObjLeavePtr( p->pGia, pObj );
    if ( fSimple )
    {
        // collect fanin literals
        for ( i = 0; i < nLeaves; i++ )
        {
            pLeaf = Gia_ManObj(p->pGia, pLeaves[i]);
            pLits[i] = Ga2_ManUnroll_rec( p, pLeaf, f );
        }
        // create fanout literal
        Lit = Ga2_ObjFindOrAddLit( p, pObj, f );
        // create clauses
        Ga2_ManCnfAddStatic( p, Ga2_ObjCnf0(p, pObj), Ga2_ObjCnf1(p, pObj), pLits, Lit, Gia_ObjId(p->pGia, pObj) );
        return Lit;
    }
    // collect fanin literals
    for ( i = 0; i < nLeaves; i++ )
    {
        pLeaf = Gia_ManObj( p->pGia, pLeaves[i] );
        if ( Ga2_ObjIsAbs0(p, pLeaf) )      // belongs to original abstraction
            pLits[i] = Ga2_ManUnroll_rec( p, pLeaf, f );
        else if ( Ga2_ObjIsLeaf0(p, pLeaf) ) // belongs to original PPIs
            pLits[i] = GA2_BIG_NUM + i;
        else assert( 0 );
    }
    // collect literals
    Vec_IntClear( p->vLits );
    for ( i = 0; i < nLeaves; i++ )
        Vec_IntPush( p->vLits, pLits[i] );
    // minimize truth table
    uTruth = Ga2_ObjComputeTruthSpecial( p->pGia, pObj, Ga2_ObjLeaves(p->pGia, pObj), p->vLits );
    if ( uTruth == 0 || uTruth == ~0 ) // const 0 / 1
        Lit = (uTruth > 0);
    else if ( uTruth == 0xAAAAAAAA || uTruth == 0x55555555 )  // buffer / inverter
    {
        Lit = Vec_IntEntry( p->vLits, 0 );
        if ( Lit >= GA2_BIG_NUM )
        {
            pLeaf = Gia_ManObj( p->pGia, pLeaves[Lit-GA2_BIG_NUM] );
            Lit = Ga2_ObjFindOrAddLit( p, pLeaf, f );
        }
        Lit = Abc_LitNotCond( Lit, uTruth == 0x55555555 );
    }
    else
    {
        // perform structural hashing here!!!

        // add new node
        Lit = Ga2_ObjFindOrAddLit(p, pObj, f);
        Ga2_ManCnfAddDynamic( p, uTruth, Vec_IntArray(p->vLits), Lit, Gia_ObjId(p->pGia, pObj) );
    }
    Ga2_ObjAddLit( p, pObj, f, Lit );
    return Lit;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Vec_IntCheckUnique( Vec_Int_t * p )
{
    int RetValue;
    Vec_Int_t * pDup = Vec_IntDup( p );
    Vec_IntUniqify( pDup );
    RetValue = Vec_IntSize(p) - Vec_IntSize(pDup);
    Vec_IntFree( pDup );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Ga2_ObjSatValue( Ga2_Man_t * p, Gia_Obj_t * pObj, int f )
{
    int Lit = Ga2_ObjFindLit( p, pObj, f );
    if ( Lit == -1 )
        return 0;
    return Abc_LitIsCompl(Lit) ^ sat_solver2_var_value( p->pSat, Abc_Lit2Var(Lit) );
}
void Ga2_GlaPrepareCexAndMap( Ga2_Man_t * p, Abc_Cex_t ** ppCex, Vec_Int_t ** pvMaps )
{
    Abc_Cex_t * pCex;
    Vec_Int_t * vMap;
    Gia_Obj_t * pObj;
    int f, i, k, Id;
    // find PIs and PPIs
    vMap = Vec_IntAlloc( 1000 );
    Gia_ManForEachObjVec( p->vValues, p->pGia, pObj, i )
    {
        if ( !i ) continue;
        Id = Ga2_ObjId(p, pObj);
        k = Gia_ObjId(p->pGia, pObj);
        if ( Ga2_ObjIsAbs(p, pObj) )
            continue;
        assert( pObj->fPhase );
        assert( Ga2_ObjIsLeaf(p, pObj) );
        assert( Gia_ObjIsAnd(pObj) || Gia_ObjIsCi(pObj) );
        Vec_IntPush( vMap, Gia_ObjId(p->pGia, pObj) );
    }
    // derive counter-example
    pCex = Abc_CexAlloc( 0, Vec_IntSize(vMap), p->pPars->iFrame+1 );
    pCex->iFrame = p->pPars->iFrame;
    for ( f = 0; f <= p->pPars->iFrame; f++ )
        Gia_ManForEachObjVec( vMap, p->pGia, pObj, k )
            if ( Ga2_ObjSatValue( p, pObj, f ) )
                Abc_InfoSetBit( pCex->pData, f * Vec_IntSize(vMap) + k );
    *pvMaps = vMap;
    *ppCex = pCex;
}
Abc_Cex_t * Ga2_ManDeriveCex( Ga2_Man_t * p, Vec_Int_t * vPis )
{
    Abc_Cex_t * pCex;
    Gia_Obj_t * pObj;
    int i, f;
    pCex = Abc_CexAlloc( Gia_ManRegNum(p->pGia), Gia_ManPiNum(p->pGia), p->pPars->iFrame+1 );
    pCex->iPo = 0;
    pCex->iFrame = p->pPars->iFrame;
    Gia_ManForEachObjVec( vPis, p->pGia, pObj, i )
    {
        if ( !Gia_ObjIsPi(p->pGia, pObj) )
            continue;
        assert( Gia_ObjIsPi(p->pGia, pObj) );
        for ( f = 0; f <= pCex->iFrame; f++ )
            if ( Ga2_ObjSatValue( p, pObj, f ) )
                Abc_InfoSetBit( pCex->pData, pCex->nRegs + f * pCex->nPis + Gia_ObjCioId(pObj) );
    }
    return pCex;
}
Vec_Int_t * Ga2_ManRefine( Ga2_Man_t * p )
{
    Abc_Cex_t * pCex;
    Vec_Int_t * vMap, * vVec;
    Gia_Obj_t * pObj;
    int i;
    Ga2_GlaPrepareCexAndMap( p, &pCex, &vMap );
    vVec = Rnm_ManRefine( p->pRnm, pCex, vMap, p->pPars->fPropFanout, 1 );
    Abc_CexFree( pCex );
    if ( Vec_IntSize(vVec) == 0 )
    {
        Vec_IntFree( vVec );
        Abc_CexFreeP( &p->pGia->pCexSeq );
        p->pGia->pCexSeq = Ga2_ManDeriveCex( p, vMap );
        Vec_IntFree( vMap );
        return NULL;
    }
    Vec_IntFree( vMap );
    // these objects should be PPIs that are not abstracted yet
    Gia_ManForEachObjVec( vVec, p->pGia, pObj, i )
        assert( pObj->fPhase && Ga2_ObjIsLeaf(p, pObj) );
    p->nObjAdded += Vec_IntSize(vVec);
    return vVec;
}

/**Function*************************************************************

  Synopsis    [Creates a new manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ga2_GlaAbsCount( Ga2_Man_t * p, int fRo, int fAnd )
{
    Gia_Obj_t * pObj;
    int i, Counter = 0;
    if ( fRo )
        Gia_ManForEachObjVec( p->vAbs, p->pGia, pObj, i )
            Counter += Gia_ObjIsRo(p->pGia, pObj);
    else if ( fAnd )
        Gia_ManForEachObjVec( p->vAbs, p->pGia, pObj, i )
            Counter += Gia_ObjIsAnd(pObj);
    else assert( 0 );
    return Counter;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ga2_ManAbsPrintFrame( Ga2_Man_t * p, int nFrames, int nConfls, int nCexes, clock_t Time, int fFinal )
{
    if ( Abc_FrameIsBatchMode() && !fFinal )
        return;
    Abc_Print( 1, "%4d :", nFrames );
    Abc_Print( 1, "%4d", Abc_MinInt(100, 100 * Vec_IntSize(p->vAbs) / p->nMarked) ); 
    Abc_Print( 1, "%6d", Vec_IntSize(p->vAbs) );
    Abc_Print( 1, "%5d", Vec_IntSize(p->vValues)-Vec_IntSize(p->vAbs)-1 );
    Abc_Print( 1, "%5d", Ga2_GlaAbsCount(p, 1, 0) );
    Abc_Print( 1, "%6d", Ga2_GlaAbsCount(p, 0, 1) );
    Abc_Print( 1, "%8d", nConfls );
    if ( nCexes == 0 )
        Abc_Print( 1, "%5c", '-' ); 
    else
        Abc_Print( 1, "%5d", nCexes ); 
    Abc_PrintInt( sat_solver2_nvars(p->pSat) );
    Abc_PrintInt( sat_solver2_nclauses(p->pSat) );
    Abc_PrintInt( sat_solver2_nlearnts(p->pSat) );
    Abc_Print( 1, "%9.2f sec", 1.0*Time/CLOCKS_PER_SEC );
    Abc_Print( 1, "%5.1f GB", (sat_solver2_memory_proof(p->pSat) + sat_solver2_memory(p->pSat, 0)) / (1<<30) );
    Abc_Print( 1, "%s", fFinal ? "\n" : "\n" );
    fflush( stdout );
}

/**Function*************************************************************

  Synopsis    [Performs gate-level abstraction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ga2_ManPerform( Gia_Man_t * pAig, Gia_ParVta_t * pPars )
{
    Ga2_Man_t * p;
    Vec_Int_t * vCore, * vPPis;
    clock_t clk2, clk = clock();
    int Status, RetValue = -1;
    int i, c, f, Lit;
    // check trivial case 
    assert( Gia_ManPoNum(pAig) == 1 ); 
    ABC_FREE( pAig->pCexSeq );
    if ( Gia_ObjIsConst0(Gia_ObjFanin0(Gia_ManPo(pAig,0))) )
    {
        if ( !Gia_ObjFaninC0(Gia_ManPo(pAig,0)) )
        {
            printf( "Sequential miter is trivially UNSAT.\n" );
            return 1;
        }
        pAig->pCexSeq = Abc_CexMakeTriv( Gia_ManRegNum(pAig), Gia_ManPiNum(pAig), 1, 0 );
        printf( "Sequential miter is trivially SAT.\n" );
        return 0;
    }
    // create gate classes if not given
    if ( pAig->vGateClasses == NULL )
    {
        pAig->vGateClasses = Vec_IntStart( Gia_ManObjNum(pAig) );
        Vec_IntWriteEntry( pAig->vGateClasses, 0, 1 );
        Vec_IntWriteEntry( pAig->vGateClasses, Gia_ObjFaninId0p(pAig, Gia_ManPo(pAig, 0)), 1 );
    }
    // start the manager
    p = Ga2_ManStart( pAig, pPars );
    p->timeInit = clock() - clk;
    // perform initial abstraction
    if ( p->pPars->fVerbose )
    {
        Abc_Print( 1, "Running gate-level abstraction (GLA) with the following parameters:\n" );
        Abc_Print( 1, "FrameMax = %d  ConfMax = %d  Timeout = %d  RatioMin = %d %%.\n", 
            pPars->nFramesMax, pPars->nConfLimit, pPars->nTimeOut, pPars->nRatioMin );
        Abc_Print( 1, "LearnStart = %d  LearnDelta = %d  LearnRatio = %d %%.\n", 
            pPars->nLearnedStart, pPars->nLearnedDelta, pPars->nLearnedPerce );
        Abc_Print( 1, " Frame   %%   Abs  PPI   FF   LUT   Confl  Cex   Vars   Clas   Lrns     Time      Mem\n" );
    }
    // iterate unrolling
    for ( i = f = 0; !pPars->nFramesMax || f < pPars->nFramesMax; i++ )
    {
        // remember the timeframe
        p->pPars->iFrame = -1;
        // create new SAT solver
        Ga2_ManRestart( p );
        // unroll the circuit
        for ( f = 0; !pPars->nFramesMax || f < pPars->nFramesMax; f++ )
        {
            // remember current limits
            int nConflsBeg = sat_solver2_nconflicts(p->pSat);
            int nAbs       = Vec_IntSize(p->vAbs);
            int nValues    = Vec_IntSize(p->vValues);
            int nVarsOld;
            // extend and clear storage
            if ( f == Vec_PtrSize(p->vId2Lit) )
                Vec_PtrPush( p->vId2Lit, Vec_IntAlloc(0) );
            Vec_IntFillExtra( Ga2_MapFrameMap(p, f), Vec_IntSize(p->vValues), -1 );
            // remember the timeframe
            p->pPars->iFrame = f;
            // add static clauses to this timeframe
            Ga2_ManAddAbsClauses( p, f );
            // get the output literal
            Lit = Ga2_ManUnroll_rec( p, Gia_ManPo(pAig,0), f );
            // check for counter-examples
            nVarsOld = p->nSatVars;
            for ( c = 0; ; c++ )
            {
                // perform SAT solving
                clk2 = clock();
                Status = sat_solver2_solve( p->pSat, &Lit, &Lit+1, (ABC_INT64_T)pPars->nConfLimit, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
                if ( Status == l_True ) // perform refinement
                {
                    p->timeSat += clock() - clk2;

                    clk2 = clock();
                    vPPis = Ga2_ManRefine( p );
                    p->timeCex += clock() - clk2;
                    if ( vPPis == NULL )
                    {
                        if ( pPars->fVerbose )
                            Ga2_ManAbsPrintFrame( p, f, sat_solver2_nconflicts(p->pSat)-nConflsBeg, c, clock() - clk, 1 );
                        goto finish;
                    }

                    if ( c == 0 )
                    {
                        // create bookmark to be used for rollback
                        assert( nVarsOld == p->pSat->size );
                        sat_solver2_bookmark( p->pSat );
                        // start incremental proof manager
                        assert( p->pSat->pPrf2 == NULL );
                        p->pSat->pPrf2 = Prf_ManAlloc();
                        if ( p->pSat->pPrf2 )
                        {
                            p->nProofIds = 0;
                            Vec_IntFill( p->vProofIds, Gia_ManObjNum(p->pGia), -1 );
                            Prf_ManRestart( p->pSat->pPrf2, p->vProofIds, sat_solver2_nlearnts(p->pSat), Vec_IntSize(vPPis) );
                        }
                    }
                    else
                    {
                        // resize the proof logger
                        if ( p->pSat->pPrf2 )
                            Prf_ManGrow( p->pSat->pPrf2, p->nProofIds + Vec_IntSize(vPPis) );
                    }

                    Ga2_ManAddToAbs( p, vPPis );
                    Vec_IntFree( vPPis );
                    if ( pPars->fVerbose )
                        Ga2_ManAbsPrintFrame( p, f, sat_solver2_nconflicts(p->pSat)-nConflsBeg, c+1, clock() - clk, 0 );
                    // verify
                    if ( Vec_IntCheckUnique(p->vAbs) )
                        printf( "Vector has %d duplicated entries.\n", Vec_IntCheckUnique(p->vAbs) );
                    continue;
                }
                p->timeUnsat += clock() - clk2;
                if ( Status == l_Undef ) // ran out of resources
                    goto finish;
                if ( p->pSat->nRuntimeLimit && clock() > p->pSat->nRuntimeLimit ) // timeout
                    goto finish;
                assert( RetValue == l_False );
                if ( c == 0 )
                    break;

                // derive the core
                assert( p->pSat->pPrf2 != NULL );
                vCore = (Vec_Int_t *)Sat_ProofCore( p->pSat );
                Prf_ManStopP( &p->pSat->pPrf2 );
                // update the SAT solver
                sat_solver2_rollback( p->pSat );
                // reduce abstraction
                Ga2_ManShrinkAbs( p, nAbs, nValues, nVarsOld );
                Ga2_ManAddToAbs( p, vCore );
                Vec_IntFree( vCore );
                // verify
                if ( Vec_IntCheckUnique(p->vAbs) )
                    printf( "Vector has %d duplicated entries.\n", Vec_IntCheckUnique(p->vAbs) );
                break;
            }
            if ( pPars->fVerbose )
                Ga2_ManAbsPrintFrame( p, f, sat_solver2_nconflicts(p->pSat)-nConflsBeg, c, clock() - clk, 1 );
            if ( c > 0 )
            {
                Vec_IntFreeP( &pAig->vGateClasses );
                pAig->vGateClasses = Ga2_ManAbsTranslate( p );
                printf( "\n" );
                break;  // temporary
            }
        }
        // check if the number of objects is below limit
        if ( Vec_IntSize(p->vAbs) >= p->nMarked * (100 - pPars->nRatioMin) / 100 )
        {
            Status = l_Undef;
            break;
        }
    }
finish:
    Prf_ManStopP( &p->pSat->pPrf2 );
    // analize the results
    if ( pAig->pCexSeq == NULL )
    {
        if ( pAig->vGateClasses != NULL )
            Abc_Print( 1, "Replacing the old abstraction by a new one.\n" );
        Vec_IntFreeP( &pAig->vGateClasses );
        pAig->vGateClasses = Ga2_ManAbsTranslate( p );
        if ( Status == l_Undef )
        {
            if ( p->pPars->nTimeOut && clock() >= p->pSat->nRuntimeLimit ) 
                Abc_Print( 1, "SAT solver ran out of time at %d sec in frame %d.  ", p->pPars->nTimeOut, f );
            else if ( pPars->nConfLimit && sat_solver2_nconflicts(p->pSat) >= pPars->nConfLimit )
                Abc_Print( 1, "SAT solver ran out of resources at %d conflicts in frame %d.  ", pPars->nConfLimit, f );
            else if ( Vec_IntSize(p->vAbs) >= p->nMarked * (100 - pPars->nRatioMin) / 100 )
                Abc_Print( 1, "The ratio of abstracted objects is less than %d %% in frame %d.  ", pPars->nRatioMin, f );
            else
                Abc_Print( 1, "Abstraction stopped for unknown reason in frame %d.  ", f );
        }
        else
        {
            p->pPars->iFrame++;
            Abc_Print( 1, "SAT solver completed %d frames and produced an abstraction.  ", f );
        }
    }
    else
    {
        if ( !Gia_ManVerifyCex( pAig, pAig->pCexSeq, 0 ) )
            Abc_Print( 1, "    Gia_GlaPerform(): CEX verification has failed!\n" );
        Abc_Print( 1, "Counter-example detected in frame %d.  ", f );
        p->pPars->iFrame = pAig->pCexSeq->iFrame - 1;
        Vec_IntFreeP( &pAig->vGateClasses );
        RetValue = 0;
    }
    Abc_PrintTime( 1, "Time", clock() - clk );
    if ( p->pPars->fVerbose )
    {
        p->timeOther = (clock() - clk) - p->timeUnsat - p->timeSat - p->timeCex - p->timeInit;
        ABC_PRTP( "Runtime: Initializing", p->timeInit,   clock() - clk );
        ABC_PRTP( "Runtime: Solver UNSAT", p->timeUnsat,  clock() - clk );
        ABC_PRTP( "Runtime: Solver SAT  ", p->timeSat,    clock() - clk );
        ABC_PRTP( "Runtime: Refinement  ", p->timeCex,    clock() - clk );
        ABC_PRTP( "Runtime: Other       ", p->timeOther,  clock() - clk );
        ABC_PRTP( "Runtime: TOTAL       ", clock() - clk, clock() - clk );
        Ga2_ManReportMemory( p );
    }
    Ga2_ManStop( p );
    fflush( stdout );
    return RetValue;
}

//#endif


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

