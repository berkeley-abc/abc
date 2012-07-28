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
    Gia_Man_t *    pGia;            // working AIG manager
    Gia_ParVta_t * pPars;           // parameters
    // markings 
    int            nMarked;         // total number of marked nodes and flops
    Vec_Int_t *    vMapping;        // for each object: leaf count, leaves, truth table
    Vec_Ptr_t *    vDatas;          // for each object: leaves, CNF0, CNF1
    // abstraction
    Vec_Int_t *    vAbs;            // array of abstracted objects
    Vec_Int_t *    vValues;         // array of objects with SAT numbers assigned
    int            LimAbs;          // limit value for starting abstraction objects
    int            LimPpi;          // limit value for starting PPI objects
    // refinement
    Rnm_Man_t *    pRnm;            // refinement manager
    // SAT solver and variables
    Vec_Ptr_t *    vId2Lit;         // mapping, for each timeframe, of object ID into SAT literal
    sat_solver2 *  pSat;            // incremental SAT solver
    int            nSatVars;        // the number of SAT variables
    // temporaries
    Vec_Int_t *    vCnf;
    Vec_Int_t *    vLits;
    Vec_Int_t *    vIsopMem;
    char * pSopSizes, ** pSops;     // CNF representation
    int            nCexes;          // the number of counter-examples
    int            nObjAdded;       // objs added during refinement
    // statistics  
    clock_t        timeStart;
    clock_t        timeInit;
    clock_t        timeSat;
    clock_t        timeUnsat;
    clock_t        timeCex;
    clock_t        timeOther;
};

static inline int         Ga2_ObjOffset( Ga2_Man_t * p, Gia_Obj_t * pObj )   { assert(pObj->Value); return Vec_IntEntry(p->vMapping, Gia_ObjId(p->pGia, pObj));                                      }
static inline int         Ga2_ObjLeaveNum( Ga2_Man_t * p, Gia_Obj_t * pObj ) { return Vec_IntEntry(p->vMapping, Ga2_ObjOffset(p, pObj));                                                             }
static inline int *       Ga2_ObjLeavePtr( Ga2_Man_t * p, Gia_Obj_t * pObj ) { return Vec_IntEntryP(p->vMapping, Ga2_ObjOffset(p, pObj) + 1);                                                        }
static inline unsigned    Ga2_ObjTruth( Ga2_Man_t * p, Gia_Obj_t * pObj )    { return (unsigned)Vec_IntEntry(p->vMapping, Ga2_ObjOffset(p, pObj) + Ga2_ObjLeaveNum(p, pObj) + 1);                    }
static inline int         Ga2_ObjRefNum( Ga2_Man_t * p, Gia_Obj_t * pObj )   { return (unsigned)Vec_IntEntry(p->vMapping, Ga2_ObjOffset(p, pObj) + Ga2_ObjLeaveNum(p, pObj) + 2);                    }
static inline Vec_Int_t * Ga2_ObjLeaves( Ga2_Man_t * p, Gia_Obj_t * pObj )   { static Vec_Int_t vVec; vVec.nSize = Ga2_ObjLeaveNum(p, pObj), vVec.pArray = Ga2_ObjLeavePtr(p, pObj); return &vVec; }

static inline Vec_Int_t * Ga2_ObjCnf0( Ga2_Man_t * p, Gia_Obj_t * pObj )     { assert(pObj->Value); return Vec_PtrEntry(p->vDatas, (pObj->Value << 1)  );  }
static inline Vec_Int_t * Ga2_ObjCnf1( Ga2_Man_t * p, Gia_Obj_t * pObj )     { assert(pObj->Value); return Vec_PtrEntry(p->vDatas, (pObj->Value << 1)+1);  }

static inline int         Ga2_ObjIsAbs( Ga2_Man_t * p, Gia_Obj_t * pObj )    { assert( pObj->Value ); return (int)pObj->Value < p->LimAbs;                                    }
static inline int         Ga2_ObjIsPPI( Ga2_Man_t * p, Gia_Obj_t * pObj )    { assert( pObj->Value ); return (int)pObj->Value >= p->LimAbs && (int)pObj->Value < p->LimPpi;   }

static inline Vec_Int_t * Ga2_MapFrameMap( Ga2_Man_t * p, int f )            { return (Vec_Int_t *)Vec_PtrEntry( p->vId2Lit, f );                          }


// returns literal of this object, or -1 if SAT variable of the object is not assigned
static inline int Ga2_ObjFindLit( Ga2_Man_t * p, Gia_Obj_t * pObj, int f )  
{ 
    assert( pObj->fPhase );
    assert( pObj->Value && pObj->Value < Vec_IntSize(p->vValues) );
    if ( f == Vec_PtrSize(p->vId2Lit) )
        Vec_PtrPush( p->vId2Lit, Vec_IntStartFull(Vec_IntSize(p->vValues)) );
    assert( f < Vec_PtrSize(p->vId2Lit) );
    return Vec_IntEntry( Ga2_MapFrameMap(p, f), pObj->Value );
}
// inserts literal of this object
static inline void Ga2_ObjAddLit( Ga2_Man_t * p, Gia_Obj_t * pObj, int f, int Lit )  
{ 
    assert( Lit > 1 );
    assert( Ga2_ObjFindLit(p, pObj, f) == -1 );
    Vec_IntSetEntry( Ga2_MapFrameMap(p, f), pObj->Value, Lit );
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
    unsigned Res, Values[5];
    Gia_Obj_t * pObj;
    int i;
    // assign elementary truth tables
    Gia_ManForEachObjVec( vLeaves, p, pObj, i )
    {
        assert( pObj->fPhase );
        Values[i] = pObj->Value;
        pObj->Value = uTruth5[i];
    }
    Res = Ga2_ObjComputeTruth_rec( p, pRoot, 1 );
    // return values
    Gia_ManForEachObjVec( vLeaves, p, pObj, i )
        pObj->Value = Values[i];
    return Res;
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
int Ga2_ManMarkup( Gia_Man_t * p, int N, Vec_Int_t ** pvMap )
{
    static unsigned uTruth5[5] = { 0xAAAAAAAA, 0xCCCCCCCC, 0xF0F0F0F0, 0xFF00FF00, 0xFFFF0000 };
    clock_t clk = clock();
    Vec_Int_t * vMap;
    Vec_Int_t * vLeaves;
    Gia_Obj_t * pObj;
    int i, k, Leaf, CountMarks;
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
    vLeaves = Vec_IntAlloc( 100 );
    Gia_ManForEachAnd( p, pObj, i )
    {
        if ( !pObj->fPhase )
            continue;
        Vec_IntClear( vLeaves );
        Ga2_ManCollectLeaves_rec( p, pObj, vLeaves, 1 );
        if ( Vec_IntSize(vLeaves) > N )
            Ga2_ManBreakTree_rec( p, pObj, 1, N );
    }
    // verify that the tree is split correctly
    CountMarks = 0;
    vMap = Vec_IntStart( Gia_ManObjNum(p) );
    Gia_ManForEachAnd( p, pObj, i )
    {
        if ( !pObj->fPhase )
            continue;
        Vec_IntClear( vLeaves );
        Ga2_ManCollectLeaves_rec( p, pObj, vLeaves, 1 );
//        printf( "%d ", Vec_IntSize(vLeaves) );
        assert( Vec_IntSize(vLeaves) <= N );
        // create map
        Vec_IntWriteEntry( vMap, i, Vec_IntSize(vMap) );
        Vec_IntPush( vMap, Vec_IntSize(vLeaves) );
        Vec_IntForEachEntry( vLeaves, Leaf, k )
        {
            Vec_IntPush( vMap, Leaf );
            Gia_ManObj(p, Leaf)->Value = uTruth5[k];
        }
        Vec_IntPush( vMap,  (int)Ga2_ObjComputeTruth_rec( p, pObj, 1 ) );
        Vec_IntPush( vMap, -1 );  // placeholder for ref counter
        CountMarks++;
    }
    *pvMap = vMap;
//    printf( "Internal nodes = %d.   ", CountMarks );
    Abc_PrintTime( 1, "Time", clock() - clk );
    Vec_IntFree( vLeaves );
    return CountMarks;
}
void Ga2_ManComputeTest( Gia_Man_t * p )
{
    clock_t clk;
    Vec_Int_t * vLeaves, * vMap;
    Gia_Obj_t * pObj;
    int i;
    Ga2_ManMarkup( p, 5, &vMap );
    clk = clock();
    vLeaves = Vec_IntAlloc( 100 );
    Gia_ManForEachAnd( p, pObj, i )
    {
        if ( !pObj->fPhase )
            continue;
        Vec_IntClear( vLeaves );
        Ga2_ManCollectLeaves_rec( p, pObj, vLeaves, 1 );
        Ga2_ManComputeTruth( p, pObj, vLeaves );
    }
    Vec_IntFree( vLeaves );
    Vec_IntFree( vMap );
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
    p->pGia  = pGia;
    p->pPars = pPars;
    // markings 
    p->nMarked  = Gia_ManRegNum(p->pGia) + Ga2_ManMarkup( pGia, 5, &p->vMapping );
    p->vDatas   = Vec_PtrAlloc( 1000 );
    Vec_PtrPush( p->vDatas, Vec_IntAlloc(0) );
    Vec_PtrPush( p->vDatas, Vec_IntAlloc(0) );
    // abstraction
    p->vAbs     = Vec_IntAlloc( 1000 );
    p->vValues  = Vec_IntAlloc( 1000 );
    Vec_IntPush( p->vValues, -1 );
    // refinement
    p->pRnm     = Rnm_ManStart( pGia );
    // SAT solver and variables
    p->vId2Lit  = Vec_PtrAlloc( 1000 );
    // temporaries
    p->vCnf     = Vec_IntAlloc( 100 );
    p->vLits    = Vec_IntAlloc( 100 );
    p->vIsopMem = Vec_IntAlloc( 100 );
    Cnf_ReadMsops( &p->pSopSizes, &p->pSops );
    // prepare
    Gia_ManCleanValue( pGia );
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ga2_ManStop( Ga2_Man_t * p )
{
//    if ( p->pPars->fVerbose )
        Abc_Print( 1, "SAT solver:  Var = %d  Cla = %d  Conf = %d  Reduce = %d  Cex = %d  ObjsAdded = %d\n", 
            sat_solver2_nvars(p->pSat), sat_solver2_nclauses(p->pSat), sat_solver2_nconflicts(p->pSat), p->pSat->nDBreduces, p->nCexes, p->nObjAdded );
    Vec_IntFree( p->vMapping );
    Vec_VecFree( (Vec_Vec_t *)p->vDatas );
    Vec_IntFree( p->vAbs );
    Vec_IntFree( p->vValues );
    Vec_VecFree( (Vec_Vec_t *)p->vId2Lit );
    Vec_IntFree( p->vCnf );
    Vec_IntFree( p->vLits );
    Vec_IntFree( p->vIsopMem );
    Rnm_ManStop( p->pRnm, 1 );
    sat_solver2_delete( p->pSat );
    ABC_FREE( p->pSopSizes );
    ABC_FREE( p->pSops[1] );
    ABC_FREE( p->pSops );
    ABC_FREE( p );
}


/**Function*************************************************************

  Synopsis    [Computes and minimizes the truth table.]

  Description [Array of input literals may contain 0 (const0), 1 (const1)
  or 2 (literal).  Upon exit, it contains the variables in the support.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned Ga2_ObjTruthDepends( unsigned t, int v )
{
    assert( v >= 0 && v <= 4 );
    if ( v == 0 )
        return ((t ^ (t >> 1)) & 0x55555555);
    if ( v == 1 )
        return ((t ^ (t >> 2)) & 0x33333333);
    if ( v == 2 )
        return ((t ^ (t >> 4)) & 0x0F0F0F0F);
    if ( v == 3 )
        return ((t ^ (t >> 8)) & 0x00FF00FF);
    if ( v == 4 )
        return ((t ^ (t >>16)) & 0x0000FFFF);
    return -1;
}
unsigned Ga2_ObjComputeTruthSpecial( Gia_Man_t * p, Gia_Obj_t * pRoot, Vec_Int_t * vLeaves, Vec_Int_t * vLits )
{
    static unsigned uTruth5[5] = { 0xAAAAAAAA, 0xCCCCCCCC, 0xF0F0F0F0, 0xFF00FF00, 0xFFFF0000 };
    unsigned Res, Values[5];
    Gia_Obj_t * pObj;
    int i, k, Entry;
    // assign elementary truth tables
    Gia_ManForEachObjVec( vLeaves, p, pObj, i )
    {
        assert( pObj->fPhase );
        Values[i] = pObj->Value;
        Entry = Vec_IntEntry( vLits, i );
        assert( Entry >= 0 && Entry <= 2 );
        if ( Entry == 0 )
            pObj->Value = 0;
        else if ( Entry == 1 )
            pObj->Value = ~0;
        else // if ( Entry == 2 )
            pObj->Value = uTruth5[i];
    }
    Res = Ga2_ObjComputeTruth_rec( p, pRoot, 1 );
    Vec_IntClear( vLits );
    if ( Res != 0 && Res != ~0 )
    {
        // check if truth table depends on them
        // and create a new array of literals with essential-support variables
        k = 0;
        Gia_ManForEachObjVec( vLeaves, p, pObj, i )
        {
            if ( Ga2_ObjTruthDepends( Res, i ) )
            {
                pObj->Value = uTruth5[k++];
                Vec_IntPush( vLits, i );
            }
        }
        // recompute the truth table
        Res = Ga2_ObjComputeTruth_rec( p, pRoot, 1 );
        // verify that the truthe table depends on them
        for ( i = 0; i < Vec_IntSize(vLeaves); i++ )
            assert( (i < Vec_IntSize(vLits)) == (Ga2_ObjTruthDepends(Res, i) > 0) );
    }
    // return values
    Gia_ManForEachObjVec( vLeaves, p, pObj, i )
        pObj->Value = Values[i];
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
                if ( Cube % 3 == 0 ) // value 0 --> write positive literal
                {
                    assert( Lits[b] > 1 );
                    ClaLits[nClaLits++] = Lits[b];
                }
                else if ( Cube % 3 == 1 ) // value 1 --> write negative literal
                {
                    assert( Lits[b] > 1 );
                    ClaLits[nClaLits++] = lit_neg(Lits[b]);
                }
                Cube = Cube / 3;
            }
//            if ( !sat_solver_addclause( p->pSat, ClaLits, ClaLits+nClaLits ) )
//                assert( 0 );
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
                if ( Literal == 1 ) // value 0 --> write positive literal
                {
//                    pCube[b] = '0';
                    assert( Lits[b] > 1 );
                    ClaLits[nClaLits++] = Lits[b];
                }
                else if ( Literal == 2 ) // value 1 --> write negative literal
                {
//                    pCube[b] = '1';
                    assert( Lits[b] > 1 );
                    ClaLits[nClaLits++] = lit_neg(Lits[b]);
                }
                else if ( Literal != 0 )
                    assert( 0 );
            }
//            if ( !sat_solver_addclause( p->pSat, ClaLits, ClaLits+nClaLits ) )
//                assert( 0 );
            sat_solver2_addclause( p->pSat, ClaLits, ClaLits+nClaLits, ProofId );
        }
    }
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
    assert( pObj->fPhase );
    assert( Vec_PtrSize(p->vDatas) == 2 * Vec_IntSize(p->vValues) );
    // assign value to the node
    if ( pObj->Value == 0 )
    {
        pObj->Value = Vec_IntSize(p->vValues);
        Vec_IntPush( p->vValues, Gia_ObjId(p->pGia, pObj) );
        Vec_PtrPush( p->vDatas, NULL );
        Vec_PtrPush( p->vDatas, NULL );
    }
    assert( Ga2_ObjCnf0(p, pObj) == NULL );
    if ( !fAbs )
        return;
    // compute parameters
    nLeaves = Ga2_ObjLeaveNum(p, pObj);
    uTruth = Ga2_ObjTruth( p, pObj );
    // create CNF for pos/neg phases
    Vec_PtrWriteEntry( p->vDatas, 2 * pObj->Value,     Ga2_ManCnfCompute(uTruth, nLeaves, p->vIsopMem) );    
    uTruth = (~uTruth) & Abc_InfoMask( (1 << nLeaves) );
    Vec_PtrWriteEntry( p->vDatas, 2 * pObj->Value + 1, Ga2_ManCnfCompute(uTruth, nLeaves, p->vIsopMem) );
}

void Ga2_ManAddToAbs( Ga2_Man_t * p, Vec_Int_t * vToAdd )
{
    Vec_Int_t * vLeaves, * vMap;
    Gia_Obj_t * pObj, * pFanin;
    int i, k;
    // add abstraction objects
    Gia_ManForEachObjVec( vToAdd, p->pGia, pObj, i )
    {
        Ga2_ManSetupNode( p, pObj, 1 );
        Vec_IntPush( p->vAbs, Gia_ObjId(p->pGia, pObj) );
    }
    // add PPI objects
    Gia_ManForEachObjVec( vToAdd, p->pGia, pObj, i )
    {
        vLeaves = Ga2_ObjLeaves( p, pObj );
        Gia_ManForEachObjVec( vLeaves, p->pGia, pFanin, k, )
            Ga2_ManSetupNode( p, pObj, 0 );
    }
    // clean mapping into timeframes
    Vec_PtrForEachEntry( Vec_Int_t *, p->vId2Lit, vMap, i )
        Vec_IntFillExtra( vMap, Vec_IntSize(p->vValues), -1 );
}

void Ga2_ManShrinkAbs( Ga2_Man_t * p, int nAbs, int nValues )
{
    Vec_Int_t * vMap;
    Gia_Obj_t * pObj;
    int i;
    assert( nAbs >= 0 );
    assert( nValues > 0 );
    // shrink abstraction
    Gia_ManForEachObjVec( p->vAbs, p->pGia, pObj, i )
    {
        assert( Ga2_ObjCnf0(p, pObj) != NULL );
        assert( Ga2_ObjCnf1(p, pObj) != NULL );
        if ( i < nAbs )
            continue;
        Vec_IntFree( Ga2_ObjCnf0(p, pObj) );
        Vec_IntFree( Ga2_ObjCnf1(p, pObj) );
        Vec_PtrWriteEntry( p->vDatas, 2 * pObj->Value,     NULL );    
        Vec_PtrWriteEntry( p->vDatas, 2 * pObj->Value + 1, NULL );
    }
    Vec_IntShrink( p->vAbs, nAbs );
    // shrink values
    Gia_ManForEachObjVec( p->vValues, p->pGia, pObj, i )
    {
        assert( pObj->Value );
        if ( i < nValues )
            continue;
        pObj->Value = 0;
    }
    Vec_IntShrink( p->vValues, nValues );
    // clean mapping into timeframes
    Vec_PtrForEachEntry( Vec_Int_t *, p->vId2Lit, vMap, i )
        Vec_IntShrink( vMap, nValues );
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
    Gia_ManForEachObjVec( p->vAbs, p->pGia, pObj, i )
        Ga2_ManAbsTranslate_rec( p->pGia, pObj, vGateClasses, 1 );
    return vGateClasses;
}
Vec_Int_t * Ga2_ManAbsDerive( Gia_Man_t * p )
{
    Vec_Int_t * vToAdd;
    Gia_Obj_t * pObj;
    int i;
    vToAdd = Vec_IntAlloc( 1000 );
    Gia_ManForEachObj( p, pObj, i )
        if ( pObj->fPhase && Vec_IntEntry(p->vGateClasses, i) )
            Vec_IntPush( vToAdd, i );
    return vToAdd;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ga2_ManRestart( Ga2_Man_t * p )
{
    Vec_Int_t * vToAdd;
    assert( p->pGia != NULL );
    assert( p->pGia->vGateClasses != NULL );
    assert( Gia_ManPi(p->pGia, 0)->fPhase ); // marks are set
    // clear mappings from objects
    Ga2_ManShrinkAbs( p, 0, 1 );
    // clear SAT variable numbers (begin with 1)
    if ( p->pSat ) sat_solver2_delete( p->pSat );
    p->pSat      = sat_solver2_new();
    p->nSatVars  = 1;
    // start abstraction
    vToAdd = Ga2_ManAbsDerive( p->pGia );
    Ga2_ManAddToAbs( p, vToAdd );
    Vec_IntFree( vToAdd );
    p->LimAbs = Vec_IntSize(p->vAbs) + 1;
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
    Vec_Int_t * vLeaves;
    Gia_Obj_t * pLeaf;
    unsigned uTruth;
    int nLeaves, * pLeaves;
    int i, Lit, pLits[5];
    if ( Gia_ObjIsCo(pObj) )
        return Abc_LitNotCond( Ga2_ManUnroll_rec(p, Gia_ObjFanin0(pObj), f), Gia_ObjFaninC0(pObj) );
    if ( Gia_ObjIsConst0(pObj) || (f==0 && Gia_ObjIsRo(p->pGia, pObj)) )
        return 0;
    Lit = Ga2_ObjFindLit( p, pObj, f );
    if ( Lit >= 0 )
        return Lit;
    if ( Gia_ObjIsPi(p->pGia, pObj) )
        return Ga2_ObjFindOrAddLit( p, pObj, f );
    if ( Gia_ObjIsRo(p->pGia, pObj) )
    {
        assert( f > 0 );
        Lit = Ga2_ManUnroll_rec( p, Gia_ObjRoToRi(p->pGia, pObj), f-1 );
        Ga2_ObjAddLit( p, pObj, f, Lit );
        return Lit;
    }
    // collect fanin literals
    nLeaves = Ga2_ObjLeaveNum( p, pObj );
    pLeaves = Ga2_ObjLeavePtr( p, pObj );
    for ( i = 0; i < nLeaves; i++ )
    {
        pLeaf = Gia_ManObj( p->pGia, pLeaves[i] );
        if ( Ga2_ObjIsAbs(p, pLeaf) )      // belongs to original abstraction
            pLits[i] = Ga2_ManUnroll_rec( p, pObj, f );
        else if ( Ga2_ObjIsPPI(p, pLeaf) ) // belongs to original PPIs
            pLits[i] = GA2_BIG_NUM + i;
        else
            assert( 0 );
    }
    // collect literals
    Vec_IntClear( p->vLits );
    for ( i = 0; i < nLeaves; i++ )
        Vec_IntPush( p->vLits, pLits[i] );
    // minimize truth table
    vLeaves = Ga2_ObjLeaves( p, pObj );
    uTruth = Ga2_ObjComputeTruthSpecial( p->pGia, pObj, vLeaves, p->vLits );
    if ( uTruth == 0 || uTruth == ~0 )
        Ga2_ObjAddLit( p, pObj, f, uTruth == 0 ? 3 : 2 );     // const 0 / 1
    else if ( uTruth == 0xAAAAAAAA || uTruth == 0x55555555 )  // buffer / inverter
    {
        Lit = Vec_IntEntry( p->vLits, 0 );
        pLeaf = Gia_ManObj( p->pGia, Vec_IntEntry(vLeaves, Lit) );
        Lit = Ga2_ObjFindOrAddLit( p, pLeaf, f );
        Ga2_ObjAddLit( p, pObj, f, Abc_LitNotCond(Lit, uTruth == 0x55555555) );
    }
    else
    {
        // replace numbers of literals by actual literals
        Vec_IntForEachEntry( p->vLits, Lit, i )
        {
            pLeaf = Gia_ManObj( p->pGia, Vec_IntEntry(vLeaves, Lit) );
            Lit = Ga2_ObjFindOrAddLit(p, pLeaf, f);
            Vec_IntWriteEntry( p->vLits, i, Lit );        
        }
        // add CNF
        Lit = Ga2_ObjFindOrAddLit(p, pObj, f);
        Ga2_ManCnfAddDynamic( p, uTruth, Vec_IntArray(p->vLits), Lit, 0 );
        Ga2_ObjAddLit( p, pObj, f, Lit );
    }
    return Lit;
}

/**Function*************************************************************

  Synopsis    [Unrolls one timeframe.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
/*
void Ga2_ManUnroll2( Ga2_Man_t * p, int f )
{
    Gia_Obj_t * pObj, * pObjRi, * pLeaf;
    Vec_Int_t * vLeaves;
    unsigned uTruth;
    int i, k, Lit, iLitOut, fFullTable;
    // construct CNF for internal nodes
    Gia_ManForEachObjVec( p->vAbs, p->pGia, pObj, i )
    {
        // assign RO literal values (no need to add clauses)
        assert( pObj->fPhase && pObj->Value );
        if ( Gia_ObjIsConst0(pObj) )
        {
            Ga2_ObjAddLit( p, pObj, f, 3 ); // const 0 
            continue;
        }
        if ( Gia_ObjIsRo(p->pGia, pObj) )
        {
            pObjRi = Gia_ObjRoToRi(p->pGia, pObj);
            Lit = f ? Ga2_ObjFindOrAddLit( p, pObjRi, f-1 ) : 3;  // const 0
            Ga2_ObjAddLit( p, pObj, f, Lit ); 
            continue;
        }
        assert( Gia_ObjIsAnd(pObj) );
        assert( pObj->Value > 0 );
        vLeaves = Ga2_ObjLeaves(p, pObj);
        // for nodes recently added to abstraction, add CNF without const propagation
        fFullTable = 1;
        if ( i < p->nAbs )
        {
            Gia_ManForEachObjVec( vLeaves, p->pGia, pLeaf, k )
            {
                Lit = Ga2_ObjFindLit( p, pLeaf, f );
                if ( Lit == 2 || Lit == 3 )
                {
                    fFullTable = 0;
                    break;
                }
            }
        }
        if ( fFullTable )
        {
            Vec_IntClear( p->vLits );
            Gia_ManForEachObjVec( vLeaves, p->pGia, pLeaf, k )
                Vec_IntWriteEntry( p->vLits, k, Ga2_ObjFindOrAddLit(p, pLeaf, f) );        
            iLitOut = Ga2_ObjFindOrAddLit(p, pObj, f);
            Ga2_ManCnfAddStatic( p, &p->pvCnfs0[pObj->Value], &p->pvCnfs1[pObj->Value], 
                Vec_IntArray(p->vLits), iLitOut, i < p->nAbs ? 0 : Gia_ObjId(p->pGia, pObj) );
            continue;
        }
        assert( i < p->nAbs );
        // collect literal types
        Vec_IntClear( p->vLits );
        Gia_ManForEachObjVec( vLeaves, p->pGia, pLeaf, k )
        {
            Lit = Ga2_ObjFindLit( p, pLeaf, f );
            if ( Lit == 3 ) // const 0
                Vec_IntPush( p->vLits, 0 );
            else if ( Lit == 2 ) // const 1
                Vec_IntPush( p->vLits, 1 );
            else 
                Vec_IntPush( p->vLits, 2 );
        }
        uTruth = Ga2_ObjComputeTruthSpecial( p->pGia, pObj, vLeaves, p->vLits );
        if ( uTruth == 0 || uTruth == ~0 )
            Ga2_ObjAddLit( p, pObj, f, uTruth == 0 ? 3 : 2 );     // const 0 / 1
        else if ( uTruth == 0xAAAAAAAA || uTruth == 0x55555555 )  // buffer / inverter
        {
            Lit = Vec_IntEntry( p->vLits, 0 );
            pLeaf = Gia_ManObj( p->pGia, Vec_IntEntry(vLeaves, Lit) );
            Lit = Ga2_ObjFindOrAddLit( p, pLeaf, f );
            Ga2_ObjAddLit( p, pObj, f, Abc_LitNotCond(Lit, uTruth == 0x55555555) );
        }
        else
        {
            // replace numbers of literals by actual literals
            Vec_IntForEachEntry( p->vLits, Lit, i )
            {
                pLeaf = Gia_ManObj( p->pGia, Vec_IntEntry(vLeaves, Lit) );
                Lit = Ga2_ObjFindOrAddLit(p, pLeaf, f);
                Vec_IntWriteEntry( p->vLits, i, Lit );        
            }
            // add CNF
            iLitOut = Ga2_ObjFindOrAddLit(p, pObj, f);
            Ga2_ManCnfAddDynamic( p, uTruth, Vec_IntArray(p->vLits), iLitOut, 0 );
        }
    }
    // propagate literals to the PO and flop outputs
    pObjRi = Gia_ManPo( p->pGia, 0 );
    Lit = Ga2_ObjFindLit( p, Gia_ObjFanin0(pObjRi), f );
    assert( Lit > 1 );
    Lit = Abc_LitNotCond( Lit, Gia_ObjFaninC0(pObjRi) );
    Ga2_ObjAddLit( p, pObj, f, Lit ); 
    Gia_ManForEachObjVec( p->vAbs, p->pGia, pObj, i )
    {
        if ( !Gia_ObjIsRo(p->pGia, pObj) )
            continue;
        pObjRi = Gia_ObjRoToRi(p->pGia, pObj);
        Lit = Ga2_ObjFindLit( p, Gia_ObjFanin0(pObjRi), f );
        assert( Lit > 1 );
        Lit = Abc_LitNotCond( Lit, Gia_ObjFaninC0(pObjRi) );
        Ga2_ObjAddLit( p, pObjRi, f, Lit ); 
    }
}
*/

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
    return Abc_LitIsCompl( Lit ) ^ sat_solver2_var_value( p->pSat, Abc_Lit2Var(Lit) );
}
void Ga2_GlaPrepareCexAndMap( Ga2_Man_t * p, Abc_Cex_t ** ppCex, Vec_Int_t ** pvMaps )
{
    Abc_Cex_t * pCex;
    Vec_Int_t * vMap;
    Gia_Obj_t * pObj;
    int f, i, k;
    // find PIs and PPIs
    vMap = Vec_IntAlloc( 1000 );
    Gia_ManForEachObjVec( p->vAbs, p->pGia, pObj, i )
    {
        if ( Gia_ObjIsAnd(pObj) )
        {
            if ( !Gia_ObjFanin0(pObj)->fMark0 ) // not used
                Vec_IntPush( vMap, Gia_ObjFaninId0p(p->pGia, pObj) );
            if ( !Gia_ObjFanin0(pObj)->fMark1 ) // not used
                Vec_IntPush( vMap, Gia_ObjFaninId1p(p->pGia, pObj) );
        }
        else if ( Gia_ObjIsRo(p->pGia, pObj) )
        {
            pObj = Gia_ObjRoToRi( p->pGia, pObj );
            if ( !Gia_ObjFanin0(pObj)->fMark0 ) // not used
                Vec_IntPush( vMap, Gia_ObjFaninId0p(p->pGia, pObj) );
        }
        else assert( 0 );
    }
    Vec_IntUniqify( vMap );
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
    // remap them into GLA objects
//    Gia_ManForEachObjVec( vVec, p->pGia, pObj, i )
//        Vec_IntWriteEntry( vVec, i, p->pObj2Obj[Gia_ObjId(p->pGia, pObj)] );
    p->nObjAdded += Vec_IntSize(vVec);
    return vVec;
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
    clock_t clk = clock();
    int i, c, f, Lit, nAbs, nValues, Status, RetValue = -1;;
    // start the manager
    p = Ga2_ManStart( pAig, pPars );
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
        Abc_Print( 1, "Frame   %%   Abs  PPI   FF   LUT   Confl  Cex   Vars   Clas   Lrns     Time      Mem\n" );
    }
    // iterate unrolling
    for ( i = f = 0; !pPars->nFramesMax || f < pPars->nFramesMax; i++ )
    {
        // create new SAT solver
        Ga2_ManRestart( p );
        // remember current limits
        nAbs    = Vec_IntSize(p->vAbs);
        nValues = Vec_IntSize(p->vValues);
        // unroll the circuit
        for ( f = 0; !pPars->nFramesMax || f < pPars->nFramesMax; f++ )
        {
            p->pPars->iFrame = f;
            // get the output literal
            Lit = Ga2_ManUnroll_rec( p, Gia_ManPo(pAig,0), f );
            // check for counter-examples
            for ( c = 0; ; c++ )
            {
                // perform SAT solving
                Status = sat_solver2_solve( p->pSat, &Lit, &Lit+1, (ABC_INT64_T)pPars->nConfLimit, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
                if ( Status == l_True ) // perform refinement
                {
                    vPPis = Ga2_ManRefine( p );
                    if ( vPPis == NULL )
                        goto finish;
                    Ga2_ManAddToAbs( p, vPPis );
                    Vec_IntFree( vPPis );
                    // verify
                    if ( Vec_IntCheckUnique(p->vAbs) )
                        printf( "Vector has %d duplicated entries.\n", Vec_IntCheckUnique(p->vAbs) );
                    continue;
                }
                if ( p->pSat->nRuntimeLimit && clock() > p->pSat->nRuntimeLimit ) // timeout
                    goto finish;
                if ( Status == l_Undef ) // ran out of resources
                    goto finish;
                assert( RetValue == l_False );
                // derive UNSAT core
                vCore = (Vec_Int_t *)Sat_ProofCore( p->pSat );
                Ga2_ManShrinkAbs( p, nAbs, nValues );
                Ga2_ManAddToAbs( p, vCore );
                Vec_IntFree( vCore );
                // remember current limits
                nAbs    = Vec_IntSize(p->vAbs);
                nValues = Vec_IntSize(p->vValues);
                // verify
                if ( Vec_IntCheckUnique(p->vAbs) )
                    printf( "Vector has %d duplicated entries.\n", Vec_IntCheckUnique(p->vAbs) );
                break;
            }
            if ( c > 0 )
            {
                Vec_IntFreeP( &pAig->vGateClasses );
                pAig->vGateClasses = Ga2_ManAbsTranslate( p );
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
//        Ga2_ManReportMemory( p );
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

