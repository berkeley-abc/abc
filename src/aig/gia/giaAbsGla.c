/**CFile****************************************************************

  FileName    [giaAbsGla.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Gate-level abstraction.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaAbsGla.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "giaAig.h"
#include "src/sat/cnf/cnf.h"
#include "src/sat/bsat/satSolver2.h"
#include "src/base/main/main.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Rfn_Obj_t_ Rfn_Obj_t; // refinement object
struct Rfn_Obj_t_
{
    unsigned       Value     :  1;  // value
    unsigned       fVisit    :  1;  // visited
    unsigned       fPPi      :  1;  // PPI
    unsigned       Prio      : 18;  // priority
    unsigned       Sign      : 10;  // priority
};

typedef struct Gla_Obj_t_ Gla_Obj_t; // abstraction object
struct Gla_Obj_t_
{
    int            iGiaObj;         // corresponding GIA obj
    unsigned       fAbs      :  1;  // belongs to abstraction
    unsigned       fCompl0   :  1;  // compl bit of the first fanin
    unsigned       fConst    :  1;  // object attribute
    unsigned       fPi       :  1;  // object attribute
    unsigned       fPo       :  1;  // object attribute
    unsigned       fRo       :  1;  // object attribute
    unsigned       fRi       :  1;  // object attribute
    unsigned       fAnd      :  1;  // object attribute
    unsigned       fMark     :  1;  // nearby object
    unsigned       nFanins   : 23;  // fanin count
    int            Fanins[4];       // fanins
    Vec_Int_t      vFrames;         // variables in each timeframe
};

typedef struct Gla_Man_t_ Gla_Man_t; // manager
struct Gla_Man_t_
{
    // user data
    Gia_Man_t *    pGia0;           // starting AIG manager
    Gia_Man_t *    pGia;            // working AIG manager
    Gia_ParVta_t*  pPars;           // parameters
    // internal data
    Vec_Int_t *    vAbs;            // abstracted objects
    Gla_Obj_t *    pObjRoot;        // the primary output
    Gla_Obj_t *    pObjs;           // objects
    unsigned *     pObj2Obj;        // mapping of GIA obj into GLA obj
    int            nObjs;           // the number of objects
    int            nAbsOld;         // previous abstraction
    // other data
    int            nCexes;          // the number of counter-examples
    int            nSatVars;        // the number of SAT variables
    Cnf_Dat_t *    pCnf;            // CNF derived for the nodes
    sat_solver2 *  pSat;            // incremental SAT solver
    Vec_Int_t *    vCla2Obj;        // mapping of clauses into GLA objs
    Vec_Int_t *    vTemp;           // temporary array
    Vec_Int_t *    vAddedNew;       // temporary array
    Vec_Int_t *    vPrevCore;       // previous core
    // refinement
    Vec_Int_t *    pvRefis;         // vectors of each object
    Vec_Int_t *    vPrioSels;       // selected priorities
    // statistics  
    int            timeInit;
    int            timeSat;
    int            timeUnsat;
    int            timeCex;
    int            timeOther;
};

// declarations
static Vec_Int_t * Gla_ManCollectPPis( Gla_Man_t * p, Vec_Int_t * vPis );
static int         Gla_ManCheckVar( Gla_Man_t * p, int iObj, int iFrame );
static int         Gla_ManGetVar( Gla_Man_t * p, int iObj, int iFrame );

// object procedures
static inline int         Gla_ObjId( Gla_Man_t * p, Gla_Obj_t * pObj )      { assert( pObj > p->pObjs && pObj < p->pObjs + p->nObjs ); return pObj - p->pObjs;   }
static inline Gla_Obj_t * Gla_ManObj( Gla_Man_t * p, int i )                { assert( i >= 0 && i < p->nObjs ); return i ? p->pObjs + i : NULL;                  }
static inline Gia_Obj_t * Gla_ManGiaObj( Gla_Man_t * p, Gla_Obj_t * pObj )  { return Gia_ManObj( p->pGia, pObj->iGiaObj );                                       }
static inline int         Gla_ObjSatValue( Gla_Man_t * p, int iGia, int f ) { return Gla_ManCheckVar(p, p->pObj2Obj[iGia], f) ? sat_solver2_var_value( p->pSat, Gla_ManGetVar(p, p->pObj2Obj[iGia], f) ) : 0;  }

static inline Rfn_Obj_t * Gla_ObjRef( Gla_Man_t * p, int iObj, int f )      {  return (Rfn_Obj_t *)Vec_IntGetEntryP( &(p->pvRefis[iObj]), f );                   }
static inline void        Gla_ObjClearRef( Rfn_Obj_t * p )                  {  *((int *)p) = 0;                                                                  }


// iterator through abstracted objects
#define Gla_ManForEachObj( p, pObj )                       \
    for ( pObj = p->pObjs + 1; pObj < p->pObjs + p->nObjs; pObj++ ) 
#define Gla_ManForEachObjAbs( p, pObj, i )                 \
    for ( i = 0; i < Vec_IntSize(p->vAbs) && ((pObj = Gla_ManObj(p, Vec_IntEntry(p->vAbs, i))),1); i++) 
#define Gla_ManForEachObjAbsVec( vVec, p, pObj, i )        \
    for ( i = 0; i < Vec_IntSize(vVec) && ((pObj = Gla_ManObj(p, Vec_IntEntry(vVec, i))),1); i++) 

// iterator through fanins of an abstracted object
#define Gla_ObjForEachFanin( p, pObj, pFanin, i )          \
    for ( i = 0; (i < (int)pObj->nFanins) && ((pFanin = Gla_ManObj(p, pObj->Fanins[i])),1); i++ )

// some lessons learned from debugging mismatches between GIA and mapped CNF
// - inputs/output of AND-node maybe PPIs (have SAT vars), but the node is not included in the abstraction
// - some logic node can be a PPI of one LUT and an internal node of another LUT

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Derive a new counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t * Gia_ManCexRemap( Gia_Man_t * p, Abc_Cex_t * pCexAbs, Vec_Int_t * vPis )
{
    Abc_Cex_t * pCex;
    int i, f, iPiNum;
    assert( pCexAbs->iPo == 0 );
    // start the counter-example
    pCex = Abc_CexAlloc( Gia_ManRegNum(p), Gia_ManPiNum(p), pCexAbs->iFrame+1 );
    pCex->iFrame = pCexAbs->iFrame;
    pCex->iPo    = pCexAbs->iPo;
    // copy the bit data
    for ( f = 0; f <= pCexAbs->iFrame; f++ )
        for ( i = 0; i < Vec_IntSize(vPis); i++ )
        {
            if ( Abc_InfoHasBit( pCexAbs->pData, pCexAbs->nRegs + pCexAbs->nPis * f + i ) )
            {
                iPiNum = Gia_ObjCioId( Gia_ManObj(p, Vec_IntEntry(vPis, i)) );
                Abc_InfoSetBit( pCex->pData, pCex->nRegs + pCex->nPis * f + iPiNum );
            }
        }
    // verify the counter example
    if ( !Gia_ManVerifyCex( p, pCex, 0 ) )
    {
        printf( "Gia_ManCexRemap(): Counter-example is invalid.\n" );
        Abc_CexFree( pCex );
        pCex = NULL;
    }
    else
    {
        printf( "Counter-example verification is successful.\n" );
        printf( "Output %d was asserted in frame %d (use \"write_counter\" to dump a witness). \n", pCex->iPo, pCex->iFrame );
    }
    return pCex;
}

/**Function*************************************************************

  Synopsis    [Refines gate-level abstraction using the counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManGlaRefine( Gia_Man_t * p, Abc_Cex_t * pCex, int fMinCut, int fVerbose )
{
    extern void Nwk_ManDeriveMinCut( Gia_Man_t * p, int fVerbose );
    extern Abc_Cex_t * Saig_ManCbaFindCexCareBits( Aig_Man_t * pAig, Abc_Cex_t * pCex, int nInputs, int fVerbose );
    int fAddOneLayer = 1;
    Abc_Cex_t * pCexNew = NULL;
    Gia_Man_t * pAbs;
    Aig_Man_t * pAig;
    Abc_Cex_t * pCare;
    Vec_Int_t * vPis, * vPPis;
    int f, i, iObjId, clk = clock();
    int nOnes = 0, Counter = 0;
    if ( p->vGateClasses == NULL )
    {
        printf( "Gia_ManGlaRefine(): Abstraction gate map is missing.\n" );
        return -1;
    }
    // derive abstraction
    pAbs = Gia_ManDupAbsGates( p, p->vGateClasses );
    Gia_ManStop( pAbs );
    pAbs = Gia_ManDupAbsGates( p, p->vGateClasses );
    if ( Gia_ManPiNum(pAbs) != pCex->nPis )
    {
        printf( "Gia_ManGlaRefine(): The PI counts in GLA and in CEX do not match.\n" );
        Gia_ManStop( pAbs );
        return -1;
    }
    if ( !Gia_ManVerifyCex( pAbs, pCex, 0 ) )
    {
        printf( "Gia_ManGlaRefine(): The initial counter-example is invalid.\n" );
        Gia_ManStop( pAbs );
        return -1;
    }
//    else
//        printf( "Gia_ManGlaRefine(): The initial counter-example is correct.\n" );
    // get inputs
    Gia_ManGlaCollect( p, p->vGateClasses, &vPis, &vPPis, NULL, NULL );
    assert( Vec_IntSize(vPis) + Vec_IntSize(vPPis) == Gia_ManPiNum(pAbs) );
    // add missing logic
    if ( fAddOneLayer )
    {
        Gia_Obj_t * pObj;
        // check if this is a real counter-example
        Gia_ObjTerSimSet0( Gia_ManConst0(pAbs) );
        for ( f = 0; f <= pCex->iFrame; f++ )
        {
            Gia_ManForEachPi( pAbs, pObj, i )
            {
                if ( i >= Vec_IntSize(vPis) ) // PPIs
                    Gia_ObjTerSimSetX( pObj );
                else if ( Abc_InfoHasBit(pCex->pData, pCex->nRegs + pCex->nPis * f + i) )
                    Gia_ObjTerSimSet1( pObj );
                else
                    Gia_ObjTerSimSet0( pObj );
            }
            Gia_ManForEachRo( pAbs, pObj, i )
            {
                if ( f == 0 )
                    Gia_ObjTerSimSet0( pObj );
                else
                    Gia_ObjTerSimRo( pAbs, pObj );
            }
            Gia_ManForEachAnd( pAbs, pObj, i )
                Gia_ObjTerSimAnd( pObj );
            Gia_ManForEachCo( pAbs, pObj, i )
                Gia_ObjTerSimCo( pObj );
        }
        pObj = Gia_ManPo( pAbs, 0 );
        if ( Gia_ObjTerSimGet1(pObj) )
        {
            pCexNew = Gia_ManCexRemap( p, pCex, vPis );
            printf( "Procedure &gla_refine found a real counter-example in frame %d.\n", pCexNew->iFrame );
        }
//        else
//            printf( "CEX is not real.\n" );
        Gia_ManForEachObj( pAbs, pObj, i )
            Gia_ObjTerSimSetC( pObj );
        if ( pCexNew == NULL )
        {
            // grow one layer
            Vec_IntForEachEntry( vPPis, iObjId, i )
            {
                assert( Vec_IntEntry( p->vGateClasses, iObjId ) == 0 );
                Vec_IntWriteEntry( p->vGateClasses, iObjId, 1 );
            }
            if ( fVerbose )
            {
                printf( "Additional objects = %d.  ", Vec_IntSize(vPPis) );
                Abc_PrintTime( 1, "Time", clock() - clk );
            }
        }
    }
    else
    {
        // minimize the CEX
        pAig = Gia_ManToAigSimple( pAbs );
        pCare = Saig_ManCbaFindCexCareBits( pAig, pCex, Vec_IntSize(vPis), fVerbose );
        Aig_ManStop( pAig );
        if ( pCare == NULL )
            printf( "Counter-example minimization has failed.\n" );
        // add new objects to the map
        iObjId = -1;
        for ( f = 0; f <= pCare->iFrame; f++ )
            for ( i = 0; i < pCare->nPis; i++ )
                if ( Abc_InfoHasBit( pCare->pData, pCare->nRegs + f * pCare->nPis + i ) )
                {
                    nOnes++;
                    assert( i >= Vec_IntSize(vPis) );
                    iObjId = Vec_IntEntry( vPPis, i - Vec_IntSize(vPis) );
                    assert( iObjId > 0 && iObjId < Gia_ManObjNum(p) );
                    if ( Vec_IntEntry( p->vGateClasses, iObjId ) == 1 )
                        continue;
                    assert( Vec_IntEntry( p->vGateClasses, iObjId ) == 0 );
                    Vec_IntWriteEntry( p->vGateClasses, iObjId, 1 );
    //                printf( "Adding object %d.\n", iObjId );
    //                Gia_ObjPrint( p, Gia_ManObj(p, iObjId) );
                    Counter++;
                }
        Abc_CexFree( pCare );
        if ( fVerbose )
        {
            printf( "Essential bits = %d.  Additional objects = %d.  ", nOnes, Counter );
            Abc_PrintTime( 1, "Time", clock() - clk );
        }
        // consider the case of SAT
        if ( iObjId == -1 )
        {
            pCexNew = Gia_ManCexRemap( p, pCex, vPis );
            printf( "Procedure &gla_refine found a real counter-example in frame %d.\n", pCexNew->iFrame );
        }
    }
    Vec_IntFree( vPis );
    Vec_IntFree( vPPis );
    Gia_ManStop( pAbs );
    if ( pCexNew )
    {
        ABC_FREE( p->pCexSeq );
        p->pCexSeq = pCexNew;
        return 0;
    }
    // extract abstraction to include min-cut
    if ( fMinCut )
        Nwk_ManDeriveMinCut( p, fVerbose );
    return -1;
}





/**Function*************************************************************

  Synopsis    [Derives counter-example using current assignments.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t * Gla_ManDeriveCex( Gla_Man_t * p, Vec_Int_t * vPis )
{
    Abc_Cex_t * pCex;
    Gia_Obj_t * pObj;
    int i, f;
    pCex = Abc_CexAlloc( Gia_ManRegNum(p->pGia), Gia_ManPiNum(p->pGia), p->pPars->iFrame+1 );
    pCex->iPo = 0;
    pCex->iFrame = p->pPars->iFrame;
    Gia_ManForEachObjVec( vPis, p->pGia, pObj, i )
    {
        assert( Gia_ObjIsPi(p->pGia, pObj) );
        for ( f = 0; f <= pCex->iFrame; f++ )
            if ( Gla_ObjSatValue( p, Gia_ObjId(p->pGia, pObj), f ) )
                Abc_InfoSetBit( pCex->pData, pCex->nRegs + f * pCex->nPis + Gia_ObjCioId(pObj) );
    }
    return pCex;
}

/**Function*************************************************************

  Synopsis    [Collects GIA abstraction objects.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gla_ManCollectInternal_rec( Gia_Man_t * p, Gia_Obj_t * pGiaObj, Vec_Int_t * vRoAnds )
{
    int Value0, Value1;
    if ( Gia_ObjIsTravIdCurrent(p, pGiaObj) )
        return 1;
    Gia_ObjSetTravIdCurrent(p, pGiaObj);
    if ( Gia_ObjIsCi(pGiaObj) )
        return 0;
    assert( Gia_ObjIsAnd(pGiaObj) );
    Value0 = Gla_ManCollectInternal_rec( p, Gia_ObjFanin0(pGiaObj), vRoAnds );
    Value1 = Gla_ManCollectInternal_rec( p, Gia_ObjFanin1(pGiaObj), vRoAnds );
    if ( Value0 || Value1 )
    {
        assert( Gia_ObjIsAnd(pGiaObj) );
        Vec_IntPush( vRoAnds, Gia_ObjId(p, pGiaObj) );
    }
    return Value0 || Value1;
}
void Gla_ManCollect( Gla_Man_t * p, Vec_Int_t * vPis, Vec_Int_t * vPPis, Vec_Int_t * vCos, Vec_Int_t * vRoAnds )
{
    Gla_Obj_t * pObj, * pFanin;
    Gia_Obj_t * pGiaObj;
    int i, k;

    // collect COs
    Vec_IntPush( vCos, Gia_ObjId(p->pGia, Gia_ManPo(p->pGia, 0)) );
    // collect fanins of abstracted objects
    Gla_ManForEachObjAbs( p, pObj, i )
    {
        assert( pObj->fConst || pObj->fRo || pObj->fAnd );
        if ( pObj->fRo )
        {
            pGiaObj = Gia_ObjRoToRi( p->pGia, Gia_ManObj(p->pGia, pObj->iGiaObj) );
            Vec_IntPush( vCos, Gia_ObjId(p->pGia, pGiaObj) );
        }
        Gla_ObjForEachFanin( p, pObj, pFanin, k )
            if ( !pFanin->fAbs )
                Vec_IntPush( (pFanin->fPi ? vPis : vPPis), pFanin->iGiaObj );
    }
    Vec_IntUniqify( vPis );
    Vec_IntUniqify( vPPis );

    // mark const/PIs/PPIs
    Gia_ManIncrementTravId( p->pGia );
    Gia_ObjSetTravIdCurrent( p->pGia, Gia_ManConst0(p->pGia) );
    Gia_ManForEachObjVec( vPis, p->pGia, pGiaObj, i )
        Gia_ObjSetTravIdCurrent( p->pGia, pGiaObj );
    Gia_ManForEachObjVec( vPPis, p->pGia, pGiaObj, i )
        Gia_ObjSetTravIdCurrent( p->pGia, pGiaObj );
    // mark and add ROs first
    Gia_ManForEachObjVec( vCos, p->pGia, pGiaObj, i )
    {
        if ( i == 0 ) continue;
        pGiaObj = Gia_ObjRiToRo( p->pGia, pGiaObj );
        Gia_ObjSetTravIdCurrent( p->pGia, pGiaObj );
        Vec_IntPush( vRoAnds, Gia_ObjId(p->pGia, pGiaObj) );
    }
    // collect nodes between PIs/PPIs/ROs and COs
    Gia_ManForEachObjVec( vCos, p->pGia, pGiaObj, i )
        Gla_ManCollectInternal_rec( p->pGia, Gia_ObjFanin0(pGiaObj), vRoAnds );
}

/**Function*************************************************************

  Synopsis    [Selects assignments to be refined.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gla_ManRefSelect_rec( Gla_Man_t * p, Gia_Obj_t * pObj, int f, Vec_Int_t * vRes, int Sign )
{
    Rfn_Obj_t * pRef = Gla_ObjRef( p, Gia_ObjId(p->pGia, pObj), f );
    assert( (int)pRef->Sign == Sign );
    if ( pRef->fVisit )
        return;
    pRef->fVisit = 1;
    if ( pRef->fPPi )
    {
        assert( (int)pRef->Prio > 0 );
        assert( (int)pRef->Prio < Vec_IntSize(p->vPrioSels) );
        if ( Vec_IntEntry( p->vPrioSels, pRef->Prio ) == 0 ) // not selected yet
        {
            Vec_IntWriteEntry( p->vPrioSels, pRef->Prio, 1 );
            Vec_IntPush( vRes, Gia_ObjId(p->pGia, pObj) );
        }
        return;
    }
    if ( Gia_ObjIsPi(p->pGia, pObj) || Gia_ObjIsConst0(pObj) )
        return;
    if ( Gia_ObjIsRo(p->pGia, pObj) )
    {
        if ( f > 0 )
            Gla_ManRefSelect_rec( p, Gia_ObjFanin0(Gia_ObjRoToRi(p->pGia, pObj)), f-1, vRes, Sign );
        return;
    }
    if ( Gia_ObjIsAnd(pObj) )
    {
        Rfn_Obj_t * pRef0 = Gla_ObjRef( p, Gia_ObjFaninId0p(p->pGia, pObj), f );
        Rfn_Obj_t * pRef1 = Gla_ObjRef( p, Gia_ObjFaninId1p(p->pGia, pObj), f );
        int fSel0 = Vec_IntEntry( p->vPrioSels, pRef0->Prio );
        int fSel1 = Vec_IntEntry( p->vPrioSels, pRef1->Prio );
        if ( pRef->Value == 1 )
        {
//            if ( !fSel0 )
                Gla_ManRefSelect_rec( p, Gia_ObjFanin0(pObj), f, vRes, Sign );
//            if ( !fSel1 )
                Gla_ManRefSelect_rec( p, Gia_ObjFanin1(pObj), f, vRes, Sign );
        }
        else // select one value
        {
            if ( (pRef0->Value ^ Gia_ObjFaninC0(pObj)) == 0 && (pRef1->Value ^ Gia_ObjFaninC1(pObj)) == 0 )
            {
//                if ( !fSel0 && !fSel1 )
                {
                    if ( pRef0->Prio <= pRef1->Prio ) // choice
                        Gla_ManRefSelect_rec( p, Gia_ObjFanin0(pObj), f, vRes, Sign );
                    else
                        Gla_ManRefSelect_rec( p, Gia_ObjFanin1(pObj), f, vRes, Sign );
                }
            }
            else if ( (pRef0->Value ^ Gia_ObjFaninC0(pObj)) == 0 )
            {
//                if ( !fSel0 )
                    Gla_ManRefSelect_rec( p, Gia_ObjFanin0(pObj), f, vRes, Sign );
            }
            else if ( (pRef1->Value ^ Gia_ObjFaninC1(pObj)) == 0 )
            {
//                if ( !fSel1 )
                    Gla_ManRefSelect_rec( p, Gia_ObjFanin1(pObj), f, vRes, Sign );
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
Vec_Int_t * Gla_ManRefinement( Gla_Man_t * p )
{
    int fVerify = 1;
    static int Sign = 0;
    Vec_Int_t * vPis, * vPPis, * vCos, * vRoAnds, * vRes = NULL;
    Rfn_Obj_t * pRef, * pRef0, * pRef1;
    Gia_Obj_t * pObj;
//    Gla_Obj_t * pGla;
    int i, f;
    Sign++;

    // compute PIs and pseudo-PIs
    vCos = Vec_IntAlloc( 1000 );
    vPis = Vec_IntAlloc( 1000 );  
    vPPis = Vec_IntAlloc( 1000 );
    vRoAnds = Vec_IntAlloc( 1000 );  
    Gla_ManCollect( p, vPis, vPPis, vCos, vRoAnds );
/*
    // check how many pseudo PIs have variables
    Gla_ManForEachObjAbsVec( vPis, p, pGla, i )
    {
        printf( "  %5d : ", Gla_ObjId(p, pGla) );
        for ( f = 0; f <= p->pPars->iFrame; f++ )
            printf( "%d", Gla_ManCheckVar(p, Gla_ObjId(p, pGla), f) );
        printf( "\n" );
    }    

    // check how many pseudo PIs have variables
    Gla_ManForEachObjAbsVec( vPPis, p, pGla, i )
    {
        printf( "%5d : ", Gla_ObjId(p, pGla) );
        for ( f = 0; f <= p->pPars->iFrame; f++ )
            printf( "%d", Gla_ManCheckVar(p, Gla_ObjId(p, pGla), f) );
        printf( "\n" );
    }    
*/
    // propagate values
    for ( f = 0; f <= p->pPars->iFrame; f++ )
    {
        // constant
        pRef = Gla_ObjRef( p, 0, f );  Gla_ObjClearRef( pRef );
        pRef->Value  = 0;
        pRef->Prio   = 0;
        pRef->Sign   = Sign;
        // primary input
        Gia_ManForEachObjVec( vPis, p->pGia, pObj, i )
        {
            assert( f == p->pPars->iFrame || Gla_ManCheckVar(p, p->pObj2Obj[Gia_ObjId(p->pGia, pObj)], f) );
            pRef = Gla_ObjRef( p, Gia_ObjId(p->pGia, pObj), f );   Gla_ObjClearRef( pRef );
            pRef->Value = Gla_ObjSatValue( p, Gia_ObjId(p->pGia, pObj), f );
            pRef->Prio = 0;
            pRef->Sign = Sign;
            assert( pRef->fVisit == 0 );
        }
        // primary input
        Gia_ManForEachObjVec( vPPis, p->pGia, pObj, i )
        {
            int ObjId = Gia_ObjId(p->pGia, pObj);
            if ( 1308 == Gia_ObjId(p->pGia, pObj) )
            {
                int s = 0;
            }
            assert( f == p->pPars->iFrame || Gla_ManCheckVar(p, p->pObj2Obj[Gia_ObjId(p->pGia, pObj)], f) );
            assert( Gia_ObjIsAnd(pObj) || Gia_ObjIsRo(p->pGia, pObj) );
            pRef = Gla_ObjRef( p, Gia_ObjId(p->pGia, pObj), f );   Gla_ObjClearRef( pRef );
            pRef->Value = Gla_ObjSatValue( p, Gia_ObjId(p->pGia, pObj), f );
            pRef->Prio  = i+1;
            pRef->fPPi  = 1;
            pRef->Sign  = Sign;
            assert( pRef->fVisit == 0 );
        }

        // internal nodes
        Gia_ManForEachObjVec( vRoAnds, p->pGia, pObj, i )
        {
            if ( 1598 == Gia_ObjId(p->pGia, pObj) )
            {
                int s = 0;
            }
            assert( Gia_ObjIsAnd(pObj) || Gia_ObjIsRo(p->pGia, pObj) );
            pRef = Gla_ObjRef( p, Gia_ObjId(p->pGia, pObj), f );   Gla_ObjClearRef( pRef );
            if ( Gia_ObjIsRo(p->pGia, pObj) )
            {
                if ( f == 0 )
                {
                    pRef->Value = 0;
                    pRef->Prio  = 0;
                    pRef->Sign  = Sign;
                }
                else
                {
                    pRef0 = Gla_ObjRef( p, Gia_ObjId(p->pGia, Gia_ObjRoToRi(p->pGia, pObj)), f-1 );
                    pRef->Value = pRef0->Value;
                    pRef->Prio  = pRef0->Prio;
                    pRef->Sign  = Sign;

                    if ( (int)pRef->Value != Gla_ObjSatValue( p, Gia_ObjId(p->pGia, pObj), f ) )
                    {
                        Gla_Obj_t * pGla = Gla_ManObj(p, p->pObj2Obj[Gia_ObjId(p->pGia, Gia_ObjRoToRi(p->pGia, pObj))]);
                        int s = 0;
                    }

                }
                continue;
            }
            assert( Gia_ObjIsAnd(pObj) );
            pRef0 = Gla_ObjRef( p, Gia_ObjFaninId0p(p->pGia, pObj), f );
            pRef1 = Gla_ObjRef( p, Gia_ObjFaninId1p(p->pGia, pObj), f );
            pRef->Value = (pRef0->Value ^ Gia_ObjFaninC0(pObj)) & (pRef1->Value ^ Gia_ObjFaninC1(pObj));

            if ( p->pObj2Obj[Gia_ObjId(p->pGia, pObj)] != ~0 && Gla_ManCheckVar(p, p->pObj2Obj[Gia_ObjId(p->pGia, pObj)], f) )
            {
                Gia_Obj_t * pFan0 = Gia_ObjFanin0(pObj);
                Gia_Obj_t * pFan1 = Gia_ObjFanin1(pObj);
                int iff = Gia_ObjId(p->pGia, pFan1);

//                assert( (int)pRef->Value == Gla_ObjSatValue( p, Gia_ObjId(p->pGia, pObj), f ) );
                if ( (int)pRef->Value != Gla_ObjSatValue( p, Gia_ObjId(p->pGia, pObj), f ) )
                {
                    Gia_Obj_t * pFanin0 = Gia_ObjFanin0(pObj);
                    Gia_Obj_t * pFanin1 = Gia_ObjFanin1(pObj);

                    int id = Gia_ObjId(p->pGia, pObj);

                    int v  = p->pObj2Obj[Gia_ObjId(p->pGia, pObj)];
                    int v1 = p->pObj2Obj[Gia_ObjId(p->pGia, Gia_ObjFanin0(pObj))];
                    int v2 = p->pObj2Obj[Gia_ObjId(p->pGia, Gia_ObjFanin1(pObj))];

                    int c  = Gla_ManCheckVar(p, p->pObj2Obj[Gia_ObjId(p->pGia, pObj)], f);
//                    int c1 = Gla_ManCheckVar(p, p->pObj2Obj[Gia_ObjId(p->pGia, Gia_ObjFanin0(pObj))], f);
//                    int c2 = Gla_ManCheckVar(p, p->pObj2Obj[Gia_ObjId(p->pGia, Gia_ObjFanin1(pObj))], f);

                    int Value  = Gla_ObjSatValue( p, Gia_ObjId(p->pGia, pObj)               , f );
//                    int Value1 = Gla_ObjSatValue( p, Gia_ObjId(p->pGia, Gia_ObjFanin0(pObj)), f );
//                    int Value2 = Gla_ObjSatValue( p, Gia_ObjId(p->pGia, Gia_ObjFanin1(pObj)), f );

                    Gla_Obj_t * pGla= Gla_ManObj( p, v );
                    Gla_Obj_t * pFanin;
                    int j;
                    Gla_ObjForEachFanin( p, pGla, pFanin, j )
                    {
                        Rfn_Obj_t * pRef3 = Gla_ObjRef( p, pFanin->iGiaObj, f );
                        int c  = Gla_ManCheckVar(p, p->pObj2Obj[pFanin->iGiaObj], f);

                        Gia_ObjPrint( p->pGia, Gia_ManObj(p->pGia, pFanin->iGiaObj) );

                        if ( (int)pRef3->Value != Gla_ObjSatValue( p, pFanin->iGiaObj, f ) )
                        {
                            int s = 0;
                        }
                    }

                    printf( "Object has value mismatch    " );
                    Gia_ObjPrint( p->pGia, pObj );
                }
            }

            if ( pRef->Value == 1 )
                pRef->Prio  = Abc_MaxInt( pRef0->Prio, pRef1->Prio );
            else if ( (pRef0->Value ^ Gia_ObjFaninC0(pObj)) == 0 && (pRef1->Value ^ Gia_ObjFaninC1(pObj)) == 0 )
                pRef->Prio  = Abc_MinInt( pRef0->Prio, pRef1->Prio ); // choice
            else if ( (pRef0->Value ^ Gia_ObjFaninC0(pObj)) == 0 )
                pRef->Prio  = pRef0->Prio;
            else 
                pRef->Prio  = pRef1->Prio;
            assert( pRef->fVisit == 0 );
            pRef->Sign  = Sign;
        }
        // output nodes
        Gia_ManForEachObjVec( vCos, p->pGia, pObj, i )
        {
            pRef = Gla_ObjRef( p, Gia_ObjId(p->pGia, pObj), f );    Gla_ObjClearRef( pRef );
            pRef0 = Gla_ObjRef( p, Gia_ObjFaninId0p(p->pGia, pObj), f ); 
            pRef->Value = (pRef0->Value ^ Gia_ObjFaninC0(pObj));
            pRef->Prio  = pRef0->Prio;
            assert( pRef->fVisit == 0 );
            pRef->Sign  = Sign;
        }
    }
    // make sure the output value is 1
    pObj = Gia_ManPo( p->pGia, 0 );
    pRef = Gla_ObjRef( p, Gia_ObjId(p->pGia, pObj), p->pPars->iFrame );
    assert( pRef->Value == 1 );

    // check the CEX
    if ( pRef->Prio == 0 )
    {
        p->pGia->pCexSeq = Gla_ManDeriveCex( p, vPis );
        Vec_IntFree( vPis );
        Vec_IntFree( vPPis );
        Vec_IntFree( vRoAnds );
        Vec_IntFree( vCos );
        return 0;
    }

    // select objects
    vRes = Vec_IntAlloc( 100 );
    Vec_IntFill( p->vPrioSels, Vec_IntSize(vPPis)+1, 0 );
    Gla_ManRefSelect_rec( p, Gia_ObjFanin0(Gia_ManPo(p->pGia, 0)), p->pPars->iFrame, vRes, Sign );

    if ( fVerify )
    {
        Gia_ManForEachObj( p->pGia, pObj, i )
            assert( Gia_ObjTerSimGetC(pObj) );
        for ( f = 0; f <= p->pPars->iFrame; f++ )
        {
            Gia_ObjTerSimSet0( Gia_ManConst0(p->pGia) );
            Gia_ManForEachObjVec( vPis, p->pGia, pObj, i )
            {
                if ( Gla_ObjSatValue( p, Gia_ObjId(p->pGia, pObj), f ) )
                    Gia_ObjTerSimSet1( pObj );
                else
                    Gia_ObjTerSimSet0( pObj );
            }
            Gia_ManForEachObjVec( vPPis, p->pGia, pObj, i )
            {
                if ( Vec_IntEntry(p->vPrioSels, i+1) == 0 ) // not selected
                    Gia_ObjTerSimSetX( pObj );
                else if ( Gla_ObjSatValue( p, Gia_ObjId(p->pGia, pObj), f ) )
                    Gia_ObjTerSimSet1( pObj );
                else
                    Gia_ObjTerSimSet0( pObj );
            }
            Gia_ManForEachObjVec( vRoAnds, p->pGia, pObj, i )
            {
                if ( Gia_ObjIsAnd(pObj) )
                    Gia_ObjTerSimAnd( pObj );
                else if ( f == 0 )
                    Gia_ObjTerSimSet0( pObj );
                else
                    Gia_ObjTerSimRo( p->pGia, pObj );
            }
            Gia_ManForEachObjVec( vCos, p->pGia, pObj, i )
                Gia_ObjTerSimCo( pObj );
        }
        pObj = Gia_ManPo( p->pGia, 0 );
        if ( !Gia_ObjTerSimGet1(pObj) )
            printf( "Refinement verification has failed!!!\n" );
        // clear
        Gia_ObjTerSimSetC( Gia_ManConst0(p->pGia) );
        Gia_ManForEachObjVec( vPis, p->pGia, pObj, i )
            Gia_ObjTerSimSetC( pObj );
        Gia_ManForEachObjVec( vPPis, p->pGia, pObj, i )
            Gia_ObjTerSimSetC( pObj );
        Gia_ManForEachObjVec( vRoAnds, p->pGia, pObj, i )
            Gia_ObjTerSimSetC( pObj );
        Gia_ManForEachObjVec( vCos, p->pGia, pObj, i )
            Gia_ObjTerSimSetC( pObj );
    }

    // remap them into GLA objects
    Gia_ManForEachObjVec( vRes, p->pGia, pObj, i )
        Vec_IntWriteEntry( vRes, i, p->pObj2Obj[Gia_ObjId(p->pGia, pObj)] );

    Vec_IntFree( vPis );
    Vec_IntFree( vPPis );
    Vec_IntFree( vRoAnds );
    Vec_IntFree( vCos );
    return vRes;
}





/**Function*************************************************************

  Synopsis    [Selects items that are new in the current abstraction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gla_ManRegionStart( Gla_Man_t * p, Vec_Int_t * vCore )
{
    Vec_Int_t * vRes;
    Gla_Obj_t * pGla;
    int i;
    vRes = Vec_IntAlloc( 100 );
    Gla_ManForEachObjAbsVec( vCore, p, pGla, i )
        if ( !pGla->fAbs )
            Vec_IntPush( vRes, Gla_ObjId(p, pGla) );
    return vRes;
}

/**Function*************************************************************

  Synopsis    [Finds adjacent to previous core among select (or all if NULL).]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gla_ManRegionFilter( Gla_Man_t * p, Vec_Int_t * vSelected, Vec_Int_t * vPrevCore )
{
    Vec_Int_t * vRes;
    Gla_Obj_t * pGla, * pFanin;
    int i, k;
    // mark fanins of previous core
    Gla_ManForEachObjAbsVec( vPrevCore, p, pGla, i )
    {
        assert( pGla->fMark == 0 );
        Gla_ObjForEachFanin( p, pGla, pFanin, k )
            pFanin->fMark = 1;
    }
    // select those not marked and included in the abstraction
    vRes = Vec_IntAlloc( 100 );
    if ( vSelected == NULL )
    {
        Gla_ManForEachObj( p, pGla )
            if ( !pGla->fAbs && pGla->fMark )
                Vec_IntPush( vRes, Gla_ObjId(p, pGla) );
    }
    else
    {
        Gla_ManForEachObjAbsVec( vSelected, p, pGla, i )
            if ( !pGla->fAbs && pGla->fMark )
                Vec_IntPush( vRes, Gla_ObjId(p, pGla) );
    }
    // unmark fanins of previous core
    Gla_ManForEachObjAbsVec( vPrevCore, p, pGla, i )
        Gla_ObjForEachFanin( p, pGla, pFanin, k )
            pFanin->fMark = 0;
    return vRes;
}



/**Function*************************************************************

  Synopsis    [Adds clauses for the given obj in the given frame.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gla_ManCollectFanins( Gla_Man_t * p, Gla_Obj_t * pGla, int iObj, Vec_Int_t * vFanins )
{
    int i, nClauses, iFirstClause, * pLit;
    nClauses = p->pCnf->pObj2Count[pGla->iGiaObj];
    iFirstClause = p->pCnf->pObj2Clause[pGla->iGiaObj];
    Vec_IntClear( vFanins );
    for ( i = iFirstClause; i < iFirstClause + nClauses; i++ )
        for ( pLit = p->pCnf->pClauses[i]; pLit < p->pCnf->pClauses[i+1]; pLit++ )
            if ( lit_var(*pLit) != iObj )
                Vec_IntPushUnique( vFanins, lit_var(*pLit) );
    assert( Vec_IntSize( vFanins ) <= 4 );
    Vec_IntSort( vFanins, 0 );
}


/**Function*************************************************************

  Synopsis    [Duplicates AIG while decoupling nodes duplicated in the mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManDupMapped_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Gia_Man_t * pNew )
{
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return;
    Gia_ObjSetTravIdCurrent(p, pObj);
    assert( Gia_ObjIsAnd(pObj) );
    Gia_ManDupMapped_rec( p, Gia_ObjFanin0(pObj), pNew );
    Gia_ManDupMapped_rec( p, Gia_ObjFanin1(pObj), pNew );
    pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Vec_IntPush( pNew->vLutConfigs, Gia_ObjId(p, pObj) );
}
Gia_Man_t * Gia_ManDupMapped( Gia_Man_t * p, Vec_Int_t * vMapping )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj, * pFanin;
    int i, k, * pMapping, * pObj2Obj;
    // start new manager
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    // start mapping
    Gia_ManFillValue( p );
    pObj2Obj = ABC_FALLOC( int, Gia_ManObjNum(p) );
    pObj2Obj[0] = 0;
    // create reverse mapping and attach it to the node
    pNew->vLutConfigs = Vec_IntAlloc( Gia_ManObjNum(p) * 4 / 3 );
    Vec_IntPush( pNew->vLutConfigs, 0 );
    Gia_ManForEachObj1( p, pObj, i )
    {
        if ( Gia_ObjIsAnd(pObj) )
        {
            int Offset = Vec_IntEntry(vMapping, Gia_ObjId(p, pObj));
            if ( Offset == 0 )
                continue;
            pMapping = Vec_IntEntryP( vMapping, Offset );
            Gia_ManIncrementTravId( p );
            for ( k = 1; k <= 4; k++ )
            {
                if ( pMapping[k] == -1 )
                    continue;
                pFanin = Gia_ManObj(p, pMapping[k]);
                Gia_ObjSetTravIdCurrent( p, pFanin );
                pFanin->Value = pObj2Obj[pMapping[k]];
                assert( ~pFanin->Value );
            }
            assert( !Gia_ObjIsTravIdCurrent(p, pObj) );
            assert( !~pObj->Value );
            Gia_ManDupMapped_rec( p, pObj, pNew );
            pObj2Obj[i] = pObj->Value;
            assert( ~pObj->Value );
        }
        else if ( Gia_ObjIsCi(pObj) )
        {
            pObj2Obj[i] = Gia_ManAppendCi( pNew );
            Vec_IntPush( pNew->vLutConfigs, i );
        }
        else if ( Gia_ObjIsCo(pObj) )
        {
            Gia_ObjFanin0(pObj)->Value = pObj2Obj[Gia_ObjFaninId0p(p, pObj)];
            assert( Gia_ObjFanin0(pObj)->Value >= 0 );
            pObj2Obj[i] = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
            Vec_IntPush( pNew->vLutConfigs, i );
        }
    }
    assert( Vec_IntSize(pNew->vLutConfigs) == Gia_ManObjNum(pNew) );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    // map original AIG into the new AIG
    Gia_ManForEachObj( p, pObj, i )
        pObj->Value = pObj2Obj[i];
    ABC_FREE( pObj2Obj );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Creates a new manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gla_Man_t * Gla_ManStart2( Gia_Man_t * pGia0, Gia_ParVta_t * pPars )
{
    Gla_Man_t * p;
    Aig_Man_t * pAig;
    Gia_Obj_t * pObj;
    Gla_Obj_t * pGla;
    Vec_Int_t * vMappingNew;
    int i, * pLits, * pObj2Count, * pObj2Clause;

    // start
    p = ABC_CALLOC( Gla_Man_t, 1 );
    p->pGia0 = pGia0;
    p->pPars = pPars;
    p->vAbs  = Vec_IntAlloc( 100 );
    p->vTemp = Vec_IntAlloc( 100 );
    p->vAddedNew = Vec_IntAlloc( 100 );
    p->vPrioSels = Vec_IntAlloc( 100 );

    // internal data
    pAig = Gia_ManToAigSimple( pGia0 );
    p->pCnf = Cnf_DeriveOther( pAig );
    Aig_ManStop( pAig );

    // create working GIA
    p->pGia = Gia_ManDupMapped( pGia0, p->pCnf->vMapping );
//printf( "Old GIA = %d.  New GIA = %d.\n", Gia_ManObjNum(pGia0), Gia_ManObjNum(p->pGia) );

    // derive new gate map
    assert( pGia0->vGateClasses != 0 );
    p->pGia->vGateClasses = Vec_IntStart( Gia_ManObjNum(p->pGia) );
    // update p->pCnf->vMapping, p->pCnf->pObj2Count, p->pCnf->pObj2Clause 
    vMappingNew = Vec_IntStart( Gia_ManObjNum(p->pGia) );
    pObj2Count  = ABC_ALLOC( int, Gia_ManObjNum(p->pGia) );
    pObj2Clause = ABC_ALLOC( int, Gia_ManObjNum(p->pGia) );
    Gia_ManForEachObj( pGia0, pObj, i )
    {
        if ( !~pObj->Value )
            continue;
        // replace positive literal by variable
        assert( !Abc_LitIsCompl(pObj->Value) );
        pObj->Value = Abc_Lit2Var(pObj->Value);
        assert( (int)pObj->Value < Gia_ManObjNum(p->pGia) );
        // update mappings
        Vec_IntWriteEntry( vMappingNew, pObj->Value, Vec_IntEntry(p->pCnf->vMapping, i) );
        pObj2Count[pObj->Value] = p->pCnf->pObj2Count[i];
        pObj2Clause[pObj->Value] = p->pCnf->pObj2Clause[i];
        if ( Vec_IntEntry(pGia0->vGateClasses, i) )
            Vec_IntWriteEntry( p->pGia->vGateClasses, pObj->Value, 1 );
    }
    Vec_IntFree( p->pCnf->vMapping );  p->pCnf->vMapping    = vMappingNew;
    ABC_FREE( p->pCnf->pObj2Count );   p->pCnf->pObj2Count  = pObj2Count;
    ABC_FREE( p->pCnf->pObj2Clause );  p->pCnf->pObj2Clause = pObj2Clause;


    // count the number of variables
    p->nObjs = 1;
    Gia_ManForEachObj( p->pGia, pObj, i )
        if ( p->pCnf->pObj2Count[i] >= 0 )
            pObj->Value = p->nObjs++;
        else
            pObj->Value = ~0;

    // re-express CNF using new variable IDs
    pLits = p->pCnf->pClauses[0];
    for ( i = 0; i < p->pCnf->nLiterals; i++ )
    {
        // find the original AIG object
        pObj = Gia_ManObj( pGia0, lit_var(pLits[i]) );
        assert( ~pObj->Value );
        // find the working AIG object
        pObj = Gia_ManObj( p->pGia, pObj->Value );
        assert( ~pObj->Value );
        // express literal in terms of LUT variables
        pLits[i] = toLitCond( pObj->Value, lit_sign(pLits[i]) );
    }

    // create objects 
    p->pObjs    = ABC_CALLOC( Gla_Obj_t, p->nObjs );
    p->pObj2Obj = ABC_FALLOC( unsigned, Gia_ManObjNum(p->pGia) );
    p->pvRefis  = ABC_CALLOC( Vec_Int_t, Gia_ManObjNum(p->pGia) );
    Gia_ManForEachObj( p->pGia, pObj, i )
    {
        p->pObj2Obj[i] = pObj->Value;
        if ( !~pObj->Value )
            continue;
        pGla = Gla_ManObj( p, pObj->Value );
        pGla->iGiaObj = i;
        pGla->fCompl0 = Gia_ObjFaninC0(pObj);
        pGla->fConst  = Gia_ObjIsConst0(pObj);
        pGla->fPi     = Gia_ObjIsPi(p->pGia, pObj);
        pGla->fPo     = Gia_ObjIsPo(p->pGia, pObj);
        pGla->fRi     = Gia_ObjIsRi(p->pGia, pObj);
        pGla->fRo     = Gia_ObjIsRo(p->pGia, pObj);
        pGla->fAnd    = Gia_ObjIsAnd(pObj);
        if ( Gia_ObjIsConst0(pObj) || Gia_ObjIsPi(p->pGia, pObj) )
            continue;
        if ( Gia_ObjIsAnd(pObj) || Gia_ObjIsCo(pObj) )
        {
            Gla_ManCollectFanins( p, pGla, pObj->Value, p->vTemp );
            pGla->nFanins = Vec_IntSize( p->vTemp );
            memcpy( pGla->Fanins, Vec_IntArray(p->vTemp), sizeof(int) * Vec_IntSize(p->vTemp) );
            continue;
        }
        assert( Gia_ObjIsRo(p->pGia, pObj) );
        pGla->nFanins   = 1;
        pGla->Fanins[0] = Gia_ObjFanin0( Gia_ObjRoToRi(p->pGia, pObj) )->Value;
        pGla->fCompl0   = Gia_ObjFaninC0( Gia_ObjRoToRi(p->pGia, pObj) );
    }
    p->pObjRoot = Gla_ManObj( p, Gia_ManPo(p->pGia, 0)->Value );
    // abstraction 
    assert( p->pGia->vGateClasses != NULL );
    Gla_ManForEachObj( p, pGla )
    {
        if ( Vec_IntEntry( p->pGia->vGateClasses, pGla->iGiaObj ) == 0 )
            continue;
        pGla->fAbs = 1;
        Vec_IntPush( p->vAbs, Gla_ObjId(p, pGla) );
    }
    // other 
    p->vCla2Obj  = Vec_IntAlloc( 1000 );  Vec_IntPush( p->vCla2Obj, -1 );
    p->pSat      = sat_solver2_new();
    p->nSatVars  = 1;
    return p;
}

/**Function*************************************************************

  Synopsis    [Creates a new manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gla_Man_t * Gla_ManStart( Gia_Man_t * pGia, Gia_ParVta_t * pPars )
{
    Gla_Man_t * p;
    Aig_Man_t * pAig;
    Gia_Obj_t * pObj;
    Gla_Obj_t * pGla;
    int i, * pLits;
    // start
    p = ABC_CALLOC( Gla_Man_t, 1 );
    p->pGia  = pGia;
    p->pPars = pPars;
    p->vAbs = Vec_IntAlloc( 100 );
    p->vTemp = Vec_IntAlloc( 100 );
    p->vAddedNew = Vec_IntAlloc( 100 );
    p->vPrioSels = Vec_IntAlloc( 100 );
    // internal data
    pAig = Gia_ManToAigSimple( p->pGia );
    p->pCnf  = Cnf_DeriveOther( pAig );
    Aig_ManStop( pAig );
    // count the number of variables
    p->nObjs = 1;
    Gia_ManForEachObj( p->pGia, pObj, i )
        if ( p->pCnf->pObj2Count[i] >= 0 )
            pObj->Value = p->nObjs++;
        else
            pObj->Value = ~0;
    // re-express CNF using new variable IDs
    pLits = p->pCnf->pClauses[0];
    for ( i = 0; i < p->pCnf->nLiterals; i++ )
    {
        pObj = Gia_ManObj( p->pGia, lit_var(pLits[i]) );
        assert( ~pObj->Value );
        pLits[i] = toLitCond( pObj->Value, lit_sign(pLits[i]) );
    }
    // create objects 
    p->pObjs    = ABC_CALLOC( Gla_Obj_t, p->nObjs );
    p->pObj2Obj = ABC_FALLOC( unsigned, Gia_ManObjNum(p->pGia) );
    p->pvRefis  = ABC_CALLOC( Vec_Int_t, Gia_ManObjNum(p->pGia) );
    Gia_ManForEachObj( p->pGia, pObj, i )
    {
        p->pObj2Obj[i] = pObj->Value;
        if ( !~pObj->Value )
            continue;
        pGla = Gla_ManObj( p, pObj->Value );
        pGla->iGiaObj = i;
        pGla->fCompl0 = Gia_ObjFaninC0(pObj);
        pGla->fConst  = Gia_ObjIsConst0(pObj);
        pGla->fPi     = Gia_ObjIsPi(p->pGia, pObj);
        pGla->fPo     = Gia_ObjIsPo(p->pGia, pObj);
        pGla->fRi     = Gia_ObjIsRi(p->pGia, pObj);
        pGla->fRo     = Gia_ObjIsRo(p->pGia, pObj);
        pGla->fAnd    = Gia_ObjIsAnd(pObj);
        if ( Gia_ObjIsConst0(pObj) || Gia_ObjIsPi(p->pGia, pObj) )
            continue;
        if ( Gia_ObjIsAnd(pObj) || Gia_ObjIsCo(pObj) )
        {
            Gla_ManCollectFanins( p, pGla, pObj->Value, p->vTemp );
            pGla->nFanins = Vec_IntSize( p->vTemp );
            memcpy( pGla->Fanins, Vec_IntArray(p->vTemp), sizeof(int) * Vec_IntSize(p->vTemp) );
            continue;
        }
        assert( Gia_ObjIsRo(p->pGia, pObj) );
        pGla->nFanins   = 1;
        pGla->Fanins[0] = Gia_ObjFanin0( Gia_ObjRoToRi(p->pGia, pObj) )->Value;
        pGla->fCompl0   = Gia_ObjFaninC0( Gia_ObjRoToRi(p->pGia, pObj) );
    }
    p->pObjRoot = Gla_ManObj( p, Gia_ManPo(p->pGia, 0)->Value );
    // abstraction 
    assert( pGia->vGateClasses != NULL );
    Gla_ManForEachObj( p, pGla )
    {
        if ( Vec_IntEntry( pGia->vGateClasses, pGla->iGiaObj ) == 0 )
            continue;
        pGla->fAbs = 1;
        Vec_IntPush( p->vAbs, Gla_ObjId(p, pGla) );
    }
    // other 
    p->vCla2Obj  = Vec_IntAlloc( 1000 );  Vec_IntPush( p->vCla2Obj, -1 );
    p->pSat      = sat_solver2_new();
    p->nSatVars  = 1;
    return p;
}

/**Function*************************************************************

  Synopsis    [Creates a new manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gla_ManStop( Gla_Man_t * p )
{
    Gla_Obj_t * pGla;
//    if ( p->pPars->fVerbose )
        Abc_Print( 1, "SAT solver:  Variables = %d. Clauses = %d. Conflicts = %d. Cexes = %d.\n", 
            sat_solver2_nvars(p->pSat), sat_solver2_nclauses(p->pSat), sat_solver2_nconflicts(p->pSat), p->nCexes );
    Gla_ManForEachObj( p, pGla )
        ABC_FREE( pGla->vFrames.pArray );
    Cnf_DataFree( p->pCnf );
    if ( p->pGia0 != NULL )
        Gia_ManStop( p->pGia );
    sat_solver2_delete( p->pSat );
    Vec_IntFreeP( &p->vCla2Obj );
    Vec_IntFreeP( &p->vPrevCore );
    Vec_IntFreeP( &p->vAddedNew );
    Vec_IntFreeP( &p->vPrioSels );
    Vec_IntFreeP( &p->vTemp );
    Vec_IntFreeP( &p->vAbs );
    ABC_FREE( p->pvRefis );
    ABC_FREE( p->pObj2Obj );
    ABC_FREE( p->pObjs );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Creates a new manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_GlaAbsCount( Gla_Man_t * p, int fRo, int fAnd )
{
    Gla_Obj_t * pObj;
    int i, Counter = 0;
    if ( fRo )
        Gla_ManForEachObjAbs( p, pObj, i )
            Counter += (pObj->fRo && pObj->fAbs);
    else if ( fAnd )
        Gla_ManForEachObjAbs( p, pObj, i )
            Counter += (pObj->fAnd && pObj->fAbs);
    else
        Gla_ManForEachObjAbs( p, pObj, i )
            Counter += (pObj->fAbs);
    return Counter;
}


/**Function*************************************************************

  Synopsis    [Derives new abstraction map.]

  Description [Returns 1 if node contains abstracted leaf on the path.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gla_ManTranslate_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vMap )
{
    int Value0, Value1;
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return 1;
    Gia_ObjSetTravIdCurrent(p, pObj);
    if ( Gia_ObjIsCi(pObj) )
        return 0;
    assert( Gia_ObjIsAnd(pObj) );
    Value0 = Gla_ManTranslate_rec( p, Gia_ObjFanin0(pObj), vMap );
    Value1 = Gla_ManTranslate_rec( p, Gia_ObjFanin1(pObj), vMap );
    if ( Value0 || Value1 )
        Vec_IntWriteEntry( vMap, Gia_ObjId(p, pObj), 1 );
    return Value0 || Value1;
}
Vec_Int_t * Gla_ManTranslate( Gla_Man_t * p )
{
    Vec_Int_t * vRes, * vRes2;
    Gla_Obj_t * pObj, * pFanin;
    Gia_Obj_t * pGiaObj;
    int i, k;
    vRes = Vec_IntStart( Gia_ManObjNum(p->pGia) );
    Gla_ManForEachObjAbs( p, pObj, i )
    {
        Vec_IntWriteEntry( vRes, pObj->iGiaObj, 1 );
        pGiaObj = Gla_ManGiaObj( p, pObj );
        if ( Gia_ObjIsConst0(pGiaObj) || Gia_ObjIsRo(p->pGia, pGiaObj) )
            continue;
        assert( Gia_ObjIsAnd(pGiaObj) );
        Gia_ManIncrementTravId( p->pGia );
        Gla_ObjForEachFanin( p, pObj, pFanin, k )
            Gia_ObjSetTravIdCurrent( p->pGia, Gla_ManGiaObj(p, pFanin) );
        Gla_ManTranslate_rec( p->pGia, pGiaObj, vRes );
    }
    if ( p->pGia->vLutConfigs )
    {
        vRes2 = Vec_IntStart( Gia_ManObjNum(p->pGia0) );
        for ( i = 0; i < Gia_ManObjNum(p->pGia); i++ )
            if ( Vec_IntEntry(vRes, i) )
                Vec_IntWriteEntry( vRes2, Vec_IntEntry(p->pGia->vLutConfigs, i), 1 );
        Vec_IntFree( vRes );
        return vRes2;
    }
    return vRes;
}


/**Function*************************************************************

  Synopsis    [Collect pseudo-PIs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gla_ManCollectPPis( Gla_Man_t * p, Vec_Int_t * vPis )
{
    Vec_Int_t * vPPis;
    Gla_Obj_t * pObj, * pFanin;
    int i, k;
    vPPis = Vec_IntAlloc( 1000 );
    if ( vPis )
        Vec_IntClear( vPis );
    Gla_ManForEachObjAbs( p, pObj, i )
    {
        assert( pObj->fConst || pObj->fRo || pObj->fAnd );
        Gla_ObjForEachFanin( p, pObj, pFanin, k )
            if ( !pFanin->fPi && !pFanin->fAbs )
                Vec_IntPush( vPPis, pObj->Fanins[k] );
            else if ( vPis && pFanin->fPi && !pFanin->fAbs )
                Vec_IntPush( vPis, pObj->Fanins[k] );
    }
    Vec_IntUniqify( vPPis );
    Vec_IntReverseOrder( vPPis );
    if ( vPis )
        Vec_IntUniqify( vPis );
    return vPPis;
}
int Gla_ManCountPPis( Gla_Man_t * p )
{
    Vec_Int_t * vPPis = Gla_ManCollectPPis( p, NULL );
    int RetValue = Vec_IntSize( vPPis );
    Vec_IntFree( vPPis );
    return RetValue;
}


void Gla_ManExplorePPis( Gla_Man_t * p, Vec_Int_t * vPPis )
{
    static int Round = 0;
    Gla_Obj_t * pObj, * pFanin;
    int i, j, k, Count;
    if ( (Round++ % 5) == 0 )
        return;
    j = 0;
    Gla_ManForEachObjAbsVec( vPPis, p, pObj, i )
    {
        assert( pObj->fAbs == 0 );
        Count = 0;
        Gla_ObjForEachFanin( p, pObj, pFanin, k )
            Count += pFanin->fAbs;
        if ( Count == 0 || ((Round & 1) && Count == 1) )
            continue;
        Vec_IntWriteEntry( vPPis, j++, Gla_ObjId(p, pObj) );
    }
//    printf( "\n%d -> %d\n", Vec_IntSize(vPPis), j );
    Vec_IntShrink( vPPis, j );
}

// add those having more than one shared fanin


void Gla_ManExplorePPis2( Gla_Man_t * p, Vec_Int_t * vPPis )
{
    static int Round = 0;
    Vec_Int_t * vTemp;
    Gla_Obj_t * pGla, * pFanin;
    int i, k, Entry, Count;
    if ( p->vPrevCore == NULL )
        return;
    if ( (Round++ % 10) == 0 )
    {
        p->vPrevCore = Gla_ManRegionFilter( p, vPPis, vTemp = p->vPrevCore );
        Vec_IntFree( vTemp );
    }
    else
    {
        p->vPrevCore = Gla_ManRegionFilter( p, NULL, vTemp = p->vPrevCore );
        Vec_IntFree( vTemp );
        // save a copy
        vTemp = Vec_IntDup( vPPis );
        // udpate
        Vec_IntClear( vPPis );
        Vec_IntForEachEntry( p->vPrevCore, Entry, i )
            Vec_IntPush( vPPis, Entry );


        // mark those included as abstracted
        Gla_ManForEachObjAbsVec( vPPis, p, pGla, i )
        {
            assert( pGla->fAbs == 0 );
            pGla->fAbs = 1;
        }
        // add those not included but to close to abstracted
        Gla_ManForEachObjAbsVec( vTemp, p, pGla, i )
        {
            if ( pGla->fAbs )
                continue;
            Count = 0;
            Gla_ObjForEachFanin( p, pGla, pFanin, k )
                Count += pFanin->fAbs;
            if ( Count == 0 || Count == 1 )
                continue;
            Vec_IntPush( vPPis, Gla_ObjId(p, pGla) );
        }
        // unmark those included
        Gla_ManForEachObjAbsVec( vPPis, p, pGla, i )
            pGla->fAbs = 0;


        // cleanup
        Vec_IntFree( vTemp );
    }
}

/*
void Gla_ManExplorePPis2( Gla_Man_t * p, Vec_Int_t * vPPis, int iIter )
{
    Gla_Obj_t * pObj, * pFanin;
    int i, j, k;
    if ( iIter > 10 )
    {
        Gla_ManForEachObj( p, pObj )
            pObj->fMark = 0;
        return;
    }
    j = 0;
    Gla_ManForEachObjAbsVec( vPPis, p, pObj, i )
    {
        assert( pObj->fAbs == 0 );
        if ( pObj->fMark == 0 )
        {
            Gla_ObjForEachFanin( p, pObj, pFanin, k )
                if ( pObj->fMark )
                    break;
            if ( k == (int)pObj->nFanins )
                continue;
        }
        Vec_IntWriteEntry( vPPis, j++, Gla_ObjId(p, pObj) );
    }
//    printf( "\n%d -> %d\n", Vec_IntSize(vPPis), j );
    Vec_IntShrink( vPPis, j );

    // update
    Gla_ManForEachObj( p, pObj )
        pObj->fMark = 0;
    Gla_ManForEachObjAbsVec( vPPis, p, pObj, i )
        Gla_ObjForEachFanin( p, pObj, pFanin, k )
            pFanin->fMark = 1;
}
*/


/**Function*************************************************************

  Synopsis    [Adds CNF for the given timeframe.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gla_ManCheckVar( Gla_Man_t * p, int iObj, int iFrame )
{
    Gla_Obj_t * pGla = Gla_ManObj( p, iObj );
    int iVar = Vec_IntGetEntry( &pGla->vFrames, iFrame );
    assert( !pGla->fPo && !pGla->fRi );
    return (iVar > 0);
}
int Gla_ManGetVar( Gla_Man_t * p, int iObj, int iFrame )
{
    Gla_Obj_t * pGla = Gla_ManObj( p, iObj );
    int iVar = Vec_IntGetEntry( &pGla->vFrames, iFrame );
    assert( !pGla->fPo && !pGla->fRi );
    if ( iVar == 0 )
    {
        Vec_IntSetEntry( &pGla->vFrames, iFrame, (iVar = p->nSatVars++) );
        // remember the change
        Vec_IntPush( p->vAddedNew, iObj );
        Vec_IntPush( p->vAddedNew, iFrame );
    }
    return iVar;
}
void Gla_ManAddClauses( Gla_Man_t * p, int iObj, int iFrame, Vec_Int_t * vLits )
{
    Gla_Obj_t * pGlaObj = Gla_ManObj( p, iObj );
    int iVar, iVar1, iVar2;
    if ( 4786 == iObj && iFrame == 2 )
    {
        int s = 0;
    }
    if ( pGlaObj->fConst )
    {
        iVar = Gla_ManGetVar( p, iObj, iFrame );
        sat_solver2_add_const( p->pSat, iVar, 1, 0 );
        // remember the clause
        Vec_IntPush( p->vCla2Obj, iObj );
    }
    else if ( pGlaObj->fRo )
    {
        assert( pGlaObj->nFanins == 1 );
        if ( iFrame == 0 )
        {
            iVar = Gla_ManGetVar( p, iObj, iFrame );
            sat_solver2_add_const( p->pSat, iVar, 1, 0 );
            // remember the clause
            Vec_IntPush( p->vCla2Obj, iObj );
        }
        else
        {
            iVar1 = Gla_ManGetVar( p, iObj, iFrame );
            iVar2 = Gla_ManGetVar( p, pGlaObj->Fanins[0], iFrame-1 );
            sat_solver2_add_buffer( p->pSat, iVar1, iVar2, pGlaObj->fCompl0, 0 );
            // remember the clause
            Vec_IntPush( p->vCla2Obj, iObj );
            Vec_IntPush( p->vCla2Obj, iObj );
        }
    }
    else if ( pGlaObj->fAnd )
    {
        int i, RetValue, nClauses, iFirstClause, * pLit;
        nClauses = p->pCnf->pObj2Count[pGlaObj->iGiaObj];
        iFirstClause = p->pCnf->pObj2Clause[pGlaObj->iGiaObj];
        for ( i = iFirstClause; i < iFirstClause + nClauses; i++ )
        {
            Vec_IntClear( vLits );
            for ( pLit = p->pCnf->pClauses[i]; pLit < p->pCnf->pClauses[i+1]; pLit++ )
            {
                iVar = Gla_ManGetVar( p, lit_var(*pLit), iFrame );
                Vec_IntPush( vLits, toLitCond( iVar, lit_sign(*pLit) ) );
            }
            RetValue = sat_solver2_addclause( p->pSat, Vec_IntArray(vLits), Vec_IntArray(vLits)+Vec_IntSize(vLits) );
            assert( RetValue );
            // remember the clause
            Vec_IntPush( p->vCla2Obj, iObj );
        }
    }
    else assert( 0 );
}
void Gia_GlaAddToAbs( Gla_Man_t * p, Vec_Int_t * vAbsAdd, int fCheck )
{
    Gla_Obj_t * pGla;
    int i;
    Gla_ManForEachObjAbsVec( vAbsAdd, p, pGla, i )
    {
        assert( !fCheck || pGla->fAbs == 0 );
        if ( pGla->fAbs )
            continue;
        pGla->fAbs = 1;
        Vec_IntPush( p->vAbs, Gla_ObjId(p, pGla) );
    }
}
void Gia_GlaAddTimeFrame( Gla_Man_t * p, int f )
{
    Gla_Obj_t * pObj;
    int i;
    Gla_ManForEachObjAbs( p, pObj, i )
        Gla_ManAddClauses( p, Gla_ObjId(p, pObj), f, p->vTemp );
    sat_solver2_simplify( p->pSat );
}
void Gia_GlaAddOneSlice( Gla_Man_t * p, int fCur, Vec_Int_t * vCore )
{
    int f, i, iGlaObj;
    for ( f = fCur; f >= 0; f-- )
        Vec_IntForEachEntry( vCore, iGlaObj, i )
            Gla_ManAddClauses( p, iGlaObj, f, p->vTemp );
    sat_solver2_simplify( p->pSat );
}
void Gla_ManRollBack( Gla_Man_t * p )
{
    int i, iObj, iFrame;
    Vec_IntForEachEntryDouble( p->vAddedNew, iObj, iFrame, i )
    {
        assert( Vec_IntEntry( &Gla_ManObj(p, iObj)->vFrames, iFrame ) > 0 );
        Vec_IntWriteEntry( &Gla_ManObj(p, iObj)->vFrames, iFrame, 0 );
    }
    Vec_IntForEachEntryStart( p->vAbs, iObj, i, p->nAbsOld )
    {
        assert( Gla_ManObj( p, iObj )->fAbs == 1 );
        Gla_ManObj( p, iObj )->fAbs = 0;
    }
    Vec_IntShrink( p->vAbs, p->nAbsOld );
}


            


/**Function*************************************************************

  Synopsis    [Finds the set of clauses involved in the UNSAT core.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gla_ManGetOutLit( Gla_Man_t * p, int f )
{
    Gla_Obj_t * pFanin = Gla_ManObj( p, p->pObjRoot->Fanins[0] );
    int iSat = Vec_IntEntry( &pFanin->vFrames, f );
    assert( iSat > 0 );
    if ( f == 0 && pFanin->fRo && !p->pObjRoot->fCompl0 )
        return -1;
    return Abc_Var2Lit( iSat, p->pObjRoot->fCompl0 );
}
Vec_Int_t * Gla_ManUnsatCore( Gla_Man_t * p, int f, Vec_Int_t * vCla2Obj, sat_solver2 * pSat, int nConfMax, int fVerbose, int * piRetValue, int * pnConfls )
{
    Vec_Int_t * vCore;
    int iLit = Gla_ManGetOutLit( p, f );
    int nConfPrev = pSat->stats.conflicts;
    int i, Entry, RetValue, clk = clock();
    if ( piRetValue )
        *piRetValue = 1;
    // consider special case when PO points to the flop
    // this leads to immediate conflict in the first timeframe
    if ( iLit == -1 )
    {
        vCore = Vec_IntAlloc( 1 );
        Vec_IntPush( vCore, p->pObjRoot->Fanins[0] );
        return vCore;
    }
    // solve the problem
    RetValue = sat_solver2_solve( pSat, &iLit, &iLit+1, (ABC_INT64_T)nConfMax, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
    if ( pnConfls )
        *pnConfls = (int)pSat->stats.conflicts - nConfPrev;
    if ( RetValue == l_Undef )
    {
        if ( piRetValue )
            *piRetValue = -1;
        return NULL;
    }
    if ( RetValue == l_True )
    {
        if ( piRetValue )
            *piRetValue = 0;
        return NULL;
    }
    if ( fVerbose )
    {
//        Abc_Print( 1, "%6d", (int)pSat->stats.conflicts - nConfPrev );
//        Abc_Print( 1, "UNSAT after %7d conflicts.      ", pSat->stats.conflicts );
//        Abc_PrintTime( 1, "Time", clock() - clk );
    }
    assert( RetValue == l_False );

    // derive the UNSAT core
    clk = clock();
    vCore = (Vec_Int_t *)Sat_ProofCore( pSat );
    if ( fVerbose )
    {
//        Abc_Print( 1, "Core is %8d clauses (out of %8d).   ", Vec_IntSize(vCore), sat_solver2_nclauses(pSat) );
//        Abc_PrintTime( 1, "Time", clock() - clk );
    }

    // remap core into original objects 
    Vec_IntForEachEntry( vCore, Entry, i )
        Vec_IntWriteEntry( vCore, i, Vec_IntEntry(p->vCla2Obj, Entry) );
    Vec_IntUniqify( vCore );
    Vec_IntReverseOrder( vCore );
    if ( fVerbose )
    {
//        Abc_Print( 1, "Core is %8d vars    (out of %8d).   ", Vec_IntSize(vCore), sat_solver2_nvars(pSat) );
//        Abc_PrintTime( 1, "Time", clock() - clk );
    }
    return vCore;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gla_ManAbsPrintFrame( Gla_Man_t * p, int nCoreSize, int nFrames, int nConfls, int nCexes, int Time )
{
    Abc_Print( 1, "%3d :", nFrames-1 );
    Abc_Print( 1, "%4d", Abc_MinInt(100, 100 * Gia_GlaAbsCount(p, 0, 0) / (p->nObjs - Gia_ManPoNum(p->pGia) + Gia_ManCoNum(p->pGia) + 1)) ); 
    Abc_Print( 1, "%6d", Gia_GlaAbsCount(p, 0, 0) );
    Abc_Print( 1, "%5d", Gla_ManCountPPis(p) );
    Abc_Print( 1, "%5d", Gia_GlaAbsCount(p, 1, 0) );
    Abc_Print( 1, "%6d", Gia_GlaAbsCount(p, 0, 1) );
    Abc_Print( 1, "%8d", nConfls );
    if ( nCexes == 0 )
        Abc_Print( 1, "%5c", '-' ); 
    else
        Abc_Print( 1, "%5d", nCexes ); 
    Abc_Print( 1, " %9d", sat_solver2_nvars(p->pSat) ); 
    Abc_Print( 1, " %6d", nCoreSize > 0 ? nCoreSize : 0 ); 
    Abc_Print( 1, "%9.2f sec", (float)(Time)/(float)(CLOCKS_PER_SEC) );
    Abc_Print( 1, "%s", nCoreSize > 0 ? "\n" : "\r" );
    fflush( stdout );
}
void Gla_ManReportMemory( Gla_Man_t * p )
{
    Gla_Obj_t * pGla;
    int i;
    double memTot = 0;
    double memAig = Gia_ManObjNum(p->pGia) * sizeof(Gia_Obj_t);
    double memSat = sat_solver2_memory( p->pSat );
    double memPro = sat_solver2_memory_proof( p->pSat );
    double memMap = p->nObjs * sizeof(Gla_Obj_t) + Gia_ManObjNum(p->pGia) * sizeof(int);
    double memRef = Gia_ManObjNum(p->pGia) * sizeof(Vec_Int_t) + Vec_IntCap(p->vPrioSels) * sizeof(int);
    double memOth = sizeof(Gla_Man_t);
    for ( pGla = p->pObjs; pGla < p->pObjs + p->nObjs; pGla++ )
        memMap += Vec_IntCap(&pGla->vFrames) * sizeof(int);
    for ( i = 0; i < Gia_ManObjNum(p->pGia); i++ )
        memRef += Vec_IntCap(&p->pvRefis[i]) * sizeof(int);
    memOth += Vec_IntCap(p->vCla2Obj) * sizeof(int);
    memOth += Vec_IntCap(p->vAddedNew) * sizeof(int);
    memOth += (p->vPrevCore ? Vec_IntCap(p->vPrevCore) : 0) * sizeof(int);
    memOth += Vec_IntCap(p->vTemp) * sizeof(int);
    memOth += Vec_IntCap(p->vAbs) * sizeof(int);
    memTot = memAig + memSat + memPro + memMap + memRef + memOth;
    ABC_PRMP( "Memory: AIG   ", memAig, memTot );
    ABC_PRMP( "Memory: SAT   ", memSat, memTot );
    ABC_PRMP( "Memory: Proof ", memPro, memTot );
    ABC_PRMP( "Memory: Map   ", memMap, memTot );
    ABC_PRMP( "Memory: Refine", memRef, memTot );
    ABC_PRMP( "Memory: Other ", memOth, memTot );
    ABC_PRMP( "Memory: TOTAL ", memTot, memTot );
}


/**Function*************************************************************

  Synopsis    [Send abstracted model or send cancel.]

  Description [Counter-example will be sent automatically when &vta terminates.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_GlaDumpAbsracted( Gla_Man_t * p, int fVerbose )
{
    char * pFileName = p->pPars->pFileVabs ? p->pPars->pFileVabs : "glabs.aig";
    Gia_Man_t * pAbs;
    Vec_Int_t * vGateClasses;
    if ( fVerbose )
        Abc_Print( 1, "Dumping abstracted model into file \"%s\"...\n", pFileName );
//    if ( !Abc_FrameIsBridgeMode() )
//        return;
    // create abstraction
    vGateClasses = Gla_ManTranslate( p );
    pAbs = Gia_ManDupAbsGates( p->pGia0, vGateClasses );
    Vec_IntFreeP( &vGateClasses );
    // write into file
    Gia_WriteAiger( pAbs, pFileName, 0, 0 );
    Gia_ManStop( pAbs );
}


/**Function*************************************************************

  Synopsis    [Performs gate-level abstraction]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_GlaPerform( Gia_Man_t * pAig, Gia_ParVta_t * pPars )
{
    extern int Gia_VtaPerformInt( Gia_Man_t * pAig, Gia_ParVta_t * pPars );
    Gla_Man_t * p;
    Vec_Int_t * vCore, * vPPis;
    Abc_Cex_t * pCex = NULL;
    int i, f, nConfls, Status, nCoreSize, RetValue = -1;
    int clk = clock(), clk2;
    // preconditions
    assert( Gia_ManPoNum(pAig) == 1 );
    assert( pPars->nFramesMax == 0 || pPars->nFramesStart <= pPars->nFramesMax );
    // compute intial abstraction
    if ( pAig->vGateClasses == NULL )
    {
        int nFramesMaxOld   = pPars->nFramesMax;
        int nFramesStartOld = pPars->nFramesStart;
        int nTimeOutOld     = pPars->nTimeOut;
        int nDumpOld        = pPars->fDumpVabs;
        pPars->nFramesMax   = pPars->nFramesStart;
        pPars->nFramesStart = Abc_MinInt( pPars->nFramesStart/2 + 1, 3 );
        pPars->nTimeOut     = 20;
        pPars->fDumpVabs    = 0;
        RetValue = Gia_VtaPerformInt( pAig, pPars );
        pPars->nFramesMax   = nFramesMaxOld;
        pPars->nFramesStart = nFramesStartOld;
        pPars->nTimeOut     = nTimeOutOld;
        pPars->fDumpVabs    = nDumpOld;
        // create gate classes
        Vec_IntFreeP( &pAig->vGateClasses );
        if ( pAig->vObjClasses )
            pAig->vGateClasses = Gia_VtaConvertToGla( pAig, pAig->vObjClasses );
        Vec_IntFreeP( &pAig->vObjClasses );
    }
    if ( RetValue == 0 || pAig->vGateClasses == NULL )
        return RetValue;
    // start the manager
    clk = clock();
    p = Gla_ManStart( pAig, pPars );
    p->timeInit = clock() - clk;
    p->pSat->fVerbose = p->pPars->fVerbose;
    sat_solver2_set_learntmax( p->pSat, pPars->nLearntMax );
    // set runtime limit
    if ( p->pPars->nTimeOut )
        sat_solver2_set_runtime_limit( p->pSat, time(NULL) + p->pPars->nTimeOut - 1 );
    // perform initial abstraction
    if ( p->pPars->fVerbose )
    {
        Abc_Print( 1, "Running gate-level abstraction (GLA) with the following parameters:\n" );
        Abc_Print( 1, "FrameStart = %d  FrameMax = %d  Conf = %d  Timeout = %d. RatioMin = %d %%.\n", 
            p->pPars->nFramesStart, p->pPars->nFramesMax, p->pPars->nConfLimit, p->pPars->nTimeOut, pPars->nRatioMin );
        Abc_Print( 1, "Frame   %%   Abs  PPI   FF   AND   Confl  Cex    SatVar   Core     Time\n" );
    }
    for ( f = i = 0; !p->pPars->nFramesMax || f < p->pPars->nFramesMax; f++ )
    {
        int nConflsBeg = sat_solver2_nconflicts(p->pSat);
        p->pPars->iFrame = f;
        // load timeframe
        Gia_GlaAddTimeFrame( p, f );
        // create bookmark to be used for rollback
//            sat_solver2_reducedb( p->pSat );
        sat_solver2_bookmark( p->pSat );
        Vec_IntClear( p->vAddedNew );
        p->nAbsOld = Vec_IntSize( p->vAbs );
//        nClaOld = Vec_IntSize( p->vCla2Obj );
        // iterate as long as there are counter-examples
        for ( i = 0; ; i++ )
        { 
            clk2 = clock();
            vCore = Gla_ManUnsatCore( p, f, p->vCla2Obj, p->pSat, pPars->nConfLimit, pPars->fVerbose, &Status, &nConfls );
            assert( (vCore != NULL) == (Status == 1) );
            if ( Status == -1 ) // resource limit is reached
            {
                Gla_ManRollBack( p );
                goto finish;
            }
            if ( vCore != NULL )
            {
                p->timeUnsat += clock() - clk2;
                break;
            }
            p->timeSat += clock() - clk2;
            assert( Status == 0 );
            p->nCexes++;
            // perform the refinement
            clk2 = clock();
/*
            vPPis = Gla_ManRefinement( p );
            if ( vPPis == NULL )
            {
                pCex = p->pGia->pCexSeq; p->pGia->pCexSeq = NULL;
                break;
            }
*/
            vPPis = Gla_ManCollectPPis( p, NULL );
            Gla_ManExplorePPis( p, vPPis );

            Gia_GlaAddToAbs( p, vPPis, 1 );
            Gia_GlaAddOneSlice( p, f, vPPis );
            Vec_IntFree( vPPis );

            p->timeCex += clock() - clk2;
            if ( pCex != NULL )
            {
                RetValue = 0;
                goto finish;
            }
            // print the result (do not count it towards change)
            if ( p->pPars->fVerbose )
            Gla_ManAbsPrintFrame( p, -1, f+1, sat_solver2_nconflicts(p->pSat)-nConflsBeg, i, clock() - clk );
        }
        assert( Status == 1 );
        // valid core is obtained
        nCoreSize = Vec_IntSize(vCore);
        if ( i == 0 )
            Vec_IntFree( vCore );
        else
        {
            // update the SAT solver
            sat_solver2_rollback( p->pSat );
            // update storage
            Gla_ManRollBack( p );
            Vec_IntShrink( p->vCla2Obj, (int)p->pSat->stats.clauses+1 );
            // load this timeframe
            Vec_IntFreeP( &p->vPrevCore );
            p->vPrevCore = Gla_ManRegionStart( p, vCore );
            Gia_GlaAddToAbs( p, vCore, 0 );
            Gia_GlaAddOneSlice( p, f, vCore );
            Vec_IntFree( vCore );
            // run SAT solver
            clk2 = clock();
            vCore = Gla_ManUnsatCore( p, f, p->vCla2Obj, p->pSat, pPars->nConfLimit, p->pPars->fVerbose, &Status, &nConfls );
            p->timeUnsat += clock() - clk2;
            assert( (vCore != NULL) == (Status == 1) );
            Vec_IntFreeP( &vCore );
            if ( Status == -1 ) // resource limit is reached
                break;
            if ( Status == 0 )
            {
                assert( 0 );
    //            Vta_ManSatVerify( p );
                // make sure, there was no initial abstraction (otherwise, it was invalid)
                assert( pAig->vObjClasses == NULL && f < p->pPars->nFramesStart );
    //            pCex = Vga_ManDeriveCex( p );
                RetValue = 0;
                break;
            }
        }
        // print the result
        if ( p->pPars->fVerbose )
        Gla_ManAbsPrintFrame( p, nCoreSize, f+1, sat_solver2_nconflicts(p->pSat)-nConflsBeg, i, clock() - clk );

        // dump the model
        if ( p->pPars->fDumpVabs && (f & 1) )
        {
            Abc_FrameSetCex( NULL );
            Abc_FrameSetNFrames( f+1 );
            Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "write_status gla.status" );
            Gia_GlaDumpAbsracted( p, pPars->fVerbose );
        }

        // check if the number of objects is below limit
        if ( Gia_GlaAbsCount(p,0,0) >= (p->nObjs - 1) * (100 - pPars->nRatioMin) / 100 )
        {
            Status = -1;
            break;
        }
    }
finish:
    // analize the results
    if ( pCex == NULL )
    {
        if ( pAig->vGateClasses != NULL )
            Abc_Print( 1, "Replacing the old abstraction by a new one.\n" );
        Vec_IntFreeP( &pAig->vGateClasses );
        pAig->vGateClasses = Gla_ManTranslate( p );
        if ( Status == -1 )
        {
            if ( p->pPars->nTimeOut && time(NULL) >= p->pSat->nRuntimeLimit ) 
                Abc_Print( 1, "SAT solver ran out of time at %d sec in frame %d.  ", p->pPars->nTimeOut, f );
            else if ( pPars->nConfLimit && sat_solver2_nconflicts(p->pSat) >= pPars->nConfLimit )
                Abc_Print( 1, "SAT solver ran out of resources at %d conflicts in frame %d.  ", pPars->nConfLimit, f );
            else if ( Gia_GlaAbsCount(p,0,0) >= (p->nObjs - 1) * (100 - pPars->nRatioMin) / 100 )
                Abc_Print( 1, "The ratio of abstracted objects is less than %d %% in frame %d.  ", pPars->nRatioMin, f );
            else
                Abc_Print( 1, "Abstraction stopped for unknown reason in frame %d.  ", f );
        }
        else
            Abc_Print( 1, "SAT solver completed %d frames and produced an abstraction.  ", f );
    }
    else
    {
        ABC_FREE( p->pGia->pCexSeq );
        p->pGia->pCexSeq = pCex;
        if ( !Gia_ManVerifyCex( p->pGia, pCex, 0 ) )
            Abc_Print( 1, "    Gia_GlaPerform(): CEX verification has failed!\n" );
        Abc_Print( 1, "Counter-example detected in frame %d.  ", f );
        p->pPars->iFrame = pCex->iFrame - 1;
    }
    Abc_PrintTime( 1, "Time", clock() - clk );
    p->timeOther = (clock() - clk) - p->timeUnsat - p->timeSat - p->timeCex - p->timeInit;
    ABC_PRTP( "Runtime: Initializing", p->timeInit,   clock() - clk );
    ABC_PRTP( "Runtime: Solver UNSAT", p->timeUnsat,  clock() - clk );
    ABC_PRTP( "Runtime: Solver SAT  ", p->timeSat,    clock() - clk );
    ABC_PRTP( "Runtime: Refinement  ", p->timeCex,    clock() - clk );
    ABC_PRTP( "Runtime: Other       ", p->timeOther,  clock() - clk );
    ABC_PRTP( "Runtime: TOTAL       ", clock() - clk, clock() - clk );
    Gla_ManReportMemory( p );
    Gla_ManStop( p );
    fflush( stdout );
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

