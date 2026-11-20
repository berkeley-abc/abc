/**CFile****************************************************************

  FileName    [bmcBmcG.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based bounded model checking.]

  Synopsis    [New BMC package.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - July 20, 2017.]

  Revision    [$Id: bmcBmcG.c,v 1.00 2017/07/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include <limits.h>
#include "bmc.h"
#include "sat/cnf/cnf.h"
#include "sat/cadical/ccadical.h"
#include "sat/bsat/satVec.h"
#include "sat/glucose/AbcGlucose.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define PAR_THR_MAX 100

typedef struct Bmcg_Man_t_ Bmcg_Man_t;
struct Bmcg_Man_t_
{
    Bmc_AndPar_t *    pPars;               // parameters
    Gia_Man_t *       pGia;                // user's AIG
    Gia_Man_t *       pFrames;             // unfolded AIG (pFrames->vCopies point to pClean)
    Gia_Man_t *       pClean;              // incremental AIG (pClean->Value point to pFrames)
    Vec_Ptr_t         vGia2Fr;             // copies of GIA in each timeframe
    Vec_Int_t         vFr2Sat;             // mapping of objects in pFrames into SAT variables
    Vec_Int_t         vCiMap;              // maps CIs of pFrames into CIs/frames of GIA
    Vec_Int_t         vPending;            // explicit traversal stack for CaDiCaL
    bmcg_sat_solver * pSats[PAR_THR_MAX];  // concurrent SAT solvers
    CCaDiCaL *        pCadical;            // optional incremental solver
    abctime           Deadline;            // deadline for the CaDiCaL instance
    int               nSatVars;            // number of SAT variables used
    int               nOldFrPis;           // number of primary inputs
    int               nOldFrPos;           // number of primary output
    int               nMemoryLimit;        // portfolio memory budget in MiB
    unsigned          nMemoryPolls;        // amortize solver accounting
    int               fStopNow;            // signal when it is time to stop
    int (*pFuncStop)(void *);              // optional per-instance cancellation
    void *            pStopData;
    unsigned          nStopCalls;
    abctime           timeUnf;             // runtime of unfolding
    abctime           timeCnf;             // runtime of CNF generation
    abctime           timeSmp;             // runtime of CNF simplification
    abctime           timeSat;             // runtime of the solvers
    abctime           timeOth;             // other runtime
};

static inline int * Bmcg_ManCopies( Bmcg_Man_t * p, int f ) { return (int*)Vec_PtrEntry(&p->vGia2Fr, f); }

/**Function*************************************************************

  Synopsis    [Bounds retained frame maps, unrolled objects and solver storage.]

  Description [Only the portfolio enables the memory estimate. The object
  guard also leaves space for a partial frame before the next stop poll.]

  SideEffects []

  SeeAlso     [Bmcg_ManCancelled]

***********************************************************************/
static int Bmcg_ManOverBudget( Bmcg_Man_t * p, int nExtraFrames )
{
    double Bytes;
    if ( Gia_ManObjNum(p->pFrames) >= (1 << 27) ) return 1;
    if ( !p->nMemoryLimit ) return 0;
    Bytes = 4.0 * (Vec_PtrSize(&p->vGia2Fr) + nExtraFrames) * Gia_ManObjNum(p->pGia);
    Bytes += 64.0 * p->pFrames->nObjsAlloc + 192.0 * p->nSatVars;
    Bytes += sizeof(int) * (double)p->vPending.nCap;
    Bytes += 64.0 * ccadical_live_clauses(p->pCadical);
    if ( p->pClean ) Bytes += 64.0 * p->pClean->nObjsAlloc;
    return Bytes >= (double)p->nMemoryLimit * (1 << 20);
}

/**Function*************************************************************

  Synopsis    [Latches an explicitly requested cancellation.]

  Description [Legacy entry points leave the callback unset.]

  SideEffects []

  SeeAlso     [Bmcg_ManPerformWithStop]

***********************************************************************/
static int Bmcg_ManCancelled( void * pData )
{
    Bmcg_Man_t * p = (Bmcg_Man_t *)pData;
    if ( p->pCadical && p->pFuncStop && !(p->nMemoryPolls++ & 255) && Bmcg_ManOverBudget(p, 0) )
        p->fStopNow = 1;
    if ( (p->pFuncStop && p->pFuncStop(p->pStopData)) ||
         (p->Deadline && Abc_Clock() >= p->Deadline) )
        p->fStopNow = 1;
    return p->fStopNow;
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static Bmcg_Man_t * Bmcg_ManStart( Gia_Man_t * pGia, Bmc_AndPar_t * pPars, int fCadical )
{
    Bmcg_Man_t * p = ABC_CALLOC( Bmcg_Man_t, 1 ); 
    int i, Lit = Abc_Var2Lit( 0, 1 );
//    opts.conf_limit = pPars->nConfLimit;
    assert( fCadical || Gia_ManRegNum(pGia) > 0 );
    p->pPars   = pPars;
    p->pGia    = pGia;
    p->pFrames = Gia_ManStart( 3*Gia_ManObjNum(pGia) );  Gia_ManHashStart(p->pFrames);
    p->pClean  = NULL;
//    Vec_PtrFill( &p->vGia2Fr, Gia_ManCountTents(pGia)+1, NULL );
//    for ( i = 0; i < Vec_PtrSize(&p->vGia2Fr); i++ )
//        Vec_PtrWriteEntry( &p->vGia2Fr, i, ABC_FALLOC(int, Gia_ManObjNum(pGia)) );
    Vec_PtrGrow( &p->vGia2Fr, 1000 );  
    Vec_IntGrow( &p->vFr2Sat, 3*Gia_ManCiNum(pGia) );  
    Vec_IntPush( &p->vFr2Sat, 0 );
    Vec_IntGrow( &p->vCiMap, 3*Gia_ManCiNum(pGia) );
    if ( fCadical )
    {
        p->pCadical = ccadical_init();
        ccadical_set_option( p->pCadical, "quiet", 1 );
        ccadical_set_option( p->pCadical, "lucky", 0 );
        ccadical_set_option( p->pCadical, "inprocessing", pPars->fUseEliminate );
        ccadical_set_option( p->pCadical, "elim", pPars->fUseEliminate );
        ccadical_set_option( p->pCadical, "fastelim", pPars->fUseEliminate );
        ccadical_add( p->pCadical, -1 ); // ABC variable zero is constant false.
        ccadical_add( p->pCadical, 0 );
    }
    else
    for ( i = 0; i < p->pPars->nProcs; i++ )
    {
        p->pSats[i] = bmcg_sat_solver_start();  
//        p->pSats[i]->SolverType = i;
        bmcg_sat_solver_addvar( p->pSats[i] );
        bmcg_sat_solver_addclause( p->pSats[i], &Lit, 1 );  
        bmcg_sat_solver_set_stop( p->pSats[i], &p->fStopNow );
    }
    p->nSatVars = 1;
    return p;
}
void Bmcg_ManStop( Bmcg_Man_t * p )
{
    int i;
    Gia_ManStopP( &p->pFrames );
    Gia_ManStopP( &p->pClean );
    Vec_PtrFreeData( &p->vGia2Fr );
    Vec_PtrErase( &p->vGia2Fr );
    Vec_IntErase( &p->vFr2Sat );
    Vec_IntErase( &p->vCiMap );
    Vec_IntErase( &p->vPending );
    for ( i = 0; i < p->pPars->nProcs; i++ )
        if ( p->pSats[i] ) 
            bmcg_sat_solver_stop( p->pSats[i] );
    if ( p->pCadical ) ccadical_release( p->pCadical );
    ABC_FREE( p );
}


/**Function*************************************************************

  Synopsis    [Incremental unfolding.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Bmcg_ManUnfold_rec( Bmcg_Man_t * p, int iObj, int f )
{
    Gia_Obj_t * pObj; 
    int iLit = 0, * pCopies = Bmcg_ManCopies( p, f );
    if ( (p->pFuncStop || p->Deadline) && (!(p->nStopCalls++ & 1023) || p->fStopNow) && Bmcg_ManCancelled(p) ) return -1;
    if ( pCopies[iObj] >= 0 )
        return pCopies[iObj];
    pObj = Gia_ManObj( p->pGia, iObj );
    if ( Gia_ObjIsCi(pObj) )
    {
        if ( Gia_ObjIsPi(p->pGia, pObj) )
        {
            Vec_IntPushTwo( &p->vCiMap, Gia_ObjCioId(pObj), f );
            iLit = Gia_ManAppendCi( p->pFrames );
        }
        else if ( f > 0 )
        {
            pObj = Gia_ObjRoToRi( p->pGia, pObj );
            iLit = Bmcg_ManUnfold_rec( p, Gia_ObjFaninId0p(p->pGia, pObj), f-1 );
            if ( iLit < 0 ) return -1;
            iLit = Abc_LitNotCond( iLit, Gia_ObjFaninC0(pObj) );
        }
    }
    else if ( Gia_ObjIsAnd(pObj) )
    {
        iLit = Bmcg_ManUnfold_rec( p, Gia_ObjFaninId0(pObj, iObj), f );
        if ( iLit < 0 ) return -1;
        iLit = Abc_LitNotCond( iLit, Gia_ObjFaninC0(pObj) );
        if ( iLit > 0 )
        {
            int iNew;
            iNew = Bmcg_ManUnfold_rec( p, Gia_ObjFaninId1(pObj, iObj), f );
            if ( iNew < 0 ) return -1;
            iNew = Abc_LitNotCond( iNew, Gia_ObjFaninC1(pObj) );
            iLit = Gia_ManHashAnd( p->pFrames, iLit, iNew );
        }
    }
    else assert( 0 );
    return (pCopies[iObj] = iLit);
}
int Bmcg_ManCollect_rec( Bmcg_Man_t * p, int iObj )
{
    Gia_Obj_t * pObj; 
    int iSatVar, iLitClean = Gia_ObjCopyArray( p->pFrames, iObj );
    if ( (p->pFuncStop || p->Deadline) && (!(p->nStopCalls++ & 1023) || p->fStopNow) && Bmcg_ManCancelled(p) ) return -1;
    if ( iLitClean >= 0 )
        return iLitClean;
    pObj = Gia_ManObj( p->pFrames, iObj );
    iSatVar = Vec_IntEntry( &p->vFr2Sat, iObj );
    if ( iSatVar > 0 || Gia_ObjIsCi(pObj) )
        iLitClean = Gia_ManAppendCi( p->pClean );
    else if ( Gia_ObjIsAnd(pObj) )
    {
        int iLit0 = Bmcg_ManCollect_rec( p, Gia_ObjFaninId0(pObj, iObj) );
        int iLit1 = Bmcg_ManCollect_rec( p, Gia_ObjFaninId1(pObj, iObj) );
        if ( iLit0 < 0 || iLit1 < 0 ) return -1;
        iLit0 = Abc_LitNotCond( iLit0, Gia_ObjFaninC0(pObj) );
        iLit1 = Abc_LitNotCond( iLit1, Gia_ObjFaninC1(pObj) );
        iLitClean = Gia_ManAppendAnd( p->pClean, iLit0, iLit1 );
    }
    else assert( 0 );
    assert( !Abc_LitIsCompl(iLitClean) );
    Gia_ManObj( p->pClean, Abc_Lit2Var(iLitClean) )->Value = iObj;
    Gia_ObjSetCopyArray( p->pFrames, iObj, iLitClean );
    return iLitClean;
}

/**Function*************************************************************

  Synopsis    [Unfolds a sequential cone on an explicit stack.]

  Description [A transition can depend on a signal many frames earlier.
  Each pending entry stores an object and frame. Cached fanins determine
  which child is visited next, in the same order as recursive unfolding.]

  SideEffects [Extends the unrolled AIG and its time-frame maps.]

  SeeAlso     [Bmcg_ManUnfold_rec]

***********************************************************************/
static int Bmcg_ManUnfoldIter( Bmcg_Man_t * p, int Root, int Frame )
{
    Vec_Int_t * v = &p->vPending;
    Gia_Obj_t * pObj;
    int f, Id, Fan0, Fan1, Lit, Other, * pCopies;
    Vec_IntClear( v );
    Vec_IntPushTwo( v, Root, Frame );
    while ( Vec_IntSize(v) )
    {
        if ( p->fStopNow || (!(p->nStopCalls++ & 1023) && Bmcg_ManCancelled(p)) ) return -1;
        f = Vec_IntEntryLast( v );
        Id = Vec_IntEntry( v, Vec_IntSize(v) - 2 );
        pCopies = Bmcg_ManCopies( p, f );
        if ( pCopies[Id] < 0 )
        {
            pObj = Gia_ManObj( p->pGia, Id );
            Lit = 0;
            if ( Gia_ObjIsPi(p->pGia, pObj) )
            {
                Vec_IntPushTwo( &p->vCiMap, Gia_ObjCioId(pObj), f );
                Lit = Gia_ManAppendCi( p->pFrames );
            }
            else if ( Gia_ObjIsRo(p->pGia, pObj) )
            {
                if ( f )
                {
                    pObj = Gia_ObjRoToRi( p->pGia, pObj );
                    Fan0 = Gia_ObjFaninId0p( p->pGia, pObj );
                    Lit = Bmcg_ManCopies(p, f - 1)[Fan0];
                    if ( Lit < 0 ) { Vec_IntPushTwo(v, Fan0, f - 1); continue; }
                    Lit = Abc_LitNotCond( Lit, Gia_ObjFaninC0(pObj) );
                }
            }
            else
            {
                assert( Gia_ObjIsAnd(pObj) );
                Fan0 = Gia_ObjFaninId0( pObj, Id );
                Lit = pCopies[Fan0];
                if ( Lit < 0 ) { Vec_IntPushTwo(v, Fan0, f); continue; }
                Lit = Abc_LitNotCond( Lit, Gia_ObjFaninC0(pObj) );
                if ( Lit )
                {
                    Fan1 = Gia_ObjFaninId1( pObj, Id );
                    Other = pCopies[Fan1];
                    if ( Other < 0 ) { Vec_IntPushTwo(v, Fan1, f); continue; }
                    Lit = Gia_ManHashAnd( p->pFrames, Lit, Abc_LitNotCond(Other, Gia_ObjFaninC1(pObj)) );
                }
            }
            pCopies[Id] = Lit;
        }
        Vec_IntShrink( v, Vec_IntSize(v) - 2 );
    }
    return Bmcg_ManCopies(p, Frame)[Root];
}

/**Function*************************************************************

  Synopsis    [Collects the incremental CNF cone without recursive calls.]

  Description [An existing SAT variable is a leaf. Otherwise both signed
  fanins are copied before their AND. The maps have the same numbering
  and interpretation as in the recursive construction.]

  SideEffects [Extends the incremental AIG and the frame-to-cone map.]

  SeeAlso     [Bmcg_ManCollect_rec]

***********************************************************************/
static int Bmcg_ManCollectIter( Bmcg_Man_t * p, int Root )
{
    Vec_Int_t * v = &p->vPending;
    Gia_Obj_t * pObj;
    int Id, Fan0, Fan1, Lit0, Lit1, Lit;
    Vec_IntClear( v );
    Vec_IntPush( v, Root );
    while ( Vec_IntSize(v) )
    {
        if ( p->fStopNow || (!(p->nStopCalls++ & 1023) && Bmcg_ManCancelled(p)) ) return -1;
        Id = Vec_IntEntryLast( v );
        if ( Gia_ObjCopyArray(p->pFrames, Id) < 0 )
        {
            pObj = Gia_ManObj( p->pFrames, Id );
            if ( Vec_IntEntry(&p->vFr2Sat, Id) > 0 || Gia_ObjIsCi(pObj) )
                Lit = Gia_ManAppendCi( p->pClean );
            else
            {
                assert( Gia_ObjIsAnd(pObj) );
                Fan0 = Gia_ObjFaninId0( pObj, Id );
                Lit0 = Gia_ObjCopyArray( p->pFrames, Fan0 );
                if ( Lit0 < 0 ) { Vec_IntPush(v, Fan0); continue; }
                Fan1 = Gia_ObjFaninId1( pObj, Id );
                Lit1 = Gia_ObjCopyArray( p->pFrames, Fan1 );
                if ( Lit1 < 0 ) { Vec_IntPush(v, Fan1); continue; }
                Lit = Gia_ManAppendAnd( p->pClean, Abc_LitNotCond(Lit0, Gia_ObjFaninC0(pObj)),
                    Abc_LitNotCond(Lit1, Gia_ObjFaninC1(pObj)) );
            }
            Gia_ManObj( p->pClean, Abc_Lit2Var(Lit) )->Value = Id;
            Gia_ObjSetCopyArray( p->pFrames, Id, Lit );
        }
        Vec_IntPop( v );
    }
    return Gia_ObjCopyArray( p->pFrames, Root );
}

Gia_Man_t * Bmcg_ManUnfold( Bmcg_Man_t * p, int f, int nFramesAdd )
{
    Gia_Man_t * pNew = NULL; Gia_Obj_t * pObj;
    int i, k, iLitFrame, iLitClean, fTrivial = 1;
    int * pCopies, nFrameObjs = Gia_ManObjNum(p->pFrames);
    assert( Gia_ManPoNum(p->pFrames) == f * Gia_ManPoNum(p->pGia) );
    for ( k = 0; k < nFramesAdd; k++ )
    {
        if ( p->pCadical && p->pFuncStop && Bmcg_ManOverBudget(p, 1) )
        {
            p->fStopNow = 1;
            return NULL;
        }
        // unfold this timeframe
        Vec_PtrPush( &p->vGia2Fr, ABC_FALLOC(int, Gia_ManObjNum(p->pGia)) );
        assert( Vec_PtrSize(&p->vGia2Fr) == f+k+1 );
        pCopies = Bmcg_ManCopies( p, f+k );
        //memset( pCopies, 0xFF, sizeof(int)*Gia_ManObjNum(p->pGia) );  
        pCopies[0] = 0;
        Gia_ManForEachPo( p->pGia, pObj, i )
        {
            int Root = Gia_ObjFaninId0p( p->pGia, pObj );
            iLitFrame = p->pCadical ? Bmcg_ManUnfoldIter(p, Root, f+k) : Bmcg_ManUnfold_rec(p, Root, f+k);
            if ( iLitFrame < 0 ) return NULL;
            iLitFrame = Abc_LitNotCond( iLitFrame, Gia_ObjFaninC0(pObj) );
            pCopies[Gia_ObjId(p->pGia, pObj)] = Gia_ManAppendCo( p->pFrames, iLitFrame );
            fTrivial &= (iLitFrame == 0);
        }
    }
    if ( fTrivial )
        return NULL;
    // create a clean copy of the new nodes of this timeframe
    Vec_IntFillExtra( &p->vFr2Sat, Gia_ManObjNum(p->pFrames), -1 );
    Vec_IntFillExtra( &p->pFrames->vCopies, Gia_ManObjNum(p->pFrames), -1 );
    //assert( Vec_IntCountEntry(&p->pFrames->vCopies, -1) == Vec_IntSize(&p->pFrames->vCopies) );
    Gia_ManStopP( &p->pClean );
    p->pClean = Gia_ManStart( Gia_ManObjNum(p->pFrames) - nFrameObjs + 1000 );
    Gia_ObjSetCopyArray( p->pFrames, 0, 0 );
    for ( k = 0; k < nFramesAdd; k++ )
    for ( i = 0; i < Gia_ManPoNum(p->pGia); i++ )
    {
        pObj = Gia_ManCo( p->pFrames, (f+k) * Gia_ManPoNum(p->pGia) + i );
        iLitClean = p->pCadical ? Bmcg_ManCollectIter(p, Gia_ObjFaninId0p(p->pFrames, pObj)) :
            Bmcg_ManCollect_rec(p, Gia_ObjFaninId0p(p->pFrames, pObj));
        if ( iLitClean < 0 ) return NULL;
        iLitClean = Abc_LitNotCond( iLitClean, Gia_ObjFaninC0(pObj) );
        iLitClean = Gia_ManAppendCo( p->pClean, iLitClean );
        Gia_ManObj( p->pClean, Abc_Lit2Var(iLitClean) )->Value = Gia_ObjId(p->pFrames, pObj);
        Gia_ObjSetCopyArray( p->pFrames, Gia_ObjId(p->pFrames, pObj), iLitClean );
    }
    pNew = p->pClean; p->pClean = NULL;
    Gia_ManForEachObj( pNew, pObj, i )
        Gia_ObjSetCopyArray( p->pFrames, pObj->Value, -1 );
    return pNew;
}
Cnf_Dat_t * Bmcg_ManAddNewCnf( Bmcg_Man_t * p, int f, int nFramesAdd )
{
    abctime clk = Abc_Clock();
    Gia_Man_t * pNew = Bmcg_ManUnfold( p, f, nFramesAdd );
    Cnf_Dat_t * pCnf;
    Gia_Obj_t * pObj; 
    int i, iVar, * pMap;
    p->timeUnf += Abc_Clock() - clk;
    if ( pNew == NULL )
        return NULL;
    clk = Abc_Clock();
    if ( p->pFuncStop )
    {
        Jf_Par_t Pars;
        Gia_Man_t * pMapped;
        Mf_ManSetDefaultPars( &Pars );
        Pars.fGenCnf = Pars.fCnfObjIds = Pars.fCnfOnly = 1;
        Pars.fCoarsen = Pars.fAddOrCla = 0;
        Pars.nLutSize = 8;
        pMapped = Mf_ManPerformMappingWithStop( pNew, &Pars, Bmcg_ManCancelled, p );
        Gia_ManStopP( &pMapped );
        pCnf = (Cnf_Dat_t *)pNew->pData;
        pNew->pData = NULL;
        if ( !pCnf ) { p->fStopNow = 1; Gia_ManStop(pNew); return NULL; }
    }
    else
        pCnf = (Cnf_Dat_t *) Mf_ManGenerateCnf( pNew, 8, 1, 0, 0, 0 );
    pMap = ABC_FALLOC( int, Gia_ManObjNum(pNew) );
    pMap[0] = 0;
    Gia_ManForEachObj1( pNew, pObj, i )
    {
        if ( pCnf->pObj2Count[i] <= 0 && !Gia_ObjIsCi(pObj) )
            continue;
        iVar = Vec_IntEntry( &p->vFr2Sat, pObj->Value );
        if ( iVar == -1 )
            Vec_IntWriteEntry( &p->vFr2Sat, pObj->Value, (iVar = p->nSatVars++) );
        pMap[i] = iVar;
    }
    Gia_ManStop( pNew );
    for ( i = 0; i < pCnf->nLiterals; i++ )
    {
        if ( p->pFuncStop && !(i & 1023) && Bmcg_ManCancelled(p) )
        {
            ABC_FREE( pMap );
            Cnf_DataFree( pCnf );
            return NULL;
        }
        pCnf->pClauses[0][i] = Abc_Lit2LitV( pMap, pCnf->pClauses[0][i] );
    }
    ABC_FREE( pMap );
    p->timeCnf += Abc_Clock() - clk;
    return pCnf;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Bmcg_ManPrintFrame( Bmcg_Man_t * p, int f, int nClauses, int Solver, abctime clkStart )
{
    int fUnfinished = 0;
    if ( !p->pPars->fVerbose )
        return;
    Abc_Print( 1, "%4d %s : ", f,   fUnfinished ? "-" : "+" );
//    Abc_Print( 1, "Var =%8.0f.  ",  (double)p->nSatVars ); 
//    Abc_Print( 1, "Cla =%9.0f.  ",  (double)nClauses );  
    if ( p->pCadical )
    {
        ABC_INT64_T Orig = ccadical_irredundant( p->pCadical );
        Abc_Print( 1, "Var =%8.0f.  Cla =%9.0f.  Learn =%9.0f.  Conf =%9.0f.  ",
            (double)ccadical_active(p->pCadical), (double)Orig,
            (double)(ccadical_live_clauses(p->pCadical) - Orig), (double)ccadical_conflicts(p->pCadical) );
    }
    else
    {
        Abc_Print( 1, "Var =%8.0f.  ", (double)(bmcg_sat_solver_varnum(p->pSats[0]) -
            bmcg_sat_solver_elim_varnum(p->pSats[0])) );
        Abc_Print( 1, "Cla =%9.0f.  ",  (double)bmcg_sat_solver_clausenum(p->pSats[0]) );
        Abc_Print( 1, "Learn =%9.0f.  ",(double)bmcg_sat_solver_learntnum(p->pSats[0]) );
        Abc_Print( 1, "Conf =%9.0f.  ", (double)bmcg_sat_solver_conflictnum(p->pSats[0]) );
    }
    if ( p->pPars->nProcs > 1 )
        Abc_Print( 1, "S = %3d. ",  Solver );
    Abc_Print( 1, "%4.0f MB",       1.0*((int)Gia_ManMemory(p->pFrames) + Vec_IntMemory(&p->vFr2Sat))/(1<<20) );
    Abc_Print( 1, "%9.2f sec  ",    (float)(Abc_Clock() - clkStart)/(float)(CLOCKS_PER_SEC) );
    printf( "\n" );
    fflush( stdout );
}
void Bmcg_ManPrintTime( Bmcg_Man_t * p )
{
    abctime clkTotal = p->timeUnf + p->timeCnf + p->timeSmp + p->timeSat + p->timeOth;
    if ( !p->pPars->fVerbose )
        return;
    ABC_PRTP( "Unfolding     ", p->timeUnf,  clkTotal );
    ABC_PRTP( "CNF generation", p->timeCnf,  clkTotal );
    ABC_PRTP( "CNF simplify  ", p->timeSmp,  clkTotal );
    ABC_PRTP( "SAT solving   ", p->timeSat,  clkTotal );
    ABC_PRTP( "Other         ", p->timeOth,  clkTotal );
    ABC_PRTP( "TOTAL         ", clkTotal  ,  clkTotal );
}
Abc_Cex_t * Bmcg_ManGenerateCex( Bmcg_Man_t * p, int i, int f, int s )
{
    Abc_Cex_t * pCex;
    Gia_Obj_t * pObj;  int k;
    if ( p->pCadical && ((ABC_INT64_T)f + 1) * Gia_ManPiNum(p->pGia) + Gia_ManRegNum(p->pGia) > INT_MAX-32 )
        return NULL;
    pCex = Abc_CexAlloc( Gia_ManRegNum(p->pGia), Gia_ManPiNum(p->pGia), f+1 );
    pCex->iFrame = f;
    pCex->iPo = i;
    Gia_ManForEachPi( p->pFrames, pObj, k )
    {
        int iSatVar = Vec_IntEntry( &p->vFr2Sat, Gia_ObjId(p->pFrames, pObj) );
        int iFrame = Vec_IntEntry( &p->vCiMap, 2*k+1 );
        if ( iFrame > f || iSatVar <= 0 ) continue;
        if ( p->pCadical ? ccadical_val(p->pCadical, iSatVar+1) > 0 :
             bmcg_sat_solver_read_cex_varvalue(p->pSats[s], iSatVar) )
        {
            int iCiId = Vec_IntEntry( &p->vCiMap, 2*k );
            Abc_InfoSetBit( pCex->pData, Gia_ManRegNum(p->pGia) + iFrame * Gia_ManPiNum(p->pGia) + iCiId );
        }
    }
    return pCex;
}
void Bmcg_ManAddCnf( Bmcg_Man_t * p, bmcg_sat_solver * pSat, Cnf_Dat_t * pCnf )
{
    int i, iSatVar;
    abctime clk = Abc_Clock();
    if ( p->pCadical )
    {
        ccadical_resize( p->pCadical, p->nSatVars );
        for ( i = 0; i < pCnf->nClauses; i++ )
        {
            int * pLit;
            if ( !(i & 1023) && Bmcg_ManCancelled(p) ) return;
            for ( pLit = pCnf->pClauses[i]; pLit < pCnf->pClauses[i+1]; pLit++ )
                ccadical_add( p->pCadical, lit_print(*pLit) );
            ccadical_add( p->pCadical, 0 );
        }
        // CaDiCaL restores eliminated variables when a later clause or assumption uses them.
        return;
    }
    bmcg_sat_solver_set_nvars( pSat, p->nSatVars );
    if ( p->pPars->fUseEliminate )
    {
        for ( i = p->nOldFrPis; i < Gia_ManPiNum(p->pFrames); i++ )
        {
            Gia_Obj_t * pObj = Gia_ManPi( p->pFrames, i );
            int iSatVar = Vec_IntEntry( &p->vFr2Sat, Gia_ObjId(p->pFrames, pObj) );
            if ( iSatVar > 0 )
                bmcg_sat_solver_var_set_frozen( pSat, iSatVar, 1 );
        }
        for ( i = p->nOldFrPos; i < Gia_ManPoNum(p->pFrames); i++ )
        {
            Gia_Obj_t * pObj = Gia_ManPo( p->pFrames, i );
            int iSatVar = Vec_IntEntry( &p->vFr2Sat, Gia_ObjId(p->pFrames, pObj) );
            if ( iSatVar > 0 )
                bmcg_sat_solver_var_set_frozen( pSat, iSatVar, 1 );
        }
        p->nOldFrPis = Gia_ManPiNum(p->pFrames);
        p->nOldFrPos = Gia_ManPoNum(p->pFrames);
    }
    for ( i = 0; i < pCnf->nClauses; i++ )
    {
        if ( p->pFuncStop && !(i & 1023) && Bmcg_ManCancelled(p) ) return;
        if ( !bmcg_sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1]-pCnf->pClauses[i] ) )
            assert( 0 );
    }
    if ( !p->pPars->fUseEliminate )
        return;
    bmcg_sat_solver_eliminate( pSat, 0 );
    Vec_IntForEachEntry( &p->vFr2Sat, iSatVar, i )
        if ( iSatVar > 0 && bmcg_sat_solver_var_is_elim(pSat, iSatVar) )
            Vec_IntWriteEntry( &p->vFr2Sat, i, -1 );
    p->timeSmp += Abc_Clock() - clk;
}
/**Function*************************************************************

  Synopsis    [Runs incremental BMC with optional cooperative cancellation.]

  Description [Returns zero for a counterexample and minus one when the
  search stops without one. A NULL callback retains the legacy mapping path.]

  SideEffects [Updates progress parameters and stores a counterexample in the input graph.]

  SeeAlso     [Bmcg_ManPerformOne Bmcg_ManPerformWithStop]

***********************************************************************/
static int Bmcg_ManPerformOneInt( Gia_Man_t * pGia, Bmc_AndPar_t * pPars,
    int (*pFuncStop)(void *), void * pStopData, int fCadical, int nMemoryLimit )
{
    abctime clkStart = Abc_Clock();
    Bmcg_Man_t * p = Bmcg_ManStart( pGia, pPars, fCadical );
    int f, k = 0, i = Gia_ManPoNum(pGia), status, RetValue = -1, nClauses = 0;
    int fCanStop = pFuncStop != NULL || (fCadical && pPars->nTimeOut);
    int fComb = fCadical && !Gia_ManRegNum(pGia);
    int Limit = fComb ? 1 : pPars->nFramesMax, Batch = pPars->nFramesAdd;
    int nSafe = 0;
    p->pFuncStop = pFuncStop;
    p->pStopData = pStopData;
    p->nMemoryLimit = nMemoryLimit;
    if ( fCadical && pPars->nTimeOut )
        p->Deadline = clkStart + (abctime)pPars->nTimeOut * CLOCKS_PER_SEC;
    if ( fCadical && fCanStop )
        ccadical_set_terminate( p->pCadical, p, Bmcg_ManCancelled );
    if ( !fCadical && pFuncStop ) bmcg_sat_solver_set_stop_func( p->pSats[0], p, Bmcg_ManCancelled );
    Abc_CexFreeP( &pGia->pCexSeq );
    for ( f = 0; !Limit || f < Limit; f += Batch )
    {
        if ( fCanStop && Bmcg_ManCancelled(p) ) break;
        if ( pPars->pFuncProgress && pPars->pFuncProgress( pPars->pProgress, 0, 0 ) )
            break;
        if ( fCadical && Limit ) Batch = Abc_MinInt( Batch, Limit - f );
        Cnf_Dat_t * pCnf = Bmcg_ManAddNewCnf( p, f, Batch );
        if ( fCanStop && Bmcg_ManCancelled(p) ) { Cnf_DataFree(pCnf); break; }
        if ( pCnf == NULL )
        {
            if ( fCadical )
            {
                for ( k = 0; k < Batch; k++ )
                    Bmcg_ManPrintFrame( p, f+k, nClauses, -1, clkStart );
                nSafe += Batch;
                pPars->iFrame = nSafe - 1;
            }
            else
                Bmcg_ManPrintFrame( p, f, nClauses, -1, clkStart );
            if( pPars->pFuncOnFrameDone )
                for ( k = 0; k < Batch; k++ )
                for ( i = 0; i < Gia_ManPoNum(pGia); i++ )
                    pPars->pFuncOnFrameDone(f+k, i, 0);
            continue;
        }
        nClauses += pCnf->nClauses;
        Bmcg_ManAddCnf( p, p->pSats[0], pCnf );
        Cnf_DataFree( pCnf );
        if ( fCanStop && Bmcg_ManCancelled(p) ) break;
        assert( Gia_ManPoNum(p->pFrames) == (f + Batch) * Gia_ManPoNum(pGia) );
        for ( k = 0; k < Batch; k++ )
        {
            if ( pPars->pFuncProgress && pPars->pFuncProgress( pPars->pProgress, 0, 0 ) )
                break;
            for ( i = 0; i < Gia_ManPoNum(pGia); i++ )
            {
                abctime clk = Abc_Clock();
                int iObj = Gia_ObjId( p->pFrames, Gia_ManCo(p->pFrames, (f+k) * Gia_ManPoNum(pGia) + i) );
                int iLit = Abc_Var2Lit( Vec_IntEntry(&p->vFr2Sat, iObj), 0 );
                if ( fCanStop && Bmcg_ManCancelled(p) ) break;
                if ( pPars->pFuncProgress && pPars->pFuncProgress( pPars->pProgress, 0, 0 ) )
                    break;
                if ( pPars->nTimeOut && (Abc_Clock() - clkStart)/CLOCKS_PER_SEC >= pPars->nTimeOut )
                    break;
                if ( fCadical )
                {
                    if ( pPars->nConfLimit ) ccadical_limit( p->pCadical, "conflicts", pPars->nConfLimit );
                    ccadical_assume( p->pCadical, lit_print(iLit) );
                    status = ccadical_solve( p->pCadical );
                    if ( status == 20 && ccadical_is_inconsistent(p->pCadical) )
                    {
                        Abc_Print( 1, "Warning: &bmcs detected contradictory circuit clauses.\n" );
                        status = 0;
                    }
                    status = status == 10 ? 1 : status == 20 ? -1 : 0;
                }
                else
                    status = bmcg_sat_solver_solve( p->pSats[0], &iLit, 1 );
                p->timeSat += Abc_Clock() - clk;
                if ( fCanStop && status != 1 && Bmcg_ManCancelled(p) ) break;
                if ( pPars->pFuncProgress && pPars->pFuncProgress( pPars->pProgress, 0, 0 ) )
                    break;
                if ( status == -1 ) // unsat
                {
                    if ( i == Gia_ManPoNum(pGia)-1 )
                    {
                        Bmcg_ManPrintFrame( p, f+k, nClauses, -1, clkStart );
                        if ( fCadical ) pPars->iFrame = nSafe++;
                    }
                    if( pPars->pFuncOnFrameDone)
                        pPars->pFuncOnFrameDone(f+k, i, 0);
                    continue;
                }
                if ( status == 1 ) // sat
                {
                    RetValue = 0;
                    pPars->iFrame = f+k;
                    pGia->pCexSeq = Bmcg_ManGenerateCex( p, i, f+k, 0 );
                    if ( fCadical && (!pGia->pCexSeq || !Gia_ManVerifyCex(pGia, pGia->pCexSeq, 0)) )
                    {
                        Abc_Print( 1, "Warning: &bmcs rejected a CaDiCaL counterexample.\n" );
                        Abc_CexFreeP( &pGia->pCexSeq );
                        RetValue = -1;
                        pPars->iFrame = nSafe - 1;
                        break;
                    }
                    pPars->nFailOuts++;
                    Bmcg_ManPrintFrame( p, f+k, nClauses, -1, clkStart );
                    if ( !pPars->fNotVerbose )
                    {
                        int nOutDigits = Abc_Base10Log( Gia_ManPoNum(pGia) );
                        Abc_Print( 1, "Output %*d was asserted in frame %2d (solved %*d out of %*d outputs).  ",  
                            nOutDigits, i, f+k, nOutDigits, pPars->nFailOuts, nOutDigits, Gia_ManPoNum(pGia) );
                        fflush( stdout );
                    }
                    if( pPars->pFuncOnFrameDone )
                        pPars->pFuncOnFrameDone(f+k, i, 1);
                }
                break;
            }
            if ( i < Gia_ManPoNum(pGia) || f+k == Limit-1 )
                break;
        }
        if ( k < Batch )
            break;
    }
    if ( fComb && nSafe == 1 ) RetValue = 1;
    p->timeOth = Abc_Clock() - clkStart - p->timeUnf - p->timeCnf - p->timeSmp - p->timeSat;
    if ( !pPars->fNotVerbose ) {
        if ( RetValue == -1 && !pPars->fNotVerbose )
            printf( "No output failed in %d frames.  ", fCadical ? nSafe : f + (k < Batch ? k+1 : 0) );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clkStart );
    }
    Bmcg_ManPrintTime( p );
    Bmcg_ManStop( p );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Runs the original single-solver entry point.]

  Description []

  SideEffects []

  SeeAlso     [Bmcg_ManPerform]

***********************************************************************/
int Bmcg_ManPerformOne( Gia_Man_t * pGia, Bmc_AndPar_t * pPars )
{
    return Bmcg_ManPerformOneInt( pGia, pPars, NULL, NULL, 0, 0 );
}

/**Function*************************************************************

  Synopsis    [Runs one Glucose solver with cancellable construction and search.]

  Description [The caller owns the stop context. Existing callers retain
  their original mapping and termination behavior.]

  SideEffects [Replaces the input graph's counterexample.]

  SeeAlso     [Bmcg_ManPerform]

***********************************************************************/
int Bmcg_ManPerformWithStop( Gia_Man_t * pGia, Bmc_AndPar_t * pPars,
    int (*pFuncStop)(void *), void * pStopData )
{
    pPars->nProcs = 1;
    if ( pFuncStop && pFuncStop(pStopData) ) return -1;
    if ( pPars->pFuncProgress && pPars->pFuncProgress(pPars->pProgress, 0, 0) ) return -1;
    return Bmcg_ManPerformOneInt( pGia, pPars, pFuncStop, pStopData, 0, 0 );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Bmcg_ManPerform( Gia_Man_t * pGia, Bmc_AndPar_t * pPars ) 
{ 
    pPars->nProcs = 1;
    if ( pPars->pFuncProgress && pPars->pFuncProgress( pPars->pProgress, 0, 0 ) )
        return -1;
    return Bmcg_ManPerformOne( pGia, pPars );
}

/**Function*************************************************************

  Synopsis    [Runs the incremental frame and CNF construction with CaDiCaL.]

  Description [One solver checks all outputs in frame order.]

  SideEffects [Returns a replayed counterexample in the input graph.]

  SeeAlso     [Bmcg_ManPerform]

***********************************************************************/
int Bmcg_ManPerformCadical( Gia_Man_t * pGia, Bmc_AndPar_t * pPars )
{
    if ( !pGia || !pPars ) return -1;
    pPars->nProcs = 1;
    pPars->iFrame = -1;
    Abc_CexFreeP( &pGia->pCexSeq );
    if ( pPars->nFramesAdd <= 0 || pPars->nFramesMax < 0 || pPars->nConfLimit < 0 || pPars->nTimeOut < 0 )
        return -1;
    if ( Gia_ManConstrNum(pGia) || Gia_ManHasChoices(pGia) || pGia->pMuxes || Gia_ManXorNum(pGia) ||
         Gia_ManBufNum(pGia) || Gia_ManBoxNum(pGia) ||
         (pGia->vRegInits && (Vec_IntSize(pGia->vRegInits) != Gia_ManRegNum(pGia) ||
                              Vec_IntCountEntry(pGia->vRegInits, 0) != Gia_ManRegNum(pGia))) )
    {
        Abc_Print( -1, "&bmcs -c requires an ordinary, zero-initialized AIG without constraints.\n" );
        return -1;
    }
    if ( !Gia_ManPoNum(pGia) ) return 1;
    return Bmcg_ManPerformOneInt( pGia, pPars, NULL, NULL, 1, 0 );
}

/**Function*************************************************************

  Synopsis    [Runs the forward CaDiCaL frame builder on a portfolio worker.]

  Description [The caller supplies a checked sequential miter and its deadline.]

  SideEffects [Returns a replayed witness on success.]

  SeeAlso     [Bmcg_ManPerformCadical]

***********************************************************************/
int Bmcg_ManPerformPortfolio( Gia_Man_t * pGia, Bmc_AndPar_t * pPars, int nMemoryLimit,
    int (*pFuncStop)(void *), void * pData )
{
    if ( !pFuncStop || pFuncStop(pData) || Gia_ManObjNum(pGia) >= (1 << 26) ||
         (nMemoryLimit && 192.0 * Gia_ManObjNum(pGia) >= (double)nMemoryLimit * (1 << 20)) ) return -1;
    pPars->nProcs = 1;
    pPars->iFrame = -1;
    return Bmcg_ManPerformOneInt( pGia, pPars, pFuncStop, pData, 1, nMemoryLimit );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
