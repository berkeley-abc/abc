/**CFile****************************************************************

  FileName    [pdr2Man.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Property directed reachability, second implementation.]

  Synopsis    [Manager, cubes, obligations, queue, invariant and CEX.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: pdr2Man.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "pdr2Int.h"
#include "aig/ioa/ioa.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates the manager.]

  Description [The AIG should have one primary output and no constraints.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr2_Man_t * Pdr2_ManStart( Aig_Man_t * pAig, char * pInit, Pdr2_Par_t * pPars )
{
    Pdr2_Man_t * p;
    Aig_Obj_t * pObj;
    int i;
    assert( Saig_ManPoNum(pAig) == 1 );
    assert( Saig_ManConstrNum(pAig) == 0 );
    p = ABC_CALLOC( Pdr2_Man_t, 1 );
    p->pPars     = pPars;
    p->pAig      = pAig;
    p->nRegs     = Saig_ManRegNum( pAig );
    p->nPis      = Saig_ManPiNum( pAig );
    // the initial values (NULL = all 0)
    p->pInit     = ABC_CALLOC( char, p->nRegs + 1 );
    p->pInitState = ABC_CALLOC( char, p->nRegs + 1 );
    if ( pInit )
        memcpy( p->pInit, pInit, (size_t)p->nRegs );
    p->timeStart = Abc_Clock();
    p->timeLimit = pPars->nTimeOut ? p->timeStart + (abctime)pPars->nTimeOut * CLOCKS_PER_SEC : 0;
    // SAT infrastructure: static CNF over the whole AIG, variable == object ID
    p->pCnfMan   = Cnf_ManStart();
    p->pCtx      = Gip_CtxCreate( pAig, p->pCnfMan );
    p->pLoVar    = ABC_ALLOC( int, p->nRegs );
    p->pLiVar    = ABC_ALLOC( int, p->nRegs );
    p->pPiVar    = ABC_ALLOC( int, Abc_MaxInt(p->nPis, 1) );
    Saig_ManForEachLo( pAig, pObj, i )
        p->pLoVar[i] = Gip_ObjVar( pObj );
    Saig_ManForEachLi( pAig, pObj, i )
        p->pLiVar[i] = Gip_ObjVar( pObj );
    Saig_ManForEachPi( pAig, pObj, i )
        p->pPiVar[i] = Gip_ObjVar( pObj );
    p->VarBad    = Gip_ObjVar( Aig_ManCo(pAig, 0) );
    p->vSolvers  = Vec_PtrAlloc( 100 );
    p->pInf      = Pdr2_ManNewSolver( p, 0 );
    p->pLift     = Pdr2_ManNewSolver( p, 0 );
    // frames
    p->vFrames   = Vec_PtrAlloc( 100 );
    p->vInf      = Vec_PtrAlloc( 100 );
    p->vGarbage  = Vec_PtrAlloc( 100 );
    p->vMicScratch = Vec_PtrAlloc( 4 );
    p->pWatch    = ABC_CALLOC( Vec_Ptr_t, 2 * p->nRegs + 2 );
    p->pOcc      = ABC_CALLOC( Vec_Ptr_t, 2 * p->nRegs + 2 );
    p->iEarly    = 1;
    p->vLemFrame = Vec_IntAlloc( 1000 );
    p->IdInit = Vec_IntSize( p->vLemFrame );  Vec_IntPush( p->vLemFrame, 0 );
    p->IdProp = Vec_IntSize( p->vLemFrame );  Vec_IntPush( p->vLemFrame, 0 );
    p->IdInf  = Vec_IntSize( p->vLemFrame );  Vec_IntPush( p->vLemFrame, GIP_FRAME_INF );
    p->iCoreFrame = GIP_FRAME_INF;
    p->fTimeGenCheck = getenv("PDR2_TIMEGEN_CHECK") != NULL;
    p->vLog      = Vec_PtrAlloc( 1000 );
    p->vLogFrame = Vec_IntAlloc( 1000 );
    p->vCtiFree  = Vec_IntAlloc( 100 );
    // obligations
    p->vQueue    = Vec_PtrAlloc( 1000 );
    // abstraction
    p->pAbs      = ABC_CALLOC( char, p->nRegs );
    p->pAbsUsed  = ABC_CALLOC( char, p->nRegs );
    p->pAbsVals  = ABC_ALLOC( char, 2 * Aig_ManObjNumMax(pAig) );
    // activity
    p->pAct      = ABC_CALLOC( double, p->nRegs );
    p->ActInc    = 1.0;
    // scratch
    p->vLastAssump = Vec_IntAlloc( 100 );
    p->vRelInd   = Vec_IntAlloc( 100 );
    p->vLits4    = Vec_IntAlloc( 100 );
    p->vAssump   = Vec_IntAlloc( 100 );
    p->vCst1     = Vec_IntAlloc( 100 );
    p->vCst2     = Vec_IntAlloc( 100 );
    p->vLem      = Vec_IntAlloc( 100 );
    p->vLift1    = Vec_IntAlloc( 100 );
    p->vLift2    = Vec_IntAlloc( 100 );
    p->vLift3    = Vec_IntAlloc( 100 );
    p->pLitMark  = ABC_CALLOC( char, 2 * p->nRegs + 2 );
    p->pVarMark  = ABC_CALLOC( char, p->pCtx->nVars + 1 );
    p->RandState = (unsigned)pPars->nRandomSeed * 2654435761u + 12345u;
    p->iResetFlop = -1;
    if ( pPars->fUseAbs && pPars->nAbsStart == 0 )
        Pdr2_ManAbsStart( p );
    return p;
}

/**Function*************************************************************

  Synopsis    [Deletes the manager.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr2_ManStop( Pdr2_Man_t * p )
{
    Gip_Solver_t * pSat;
    Vec_Ptr_t * vFrame;
    Pdr2_Lem_t * pLem;
    Pdr2_Obl_t * pObl;
    int i, k;
    if ( p->pAig->pFanData )
        Aig_ManFanoutStop( p->pAig );
    Pdr2_ManCollectGarbage( p, 1 );
    Pdr2_QueueClear( p );
    Vec_PtrFree( p->vQueue );
    if ( p->pCexObl )
        Pdr2_OblDeref( p->pCexObl );
    Vec_PtrForEachEntry( Vec_Ptr_t *, p->vFrames, vFrame, k )
    {
        Vec_PtrForEachEntry( Pdr2_Lem_t *, vFrame, pLem, i )
        {
            Pdr2_CubeDeref( pLem->pCube );
            if ( pLem->pObl ) Pdr2_OblDeref( pLem->pObl );
            ABC_FREE( pLem );
        }
        Vec_PtrFree( vFrame );
    }
    Vec_PtrFree( p->vFrames );
    Vec_PtrForEachEntry( Pdr2_Lem_t *, p->vInf, pLem, i )
    {
        Pdr2_CubeDeref( pLem->pCube );
        if ( pLem->pObl ) Pdr2_OblDeref( pLem->pObl );
        ABC_FREE( pLem );
    }
    Vec_PtrFree( p->vInf );
    Vec_PtrFree( p->vGarbage );
    Vec_PtrFreeFree( p->vMicScratch );
    ABC_FREE( p->pCtiVal );
    ABC_FREE( p->pCtiMask );
    ABC_FREE( p->pCtiLive );
    ABC_FREE( p->pCtiLem );
    ABC_FREE( p->pCtiFrame );
    Vec_IntFree( p->vCtiFree );
    for ( i = 0; i < 2 * p->nRegs + 2; i++ )
    {
        ABC_FREE( p->pWatch[i].pArray );
        ABC_FREE( p->pOcc[i].pArray );
    }
    ABC_FREE( p->pWatch );
    ABC_FREE( p->pOcc );
    {
        Pdr2_Cube_t * pCube;
        Vec_PtrForEachEntry( Pdr2_Cube_t *, p->vLog, pCube, i )
            Pdr2_CubeDeref( pCube );
        Vec_PtrFree( p->vLog );
        Vec_IntFree( p->vLogFrame );
        Vec_IntFree( p->vLemFrame );
    }
    Vec_PtrForEachEntry( Gip_Solver_t *, p->vSolvers, pSat, i )
        Gip_SolverFree( pSat );
    Vec_PtrFree( p->vSolvers );
    Gip_SolverFree( p->pInf );
    Gip_SolverFree( p->pLift );
    Gip_CtxFree( p->pCtx );
    Cnf_ManStop( p->pCnfMan );
    ABC_FREE( p->pLoVar );
    ABC_FREE( p->pLiVar );
    ABC_FREE( p->pPiVar );
    ABC_FREE( p->pAct );
    ABC_FREE( p->pInit );
    ABC_FREE( p->pInitState );
    ABC_FREE( p->pAbs );
    ABC_FREE( p->pAbsUsed );
    ABC_FREE( p->pAbsVals );
    ABC_FREE( p->pLiftVals );
    ABC_FREE( p->pLiftMark );
    ABC_FREE( p->pLiftPi );
    ABC_FREE( p->pLiftTrav );
    Vec_IntFreeP( &p->vLiftCone );
    Vec_IntFreeP( &p->vLiftUndo );
    Vec_IntFreeP( &p->vLiftWork );
    Vec_IntFreeP( &p->vLiftJust );
    Vec_IntFreeP( &p->vLiftVisit );
    Vec_IntFree( p->vLastAssump );
    Vec_IntFree( p->vRelInd );
    Vec_IntFree( p->vLits4 );
    Vec_IntFree( p->vAssump );
    Vec_IntFree( p->vCst1 );
    Vec_IntFree( p->vCst2 );
    Vec_IntFree( p->vLem );
    Vec_IntFree( p->vLift1 );
    Vec_IntFree( p->vLift2 );
    Vec_IntFree( p->vLift3 );
    ABC_FREE( p->pLitMark );
    ABC_FREE( p->pVarMark );
    ABC_FREE( p );
    (void)pObl;
}

/**Function*************************************************************

  Synopsis    [Cubes: sorted, signed, reference counted.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pdr2_IntCompare( const void * pa, const void * pb )
{
    return *(const int *)pa - *(const int *)pb;
}
Pdr2_Cube_t * Pdr2_CubeAlloc( int * pLits, int nLits )
{
    Pdr2_Cube_t * p;
    int i;
    p = (Pdr2_Cube_t *)ABC_ALLOC( char, sizeof(Pdr2_Cube_t) + sizeof(int) * Abc_MaxInt(nLits - 1, 0) );
    p->nRefs = 1;
    p->nLits = nLits;
    p->Sign  = 0;
    if ( nLits > 0 )
        memcpy( p->Lits, pLits, sizeof(int) * nLits );
    // insertion sort (cubes are short) with fallback to qsort
    if ( nLits > 32 )
        qsort( p->Lits, (size_t)nLits, sizeof(int), Pdr2_IntCompare );
    else
    {
        int j, k, Lit;
        for ( j = 1; j < nLits; j++ )
        {
            Lit = p->Lits[j];
            for ( k = j - 1; k >= 0 && p->Lits[k] > Lit; k-- )
                p->Lits[k+1] = p->Lits[k];
            p->Lits[k+1] = Lit;
        }
    }
    for ( i = 0; i < nLits; i++ )
    {
        assert( i == 0 || p->Lits[i-1] < p->Lits[i] );
        p->Sign |= Pdr2_LitSign( p->Lits[i] );
    }
    return p;
}
Pdr2_Cube_t * Pdr2_CubeAllocVec( Vec_Int_t * vLits )
{
    return Pdr2_CubeAlloc( Vec_IntArray(vLits), Vec_IntSize(vLits) );
}
void Pdr2_CubeRef( Pdr2_Cube_t * p )
{
    p->nRefs++;
}
void Pdr2_CubeDeref( Pdr2_Cube_t * p )
{
    assert( p->nRefs > 0 );
    if ( --p->nRefs == 0 )
        ABC_FREE( p );
}
// returns 1 if the literal set of pA is contained in that of pB
int Pdr2_CubeSubsume( Pdr2_Cube_t * pA, Pdr2_Cube_t * pB )
{
    int i, k;
    if ( pA->nLits > pB->nLits )
        return 0;
    if ( pA->Sign & ~pB->Sign )
        return 0;
    for ( i = k = 0; i < pA->nLits; i++ )
    {
        while ( k < pB->nLits && pB->Lits[k] < pA->Lits[i] )
            k++;
        if ( k == pB->nLits || pB->Lits[k] != pA->Lits[i] )
            return 0;
        k++;
    }
    return 1;
}
int Pdr2_CubeEqual( Pdr2_Cube_t * pA, Pdr2_Cube_t * pB )
{
    return pA->nLits == pB->nLits && pA->Sign == pB->Sign && !memcmp( pA->Lits, pB->Lits, sizeof(int) * pA->nLits );
}
// returns 1 if the literals of pA are all marked (pB's literals are marked in pLitMark)
int Pdr2_CubeSubsumeMarked( Pdr2_Man_t * p, Pdr2_Cube_t * pA, Pdr2_Cube_t * pB )
{
    int i;
    if ( pA->nLits > pB->nLits )
        return 0;
    if ( pA->Sign & ~pB->Sign )
        return 0;
    for ( i = 0; i < pA->nLits; i++ )
        if ( !p->pLitMark[pA->Lits[i]] )
            return 0;
    return 1;
}
void Pdr2_CubeToVec( Pdr2_Cube_t * p, Vec_Int_t * vLits )
{
    int i;
    Vec_IntClear( vLits );
    for ( i = 0; i < p->nLits; i++ )
        Vec_IntPush( vLits, p->Lits[i] );
}

/**Function*************************************************************

  Synopsis    [Proof obligations.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr2_Obl_t * Pdr2_OblAlloc( Pdr2_Man_t * p, int iFrame, Pdr2_Cube_t * pState, Vec_Int_t * vInputs, Vec_Int_t * vPpis, int nDepth, Pdr2_Obl_t * pNext )
{
    Pdr2_Obl_t * pObl = ABC_CALLOC( Pdr2_Obl_t, 1 );
    pObl->nRefs   = 1;
    pObl->iFrame  = iFrame;
    pObl->nDepth  = nDepth;
    pObl->iPos    = -1;
    pObl->Id      = p->nOblIds++;
    pObl->Act     = 0.0;
    pObl->pState  = pState;  Pdr2_CubeRef( pState );
    pObl->vInputs = vInputs ? Vec_IntDup( vInputs ) : Vec_IntAlloc( 0 );
    pObl->vPpis   = vPpis ? Vec_IntDup( vPpis ) : Vec_IntAlloc( 0 );
    pObl->pNext   = pNext;   if ( pNext ) Pdr2_OblRef( pNext );
    p->nObls++;
    p->nOblLits += pState->nLits;
    return pObl;
}
void Pdr2_OblRef( Pdr2_Obl_t * p )
{
    p->nRefs++;
}
void Pdr2_OblDeref( Pdr2_Obl_t * p )
{
    while ( p )
    {
        Pdr2_Obl_t * pNext;
        assert( p->nRefs > 0 );
        if ( --p->nRefs > 0 )
            return;
        assert( p->iPos == -1 );
        pNext = p->pNext;
        Pdr2_CubeDeref( p->pState );
        Vec_IntFree( p->vInputs );
        Vec_IntFree( p->vPpis );
        ABC_FREE( p );
        p = pNext;
    }
}
void Pdr2_OblPushTo( Pdr2_Obl_t * p, int iFrame )
{
    int i;
    for ( i = p->iFrame; i < iFrame; i++ )
        p->Act *= 0.6;
    p->iFrame = iFrame;
}

/**Function*************************************************************

  Synopsis    [Priority queue of obligations: binary heap.]

  Description [Order: lowest frame, then largest depth, then shortest cube,
  then lexicographically smaller cube, then earlier creation.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Pdr2_OblBefore( Pdr2_Man_t * p, Pdr2_Obl_t * a, Pdr2_Obl_t * b )
{
    int i;
    if ( a->iFrame != b->iFrame )
        return a->iFrame < b->iFrame;
    if ( p->pPars->nQueueOrder == 1 )
    {
        // shortest cube first, then the newest obligation (treb with -ssize)
        if ( a->pState->nLits != b->pState->nLits )
            return a->pState->nLits < b->pState->nLits;
        return a->Id > b->Id;
    }
    if ( p->pPars->nQueueOrder == 2 )
        return a->Stamp > b->Stamp;  // most recently queued first (treb's default: a requeued obligation is new again)
    if ( p->pPars->nQueueOrder == 3 )
    {
        if ( a->pState->nLits != b->pState->nLits )
            return a->pState->nLits < b->pState->nLits;
        return a->Stamp > b->Stamp;
    }
    if ( a->nDepth != b->nDepth )
        return a->nDepth > b->nDepth;
    if ( a->pState->nLits != b->pState->nLits )
        return a->pState->nLits < b->pState->nLits;
    for ( i = 0; i < a->pState->nLits; i++ )
        if ( a->pState->Lits[i] != b->pState->Lits[i] )
            return a->pState->Lits[i] < b->pState->Lits[i];
    return a->Id < b->Id;
}
static inline void Pdr2_QueueSet( Vec_Ptr_t * vHeap, int i, Pdr2_Obl_t * pObl )
{
    Vec_PtrWriteEntry( vHeap, i, pObl );
    pObl->iPos = i;
}
static void Pdr2_QueueSiftUp( Pdr2_Man_t * p, int i )
{
    Vec_Ptr_t * vHeap = p->vQueue;
    Pdr2_Obl_t * pObl = (Pdr2_Obl_t *)Vec_PtrEntry( vHeap, i );
    while ( i > 0 )
    {
        int iPar = (i - 1) >> 1;
        Pdr2_Obl_t * pPar = (Pdr2_Obl_t *)Vec_PtrEntry( vHeap, iPar );
        if ( !Pdr2_OblBefore( p, pObl, pPar ) )
            break;
        Pdr2_QueueSet( vHeap, i, pPar );
        i = iPar;
    }
    Pdr2_QueueSet( vHeap, i, pObl );
}
static void Pdr2_QueueSiftDown( Pdr2_Man_t * p, int i )
{
    Vec_Ptr_t * vHeap = p->vQueue;
    Pdr2_Obl_t * pObl = (Pdr2_Obl_t *)Vec_PtrEntry( vHeap, i );
    int nSize = Vec_PtrSize( vHeap );
    while ( 1 )
    {
        int iLeft = 2*i + 1, iRight = iLeft + 1, iChild;
        Pdr2_Obl_t * pChild;
        if ( iLeft >= nSize )
            break;
        iChild = iLeft;
        if ( iRight < nSize && Pdr2_OblBefore( p, (Pdr2_Obl_t *)Vec_PtrEntry(vHeap, iRight), (Pdr2_Obl_t *)Vec_PtrEntry(vHeap, iLeft) ) )
            iChild = iRight;
        pChild = (Pdr2_Obl_t *)Vec_PtrEntry( vHeap, iChild );
        if ( !Pdr2_OblBefore( p, pChild, pObl ) )
            break;
        Pdr2_QueueSet( vHeap, i, pChild );
        i = iChild;
    }
    Pdr2_QueueSet( vHeap, i, pObl );
}
void Pdr2_QueuePush( Pdr2_Man_t * p, Pdr2_Obl_t * pObl )
{
    assert( pObl->iPos == -1 );
    Pdr2_OblRef( pObl );
    pObl->Stamp = (int)++p->nQueuePushes;
    Vec_PtrPush( p->vQueue, pObl );
    pObl->iPos = Vec_PtrSize(p->vQueue) - 1;
    Pdr2_QueueSiftUp( p, pObl->iPos );
}
// removes the obligation at the given heap position; the caller owns the returned reference
static Pdr2_Obl_t * Pdr2_QueueRemoveAt( Pdr2_Man_t * p, int i )
{
    Pdr2_Obl_t * pObl = (Pdr2_Obl_t *)Vec_PtrEntry( p->vQueue, i );
    Pdr2_Obl_t * pLast = (Pdr2_Obl_t *)Vec_PtrPop( p->vQueue );
    assert( pObl->iPos == i );
    pObl->iPos = -1;
    if ( pLast != pObl )
    {
        Pdr2_QueueSet( p->vQueue, i, pLast );
        Pdr2_QueueSiftUp( p, i );
        Pdr2_QueueSiftDown( p, pLast->iPos );
    }
    return pObl;
}
Pdr2_Obl_t * Pdr2_QueuePop( Pdr2_Man_t * p, int iFrameMax )
{
    Pdr2_Obl_t * pObl;
    if ( Vec_PtrSize(p->vQueue) == 0 )
        return NULL;
    pObl = (Pdr2_Obl_t *)Vec_PtrEntry( p->vQueue, 0 );
    if ( pObl->iFrame > iFrameMax )
        return NULL;
    return Pdr2_QueueRemoveAt( p, 0 );
}
int Pdr2_QueueRemove( Pdr2_Man_t * p, Pdr2_Obl_t * pObl )
{
    if ( pObl->iPos == -1 )
        return 0;
    Pdr2_QueueRemoveAt( p, pObl->iPos );
    Pdr2_OblDeref( pObl );
    return 1;
}
void Pdr2_QueueClear( Pdr2_Man_t * p )
{
    Pdr2_Obl_t * pObl;
    int i;
    Vec_PtrForEachEntry( Pdr2_Obl_t *, p->vQueue, pObl, i )
    {
        pObl->iPos = -1;
        Pdr2_OblDeref( pObl );
    }
    Vec_PtrClear( p->vQueue );
}

/**Function*************************************************************

  Synopsis    [Lemma records.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Pdr2_ManIndexAdd( Pdr2_Man_t * p, Pdr2_Lem_t * pLem )
{
    int i, Lit, iBest = -1, nBest = ABC_INFINITY;
    for ( i = 0; i < pLem->pCube->nLits; i++ )
    {
        Lit = pLem->pCube->Lits[i];
        Vec_PtrPush( &p->pOcc[Lit], pLem );
        if ( Vec_PtrSize(&p->pWatch[Lit]) < nBest )
        {
            nBest = Vec_PtrSize( &p->pWatch[Lit] );
            iBest = Lit;
        }
    }
    assert( iBest >= 0 );
    Vec_PtrPush( &p->pWatch[iBest], pLem );
}
// creates a lemma record and, for frames 1 and above, indexes it; the record takes the given id
// (an existing entry of the frame table, whose clauses the record inherits) or a new one (Id < 0)
Pdr2_Lem_t * Pdr2_LemAllocId( Pdr2_Man_t * p, Pdr2_Cube_t * pCube, Pdr2_Obl_t * pObl, int iFrame, int Id )
{
    Pdr2_Lem_t * pLem = ABC_CALLOC( Pdr2_Lem_t, 1 );
    pLem->pCube  = pCube;  Pdr2_CubeRef( pCube );
    pLem->pObl   = pObl;   if ( pObl ) Pdr2_OblRef( pObl );
    pLem->iFrame = iFrame;
    pLem->iSlot  = -1;
    pLem->iCti   = -1;
    pLem->iCtiInf = -1;
    if ( Id >= 0 )
    {
        pLem->Id = Id;
        Vec_IntWriteEntry( p->vLemFrame, Id, iFrame == -1 ? GIP_FRAME_INF : iFrame );
    }
    else
    {
        pLem->Id = Vec_IntSize( p->vLemFrame );
        Vec_IntPush( p->vLemFrame, iFrame == -1 ? GIP_FRAME_INF : iFrame );
    }
    if ( iFrame != 0 )
        Pdr2_ManIndexAdd( p, pLem );
    return pLem;
}
Pdr2_Lem_t * Pdr2_LemAlloc( Pdr2_Man_t * p, Pdr2_Cube_t * pCube, Pdr2_Obl_t * pObl, int iFrame )
{
    return Pdr2_LemAllocId( p, pCube, pObl, iFrame, -1 );
}
// appends a lemma to a frame vector, recording its position
void Pdr2_LemPush( Vec_Ptr_t * vFrame, Pdr2_Lem_t * pLem )
{
    pLem->iSlot = Vec_PtrSize( vFrame );
    Vec_PtrPush( vFrame, pLem );
}
// the position of a lemma in its frame vector: the recorded one if it is still valid
int Pdr2_LemFind( Vec_Ptr_t * vFrame, Pdr2_Lem_t * pLem )
{
    int i;
    if ( pLem->iSlot >= 0 && pLem->iSlot < Vec_PtrSize(vFrame) && Vec_PtrEntry(vFrame, pLem->iSlot) == pLem )
        return pLem->iSlot;
    for ( i = 0; i < Vec_PtrSize(vFrame); i++ )
        if ( Vec_PtrEntry(vFrame, i) == pLem )
            return pLem->iSlot = i;
    return -1;
}
// swap-removes the lemma at the given position; the record goes to the garbage list
// (it stays in the index lists, marked removed, until the next index rebuild)
void Pdr2_LemRemove( Pdr2_Man_t * p, Vec_Ptr_t * vFrame, int iPos )
{
    Pdr2_Lem_t * pLem = (Pdr2_Lem_t *)Vec_PtrEntry( vFrame, iPos );
    Pdr2_Lem_t * pLast = (Pdr2_Lem_t *)Vec_PtrPop( vFrame );
    if ( pLast != pLem )
    {
        Vec_PtrWriteEntry( vFrame, iPos, pLast );
        pLast->iSlot = iPos;
    }
    pLem->fRemoved = 1;
    Pdr2_LemFreeCti( p, pLem, 0 );
    Vec_PtrPush( p->vGarbage, pLem );
}
// rebuilds the index lists from the live records
void Pdr2_ManIndexRebuild( Pdr2_Man_t * p )
{
    Pdr2_Lem_t * pLem;
    int i, k;
    for ( i = 0; i < 2 * p->nRegs + 2; i++ )
    {
        Vec_PtrClear( &p->pWatch[i] );
        Vec_PtrClear( &p->pOcc[i] );
    }
    for ( k = 1; k < Pdr2_ManFrameNum(p); k++ )
        Vec_PtrForEachEntry( Pdr2_Lem_t *, Pdr2_ManFrame(p, k), pLem, i )
            Pdr2_ManIndexAdd( p, pLem );
    Vec_PtrForEachEntry( Pdr2_Lem_t *, p->vInf, pLem, i )
        Pdr2_ManIndexAdd( p, pLem );
}
// finds a live lemma whose cube is contained in pCube, among lemmas of frames
// iFrameMin..iFrameMax (and of infinity if fInf); returns the one with the highest
// frame (infinity counts highest); with fEqualOnly, only an equal lemma qualifies
Pdr2_Lem_t * Pdr2_ManIndexFindSubsuming( Pdr2_Man_t * p, Pdr2_Cube_t * pCube, int iFrameMin, int iFrameMax, int fInf, int fEqualOnly, int fLowest )
{
    Pdr2_Lem_t * pLem, * pBest = NULL;
    int i, k, Lit;
    // (each record is in one watch list and the cube's literals are distinct: no record is
    // visited twice)
    for ( i = 0; i < pCube->nLits; i++ )
        p->pLitMark[pCube->Lits[i]] = 1;
    for ( i = 0; i < pCube->nLits; i++ )
    {
        Lit = pCube->Lits[i];
        Vec_PtrForEachEntry( Pdr2_Lem_t *, &p->pWatch[Lit], pLem, k )
        {
            if ( pLem->fRemoved )
                continue;
            if ( pLem->iFrame == -1 ? !fInf : (pLem->iFrame < iFrameMin || pLem->iFrame > iFrameMax) )
                continue;
            if ( fEqualOnly && pLem->pCube->nLits != pCube->nLits )
                continue;
            if ( !Pdr2_CubeSubsumeMarked( p, pLem->pCube, pCube ) )
                continue;
            if ( fLowest )
            {
                // prefer the lowest finite frame; infinity only if no finite frame qualifies
                if ( pBest == NULL || pBest->iFrame == -1 || (pLem->iFrame != -1 && pLem->iFrame < pBest->iFrame) )
                    pBest = pLem;
                if ( pBest->iFrame == iFrameMin )
                    break;
            }
            else
            {
                if ( pBest == NULL || pLem->iFrame == -1 || (pBest->iFrame != -1 && pLem->iFrame > pBest->iFrame) )
                    pBest = pLem;
                if ( pBest->iFrame == -1 )
                    break;
            }
        }
        if ( pBest && (fLowest ? pBest->iFrame == iFrameMin : pBest->iFrame == -1) )
            break;
    }
    for ( i = 0; i < pCube->nLits; i++ )
        p->pLitMark[pCube->Lits[i]] = 0;
    return pBest;
}
// frees the removed lemma records once they are purged from the index
void Pdr2_ManCollectGarbage( Pdr2_Man_t * p, int fForce )
{
    Pdr2_Lem_t * pLem;
    int i, k, nLive = Vec_PtrSize( p->vInf );
    if ( Vec_PtrSize(p->vGarbage) == 0 )
        return;
    for ( k = 1; k < Pdr2_ManFrameNum(p); k++ )
        nLive += Vec_PtrSize( Pdr2_ManFrame(p, k) );
    // the index is rebuilt after 1000 removals or when the removed records reach 1/8 of the live
    // ones; the rebuilds cost under 1% of the run time on the IWLS examples with the most lemmas
    // (Ex76, Ex57: 1.4 s in 250 s, up to 30,000 live lemmas); a proportional threshold alone
    // would change the order of the index lists and thereby the search trajectories
    if ( !fForce && Vec_PtrSize(p->vGarbage) < 1000 && Vec_PtrSize(p->vGarbage) * 8 < nLive )
        return;
    if ( !fForce )
        Pdr2_ManIndexRebuild( p );
    Vec_PtrForEachEntry( Pdr2_Lem_t *, p->vGarbage, pLem, i )
    {
        Pdr2_CubeDeref( pLem->pCube );
        if ( pLem->pObl ) Pdr2_OblDeref( pLem->pObl );
        Pdr2_LemFreeCti( p, pLem, 1 );
        ABC_FREE( pLem );
    }
    Vec_PtrClear( p->vGarbage );
}

/**Function*************************************************************

  Synopsis    [Pool of cached counterexamples to propagation.]

  Description [A failed propagation query of a lemma at frame k yields a
  state of F_k (resp. of the inf lemmas for k = -1) with a transition into
  the lemma's cube. The state stays a counterexample as long as no lemma
  added later to a frame >= k (or to infinity) excludes it; unknown
  (unassigned) latches never let a lemma exclude the state. The states
  are stored bit-parallel (one row of words per flop) so that each new
  lemma is checked against all cached states at once; this check is run
  lazily over the lemma log before a cached state is used.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Pdr2_CtiCapNext( Pdr2_Man_t * p ) { return p->nCtiCap ? 2 * p->nCtiCap : 1024; }
static void Pdr2_CtiPoolGrow( Pdr2_Man_t * p )
{
    int nCapNew = Pdr2_CtiCapNext( p );
    int nOld = p->nCtiCap / 64, nNew = nCapNew / 64, i;
    word * pVal  = ABC_CALLOC( word, (size_t)p->nRegs * nNew );
    word * pMask = ABC_CALLOC( word, (size_t)p->nRegs * nNew );
    for ( i = 0; i < p->nRegs && nOld; i++ )
    {
        memcpy( pVal  + (size_t)i * nNew, p->pCtiVal  + (size_t)i * nOld, sizeof(word) * nOld );
        memcpy( pMask + (size_t)i * nNew, p->pCtiMask + (size_t)i * nOld, sizeof(word) * nOld );
    }
    ABC_FREE( p->pCtiVal );
    ABC_FREE( p->pCtiMask );
    p->pCtiVal  = pVal;
    p->pCtiMask = pMask;
    p->pCtiLive = ABC_REALLOC( word, p->pCtiLive, nNew );
    memset( p->pCtiLive + nOld, 0, sizeof(word) * (nNew - nOld) );
    p->pCtiLem   = ABC_REALLOC( Pdr2_Lem_t *, p->pCtiLem, nCapNew );
    p->pCtiFrame = ABC_REALLOC( int, p->pCtiFrame, nCapNew );
    p->nCtiCap = nCapNew;
}
static inline void Pdr2_CtiSlotFree( Pdr2_Man_t * p, int Slot )
{
    p->pCtiLive[Slot >> 6] &= ~((word)1 << (Slot & 63));
    p->pCtiLem[Slot] = NULL;
    Vec_IntPush( p->vCtiFree, Slot );
}
void Pdr2_LemFreeCti( Pdr2_Man_t * p, Pdr2_Lem_t * pLem, int fInfToo )
{
    if ( pLem->iCti >= 0 )
    {
        Pdr2_CtiSlotFree( p, pLem->iCti );
        pLem->iCti = -1;
    }
    if ( fInfToo && pLem->iCtiInf >= 0 )
    {
        Pdr2_CtiSlotFree( p, pLem->iCtiInf );
        pLem->iCtiInf = -1;
    }
}
// a pushed lemma (a subset of the literals of pFrom) keeps the counterexample to
// propagation to infinity: the state still has a transition into the larger cube
void Pdr2_LemInheritInfCti( Pdr2_Man_t * p, Pdr2_Lem_t * pLem, Pdr2_Lem_t * pFrom )
{
    int i, Slot, nStride, Var, fOutside = 0;
    word Bit;
    if ( pFrom == NULL || pFrom->iCtiInf < 0 )
        return;
    assert( pLem->iCtiInf < 0 );
    Slot = pFrom->iCtiInf;
    pFrom->iCtiInf = -1;
    // the state must lie outside the (larger) pushed cube: some literal is known false
    nStride = p->nCtiCap / 64;
    Bit = (word)1 << (Slot & 63);
    for ( i = 0; i < pLem->pCube->nLits && !fOutside; i++ )
    {
        Var = Abc_Lit2Var( pLem->pCube->Lits[i] );
        if ( !(p->pCtiMask[(size_t)Var * nStride + (Slot >> 6)] & Bit) )
            continue;
        if ( ((p->pCtiVal[(size_t)Var * nStride + (Slot >> 6)] & Bit) != 0) == Abc_LitIsCompl(pLem->pCube->Lits[i]) )
            fOutside = 1;
    }
    if ( !fOutside )
    {
        Pdr2_CtiSlotFree( p, Slot );
        return;
    }
    pLem->iCtiInf = Slot;
    p->pCtiLem[Slot] = pLem;
}
// applies the lemmas logged since the last call: a cached state excluded by a new lemma is dropped
static void Pdr2_CtiApplyLog( Pdr2_Man_t * p )
{
    Pdr2_Cube_t * pCube;
    int j, k, w, nWords = (p->nCtiUsed + 63) / 64, nStride = p->nCtiCap / 64, Frame, Slot;
    word r, * pRow;
    for ( j = 0; j < Vec_PtrSize(p->vLog); j++ )
    {
        pCube = (Pdr2_Cube_t *)Vec_PtrEntry( p->vLog, j );
        Frame = Vec_IntEntry( p->vLogFrame, j );
        for ( w = 0; w < nWords; w++ )
        {
            r = p->pCtiLive[w];
            for ( k = 0; k < pCube->nLits && r; k++ )
            {
                int Var = Abc_Lit2Var( pCube->Lits[k] );
                pRow = p->pCtiVal + (size_t)Var * nStride;
                // a literal known to be false in the state keeps the state outside the cube;
                // an unknown latch does not (several lemmas may jointly exclude all completions)
                r &= (Abc_LitIsCompl(pCube->Lits[k]) ? ~pRow[w] : pRow[w]) | ~p->pCtiMask[(size_t)Var * nStride + w];
            }
            // the states in r may satisfy the cube: they are dropped if the new lemma
            // belongs to their frame
            while ( r )
            {
                Slot = 64 * w + Abc_Tt6FirstBit( r );
                r &= r - 1;
                if ( Frame != -1 && (p->pCtiFrame[Slot] == -1 || p->pCtiFrame[Slot] > Frame) )
                    continue;
                assert( p->pCtiLem[Slot] );
                if ( p->pCtiFrame[Slot] == -1 )
                    p->pCtiLem[Slot]->iCtiInf = -1;
                else
                    p->pCtiLem[Slot]->iCti = -1;
                Pdr2_CtiSlotFree( p, Slot );
                p->nCtiKilled++;
            }
        }
    }
    // the entries have been applied to every live slot and are not needed again
    Vec_PtrForEachEntry( Pdr2_Cube_t *, p->vLog, pCube, j )
        Pdr2_CubeDeref( pCube );
    Vec_PtrClear( p->vLog );
    Vec_IntClear( p->vLogFrame );
}
void Pdr2_LemCacheCti( Pdr2_Man_t * p, Pdr2_Lem_t * pLem, Gip_Solver_t * pSat, int iFrame )
{
    int * pSlot = iFrame == -1 ? &pLem->iCtiInf : &pLem->iCti;
    int i, Slot, nStride, Value;
    word Bit;
    Pdr2_CtiApplyLog( p );
    if ( *pSlot < 0 )
    {
        if ( Vec_IntSize(p->vCtiFree) > 0 )
            Slot = Vec_IntPop( p->vCtiFree );
        else
        {
            // memory guard: the pool takes nRegs * nCtiCap / 4 bytes, checked for the grown capacity
            if ( p->nCtiUsed == p->nCtiCap && (ABC_INT64_T)p->nRegs * Pdr2_CtiCapNext(p) / 4 > ((ABC_INT64_T)512 << 20) )
                return;
            if ( p->nCtiUsed == p->nCtiCap )
                Pdr2_CtiPoolGrow( p );
            Slot = p->nCtiUsed++;
        }
        *pSlot = Slot;
    }
    else
        Slot = *pSlot;
    nStride = p->nCtiCap / 64;
    Bit = (word)1 << (Slot & 63);
    for ( i = 0; i < p->nRegs; i++ )
    {
        word * pVal  = p->pCtiVal  + (size_t)i * nStride + (Slot >> 6);
        word * pMask = p->pCtiMask + (size_t)i * nStride + (Slot >> 6);
        Value = pSat->pValue[p->pLoVar[i]];
        if ( Value == GIP_NONE )
        {
            *pMask &= ~Bit;
            *pVal  &= ~Bit;
            continue;
        }
        *pMask |= Bit;
        if ( Value == GIP_TRUE )
            *pVal |= Bit;
        else
            *pVal &= ~Bit;
    }
    p->pCtiLive[Slot >> 6] |= Bit;
    p->pCtiLem[Slot]   = pLem;
    p->pCtiFrame[Slot] = iFrame;
}
// returns 1 if a cached state still shows that the lemma cannot be pushed from iFrame
int Pdr2_LemCtiValid( Pdr2_Man_t * p, Pdr2_Lem_t * pLem, int iFrame )
{
    int Slot;
    Pdr2_CtiApplyLog( p );
    Slot = iFrame == -1 ? pLem->iCtiInf : pLem->iCti;
    if ( Slot < 0 )
        return 0;
    assert( p->pCtiLem[Slot] == pLem );
    if ( iFrame != -1 && p->pCtiFrame[Slot] != iFrame )
        return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Activity of flop variables (rIC3 style, with decay).]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr2_ManActBump( Pdr2_Man_t * p, Vec_Int_t * vCube )
{
    int i, Lit;
    p->ActInc *= 1.0 / 0.9;
    Vec_IntForEachEntry( vCube, Lit, i )
    {
        p->pAct[Abc_Lit2Var(Lit)] += p->ActInc;
        if ( p->pAct[Abc_Lit2Var(Lit)] > 1e100 )
        {
            int k;
            for ( k = 0; k < p->nRegs; k++ )
                p->pAct[k] *= 1e-100;
            p->ActInc *= 1e-100;
        }
    }
}
typedef struct Pdr2_ActPair_t_ { double Act; int Idx; int Lit; } Pdr2_ActPair_t;
static int Pdr2_ActPairCmpAsc( const void * pa, const void * pb )
{
    const Pdr2_ActPair_t * a = (const Pdr2_ActPair_t *)pa, * b = (const Pdr2_ActPair_t *)pb;
    if ( a->Act < b->Act ) return -1;
    if ( a->Act > b->Act ) return  1;
    return a->Idx - b->Idx;
}
static int Pdr2_ActPairCmpDesc( const void * pa, const void * pb )
{
    const Pdr2_ActPair_t * a = (const Pdr2_ActPair_t *)pa, * b = (const Pdr2_ActPair_t *)pb;
    if ( a->Act > b->Act ) return -1;
    if ( a->Act < b->Act ) return  1;
    return a->Idx - b->Idx;
}
// stable sort of flop literals by the activity of their variables
void Pdr2_ManSortByAct( Pdr2_Man_t * p, Vec_Int_t * vCube, int fAscending )
{
    Pdr2_ActPair_t Pairs[64];
    Pdr2_ActPair_t * pPairs;
    int i, n = Vec_IntSize(vCube);
    if ( n < 2 )
        return;
    pPairs = n <= 64 ? Pairs : ABC_ALLOC( Pdr2_ActPair_t, n );
    for ( i = 0; i < n; i++ )
    {
        pPairs[i].Lit = Vec_IntEntry( vCube, i );
        pPairs[i].Act = p->pAct[Abc_Lit2Var(pPairs[i].Lit)];
        pPairs[i].Idx = i;
    }
    qsort( pPairs, (size_t)n, sizeof(Pdr2_ActPair_t), fAscending ? Pdr2_ActPairCmpAsc : Pdr2_ActPairCmpDesc );
    for ( i = 0; i < n; i++ )
        Vec_IntWriteEntry( vCube, i, pPairs[i].Lit );
    if ( pPairs != Pairs )
        ABC_FREE( pPairs );
}

/**Function*************************************************************

  Synopsis    [Random numbers (xorshift32).]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned Pdr2_ManRandom( Pdr2_Man_t * p )
{
    unsigned x = p->RandState;
    if ( x == 0 ) x = 0x9E3779B9u;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    p->RandState = x;
    return x;
}
int Pdr2_ManRandomBool( Pdr2_Man_t * p, double Prob )
{
    return (Pdr2_ManRandom(p) % 1000000u) < (unsigned)(Prob * 1000000.0);
}
void Pdr2_ManShuffle( Pdr2_Man_t * p, Vec_Int_t * vLits )
{
    int i, j, n = Vec_IntSize(vLits);
    for ( i = n - 1; i > 0; i-- )
    {
        j = (int)(Pdr2_ManRandom(p) % (unsigned)(i + 1));
        if ( j != i )
        {
            int t = Vec_IntEntry( vLits, i );
            Vec_IntWriteEntry( vLits, i, Vec_IntEntry(vLits, j) );
            Vec_IntWriteEntry( vLits, j, t );
        }
    }
}
void Pdr2_ManShufflePtr( Pdr2_Man_t * p, Vec_Ptr_t * vPtrs )
{
    int i, j, n = Vec_PtrSize(vPtrs);
    for ( i = n - 1; i > 0; i-- )
    {
        j = (int)(Pdr2_ManRandom(p) % (unsigned)(i + 1));
        if ( j != i )
        {
            void * t = Vec_PtrEntry( vPtrs, i );
            Vec_PtrWriteEntry( vPtrs, i, Vec_PtrEntry(vPtrs, j) );
            Vec_PtrWriteEntry( vPtrs, j, t );
        }
    }
}

/**Function*************************************************************

  Synopsis    [Completes a cube intersecting the initial states into one of them.]

  Description [The flops with a defined initial value take it (the literals
  of the cube agree with it); a don't-care flop takes its value in the cube
  if it has one and 0 otherwise. The counterexample and the simulation of
  the abstraction checks use the same initial state.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr2_ManInitState( Pdr2_Man_t * p, Pdr2_Cube_t * pCube, char * pState )
{
    int i;
    for ( i = 0; i < p->nRegs; i++ )
        pState[i] = p->pInit[i] == 1;
    for ( i = 0; i < pCube->nLits; i++ )
    {
        assert( !Pdr2_ManLitIsNonInit(p, pCube->Lits[i]) );
        pState[Abc_Lit2Var(pCube->Lits[i])] = !Abc_LitIsCompl(pCube->Lits[i]);
    }
}

/**Function*************************************************************

  Synopsis    [Derives the counterexample from the obligation chain.]

  Description [The chain starts at the obligation that reached the initial
  states and follows pNext to the bad state. Each obligation carries the
  input values that take its state into the next state (or into the
  property failure for the last one). The register values of the
  counterexample are the initial state (Pdr2_ManInitState).]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t * Pdr2_ManDeriveCex( Pdr2_Man_t * p )
{
    Abc_Cex_t * pCex;
    Pdr2_Obl_t * pObl;
    int i, f, Lit, nFrames = 0;
    for ( pObl = p->pCexObl; pObl; pObl = pObl->pNext )
        nFrames++;
    assert( nFrames == p->pCexObl->nDepth + 1 );
    pCex = Abc_CexAlloc( p->nRegs, p->nPis, nFrames );
    pCex->iPo    = 0;
    pCex->iFrame = nFrames - 1;
    Pdr2_ManInitState( p, p->pCexObl->pState, p->pInitState );
    for ( i = 0; i < p->nRegs; i++ )
        if ( p->pInitState[i] )
            Abc_InfoSetBit( pCex->pData, i );
    for ( pObl = p->pCexObl, f = 0; pObl; pObl = pObl->pNext, f++ )
        Vec_IntForEachEntry( pObl->vInputs, Lit, i )
            if ( !Abc_LitIsCompl(Lit) )
                Abc_InfoSetBit( pCex->pData, pCex->nRegs + f * pCex->nPis + Abc_Lit2Var(Lit) );
    assert( f == nFrames );
    return pCex;
}

/**Function*************************************************************

  Synopsis    [Collects the inductive invariant as a list of cubes.]

  Description [The invariant consists of the lemmas of all frames starting
  from the first empty one, plus the lemmas at frame infinity.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Ptr_t * Pdr2_ManCollectInvariant( Pdr2_Man_t * p )
{
    Vec_Ptr_t * vInv = Vec_PtrAlloc( 1000 );
    Pdr2_Lem_t * pLem;
    int k, i, kStart = -1;
    for ( k = 1; k < Pdr2_ManFrameNum(p); k++ )
        if ( Vec_PtrSize(Pdr2_ManFrame(p, k)) == 0 )
        {
            kStart = k;
            break;
        }
    if ( kStart == -1 )
    {
        // no empty frame: this only happens if the property is proved by inf lemmas alone
        kStart = Pdr2_ManFrameNum(p);
    }
    for ( k = kStart; k < Pdr2_ManFrameNum(p); k++ )
        Vec_PtrForEachEntry( Pdr2_Lem_t *, Pdr2_ManFrame(p, k), pLem, i )
            Vec_PtrPush( vInv, pLem->pCube );
    Vec_PtrForEachEntry( Pdr2_Lem_t *, p->vInf, pLem, i )
        Vec_PtrPush( vInv, pLem->pCube );
    return vInv;
}

/**Function*************************************************************

  Synopsis    [Verifies the inductive invariant with a fresh solver.]

  Description [Checks that each cube excludes the initial state, that the
  invariant is closed under the transition relation, and that it excludes
  the bad states. Only the overall deadline applies (the propagation
  budgets of the search do not). Returns 1 if all checks pass (verified),
  0 if a check fails, -1 if the deadline stopped the checks (incomplete).]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr2_ManVerifyInvariant( Pdr2_Man_t * p )
{
    Vec_Ptr_t * vInv = Pdr2_ManCollectInvariant( p );
    Gip_Solver_t * pSat = Pdr2_ManNewSolver( p, 0 );
    Pdr2_Cube_t * pCube;
    int i, Lit, RetValue, fOk = 1;
    abctime clk = Abc_Clock();
    // the slice budgets of the search do not apply to the verification
    p->timeLimit = p->timeGlobal;
    p->propLimit = p->propSlice = 0;
    Vec_PtrForEachEntry( Pdr2_Cube_t *, vInv, pCube, i )
    {
        if ( Pdr2_CubeIsInit(p, pCube) )
        {
            Abc_Print( 1, "Invariant check failed: cube %d intersects the initial states.\n", i );
            fOk = 0;
        }
        Pdr2_ManSolverAddLemma( p, pSat, pCube, p->IdInf );
    }
    Vec_PtrForEachEntry( Pdr2_Cube_t *, vInv, pCube, i )
    {
        Pdr2_CubeToVec( pCube, p->vLits4 );
        RetValue = Pdr2_ManSolveRelative( p, pSat, p->vLits4, 0, NULL );
        if ( RetValue == -1 )
        {
            // the overall time limit was reached during the check: the proof itself stands
            Abc_Print( 1, "Invariant verification is incomplete: the time limit was reached at clause %d of %d.\n", i, Vec_PtrSize(vInv) );
            if ( fOk == 1 )
                fOk = -1;
            break;
        }
        if ( RetValue != 1 )
        {
            Abc_Print( 1, "Invariant check failed: cube %d is not inductive.\n", i );
            fOk = 0;
            break;
        }
    }
    if ( fOk == 1 )
    {
        Lit = Abc_Var2Lit( p->VarBad, 0 );
        pSat->nConfLimit = 0;
        pSat->nPropLimit = 0;
        pSat->TimeLimit = p->timeGlobal;
        RetValue = Gip_SolverSolve( pSat, &Lit, 1, NULL, NULL, 0, -1 );
        if ( RetValue == GIP_UNDEF )
        {
            Abc_Print( 1, "Invariant verification is incomplete: the time limit was reached in the property check.\n" );
            fOk = -1;
        }
        else if ( RetValue != GIP_UNSAT )
        {
            Abc_Print( 1, "Invariant check failed: the invariant does not exclude the bad states.\n" );
            fOk = 0;
        }
    }
    if ( p->pPars->fVerbose )
    {
        Abc_Print( 1, "Verification of the invariant with %d clauses %s.  ", Vec_PtrSize(vInv), fOk == 1 ? "passed" : fOk == 0 ? "FAILED" : "incomplete" );
        ABC_PRT( "Time", Abc_Clock() - clk );
    }
    Gip_SolverFree( pSat );
    Vec_PtrFree( vInv );
    return fOk;
}

/**Function*************************************************************

  Synopsis    [Writes the AIG of the design into an AIGER file.]

  Description [The initial values of the flops are written in the latch
  lines (AIGER 1.9: "next init", where init is 0, 1, or the latch literal
  itself for a don't-care value; 0 is the default and is omitted). Returns
  1 on success, 0 if the file could not be written.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pdr2_ManWriteDesign( Aig_Man_t * pAig, char * pInit, char * pFileName )
{
    Vec_Str_t * vBuffer = Ioa_WriteAigerIntoMemoryStr( pAig );
    FILE * pFile = fopen( pFileName, "wb" );
    char * pCur = Vec_StrArray( vBuffer ), * pEnd = pCur + Vec_StrSize( vBuffer ), * pLine;
    int i, fOk = pFile != NULL;
    if ( pFile )
    {
        // the header line, then one latch line per flop (the binary format writes them as text)
        pLine = (char *)memchr( pCur, '\n', (size_t)(pEnd - pCur) ) + 1;
        fOk &= fwrite( pCur, 1, (size_t)(pLine - pCur), pFile ) == (size_t)(pLine - pCur);
        for ( i = 0; i < Aig_ManRegNum(pAig); i++ )
        {
            pCur = pLine;
            pLine = (char *)memchr( pCur, '\n', (size_t)(pEnd - pCur) ) + 1;
            fOk &= fwrite( pCur, 1, (size_t)(pLine - 1 - pCur), pFile ) == (size_t)(pLine - 1 - pCur);
            if ( pInit[i] == 1 )
                fprintf( pFile, " 1" );
            else if ( pInit[i] == 2 )
                fprintf( pFile, " %d", 2 * (Saig_ManPiNum(pAig) + 1 + i) );
            fprintf( pFile, "\n" );
        }
        fOk &= fwrite( pLine, 1, (size_t)(pEnd - pLine), pFile ) == (size_t)(pEnd - pLine);
        fOk &= fclose( pFile ) == 0;
    }
    Vec_StrFree( vBuffer );
    return fOk;
}

/**Function*************************************************************

  Synopsis    [Dumps the invariant as a PLA file (one cube per blocked cube).]

  Description [The cubes are over the flops of the design the winning run
  worked on, in their original polarities. This is the input design, with
  its initial values, for the plain runs; it differs from it when a
  combinational network gets a flop, the abstraction runs add a reset
  flop, or -q merges and removes flops (fTransformed). The design is
  therefore always written next to the invariant (as <name>_design.aig,
  flops in the same order, with their initial values). Returns 1 if both
  files were written.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr2_ManDumpInvariant( Pdr2_Man_t * p, int fTransformed )
{
    Vec_Ptr_t * vInv;
    char * pFileName = p->pPars->pInvFileName ? p->pPars->pInvFileName : (char *)"inv.pla";
    char * pDesign = ABC_ALLOC( char, strlen(pFileName) + 20 ), * pDot, * pBuffer;
    Pdr2_Cube_t * pCube;
    FILE * pFile;
    int i, k, fOk;
    // the name of the design file: the invariant file name without the extension, plus "_design.aig"
    strcpy( pDesign, pFileName );
    if ( (pDot = strrchr(pDesign, '.')) && !strchr(pDot, '/') )
        *pDot = 0;
    strcat( pDesign, "_design.aig" );
    if ( !Pdr2_ManWriteDesign( p->pAig, p->pInit, pDesign ) )
    {
        Abc_Print( 1, "Cannot write the design into file \"%s\"; the invariant is not dumped.\n", pDesign );
        ABC_FREE( pDesign );
        return 0;
    }
    pFile = fopen( pFileName, "w" );
    if ( pFile == NULL )
    {
        Abc_Print( 1, "Cannot open file \"%s\" for writing the invariant.\n", pFileName );
        ABC_FREE( pDesign );
        return 0;
    }
    vInv = Pdr2_ManCollectInvariant( p );
    pBuffer = ABC_ALLOC( char, p->nRegs + 1 );
    fprintf( pFile, "# Inductive invariant computed by pdr2 (each line is a blocked cube over the flops)\n" );
    fprintf( pFile, "# The flops are those of the %s design in \"%s\" (%d flops), in the same order\n",
        fTransformed ? "transformed" : "solved", pDesign, p->nRegs );
    fprintf( pFile, ".i %d\n.o 1\n.p %d\n", p->nRegs, Vec_PtrSize(vInv) );
    Vec_PtrForEachEntry( Pdr2_Cube_t *, vInv, pCube, i )
    {
        for ( k = 0; k < p->nRegs; k++ )
            pBuffer[k] = '-';
        pBuffer[p->nRegs] = 0;
        for ( k = 0; k < pCube->nLits; k++ )
            pBuffer[Abc_Lit2Var(pCube->Lits[k])] = Abc_LitIsCompl(pCube->Lits[k]) ? '0' : '1';
        fprintf( pFile, "%s 1\n", pBuffer );
    }
    fprintf( pFile, ".e\n" );
    fOk = !ferror( pFile );
    fOk &= fclose( pFile ) == 0;
    if ( !fOk )
        Abc_Print( 1, "Writing the invariant into file \"%s\" has failed.\n", pFileName );
    else if ( !p->pPars->fSilent )
        Abc_Print( 1, "Dumped the inductive invariant with %d cubes into file \"%s\" (over the flops of the design in \"%s\").\n", Vec_PtrSize(vInv), pFileName, pDesign );
    ABC_FREE( pBuffer );
    ABC_FREE( pDesign );
    Vec_PtrFree( vInv );
    return fOk;
}

/**Function*************************************************************

  Synopsis    [Progress and statistics.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr2_ManTimedOut( Pdr2_Man_t * p )
{
    return (p->timeLimit && Abc_Clock() > p->timeLimit) || (p->propLimit && p->nProps >= p->propLimit);
}
void Pdr2_ManPrintProgress( Pdr2_Man_t * p, int fForce )
{
    int k, nFrames = Pdr2_ManFrameNum(p), kStart;
    if ( !p->pPars->fVerbose && !fForce )
        return;
    Abc_Print( 1, "%3d :", Pdr2_ManLevel(p) );
    kStart = nFrames > 40 ? nFrames - 40 : 1;
    if ( kStart > 1 )
        Abc_Print( 1, " ..." );
    for ( k = kStart; k < nFrames; k++ )
        Abc_Print( 1, " %d", Vec_PtrSize(Pdr2_ManFrame(p, k)) );
    Abc_Print( 1, " | inf = %d  obl = %d  lvObl = %d  lvLem = %d  sat = %.0fK  ", Vec_PtrSize(p->vInf), Vec_PtrSize(p->vQueue), p->nOblsLevel, (int)(p->nLemmas - p->nLemmasLevel), (double)p->nSolves / 1000.0 );
    if ( p->fAbsActive )
        Abc_Print( 1, "abs = %d  ", p->nAbsFlops );
    Abc_Print( 1, "%6.2f sec\n", (double)(Abc_Clock() - p->timeStart) / CLOCKS_PER_SEC );
    fflush( stdout );
}
void Pdr2_ManPrintStats( Pdr2_Man_t * p )
{
    abctime timeTotal = p->timeRun ? p->timeRun : Abc_Clock() - p->timeStart;
    Abc_Print( 1, "Frames = %d. Lemmas = %d (inf = %d). Obligations = %d (dropped = %d). SAT calls = %d. MICs = %d.\n",
        Pdr2_ManLevel(p), (int)p->nLemmas, (int)p->nInfLemmas, (int)p->nObls, (int)p->nOblsDropped, (int)p->nSolves, (int)p->nMics );
    if ( p->pPars->fTimeGen )
        Abc_Print( 1, "Time generalization: %d pushes skipped %d frames, %d lemmas placed in frame infinity directly%s.\n",
            (int)p->nTgJumps, (int)p->nTgFrames, (int)p->nTgInf, p->fTimeGenCheck ? " (checked)" : "" );
    if ( p->nTgChecks )
        Abc_Print( 1, "Time generalization checks: %d, failed %d, undecided (deadline) %d.\n", (int)p->nTgChecks, (int)p->nTgFailed, (int)p->nTgUndecided );
    if ( p->nIdChecks )
        Abc_Print( 1, "Lemma id checks: %d, shared ids %d, new ids for lemmas with a live source %d.\n", (int)p->nIdChecks, (int)p->nIdShared, (int)p->nIdFresh );
    Abc_Print( 1, "Solver propagations = %.1f M (%.1f M/sec). Conflicts = %.2f M. Level restarts = %d. Learnt cleanups = %d (%d removed nothing, %.2f sec).\n",
        p->nProps / 1e6, timeTotal > 0 ? p->nProps / 1e6 / ((double)timeTotal / CLOCKS_PER_SEC) : 0.0, p->nConflicts / 1e6, p->nLevelRestarts,
        (int)p->nCleanL, (int)p->nCleanLNone, (double)p->timeCleanL / CLOCKS_PER_SEC );
    Abc_Print( 1, "Propagation queries: %d (skipped %d). Propagation to inf: %d (skipped %d; promoted %d of %d trials, %d by time generalization). CTIs dropped: %d. Semantically contained obligations: %d.\n",
        (int)p->nPropCalls, (int)p->nPropSkipped, (int)p->nPropInfCalls, (int)p->nPropInfSkipped, (int)p->nInfPromoted, (int)p->nInfPromoteCalls, (int)p->nInfPromotedTg, (int)p->nCtiKilled, (int)p->nSemContained );
    Abc_Print( 1, "Lifting: %d calls, average size in the cone = %.1f, after flipping = %.1f, after simulation = %.1f (%d not reproduced, %d cut by the deadline), after the SAT core = %.1f.\n",
        (int)p->nLiftCalls, p->nLiftCalls ? 1.0 * p->nLiftCone / p->nLiftCalls : 0.0, p->nLiftCalls ? 1.0 * p->nLiftFlip / p->nLiftCalls : 0.0,
        p->nLiftCalls ? 1.0 * p->nLiftSim / p->nLiftCalls : 0.0, (int)p->nLiftSimFail, (int)p->nLiftSimCut, p->nLiftCalls ? 1.0 * p->nLiftCore / p->nLiftCalls : 0.0 );
    Abc_Print( 1, "Average cube length: obligation = %.1f, MIC input = %.1f, lemma = %.1f. Literal drops: %d ok, %d failed (%.1f%%). Downs = %d. CTGs blocked = %d.\n",
        p->nObls ? 1.0 * p->nOblLits / p->nObls : 0.0, p->nMics ? 1.0 * p->nMicLits / p->nMics : 0.0, p->nLemmas ? 1.0 * p->nLemmaLits / p->nLemmas : 0.0,
        (int)p->nMicDropOk, (int)p->nMicDropFail, (p->nMicDropOk + p->nMicDropFail) ? 100.0 * p->nMicDropOk / (p->nMicDropOk + p->nMicDropFail) : 0.0,
        (int)p->nDowns, (int)p->nCtgsBlocked );
    Abc_Print( 1, "Plain downs: %d queries, %d proved after joins. Queries canceled by the slice overrun limit: %d.\n", (int)p->nDownQueries, (int)p->nDownJoined, p->nQueryCuts );
    if ( p->pPars->fUseAbs )
        Abc_Print( 1, "Abstraction: %d of %d flops. Spurious counterexamples = %d (by simulation %d). Refined flops = %d (fixups = %d, stale chains = %d). Cleaned flops = %d. Checks cut by the deadline = %d.\n",
            p->nAbsFlops, p->nRegs, p->nAbsCexes, p->nAbsXsimRefs, p->nAbsRefined, p->nAbsFixups, p->nAbsStale, p->nAbsCleaned, p->nAbsCut );
    ABC_PRTP( "Bad states  ", p->timeGetBad,  timeTotal );
    ABC_PRTP( "Abstraction ", p->timeAbs,     timeTotal );
    ABC_PRTP( "Blocking    ", p->timeBlocked, timeTotal );
    ABC_PRTP( "Predecessors", p->timeGetPred, timeTotal );
    ABC_PRTP( "MIC         ", p->timeMic,     timeTotal );
    ABC_PRTP( "Pushing     ", p->timePush,    timeTotal );
    ABC_PRTP( "Propagation ", p->timeProp,    timeTotal );
    ABC_PRTP( "Prop to inf ", p->timePropInf, timeTotal );
    ABC_PRTP( "Lifting, all", p->timeLift,    timeTotal );
    ABC_PRTP( "  simulation", p->timeLiftSim, timeTotal );
    ABC_PRTP( "TOTAL       ", timeTotal,      timeTotal );
    if ( p->fAlternate || p->timeRun < Abc_Clock() - p->timeStart - CLOCKS_PER_SEC / 10 )
        Abc_Print( 1, "(the total is the time inside this run; %.2f sec elapsed in all runs)\n", (double)(Abc_Clock() - p->timeStart) / CLOCKS_PER_SEC );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
