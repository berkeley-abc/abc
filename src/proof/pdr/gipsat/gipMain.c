/**************************************************************************************************
GipSAT -- C port of the GipSAT solver from the rIC3 model checker (https://github.com/gipsyh/rIC3),
ported from rIC3 v1.5.2-60-g4a97bec, src/gipsat/.
Copyright (C) 2023 - Present, Yuheng Su <gipsyh.icu@gmail.com>. All rights reserved.
Ported to C for ABC by Wish, 2026.

rIC3 is distributed under the GNU General Public License v3. This port is distributed as part of
ABC under the ABC license (see copyright.txt in the ABC root) with the explicit permission of the
rIC3 author.
**************************************************************************************************/

#include <limits.h>
#include "gipsat.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

static int Gip_SolverSimplifyClause( Gip_Solver_t * p, int * pLits, int nLits );

/**Function*************************************************************

  Synopsis    [Reads an experimental setting for a solver owned by pdr2.]

  Description []

***********************************************************************/
// Only pdr2-created contexts consult experimental solver settings.
static inline const char * Gip_SolverOption( Gip_Solver_t * p, const char * pName )
{
    return p->pCtx->fPdr2 ? Gip_OptionGet(pName) : NULL;
}


/**Function*************************************************************

  Synopsis    [Places the initial watch lists in literal order in one allocation.]

  Description [Watch order is preserved. Lists that outgrow their initial
  slice move to a separately owned allocation.]

  SideEffects []

***********************************************************************/
static void Gip_SolverPackWatches( Gip_Solver_t * p )
{
    size_t Total = 0, Off = 0;
    int i;
    assert(!p->pWatchData);
    for ( i = 0; i < 2*p->nVarsAlloc; ++i )
    {
        int Cap = p->pWatchers[i].nCap;
        if ( (size_t)Cap > (size_t)-1 / sizeof(Gip_Wat_t) - Total ) return;
        Total += Cap;
    }
    if ( !Total ) return;
    p->pWatchData = ABC_ALLOC(Gip_Wat_t, Total);
    if ( !p->pWatchData ) return;
    for ( i = 0; i < 2*p->nVarsAlloc; ++i )
    {
        Gip_WVec_t * pW = &p->pWatchers[i];
        if ( !pW->nCap ) continue;
        memcpy(p->pWatchData + Off, pW->pArray, sizeof(Gip_Wat_t) * pW->nSize);
        ABC_FREE(pW->pArray);
        pW->pArray = p->pWatchData + Off;
        Off += pW->nCap;
        pW->nCap += INT_MIN;
    }
}

/**Function*************************************************************

  Synopsis    [Allocates an eager or demand-loaded solver over an immutable circuit context.]

  Description []

***********************************************************************/
static Gip_Solver_t * Gip_SolverNewInt( Gip_Ctx_t * pCtx, int fLazy )
{
    Gip_Solver_t * p = ABC_CALLOC( Gip_Solver_t, 1 );
    int i, c, Conflict;
    p->pCtx = pCtx;
    p->fInlineBinary = Gip_SolverOption(p, "PDR2_WATCH_BINARY") && atoi(Gip_SolverOption(p, "PDR2_WATCH_BINARY")) > 0;
    if ( Gip_SolverOption(p, "PDR2_WATCH_AHEAD") )
        p->nWatchAhead = Abc_MaxInt(0, Abc_MinInt(32, atoi(Gip_SolverOption(p, "PDR2_WATCH_AHEAD"))));
    p->nVars = pCtx->nVars;
    p->constrainAct = pCtx->nVars;
    p->nVarsAlloc = pCtx->nVars + 1;
    p->pValue  = ABC_ALLOC( char, p->nVarsAlloc );
    p->pLitVal = ABC_ALLOC( char, 2 * p->nVarsAlloc );
    p->pPhase  = ABC_ALLOC( char, p->nVarsAlloc );
    p->pMark   = ABC_CALLOC( char, p->nVarsAlloc );
    p->pRemFrame = ABC_ALLOC( int, p->nVarsAlloc );
    p->pLevel  = ABC_CALLOC( unsigned, p->nVarsAlloc );
    p->pReason = ABC_ALLOC( int, p->nVarsAlloc );
    p->pTag0   = ABC_ALLOC( int, p->nVarsAlloc );
    for ( i = 0; i < p->nVarsAlloc; i++ )
    {
        p->pValue[i]  = GIP_NONE;
        p->pLitVal[2*i] = p->pLitVal[2*i+1] = GIP_NONE;
        p->pPhase[i]  = GIP_NONE;
        p->pReason[i] = GIP_CREF_NONE;
        p->pTag0[i]   = GIP_FRAME_INF;
    }
    p->iCoreFrame = p->iAnaFrame = p->iTrivialFrame = GIP_FRAME_INF;
    p->pWatchers = ABC_CALLOC( Gip_WVec_t, 2 * p->nVarsAlloc );
    p->fActLast = Gip_SolverOption(p, "PDR2_ACTLAST") && atoi(Gip_SolverOption(p, "PDR2_ACTLAST"));
    if ( (Gip_SolverOption(p, "PDR2_SKIPWATCH") && atoi(Gip_SolverOption(p, "PDR2_SKIPWATCH"))) ||
         (Gip_SolverOption(p, "PDR2_PARTWATCH") && atoi(Gip_SolverOption(p, "PDR2_PARTWATCH"))) )
    {
        p->pSkipWatch = ABC_CALLOC( unsigned, 2 * p->nVarsAlloc );
        p->nWatchEpoch = 1;
        p->fCheckSkipWatch = Gip_SolverOption(p, "PDR2_SKIPWATCH_CHECK") != NULL;
    }
    if ( Gip_SolverOption(p, "PDR2_PARTWATCH") && atoi(Gip_SolverOption(p, "PDR2_PARTWATCH")) )
    {
        p->pActiveWatch = ABC_CALLOC( int, 2 * p->nVarsAlloc );
        p->fCheckSkipWatch |= Gip_SolverOption(p, "PDR2_PARTWATCH_CHECK") != NULL;
    }
    Gip_CdbInit( &p->Cdb );
    Gip_VsidsInit( &p->Vsids, p->nVarsAlloc );
    Gip_DomainInit( &p->Domain, p->nVarsAlloc, pCtx->varConst );
    if ( Gip_SolverOption(p, "PDR2_WATCH_STATE") && atoi(Gip_SolverOption(p, "PDR2_WATCH_STATE")) )
    {
        p->Domain.Set.pValues = p->pValue;
        p->Domain.Set.pHas[pCtx->varConst] = 1 + p->pValue[pCtx->varConst];
    }
    else if ( Gip_SolverOption(p, "PDR2_PACKEDDOM") && atoi(Gip_SolverOption(p, "PDR2_PACKEDDOM")) )
    {
        p->Domain.Set.pLitFlags = p->pLitVal;
        p->pLitVal[2*pCtx->varConst] |= 4;
        p->pLitVal[2*pCtx->varConst+1] |= 4;
    }
    Gip_LitSetInit( &p->UnsatCore, p->nVarsAlloc );
    p->vTrail      = Vec_IntAlloc( 1000 );
    p->vPosInTrail = Vec_IntAlloc( 100 );
    p->vClear      = Vec_IntAlloc( 100 );
    p->vAnaStack   = Vec_IntAlloc( 100 );
    p->vLearntCls  = Vec_IntAlloc( 100 );
    p->vSimpCls    = Vec_IntAlloc( 100 );
    p->vSeeds      = Vec_IntAlloc( 100 );
    p->vAssump     = Vec_IntAlloc( 16 );
    p->nRecycleMode = Gip_SolverOption(p, "PDR2_RECYCLE") ? atoi(Gip_SolverOption(p, "PDR2_RECYCLE")) & 3 : 0;
    if ( p->nRecycleMode )
    {
        p->nRecycleCopies = Gip_SolverOption(p, "PDR2_RECYCLE_N") ? Abc_MaxInt(1, Abc_MinInt(8, atoi(Gip_SolverOption(p, "PDR2_RECYCLE_N")))) : 1;
        p->nRecycleWidth = Gip_SolverOption(p, "PDR2_RECYCLE_WIDTH") ? Abc_MaxInt(2, Abc_MinInt(512, atoi(Gip_SolverOption(p, "PDR2_RECYCLE_WIDTH")))) : 128;
        p->fRecycleCheck = Gip_SolverOption(p, "PDR2_RECYCLE_CHECK") != NULL;
        p->vRecycleCond = Vec_IntAlloc( 100 );
        p->vRecycleQueue = Vec_IntAlloc( 100 );
        p->vRecycleTmp = Vec_IntAlloc( 100 );
    }
    p->fJustify = Gip_SolverOption(p, "PDR2_JUSTIFY") && atoi(Gip_SolverOption(p, "PDR2_JUSTIFY"));
    p->fInputDecisions = Gip_SolverOption(p, "PDR2_INPUT_DECISIONS") && atoi(Gip_SolverOption(p, "PDR2_INPUT_DECISIONS"));
    p->fInputQueue = Gip_SolverOption(p, "PDR2_INPUT_QUEUE") && atoi(Gip_SolverOption(p, "PDR2_INPUT_QUEUE"));
    p->nInputConfLimit = Gip_SolverOption(p, "PDR2_INPUT_CONFS") ? Abc_MaxInt(0, atoi(Gip_SolverOption(p, "PDR2_INPUT_CONFS"))) : 0;
    p->nInputMillis = Gip_SolverOption(p, "PDR2_INPUT_MSEC") ? Abc_MaxInt(0, Abc_MinInt(10000, atoi(Gip_SolverOption(p, "PDR2_INPUT_MSEC")))) : 0;
    if ( p->fJustify )
    {
        p->pJustSkip = ABC_CALLOC( char, p->nVarsAlloc );
        p->vJustSkip = Vec_IntAlloc( 100 );
    }
    p->nLastNumLemma = 1000;
    p->nCleanIdle = -1;
    if ( fLazy )
    {
        p->pLoaded = ABC_CALLOC( char, p->nVars );
        p->vLoad = Vec_IntAlloc( 100 );
        Gip_SolverLoadVar( p, pCtx->varConst );
    }
    else
        for ( c = 0; c < pCtx->pCnf->nClauses; c++ )
            Gip_SolverAddClauseInner( p, pCtx->pCnf->pClauses[c],
                (int)(pCtx->pCnf->pClauses[c+1] - pCtx->pCnf->pClauses[c]), GIP_CLA_TRANS );
    Conflict = Gip_SolverPropagate( p );
    assert( Conflict == GIP_CREF_NONE );
    assert( !p->fTrivialUnsat );
    if ( !fLazy && Gip_SolverOption(p, "PDR2_WATCH_PACK") && atoi(Gip_SolverOption(p, "PDR2_WATCH_PACK")) )
        Gip_SolverPackWatches(p);
    return p;
}

/**Function*************************************************************

  Synopsis    [Creates a solver over the shared context.]

  Description [Loads the entire static CNF as transition clauses.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gip_Solver_t * Gip_SolverNew( Gip_Ctx_t * pCtx )
{
    return Gip_SolverNewInt( pCtx, 0 );
}

/**Function*************************************************************

  Synopsis    [Creates a solver that loads circuit clauses when their variables enter a query.]

  Description []

***********************************************************************/
Gip_Solver_t * Gip_SolverNewLazy( Gip_Ctx_t * pCtx )
{
    return Gip_SolverNewInt( pCtx, 1 );
}

/**Function*************************************************************

  Synopsis    [Duplicates an optional solver array.]

  Description []

***********************************************************************/
static void * Gip_CloneArray( const void * pSrc, size_t nBytes )
{
    void * pDst;
    if ( !pSrc || !nBytes ) return NULL;
    pDst = ABC_ALLOC( char, nBytes );
    memcpy( pDst, pSrc, nBytes );
    return pDst;
}

/**Function*************************************************************

  Synopsis    [Copies a level-zero solver with its clause database and search heuristics.]

  Description []

***********************************************************************/
// Copy the actual root solver, including clause/watch order, learned clauses,
// phases, and heuristic queues. Only the immutable context and the caller's
// lemma-to-frame table remain shared. No temporary activation or assignment
// above level zero may survive into the new solver.
Gip_Solver_t * Gip_SolverCloneRoot( Gip_Solver_t * pSrc )
{
    Gip_Solver_t * p = ABC_ALLOC( Gip_Solver_t, 1 );
    int i, n = pSrc->nVarsAlloc;
    assert( !pSrc->pShared && !pSrc->fTempDomain );
    assert( Gip_SolverLevelOf(pSrc) == 0 && Vec_IntSize(pSrc->Cdb.vTemp) == 0 );
    assert( pSrc->pValue[pSrc->constrainAct] == GIP_NONE );
    *p = *pSrc;
    p->Batch.vClause = p->Batch.vPrevious = NULL;
    p->Batch.nResumed = 0;
    p->pWatchData = NULL;
    p->pDumpFile = NULL;
    p->vSharedDomain = NULL;
    p->pLoaded = (char *)Gip_CloneArray( pSrc->pLoaded, pSrc->nVars );
    p->vLoad = pSrc->vLoad ? Vec_IntDup(pSrc->vLoad) : NULL;
    p->Cdb.Alloc.pData = ABC_ALLOC( unsigned, pSrc->Cdb.Alloc.nCap );
    memcpy( p->Cdb.Alloc.pData, pSrc->Cdb.Alloc.pData, sizeof(unsigned) * pSrc->Cdb.Alloc.nSize );
    p->Cdb.vTrans = Vec_IntDup( pSrc->Cdb.vTrans );
    p->Cdb.vLemmas = Vec_IntDup( pSrc->Cdb.vLemmas );
    p->Cdb.vLearnt = Vec_IntDup( pSrc->Cdb.vLearnt );
    p->Cdb.vTemp = Vec_IntDup( pSrc->Cdb.vTemp );
    p->pWatchers = ABC_CALLOC( Gip_WVec_t, 2*n );
    for ( i = 0; i < 2*n; i++ )
    {
        p->pWatchers[i] = pSrc->pWatchers[i];
        p->pWatchers[i].nCap &= INT_MAX;
        p->pWatchers[i].pArray = p->pWatchers[i].nCap ? ABC_ALLOC( Gip_Wat_t, p->pWatchers[i].nCap ) : NULL;
        if ( pSrc->pWatchers[i].nSize )
            memcpy( p->pWatchers[i].pArray, pSrc->pWatchers[i].pArray, sizeof(Gip_Wat_t) * pSrc->pWatchers[i].nSize );
    }
    if ( pSrc->pWatchData ) Gip_SolverPackWatches(p);
    p->pValue = (char *)Gip_CloneArray( pSrc->pValue, n );
    p->pLitVal = (char *)Gip_CloneArray( pSrc->pLitVal, 2*n );
    p->pSkipWatch = (unsigned *)Gip_CloneArray( pSrc->pSkipWatch, sizeof(unsigned)*2*n );
    p->pActiveWatch = (int *)Gip_CloneArray( pSrc->pActiveWatch, sizeof(int)*2*n );
    p->pPhase = (char *)Gip_CloneArray( pSrc->pPhase, n );
    p->pMark = (char *)Gip_CloneArray( pSrc->pMark, n );
    p->pRemFrame = (int *)Gip_CloneArray( pSrc->pRemFrame, sizeof(int)*n );
    p->pLevel = (unsigned *)Gip_CloneArray( pSrc->pLevel, sizeof(unsigned)*n );
    p->pReason = (int *)Gip_CloneArray( pSrc->pReason, sizeof(int)*n );
    p->pTag0 = (int *)Gip_CloneArray( pSrc->pTag0, sizeof(int)*n );
    p->vTrail = Vec_IntDup( pSrc->vTrail );
    p->vPosInTrail = Vec_IntDup( pSrc->vPosInTrail );
    p->vClear = Vec_IntDup( pSrc->vClear );
    p->vAnaStack = Vec_IntDup( pSrc->vAnaStack );
    p->vLearntCls = Vec_IntDup( pSrc->vLearntCls );
    p->vSimpCls = Vec_IntDup( pSrc->vSimpCls );
    p->vSeeds = Vec_IntDup( pSrc->vSeeds );
    p->vAssump = Vec_IntDup( pSrc->vAssump );
    p->Domain.Set.vSet = Vec_IntDup( pSrc->Domain.Set.vSet );
    p->Domain.Set.pHas = (char *)Gip_CloneArray( pSrc->Domain.Set.pHas, n );
    p->Domain.Set.pLitFlags = pSrc->Domain.Set.pLitFlags ? p->pLitVal : NULL;
    p->Domain.Set.pValues = pSrc->Domain.Set.pValues ? p->pValue : NULL;
    p->UnsatCore.vSet = Vec_IntDup( pSrc->UnsatCore.vSet );
    p->UnsatCore.pHas = (char *)Gip_CloneArray( pSrc->UnsatCore.pHas, 2*n );
    p->Vsids.Act.pAct = (double *)Gip_CloneArray( pSrc->Vsids.Act.pAct, sizeof(double)*n );
    p->Vsids.Act.BktHeap.vHeap = Vec_IntDup( pSrc->Vsids.Act.BktHeap.vHeap );
    p->Vsids.Act.BktHeap.pPos = (int *)Gip_CloneArray( pSrc->Vsids.Act.BktHeap.pPos, sizeof(int)*n );
    p->Vsids.Act.vBktTable = Vec_IntDup( pSrc->Vsids.Act.vBktTable );
    p->Vsids.Heap.vHeap = Vec_IntDup( pSrc->Vsids.Heap.vHeap );
    p->Vsids.Heap.pPos = (int *)Gip_CloneArray( pSrc->Vsids.Heap.pPos, sizeof(int)*n );
    p->Vsids.Bucket.pInBucket = (char *)Gip_CloneArray( pSrc->Vsids.Bucket.pInBucket, n );
    p->Vsids.Bucket.vBuckets = Vec_PtrAlloc( Vec_PtrSize(pSrc->Vsids.Bucket.vBuckets) );
    for ( i = 0; i < Vec_PtrSize(pSrc->Vsids.Bucket.vBuckets); i++ )
    {
        Vec_Int_t * v = (Vec_Int_t *)Vec_PtrEntry( pSrc->Vsids.Bucket.vBuckets, i );
        Vec_PtrPush( p->Vsids.Bucket.vBuckets, v ? Vec_IntDup(v) : NULL );
    }
    p->pJustSkip = (char *)Gip_CloneArray( pSrc->pJustSkip, n );
    p->vJustSkip = pSrc->vJustSkip ? Vec_IntDup(pSrc->vJustSkip) : NULL;
    p->vRecycleCond = pSrc->vRecycleCond ? Vec_IntDup(pSrc->vRecycleCond) : NULL;
    p->vRecycleQueue = pSrc->vRecycleQueue ? Vec_IntDup(pSrc->vRecycleQueue) : NULL;
    p->vRecycleTmp = pSrc->vRecycleTmp ? Vec_IntDup(pSrc->vRecycleTmp) : NULL;
    p->Stats.nRecycleTry = p->Stats.nRecycled = 0;
    return p;
}

/**Function*************************************************************

  Synopsis    [Imports frame-independent information from an established solver.]

  Description []

***********************************************************************/
// The destination already contains the source's invariant lemmas. Import only
// facts/clauses whose proofs have no finite-frame dependency, never activation
// literals. Search state is heuristic; assignments above level zero are not copied.
int Gip_SolverWarmStartMode( Gip_Solver_t * p, Gip_Solver_t * pSrc, int Mode )
{
    int i, j, Lit, Var, Cref, New, nLits, fTemporary, nCopied = 0;
    int * pLits;
    assert( p->pCtx == pSrc->pCtx && p->nVarsAlloc == pSrc->nVarsAlloc );
    assert( Gip_SolverLevelOf(p) == 0 );
    if ( p->fTrivialUnsat || pSrc->fTrivialUnsat )
        return 0;
    if ( Mode & 4 )
    {
    Vec_IntForEachEntry( pSrc->vTrail, Lit, i )
    {
        Var = Gip_LitVar( Lit );
        if ( Var == pSrc->constrainAct || pSrc->pLevel[Var] != 0 ||
             pSrc->pValue[Var] == GIP_NONE || pSrc->pTag0[Var] != GIP_FRAME_INF ||
             Gip_SolverLitValue(p, Lit) == GIP_TRUE )
            continue;
        Gip_SolverLoadVar( p, Var );
        Gip_SolverAddClauseInner( p, &Lit, 1, GIP_CLA_LEARNT );
        nCopied++;
    }
    Vec_IntForEachEntry( pSrc->Cdb.vLearnt, Cref, i )
    {
        if ( Gip_ClaIsRemoved(&pSrc->Cdb.Alloc, Cref) ||
             Gip_SolverClaFrame(pSrc, Cref) != GIP_FRAME_INF )
            continue;
        pLits = Gip_ClaLits( &pSrc->Cdb.Alloc, Cref );
        nLits = Gip_ClaLen( &pSrc->Cdb.Alloc, Cref );
        fTemporary = 0;
        for ( j = 0; j < nLits; j++ )
            fTemporary |= Gip_LitVar(pLits[j]) == pSrc->constrainAct;
        if ( fTemporary )
            continue;
        for ( j = 0; j < nLits; j++ )
            Gip_SolverLoadVar( p, Gip_LitVar(pLits[j]) );
        New = Gip_SolverAddClauseInner( p, pLits, nLits, GIP_CLA_LEARNT );
        if ( New != GIP_CREF_NONE )
        {
            Gip_ClaSetAct( &p->Cdb.Alloc, New, Gip_ClaAct(&pSrc->Cdb.Alloc, Cref) );
            nCopied++;
        }
    }
    p->Cdb.actInc = pSrc->Cdb.actInc;
    }
    if ( Mode & 1 )
        memcpy( p->pPhase, pSrc->pPhase, (size_t)p->nVarsAlloc );
    if ( Mode & 2 )
    {
    memcpy( p->Vsids.Act.pAct, pSrc->Vsids.Act.pAct, sizeof(double) * p->nVarsAlloc );
    p->Vsids.Act.actInc = pSrc->Vsids.Act.actInc;
    Gip_HeapClear( &p->Vsids.Act.BktHeap );
    Vec_IntAppend( p->Vsids.Act.BktHeap.vHeap, pSrc->Vsids.Act.BktHeap.vHeap );
    memcpy( p->Vsids.Act.BktHeap.pPos, pSrc->Vsids.Act.BktHeap.pPos, sizeof(int) * p->nVarsAlloc );
    Vec_IntClear( p->Vsids.Act.vBktTable );
    Vec_IntAppend( p->Vsids.Act.vBktTable, pSrc->Vsids.Act.vBktTable );
    }
    return nCopied;
}

/**Function*************************************************************

  Synopsis    [Seeds a new solver with frame-independent clauses and search state.]

  Description []

***********************************************************************/
int Gip_SolverWarmStart( Gip_Solver_t * p, Gip_Solver_t * pSrc )
{
    return Gip_SolverWarmStartMode( p, pSrc, 7 );
}

/**Function*************************************************************

  Synopsis    [Loads the defining clauses of a variable and its transitive dependencies.]

  Description []

***********************************************************************/
// Every omitted transition clause defines a function of earlier AIG signals.
// Load the entire dependency cone before constraining a signal, so a model of
// the loaded clauses always extends to a model of the full transition relation.
// This must run at level zero, including for permanent property units.
void Gip_SolverLoadVar( Gip_Solver_t * p, int Var )
{
    Gip_Ctx_t * pCtx = p->pCtx;
    Cnf_Dat_t * pCnf = pCtx->pCnf;
    int v, ObjId, c, i;
    if ( !p->pLoaded || Var >= pCtx->pCnf->nVars || p->pLoaded[Var] )
        return;
    assert( Gip_SolverLevelOf(p) == 0 );
    Vec_IntClear( p->vLoad );
    Vec_IntPush( p->vLoad, Var );
    while ( Vec_IntSize(p->vLoad) && !p->fTrivialUnsat )
    {
        v = Vec_IntPop( p->vLoad );
        if ( p->pLoaded[v] )
            continue;
        p->pLoaded[v] = 1;
        for ( i = pCtx->pDepOffset[v]; i < pCtx->pDepOffset[v+1]; i++ )
            if ( !p->pLoaded[pCtx->pDepData[i]] )
                Vec_IntPush( p->vLoad, pCtx->pDepData[i] );
        ObjId = pCtx->pVar2Obj ? pCtx->pVar2Obj[v] : v;
        for ( c = pCnf->pObj2Clause[ObjId]; !p->fTrivialUnsat && pCnf->pObj2Count[ObjId] > 0 && c < pCnf->pObj2Clause[ObjId] + pCnf->pObj2Count[ObjId]; c++ )
            Gip_SolverAddClauseInner( p, pCnf->pClauses[c],
                (int)(pCnf->pClauses[c+1] - pCnf->pClauses[c]), GIP_CLA_TRANS );
    }
}

/**Function*************************************************************

  Synopsis    [Frees the solver.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gip_SolverFree( Gip_Solver_t * p )
{
    int i;
    if ( p == NULL )
        return;
    Gip_SolverStopBatch( p );
    if ( p->pActiveWatch && Gip_SolverOption(p, "PDR2_PARTWATCH_STATS") )
        Abc_Print(1, "Watch partitions: %.0f visits, %.0f rebuilt, skipped %.0f of %.0f entries.\n",
            (double)p->nPartWatchLists, (double)p->nPartWatchRebuilt,
            (double)p->nPartWatchSkipped, (double)p->nPartWatchEntries);
    for ( i = 0; i < 2 * p->nVarsAlloc; i++ )
        if ( p->pWatchers[i].nCap >= 0 ) ABC_FREE( p->pWatchers[i].pArray );
    ABC_FREE( p->pWatchData );
    ABC_FREE( p->pWatchers );
    ABC_FREE( p->pSkipWatch );
    ABC_FREE( p->pActiveWatch );
    ABC_FREE( p->pValue );
    ABC_FREE( p->pLitVal );
    ABC_FREE( p->pPhase );
    ABC_FREE( p->pMark );
    ABC_FREE( p->pRemFrame );
    ABC_FREE( p->pLevel );
    ABC_FREE( p->pReason );
    ABC_FREE( p->pTag0 );
    ABC_FREE( p->pLoaded );
    Vec_IntFreeP( &p->vLoad );
    Gip_CdbFree( &p->Cdb );
    Gip_VsidsFree( &p->Vsids );
    Gip_DomainFree( &p->Domain );
    Gip_LitSetFree( &p->UnsatCore );
    Vec_IntFreeP( &p->vTrail );
    Vec_IntFreeP( &p->vPosInTrail );
    Vec_IntFreeP( &p->vClear );
    Vec_IntFreeP( &p->vAnaStack );
    Vec_IntFreeP( &p->vLearntCls );
    Vec_IntFreeP( &p->vSimpCls );
    Vec_IntFreeP( &p->vSeeds );
    Vec_IntFreeP( &p->vAssump );
    Vec_IntFreeP( &p->vJustSkip );
    ABC_FREE( p->pJustSkip );
    Vec_IntFreeP( &p->vRecycleCond );
    Vec_IntFreeP( &p->vRecycleQueue );
    Vec_IntFreeP( &p->vRecycleTmp );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Queues permanent consequences of a temporary query constraint.]

  Description []

***********************************************************************/
// Let the single query constraint be C = (c1 OR ... OR cn). A clause
// L OR !activation learned under activation => C proves C => L. Therefore
// each L OR !ci is an unconditional consequence of the permanent formula.
// Defer insertion until the query model/core has been consumed and the
// temporary clauses have been removed. The original proof's frame tag stays.
void Gip_SolverSaveRecycled( Gip_Solver_t * p, int * pLits, int nLits, int Frame )
{
    int i, j, Act = -1, Count;
    if ( !p->nRecycleMode || nLits < 1 || nLits > p->nRecycleWidth ) return;
    for ( i = 0; i < nLits; i++ )
        if ( Gip_LitVar(pLits[i]) == p->constrainAct )
        {
            if ( !Gip_LitCompl(pLits[i]) || Act != -1 ) return;
            Act = i;
        }
    if ( Act != -1 && (!Vec_IntSize(p->vRecycleCond) || Vec_IntSize(p->vRecycleCond) > p->nRecycleWidth) ) return;
    Count = Act == -1 ? 1 : Abc_MinInt(p->nRecycleCopies, Vec_IntSize(p->vRecycleCond));
    for ( j = 0; j < Count; j++ )
    {
        Vec_IntPush( p->vRecycleQueue, nLits );
        Vec_IntPush( p->vRecycleQueue, Frame );
        for ( i = 0; i < nLits; i++ )
            Vec_IntPush( p->vRecycleQueue, i == Act ? Gip_LitNot(Vec_IntEntry(p->vRecycleCond, j)) : pLits[i] );
    }
}

/**Function*************************************************************

  Synopsis    [Installs queued consequences after the temporary query has been removed.]

  Description []

***********************************************************************/
void Gip_SolverFlushRecycled( Gip_Solver_t * p )
{
    int Off = 0, Size, Frame, Cref, Before, * pLits;
    if ( !p->nRecycleMode ) return;
    assert( Gip_SolverLevelOf(p) == 0 && !Vec_IntSize(p->Cdb.vTemp) );
    while ( Off < Vec_IntSize(p->vRecycleQueue) && !p->fTrivialUnsat )
    {
        Size = Vec_IntEntry(p->vRecycleQueue, Off++);
        Frame = Vec_IntEntry(p->vRecycleQueue, Off++);
        pLits = Vec_IntArray(p->vRecycleQueue) + Off;
        Off += Size;
        if ( p->fRecycleCheck )
        {
            Gip_Solver_t * pCheck;
            Vec_Int_t * vNeg = Vec_IntAlloc( Size );
            int i, Ret, Temp = p->fTempDomain;
            p->fTempDomain = 0;
            pCheck = Gip_SolverCloneRoot( p );
            p->fTempDomain = Temp;
            pCheck->nRecycleMode = 0;
            pCheck->TimeLimit = 0;
            pCheck->nPropLimit = pCheck->nConfLimit = 0;
            pCheck->pFuncStop = NULL;
            for ( i = 0; i < Size; i++ ) Vec_IntPush( vNeg, Gip_LitNot(pLits[i]) );
            Ret = Gip_SolverSolve( pCheck, Vec_IntArray(vNeg), Size, NULL, NULL, 0, -1 );
            if ( Ret != GIP_UNSAT ) Abc_Print( 1, "RECYCLE CHECK FAILED: proposed permanent clause is not implied.\n" );
            assert( Ret == GIP_UNSAT );
            Vec_IntFree( vNeg );
            Gip_SolverFree( pCheck );
        }
        Before = Vec_IntSize(p->vTrail);
        Cref = Gip_SolverAddClauseTag( p, pLits, Size, GIP_CLA_LEARNT, (unsigned)Frame << 1 );
        p->Stats.nRecycleTry++;
        if ( Cref != GIP_CREF_NONE ) Gip_CdbBump( &p->Cdb, Cref );
        p->Stats.nRecycled += Cref != GIP_CREF_NONE || Vec_IntSize(p->vTrail) > Before;
    }
    Vec_IntClear( p->vRecycleQueue );
}

/**Function*************************************************************

  Synopsis    [Level-0 clause simplification.]

  Description [Sorts literals, drops duplicates and false literals,
  detects tautologies and satisfied clauses. Fills p->vSimpCls. Returns
  0 if the clause should be dropped; an empty result sets fTrivialUnsat.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Gip_SolverSimplifyClause( Gip_Solver_t * p, int * pLits, int nLits )
{
    int i, k = 0, prev = -1;
    assert( Gip_SolverLevelOf(p) == 0 );
    Vec_IntClear( p->vSimpCls );
    for ( i = 0; i < nLits; i++ )
        Vec_IntPush( p->vSimpCls, pLits[i] );
    Vec_IntSort( p->vSimpCls, 0 );
    for ( i = 0; i < Vec_IntSize(p->vSimpCls); i++ )
    {
        int Lit = Vec_IntEntry( p->vSimpCls, i );
        int v;
        if ( Lit == prev )
            continue;
        if ( prev != -1 && Lit == Gip_LitNot(prev) )
            return 0;
        prev = Lit;
        v = Gip_SolverLitValue( p, Lit );
        if ( v == GIP_TRUE )
            return 0;
        if ( v == GIP_FALSE )
            continue;
        Vec_IntWriteEntry( p->vSimpCls, k++, Lit );
    }
    Vec_IntShrink( p->vSimpCls, k );
    if ( k == 0 )
    {
        p->fTrivialUnsat = 1;
        return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Simplifies and attaches a clause; returns CRef or GIP_CREF_NONE.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gip_SolverAddClauseTag( Gip_Solver_t * p, int * pLits, int nLits, int Kind, unsigned TagWord )
{
    int i, Lit, Conflict, Frame = GIP_FRAME_INF, fStripped = 0;
    // literals false at level 0 are dropped: the clause then depends on those facts
    for ( i = 0; i < nLits; i++ )
        if ( Gip_SolverLitValue(p, pLits[i]) == GIP_FALSE )
        {
            fStripped = 1;
            if ( p->pTag0[Gip_LitVar(pLits[i])] < Frame )
                Frame = p->pTag0[Gip_LitVar(pLits[i])];
        }
    if ( !Gip_SolverSimplifyClause( p, pLits, nLits ) )
    {
        // an empty clause (every literal false at level 0) is a permanent contradiction that
        // depends on the clause's own frame and on the facts that falsified its literals
        if ( Vec_IntSize(p->vSimpCls) == 0 )
        {
            int Own = (TagWord & 1) ? (p->vLemFrame ? Vec_IntEntry(p->vLemFrame, (int)(TagWord >> 1)) : GIP_FRAME_INF) : (int)(TagWord >> 1);
            assert( p->fTrivialUnsat );
            if ( Own < p->iTrivialFrame )
                p->iTrivialFrame = Own;
            if ( Frame < p->iTrivialFrame )
                p->iTrivialFrame = Frame;
        }
        return GIP_CREF_NONE;
    }
    Vec_IntForEachEntry( p->vSimpCls, Lit, i )
        if ( Gip_LitVar(Lit) == p->constrainAct )
            Kind = GIP_CLA_TEMPORARY;
    if ( fStripped )
    {
        // resolve the tag to a frame value and lower it by the facts used
        int Own = (TagWord & 1) ? (p->vLemFrame ? Vec_IntEntry(p->vLemFrame, (int)(TagWord >> 1)) : GIP_FRAME_INF) : (int)(TagWord >> 1);
        TagWord = (unsigned)(Own < Frame ? Own : Frame) << 1;
    }
    if ( Vec_IntSize(p->vSimpCls) == 1 )
    {
        Lit = Vec_IntEntry( p->vSimpCls, 0 );
        assert( Gip_LitVar(Lit) != p->constrainAct );
        assert( Gip_SolverLitValue(p, Lit) == GIP_NONE );
        Gip_SolverAssign( p, Lit, GIP_CREF_NONE );
        p->pTag0[Gip_LitVar(Lit)] = (TagWord & 1) ? (p->vLemFrame ? Vec_IntEntry(p->vLemFrame, (int)(TagWord >> 1)) : GIP_FRAME_INF) : (int)(TagWord >> 1);
        Conflict = Gip_SolverPropagate( p );
        if ( Conflict != GIP_CREF_NONE )
        {
            p->fTrivialUnsat = 1;
            p->iTrivialFrame = Gip_SolverConflictFrame( p, Conflict );
        }
        return GIP_CREF_NONE;
    }
    return Gip_SolverAttachClauseTag( p, Vec_IntArray(p->vSimpCls), Vec_IntSize(p->vSimpCls), Kind, TagWord );
}
int Gip_SolverAddClauseInner( Gip_Solver_t * p, int * pLits, int nLits, int Kind )
{
    return Gip_SolverAddClauseTag( p, pLits, nLits, Kind, (unsigned)GIP_FRAME_INF << 1 );
}

/**Function*************************************************************

  Synopsis    [Backtracks to level 0 and drops temporaries and local domain.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gip_SolverReset( Gip_Solver_t * p )
{
    Gip_SolverBacktrack( p, 0, 0 );
    Gip_SolverCleanTemporary( p );
    p->fPreparedVsids = 0;
    Gip_DomainReset( &p->Domain );
    assert( !p->fTempDomain );
}

// The cached prefix and its temporary clause belong to this solver and
// this batch. Restarting a batch requires installing the clause again.
void Gip_SolverStartBatch( Gip_Solver_t * p, int nLits )
{
    assert( !p->Batch.vPrevious && p->fTempDomain && !p->pShared );
    p->Batch.vClause = Vec_IntAlloc( nLits );
    p->Batch.vPrevious = Vec_IntAlloc( nLits + 1 );
    p->Batch.nResumed = 0;
}

int Gip_SolverStopBatch( Gip_Solver_t * p )
{
    int nResumed = p->Batch.nResumed;
    Vec_IntFreeP( &p->Batch.vPrevious );
    Vec_IntFreeP( &p->Batch.vClause );
    p->Batch.nResumed = 0;
    return nResumed;
}

/**Function*************************************************************

  Synopsis    [Adds a lemma clause.]

  Description [The only external entry for frame cubes; permanently
  extends the fixed domain with the lemma variables.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gip_SolverAddLemmaId( Gip_Solver_t * p, int * pLits, int nLits, int Id )
{
    int i;
    Gip_SolverReset( p );
    if ( p->pLoaded )
        for ( i = 0; i < nLits; i++ )
            Gip_SolverLoadVar( p, Gip_LitVar(pLits[i]) );
    for ( i = 0; i < nLits; i++ )
        Gip_SolverAddDomain( p, Gip_LitVar(pLits[i]), 1 );
    Gip_SolverAddClauseTag( p, pLits, nLits, GIP_CLA_LEMMA, Id >= 0 ? (((unsigned)Id << 1) | 1) : ((unsigned)GIP_FRAME_INF << 1) );
}
void Gip_SolverAddLemma( Gip_Solver_t * p, int * pLits, int nLits )
{
    Gip_SolverAddLemmaId( p, pLits, nLits, -1 );
}
// the table that maps lemma ids to their current frames (owned by the caller)
void Gip_SolverSetLemFrames( Gip_Solver_t * p, Vec_Int_t * vLemFrame )
{
    p->vLemFrame = vLemFrame;
}

/**Function*************************************************************

  Synopsis    [Starts a query round.]

  Description [Attaches the constraint clauses as temporaries and builds
  the local domain from the seeds. Returns 0 if a constraint clause
  simplifies to a unit (query is UNSAT).]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Gip_SolverNewRound( Gip_Solver_t * p, Vec_Int_t * vSeeds,
                               int ** ppCstCls, int * pnCstLits, int nCst, int fBucket )
{
    int c, i;
    Gip_SolverBacktrack( p, 0, p->fTempDomain );
    Gip_SolverCleanTemporary( p );
    if ( !p->fTrivialUnsat )
    {
        int Conflict = Gip_SolverPropagate( p );
        if ( Conflict != GIP_CREF_NONE )
        {
            p->fTrivialUnsat = 1;
            p->iTrivialFrame = Gip_SolverConflictFrame( p, Conflict );
        }
    }
    if ( p->fTrivialUnsat )
    {
        p->iCoreFrame = p->iTrivialFrame;
        return 0;
    }
    p->fPreparedVsids = 0;
    for ( c = 0; c < nCst; c++ )
    {
        Vec_IntClear( p->vAssump );   // scratch here; real assumptions built later
        for ( i = 0; i < pnCstLits[c]; i++ )
            Vec_IntPush( p->vAssump, ppCstCls[c][i] );
        Vec_IntPush( p->vAssump, Gip_Lit(p->constrainAct, 1) );
        if ( !Gip_SolverSimplifyClause( p, Vec_IntArray(p->vAssump), Vec_IntSize(p->vAssump) ) )
            continue;
        assert( Vec_IntSize(p->vSimpCls) > 0 );
        if ( Vec_IntSize(p->vSimpCls) == 1 )
        {
            // every literal of the constraint is false at level 0: the query depends on those facts
            p->iCoreFrame = GIP_FRAME_INF;
            for ( i = 0; i < pnCstLits[c]; i++ )
                if ( p->pTag0[Gip_LitVar(ppCstCls[c][i])] < p->iCoreFrame )
                    p->iCoreFrame = p->pTag0[Gip_LitVar(ppCstCls[c][i])];
            return 0;
        }
        {
            // literals false at level 0 were stripped: the constraint depends on those facts
            int Frame = GIP_FRAME_INF;
            for ( i = 0; i < pnCstLits[c]; i++ )
                if ( Gip_SolverLitValue(p, ppCstCls[c][i]) == GIP_FALSE && p->pTag0[Gip_LitVar(ppCstCls[c][i])] < Frame )
                    Frame = p->pTag0[Gip_LitVar(ppCstCls[c][i])];
            Gip_SolverAttachClauseTag( p, Vec_IntArray(p->vSimpCls), Vec_IntSize(p->vSimpCls), GIP_CLA_TEMPORARY, (unsigned)Frame << 1 );
        }
    }
    if ( !p->fTempDomain )
    {
        Gip_DomainEnableLocal( p, vSeeds );
        assert( !Gip_DomainHas(&p->Domain, p->constrainAct) );
        Gip_DomainInsert( &p->Domain, p->constrainAct );
        if ( fBucket )
        {
            p->Vsids.fEnableBucket = 1;
            Gip_BucketClear( &p->Vsids.Bucket );
        }
        else
        {
            p->Vsids.fEnableBucket = 0;
            Gip_HeapClear( &p->Vsids.Heap );
        }
    }
    return 1;
}


/**Function*************************************************************

  Synopsis    [Writes a live clause whose variables belong to the selected query cone.]

  Description []

***********************************************************************/
// The query domain is closed under circuit dependencies. Clauses involving
// an unassigned variable outside it are not active in GipSAT's local search.
// Export that projection separately, so cold backends need not solve every
// unrelated cone of the full transition relation. This is a diagnostic only.
static int Gip_SolverDumpConeClause( Gip_Solver_t * p, FILE * pFile, int Cref )
{
    int i, Lit, * pLits = Gip_ClaLits(&p->Cdb.Alloc, Cref);
    for ( i = 0; i < Gip_ClaLen(&p->Cdb.Alloc, Cref); i++ )
    {
        Lit = pLits[i];
        if ( (p->pLevel[Gip_LitVar(Lit)] == 0 && Gip_SolverLitValue(p, Lit) == GIP_TRUE) ||
             (p->pValue[Gip_LitVar(Lit)] == GIP_NONE && !Gip_DomainHas(&p->Domain, Gip_LitVar(Lit))) )
            return 0;
    }
    if ( pFile )
    {
        for ( i = 0; i < Gip_ClaLen(&p->Cdb.Alloc, Cref); i++ )
        {
            Lit = pLits[i];
            if ( p->pLevel[Gip_LitVar(Lit)] == 0 && Gip_SolverLitValue(p, Lit) == GIP_FALSE )
                continue;
            fprintf( pFile, "%d ", Gip_LitCompl(Lit) ? -Gip_LitVar(Lit)-1 : Gip_LitVar(Lit)+1 );
        }
        fprintf( pFile, "0\n" );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Writes the CNF induced by a query's domain and assumptions.]

  Description []

***********************************************************************/
static void Gip_SolverDumpCone( Gip_Solver_t * p, int * pAssump, int nAssump )
{
    Vec_Int_t * vLists[4] = { p->Cdb.vTrans, p->Cdb.vLemmas, p->Cdb.vLearnt, p->Cdb.vTemp };
    char FileName[8192];
    FILE * pFile;
    int k, i, Cref, Lit, nClauses = Vec_IntSize(p->vTrail) + nAssump;
    if ( snprintf(FileName, sizeof(FileName), "%s.cone.cnf", p->pDumpFile) >= (int)sizeof(FileName) ) return;
    pFile = fopen( FileName, "w" );
    if ( !pFile ) return;
    for ( k = 0; k < 4; k++ )
        Vec_IntForEachEntry( vLists[k], Cref, i )
            if ( !Gip_ClaIsRemoved(&p->Cdb.Alloc, Cref) )
                nClauses += Gip_SolverDumpConeClause( p, NULL, Cref );
    fprintf( pFile, "c Projection to GipSAT query domain; root facts and assumptions are units\np cnf %d %d\n", p->nVarsAlloc, nClauses );
    for ( k = 0; k < 4; k++ )
        Vec_IntForEachEntry( vLists[k], Cref, i )
            if ( !Gip_ClaIsRemoved(&p->Cdb.Alloc, Cref) )
                Gip_SolverDumpConeClause( p, pFile, Cref );
    Vec_IntForEachEntry( p->vTrail, Lit, i )
        fprintf( pFile, "%d 0\n", Gip_LitCompl(Lit) ? -Gip_LitVar(Lit)-1 : Gip_LitVar(Lit)+1 );
    for ( i = 0; i < nAssump; i++ )
        fprintf( pFile, "%d 0\n", Gip_LitCompl(pAssump[i]) ? -Gip_LitVar(pAssump[i])-1 : Gip_LitVar(pAssump[i])+1 );
    fclose( pFile );
    Abc_Print( 1, "Query cone snapshot %s: %d clauses, %d domain variables.\n", FileName, nClauses, Vec_IntSize(p->Domain.Set.vSet) );
}

/**Function*************************************************************

  Synopsis    [Writes a DIMACS snapshot of a query and its assumptions.]

  Description []

***********************************************************************/
static int Gip_SolverDumpQuery( Gip_Solver_t * p, int * pAssump, int nAssump )
{
    Vec_Int_t * vLists[4] = { p->Cdb.vTrans, p->Cdb.vLemmas, p->Cdb.vLearnt, p->Cdb.vTemp };
    FILE * pFile = fopen( p->pDumpFile, "w" );
    int k, i, j, Cref, Lit, nClauses = Vec_IntSize(p->vTrail) + nAssump;
    if ( !pFile )
    {
        Abc_Print( 1, "Cannot write query snapshot %s.\n", p->pDumpFile );
        return 0;
    }
    assert( Gip_SolverLevelOf(p) == 0 );
    for ( k = 0; k < 4; k++ )
        Vec_IntForEachEntry( vLists[k], Cref, i )
            nClauses += !Gip_ClaIsRemoved(&p->Cdb.Alloc, Cref);
    fprintf( pFile, "c GipSAT active clauses, root facts, and query assumptions\np cnf %d %d\n", p->nVarsAlloc, nClauses );
    for ( k = 0; k < 4; k++ )
        Vec_IntForEachEntry( vLists[k], Cref, i )
        {
            int * pLits = Gip_ClaLits( &p->Cdb.Alloc, Cref );
            if ( Gip_ClaIsRemoved(&p->Cdb.Alloc, Cref) )
                continue;
            for ( j = 0; j < Gip_ClaLen(&p->Cdb.Alloc, Cref); j++ )
                fprintf( pFile, "%d ", Gip_LitCompl(pLits[j]) ? -Gip_LitVar(pLits[j])-1 : Gip_LitVar(pLits[j])+1 );
            fprintf( pFile, "0\n" );
        }
    Vec_IntForEachEntry( p->vTrail, Lit, i )
        fprintf( pFile, "%d 0\n", Gip_LitCompl(Lit) ? -Gip_LitVar(Lit)-1 : Gip_LitVar(Lit)+1 );
    for ( i = 0; i < nAssump; i++ )
        fprintf( pFile, "%d 0\n", Gip_LitCompl(pAssump[i]) ? -Gip_LitVar(pAssump[i])-1 : Gip_LitVar(pAssump[i])+1 );
    k = ferror( pFile );
    k |= fclose( pFile ) != 0;
    return !k;
}

/**Function*************************************************************

  Synopsis    [Full query entry point.]

  Description [Solves under the given assumptions and temporary
  constraint clauses. Returns GIP_SAT/GIP_UNSAT/GIP_UNDEF.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gip_SolverSolve( Gip_Solver_t * p,
                     int * pAssump, int nAssump,
                     int ** ppCstCls, int * pnCstLits, int nCst,
                     int nRestartLimit )
{
    abctime clk, clkQuery = 0;
    int i, c, res, * pUse, nUse;
    Gip_Batch_t * pBatch = p->Batch.vPrevious ? &p->Batch : NULL;
    int fFixed = pBatch && nCst == 1 && !p->pLoaded && p->fTempDomain && !p->pDumpFile && !p->nRecycleMode;
    int fResume = fFixed && Vec_IntSize(pBatch->vPrevious) &&
        Vec_IntSize(pBatch->vClause) == pnCstLits[0] &&
        !memcmp(Vec_IntArray(pBatch->vClause), ppCstCls[0], sizeof(int) * pnCstLits[0]);
    p->fCanceled = 0;
    p->nConfCounted = p->Stats.nConflicts;
    p->fInputAbandoned = 0;
    p->InputDeadline = p->fInputDecisions && p->nInputMillis ?
        Abc_Clock() + (abctime)p->nInputMillis * CLOCKS_PER_SEC / 1000 : 0;
    p->nInputTimeCheck = p->Stats.nPropagations + 4096;
    p->iCoreFrame = GIP_FRAME_INF;
    if ( p->pLoaded )
    {
        // Preserve a MIC's fixed domain while retiring the preceding query.
        Gip_SolverBacktrack( p, 0, p->fTempDomain );
        Gip_SolverCleanTemporary( p );
        for ( i = 0; i < nAssump; i++ )
            Gip_SolverLoadVar( p, Gip_LitVar(pAssump[i]) );
        for ( c = 0; c < nCst; c++ )
            for ( i = 0; i < pnCstLits[c]; i++ )
                Gip_SolverLoadVar( p, Gip_LitVar(ppCstCls[c][i]) );
    }
    if ( p->fTrivialUnsat )
    {
        Gip_LitSetClear( &p->UnsatCore );
        p->iCoreFrame = p->iTrivialFrame;
        return GIP_UNSAT;
    }
    // the deadline is checked on entry (and then periodically during the search)
    if ( (p->TimeLimit || p->pFuncStop) && Gip_SolverTimedOut(p) )
    {
        p->fCanceled = 1;
        return GIP_UNDEF;
    }
    p->Stats.nSolves++;
    clk = Abc_Clock();
    if ( fResume ) goto assumptions;
    // domain seeds = assumption vars + constraint vars
    Vec_IntClear( p->vSeeds );
    for ( i = 0; i < nAssump; i++ )
        Vec_IntPush( p->vSeeds, Gip_LitVar(pAssump[i]) );
    for ( c = 0; c < nCst; c++ )
        for ( i = 0; i < pnCstLits[c]; i++ )
            Vec_IntPush( p->vSeeds, Gip_LitVar(ppCstCls[c][i]) );
    if ( nCst > 0 )
    {
        if ( !Gip_SolverNewRound( p, p->vSeeds, ppCstCls, pnCstLits, nCst, 1 ) )
        {
            Gip_LitSetClear( &p->UnsatCore );
            p->Stats.timeSolve += Abc_Clock() - clk;
            return GIP_UNSAT;
        }
        // The guard can be placed last without changing the formula. This
        // lets propagation under the cube find conflicts independent of the
        // temporary strengthening clause before the guard is assumed.
assumptions:
        Vec_IntClear( p->vAssump );
        if ( !p->fActLast ) Vec_IntPush( p->vAssump, Gip_Lit(p->constrainAct, 0) );
        for ( i = 0; i < nAssump; i++ )
            Vec_IntPush( p->vAssump, pAssump[i] );
        if ( p->fActLast ) Vec_IntPush( p->vAssump, Gip_Lit(p->constrainAct, 0) );
        pUse = Vec_IntArray( p->vAssump );
        nUse = Vec_IntSize( p->vAssump );
    }
    else
    {
        res = Gip_SolverNewRound( p, p->vSeeds, NULL, NULL, 0, 1 );
        if ( !res )
        {
            Gip_LitSetClear( &p->UnsatCore );
            p->Stats.timeSolve += Abc_Clock() - clk;
            return GIP_UNSAT;
        }
        pUse = pAssump;
        nUse = nAssump;
    }
    if ( p->nRecycleMode && nCst == 1 )
        Vec_IntPushArray( p->vRecycleCond, ppCstCls[0], pnCstLits[0] );
    if ( p->pDumpFile )
    {
        Gip_SolverDumpQuery( p, pUse, nUse );
        if ( Gip_SolverOption(p, "PDR2_DUMP_CONE") ) Gip_SolverDumpCone( p, pUse, nUse );
        clkQuery = Abc_Clock();
    }
    if ( fResume )
    {
        int Limit = Abc_MinInt(Gip_SolverLevelOf(p), Abc_MinInt(nUse, Vec_IntSize(pBatch->vPrevious)));
        for ( i = 0; i < Limit; ++i )
            if ( pUse[i] != Vec_IntEntry(pBatch->vPrevious, i) ||
                 Gip_SolverLitValue(p, pUse[i]) != GIP_TRUE ||
                 p->pLevel[Gip_LitVar(pUse[i])] > (unsigned)(i + 1) )
                break;
        Gip_SolverBacktrack(p, i, 1);
        pBatch->nResumed += i;
    }
    else
    {
        Gip_SolverCleanLearnt( p, 1 );
        Gip_SolverSimplify( p );
    }
    res = Gip_SolverSearchWithRestart( p, pUse, nUse, nRestartLimit );
    if ( fFixed && res != GIP_UNDEF && !p->fTrivialUnsat )
    {
        if ( !fResume )
        {
            Vec_IntClear(pBatch->vClause);
            Vec_IntPushArray(pBatch->vClause, ppCstCls[0], pnCstLits[0]);
        }
        Vec_IntClear(pBatch->vPrevious);
        Vec_IntPushArray(pBatch->vPrevious, pUse, nUse);
    }
    else if ( pBatch )
        Vec_IntClear( pBatch->vPrevious );
    if ( (p->nRecycleMode & 1) && res == GIP_UNSAT )
    {
        int Lit;
        Vec_IntClear( p->vRecycleTmp );
        Vec_IntForEachEntry( p->UnsatCore.vSet, Lit, i )
            Vec_IntPush( p->vRecycleTmp, Gip_LitNot(Lit) );
        Gip_SolverSaveRecycled( p, Vec_IntArray(p->vRecycleTmp), Vec_IntSize(p->vRecycleTmp), p->iCoreFrame );
    }
    if ( p->Domain.Set.pValues && Gip_SolverOption(p, "PDR2_WATCH_STATE_CHECK") )
        for ( i = 0; i < p->nVarsAlloc; i++ )
            assert( !p->Domain.Set.pHas[i] || p->Domain.Set.pHas[i] == 1 + p->pValue[i] );
    if ( p->Domain.Set.pLitFlags && Gip_SolverOption(p, "PDR2_PACKED_CHECK") )
        for ( i = 0; i < p->nVarsAlloc; i++ )
        {
            assert( ((p->pLitVal[2*i] >> 2) & 1) == !!p->Domain.Set.pHas[i] );
            assert( ((p->pLitVal[2*i+1] >> 2) & 1) == !!p->Domain.Set.pHas[i] );
            assert( (p->pLitVal[2*i] & 3) == p->pValue[i] );
            assert( (p->pLitVal[2*i+1] & 3) == (p->pValue[i] == GIP_NONE ? GIP_NONE : p->pValue[i] ^ 1) );
        }
    if ( res == GIP_SAT && ((p->fJustify && Gip_SolverOption(p, "PDR2_JUSTIFY_CHECK")) ||
                            (p->fInputDecisions && Gip_SolverOption(p, "PDR2_INPUT_CHECK"))) )
        Gip_SolverCheckPartialModel( p, pUse, nUse );
    if ( p->pDumpFile )
        Abc_Print( 1, "Query snapshot %s result=%d search_seconds=%.6f\n", p->pDumpFile, res, (double)(Abc_Clock()-clkQuery)/CLOCKS_PER_SEC );
    p->Stats.timeSolve += Abc_Clock() - clk;
    return res;
}

/**Function*************************************************************

  Synopsis    [Model value of a variable; unassigned counts as 0.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gip_SolverVarValue( Gip_Solver_t * p, int Var )
{
    return p->pValue[Var] == GIP_TRUE ? 1 : 0;
}

/**Function*************************************************************

  Synopsis    [Checks whether a literal is in the last unsat core.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gip_SolverUnsatHas( Gip_Solver_t * p, int Lit )
{
    return Gip_LitSetHas( &p->UnsatCore, Lit );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
