/**CFile****************************************************************

  FileName    [giaScmapRefine.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [SCMap refinement of the selected cover; included by giaScmap.c.]

  Description [Refinement alternates two searches over the electrical model
  (rise/fall arcs at each net's load through its best size/buffer tree):
  a cheap forward repair, which visits every root once and checks a candidate
  against residual tails of the rest of the cover, and a bounded delay-first
  search, which ranks the critical roots, screens their candidates, and
  accepts an edit only after propagating it to every affected output. Delay
  rounds come first; area rounds then keep the achieved delay. No backend
  timing or sizing result takes part in a decision.]

  Author      [Anqi Lu]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 2026.]

  Revision    [$Id: giaScmapRefine.h,v 1.00 2026/11/27 00:00:00 anqilu Exp $]

***********************************************************************/

/**Function*************************************************************

  Synopsis    [Delay through a literal: its arrival plus its residual tail.]

  Description [The trial or committed arrival and slew of the same
  implementation, transition by transition.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static float Scm_CtxScore( Scm_Man_t * p, Scm_Ctx_t * pCtx, int Lit, int fTrial )
{
    Scm_RfPair_t a = fTrial ? pCtx->pTrialRfArrs[Lit] : p->pRfArrs[Lit];
    Scm_RfPair_t s = fTrial ? pCtx->pTrialRfSlews[Lit] : p->pRfSlews[Lit];
    Scm_RfPair_t Tail = Scm_RfLinesEval(pCtx->pTails + Lit, s);
    return Abc_MaxFloat(a.Value[0] + Tail.Value[0], a.Value[1] + Tail.Value[1]);
}

/**Function*************************************************************

  Synopsis    [Adds the selected match's arcs to its leaves' tails (required times
  only tighten during a pass).]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_CtxTighten( Scm_Man_t * p, Scm_Ctx_t * pCtx, int iObj )
{
    int Pass, c, k;
    for ( Pass = 1; Pass >= 0; Pass-- )
        for ( c = 0; c < 2; c++ )
        {
            int Lit = 2*iObj + c, * pCut;
            Scm_Mat_t * pM = Scm_ObjMatch(p, iObj, c);
            Mio_Cell2_t * pCell;
            Scm_RfPair_t Tail, Load;
            if ( !Scm_ObjMapRefNum(p, iObj, c) || !!pM->fCompl != Pass ) continue;
            Tail = Scm_RfLinesEval(pCtx->pTails + Lit, p->pRfSlews[Lit]);
            pCell = pM->fCompl ? p->pCells + 3 : Scm_ManCell(p, pM->Gate);
            if ( !pCell->nFanins ) continue;
            pCut = pM->fCompl ? NULL : Scm_CutFromHandle(Scm_ObjCutSet(p, iObj), pM->CutH);
            Load = Scm_ManRfLoad(p, Lit);
            for ( k = 0; k < (int)pCell->nFanins; k++ )
            {
                int Child = pM->fCompl ? (Lit ^ 1) : Abc_Var2Lit(Scm_CutLeaves(pCut)[Scm_CfgVar(pM->Cfg, k)], Scm_CfgCompl(pM->Cfg, k));
                Scm_Arc_t Temp, * pArc = Scm_ManArcAtLoad(p, pCell, k, Load, &Temp);
                Scm_RfLinesAddArc(pCtx->pTails + Child, pArc, Load, Tail);
                pCtx->pTailBase[Child] = Scm_RfLinesEval(pCtx->pTails + Child, p->pRfSlews[Child]);
                pCtx->pTailValid[Child] = 1;
            }
        }
}

/**Function*************************************************************

  Synopsis    [Builds the round-start tails of every mapped literal, the primary
  inputs included.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_CtxTailBuildAll( Scm_Man_t * p, Scm_Ctx_t * pCtx )
{
    Gia_Obj_t * pObj;
    int i, j, c;
    Gia_ManForEachAndReverse( p->pGia, pObj, i )
        for ( c = 0; c < 2; c++ )
            if ( Scm_ObjMapRefNum(p, i, c) && !Scm_CtxTailBuild(p, pCtx, 2*i+c) )
                return 0;
    Gia_ManForEachCiId( p->pGia, i, j )
        for ( c = 0; c < 2; c++ )
            if ( Scm_ObjMapRefNum(p, i, c) && !Scm_CtxTailBuild(p, pCtx, 2*i+c) )
                return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Retimes one node from its fanins' current timing (the direct phase
  before the inverter).]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_CtxRefreshRoot( Scm_Man_t * p, Scm_Ctx_t * pCtx, int iObj )
{
    int Pass, c;
    ++pCtx->Epoch;
    assert( pCtx->Epoch != 0 );
    for ( Pass = 0; Pass < 2; Pass++ )
        for ( c = 0; c < 2; c++ )
            if ( Scm_ObjMapRefNum(p, iObj, c) && !!Scm_ObjMatch(p, iObj, c)->fCompl == Pass )
            {
                int Lit = Abc_Var2Lit(iObj, c);
                if ( !Scm_CtxEvalLit(p, pCtx, iObj, c) ) return 0;
                p->pRfArrs[Lit] = pCtx->pTrialRfArrs[Lit];
                p->pRfSlews[Lit] = pCtx->pTrialRfSlews[Lit];
                p->pArrMax[Lit] = pCtx->pTrialArrMax[Lit];
                p->pSlewMax[Lit] = pCtx->pTrialSlewMax[Lit];
            }
    return 1;
}

/**Function*************************************************************

  Synopsis    [One pass of the cheap forward repair.]

  Description [Visits the nodes in topological order. The delay pass
  (fArea = 0) works on roots within SCM_CRITICAL_PCT of the target and picks
  the candidate with the smallest delay through the root; the area pass works
  on every root and picks the candidate freeing the most exact area. Either
  way a candidate must free at least the logic area its modeled buffer trees
  add, and keep the delay to the outputs within the target.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_ManRepair( Scm_Man_t * p, int fArea )
{
    Gia_Obj_t * pObj;
    float Target = p->pPars->ModelDelayTarget > 0 ? fmaxf(p->ModelDelay, p->pPars->ModelDelayTarget) : p->ModelDelay;
    Scm_Ctx_t * pCtx;
    long long trackedArea, startArea, actual;
    int i, c;
    trackedArea = startArea = (long long)Scm_ManCoverArea(p);
    if ( !Scm_ManTimeCover(p) ) return 0;
    pCtx = Scm_CtxStart(p, 1);
    if ( !pCtx ) return 0;
    if ( !Scm_CtxTailBuildAll(p, pCtx) )
    {
        Scm_CtxFree( pCtx );
        return 0;
    }
    Gia_ManForEachAnd( p->pGia, pObj, i )
    {
        if ( !Scm_CtxRefreshRoot(p, pCtx, i) )
        {
            Scm_CtxFree( pCtx );
            return 0;
        }
        for ( c = 0; c < 2; c++ )
        {
            int Lit = Abc_Var2Lit(i, c), nList = 0, nAlloc = 0, Best = -1, q;
            Scm_Mat_t Old = *Scm_ObjMatch(p, i, c);
            Scm_Cand_t * pList = NULL;
            word Freed;
            float BestScore;
            if ( !Scm_ObjMapRefNum(p, i, c) ) continue;
            BestScore = Scm_CtxScore(p, pCtx, Lit, 0);
            if ( !fArea && BestScore < 0.01f * SCM_CRITICAL_PCT * Target ) continue;
            Vec_IntClear( pCtx->vOldSeeds );
            pCtx->pCollectSeeds = pCtx->vOldSeeds;
            Freed = Scm_CtxDeref_rec(p, pCtx, i, c, &Old);
            pCtx->pCollectSeeds = NULL;
            pCtx->BufferFreed = Freed;
            Scm_ManCandidates(p, i, c, &Old, Freed+1, &pList, &nList, &nAlloc, 1);
            for ( q = 0; !pCtx->fError && q < nList; q++ )
            {
                float Delay, Score;
                int Status = Scm_CtxTry(p, pCtx, i, c, &Old, pList + q, Target, &Delay);
                if ( Status < 0 ) { pCtx->fError = 1; break; }
                if ( !Status ) continue;
                Score = Scm_CtxScore(p, pCtx, Lit, 1);
                if ( fArea ?
                     (pList[q].Area < (Best >= 0 ? pList[Best].Area : Freed) ||
                      (Best >= 0 && pList[q].Area == pList[Best].Area && Score < BestScore)) :
                     (Score < BestScore - 1.0e-3f ||
                      (Best >= 0 && fabsf(Score - BestScore) <= 1.0e-3f && pList[q].Area < pList[Best].Area)) )
                    BestScore = Score, Best = q;
            }
            if ( !pCtx->fError && Best >= 0 )
            {
                assert( pList[Best].Area <= Freed );
                trackedArea += (long long)pList[Best].Area - (long long)Freed;
                if ( Scm_CtxApply(p, pCtx, i, c, pList + Best) < 0 ) pCtx->fError = 1;
            }
            else
            {
                word Restored = Scm_CtxRef_rec(p, pCtx, i, c, &Old);
                (void)Restored;
                assert( Restored == Freed );
                *Scm_ObjMatch(p, i, c) = Old;
            }
            ABC_FREE( pList );
            if ( pCtx->fError )
            {
                Scm_CtxFree( pCtx );
                return 0;
            }
        }
        Scm_CtxTighten( p, pCtx, i );
    }
    Scm_CtxRecycle( p, pCtx );
    actual = (long long)Scm_ManCoverArea(p);
    if ( actual != trackedArea || (fArea && actual > startArea) ) return 0;
    if ( !Scm_ManTimeCover(p) ) return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Output score tree: the maximum arrival and the pressure.]

  Description [Pressure is the sum over outputs and transitions of the
  arrival beyond the round's threshold. A trial sets the leaves of its changed
  outputs, reads the root, and restores them. Duplicate output drivers keep
  separate leaves.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
typedef struct Scm_PoTree_t_ Scm_PoTree_t;
struct Scm_PoTree_t_
{
    int            size, count, depth;
    int *          head;       // per literal: first leaf driven by it, -1 if none
    int *          next;       // per leaf: next leaf of the same literal
    int *          degree;     // per literal: number of leaves
    float *        delay;      // the heap of maxima
    double *       pressure;   // the heap of sums
    word           updates;    // node updates, counted as search work
};

/**Function*************************************************************

  Synopsis    [Sets the leaf of an output: its worst arrival and its pressure.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_PoTreeLeaf( Scm_PoTree_t * q, int k, Scm_RfPair_t a, double threshold )
{
    q->delay[k] = fmaxf(0, fmaxf(a.Value[0], a.Value[1]));
    q->pressure[k] = fmax(0, (double)a.Value[0] - threshold) + fmax(0, (double)a.Value[1] - threshold);
}

/**Function*************************************************************

  Synopsis    [Updates the leaf of an output and its ancestors.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_PoTreeSet( Scm_PoTree_t * q, int index, Scm_RfPair_t a, double threshold )
{
    int k = q->size + index;
    Scm_PoTreeLeaf( q, k, a, threshold );
    q->updates++;
    for ( k >>= 1; k; k >>= 1 )
    {
        q->delay[k] = fmaxf(q->delay[2*k], q->delay[2*k+1]);
        q->pressure[k] = q->pressure[2*k] + q->pressure[2*k+1];
        q->updates++;
    }
}

/**Function*************************************************************

  Synopsis    [Rebuilds the output score tree from the committed arrivals.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_PoTreeRebuild( Scm_PoTree_t * q, Scm_Man_t * p, Vec_Int_t * vPos, double threshold )
{
    int i, k;
    for ( i = 0; i < q->count; i++ )
    {
        Scm_PoTreeLeaf( q, q->size + i, p->pRfArrs[Vec_IntEntry(vPos, i)], threshold );
        q->updates++;
    }
    for ( k = q->size - 1; k; k-- )
    {
        q->delay[k] = fmaxf(q->delay[2*k], q->delay[2*k+1]);
        q->pressure[k] = q->pressure[2*k] + q->pressure[2*k+1];
        q->updates++;
    }
}

/**Function*************************************************************

  Synopsis    [Starts the output score tree.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Scm_PoTree_t * Scm_PoTreeStart( Scm_Man_t * p, Vec_Int_t * vPos, double threshold )
{
    Scm_PoTree_t * q = ABC_CALLOC(Scm_PoTree_t, 1);
    int i, nLits = 2*Gia_ManObjNum(p->pGia);
    q->count = Vec_IntSize(vPos);
    q->size = 1;
    while ( q->size < q->count )
        q->size *= 2, q->depth++;
    q->degree = ABC_CALLOC(int, nLits);
    q->head = ABC_FALLOC(int, nLits);
    q->next = ABC_ALLOC(int, q->count);
    q->delay = ABC_CALLOC(float, 2*q->size);
    q->pressure = ABC_CALLOC(double, 2*q->size);
    for ( i = 0; i < q->count; i++ )
    {
        int lit = Vec_IntEntry(vPos, i);
        q->next[i] = q->head[lit];
        q->head[lit] = i;
        q->degree[lit]++;
    }
    Scm_PoTreeRebuild( q, p, vPos, threshold );
    q->updates = 0;
    return q;
}

/**Function*************************************************************

  Synopsis    [Stops the output score tree.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_PoTreeStop( Scm_PoTree_t * q )
{
    if ( !q ) return;
    ABC_FREE( q->head ); ABC_FREE( q->next ); ABC_FREE( q->degree );
    ABC_FREE( q->delay ); ABC_FREE( q->pressure ); ABC_FREE( q );
}

/**Function*************************************************************

  Synopsis    [Sets the leaves of the outputs a trial changed, from the trial's or
  the committed arrivals.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_PoTreeAffected( Scm_PoTree_t * q, Scm_Man_t * p, Scm_Ctx_t * pCtx, double threshold, int fTrial )
{
    int i, lit, index;
    Vec_IntForEachEntry( pCtx->vScoreOutputs, lit, i )
    {
        Scm_RfPair_t a;
        if ( q->head[lit] < 0 || pCtx->pComputed[lit] != pCtx->Epoch ) continue;
        a = fTrial ? pCtx->pTrialRfArrs[lit] : p->pRfArrs[lit];
        for ( index = q->head[lit]; index >= 0; index = q->next[index] )
            Scm_PoTreeSet( q, index, a, threshold );
    }
}

/**Function*************************************************************

  Synopsis    [Whether a trial changed so many outputs that one linear scan is
  cheaper than the tree.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_PoTreeDense( Scm_PoTree_t * q, Scm_Ctx_t * pCtx )
{
    int i, lit, n = 0;
    Vec_IntForEachEntry( pCtx->vScoreOutputs, lit, i )
        n += q->degree[lit];
    return (unsigned long long)n * (q->depth + 1) >= (unsigned long long)q->count;
}

/**Function*************************************************************

  Synopsis    [The bounded delay-first search.]

  Description [Scm_Search_t holds one refinement round: the output score
  tree, the work budget (cap trials per root, counted in retimed literals),
  and the timing of the best trial of the current root, which is restored on
  commit instead of being recomputed.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
typedef struct Scm_Score_t_ Scm_Score_t;
struct Scm_Score_t_
{
    float          delay;      // the maximum output arrival
    double         pressure;   // the arrival beyond the threshold, summed over outputs and transitions
};
typedef struct Scm_Undo_t_ Scm_Undo_t;
struct Scm_Undo_t_
{
    int            lit;
    Scm_Mat_t      old;
    long long      delta;      // logic area change of the edit
};
// The trial timing of one literal: the later arrival, the larger slew, and both per transition.
typedef struct Scm_Saved_t_ Scm_Saved_t;
struct Scm_Saved_t_
{
    int            lit;
    float          arr, slew;
    Scm_RfPair_t   ar, sr;
};
typedef struct Scm_Snapshot_t_ Scm_Snapshot_t;
struct Scm_Snapshot_t_
{
    Scm_Saved_t *  data;
    int            size, cap;
    Scm_Score_t    score;
};
typedef struct Scm_Search_t_ Scm_Search_t;
struct Scm_Search_t_
{
    Scm_Man_t *    p;
    Scm_Ctx_t *    ctx;
    Vec_Int_t *    pos;        // output drivers
    double         threshold;  // SCM_CRITICAL_PCT of the round's target
    long long      area;       // logic area of the cover
    int            keep;       // candidates kept by a screen (1 fast, 4 quality)
    int            delayRounds;
    int            edits;      // edits committed so far
    int            sideRoot;   // the current root is a side root
    int            baseValid;  // cachedBase is the score of the current cover
    float          acceptBound; // the delay bound of the current root's trials
    Scm_Score_t    cachedBase; // the score of the unchanged cover
    Scm_Snapshot_t bestState;  // timing of the best trial of the current root
    Scm_PoTree_t * outputs;    // the output score tree
    unsigned long long work, limit;   // work done and the round's budget, in retimed literals
};

/**Function*************************************************************

  Synopsis    [A consistency-check tolerance only (a float ULP exceeds 0.001 ps on
  long paths); never a selection rule.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static float Scm_DelayTolerance( float a, float b )
{
    float scale = fmaxf(fabsf(a), fabsf(b));
    return fmaxf(1e-3f, 4.0f*(nextafterf(scale, INFINITY) - scale));
}

/**Function*************************************************************

  Synopsis    [Checks whether two delays agree within the consistency tolerance.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_DelayClose( float a, float b )
{
    return isfinite(a) && isfinite(b) && fabsf(a-b) <= Scm_DelayTolerance(a, b);
}

/**Function*************************************************************

  Synopsis    [Ranks scores by delay, then by pressure.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_ScoreBetter( Scm_Score_t a, Scm_Score_t b )
{
    if ( a.delay < b.delay - 1e-4f ) return 1;
    if ( a.delay > b.delay ) return 0;
    return a.pressure < b.pressure - 1e-4;
}

/**Function*************************************************************

  Synopsis    [Scores all outputs at the committed or trial arrivals.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Scm_Score_t Scm_SearchMeasureAll( Scm_Search_t * d, int fTrial )
{
    Scm_Score_t s = {0, 0};
    int i, lit, t;
    Vec_IntForEachEntry( d->pos, lit, i )
    {
        Scm_RfPair_t a = d->p->pRfArrs[lit];
        if ( fTrial && d->ctx->pComputed[lit] == d->ctx->Epoch ) a = d->ctx->pTrialRfArrs[lit];
        for ( t = 0; t < 2; t++ )
        {
            s.delay = fmaxf(s.delay, a.Value[t]);
            s.pressure += fmax(0, (double)a.Value[t] - d->threshold);
        }
    }
    return s;
}

/**Function*************************************************************

  Synopsis    [The score of the committed cover or of the current trial.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Scm_Score_t Scm_SearchMeasure( Scm_Search_t * d, int fTrial )
{
    Scm_PoTree_t * q = d->outputs;
    word before = q->updates;
    Scm_Score_t score;
    if ( fTrial && Scm_PoTreeDense(q, d->ctx) )
    {
        d->work += 2*(unsigned)Vec_IntSize(d->pos);
        return Scm_SearchMeasureAll(d, fTrial);
    }
    if ( fTrial ) Scm_PoTreeAffected( q, d->p, d->ctx, d->threshold, 1 );
    score.delay = q->delay[1];
    score.pressure = q->pressure[1];
    if ( fTrial ) Scm_PoTreeAffected( q, d->p, d->ctx, d->threshold, 0 );
    d->work += q->updates - before;
    return score;
}

/**Function*************************************************************

  Synopsis    [Starts collecting the literals that an edit changes.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_SearchBegin( Scm_Search_t * d )
{
    Vec_IntClear( d->ctx->vTrialSeeds );
    d->ctx->pCollectSeeds = d->ctx->vTrialSeeds;
}

/**Function*************************************************************

  Synopsis    [Applies a match edit to the cover and records how to undo it.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Scm_Undo_t Scm_SearchEdit( Scm_Search_t * d, int lit, Scm_Mat_t * m )
{
    Scm_Man_t * p = d->p;
    int i = lit >> 1, c = lit & 1;
    Scm_Undo_t u;
    word freed, added;
    u.lit = lit;
    u.old = *Scm_ObjMatch(p, i, c);
    freed = Scm_CtxDeref_rec(p, d->ctx, i, c, &u.old);
    *Scm_ObjMatch(p, i, c) = *m;
    added = Scm_CtxRef_rec(p, d->ctx, i, c, m);
    u.delta = (long long)added - (long long)freed;
    return u;
}

/**Function*************************************************************

  Synopsis    [Undoes a match edit.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_SearchRestore( Scm_Search_t * d, Scm_Undo_t u )
{
    Scm_Man_t * p = d->p;
    int i = u.lit >> 1, c = u.lit & 1;
    word removed, restored;
    d->ctx->pCollectSeeds = NULL;
    removed = Scm_CtxDeref_rec(p, d->ctx, i, c, Scm_ObjMatch(p, i, c));
    *Scm_ObjMatch(p, i, c) = u.old;
    restored = Scm_CtxRef_rec(p, d->ctx, i, c, &u.old);
    (void)removed; (void)restored;
    assert( (long long)removed - (long long)restored == u.delta );
}

/**Function*************************************************************

  Synopsis    [Delay rounds: every other match (area is counted per trial); area
  rounds: the matches that free area.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Scm_Cand_t * Scm_SearchCandidates( Scm_Search_t * d, int lit, int fArea, int * pCount )
{
    Scm_Man_t * p = d->p;
    int alloc = 0, i = lit >> 1, c = lit & 1;
    Scm_Cand_t * list = NULL;
    Scm_Mat_t old = *Scm_ObjMatch(p, i, c);
    word freed, restored;
    d->ctx->pCollectSeeds = NULL;
    if ( !fArea )
    {
        Scm_ManCandidates(p, i, c, &old, (~(word)0)/4, &list, pCount, &alloc, 0);
        return list;
    }
    freed = Scm_CtxDeref_rec(p, d->ctx, i, c, &old);
    Scm_ManCandidates(p, i, c, &old, freed, &list, pCount, &alloc, 1);
    restored = Scm_CtxRef_rec(p, d->ctx, i, c, &old);
    (void)restored;
    assert( restored == freed );
    return list;
}

/**Function*************************************************************

  Synopsis    [Saves the timing of the current trial: committing the same edit later
  restores it.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_SearchSave( Scm_Search_t * d, Scm_Snapshot_t * save, Scm_Score_t score )
{
    Scm_Ctx_t * ctx = d->ctx;
    int i;
    save->size = Vec_IntSize(ctx->vAffected);
    save->score = score;
    if ( save->cap < save->size )
    {
        save->cap = Abc_MaxInt(save->size, 2*save->cap + 16);
        save->data = ABC_REALLOC(Scm_Saved_t, save->data, save->cap);
    }
    for ( i = 0; i < save->size; i++ )
    {
        int x = Vec_IntEntry(ctx->vAffected, i);
        Scm_Saved_t * v = save->data + i;
        assert( ctx->pComputed[x] == ctx->Epoch );
        v->lit = x;
        v->arr = ctx->pTrialArrMax[x]; v->slew = ctx->pTrialSlewMax[x];
        v->ar = ctx->pTrialRfArrs[x];  v->sr = ctx->pTrialRfSlews[x];
    }
}

/**Function*************************************************************

  Synopsis    [Restores the timing saved before a trial and returns its score.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Scm_Score_t Scm_SearchLoad( Scm_Search_t * d, Scm_Snapshot_t * save )
{
    Scm_Ctx_t * ctx = d->ctx;
    int i;
    ++ctx->Epoch;
    assert( ctx->Epoch );
    Vec_IntClear( ctx->vAffected );
    Vec_IntClear( ctx->vScoreOutputs );
    ctx->pCollectSeeds = NULL;
    ctx->fScoreRejected = 0;
    ctx->fScorePrune = 0;
    d->work += save->size;
    for ( i = 0; i < save->size; i++ )
    {
        Scm_Saved_t * v = save->data + i;
        int x = v->lit;
        Vec_IntPush( ctx->vAffected, x );
        ctx->pComputed[x] = ctx->Epoch;
        if ( ctx->pIsPo[x] ) Vec_IntPush( ctx->vScoreOutputs, x );
        ctx->pTrialArrMax[x] = v->arr; ctx->pTrialSlewMax[x] = v->slew;
        ctx->pTrialRfArrs[x] = v->ar;  ctx->pTrialRfSlews[x] = v->sr;
    }
    return save->score;
}

/**Function*************************************************************

  Synopsis    [Times a trial to every affected output; it stops once a changed
  arrival exceeds its required time.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_SearchEvaluate( Scm_Search_t * d, Scm_Score_t * s )
{
    Scm_Ctx_t * ctx = d->ctx;
    Scm_Prune_t * r = (Scm_Prune_t *)ctx->pScorePrune;
    int x, i;
    ctx->pCollectSeeds = NULL;
    ctx->fScorePrune = 1;
    if ( r->threshold != d->acceptBound )
    {
        memset( r->shadow.pTailValid, 0, ctx->nLits );
        r->threshold = d->acceptBound;
    }
    ctx->fScoreRejected = 0;
    ctx->ScorePruneCutoff = 0;
    Vec_IntForEachEntry( ctx->vTrialSeeds, x, i )
        ctx->ScorePruneCutoff = Abc_MaxInt(ctx->ScorePruneCutoff, x >> 1);
    if ( !Scm_CtxTimeLocal(d->p, ctx, Gia_ManObjNum(d->p->pGia)-1) ) return 0;
    d->work += 1 + (unsigned)Vec_IntSize(ctx->vAffected);
    if ( ctx->fScoreRejected )
        s->delay = FLT_MAX, s->pressure = 0;
    else
        *s = Scm_SearchMeasure(d, 1);
    ctx->fScorePrune = 0;
    return isfinite(s->delay) && isfinite(s->pressure);
}

/**Function*************************************************************

  Synopsis    [Screens a root's candidates by the delay through the root.]

  Description [Times each candidate only up to the root and ranks it with
  the root's round-start tail. Keeps the d->keep fastest candidates and, in
  area rounds, also the d->keep smallest; in delay rounds a candidate must be
  faster than the current match. Returns the number selected, -1 on error.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_SearchScreen( Scm_Search_t * d, int lit, Scm_Cand_t * list, int n, int fArea, int selected[8] )
{
    int fast[4] = {-1, -1, -1, -1}, small[4] = {-1, -1, -1, -1}, count = 0, keep = d->keep, j, k, z;
    float costs[4] = {0, 0, 0, 0};
    assert( keep >= 1 && keep <= 4 );
    for ( k = 0; k < n; k++ )
    {
        Scm_Undo_t u;
        float score = FLT_MAX;
        int ok;
        if ( d->work >= d->limit ) break;
        Vec_IntClear( d->ctx->vTrialSeeds );
        d->ctx->pCollectSeeds = d->ctx->vTrialSeeds;
        u = Scm_SearchEdit(d, lit, &list[k].M);
        d->ctx->fFullPropagation = 0;
        ok = Scm_CtxTimeLocal(d->p, d->ctx, lit >> 1);
        d->ctx->fFullPropagation = 1;
        d->work += 1 + (unsigned)Vec_IntSize(d->ctx->vAffected);
        if ( ok )
            score = d->ctx->pTailValid[lit] && d->ctx->pTails[lit].nFans ? Scm_CtxScore(d->p, d->ctx, lit, 1) : d->ctx->pTrialArrMax[lit];
        Scm_SearchRestore( d, u );
        if ( !ok || !isfinite(score) ) return -1;
        if ( !fArea && score >= Scm_CtxScore(d->p, d->ctx, lit, 0) - 1e-4f ) continue;
        for ( j = 0; j < keep; j++ )
            if ( fast[j] < 0 || score < costs[j] )
            {
                for ( z = keep-1; z > j; z-- )
                    fast[z] = fast[z-1], costs[z] = costs[z-1];
                fast[j] = k; costs[j] = score;
                break;
            }
        if ( fArea )
            for ( j = 0; j < keep; j++ )
                if ( small[j] < 0 || list[k].Area < list[small[j]].Area )
                {
                    for ( z = keep-1; z > j; z-- )
                        small[z] = small[z-1];
                    small[j] = k;
                    break;
                }
    }
    for ( j = 0; j < keep; j++ )
        if ( fast[j] >= 0 ) selected[count++] = fast[j];
    for ( j = 0; j < keep; j++ )
        if ( small[j] >= 0 )
        {
            int exists = 0;
            for ( k = 0; k < count; k++ )
                exists |= selected[k] == small[j];
            if ( !exists ) selected[count++] = small[j];
        }
    return count;
}

/**Function*************************************************************

  Synopsis    [Whether a mapped literal lies on a path within SCM_CRITICAL_PCT of the
  round's target.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_SearchLeafCritical( Scm_Search_t * d, int child )
{
    Scm_Man_t * p = d->p;
    if ( !Scm_ObjMapRefNum(p, child >> 1, child & 1) || !d->ctx->pTailValid[child] || !d->ctx->pTails[child].nFans ) return 0;
    return Scm_CtxScore(p, d->ctx, child, 0) >= d->threshold;
}

/**Function*************************************************************

  Synopsis    [The capacitance a match adds to critical nets.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static float Scm_SearchCritCap( Scm_Search_t * d, int lit, Scm_Mat_t * m )
{
    Scm_Man_t * p = d->p;
    Mio_Cell2_t * cell;
    SC_Cell * scl;
    float cap = 0;
    int k, * cut;
    if ( m->fCompl ) return Scm_SearchLeafCritical(d, lit^1) ? Scm_ManInvInputCap(p) : 0;
    if ( !Scm_ObjCutSetId(p, lit >> 1) ) return 0;
    cell = Scm_ManCell(p, m->Gate);
    if ( !cell->nFanins ) return 0;
    scl = Scm_ManSclCell(p, cell);
    cut = Scm_CutFromHandle(Scm_ObjCutSet(p, lit >> 1), m->CutH);
    for ( k = 0; k < (int)cell->nFanins; k++ )
    {
        int child = Abc_Var2Lit(Scm_CutLeaves(cut)[Scm_CfgVar(m->Cfg, k)], Scm_CfgCompl(m->Cfg, k));
        if ( Scm_SearchLeafCritical(d, child) ) cap += Scm_ManCellPinCap(p, scl, k);
    }
    return cap;
}

/**Function*************************************************************

  Synopsis    [A side root (off the critical paths, loading them): its three
  candidates adding the least critical load.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_SearchSideScreen( Scm_Search_t * d, int lit, Scm_Cand_t * list, int n, int selected[8] )
{
    int keep = 3, count = 0, j, k, z;
    float caps[8];
    float own = Scm_SearchCritCap(d, lit, Scm_ObjMatch(d->p, lit >> 1, lit & 1));
    if ( own <= 0 ) return 0;
    for ( k = 0; k < n; k++ )
    {
        float c;
        if ( d->work >= d->limit ) break;
        d->work++;
        c = Scm_SearchCritCap(d, lit, &list[k].M);
        if ( c >= own*(1-1e-4f) ) continue;
        for ( j = 0; j < count; j++ )
            if ( c < caps[j] ) break;
        if ( j >= keep ) continue;
        if ( count < keep ) count++;
        for ( z = count-1; z > j; z-- )
            caps[z] = caps[z-1], selected[z] = selected[z-1];
        caps[j] = c; selected[j] = k;
    }
    return count;
}

/**Function*************************************************************

  Synopsis    [Tries a root's screened candidates and commits the best.]

  Description [Delay rounds keep the best score (delay, then pressure);
  area rounds the smallest area, then the best score. Every accepted
  candidate keeps the output delay within the target.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_SearchRoot( Scm_Search_t * d, int lit, int fArea, float target )
{
    Scm_Score_t base, score;
    Scm_Cand_t * list;
    long long bestArea = d->area;
    int n = 0, best = -1, selected[8], side, count, z;
    d->acceptBound = target;
    base = d->baseValid ? d->cachedBase : Scm_SearchMeasure(d, 0);
    score = base;
    d->cachedBase = base;
    d->baseValid = 1;
    list = Scm_SearchCandidates(d, lit, fArea, &n);
    Scm_SearchBegin( d );
    side = d->sideRoot && !fArea;
    count = side ? Scm_SearchSideScreen(d, lit, list, n, selected) : Scm_SearchScreen(d, lit, list, n, fArea, selected);
    if ( count < 0 ) { ABC_FREE( list ); return 0; }
    for ( z = 0; z < count; z++ )
    {
        int k = selected[z], ok;
        Scm_Undo_t u;
        Scm_Score_t q = {0, 0};
        long long area;
        Scm_SearchBegin( d );
        u = Scm_SearchEdit(d, lit, &list[k].M);
        ok = Scm_SearchEvaluate(d, &q);
        area = d->area + u.delta;
        Scm_SearchRestore( d, u );
        if ( !ok || d->ctx->fError ) { ABC_FREE( list ); return 0; }
        if ( q.delay > target ) continue;
        if ( fArea ? (area < bestArea || (best >= 0 && area == bestArea && Scm_ScoreBetter(q, score))) : Scm_ScoreBetter(q, score) )
        {
            best = k; score = q; bestArea = area;
            Scm_SearchSave( d, &d->bestState, q );
        }
    }
    if ( best >= 0 )
    {
        // re-apply the best edit and restore its saved timing
        Scm_Prune_t * r = (Scm_Prune_t *)d->ctx->pScorePrune;
        word before = d->outputs->updates;
        Scm_Score_t actual;
        Scm_SearchBegin( d );
        Scm_SearchEdit( d, lit, &list[best].M );
        actual = Scm_SearchLoad(d, &d->bestState);
        assert( actual.delay <= target && actual.delay == score.delay );
        Scm_CtxCommit( d->p, d->ctx );
        d->p->ModelDelay = actual.delay;
        if ( Scm_PoTreeDense(d->outputs, d->ctx) )
            Scm_PoTreeRebuild( d->outputs, d->p, d->pos, d->threshold );
        else
            Scm_PoTreeAffected( d->outputs, d->p, d->ctx, d->threshold, 0 );
        d->work += d->outputs->updates - before;
        d->cachedBase = actual;
        d->baseValid = 1;
        Scm_CtxTailInvalidate( d->p, &r->shadow, d->ctx->vTrialSeeds, -1 );
        d->area = bestArea;
        d->edits++;
    }
    ABC_FREE( list );
    return !d->ctx->fError;
}

// Root order: path delay, then the gate's stage delay (a work schedule only, never an acceptance rule).
typedef struct Scm_Root_t_ Scm_Root_t;
struct Scm_Root_t_
{
    int            lit;        // negative for a side root
    int            ordinal;
    float          path, stage;
};

/**Function*************************************************************

  Synopsis    [Orders roots by path delay, then by stage delay, then by position.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_RootCompare( const void * pa, const void * pb )
{
    const Scm_Root_t * a = (const Scm_Root_t *)pa, * b = (const Scm_Root_t *)pb;
    if ( a->path != b->path ) return a->path > b->path ? -1 : 1;
    if ( a->stage != b->stage ) return a->stage > b->stage ? -1 : 1;
    return (a->ordinal > b->ordinal) - (a->ordinal < b->ordinal);
}

/**Function*************************************************************

  Synopsis    [Orders roots by stage delay, then by position.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_RootStageCompare( const void * pa, const void * pb )
{
    const Scm_Root_t * a = (const Scm_Root_t *)pa, * b = (const Scm_Root_t *)pb;
    if ( a->stage != b->stage ) return a->stage > b->stage ? -1 : 1;
    if ( a->path != b->path ) return a->path > b->path ? -1 : 1;
    return (a->ordinal > b->ordinal) - (a->ordinal < b->ordinal);
}

/**Function*************************************************************

  Synopsis    [The delay a literal's gate adds to its latest input.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static float Scm_ManStageDelay( Scm_Man_t * p, int lit )
{
    Scm_Mat_t * m = Scm_ObjMatch(p, lit >> 1, lit & 1);
    float input = 0;
    int k;
    if ( m->fCompl )
        input = p->pArrMax[lit^1];
    else
    {
        Mio_Cell2_t * cell = Scm_ManCell(p, m->Gate);
        if ( cell->nFanins )
        {
            int * cut = Scm_CutFromHandle(Scm_ObjCutSet(p, lit >> 1), m->CutH);
            for ( k = 0; k < (int)cell->nFanins; k++ )
            {
                int child = Abc_Var2Lit(Scm_CutLeaves(cut)[Scm_CfgVar(m->Cfg, k)], Scm_CfgCompl(m->Cfg, k));
                input = fmaxf(input, p->pArrMax[child]);
            }
        }
    }
    return fmaxf(0, p->pArrMax[lit] - input);
}

/**Function*************************************************************

  Synopsis    [Refines the selected cover.]

  Description [Repair (delay pass), then up to delayRounds delay rounds of
  the bounded search; repair (area pass), then up to `recovery` area rounds.
  A delay round ranks the critical roots and interleaves one side root after
  every three; an area round visits the roots in reverse topological order.
  The work of a round is capped at cap trials per root (fast 64, quality 256,
  split over the delay rounds). After each round the cover is retimed from
  scratch and must match the incremental timing and area.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_ManRefineCover( Scm_Man_t * p )
{
    Scm_Search_t d = {0};
    Gia_Obj_t * o;
    float target;
    int i, j, c, phase, round, ok = 0;
    int recovery = p->pPars->fQuality ? 2 : 1;
    d.keep = p->pPars->fQuality ? 4 : 1;
    d.delayRounds = p->pPars->fQuality ? 4 : 2;
    if ( !Scm_ManRepair(p, 0) ) return 0;
    d.p = p;
    d.pos = Vec_IntAlloc(Gia_ManCoNum(p->pGia));
    Gia_ManForEachCo( p->pGia, o, i )
        Vec_IntPush( d.pos, Gia_ObjFaninLit0p(p->pGia, o) );
    if ( !Scm_ManTimeCover(p) ) goto done;
    d.area = (long long)Scm_ManCoverArea(p);
    target = p->ModelDelay;
    if ( p->pPars->ModelDelayTarget > 0 ) target = fmaxf(target, p->pPars->ModelDelayTarget);
    for ( phase = 0; phase < 2; phase++ )
        for ( round = 0; round < (phase ? recovery : d.delayRounds); round++ )
        {
            Scm_Root_t * ranked;
            Scm_Prune_t * r;
            float incremental;
            int before = d.edits, n = Gia_ManObjNum(p->pGia), count = 0, budgetRoots = 0;
            int cap = p->pPars->fQuality ? 256 : 64;
            if ( !phase && p->pPars->ModelDelayTarget > 0 && p->ModelDelay <= p->pPars->ModelDelayTarget ) break;
            if ( phase == 1 && round == 0 )
            {
                if ( !Scm_ManRepair(p, 1) || !Scm_ManTimeCover(p) ) goto done;
                d.area = (long long)Scm_ManCoverArea(p);
                target = p->ModelDelay;
                if ( p->pPars->ModelDelayTarget > 0 ) target = fmaxf(p->ModelDelay, p->pPars->ModelDelayTarget);
            }
            d.threshold = .01*SCM_CRITICAL_PCT*target;
            // the search scores exact logic area: no buffer-area envelopes
            d.ctx = Scm_CtxStart(p, 0);
            if ( !d.ctx ) goto done;
            d.ctx->fFullPropagation = 1;
            d.baseValid = 0;
            d.outputs = Scm_PoTreeStart(p, d.pos, d.threshold);
            d.ctx->vScoreOutputs = Vec_IntAlloc(Gia_ManCoNum(p->pGia));
            d.ctx->pScorePrune = Scm_PruneStart(d.ctx, d.threshold);
            // round-start tails of every mapped literal rank the shortlist and the roots; acceptance never uses them
            if ( !Scm_CtxTailBuildAll(p, d.ctx) ) goto done;
            if ( !phase ) cap = (cap + d.delayRounds - 1) / d.delayRounds;
            ranked = ABC_ALLOC(Scm_Root_t, 2*n);
            for ( j = 1; j < n; j++ )
            {
                i = phase ? n-j : j;
                o = Gia_ManObj(p->pGia, i);
                if ( !Gia_ObjIsAnd(o) ) continue;
                for ( c = 0; c < 2; c++ )
                {
                    int lit = 2*i+c, sideRoot = 0;
                    float path;
                    if ( !Scm_ObjMapRefNum(p, i, c) ) continue;
                    path = Scm_CtxScore(p, d.ctx, lit, 0);
                    if ( !phase && d.ctx->pTailValid[lit] && d.ctx->pTails[lit].nFans && path < d.threshold )
                    {
                        if ( Scm_SearchCritCap(&d, lit, Scm_ObjMatch(p, i, c)) <= 0 ) continue;
                        sideRoot = 1;
                    }
                    if ( !sideRoot ) budgetRoots++;
                    ranked[count].lit = sideRoot ? -lit : lit;
                    ranked[count].ordinal = count;
                    ranked[count].path = isfinite(path) ? path : 0;
                    ranked[count].stage = Scm_ManStageDelay(p, lit);
                    count++;
                }
            }
            // the root list is frozen for the round: newly activated roots wait for the next round
            if ( !phase )
            {
                Scm_Root_t * critical = ABC_ALLOC(Scm_Root_t, count), * side = ABC_ALLOC(Scm_Root_t, count);
                int nc = 0, ns = 0, ic = 0, is = 0, out = 0;
                qsort( ranked, count, sizeof(*ranked), Scm_RootCompare );
                for ( j = 0; j < count; j++ )
                {
                    if ( ranked[j].lit >= 0 )
                        critical[nc++] = ranked[j];
                    else
                    {
                        int lit = -ranked[j].lit;
                        side[ns] = ranked[j];
                        side[ns++].stage = Scm_SearchCritCap(&d, lit, Scm_ObjMatch(p, lit >> 1, lit & 1));
                    }
                }
                qsort( side, ns, sizeof(*side), Scm_RootStageCompare );
                // three critical roots, then one side root; the critical roots alone set the budget
                while ( ic < nc || is < ns )
                {
                    for ( j = 0; j < 3 && ic < nc; j++ )
                        ranked[out++] = critical[ic++];
                    if ( is < ns ) ranked[out++] = side[is++];
                }
                assert( out == count );
                ABC_FREE( critical );
                ABC_FREE( side );
            }
            d.limit = d.work + (unsigned long long)cap * (budgetRoots + Gia_ManCoNum(p->pGia) + 1);
            for ( j = 0; j < count && d.work < d.limit; j++ )
            {
                int lit = ranked[j].lit;
                d.sideRoot = lit < 0;
                if ( lit < 0 ) lit = -lit;
                if ( !Scm_ObjMapRefNum(p, lit >> 1, lit & 1) ) continue;
                if ( !Scm_SearchRoot(&d, lit, phase, target) ) { ABC_FREE( ranked ); goto done; }
                d.sideRoot = 0;
                target = fminf(target, p->ModelDelay);
                if ( p->pPars->ModelDelayTarget > 0 ) target = fmaxf(target, p->pPars->ModelDelayTarget);
            }
            ABC_FREE( ranked );
            r = (Scm_Prune_t *)d.ctx->pScorePrune;
            Scm_PruneStop( r );
            d.ctx->pScorePrune = NULL;
            Scm_PoTreeStop( d.outputs );
            d.outputs = NULL;
            Scm_CtxRecycle( p, d.ctx );
            d.ctx = NULL;
            // consistency check against a full retiming (not a selection or a rollback)
            incremental = p->ModelDelay;
            if ( !Scm_ManTimeCover(p) || !Scm_DelayClose(p->ModelDelay, incremental) ||
                 (p->ModelDelay > target && !Scm_DelayClose(p->ModelDelay, target)) || (long long)Scm_ManCoverArea(p) != d.area ) goto done;
            if ( d.edits == before ) break;
        }
    ok = 1;
done:
    Scm_PoTreeStop( d.outputs );
    if ( d.ctx )
    {
        Scm_PruneStop( (Scm_Prune_t *)d.ctx->pScorePrune );
        Scm_CtxFree( d.ctx );
    }
    ABC_FREE( d.bestState.data );
    Vec_IntFree( d.pos );
    return ok;
}
