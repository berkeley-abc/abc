/* Private implementation included by giaScmap.c. */
/* SCMap uses paired size/buffer envelopes with family-average sink caps.
   A paired constant-arc seed supplies implementations for unused nodes.
   Cheap forward repair proposes a cover, then bounded delay/area search
   checks affected-output timing using the same fitted model. Screening
   tails are approximate; committed focused moves retain propagated state.
   No backend STA or buffering/sizing result participates in selection. */

/* Keep the rise/fall arrival, slew and tail of the same implementation. */
static float Scm_ManAffFastScore(Scm_Man_t *p,Scm_AffElaCtx_t *ctx,int lit,int trial)
{
    if(ctx->fRiseFall) {
        Scm_RfPair_t a=trial?ctx->pTrialArrRf[lit]:p->pAffExactRfArrs[lit];
        Scm_RfPair_t s=trial?ctx->pTrialSlewRf[lit]:p->pAffExactRfSlews[lit];
        Scm_RfPair_t tail=Scm_ManRfTailLinesEval(ctx->pTailLinesRf+lit,s);
        return Abc_MaxFloat(a.Value[0]+tail.Value[0],a.Value[1]+tail.Value[1]);
    }
    return (trial?ctx->pTrialArr[lit]:p->pAffExactArrs[lit])+
        Scm_ManAffElaTailLinesEval(ctx->pTailLines+lit,trial?ctx->pTrialSlew[lit]:p->pAffExactSlews[lit]);
}
static void Scm_ManAffFastTighten(Scm_Man_t *p,Scm_AffElaCtx_t *ctx,int obj)
{
    if(!ctx->fRiseFall) { Scm_ManAffElaTightenInputs(p,ctx,obj);return; }
    for(int pass=1;pass>=0;pass--) for(int c=0;c<2;c++) {
        int lit=2*obj+c;
        Scm_Mat_t *m=Scm_ObjMatchD(p,obj,c);
        if(!Scm_ObjMapRefNum(p,obj,c) || !!m->fCompl!=pass) continue;
        Scm_RfPair_t tail=Scm_ManRfTailLinesEval(ctx->pTailLinesRf+lit,p->pAffExactRfSlews[lit]);
        Mio_Cell2_t *cell=m->fCompl?p->pCells+3:Scm_ManCell(p,m->Gate);
        if(!cell->nFanins) continue;
        int *cut=m->fCompl?NULL:Scm_CutFromHandle(Scm_ObjCutSet(p,obj),m->CutH);
        Scm_RfPair_t load=Scm_ManRfLoad(p,lit);
        for(int k=0;k<(int)cell->nFanins;k++) {
            int child=m->fCompl?(lit^1):Abc_Var2Lit(Scm_CutLeaves(cut)[Scm_CfgVar(m->Cfg,k)],Scm_CfgCompl(m->Cfg,k));
            Scm_LinArc_t temp,*a=Scm_ManAffArcAtLoadRf(p,cell,k,load,&temp);
            Scm_ManAffElaRfTailAddArc(ctx->pTailLinesRf+child,a,load,tail);
            ctx->pTailAtBaseSlewRf[child]=Scm_ManRfTailLinesEval(ctx->pTailLinesRf+child,p->pAffExactRfSlews[child]);
            ctx->pTailValid[child]=1;
        }
    }
}
/* SCMap: gain-seeded forward repair using current fanin arrival/slew,
   exact reference-counted cell area and fitted library cost envelopes.
   Round-end timing refreshes never select between complete coverings. */
static int Scm_ManAffFastRefreshRoot( Scm_Man_t * p,
    Scm_AffElaCtx_t * pCtx, int iObj )
{
    int Pass, c;
    ++pCtx->Epoch;
    assert(pCtx->Epoch != 0);
    /* Direct implementation before the inverter on the opposite phase. */
    for ( Pass = 0; Pass < 2; Pass++ )
        for ( c = 0; c < 2; c++ )
            if ( Scm_ObjMapRefNum(p, iObj, c) &&
                 !!Scm_ObjMatchBest(p, iObj, c)->fCompl == Pass )
            {
                int Lit = Abc_Var2Lit(iObj, c);
                if ( pCtx->fRiseFall ? !Scm_ManAffElaEvalLitRf(p,pCtx,iObj,c) :
                     !Scm_ManAffElaEvalLit(p, pCtx, iObj, c) ) return 0;
                if(pCtx->fRiseFall) {
                    p->pAffExactRfArrs[Lit]=pCtx->pTrialArrRf[Lit];
                    p->pAffExactRfSlews[Lit]=pCtx->pTrialSlewRf[Lit];
                }
                p->pAffExactArrs[Lit] = pCtx->pTrialArr[Lit];
                p->pAffExactSlews[Lit] = pCtx->pTrialSlew[Lit];
            }
    return 1;
}

/* Diagnostic exact shared-area bookkeeping; not a cover selector. */
static long long Fr_LogicArea(Scm_Man_t *p)
{
    Gia_Obj_t *o;int i,c;long long area=0;
    Gia_ManForEachAnd(p->pGia,o,i) for(c=0;c<2;c++) if(Scm_ObjMapRefNum(p,i,c)) {
        Scm_Mat_t *m=Scm_ObjMatchD(p,i,c);
        area+=m->fCompl?p->InvAreaW:Scm_ManCell(p,m->Gate)->AreaW;
    }
    Gia_ManForEachCiId(p->pGia,i,c) if(Scm_ObjMapRefNum(p,i,1)) area+=p->InvAreaW;
    return area;
}
static int Scm_ManAffFastRepairPart( Scm_Man_t * p, int part )
{
    Gia_Obj_t * pObj;
    float Target = p->pPars->ModelDelayTarget > 0 ? fmaxf(p->AffExactDelay, p->pPars->ModelDelayTarget) : p->AffExactDelay;
    int Round, i, c;
    int protect=0;
    int phases=1;
    assert(phases>=0 && phases<=2);
#ifdef SCM_AFF_REPAIR_START_VERIFY
    SCM_AFF_REPAIR_START_VERIFY(p);
#endif
    /* Unmapped nodes retain the NF seed implementation.
       Transactions require the D slot. */
    Gia_ManForEachAnd(p->pGia, pObj, i)
        for ( c = 0; c < 2; c++ )
            if ( !Scm_ObjMapRefNum(p, i, c) )
            {
                Scm_ObjMatchD(p, i, c)->fBest = 1;
                Scm_ObjMatchA(p, i, c)->fBest = 0;
            }
    /* The NF seed already counts the CI inverter edge. */
    for ( Round = part==2?1:0; Round < (part==1?1:2); Round++ )
    {
        Scm_AffElaCtx_t * pCtx;
        int delayPass=phases && Round==0, areaPass=phases && Round>0;
        int releaseArea=phases==2 && delayPass, edits=0;
        long long trackedArea=phases?Fr_LogicArea(p):0, startArea=trackedArea;
        if ( !Scm_ManAffElaTimeCover(p) || !Scm_ManAffElaRebuildTails(p) ) return 0;
        pCtx = Scm_ManAffElaCtxStart(p);
        if ( !pCtx ) return 0;
        /* Delay pass may trade logic area for timing. The second pass restores
           the ordinary non-increasing-area candidate filter. */
        if(releaseArea) ABC_FREE(pCtx->pBufferAreas);
        if(pCtx->fRiseFall) {
            Gia_ManForEachObjReverseWithBoxes(p->pGia,pObj,i)
                for(c=0;c<2;c++) if(Scm_ObjMapRefNum(p,i,c))
                    if(!Scm_ManAffElaTailBuild(p,pCtx,2*i+c)) {Scm_ManAffElaCtxFree(pCtx);return 0;}
        }
        Gia_ManForEachObjWithBoxes(p->pGia, pObj, i)
        {
            if ( !Gia_ObjIsAnd(pObj) || Gia_ObjIsBuf(pObj) ) continue;
            if ( !Scm_ManAffFastRefreshRoot(p, pCtx, i) )
            {
                Scm_ManAffElaCtxFree(pCtx);
                return 0;
            }
            for ( c = 0; c < 2; c++ )
            if ( Scm_ObjMapRefNum(p, i, c) )
            {
                int Lit = Abc_Var2Lit(i, c), nList = 0, nAlloc = 0, Best = -1, q;
                Scm_Mat_t Old = *Scm_ObjMatchD(p, i, c);
                Scm_AffElaCand_t * pList = NULL;
                word Freed;
                int fAreaRecovery;
                float BestScore = Scm_ManAffFastScore(p,pCtx,Lit,0), OriginalScore=BestScore;
                /* Optimize delay near the seed's worst path; recover area
                   on other paths. Both objectives preserve the exact
                   cell-area bound and use the same fitted timing target. */
                fAreaRecovery = !(0) &&
                    BestScore < 0.01f * p->pPars->nPaperAffineElaCritical * Target;
                if(delayPass && fAreaRecovery) continue; /* reserve area work for pass two */
                if(phases) fAreaRecovery=areaPass;
                Vec_IntClear(pCtx->vOldSeeds);
                pCtx->pCollectSeeds = pCtx->vOldSeeds;
                Freed = Scm_ManAffElaDerefRec(p, pCtx, i, c, &Old);
                pCtx->pCollectSeeds = NULL;
                pCtx->BufferFreed = Freed;
                Scm_ManAffElaCandidates(p, i, c, &Old, releaseArea?(~(word)0)/4:Freed+1,
                    &pList, &nList, &nAlloc);
                for ( q = 0; !pCtx->fError && q < nList; q++ )
                {
                    float Delay, Score;
                    int Status = Scm_ManAffElaTryCandidate(p, pCtx, i, c,
                        &Old, pList + q, Target, 0, &Delay);
                    if ( Status < 0 ) { pCtx->fError = 1; break; }
                    if ( !Status ) continue;
                    Score = Scm_ManAffFastScore(p,pCtx,Lit,1);
                    /* Preserve near-critical local path quality during cheap area recovery.
                       This is a local surrogate constraint, not a global timing proof. */
                    if(protect && areaPass && OriginalScore>=.01f*p->pPars->nPaperAffineElaCritical*Target && Score>OriginalScore) continue;
                    if ( fAreaRecovery ?
                         (pList[q].Area < (Best >= 0 ? pList[Best].Area : Freed) ||
                          (Best >= 0 && pList[q].Area == pList[Best].Area && Score < BestScore)) :
                         (Score < BestScore - 1.0e-3f ||
                          (Best >= 0 && fabsf(Score - BestScore) <= 1.0e-3f &&
                           pList[q].Area < pList[Best].Area)) )
                        BestScore = Score, Best = q;
                }
                if ( !pCtx->fError && Best >= 0 )
                {
                    assert(releaseArea || pList[Best].Area <= Freed);
                    if(phases) trackedArea+=(long long)pList[Best].Area-(long long)Freed;
                    edits++;
                    if ( Scm_ManAffElaApplyCandidate(p, pCtx, i, c,
                            pList + Best) < 0 ) pCtx->fError = 1;
#ifdef SCM_AFF_REPAIR_AREA_VERIFY
                    SCM_AFF_REPAIR_AREA_VERIFY(p);
#endif
                }
                else
                {
                    word Restored = Scm_ManAffElaRefRec(p, pCtx, i, c, &Old);
                    (void)Restored;
                    assert(Restored == Freed);
                    *Scm_ObjMatchD(p, i, c) = Old;
                }
                ABC_FREE(pList);
                if ( pCtx->fError ) { Scm_ManAffElaCtxFree(pCtx); return 0; }
            }
            Scm_ManAffFastTighten(p, pCtx, i);
        }
        Scm_ManAffElaCtxFree(pCtx);
        if(phases) {
            long long actual=Fr_LogicArea(p);
            if(actual!=trackedArea || (areaPass && actual>startArea)) {
                puts("FR_FAIL exact shared-area bookkeeping");return 0;
            }
            /* Materialize the chosen cover only. No backend timing, best-cover
               comparison or rollback. Warm-pass feasibility is approximate,
               exactly as in the existing cheap repair; bounded search below
               still uses full affected-output checks. */
            if(!Scm_ManAffElaTimeCover(p)) return 0;
            if(p->pPars->fVerbose) printf("SCMAP_REPAIR_PHASE mode=%d pass=%s edits=%d area=%lld initial_area=%lld delay=%.9g target=%.9g\n",
                phases,delayPass?"delay":"area",edits,actual,startArea,p->AffExactDelay,Target);
            /* Keep the achieved modeled delay as the next pass target. This
               tightens the local model constraint; it is not cover rollback. */
            Target=fminf(Target,p->AffExactDelay);
            if ( p->pPars->ModelDelayTarget > 0 ) Target = fmaxf(Target, p->pPars->ModelDelayTarget);
        }
    }
    if ( !Scm_ManAffElaTimeCover(p) ) return 0;
    Scm_ManUpdateStats(p);
    return 1;
}

/* Bounded SCMap refinement: delay-only affine search, then exact shared-area
   recovery under the achieved fitted delay. No backend timing is called.
   Every trial propagates changed matches and loads to affected outputs. */

/* Exact maximum and incremental pressure over the fixed output multiset.
   Trial leaves are restored from the incumbent before returning. Duplicate
   PO drivers keep separate leaves, preserving their multiplicity and order.
   Only pressure additions regroup; delay comparisons remain bit exact. */
typedef struct {
    int size, count, depth, *head, *next, *degree;
    float *delay;
    double *pressure;
    unsigned long updates;
} Po_Score;

static void Po_Set(Po_Score *q,int index,Scm_RfPair_t a,double threshold)
{
    int k=q->size+index;
    q->delay[k]=fmaxf(0,fmaxf(a.Value[0],a.Value[1]));
    q->pressure[k]=fmax(0,(double)a.Value[0]-threshold)+fmax(0,(double)a.Value[1]-threshold);
    q->updates++;
    for(k>>=1;k;k>>=1) {
        q->delay[k]=fmaxf(q->delay[2*k],q->delay[2*k+1]);
        q->pressure[k]=q->pressure[2*k]+q->pressure[2*k+1];
        q->updates++;
    }
}

static Po_Score *Po_Start(Scm_Man_t *p,Vec_Int_t *pos,double threshold)
{
    Po_Score *q=ABC_CALLOC(Po_Score,1);
    q->count=Vec_IntSize(pos);q->size=1;
    while(q->size<q->count) q->size*=2,q->depth++;
    q->degree=ABC_CALLOC(int,2*Gia_ManObjNum(p->pGia));
    q->head=ABC_ALLOC(int,2*Gia_ManObjNum(p->pGia));
    memset(q->head,0xff,sizeof(int)*2*Gia_ManObjNum(p->pGia));
    q->next=ABC_ALLOC(int,q->count);
    q->delay=ABC_CALLOC(float,2*q->size);
    q->pressure=ABC_CALLOC(double,2*q->size);
    for(int i=0;i<q->count;i++) {
        int lit=Vec_IntEntry(pos,i);
        q->next[i]=q->head[lit];q->head[lit]=i;q->degree[lit]++;
        Scm_RfPair_t a=p->pAffExactRfArrs[lit];int k=q->size+i;
        q->delay[k]=fmaxf(0,fmaxf(a.Value[0],a.Value[1]));
        q->pressure[k]=fmax(0,(double)a.Value[0]-threshold)+fmax(0,(double)a.Value[1]-threshold);
    }
    for(int k=q->size-1;k;k--) {
        q->delay[k]=fmaxf(q->delay[2*k],q->delay[2*k+1]);
        q->pressure[k]=q->pressure[2*k]+q->pressure[2*k+1];
    }
    q->updates=0;
    return q;
}

static void Po_Affected(Po_Score *q,Scm_Man_t *p,Scm_AffElaCtx_t *ctx,double threshold,int trial)
{
    int i,lit;
    Vec_IntForEachEntry(ctx->vScoreOutputs,lit,i) {
        if(q->head[lit]<0 || ctx->pComputed[lit]!=ctx->Epoch) continue;
        Scm_RfPair_t a=trial?ctx->pTrialArrRf[lit]:p->pAffExactRfArrs[lit];
        for(int index=q->head[lit];index>=0;index=q->next[index]) Po_Set(q,index,a,threshold);
    }
}

/* A score query changes and restores leaves: bound its tree work against
   one linear scan. This is a runtime choice only, not a candidate selector. */
static int Po_Dense(Po_Score *q,Scm_AffElaCtx_t *ctx)
{
    int i,lit,n=0;
    Vec_IntForEachEntry(ctx->vScoreOutputs,lit,i) n+=q->degree[lit];
    return (unsigned long long)n*(q->depth+1)>=q->count;
}
static void Po_Rebuild(Po_Score *q,Scm_Man_t *p,Vec_Int_t *pos,double threshold)
{
    for(int i=0;i<q->count;i++) {
        Scm_RfPair_t a=p->pAffExactRfArrs[Vec_IntEntry(pos,i)];int k=q->size+i;
        q->delay[k]=fmaxf(0,fmaxf(a.Value[0],a.Value[1]));
        q->pressure[k]=fmax(0,(double)a.Value[0]-threshold)+fmax(0,(double)a.Value[1]-threshold);
        q->updates++;
    }
    for(int k=q->size-1;k;k--) {
        q->delay[k]=fmaxf(q->delay[2*k],q->delay[2*k+1]);
        q->pressure[k]=q->pressure[2*k]+q->pressure[2*k+1];q->updates++;
    }
}

static void Po_Stop(Po_Score *q)
{
    if(!q) return;
    ABC_FREE(q->head);ABC_FREE(q->next);ABC_FREE(q->degree);ABC_FREE(q->delay);ABC_FREE(q->pressure);ABC_FREE(q);
}

typedef struct { float delay; double pressure; } Df_Score;
typedef struct { int lit; Scm_Mat_t old; long long delta; } Df_Undo;
typedef struct { int lit; float arr, slew; Scm_RfPair_t ar, sr; } Df_SavedLit;
typedef struct { Df_SavedLit *data; int size, cap; Df_Score score; } Df_Snapshot;
typedef struct {
    Scm_Man_t *p; Scm_AffElaCtx_t *ctx;
    Vec_Int_t *pos; double threshold; long long area;
    unsigned long trials, visits, screens; int edits, keep, delayRounds, screenGate, reuse;
    Df_Snapshot bestState; unsigned reused;
    int prune, committing, baseValid; Df_Score cachedBase; float acceptBound;
    unsigned long scoreFallbacks, overTarget, noWin;
    unsigned long long work, limit;
    int outputCache, sideRoot; unsigned long sideTried, sideWon; Po_Score *outputs;
} Df_Man;

/* Verification tolerance only. At long path delays a single float ULP
   exceeds 0.001 ps. Never use this tolerance to rank or accept a move. */
static float Df_CheckTolerance(float a,float b)
{
    float scale=fmaxf(fabsf(a),fabsf(b));
    return fmaxf(1e-3f,4.0f*(nextafterf(scale,INFINITY)-scale));
}
static int Df_CheckClose(float a,float b)
{
    return isfinite(a) && isfinite(b) && fabsf(a-b)<=Df_CheckTolerance(a,b);
}

static long long Df_Area(Scm_Man_t *p)
{
    Gia_Obj_t *o; int i,c; long long area=0;
    Gia_ManForEachAnd(p->pGia,o,i) for(c=0;c<2;c++)
        if(Scm_ObjMapRefNum(p,i,c)) {
            Scm_Mat_t *m=Scm_ObjMatchD(p,i,c);
            area+=m->fCompl?p->InvAreaW:Scm_ManCell(p,m->Gate)->AreaW;
        }
    Gia_ManForEachCiId(p->pGia,i,c) if(Scm_ObjMapRefNum(p,i,1)) area+=p->InvAreaW;
    return area;
}
static Df_Score Df_FullMeasure(Df_Man *d,int trial)
{
    Df_Score s={0,0}; int i,lit,t;
    Vec_IntForEachEntry(d->pos,lit,i) {
        Scm_RfPair_t a=d->p->pAffExactRfArrs[lit];
        if(trial && d->ctx->pComputed[lit]==d->ctx->Epoch) a=d->ctx->pTrialArrRf[lit];
        for(t=0;t<2;t++) {
            s.delay=fmaxf(s.delay,a.Value[t]);
            s.pressure+=fmax(0,(double)a.Value[t]-d->threshold);
        }
    }
    return s;
}
/* Evaluate only changed PO drivers, then restore the incumbent aggregate.
   Full propagation/guard decides which arrivals are valid before this call. */
static Df_Score Df_Measure(Df_Man *d,int trial)
{
    if(!d->outputs) {
        d->work+=2*(unsigned)Vec_IntSize(d->pos);
        return Df_FullMeasure(d,trial);
    }
    Po_Score *q=d->outputs;unsigned long before=q->updates;
    /* Dense changes are cheaper to score by one linear PO scan. */
    if(trial && Po_Dense(q,d->ctx)) {
        d->work+=2*(unsigned)Vec_IntSize(d->pos);
        return Df_FullMeasure(d,trial);
    }
    if(trial) Po_Affected(q,d->p,d->ctx,d->threshold,1);
    Df_Score score={q->delay[1],q->pressure[1]};
    if(trial) Po_Affected(q,d->p,d->ctx,d->threshold,0);
    d->work+=q->updates-before;
#ifdef SCM_DF_VERIFY
    Df_Score full=Df_FullMeasure(d,trial);
    assert(score.delay==full.delay);
    assert(fabs(score.pressure-full.pressure)<=fmax(1e-9,8*DBL_EPSILON*q->count*fmax(1.,fabs(full.pressure))));
#endif
    return score;
}
static int Df_Better(Df_Score a,Df_Score b)
{
    if(a.delay<b.delay-1e-4f) return 1;
    if(a.delay>b.delay) return 0;
    return a.pressure<b.pressure-1e-4;
}
static void Df_Begin(Df_Man *d)
{
    Vec_IntClear(d->ctx->vTrialSeeds);
    d->ctx->pCollectSeeds=d->ctx->vTrialSeeds;
}
static Df_Undo Df_Edit(Df_Man *d,int lit,Scm_Mat_t *m)
{
    Scm_Man_t *p=d->p; int i=lit>>1,c=lit&1;
    Df_Undo u={lit,*Scm_ObjMatchD(p,i,c),0};
    word freed=Scm_ManAffElaDerefRec(p,d->ctx,i,c,&u.old);
    *Scm_ObjMatchD(p,i,c)=*m;
    word added=Scm_ManAffElaRefRec(p,d->ctx,i,c,m);
    u.delta=(long long)added-(long long)freed;
    return u;
}
static void Df_Restore(Df_Man *d,Df_Undo u)
{
    Scm_Man_t *p=d->p; int i=u.lit>>1,c=u.lit&1;
    d->ctx->pCollectSeeds=NULL;
    word removed=Scm_ManAffElaDerefRec(p,d->ctx,i,c,Scm_ObjMatchD(p,i,c));
    *Scm_ObjMatchD(p,i,c)=u.old;
    word restored=Scm_ManAffElaRefRec(p,d->ctx,i,c,&u.old);
    (void)removed; (void)restored;
    assert((long long)removed-(long long)restored==u.delta);
}
static Scm_AffElaCand_t *Df_Candidates(Df_Man *d,int lit,int areaOnly,int *count)
{
    Scm_Man_t *p=d->p;int alloc=0,i=lit>>1,c=lit&1;
    Scm_AffElaCand_t *list=NULL;Scm_Mat_t old=*Scm_ObjMatchD(p,i,c);
    d->ctx->pCollectSeeds=NULL;
    if(!areaOnly) {
        /* The delay shortlist consumes matches, not precomputed area. Exact
           shared area is still counted by Df_Edit for every timed trial. */
        Scm_ManAffElaCandidatesInt(p,i,c,&old,(~(word)0)/4,&list,count,&alloc,0);
#ifdef SCM_DF_VERIFY
        Scm_AffElaCand_t *reference=NULL;int nr=0,ar=0;
        word freed=Scm_ManAffElaDerefRec(p,d->ctx,i,c,&old);
        Scm_ManAffElaCandidates(p,i,c,&old,(~(word)0)/4,&reference,&nr,&ar);
        word restored=Scm_ManAffElaRefRec(p,d->ctx,i,c,&old);
        assert(freed==restored && nr==*count);
        for(int k=0;k<nr;k++) assert(Scm_PaperMatSame(&reference[k].M,&list[k].M));
        ABC_FREE(reference);
#endif
        return list;
    }
    word freed=Scm_ManAffElaDerefRec(p,d->ctx,i,c,&old);
    /* No logic-area veto in delay rounds. Positive costs still allow exact
       bounded traversal in the later, strictly area-reducing rounds. */
    Scm_ManAffElaCandidates(p,i,c,&old,areaOnly?freed:(~(word)0)/4,&list,count,&alloc);
    word restored=Scm_ManAffElaRefRec(p,d->ctx,i,c,&old);
    (void)restored;
    assert(restored==freed);
    return list;
}

#ifdef SCM_DF_VERIFY
/* An independent full affine traversal checks trial propagation in the
   sanitizer build only. Its results never rank or accept a candidate. */
static void Df_VerifyTrial(Df_Man *d,Df_Score expected)
{
    Scm_Man_t *p=d->p;int n=d->ctx->nLits,i,t;
    float delay=p->AffExactDelay;
    float *a=ABC_ALLOC(float,n),*s=ABC_ALLOC(float,n);
    Scm_RfPair_t *ar=ABC_ALLOC(Scm_RfPair_t,n),*sr=ABC_ALLOC(Scm_RfPair_t,n);
    memcpy(a,p->pAffExactArrs,sizeof(float)*n);memcpy(s,p->pAffExactSlews,sizeof(float)*n);
    memcpy(ar,p->pAffExactRfArrs,sizeof(*ar)*n);memcpy(sr,p->pAffExactRfSlews,sizeof(*sr)*n);
    assert(Scm_ManAffAuditTimingRf(p));
    for(i=0;i<n;i++) if(!d->ctx->fScoreRejected && !d->ctx->nScorePruned && Scm_ObjMapRefNum(p,i>>1,i&1)) for(t=0;t<2;t++) {
        int trial=d->ctx->pComputed[i]==d->ctx->Epoch;
        float aa=trial?d->ctx->pTrialArrRf[i].Value[t]:ar[i].Value[t];
        float ss=trial?d->ctx->pTrialSlewRf[i].Value[t]:sr[i].Value[t];
        assert(Df_CheckClose(aa,p->pAffExactRfArrs[i].Value[t]));
        assert(Df_CheckClose(ss,p->pAffExactRfSlews[i].Value[t]));
    }
    if(d->ctx->fScoreRejected) assert(p->AffExactDelay>d->acceptBound);
    else assert(Df_CheckClose(expected.delay,p->AffExactDelay));
    if(d->ctx->nScorePruned) {
        Df_Score complete=Df_FullMeasure(d,0);
        assert(fabs(complete.pressure-expected.pressure)<=1e-6*fmax(1.0,fabs(complete.pressure)));
    }
    memcpy(p->pAffExactArrs,a,sizeof(float)*n);memcpy(p->pAffExactSlews,s,sizeof(float)*n);
    memcpy(p->pAffExactRfArrs,ar,sizeof(*ar)*n);memcpy(p->pAffExactRfSlews,sr,sizeof(*sr)*n);
    p->AffExactDelay=delay;ABC_FREE(a);ABC_FREE(s);ABC_FREE(ar);ABC_FREE(sr);
}
#endif
/* Sparse timing snapshots belong to one root's unchanged incumbent. They
   are restored only after reconstructing the identical structural edit.
   Never share a snapshot across commits or roots. */
static void Df_Save(Df_Man *d, Df_Snapshot *save, Df_Score score)
{
    Scm_AffElaCtx_t *ctx=d->ctx;
    save->size=Vec_IntSize(ctx->vAffected);save->score=score;
    if(save->cap<save->size) {
        save->cap=Abc_MaxInt(save->size,2*save->cap+16);
        save->data=ABC_REALLOC(Df_SavedLit,save->data,save->cap);
    }
    for(int i=0;i<save->size;i++) {
        int x=Vec_IntEntry(ctx->vAffected,i);Df_SavedLit *v=save->data+i;
        assert(ctx->pComputed[x]==ctx->Epoch);
        v->lit=x;v->arr=ctx->pTrialArr[x];v->slew=ctx->pTrialSlew[x];
        v->ar=ctx->pTrialArrRf[x];v->sr=ctx->pTrialSlewRf[x];
    }
}
static Df_Score Df_Load(Df_Man *d, Df_Snapshot *save)
{
    Scm_AffElaCtx_t *ctx=d->ctx;
    ++ctx->Epoch;assert(ctx->Epoch);Vec_IntClear(ctx->vAffected);
    if(ctx->vScoreOutputs) Vec_IntClear(ctx->vScoreOutputs);
    ctx->pCollectSeeds=NULL;ctx->fScoreRejected=0;ctx->nScorePruned=0;ctx->fScorePrune=0;
    d->work+=save->size;
    for(int i=0;i<save->size;i++) {
        Df_SavedLit *v=save->data+i;int x=v->lit;
        Vec_IntPush(ctx->vAffected,x);ctx->pComputed[x]=ctx->Epoch;
        if(ctx->vScoreOutputs && ctx->pIsPo[x]) Vec_IntPush(ctx->vScoreOutputs,x);
        ctx->pTrialArr[x]=v->arr;ctx->pTrialSlew[x]=v->slew;
        ctx->pTrialArrRf[x]=v->ar;ctx->pTrialSlewRf[x]=v->sr;
    }
    d->reused++;
#ifdef SCM_DF_VERIFY
    if(d->reuse) Df_VerifyTrial(d,save->score);
#endif
    return save->score;
}
static int Df_Evaluate(Df_Man *d,Df_Score *s)
{
    Scm_AffElaCtx_t *ctx=d->ctx;ctx->pCollectSeeds=NULL;d->trials++;
    ctx->fScorePrune=d->prune && !d->committing && (d->prune==2 || d->p->AffExactDelay>d->threshold);
    if(d->prune==2) {
        Rq_Man *r=(Rq_Man *)ctx->pScorePrune;r->reject=1;
        if(r->threshold!=d->acceptBound) {
            memset(r->shadow.pTailValid,0,ctx->nLits);
            r->threshold=d->acceptBound;
        }
    }
    ctx->fScoreRejected=0;
    ctx->nScorePruned=0;ctx->ScorePruneCutoff=0;
    if(ctx->fScorePrune) {
        int x,i;Vec_IntForEachEntry(ctx->vTrialSeeds,x,i)
            ctx->ScorePruneCutoff=Abc_MaxInt(ctx->ScorePruneCutoff,x>>1);
    }
    if(!Scm_ManAffElaTimeLocal(d->p,ctx,Gia_ManObjNum(d->p->pGia)-1)) return 0;
    d->visits+=Vec_IntSize(ctx->vAffected);
    d->work+=1+(unsigned)Vec_IntSize(ctx->vAffected);
    if(ctx->fScoreRejected) {s->delay=FLT_MAX;s->pressure=0;}
    else *s=Df_Measure(d,1);
    ctx->fScorePrune=0;
    /* Max-delay ordering is still relevant below the pressure threshold.
       In that unusual case, compute the complete trial instead. */
    if(ctx->nScorePruned && s->delay<=d->threshold) {
        d->scoreFallbacks++;ctx->nScorePruned=0;
        if(!Scm_ManAffElaTimeLocal(d->p,ctx,Gia_ManObjNum(d->p->pGia)-1)) return 0;
        d->visits+=Vec_IntSize(ctx->vAffected);*s=Df_Measure(d,1);
    }
#ifdef SCM_DF_VERIFY
    Df_VerifyTrial(d,*s);
#endif
    return isfinite(s->delay) && isfinite(s->pressure);
}
/* Cheap affine screening only ranks proposals. Full affected-output timing
   below remains the acceptance test. The delay screen has no area veto. */
static int Df_Screen(Df_Man *d,int lit,int root,Scm_AffElaCand_t *list,int n,
                     int areaOnly,int prefixSeeds,int selected[8])
{
    int fast[4]={-1,-1,-1,-1},small[4]={-1,-1,-1,-1},count=0;
    int keep=d->keep?d->keep:4;
    assert(keep>=1 && keep<=4);
    float costs[4]={0,0,0,0};
    for(int k=0;k<n;k++) {
        if(d->limit && d->work>=d->limit) break;
        Vec_IntShrink(d->ctx->vTrialSeeds,prefixSeeds);
        d->ctx->pCollectSeeds=d->ctx->vTrialSeeds;
        Df_Undo u=Df_Edit(d,lit,&list[k].M);
        d->ctx->fFullPropagation=0;d->screens++;
        int ok=Scm_ManAffElaTimeLocal(d->p,d->ctx,root>>1);
        d->ctx->fFullPropagation=1;
        d->work+=1+(unsigned)Vec_IntSize(d->ctx->vAffected);
        float score=FLT_MAX;
        if(ok) score=d->ctx->pTailValid[root] && d->ctx->pTailLinesRf[root].nFans ?
            Scm_ManAffFastScore(d->p,d->ctx,root,1):d->ctx->pTrialArr[root];
        Df_Restore(d,u);
        if(!ok || !isfinite(score)) return -1;
        if(d->screenGate && !areaOnly && score>=Scm_ManAffFastScore(d->p,d->ctx,root,0)-1e-4f) continue;
        for(int j=0;j<keep;j++) if(fast[j]<0 || score<costs[j]) {
            for(int z=keep-1;z>j;z--) fast[z]=fast[z-1],costs[z]=costs[z-1];
            fast[j]=k;costs[j]=score;break;
        }
        if(areaOnly) for(int j=0;j<keep;j++) if(small[j]<0 || list[k].Area<list[small[j]].Area) {
            for(int z=keep-1;z>j;z--) small[z]=small[z-1];
            small[j]=k;break;
        }
    }
    for(int j=0;j<keep;j++) if(fast[j]>=0) selected[count++]=fast[j];
    for(int j=0;j<keep;j++) if(small[j]>=0) {
        int exists=0;for(int k=0;k<count;k++) exists|=selected[k]==small[j];
        if(!exists) selected[count++]=small[j];
    }
    return count;
}

/* Capacitance that an off-critical sink adds to near-critical nets.
   This ranks candidates only; acceptance uses propagated fitted timing. */
static int Df_LeafCritical(Df_Man *d,int child)
{
    Scm_Man_t *p=d->p;
    if(!Scm_ObjMapRefNum(p,child>>1,child&1) || !d->ctx->pTailValid[child] || !d->ctx->pTailLinesRf[child].nFans) return 0;
    return Scm_ManAffFastScore(p,d->ctx,child,0)>=d->threshold;
}
static float Df_CritCap(Df_Man *d,int lit,Scm_Mat_t *m)
{
    Scm_Man_t *p=d->p;float cap=0;
    if(m->fCompl) return Df_LeafCritical(d,lit^1)?Scm_ManInvInputCap(p):0;
    if(!Scm_ObjCutSetId(p,lit>>1)) return 0;
    Mio_Cell2_t *cell=Scm_ManCell(p,m->Gate);
    if(!cell->nFanins) return 0;
    SC_Cell *scl=Scm_ManSclCell(p,cell);
    int *cut=Scm_CutFromHandle(Scm_ObjCutSet(p,lit>>1),m->CutH);
    for(int k=0;k<(int)cell->nFanins;k++) {
        int child=Abc_Var2Lit(Scm_CutLeaves(cut)[Scm_CfgVar(m->Cfg,k)],Scm_CfgCompl(m->Cfg,k));
        if(Df_LeafCritical(d,child)) cap+=Scm_ManCellPinCap(p,scl,k);
    }
    return cap;
}
static int Df_SideScreen(Df_Man *d,int lit,Scm_AffElaCand_t *list,int n,int selected[8])
{
    int keep=Abc_MinInt(8,3),count=0;float caps[8];
    float own=Df_CritCap(d,lit,Scm_ObjMatchD(d->p,lit>>1,lit&1));
    if(own<=0) return 0;
    for(int k=0;k<n;k++) {
        if(d->limit && d->work>=d->limit) break;
        d->work++; /* Charge each side-screen candidate, even if rejected. */
        float c=Df_CritCap(d,lit,&list[k].M);int j;
        if(c>=own*(1-1e-4f)) continue;
        for(j=0;j<count;j++) if(c<caps[j]) break;
        if(j>=keep) continue;
        if(count<keep) count++;
        for(int z=count-1;z>j;z--) caps[z]=caps[z-1],selected[z]=selected[z-1];
        caps[j]=c;selected[j]=k;
    }
    return count;
}
static int Df_Root(Df_Man *d,int lit,int areaOnly,float target)
{
    int n=0,best=-1;
    d->acceptBound=target;
    Df_Score base=d->prune && d->baseValid?d->cachedBase:Df_Measure(d,0),score=base;
    if(d->prune) {d->cachedBase=base;d->baseValid=1;}
    long long bestArea=d->area;
    Scm_AffElaCand_t *list=Df_Candidates(d,lit,areaOnly,&n);
    int selected[8];Df_Begin(d);
    int side=d->sideRoot && !areaOnly;
    int count=side?Df_SideScreen(d,lit,list,n,selected):Df_Screen(d,lit,lit,list,n,areaOnly,0,selected);
    if(side) d->sideTried+=count;
    if(count<0) {ABC_FREE(list);return 0;}
    for(int z=0;z<count;z++) {
        int k=selected[z];
        Df_Begin(d);Df_Undo u=Df_Edit(d,lit,&list[k].M);Df_Score q;
        int ok=Df_Evaluate(d,&q);long long area=d->area+u.delta;
        Df_Restore(d,u);if(!ok || d->ctx->fError) {ABC_FREE(list);return 0;}
        if(q.delay>target) {d->overTarget++;continue;}
        if(areaOnly ? (area<bestArea || (best>=0 && area==bestArea && Df_Better(q,score))) : Df_Better(q,score))
            {best=k;score=q;bestArea=area;
             if(d->reuse) Df_Save(d,&d->bestState,q);}
    }
    if(best>=0) {
        Df_Begin(d);Df_Edit(d,lit,&list[best].M);
        Df_Score actual;
        int timed=1;d->committing=1;
        if(d->reuse) actual=Df_Load(d,&d->bestState);
        else timed=Df_Evaluate(d,&actual);
        if(!timed || actual.delay>target+1e-4f || !Df_CheckClose(actual.delay,score.delay)) {ABC_FREE(list);return 0;}
        d->committing=0;
        Scm_ManAffElaCommitTail(d->p,d->ctx);d->p->AffExactDelay=actual.delay;
        if(d->outputs) {
            unsigned long before=d->outputs->updates;
            if(Po_Dense(d->outputs,d->ctx)) Po_Rebuild(d->outputs,d->p,d->pos,d->threshold);
            else Po_Affected(d->outputs,d->p,d->ctx,d->threshold,0);
            d->work+=d->outputs->updates-before;
        }
        if(d->prune) {
            d->cachedBase=actual;d->baseValid=1;
            Rq_Man *r=(Rq_Man *)d->ctx->pScorePrune;
            Scm_ManAffElaTailInvalidate(d->p,&r->shadow,d->ctx->vTrialSeeds,-1);
        }
        d->area=bestArea;d->edits++;d->sideWon+=side;
#ifdef SCM_DF_VERIFY
        assert(Df_Area(d->p)==d->area);
#endif
    }
    if(best<0) d->noWin++;
    ABC_FREE(list);return !d->ctx->fError;
}
/* Rank critical roots by current path delay, then by the selected gate's
   stage contribution. These scores only schedule work, never accept edits. */
typedef struct { int lit,ordinal; float path,stage; } Df_Ranked;
static int Df_RankCompare(const void *pa,const void *pb)
{
    const Df_Ranked *a=(const Df_Ranked *)pa,*b=(const Df_Ranked *)pb;
    if(a->path!=b->path) return a->path>b->path?-1:1;
    if(a->stage!=b->stage) return a->stage>b->stage?-1:1;
    return (a->ordinal>b->ordinal)-(a->ordinal<b->ordinal);
}
/* Same eligible critical roots and work budget, different work order. */
static int Df_StageRankCompare(const void *pa,const void *pb)
{
    const Df_Ranked *a=(const Df_Ranked *)pa,*b=(const Df_Ranked *)pb;
    if(a->stage!=b->stage) return a->stage>b->stage?-1:1;
    if(a->path!=b->path) return a->path>b->path?-1:1;
    return (a->ordinal>b->ordinal)-(a->ordinal<b->ordinal);
}
static float Df_StageDelay(Scm_Man_t *p,int lit)
{
    Scm_Mat_t *m=Scm_ObjMatchD(p,lit>>1,lit&1);float input=0;
    if(m->fCompl) input=p->pAffExactArrs[lit^1];
    else {
        Mio_Cell2_t *cell=Scm_ManCell(p,m->Gate);
        if(cell->nFanins) {
            int *cut=Scm_CutFromHandle(Scm_ObjCutSet(p,lit>>1),m->CutH);
            for(int k=0;k<(int)cell->nFanins;k++) {
                int child=Abc_Var2Lit(Scm_CutLeaves(cut)[Scm_CfgVar(m->Cfg,k)],Scm_CfgCompl(m->Cfg,k));
                input=fmaxf(input,p->pAffExactArrs[child]);
            }
        }
    }
    return fmaxf(0,p->pAffExactArrs[lit]-input);
}
static int Scm_ManRefineCover(Scm_Man_t *p)
{
    Df_Man d={0};Gia_Obj_t *o;int i,c,ok=0;
    float initial, target;
    int recovery=1;
    d.keep=p->pPars->fQuality?4:1;
    d.delayRounds=p->pPars->fQuality?4:2;
    if(p->pPars->fQuality) recovery=2;
    d.screenGate=1;
    assert(d.keep>=1 && d.keep<=4 && d.delayRounds>=1);
    d.outputCache=1;
    d.prune=2;
    d.reuse=1;
    if(!Scm_ManAffFastRepairPart(p,1)) return 0;
    d.p=p;d.pos=Vec_IntAlloc(Gia_ManCoNum(p->pGia));
    Gia_ManForEachCo(p->pGia,o,i) Vec_IntPush(d.pos,Gia_ObjFaninLit0p(p->pGia,o));
    /* Every unused implementation is a legal seed for later cone activation. */
    Gia_ManForEachAnd(p->pGia,o,i) for(c=0;c<2;c++) if(!Scm_ObjMapRefNum(p,i,c)) {
        Scm_ObjMatchD(p,i,c)->fBest=1;Scm_ObjMatchA(p,i,c)->fBest=0;
    }
    if(!Scm_ManAffElaTimeCover(p)) goto done;
    d.area=Df_Area(p);initial=p->AffExactDelay;target=initial*p->pPars->RefineRelax;
    if ( p->pPars->ModelDelayTarget > 0 ) target = fmaxf(initial, p->pPars->ModelDelayTarget);
    assert(recovery>=0);
    for(int phase=0;phase<2;phase++) for(int round=0;round<(phase?recovery:d.delayRounds);round++) {
        if ( !phase && p->pPars->ModelDelayTarget > 0 && p->AffExactDelay <= p->pPars->ModelDelayTarget ) break;
        /* Alternate broad cheap delay repair with the focused bounded search.
           Rebuild the actual chosen affine state before the next exact round. */

        if(phase==1 && round==0) {
            if(!Scm_ManAffFastRepairPart(p,2) || !Scm_ManAffElaTimeCover(p)) goto done;
            d.area=Df_Area(p);target=p->AffExactDelay*p->pPars->RefineRelax;
            if ( p->pPars->ModelDelayTarget > 0 ) target = fmaxf(p->AffExactDelay, p->pPars->ModelDelayTarget);
        }
        int before=d.edits;d.threshold=.01*p->pPars->nPaperAffineElaCritical*target;
        d.ctx=Scm_ManAffElaCtxStart(p);if(!d.ctx) goto done;
        d.ctx->fFullPropagation=1;d.baseValid=0;
        if(d.outputCache) {d.outputs=Po_Start(p,d.pos,d.threshold);d.ctx->vScoreOutputs=Vec_IntAlloc(Gia_ManCoNum(p->pGia));}
        if(d.prune) d.ctx->pScorePrune=Rq_Start(d.ctx,d.threshold);
        /* Area envelopes are deliberately absent from the delay objective;
           exact physical logic-cell area is used during recovery. */
        ABC_FREE(d.ctx->pBufferAreas);
        /* Round-start tails guide the shortlist and critical-region work.
           Stale tails can affect ranking, never the exact acceptance bound. */
        Gia_ManForEachAndReverse(p->pGia,o,i) for(c=0;c<2;c++)
            if(Scm_ObjMapRefNum(p,i,c) && !Scm_ManAffElaTailBuild(p,d.ctx,2*i+c)) goto done;
        int n=Gia_ManObjNum(p->pGia),count=0,budgetRoots=0;
        int cap=p->pPars->fQuality?256:64;

        assert(cap>=0 && cap<=1048576);
        if(!phase) cap=(cap+d.delayRounds-1)/d.delayRounds;
        Df_Ranked *ranked=ABC_ALLOC(Df_Ranked,2*n);
        for(int j=1;j<n;j++) {
            i=phase?n-j:j;o=Gia_ManObj(p->pGia,i);if(!Gia_ObjIsAnd(o)) continue;
            for(c=0;c<2;c++) if(Scm_ObjMapRefNum(p,i,c)) {
                int lit=2*i+c;
                float path=Scm_ManAffFastScore(p,d.ctx,lit,0);
                int sideRoot=0;
                if(!phase && d.ctx->pTailValid[lit] && d.ctx->pTailLinesRf[lit].nFans && path<d.threshold) {
                    if(Df_CritCap(&d,lit,Scm_ObjMatchD(p,i,c))<=0) continue;
                    sideRoot=1;
                }
                if(!sideRoot) budgetRoots++;
                ranked[count].lit=sideRoot?-lit:lit;ranked[count].ordinal=count;
                ranked[count].path=isfinite(path)?path:0;
                ranked[count].stage=Df_StageDelay(p,lit);
                count++;
            }
        }
        /* Bounded search freezes the round's root list; newly activated roots
           become eligible in a later round, never dereferenced without a ref. */
        if(!phase) qsort(ranked,count,sizeof(*ranked),Df_RankCompare);
        if(!phase) {
            Df_Ranked *critical=ABC_ALLOC(Df_Ranked,count),*side=ABC_ALLOC(Df_Ranked,count);
            int nc=0,ns=0,ic=0,is=0,out=0;
            for(int j=0;j<count;j++) {
                if(ranked[j].lit>=0) critical[nc++]=ranked[j];
                else {
                    side[ns]=ranked[j];int lit=-side[ns].lit;
                    side[ns++].stage=Df_CritCap(&d,lit,Scm_ObjMatchD(p,lit>>1,lit&1));
                }
            }
            qsort(side,ns,sizeof(*side),Df_StageRankCompare);
            /* Three ordinary roots, then one side-load root. The original
               critical-root count still defines the total work budget. */
            while(ic<nc || is<ns) {
                for(int j=0;j<3 && ic<nc;j++) ranked[out++]=critical[ic++];
                if(is<ns) ranked[out++]=side[is++];
            }
            assert(out==count);ABC_FREE(critical);ABC_FREE(side);
        }
        d.limit=cap?d.work+(unsigned long long)cap*(budgetRoots+Gia_ManCoNum(p->pGia)+1):0;
        unsigned long long workStart=d.work;
        int examined=0;

            for(int j=0;j<count;j++) {
                if(d.work>=d.limit) break;
                int lit=ranked[j].lit;
                d.sideRoot=lit<0;if(lit<0) lit=-lit;
                if(!Scm_ObjMapRefNum(p,lit>>1,lit&1)) continue;
                if(!Df_Root(&d,lit,phase,target)) {ABC_FREE(ranked);goto done;}
                d.sideRoot=0;
                examined++;target=fminf(target,p->AffExactDelay*p->pPars->RefineRelax);
                if ( p->pPars->ModelDelayTarget > 0 ) target = fmaxf(target, p->pPars->ModelDelayTarget);
            }

        ABC_FREE(ranked);
        if(p->pPars->fVerbose) printf("SCMAP_WORK_CAP phase=%d round=%d cap=%d roots=%d examined=%d work=%llu budget=%llu\n",
            phase,round,cap,count,examined,d.work-workStart,d.limit-workStart);
        if(d.prune) {
            Rq_Man *r=(Rq_Man *)d.ctx->pScorePrune;
            if(p->pPars->fVerbose) printf("SCMAP_SCORE_PRUNE phase=%d round=%d queries=%lu builds=%lu skips=%lu fallbacks=%lu over_target=%lu no_win=%lu\n",phase,round,r->queries,r->builds,r->skips,d.scoreFallbacks,d.overTarget,d.noWin);
            Rq_Stop(r);d.ctx->pScorePrune=NULL;
        }
        if(d.outputs) {if(p->pPars->fVerbose) printf("SCMAP_PO_CACHE updates=%lu outputs=%d\n",d.outputs->updates,d.outputs->count);Po_Stop(d.outputs);d.outputs=NULL;}
        Scm_ManAffElaCtxFree(d.ctx);d.ctx=NULL;
        float incremental=p->AffExactDelay;
        /* Consistency check, not cover selection or rollback. */
#ifdef SCM_DF_ROUND_VERIFY
        int nLits=2*Gia_ManObjNum(p->pGia);
        Scm_RfPair_t *roundArr=ABC_ALLOC(Scm_RfPair_t,nLits),*roundSlew=ABC_ALLOC(Scm_RfPair_t,nLits);
        memcpy(roundArr,p->pAffExactRfArrs,sizeof(*roundArr)*nLits);
        memcpy(roundSlew,p->pAffExactRfSlews,sizeof(*roundSlew)*nLits);
#endif
        int auditOk=Scm_ManAffElaTimeCover(p);
#ifdef SCM_DF_ROUND_VERIFY
        int badStates=0;float maxArrDiff=0,maxSlewDiff=0;
        for(int lit=0;lit<nLits;lit++) if(Scm_ObjMapRefNum(p,lit>>1,lit&1)) for(int t=0;t<2;t++) {
            float a=roundArr[lit].Value[t],b=p->pAffExactRfArrs[lit].Value[t];
            float c=roundSlew[lit].Value[t],e=p->pAffExactRfSlews[lit].Value[t];
            maxArrDiff=fmaxf(maxArrDiff,fabsf(a-b));maxSlewDiff=fmaxf(maxSlewDiff,fabsf(c-e));
            if(!Df_CheckClose(a,b) || !Df_CheckClose(c,e)) {
                if(badStates<4) fprintf(stderr,"DF_ROUND_BAD lit=%d transition=%d arr=%.9g/%.9g slew=%.9g/%.9g\n",lit,t,a,b,c,e);
                badStates++;
            }
        }
        ABC_FREE(roundArr);ABC_FREE(roundSlew);
        fprintf(stderr,"DF_ROUND_CHECK phase=%d round=%d bad=%d max_arr_diff=%.9g max_slew_diff=%.9g incremental=%.9g recomputed=%.9g target=%.9g\n",phase,round,badStates,maxArrDiff,maxSlewDiff,incremental,p->AffExactDelay,target);
        if(badStates) goto done;
#endif
        if(!auditOk || !Df_CheckClose(p->AffExactDelay,incremental) ||
           (p->AffExactDelay>target && !Df_CheckClose(p->AffExactDelay,target)) || Df_Area(p)!=d.area) goto done;
        if(p->pPars->fVerbose) printf("SCM_SIDE phase=%d round=%d side_trials=%lu side_edits=%lu\n",phase,round,d.sideTried,d.sideWon);
        if(p->pPars->fVerbose) printf("SCMAP_DELAY_FIRST phase=%s round=%d edits=%d area=%lld delay=%.9g initial=%.9g trials=%lu visits=%lu screens=%lu\n",
               phase?"area":"delay",round,d.edits-before,d.area,p->AffExactDelay,initial,d.trials,d.visits,d.screens);
        if(d.edits==before) break;
    }
    Scm_ManUpdateStats(p);ok=1;
done:
    Po_Stop(d.outputs);
    if(d.ctx) {Rq_Stop((Rq_Man *)d.ctx->pScorePrune);Scm_ManAffElaCtxFree(d.ctx);}
    if(d.reuse && p->pPars->fVerbose) printf("SCMAP_REUSE avoided_evaluations=%u\n",d.reused);
    ABC_FREE(d.bestState.data);
    Vec_IntFree(d.pos);if(!ok) puts("DF_FAIL staged affine invariant");return ok;
}
