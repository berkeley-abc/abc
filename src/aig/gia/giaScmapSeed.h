/* Private implementation included by giaScmap.c. */
/* Global cover construction. One coherent implementation per literal;
   paired constant-arc search followed by the retained affine repair. */
typedef struct { double a[2], flow; Scm_Mat_t mat; int valid; } Gp_Label;
typedef struct { double d[2]; int sense; } Gp_Arc;
typedef struct {
    Scm_Man_t *p; Gp_Label *labels; Gp_Arc *arcs;
    double *req; double target; int round;
} Gp_Man;

static int Gp_Allows(int sense,int out,int in)
{ return sense==sc_ts_Non || (sense==sc_ts_Pos ? out==in : out!=in); }
static double Gp_Worst(Gp_Label *q) { return fmax(q->a[0],q->a[1]); }
static int Gp_Better(Gp_Label *a,Gp_Label *b,int area)
{
    if(!a->valid) return 0;
    if(!b->valid) return 1;
    if(area && fabs(a->flow-b->flow)>1e-9) return a->flow<b->flow;
    if(fabs(Gp_Worst(a)-Gp_Worst(b))>1e-9) return Gp_Worst(a)<Gp_Worst(b);
    return a->flow<b->flow;
}
static int Gp_Feasible(Gp_Man *g,Gp_Label *q,int lit)
{ return q->valid && q->a[0]<=g->req[2*lit]+1e-7 && q->a[1]<=g->req[2*lit+1]+1e-7; }
static Gp_Label Gp_Invert(Gp_Man *g,Gp_Label *src,int obj,int phase)
{
    Gp_Label q={0}; Gp_Arc *arc=g->arcs+3*NF_LEAF_MAX;
    if(!src->valid) return q;
    q.valid=1;q.mat.fBest=1;q.mat.fCompl=1;q.mat.Gate=3;
    q.flow=(g->p->InvAreaF+src->flow)/fmax(1,Scm_ObjFlowRefs(g->p,obj,phase));
    for(int t=0;t<2;t++) q.a[t]=src->a[!t]+arc->d[t];
    return q;
}
static Gp_Label Gp_Make(Gp_Man *g,int obj,int phase,Scm_Mat_t m)
{
    Scm_Man_t *p=g->p; Gp_Label q={0};
    Mio_Cell2_t *cell=Scm_ManCell(p,m.Gate);
    int *cut=Scm_CutFromHandle(Scm_ObjCutSet(p,obj),m.CutH);
    q.valid=1;q.mat=m;q.mat.fBest=1;q.flow=cell->AreaF;
    for(int k=0;k<(int)cell->nFanins;k++) {
        int lit=Abc_Var2Lit(Scm_CutLeaves(cut)[Scm_CfgVar(m.Cfg,k)],Scm_CfgCompl(m.Cfg,k));
        Gp_Label *ch=g->labels+lit;Gp_Arc *a=g->arcs+cell->Id*NF_LEAF_MAX+k;
        assert(lit<2*obj && ch->valid);q.flow+=ch->flow;
        /* Same max operations, in the same order, as the generic (t,u) loop
           filtered by Gp_Allows(): non-unate, positive, otherwise negative. */
        if(a->sense==sc_ts_Non) {
            q.a[0]=fmax(fmax(q.a[0],ch->a[0]+a->d[0]),ch->a[1]+a->d[0]);
            q.a[1]=fmax(fmax(q.a[1],ch->a[0]+a->d[1]),ch->a[1]+a->d[1]);
        } else if(a->sense==sc_ts_Pos) {
            q.a[0]=fmax(q.a[0],ch->a[0]+a->d[0]);
            q.a[1]=fmax(q.a[1],ch->a[1]+a->d[1]);
        } else {
            q.a[0]=fmax(q.a[0],ch->a[1]+a->d[0]);
            q.a[1]=fmax(q.a[1],ch->a[0]+a->d[1]);
        }
    }
    q.flow/=fmax(1,Scm_ObjFlowRefs(p,obj,phase));
    return q;
}

/* Select the two polarities together before forwarding any demand to leaves.
   The allowed realizations are two direct gates, or one direct gate plus an
   inverter. Each inherited rise/fall bound must be met by that same pair. */

static int Gp_Forward(Gp_Man *g)
{
    Scm_Man_t *p=g->p;Gia_Obj_t *o;int obj,j,k,info,offset;
    for(int c=0;c<2;c++) {Gp_Label q={0};q.valid=1;q.mat.Gate=c;q.mat.fBest=1;g->labels[c]=q;}
    Gia_ManForEachCiId(p->pGia,obj,j) {
        Gp_Label q={0};q.valid=1;q.mat.fBest=1;g->labels[2*obj]=q;
        g->labels[2*obj+1]=Gp_Invert(g,&q,obj,1);
    }
    Gia_ManForEachAnd(p->pGia,o,obj) {
        Gp_Label direct[2]={0},fast[2]={0},chosen[2],inverse[2];
        int *cut,*set=Scm_ObjCutSet(p,obj);
        if(Gia_ObjIsBuf(o)) return 0;
        Scm_SetForEachCut(set,cut,j) {
            int func=Scm_CutFunc(cut),n=Scm_CutSize(cut);
            if(!Scm_CutLeavesAreValid(Scm_CutLeaves(cut),n,obj)) continue;
            if(!n) {
                for(int c=0;c<2;c++) {
                    Scm_Mat_t m={0};m.Gate=c^(func==1);m.CutH=Scm_CutHandle(set,cut);
                    Gp_Label q=Gp_Make(g,obj,c,m);
                    if(Gp_Better(&q,&fast[c],0)) fast[c]=q;
                    if((!g->round || Gp_Feasible(g,&q,2*obj+c)) && Gp_Better(&q,&direct[c],g->round>0 && g->req[4*obj+2*c]<1e99)) direct[c]=q;
                }
                continue;
            }
            if(Abc_Lit2Var(func)>=Vec_WecSize(p->vTt2Match)) continue;
            Vec_Int_t *v=Vec_WecEntry(p->vTt2Match,Abc_Lit2Var(func));
            Vec_IntForEachEntryDouble(v,info,offset,k) {
                Scm_Cfg_t cfg=Scm_Int2Cfg(offset);Scm_Mat_t m={0};
                if(n!=(int)Scm_ManCell(p,info)->nFanins || !Scm_CfgIsCutPermutation(cfg,n)) continue;
                int c=cfg.fCompl^Abc_LitIsCompl(func);cfg.fCompl=0;
                m.Gate=info;m.CutH=Scm_CutHandle(set,cut);m.Cfg=cfg;
                Gp_Label q=Gp_Make(g,obj,c,m);
                if(Gp_Better(&q,&fast[c],0)) fast[c]=q;
                if((!g->round || Gp_Feasible(g,&q,2*obj+c)) && Gp_Better(&q,&direct[c],g->round>0 && g->req[4*obj+2*c]<1e99)) direct[c]=q;
            }
        }
        for(int c=0;c<2;c++) if(!direct[c].valid) direct[c]=fast[c];
        for(int c=0;c<2;c++) {
            chosen[c]=direct[c];inverse[c]=Gp_Invert(g,&direct[!c],obj,c);
            /* A fallback direct label can be valid but miss its required
               time. It must not defeat a feasible inverter by area. */
            if((!g->round || Gp_Feasible(g,&inverse[c],2*obj+c)) &&
               ((g->round && !Gp_Feasible(g,&chosen[c],2*obj+c)) ||
                Gp_Better(&inverse[c],&chosen[c],g->round>0 && g->req[4*obj+2*c]<1e99))) chosen[c]=inverse[c];
        }
        /* The source of an inverter is the selected direct implementation.
           Never allow two opposite inverters to form a fictitious cycle. */
        if(chosen[0].mat.fCompl && chosen[1].mat.fCompl) {
            double cost0=direct[0].flow+inverse[1].flow;
            double cost1=direct[1].flow+inverse[0].flow;
            int can0=!g->round || Gp_Feasible(g,&direct[0],2*obj);
            int can1=!g->round || Gp_Feasible(g,&direct[1],2*obj+1);
            if(!can0 && !can1) { printf("GP_FAIL polarity round=%d obj=%d\n",g->round,obj);return 0; }
            int source=can0 && (!can1 || cost0<=cost1)?0:1;
            chosen[source]=direct[source];
        }
        for(int c=0;c<2;c++) {
            if(!chosen[c].valid) { printf("GP_FAIL empty round=%d obj=%d c=%d\n",g->round,obj,c);return 0; }
            if(g->round && !Gp_Feasible(g,&chosen[c],2*obj+c)) {printf("GP_FAIL forward round=%d obj=%d c=%d arr=%.17g/%.17g req=%.17g/%.17g direct=%d inv=%d\n",g->round,obj,c,chosen[c].a[0],chosen[c].a[1],g->req[4*obj+2*c],g->req[4*obj+2*c+1],direct[c].valid,inverse[c].valid);return 0;}
            g->labels[2*obj+c]=chosen[c];
        }
    }
    return 1;
}
static void Gp_RequireArc(Gp_Man *g,int root,int child,Gp_Arc *a)
{
    for(int t=0;t<2;t++) for(int u=0;u<2;u++) if(Gp_Allows(a->sense,t,u))
        g->req[2*child+u]=fmin(g->req[2*child+u],g->req[2*root+t]-a->d[t]);
}
static int Gp_Cover(Gp_Man *g)
{
    Scm_Man_t *p=g->p;Gia_Obj_t *o;int i,j,n=2*Gia_ManObjNum(p->pGia);
    Vec_IntFill(&p->vMapRefs,n,0);
    for(i=0;i<2*n;i++) g->req[i]=1e100;
    Gia_ManForEachCo(p->pGia,o,j) {
        int lit=Gia_ObjFaninLit0p(p->pGia,o);Scm_ObjMapRefInc(p,lit>>1,lit&1);
        if(Gp_Worst(g->labels+lit)>g->target+1e-6) {printf("GP_FAIL po round=%d lit=%d arrival=%.17g target=%.17g\n",g->round,lit,Gp_Worst(g->labels+lit),g->target);return 0;}
        g->req[2*lit]=g->req[2*lit+1]=g->target;
    }
    Gia_ManForEachAndReverse(p->pGia,o,i) {
            for(int pass=1;pass>=0;pass--) for(int c=0;c<2;c++) {
            int lit=2*i+c;Gp_Label *q=g->labels+lit;
            if(!Scm_ObjMapRefNum(p,i,c) || !!q->mat.fCompl!=pass) continue;
            if(pass) {Scm_ObjMapRefInc(p,i,!c);Gp_RequireArc(g,lit,lit^1,g->arcs+3*NF_LEAF_MAX);continue;}
            Mio_Cell2_t *cell=Scm_ManCell(p,q->mat.Gate);
            int *cut=Scm_CutFromHandle(Scm_ObjCutSet(p,i),q->mat.CutH);
            for(int k=0;k<(int)cell->nFanins;k++) {
                int child=Abc_Var2Lit(Scm_CutLeaves(cut)[Scm_CfgVar(q->mat.Cfg,k)],Scm_CfgCompl(q->mat.Cfg,k));
                Scm_ObjMapRefInc(p,child>>1,child&1);
                Gp_RequireArc(g,lit,child,g->arcs+cell->Id*NF_LEAF_MAX+k);
            }
        }
    }
    Gia_ManForEachCiId(p->pGia,i,j) if(Scm_ObjMapRefNum(p,i,1)) {
        Scm_ObjMapRefInc(p,i,0);Gp_RequireArc(g,2*i+1,2*i,g->arcs+3*NF_LEAF_MAX);
    }
    /* Unreferenced literals have no inherited bound. Keep their fastest
       implementation available in the next forward pass; a newly selected
       parent still checks its actual paired arrival against its own bound. */
    for(i=0;i<n;i++) {
        for(int t=0;t<2;t++) {
            if(g->labels[i].valid && g->labels[i].a[t]>g->req[2*i+t]+1e-6) {printf("GP_FAIL cover round=%d lit=%d t=%d a=%.17g r=%.17g refs=%d\n",g->round,i,t,g->labels[i].a[t],g->req[2*i+t],Vec_IntEntry(&p->vMapRefs,i));return 0;}
        }
        float coef=1.0/(1+(g->round+1)*(g->round+1));
        Vec_FltWriteEntry(&p->vFlowRefs,i,fmax(1,coef*Vec_FltEntry(&p->vFlowRefs,i)+(1-coef)*Vec_IntEntry(&p->vMapRefs,i)));
    }
    return 1;
}

/* Two reverse exact-shared-area passes under
   the same paired fixed-arc target used to construct the global cover.
   No affine or backend delay is used to select these replacements. */
static word Gp_Area(Gp_Man *g)
{
    Scm_Man_t *p=g->p; Gia_Obj_t *o; int i,c; word area=0;
    Gia_ManForEachAnd(p->pGia,o,i) for(c=0;c<2;c++)
        if(Scm_ObjMapRefNum(p,i,c)) {
            Scm_Mat_t *m=Scm_ObjMatchD(p,i,c);
            area+=m->fCompl?p->InvAreaW:Scm_ManCell(p,m->Gate)->AreaW;
        }
    Gia_ManForEachCiId(p->pGia,i,c)
        if(Scm_ObjMapRefNum(p,i,1)) area+=p->InvAreaW;
    return area;
}
static void Gp_RequireSelected(Gp_Man *g,int obj,int phase)
{
    Scm_Man_t *p=g->p; int lit=2*obj+phase;
    Scm_Mat_t *m=Scm_ObjMatchD(p,obj,phase);
    if(m->fCompl) {
        Gp_RequireArc(g,lit,lit^1,g->arcs+3*NF_LEAF_MAX);return;
    }
    Mio_Cell2_t *cell=Scm_ManCell(p,m->Gate);
    if(!cell->nFanins) return;
    int *cut=Scm_CutFromHandle(Scm_ObjCutSet(p,obj),m->CutH);
    for(int k=0;k<(int)cell->nFanins;k++) {
        int child=Abc_Var2Lit(Scm_CutLeaves(cut)[Scm_CfgVar(m->Cfg,k)],Scm_CfgCompl(m->Cfg,k));
        Gp_RequireArc(g,lit,child,g->arcs+cell->Id*NF_LEAF_MAX+k);
    }
}
static int Gp_RetimeSelected(Gp_Man *g)
{
    Scm_Man_t *p=g->p;Gia_Obj_t *o;int obj,phase,pass;
    /* Only materialize the chosen cover; do not perform forward selection. */
    Gia_ManForEachAnd(p->pGia,o,obj) for(pass=0;pass<2;pass++)
        for(phase=0;phase<2;phase++) {
            Scm_Mat_t m=*Scm_ObjMatchD(p,obj,phase);
            if(!!m.fCompl!=pass) continue;
            Gp_Label q=pass?Gp_Invert(g,g->labels+(2*obj+(phase^1)),obj,phase):Gp_Make(g,obj,phase,m);
            if(!q.valid) return 0;
            q.mat=m;g->labels[2*obj+phase]=q;
            Scm_ObjMatchD(p,obj,phase)->D=Scm_AffArrivalRecord(Gp_Worst(&q));
        }
    return 1;
}
static int Gp_ExactArea(Gp_Man *g)
{
    Scm_Man_t *p=g->p;Gia_Obj_t *o;int n=2*Gia_ManObjNum(p->pGia),i,c,pass;
    int *refs=ABC_ALLOC(int,n);word seedArea=Gp_Area(g),currentArea=seedArea;
    for(int round=0;round<2;round++) {
        int edits=0;
        for(i=0;i<2*n;i++) g->req[i]=1e100;
        Gia_ManForEachCo(p->pGia,o,i) {
            int lit=Gia_ObjFaninLit0p(p->pGia,o);
            g->req[2*lit]=g->req[2*lit+1]=g->target;
        }
        Gia_ManForEachAndReverse(p->pGia,o,i) {
            /* Propagate an inverter's bound before processing its source.
               This extension changes cuts/cells but preserves phase choices. */
            for(pass=1;pass>=0;pass--) for(c=0;c<2;c++) {
                int lit=2*i+c;Scm_Mat_t old=*Scm_ObjMatchD(p,i,c);
                if(!Scm_ObjMapRefNum(p,i,c) || !!old.fCompl!=pass) continue;
                if(!Gp_Feasible(g,g->labels+lit,lit)) goto fail;
                if(!pass) {
                    int count=0,alloc=0,best=-1;
                    Scm_AffElaCand_t *list=NULL;
                    word freed=Scm_MatchDeref_rec(p,i,c,&old),bestArea=freed;
                    Gp_Label chosen=g->labels[lit];
                    /* Timing feasibility first; exact shared area only for feasible
                       candidates (same candidate order, area values and choice). */
                    Scm_ManAffElaCandidatesInt(p,i,c,&old,freed,&list,&count,&alloc,0);
                    for(int k=0;k<count;k++) {
                        Gp_Label q=Gp_Make(g,i,c,list[k].M);
                        if(!Gp_Feasible(g,&q,lit)) continue;
                        list[k].Area=Scm_ManAffElaRefArea(p,i,c,&list[k].M,freed);
                        if(!Scm_ManAffElaAreaUseful(freed,list[k].Area)) continue;
                        if(list[k].Area<bestArea || (best>=0 && list[k].Area==bestArea && Gp_Worst(&q)<Gp_Worst(&chosen)))
                            best=k,bestArea=list[k].Area,chosen=q;
                    }
                    Scm_Mat_t m=best>=0?list[best].M:old;
                    m.D=Scm_AffArrivalRecord(Gp_Worst(&chosen));
                    word restored=Scm_MatchRef_rec(p,i,c,&m,SCL_INFINITY,NULL);
                    assert(restored==bestArea && bestArea<=freed);
                    *Scm_ObjMatchD(p,i,c)=m;chosen.mat=m;g->labels[lit]=chosen;
                    currentArea=currentArea-freed+restored;edits+=best>=0;
                    ABC_FREE(list);
                }
                Gp_RequireSelected(g,i,c);
            }
        }
        Gia_ManForEachCiId(p->pGia,i,c)
            if(Scm_ObjMapRefNum(p,i,1)) Gp_RequireSelected(g,i,1);
        if(!Gp_RetimeSelected(g) || Gp_Area(g)!=currentArea || currentArea>seedArea) goto fail;
        memcpy(refs,Vec_IntArray(&p->vMapRefs),sizeof(int)*n);
        /* Independently rebuild references and validate both transitions
           against the unchanged initial target after each pass. */
        if(!Gp_Cover(g) || memcmp(refs,Vec_IntArray(&p->vMapRefs),sizeof(int)*n)) goto fail;
        if(p->pPars->fVerbose) printf("SCMAP_GLOBAL_EXACT round=%d edits=%d area=%llu seed=%llu target=%.9g\n",round,edits,(unsigned long long)currentArea,(unsigned long long)seedArea,g->target);
        if(!edits) break;
    }
    ABC_FREE(refs);return 1;
fail:
    puts("GP_FAIL exact-area invariant");ABC_FREE(refs);return 0;
}

static int Scm_ManBuildPairedSeed(Scm_Man_t *p,int mode)
{
    int nGlobalRounds=4;
    Gp_Man g={0};int n=2*Gia_ManObjNum(p->pGia),ok=0,i,k,j;
    Gia_Obj_t *o;g.p=p;g.labels=ABC_CALLOC(Gp_Label,n);
    g.req=ABC_ALLOC(double,2*n);g.arcs=ABC_CALLOC(Gp_Arc,p->nCells*NF_LEAF_MAX);
    for(i=0;i<p->nCells;i++) {
        Mio_Cell2_t *cell=p->pCells+i;SC_Cell *rep=Scm_ManSclCell(p,cell),*member;
        for(k=0;k<(int)cell->nFanins;k++) {
            Gp_Arc *a=g.arcs+i*NF_LEAF_MAX+k;double d[2]={0};int count=0;
            if(!rep) goto done;
            SC_RingForEachCell(rep,member,j) {
                Scm_LinArc_t arc={0};if(member->fSkip) continue;
                if(!Scm_ManFitOwnGridCached(p,member,k,&arc)) goto done;
                a->sense=arc.TimingSense;count++;
                if(p->pPars->nSeedMode&1) {
                    /* Common-load seed: every input arc of a family member sees the
                       same G=250 load relative to its mean pin capacitance, and
                       the fitted family delay is used directly (not rescaled). */
                    double cin=0;
                    for(int pin=0;pin<(int)cell->nFanins;pin++) cin+=SC_CellPinCap(member,pin);
                    cin/=cell->nFanins;
                    for(int t=0;t<2;t++) d[t]+=fmax(1e-3,arc.RfDelay0[t]+arc.RfDelayLoad[t]*2.5*cin+arc.RfDelaySlew[t]*p->BufferRefSlew);
                }
                else
                for(int t=0;t<2;t++) d[t]+=fmax(1e-3,arc.RfDelay0[t]+arc.RfDelayLoad[t]*2.5*SC_CellPinCap(member,k)+arc.RfDelaySlew[t]*p->BufferRefSlew);
            }
            if(!count || d[0]+d[1]<=0) goto done;
            if(p->pPars->nSeedMode&1) for(int t=0;t<2;t++) a->d[t]=d[t]/count;
            else
            for(int t=0;t<2;t++) a->d[t]=Scl_Int2Flt(cell->iDelays[k])*(2*d[t]/(d[0]+d[1]));
        }
    }
    /* No NF cover is built first. Flow references start from AIG structure. */
    for(g.round=0;g.round<nGlobalRounds;g.round++) {
        if(!Gp_Forward(&g)) goto done;
        if(!g.round) Gia_ManForEachCo(p->pGia,o,i)
            g.target=fmax(g.target,Gp_Worst(g.labels+Gia_ObjFaninLit0p(p->pGia,o)));

        if(!Gp_Cover(&g)) goto done;
    }
    for(i=0;i<n;i++) if(g.labels[i].valid) {
        Scm_Mat_t m=g.labels[i].mat;m.fBest=1;m.D=Scm_AffArrivalRecord(Gp_Worst(g.labels+i));m.F=g.labels[i].flow;
        *Scm_ObjMatchD(p,i>>1,i&1)=m;m.fBest=0;*Scm_ObjMatchA(p,i>>1,i&1)=m;
    }
    if(!Gp_ExactArea(&g)) goto done;
    if(!Scm_ManAffElaCollectLoads(p,1)) {puts("GP_FAIL collect");goto done;}
    if(!Scm_ManAffAuditTiming(p)) {puts("GP_FAIL audit");goto done;}
    Scm_ManUpdateStats(p);ok=Scm_ManAffElaRebuildTails(p);if(!ok) puts("GP_FAIL tails");
    if(p->pPars->fVerbose) printf("SCMAP_SEED mode=%d rounds=%d fixed_delay=%.9g affine_delay=%.9g\n",mode,nGlobalRounds,g.target,p->AffExactDelay);
done:
    ABC_FREE(g.labels);ABC_FREE(g.req);ABC_FREE(g.arcs);return ok;
}

static int Scm_ManAffPairedSeed( Scm_Man_t * p )
{
    return Scm_ManBuildPairedSeed(p, 2);
}
