/**CFile****************************************************************

  FileName    [giaScmapSeed.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [SCMap seed covers with fixed rise/fall arc costs; included by giaScmap.c.]

  Description [A seed is a complete cover built with one fixed cost per arc
  and output transition. Four global rounds alternate a forward pass, which
  selects both polarities of every node together (two direct gates, or one
  direct gate and an inverter) within the required times of the previous
  round, with a backward pass that references the selected cover from the
  outputs, propagates paired rise/fall required times and blends the flow
  references toward the actual references. Two exact-area passes then replace
  matches that free area within the same required times.]

  Author      [Anqi Lu]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 2026.]

  Revision    [$Id: giaScmapSeed.h,v 1.00 2026/11/27 00:00:00 anqilu Exp $]

***********************************************************************/

// The best implementation of one literal: rise/fall arrival, area flow and the match.
typedef struct Scm_Label_t_ Scm_Label_t;
struct Scm_Label_t_
{
    double         a[2];       // arrival of the fall and rise output transitions
    double         flow;       // area flow
    Scm_Mat_t      mat;
    int            valid;      // the literal has an implementation
};
// The fixed cost of one cell pin arc per output transition, and its timing sense.
typedef struct Scm_SeedArc_t_ Scm_SeedArc_t;
struct Scm_SeedArc_t_
{
    double         d[2];       // per output transition
    int            sense;
};
typedef struct Scm_Seed_t_ Scm_Seed_t;
struct Scm_Seed_t_
{
    Scm_Man_t *    p;
    Scm_Label_t *  labels;     // per literal
    Scm_SeedArc_t * arcs;      // per cell and pin
    double *       req;        // per literal and transition: required time
    double         target;     // required time of the outputs
    int            round;      // global round; round 0 has no required times
};

/**Function*************************************************************

  Synopsis    [Whether an input transition (in) can cause an output transition (out)
  through an arc of this sense.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_SeedAllows( int sense, int out, int in )
{
    return sense == sc_ts_Non || (sense == sc_ts_Pos ? out == in : out != in);
}

/**Function*************************************************************

  Synopsis    [Returns the later of the fall and rise arrivals of a label.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static double Scm_LabelWorst( Scm_Label_t * q )
{
    return fmax( q->a[0], q->a[1] );
}

/**Function*************************************************************

  Synopsis    [Smaller area flow first when fArea, else smaller worst arrival first,
  then smaller flow.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_LabelBetter( Scm_Label_t * a, Scm_Label_t * b, int fArea )
{
    if ( !a->valid ) return 0;
    if ( !b->valid ) return 1;
    if ( fArea && fabs(a->flow - b->flow) > 1e-9 ) return a->flow < b->flow;
    if ( fabs(Scm_LabelWorst(a) - Scm_LabelWorst(b)) > 1e-9 ) return Scm_LabelWorst(a) < Scm_LabelWorst(b);
    return a->flow < b->flow;
}

/**Function*************************************************************

  Synopsis    [Checks that a label meets the rise/fall required times of its literal.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_SeedFeasible( Scm_Seed_t * g, Scm_Label_t * q, int lit )
{
    return q->valid && q->a[0] <= g->req[2*lit] + 1e-7 && q->a[1] <= g->req[2*lit+1] + 1e-7;
}

/**Function*************************************************************

  Synopsis    [An inverter driven by the label of the opposite phase.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Scm_Label_t Scm_SeedInvert( Scm_Seed_t * g, Scm_Label_t * src, int obj, int phase )
{
    Scm_Label_t q;
    Scm_SeedArc_t * arc = g->arcs + 3*SCM_LEAF_MAX;
    int t;
    memset(&q, 0, sizeof(q));
    if ( !src->valid ) return q;
    q.valid = 1; q.mat.fCompl = 1; q.mat.Gate = 3;
    q.flow = (g->p->InvAreaF + src->flow) / fmax(1, Scm_ObjFlowRefs(g->p, obj, phase));
    for ( t = 0; t < 2; t++ )
        q.a[t] = src->a[!t] + arc->d[t];
    return q;
}

/**Function*************************************************************

  Synopsis    [A match over the current labels of its leaves.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Scm_Label_t Scm_SeedMake( Scm_Seed_t * g, int obj, int phase, Scm_Mat_t m )
{
    Scm_Man_t * p = g->p;
    Scm_Label_t q;
    Mio_Cell2_t * cell = Scm_ManCell(p, m.Gate);
    int * cut = Scm_CutFromHandle(Scm_ObjCutSet(p, obj), m.CutH);
    int k;
    memset(&q, 0, sizeof(q));
    q.valid = 1; q.mat = m; q.flow = cell->AreaF;
    for ( k = 0; k < (int)cell->nFanins; k++ )
    {
        int lit = Abc_Var2Lit(Scm_CutLeaves(cut)[Scm_CfgVar(m.Cfg, k)], Scm_CfgCompl(m.Cfg, k));
        Scm_Label_t * ch = g->labels + lit;
        Scm_SeedArc_t * a = g->arcs + cell->Id*SCM_LEAF_MAX + k;
        assert( lit < 2*obj && ch->valid );
        q.flow += ch->flow;
        if ( a->sense == sc_ts_Non )
        {
            q.a[0] = fmax(fmax(q.a[0], ch->a[0] + a->d[0]), ch->a[1] + a->d[0]);
            q.a[1] = fmax(fmax(q.a[1], ch->a[0] + a->d[1]), ch->a[1] + a->d[1]);
        }
        else if ( a->sense == sc_ts_Pos )
        {
            q.a[0] = fmax(q.a[0], ch->a[0] + a->d[0]);
            q.a[1] = fmax(q.a[1], ch->a[1] + a->d[1]);
        }
        else
        {
            q.a[0] = fmax(q.a[0], ch->a[1] + a->d[0]);
            q.a[1] = fmax(q.a[1], ch->a[0] + a->d[1]);
        }
    }
    q.flow /= fmax(1, Scm_ObjFlowRefs(p, obj, phase));
    return q;
}

/**Function*************************************************************

  Synopsis    [Forward pass: labels every literal.]

  Description [Both polarities of a node are selected together, before any
  demand reaches the leaves: two direct gates, or one direct gate and an
  inverter, and each must meet its inherited rise/fall required time. Round 0
  has no required times and prefers delay; later rounds prefer area flow
  where a required time exists.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_SeedForward( Scm_Seed_t * g )
{
    Scm_Man_t * p = g->p;
    Gia_Obj_t * o;
    int obj, j, k, c, info, offset;
    for ( c = 0; c < 2; c++ )
    {
        Scm_Label_t q;
        memset(&q, 0, sizeof(q));
        q.valid = 1; q.mat.Gate = c;
        g->labels[c] = q;
    }
    Gia_ManForEachCiId( p->pGia, obj, j )
    {
        Scm_Label_t q;
        memset(&q, 0, sizeof(q));
        q.valid = 1;
        g->labels[2*obj] = q;
        g->labels[2*obj+1] = Scm_SeedInvert(g, &q, obj, 1);
    }
    Gia_ManForEachAnd( p->pGia, o, obj )
    {
        Scm_Label_t direct[2], fast[2], chosen[2], inverse[2];
        int * cut, * set = Scm_ObjCutSet(p, obj);
        memset( direct, 0, sizeof(direct) );
        memset( fast, 0, sizeof(fast) );
        Scm_SetForEachCut( set, cut, j )
        {
            int func = Scm_CutFunc(cut), n = Scm_CutSize(cut);
            Vec_Int_t * v;
            if ( !Scm_CutLeavesAreValid(Scm_CutLeaves(cut), n, obj) ) continue;
            if ( !n )
            {
                for ( c = 0; c < 2; c++ )
                {
                    Scm_Mat_t m = {0};
                    Scm_Label_t q;
                    m.Gate = c ^ (func == 1); m.CutH = Scm_CutHandle(set, cut);
                    q = Scm_SeedMake(g, obj, c, m);
                    if ( Scm_LabelBetter(&q, &fast[c], 0) ) fast[c] = q;
                    if ( (!g->round || Scm_SeedFeasible(g, &q, 2*obj+c)) &&
                         Scm_LabelBetter(&q, &direct[c], g->round > 0 && g->req[4*obj+2*c] < 1e99) ) direct[c] = q;
                }
                continue;
            }
            if ( Abc_Lit2Var(func) >= Vec_WecSize(p->vTt2Match) ) continue;
            v = Vec_WecEntry(p->vTt2Match, Abc_Lit2Var(func));
            Vec_IntForEachEntryDouble( v, info, offset, k )
            {
                Scm_Cfg_t cfg = Scm_Int2Cfg(offset);
                Scm_Mat_t m = {0};
                Scm_Label_t q;
                if ( n != (int)Scm_ManCell(p, info)->nFanins || !Scm_CfgIsCutPermutation(cfg, n) ) continue;
                c = cfg.fCompl ^ Abc_LitIsCompl(func);
                cfg.fCompl = 0;
                m.Gate = info; m.CutH = Scm_CutHandle(set, cut); m.Cfg = cfg;
                q = Scm_SeedMake(g, obj, c, m);
                if ( Scm_LabelBetter(&q, &fast[c], 0) ) fast[c] = q;
                if ( (!g->round || Scm_SeedFeasible(g, &q, 2*obj+c)) &&
                     Scm_LabelBetter(&q, &direct[c], g->round > 0 && g->req[4*obj+2*c] < 1e99) ) direct[c] = q;
            }
        }
        for ( c = 0; c < 2; c++ )
            if ( !direct[c].valid ) direct[c] = fast[c];
        for ( c = 0; c < 2; c++ )
        {
            chosen[c] = direct[c];
            inverse[c] = Scm_SeedInvert(g, &direct[!c], obj, c);
            // a fallback direct label can be valid but miss its required time: a feasible inverter then wins
            if ( (!g->round || Scm_SeedFeasible(g, &inverse[c], 2*obj+c)) &&
                 ((g->round && !Scm_SeedFeasible(g, &chosen[c], 2*obj+c)) ||
                  Scm_LabelBetter(&inverse[c], &chosen[c], g->round > 0 && g->req[4*obj+2*c] < 1e99)) )
                chosen[c] = inverse[c];
        }
        // an inverter's source is the direct implementation: never two inverters on one node
        if ( chosen[0].mat.fCompl && chosen[1].mat.fCompl )
        {
            double cost0 = direct[0].flow + inverse[1].flow;
            double cost1 = direct[1].flow + inverse[0].flow;
            int can0 = !g->round || Scm_SeedFeasible(g, &direct[0], 2*obj);
            int can1 = !g->round || Scm_SeedFeasible(g, &direct[1], 2*obj+1);
            int source;
            if ( !can0 && !can1 ) return 0;
            source = can0 && (!can1 || cost0 <= cost1) ? 0 : 1;
            chosen[source] = direct[source];
        }
        for ( c = 0; c < 2; c++ )
        {
            if ( !chosen[c].valid || (g->round && !Scm_SeedFeasible(g, &chosen[c], 2*obj+c)) ) return 0;
            g->labels[2*obj+c] = chosen[c];
        }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Propagates the rise/fall required times of a root to a fanin through
  one arc.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_SeedRequireArc( Scm_Seed_t * g, int root, int child, Scm_SeedArc_t * a )
{
    int t, u;
    for ( t = 0; t < 2; t++ )
        for ( u = 0; u < 2; u++ )
            if ( Scm_SeedAllows(a->sense, t, u) )
                g->req[2*child+u] = fmin(g->req[2*child+u], g->req[2*root+t] - a->d[t]);
}

/**Function*************************************************************

  Synopsis    [Backward pass: references the cover and sets required times.]

  Description [Checks that every selected label meets its required time and
  blends the flow references toward the actual references of this round.
  Unreferenced literals keep no bound, so their fastest implementation stays
  available to the next forward pass.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_SeedCover( Scm_Seed_t * g )
{
    Scm_Man_t * p = g->p;
    Gia_Obj_t * o;
    int i, j, k, c, t, pass, n = 2*Gia_ManObjNum(p->pGia);
    Vec_IntFill( &p->vMapRefs, n, 0 );
    for ( i = 0; i < 2*n; i++ )
        g->req[i] = 1e100;
    Gia_ManForEachCo( p->pGia, o, j )
    {
        int lit = Gia_ObjFaninLit0p(p->pGia, o);
        Scm_ObjMapRefInc(p, lit >> 1, lit & 1);
        if ( Scm_LabelWorst(g->labels+lit) > g->target + 1e-6 ) return 0;
        g->req[2*lit] = g->req[2*lit+1] = g->target;
    }
    Gia_ManForEachAndReverse( p->pGia, o, i )
        for ( pass = 1; pass >= 0; pass-- )   // an inverter's bound reaches its source first
            for ( c = 0; c < 2; c++ )
            {
                int lit = 2*i+c, * cut;
                Scm_Label_t * q = g->labels + lit;
                Mio_Cell2_t * cell;
                if ( !Scm_ObjMapRefNum(p, i, c) || !!q->mat.fCompl != pass ) continue;
                if ( pass )
                {
                    Scm_ObjMapRefInc(p, i, !c);
                    Scm_SeedRequireArc(g, lit, lit^1, g->arcs + 3*SCM_LEAF_MAX);
                    continue;
                }
                cell = Scm_ManCell(p, q->mat.Gate);
                cut = Scm_CutFromHandle(Scm_ObjCutSet(p, i), q->mat.CutH);
                for ( k = 0; k < (int)cell->nFanins; k++ )
                {
                    int child = Abc_Var2Lit(Scm_CutLeaves(cut)[Scm_CfgVar(q->mat.Cfg, k)], Scm_CfgCompl(q->mat.Cfg, k));
                    Scm_ObjMapRefInc(p, child >> 1, child & 1);
                    Scm_SeedRequireArc(g, lit, child, g->arcs + cell->Id*SCM_LEAF_MAX + k);
                }
            }
    Gia_ManForEachCiId( p->pGia, i, j )
        if ( Scm_ObjMapRefNum(p, i, 1) )
        {
            Scm_ObjMapRefInc(p, i, 0);
            Scm_SeedRequireArc(g, 2*i+1, 2*i, g->arcs + 3*SCM_LEAF_MAX);
        }
    for ( i = 0; i < n; i++ )
    {
        float coef = 1.0/(1+(g->round+1)*(g->round+1));
        for ( t = 0; t < 2; t++ )
            if ( g->labels[i].valid && g->labels[i].a[t] > g->req[2*i+t] + 1e-6 ) return 0;
        Vec_FltWriteEntry( &p->vFlowRefs, i, fmax(1, coef*Vec_FltEntry(&p->vFlowRefs, i) + (1-coef)*Vec_IntEntry(&p->vMapRefs, i)) );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Required times of the selected match's leaves.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_SeedRequireSelected( Scm_Seed_t * g, int obj, int phase )
{
    Scm_Man_t * p = g->p;
    Scm_Mat_t * m = Scm_ObjMatch(p, obj, phase);
    Mio_Cell2_t * cell;
    int lit = 2*obj+phase, k, * cut;
    if ( m->fCompl )
    {
        Scm_SeedRequireArc(g, lit, lit^1, g->arcs + 3*SCM_LEAF_MAX);
        return;
    }
    cell = Scm_ManCell(p, m->Gate);
    if ( !cell->nFanins ) return;
    cut = Scm_CutFromHandle(Scm_ObjCutSet(p, obj), m->CutH);
    for ( k = 0; k < (int)cell->nFanins; k++ )
    {
        int child = Abc_Var2Lit(Scm_CutLeaves(cut)[Scm_CfgVar(m->Cfg, k)], Scm_CfgCompl(m->Cfg, k));
        Scm_SeedRequireArc(g, lit, child, g->arcs + cell->Id*SCM_LEAF_MAX + k);
    }
}

/**Function*************************************************************

  Synopsis    [Recomputes the labels of the selected cover (no selection).]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_SeedRetime( Scm_Seed_t * g )
{
    Scm_Man_t * p = g->p;
    Gia_Obj_t * o;
    int obj, phase, pass;
    Gia_ManForEachAnd( p->pGia, o, obj )
        for ( pass = 0; pass < 2; pass++ )
            for ( phase = 0; phase < 2; phase++ )
            {
                Scm_Mat_t m = *Scm_ObjMatch(p, obj, phase);
                Scm_Label_t q;
                if ( !!m.fCompl != pass ) continue;
                q = pass ? Scm_SeedInvert(g, g->labels + (2*obj + (phase^1)), obj, phase) : Scm_SeedMake(g, obj, phase, m);
                if ( !q.valid ) return 0;
                q.mat = m;
                g->labels[2*obj+phase] = q;
            }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Exact-area passes under the seed's fixed-arc required times.]

  Description [In reverse topological order, replaces each selected match by
  the feasible candidate that frees the most exact shared area (ties: smaller
  arrival). Each pass is checked: area bookkeeping, a fresh backward pass with
  identical references, and every label within the unchanged target.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_SeedExactArea( Scm_Seed_t * g )
{
    Scm_Man_t * p = g->p;
    Gia_Obj_t * o;
    int n = 2*Gia_ManObjNum(p->pGia), i, c, k, pass, round;
    int * refs = ABC_ALLOC(int, n);
    word seedArea = Scm_ManCoverArea(p), currentArea = seedArea;
    for ( round = 0; round < 2; round++ )
    {
        int edits = 0;
        for ( i = 0; i < 2*n; i++ )
            g->req[i] = 1e100;
        Gia_ManForEachCo( p->pGia, o, i )
        {
            int lit = Gia_ObjFaninLit0p(p->pGia, o);
            g->req[2*lit] = g->req[2*lit+1] = g->target;
        }
        Gia_ManForEachAndReverse( p->pGia, o, i )
            for ( pass = 1; pass >= 0; pass-- )   // an inverter's bound reaches its source first
                for ( c = 0; c < 2; c++ )
                {
                    int lit = 2*i+c;
                    Scm_Mat_t old = *Scm_ObjMatch(p, i, c);
                    if ( !Scm_ObjMapRefNum(p, i, c) || !!old.fCompl != pass ) continue;
                    if ( !Scm_SeedFeasible(g, g->labels+lit, lit) ) goto fail;
                    if ( !pass )
                    {
                        int count = 0, alloc = 0, best = -1;
                        Scm_Cand_t * list = NULL;
                        word freed = Scm_MatchDeref_rec(p, i, c, &old), bestArea = freed, restored;
                        Scm_Label_t chosen = g->labels[lit];
                        Scm_Mat_t m;
                        // feasibility first; exact shared area only for the feasible candidates
                        Scm_ManCandidates(p, i, c, &old, freed, &list, &count, &alloc, 0);
                        for ( k = 0; k < count; k++ )
                        {
                            Scm_Label_t q = Scm_SeedMake(g, i, c, list[k].M);
                            if ( !Scm_SeedFeasible(g, &q, lit) ) continue;
                            list[k].Area = Scm_ManRefArea(p, i, c, &list[k].M, freed);
                            if ( list[k].Area >= freed ) continue;
                            if ( list[k].Area < bestArea || (best >= 0 && list[k].Area == bestArea && Scm_LabelWorst(&q) < Scm_LabelWorst(&chosen)) )
                                best = k, bestArea = list[k].Area, chosen = q;
                        }
                        m = best >= 0 ? list[best].M : old;
                        restored = Scm_MatchRef_rec(p, i, c, &m);
                        assert( restored == bestArea && bestArea <= freed );
                        *Scm_ObjMatch(p, i, c) = m;
                        chosen.mat = m;
                        g->labels[lit] = chosen;
                        currentArea = currentArea - freed + restored;
                        edits += best >= 0;
                        ABC_FREE( list );
                    }
                    Scm_SeedRequireSelected(g, i, c);
                }
        Gia_ManForEachCiId( p->pGia, i, c )
            if ( Scm_ObjMapRefNum(p, i, 1) )
                Scm_SeedRequireSelected(g, i, 1);
        if ( !Scm_SeedRetime(g) || Scm_ManCoverArea(p) != currentArea || currentArea > seedArea ) goto fail;
        memcpy( refs, Vec_IntArray(&p->vMapRefs), sizeof(int)*n );
        if ( !Scm_SeedCover(g) || memcmp(refs, Vec_IntArray(&p->vMapRefs), sizeof(int)*n) ) goto fail;
        if ( !edits ) break;
    }
    ABC_FREE( refs );
    return 1;
fail:
    ABC_FREE( refs );
    return 0;
}

/**Function*************************************************************

  Synopsis    [The output required time: the seed's own fixed-arc delay, relaxed by
  the ratio of the -t model target to the incumbent's model delay
  (ModelRef).]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_SeedSetTarget( Scm_Seed_t * g, float ModelRef )
{
    Scm_Man_t * p = g->p;
    Gia_Obj_t * o;
    double Fixed = 0;
    int i;
    Gia_ManForEachCo( p->pGia, o, i )
        Fixed = fmax(Fixed, Scm_LabelWorst(g->labels + Gia_ObjFaninLit0p(p->pGia, o)));
    g->target = Fixed;
    if ( p->pPars->ModelDelayTarget > 0 && Fixed > 0 && ModelRef > 0 )
        g->target = Fixed * fmax(1.0, (double)p->pPars->ModelDelayTarget / ModelRef);
}

/**Function*************************************************************

  Synopsis    [Builds the cover of seed iSeed.]

  Description [Arc costs per output transition:
  unit view: one unit;
  seed 0: the GENLIB pin delay (read_lib -G's gain delay), split into rise
  and fall in the ratio of the family's fitted Liberty delays at a load of
  SeedLoad times the pin's capacitance;
  seed 1: the family average of the fitted Liberty delays at a load of
  SeedLoad times each member's mean input capacitance.
  ModelRef relaxes the target under -t (see Scm_SeedSetTarget).]

  SideEffects [Replaces the cover and the flow references.]

  SeeAlso     []

***********************************************************************/
static int Scm_ManSeedBuild( Scm_Man_t * p, int iSeed, float ModelRef )
{
    int nGlobalRounds = 4;
    Scm_Seed_t g = {0};
    int n = 2*Gia_ManObjNum(p->pGia), ok = 0, i, j, k, t;
    g.p = p;
    g.labels = ABC_CALLOC(Scm_Label_t, n);
    g.req = ABC_ALLOC(double, 2*n);
    g.arcs = ABC_CALLOC(Scm_SeedArc_t, p->nCells*SCM_LEAF_MAX);
    for ( i = 0; i < p->nCells; i++ )
    {
        Mio_Cell2_t * cell = p->pCells + i;
        SC_Cell * rep = Scm_ManSclCell(p, cell), * member;
        for ( k = 0; k < (int)cell->nFanins; k++ )
        {
            Scm_SeedArc_t * a = g.arcs + i*SCM_LEAF_MAX + k;
            double d[2] = {0};
            int count = 0;
            if ( !rep ) goto done;
            SC_RingForEachCell( rep, member, j )
            {
                Scm_Arc_t arc = {0};
                if ( member->fSkip ) continue;
                if ( !Scm_ManFitArcCached(p, member, k, &arc) ) goto done;
                a->sense = arc.TimingSense;
                count++;
                if ( p->fUnitView ) continue;
                if ( iSeed )
                {
                    double cin = 0;
                    int pin;
                    for ( pin = 0; pin < (int)cell->nFanins; pin++ )
                        cin += SC_CellPinCap(member, pin);
                    cin /= cell->nFanins;
                    for ( t = 0; t < 2; t++ )
                        d[t] += fmax(1e-3, arc.RfDelay0[t] + arc.RfDelayLoad[t]*(double)p->pPars->SeedLoad*cin + arc.RfDelaySlew[t]*p->AveSlew);
                }
                else
                    for ( t = 0; t < 2; t++ )
                        d[t] += fmax(1e-3, arc.RfDelay0[t] + arc.RfDelayLoad[t]*(double)p->pPars->SeedLoad*SC_CellPinCap(member, k) + arc.RfDelaySlew[t]*p->AveSlew);
            }
            if ( !count ) goto done;
            if ( p->fUnitView )
                a->d[0] = a->d[1] = 1.0;
            else if ( d[0] + d[1] <= 0 )
                goto done;
            else if ( iSeed )
                for ( t = 0; t < 2; t++ )
                    a->d[t] = d[t]/count;
            else
            {
                double cost = Scl_Int2Flt(cell->iDelays[k]);
                for ( t = 0; t < 2; t++ )
                    a->d[t] = cost*(2*d[t]/(d[0]+d[1]));
            }
        }
    }
    // the flow references start from the AIG's structure
    for ( g.round = 0; g.round < nGlobalRounds; g.round++ )
    {
        if ( !Scm_SeedForward(&g) ) goto done;
        if ( !g.round ) Scm_SeedSetTarget(&g, ModelRef);
        if ( !Scm_SeedCover(&g) ) goto done;
    }
    for ( i = 0; i < n; i++ )
        if ( g.labels[i].valid )
            *Scm_ObjMatch(p, i >> 1, i & 1) = g.labels[i].mat;
    if ( !Scm_SeedExactArea(&g) ) goto done;
    ok = 1;
done:
    ABC_FREE( g.labels );
    ABC_FREE( g.req );
    ABC_FREE( g.arcs );
    return ok;
}
