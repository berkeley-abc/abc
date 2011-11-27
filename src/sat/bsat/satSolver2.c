/**************************************************************************************************
MiniSat -- Copyright (c) 2005, Niklas Sorensson
http://www.cs.chalmers.se/Cs/Research/FormalMethods/MiniSat/

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/
// Modified to compile with MS Visual Studio 6.0 by Alan Mishchenko

#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <math.h>

#include "satSolver2.h"

ABC_NAMESPACE_IMPL_START


#define SAT_USE_ANALYZE_FINAL
//#define SAT_USE_WATCH_ARRAYS

//=================================================================================================
// Debug:

//#define VERBOSEDEBUG

// For derivation output (verbosity level 2)
#define L_IND    "%-*d"
#define L_ind    sat_solver2_dlevel(s)*3+3,sat_solver2_dlevel(s)
#define L_LIT    "%sx%d"
#define L_lit(p) lit_sign(p)?"~":"", (lit_var(p))
static void printlits(lit* begin, lit* end)
{
    int i;
    for (i = 0; i < end - begin; i++)
        printf(L_LIT" ",L_lit(begin[i]));
}

//=================================================================================================
// Random numbers:


// Returns a random float 0 <= x < 1. Seed must never be 0.
static inline double drand(double* seed) {
    int q;
    *seed *= 1389796;
    q = (int)(*seed / 2147483647);
    *seed -= (double)q * 2147483647;
    return *seed / 2147483647; }


// Returns a random integer 0 <= x < size. Seed must never be 0.
static inline int irand(double* seed, int size) {
    return (int)(drand(seed) * size); }


//=================================================================================================
// Predeclarations:

static void sat_solver2_sort(void** array, int size, int(*comp)(const void *, const void *));

//=================================================================================================
// Variable datatype + minor functions:

static const int var0  = 1;
static const int var1  = 0;
static const int varX  = 3;

struct varinfo_t
{
    unsigned val    :  2; 
    unsigned pol    :  1;
    unsigned mark   :  1;
    unsigned tag    :  3;
    unsigned lev    : 25;
};

static inline int     var_value     (sat_solver2 * s, int v)            { return s->vi[v].val;                          }
static inline int     var_polar     (sat_solver2 * s, int v)            { return s->vi[v].pol;                          }
static inline int     var_tag       (sat_solver2 * s, int v)            { return s->vi[v].tag;                          }
static inline int     var_mark      (sat_solver2 * s, int v)            { return s->vi[v].mark;                         }
static inline int     var_level     (sat_solver2 * s, int v)            { return s->vi[v].lev;                          }

static inline void    var_set_value (sat_solver2 * s, int v, int val )  { s->vi[v].val = val;                           }
static inline void    var_set_polar (sat_solver2 * s, int v, int pol )  { s->vi[v].pol = pol;                           }
static inline void    var_set_tag   (sat_solver2 * s, int v, int tag )  { s->vi[v].tag = tag;                           }
static inline void    var_set_mark  (sat_solver2 * s, int v, int mark)  { s->vi[v].mark = mark;                         }
static inline void    var_set_level (sat_solver2 * s, int v, int lev )  { s->vi[v].lev = lev;                           }

//=================================================================================================
// Clause datatype + minor functions:

struct clause_t // should have odd number of entries!
{
    unsigned learnt :  1;
    unsigned fMark  :  1;
    unsigned fPartA :  1;
    unsigned fRefed :  1;
    unsigned nLits  : 28;
    unsigned act;
    unsigned proof;
#ifndef SAT_USE_WATCH_ARRAYS
    int      pNext[2];
#endif
    lit lits[0];
};

static inline lit*    clause_begin  (clause* c)                  { return c->lits;                                 }
static inline int     clause_learnt (clause* c)                  { return c->learnt;                               }
static inline int     clause_nlits  (clause* c)                  { return c->nLits;                                }
static inline int     clause_size   (int nLits)                  { return sizeof(clause)/4 + nLits + !(nLits & 1); }

static inline clause* get_clause    (sat_solver2* s, int c)      { return (clause *)(s->pMemArray + c);            }
static inline int     clause_id     (sat_solver2* s, clause* c)  { return ((int *)c - s->pMemArray);               }

#define sat_solver_foreach_clause( s, c, i )  \
    for ( i = 16; (i < s->nMemSize) && (((c) = get_clause(s, i)), 1); i += clause_size(c->nLits) )
#define sat_solver_foreach_learnt( s, c, i )  \
    for ( i = s->iLearnt; (i < s->nMemSize) && (((c) = get_clause(s, i)), 1); i += clause_size(c->nLits) )

//=================================================================================================
// Simple helpers:

static inline int     sat_solver2_dlevel(sat_solver2* s)            { return veci_size(&s->trail_lim); }
static inline veci*   sat_solver2_read_wlist(sat_solver2* s, lit l) { return &s->wlists[l]; }

//=================================================================================================
// Variable order functions:

static inline void order_update(sat_solver2* s, int v) // updateorder
{
    int*      orderpos = s->orderpos;
    int*      heap     = veci_begin(&s->order);
    int       i        = orderpos[v];
    int       x        = heap[i];
    int       parent   = (i - 1) / 2;

    assert(s->orderpos[v] != -1);

    while (i != 0 && s->activity[x] > s->activity[heap[parent]]){
        heap[i]           = heap[parent];
        orderpos[heap[i]] = i;
        i                 = parent;
        parent            = (i - 1) / 2;
    }
    heap[i]     = x;
    orderpos[x] = i;
}

static inline void order_assigned(sat_solver2* s, int v) 
{
}

static inline void order_unassigned(sat_solver2* s, int v) // undoorder
{
    int* orderpos = s->orderpos;
    if (orderpos[v] == -1){
        orderpos[v] = veci_size(&s->order);
        veci_push(&s->order,v);
        order_update(s,v);
    }
}

static inline int  order_select(sat_solver2* s, float random_var_freq) // selectvar
{
    int*      heap     = veci_begin(&s->order);
    int*      orderpos = s->orderpos;
//    lbool*    values   = s->assigns;

    // Random decision:
    if (drand(&s->random_seed) < random_var_freq){
        int next = irand(&s->random_seed,s->size);
        assert(next >= 0 && next < s->size);
//        if (values[next] == l_Undef)
        if (var_value(s, next) == varX)
            return next;
    }

    // Activity based decision:
    while (veci_size(&s->order) > 0){
        int    next  = heap[0];
        int    size  = veci_size(&s->order)-1;
        int    x     = heap[size];

        veci_resize(&s->order,size);

        orderpos[next] = -1;

        if (size > 0){
            unsigned act   = s->activity[x];
            int      i     = 0;
            int      child = 1;

            while (child < size){
                if (child+1 < size && s->activity[heap[child]] < s->activity[heap[child+1]])
                    child++;

                assert(child < size);

                if (act >= s->activity[heap[child]])
                    break;

                heap[i]           = heap[child];
                orderpos[heap[i]] = i;
                i                 = child;
                child             = 2 * child + 1;
            }
            heap[i]           = x;
            orderpos[heap[i]] = i;
        }

//printf( "-%d ", next );
//        if (values[next] == l_Undef)
        if (var_value(s, next) == varX)
            return next;
    }

    return var_Undef;
}

//=================================================================================================
// Activity functions:

static inline void act_var_rescale(sat_solver2* s) {
    unsigned* activity = s->activity;
    int i, clk = clock();
    static int Total = 0;
    for (i = 0; i < s->size; i++)
        activity[i] >>= 19;
    s->var_inc >>= 19;
//    assert( s->var_inc > 15 );
    s->var_inc = Abc_MaxInt( s->var_inc, (1<<4) );
//    printf( "Rescaling... Var inc = %5d  Conf = %10d ", s->var_inc,  s->stats.conflicts );
    Total += clock() - clk;
//    Abc_PrintTime( 1, "Time", Total );
}

static inline void act_var_bump(sat_solver2* s, int v) {
    static int Counter = 0;
    s->activity[v] += s->var_inc;
    if (s->activity[v] & 0x80000000)
        act_var_rescale(s);
    if (s->orderpos[v] != -1)
        order_update(s,v);
}

//static inline void act_var_decay(sat_solver2* s) { s->var_inc *= s->var_decay; }
static inline void act_var_decay(sat_solver2* s) { s->var_inc += (s->var_inc >> 4); }

static inline void act_clause_rescale(sat_solver2* s) {
    clause * c;
    int i, clk = clock();
    static int Total = 0;
    sat_solver_foreach_learnt( s, c, i )
        c->act >>= 14;
    s->cla_inc >>= 14;
//    assert( s->cla_inc > (1<<10)-1 );
    s->cla_inc = Abc_MaxInt( s->cla_inc, (1<<10) );
    printf( "Rescaling... Cla inc = %5d  Conf = %10d   ", s->cla_inc,  s->stats.conflicts );
    Total += clock() - clk;
    Abc_PrintTime( 1, "Time", Total );
}


static inline void act_clause_bump(sat_solver2* s, clause *c) {
    c->act += s->cla_inc;
    if (c->act & 0x80000000) 
        act_clause_rescale(s);
}

//static inline void act_clause_decay(sat_solver2* s) { s->cla_inc *= s->cla_decay; }
static inline void act_clause_decay(sat_solver2* s) { s->cla_inc += (s->cla_inc >> 10); }

//=================================================================================================
// Clause functions:
#ifndef SAT_USE_WATCH_ARRAYS

static inline void clause_watch_front( sat_solver2* s, clause* c, lit Lit )
{
    if ( c->lits[0] == Lit )
        c->pNext[0] = s->pWatches[lit_neg(Lit)];  
    else
    {
        assert( c->lits[1] == Lit );
        c->pNext[1] = s->pWatches[lit_neg(Lit)];  
    }
    s->pWatches[lit_neg(Lit)] = clause_id(s, c);
}
static inline void clause_watch( sat_solver2* s, clause* c, lit Lit )
{
    clause * pList;
    cla * ppList = s->pWatches + lit_neg(Lit), * ppNext;
    if ( c->lits[0] == Lit )
        ppNext = &c->pNext[0];  
    else
    {
        assert( c->lits[1] == Lit );
        ppNext = &c->pNext[1];
    }
    if ( *ppList == 0 )
    {
        *ppList = clause_id(s, c);
        *ppNext = clause_id(s, c);
        return;
    }
    // add at the tail
    pList = get_clause( s, *ppList );
    if ( pList->lits[0] == Lit )
    {
        assert( pList->pNext[0] != 0 );
        *ppNext = pList->pNext[0];
        pList->pNext[0] = clause_id(s, c);  
    }
    else
    {
        assert( pList->lits[1] == Lit );
        assert( pList->pNext[1] != 0 );
        *ppNext = pList->pNext[1];
        pList->pNext[1] = clause_id(s, c);  
    }
    *ppList = clause_id(s, c);
}
/*
static inline void clause_watch( sat_solver2* s, clause* c, lit Lit )
{
    int * ppList = s->pWatches[lit_neg(Lit)];
    assert( c->lits[0] == Lit || c->lits[1] == Lit );
    if ( *ppList == NULL )
        c->pNext[c->lits[1] == Lit] = clause_id(s, c);
    else
    {
        clause * pList = get_clause( s, *ppList );
        assert( pList->lits[0] == Lit || pList->lits[1] == Lit );
        c->pNext[c->lits[1] == Lit] = pList->pNext[pList->lits[1] == Lit];
        pList->pNext[pList->lits[1] == Lit] = clause_id(s, c);  
    }
    s->pWatches[lit_neg(Lit)] = clause_id(s, c);
}
*/
#endif

static int clause_new(sat_solver2* s, lit* begin, lit* end, int learnt)
{
    clause* c;
    int i, Cid, nLits = end - begin;
    assert(nLits > 1);
    assert(begin[0] >= 0);
    assert(begin[1] >= 0);
    assert(lit_var(begin[0]) < s->size);
    assert(lit_var(begin[1]) < s->size);
    // add memory if needed
    if ( s->nMemSize + clause_size(nLits) > s->nMemAlloc )
    {
        int nMemAlloc = s->nMemAlloc ? s->nMemAlloc * 2 : (1 << 24);
        s->pMemArray  = ABC_REALLOC( int, s->pMemArray, nMemAlloc );
        memset( s->pMemArray + s->nMemAlloc, 0, sizeof(int) * (nMemAlloc - s->nMemAlloc) );
        printf( "Reallocing from %d to %d...\n", s->nMemAlloc, nMemAlloc );
        s->nMemAlloc = nMemAlloc;
        s->nMemSize = Abc_MaxInt( s->nMemSize, 16 ); 
    }
    // create clause
    c = (clause*)(s->pMemArray + s->nMemSize);
    c->learnt = learnt;
    c->nLits  = nLits;
    for (i = 0; i < nLits; i++)
        c->lits[i] = begin[i];

    // extend storage
    Cid = s->nMemSize;
    s->nMemSize += clause_size(nLits);
    if ( s->nMemSize > s->nMemAlloc )
        printf( "Out of memory!!!\n" );
    assert( s->nMemSize <= s->nMemAlloc );
    assert(((ABC_PTRUINT_T)c & 7) == 0);


#ifdef SAT_USE_WATCH_ARRAYS
    veci_push(sat_solver2_read_wlist(s,lit_neg(begin[0])),clause_id(s,c));
    veci_push(sat_solver2_read_wlist(s,lit_neg(begin[1])),clause_id(s,c));
#else
    clause_watch( s, c, begin[0] );
    clause_watch( s, c, begin[1] );
#endif

    // remember the last one and first learnt
    s->iLast = Cid;
    if ( learnt && s->iLearnt == -1 )
        s->iLearnt = Cid;
    return Cid;
}


static void clause_remove(sat_solver2* s, clause* c)
{
    lit* lits = clause_begin(c);
    assert(lit_neg(lits[0]) < s->size*2);
    assert(lit_neg(lits[1]) < s->size*2);

#ifdef SAT_USE_WATCH_ARRAYS
    veci_remove(sat_solver2_read_wlist(s,lit_neg(lits[0])),clause_id(s,c));
    veci_remove(sat_solver2_read_wlist(s,lit_neg(lits[1])),clause_id(s,c));
#endif

    if (clause_learnt(c)){
        s->stats.learnts--;
        s->stats.learnts_literals -= clause_nlits(c);
    }else{
        s->stats.clauses--;
        s->stats.clauses_literals -= clause_nlits(c);
    }
}


static lbool clause_simplify(sat_solver2* s, clause* c)
{
    lit*   lits   = clause_begin(c);
//    lbool* values = s->assigns;
    int i;

    assert(sat_solver2_dlevel(s) == 0);

    for (i = 0; i < clause_nlits(c); i++){
//        lbool sig = !lit_sign(lits[i]); sig += sig - 1;
//        if (values[lit_var(lits[i])] == sig)
        if (var_value(s, lit_var(lits[i])) == lit_sign(lits[i]))
            return l_True;
    }
    return l_False;
}

//=================================================================================================
// Minor (solver) functions:

void sat_solver2_setnvars(sat_solver2* s,int n)
{
    int var;

    if (s->cap < n){
 
        while (s->cap < n) s->cap = s->cap*2+1;

#ifdef SAT_USE_WATCH_ARRAYS
        s->wlists    = ABC_REALLOC(veci,     s->wlists,   s->cap*2);
#else
        s->pWatches  = ABC_REALLOC(cla,      s->pWatches, s->cap*2);
#endif
        s->vi        = ABC_REALLOC(varinfo,  s->vi,       s->cap);
        s->activity  = ABC_REALLOC(unsigned, s->activity, s->cap);
        s->orderpos  = ABC_REALLOC(int,      s->orderpos, s->cap);
        s->reasons   = ABC_REALLOC(cla,      s->reasons,  s->cap);
        s->trail     = ABC_REALLOC(lit,      s->trail,    s->cap);
    }

    for (var = s->size; var < n; var++){
#ifdef SAT_USE_WATCH_ARRAYS
        veci_new(&s->wlists[2*var]);
        veci_new(&s->wlists[2*var+1]);
#else
        s->pWatches[2*var]   = 0;
        s->pWatches[2*var+1] = 0;
#endif
        *((int*)s->vi + var) = 0; s->vi[var].val = varX;
        s->activity [var]    = (1<<10);
        s->orderpos [var]    = veci_size(&s->order);
        s->reasons  [var]    = 0;
        
        // does not hold because variables enqueued at top level will not be reinserted in the heap
        // assert(veci_size(&s->order) == var); 
        veci_push(&s->order,var);
        order_update(s, var);
    }

    s->size = n > s->size ? n : s->size;
}


static inline int enqueue(sat_solver2* s, lit l, int from)
{
    int    v      = lit_var(l);
#ifdef VERBOSEDEBUG
    printf(L_IND"enqueue("L_LIT")\n", L_ind, L_lit(l));
#endif
    if (var_value(s, v) != varX)
        return var_value(s, v) == lit_sign(l);
    else
    {  // New fact -- store it.
#ifdef VERBOSEDEBUG
        printf(L_IND"bind("L_LIT")\n", L_ind, L_lit(l));
#endif
        var_set_value( s, v, lit_sign(l) );
        var_set_level( s, v, sat_solver2_dlevel(s) );
        s->reasons[v] = from;
        s->trail[s->qtail++] = l;
        order_assigned(s, v);
        return true;
    }
}

static inline int assume(sat_solver2* s, lit l)
{
    assert(s->qtail == s->qhead);
    assert(var_value(s, lit_var(l)) == varX);
#ifdef VERBOSEDEBUG
    printf(L_IND"assume("L_LIT")\n", L_ind, L_lit(l));
#endif
    veci_push(&s->trail_lim,s->qtail);
    return enqueue(s,l,0);
}

static void sat_solver2_canceluntil(sat_solver2* s, int level) {
    lit*     trail;   
    int      bound;
    int      lastLev;
    int      c, x;
   
    if (sat_solver2_dlevel(s) <= level)
        return;

    trail   = s->trail;
    bound   = (veci_begin(&s->trail_lim))[level];
    lastLev = (veci_begin(&s->trail_lim))[veci_size(&s->trail_lim)-1];

    for (c = s->qtail-1; c >= bound; c--) 
    {
        x = lit_var(trail[c]);
        var_set_value(s, x, varX);
        s->reasons[x] = 0;
        if ( c < lastLev )
            var_set_polar(s, x, !lit_sign(trail[c]));
    }

    for (c = s->qhead-1; c >= bound; c--)
        order_unassigned(s,lit_var(trail[c]));

    s->qhead = s->qtail = bound;
    veci_resize(&s->trail_lim,level);
}

static void sat_solver2_record(sat_solver2* s, veci* cls)
{
    lit* begin = veci_begin(cls);
    lit* end   = begin + veci_size(cls);
    int  c     = (veci_size(cls) > 1) ? clause_new(s,begin,end,1) : 0;
    enqueue(s,*begin,c);

    assert(veci_size(cls) > 0);

    if (c) {
        act_clause_bump(s,get_clause(s,c));
        s->stats.learnts++;
        s->stats.learnts_literals += veci_size(cls);
    }
}


static double sat_solver2_progress(sat_solver2* s)
{
    int i;
    double progress = 0.0, F = 1.0 / s->size;
    for (i = 0; i < s->size; i++)
        if (var_value(s, i) != varX)
            progress += pow(F, var_level(s, i));
    return progress / s->size;
}

//=================================================================================================
// Major methods:

static int sat_solver2_lit_removable(sat_solver2* s, lit l, int minl)
{
    clause* c;
    lit* lits;
    int i, j, v, top = veci_size(&s->tagged);
    assert(lit_var(l) >= 0 && lit_var(l) < s->size);
    assert(s->reasons[lit_var(l)] != 0);
    veci_resize(&s->stack,0);
    veci_push(&s->stack,lit_var(l));
    while (veci_size(&s->stack) > 0)
    {
        v = veci_begin(&s->stack)[veci_size(&s->stack)-1];
        assert(v >= 0 && v < s->size);
        veci_resize(&s->stack,veci_size(&s->stack)-1);
        assert(s->reasons[v] != 0);
        c = get_clause(s, s->reasons[v]);
        lits = clause_begin(c);
        for (i = 1; i < clause_nlits(c); i++){
            int v = lit_var(lits[i]);
            if (s->vi[v].tag == 0 && var_level(s,v)){
                if (s->reasons[v] != 0 && ((1 << (var_level(s,v) & 31)) & minl)){
                    veci_push(&s->stack,lit_var(lits[i]));
                    var_set_tag(s, v, 1);
                    veci_push(&s->tagged,v);
                }else{
                    int* tagged = veci_begin(&s->tagged);
                    for (j = top; j < veci_size(&s->tagged); j++)
                        var_set_tag(s, tagged[j], 0);
                    veci_resize(&s->tagged,top);
                    return false;
                }
            }
        }
    }
    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|  
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
/*
void Solver::analyzeFinal(Clause* confl, bool skip_first)
{
    // -- NOTE! This code is relatively untested. Please report bugs!
    conflict.clear();
    if (root_level == 0) return;

    vec<char>& seen  = analyze_seen;
    for (int i = skip_first ? 1 : 0; i < confl->size(); i++){
        Var x = var((*confl)[i]);
        if (level[x] > 0)
            seen[x] = 1;
    }

    int start = (root_level >= trail_lim.size()) ? trail.size()-1 : trail_lim[root_level];
    for (int i = start; i >= trail_lim[0]; i--){
        Var     x = var(trail[i]);
        if (seen[x]){
            GClause r = reason[x];
            if (r == GClause_NULL){
                assert(level[x] > 0);
                conflict.push(~trail[i]);
            }else{
                if (r.isLit()){
                    Lit p = r.lit();
                    if (level[var(p)] > 0)
                        seen[var(p)] = 1;
                }else{
                    Clause& c = *r.clause();
                    for (int j = 1; j < c.size(); j++)
                        if (level[var(c[j])] > 0)
                            seen[var(c[j])] = 1;
                }
            }
            seen[x] = 0;
        }
    }
}
*/

#ifdef SAT_USE_ANALYZE_FINAL

static void sat_solver2_analyze_final(sat_solver2* s, clause* conf, int skip_first)
{
    int* tagged;
    int i, j, start;
    veci_resize(&s->conf_final,0);
    if ( s->root_level == 0 )
        return;
    assert( veci_size(&s->tagged) == 0 );
    for (i = skip_first ? 1 : 0; i < clause_nlits(conf); i++)
    {
        int x = lit_var(clause_begin(conf)[i]);
        if ( var_level(s,x) )
        {
            var_set_tag(s, x, 1);
            veci_push(&s->tagged,x);
        }
    }

    start = (s->root_level >= veci_size(&s->trail_lim))? s->qtail-1 : (veci_begin(&s->trail_lim))[s->root_level];
    for (i = start; i >= (veci_begin(&s->trail_lim))[0]; i--){
        int x = lit_var(s->trail[i]);
        if (s->vi[x].tag == 1){
            if (s->reasons[x] == 0){
                assert( var_level(s,x) );
                veci_push(&s->conf_final,lit_neg(s->trail[i]));
            }else{
                clause* c = get_clause(s, s->reasons[x]);
                int* lits = clause_begin(c);
                for (j = 1; j < clause_nlits(c); j++)
                    if ( var_level(s,lit_var(lits[j])) )
                    {
                        var_set_tag(s, lit_var(lits[j]), 1);
                        veci_push(&s->tagged,lit_var(lits[j]));
                    }
            }
        }
    }
    tagged = veci_begin(&s->tagged);
    for (i = 0; i < veci_size(&s->tagged); i++)
        var_set_tag(s, tagged[i], 0);
    veci_resize(&s->tagged,0);
}

#endif


static void sat_solver2_analyze(sat_solver2* s, clause* c, veci* learnt)
{
    lit*     trail   = s->trail;
    int      cnt     = 0;
    lit      p       = lit_Undef;
    int      ind     = s->qtail-1;
    lit*     lits;
    int      i, j, minl;
    int*     tagged;
    assert( veci_size(&s->tagged) == 0 );

    veci_push(learnt,lit_Undef);

    do{
        assert(c != 0);
        if (clause_learnt(c))
            act_clause_bump(s,c);

        lits = clause_begin(c);
        for (j = (p == lit_Undef ? 0 : 1); j < clause_nlits(c); j++){
            lit q = lits[j];
            assert(lit_var(q) >= 0 && lit_var(q) < s->size);
            if (!var_tag(s, lit_var(q)) && var_level(s,lit_var(q))){
                var_set_tag(s, lit_var(q), 1);
                veci_push(&s->tagged,lit_var(q));
                act_var_bump(s,lit_var(q));
                if (var_level(s,lit_var(q)) == sat_solver2_dlevel(s))
                    cnt++;
                else
                    veci_push(learnt,q);
            }
        }

        while (!var_tag(s, lit_var(trail[ind--])));

        p = trail[ind+1];
        c = get_clause(s, s->reasons[lit_var(p)]);
        cnt--;

    }while (cnt > 0);

    *veci_begin(learnt) = lit_neg(p);

    lits = veci_begin(learnt);
    minl = 0;
    for (i = 1; i < veci_size(learnt); i++)
        minl |= 1 << (var_level(s,lit_var(lits[i])) & 31);

    // simplify (full)
    for (i = j = 1; i < veci_size(learnt); i++){
        if (s->reasons[lit_var(lits[i])] == 0 || !sat_solver2_lit_removable(s,lits[i],minl))
            lits[j++] = lits[i];
    }

    // update size of learnt + statistics
    s->stats.max_literals += veci_size(learnt);
    veci_resize(learnt,j);
    s->stats.tot_literals += j;

    // clear tags
    tagged = veci_begin(&s->tagged);
    for (i = 0; i < veci_size(&s->tagged); i++)
        var_set_tag(s, tagged[i], 0);
    veci_resize(&s->tagged,0);

#ifdef DEBUG
    for (i = 0; i < s->size; i++)
        assert(!var_tag(s, i));
#endif

#ifdef VERBOSEDEBUG
    printf(L_IND"Learnt {", L_ind);
    for (i = 0; i < veci_size(learnt); i++) printf(" "L_LIT, L_lit(lits[i]));
#endif
    if (veci_size(learnt) > 1){
        lit tmp;
        int max_i = 1;
        int max   = var_level(s, lit_var(lits[1]));
        for (i = 2; i < veci_size(learnt); i++)
            if (max < var_level(s, lit_var(lits[i]))) {
                max = var_level(s, lit_var(lits[i]));
                max_i = i;
            }

        tmp         = lits[1];
        lits[1]     = lits[max_i];
        lits[max_i] = tmp;
    }
#ifdef VERBOSEDEBUG
    {
        int lev = veci_size(learnt) > 1 ? var_level(s, lit_var(lits[1])) : 0;
        printf(" } at level %d\n", lev);
    }
#endif
}

#ifndef SAT_USE_WATCH_ARRAYS

static inline clause* clause_propagate__front( sat_solver2* s, lit Lit )
{
    clause * pCur;
    cla * ppPrev, pThis, pTemp;
    lit LitF = lit_neg(Lit);
    int i, Counter = 0;
    s->stats.propagations++;
    if ( s->pWatches[Lit] == 0 )
        return NULL;
    // iterate through the literals
    ppPrev = s->pWatches + Lit;
    for ( pThis = *ppPrev; pThis; pThis = *ppPrev )
    {
        Counter++;
        // make sure the false literal is in the second literal of the clause
        pCur = get_clause( s, pThis );
        if ( pCur->lits[0] == LitF )
        {
            pCur->lits[0] = pCur->lits[1];
            pCur->lits[1] = LitF;
            pTemp = pCur->pNext[0];
            pCur->pNext[0] = pCur->pNext[1];
            pCur->pNext[1] = pTemp;
        }
        assert( pCur->lits[1] == LitF );

        // if the first literal is true, the clause is satisfied
//        if ( pCur->lits[0] == s->pAssigns[lit_var(pCur->lits[0])] )
//        sig = !lit_sign(pCur->lits[0]); sig += sig - 1;
//        if (s->assigns[lit_var(pCur->lits[0])] == sig)
        if (var_value(s, lit_var(pCur->lits[0])) == lit_sign(pCur->lits[0]))
        {
            ppPrev = &pCur->pNext[1];
            continue;
        }

        // look for a new literal to watch
        for ( i = 2; i < clause_nlits(pCur); i++ )
        {
            // skip the case when the literal is false
//            if ( lit_neg(pCur->lits[i]) == p->pAssigns[lit_var(pCur->lits[i])] )
//            sig = lit_sign(pCur->lits[i]); sig += sig - 1;
//            if (s->assigns[lit_var(pCur->lits[i])] == sig)
            if (var_value(s, lit_var(pCur->lits[i])) == !lit_sign(pCur->lits[i]))
                continue;
            // the literal is either true or unassigned - watch it
            pCur->lits[1] = pCur->lits[i];
            pCur->lits[i] = LitF;
            // remove this clause from the watch list of Lit
            *ppPrev = pCur->pNext[1];
            // add this clause to the watch list of pCur->lits[i] (now it is pCur->lits[1])
            clause_watch( s, pCur, pCur->lits[1] );
            break;
        }
        if ( i < clause_nlits(pCur) ) // found new watch
            continue;

        // clause is unit - enqueue new implication
        if ( enqueue(s, pCur->lits[0], clause_id(s,pCur)) )
        {
            ppPrev = &pCur->pNext[1];
            continue;
        }

        // conflict detected - return the conflict clause
//        printf( "%d ", Counter );
        return pCur;
    }
//    printf( "%d ", Counter );
    return NULL;
}
clause* sat_solver2_propagate_new__front( sat_solver2* s )
{
    clause* pClause;
    lit Lit;
    while ( s->qtail - s->qhead > 0 )
    {
        Lit = s->trail[s->qhead++];
        pClause = clause_propagate__front( s, Lit );
        if ( pClause )
            return pClause;
    }
    return NULL;
}

static inline clause* clause_propagate( sat_solver2* s, lit Lit, int * ppHead, int * ppTail )
{
    clause * pCur;
    cla * ppPrev = ppHead, pThis, pTemp, pPrev = 0;
    lit LitF = lit_neg(Lit);
    int i, Counter = 0;
    // iterate through the literals
    for ( pThis = *ppPrev; pThis; pThis = *ppPrev )
    {
        Counter++;
        // make sure the false literal is in the second literal of the clause
        pCur = get_clause( s, pThis );
        if ( pCur->lits[0] == LitF )
        {
            pCur->lits[0] = pCur->lits[1];
            pCur->lits[1] = LitF;
            pTemp = pCur->pNext[0];
            pCur->pNext[0] = pCur->pNext[1];
            pCur->pNext[1] = pTemp;
        }
        assert( pCur->lits[1] == LitF );

        // if the first literal is true, the clause is satisfied
//        if ( pCur->lits[0] == s->pAssigns[lit_var(pCur->lits[0])] )
//        sig = !lit_sign(pCur->lits[0]); sig += sig - 1;
//        if ( s->assigns[lit_var(pCur->lits[0])] == sig )
        if (var_value(s, lit_var(pCur->lits[0])) == lit_sign(pCur->lits[0]))
        {
            pPrev = pThis;
            ppPrev = &pCur->pNext[1];
            continue;
        }

        // look for a new literal to watch
        for ( i = 2; i < clause_nlits(pCur); i++ )
        {
            // skip the case when the literal is false
//            if ( lit_neg(pCur->lits[i]) == p->pAssigns[lit_var(pCur->lits[i])] )
//            sig = lit_sign(pCur->lits[i]); sig += sig - 1;
//            if ( s->assigns[lit_var(pCur->lits[i])] == sig )
            if (var_value(s, lit_var(pCur->lits[i])) == !lit_sign(pCur->lits[i]))
                continue;
            // the literal is either true or unassigned - watch it
            pCur->lits[1] = pCur->lits[i];
            pCur->lits[i] = LitF;
            // remove this clause from the watch list of Lit
            if ( pCur->pNext[1] == 0 )
            {
                assert( *ppTail == pThis );
                *ppTail = pPrev;
            }
            *ppPrev = pCur->pNext[1];
            // add this clause to the watch list of pCur->lits[i] (now it is pCur->lits[1])
            clause_watch( s, pCur, pCur->lits[1] );
            break;
        }
        if ( i < clause_nlits(pCur) ) // found new watch
            continue;

        // clause is unit - enqueue new implication
        if ( enqueue(s, pCur->lits[0], clause_id(s,pCur)) )
        {
            pPrev = pThis;
            ppPrev = &pCur->pNext[1];
            continue;
        }

        // conflict detected - return the conflict clause
//        printf( "%d ", Counter );
        return pCur;
    }
//    printf( "%d ", Counter );
    return NULL;

}
clause* sat_solver2_propagate_new( sat_solver2* s )
{ 
    clause * pClause, * pTailC;
    cla pHead, pTail;
    lit Lit;
    while ( s->qtail - s->qhead > 0 )
    {
        s->stats.propagations++;
        Lit = s->trail[s->qhead++];
        if ( s->pWatches[Lit] == 0 )
            continue;
        // get head and tail
        pTail = s->pWatches[Lit];
        pTailC = get_clause( s, pTail );
/*
        if ( pTailC->lits[0] == lit_neg(Lit) )
        {
            pHead = pTailC->pNext[0]; 
            pTailC->pNext[0] = NULL;
        }
        else
        {
            assert( pTailC->lits[1] == lit_neg(Lit) );
            pHead = pTailC->pNext[1];  
            pTailC->pNext[1] = NULL;
        }
*/
        if ( s->stats.propagations == 10 )
        {
            int s = 0;
        }
        assert( pTailC->lits[0] == lit_neg(Lit) || pTailC->lits[1] == lit_neg(Lit) );
        pHead = pTailC->pNext[pTailC->lits[1] == lit_neg(Lit)]; 
        pTailC->pNext[pTailC->lits[1] == lit_neg(Lit)] = 0;

        // propagate
        pClause = clause_propagate( s, Lit, &pHead, &pTail );
        assert( (pHead == 0) == (pTail == 0) );

        // create new list
        s->pWatches[Lit] = pTail;
/*
        if ( pTail )
        {
            pTailC = get_clause( s, pTail );
            if ( pTailC->lits[0] == lit_neg(Lit) )
                pTailC->pNext[0] = pHead;
            else
            {
                assert( pTailC->lits[1] == lit_neg(Lit) );
                pTailC->pNext[1] = pHead;
            }
        }
*/
        if ( pTail )
        {
            pTailC = get_clause( s, pTail );
            assert( pTailC->lits[0] == lit_neg(Lit) || pTailC->lits[1] == lit_neg(Lit) );
            pTailC->pNext[pTailC->lits[1] == lit_neg(Lit)] = pHead;
        }
        if ( pClause )
            return pClause;
    }
    return NULL;
}

#endif

clause* sat_solver2_propagate(sat_solver2* s)
{
    clause * c, * confl  = NULL;
    veci* ws;
    lit* lits, false_lit, p, * stop, * k;
    cla* begin,* end, *i, *j;


#ifndef SAT_USE_WATCH_ARRAYS
    return sat_solver2_propagate_new( s );
#endif

    while (confl == 0 && s->qtail - s->qhead > 0){
        p  = s->trail[s->qhead++];
        ws = sat_solver2_read_wlist(s,p);
        begin = (cla*)veci_begin(ws);
        end   = begin + veci_size(ws);

        s->stats.propagations++;
        s->simpdb_props--;

        for (i = j = begin; i < end; ){
            {
                c = get_clause(s,*i);
                lits = clause_begin(c);

                // Make sure the false literal is data[1]:
                false_lit = lit_neg(p);
                if (lits[0] == false_lit){
                    lits[0] = lits[1];
                    lits[1] = false_lit;
                }
                assert(lits[1] == false_lit);

                // If 0th watch is true, then clause is already satisfied.
    //            sig = !lit_sign(lits[0]); sig += sig - 1;
    //            if (values[lit_var(lits[0])] == sig){
                if (var_value(s, lit_var(lits[0])) == lit_sign(lits[0]))
                    *j++ = *i;
                else{
                    // Look for new watch:
                    stop = lits + clause_nlits(c);
                    for (k = lits + 2; k < stop; k++){
    //                    lbool sig = lit_sign(*k); sig += sig - 1;
    //                    if (values[lit_var(*k)] != sig){
                        if (var_value(s, lit_var(*k)) != !lit_sign(*k)){
                            lits[1] = *k;
                            *k = false_lit;
                            veci_push(sat_solver2_read_wlist(s,lit_neg(lits[1])),*i);
                            goto next; }
                    }

                    *j++ = *i;
                    // Clause is unit under assignment:
                    if (!enqueue(s,lits[0], *i)){
                        confl = get_clause(s,*i++);
                        // Copy the remaining watches:
    //                        s->stats.inspects2 += end - i;
                        while (i < end)
                            *j++ = *i++;
                    }
                }
            }
next:       i++;
        }
        s->stats.inspects += j - (int*)veci_begin(ws);
        veci_resize(ws,j - (int*)veci_begin(ws));
    }

    return confl;
}


static int clause_cmp (const void* x, const void* y) {
//    return clause_nlits((clause*)x) > 2 && (clause_nlits((clause*)y) == 2 || clause_activity((clause*)x) < clause_activity((clause*)y)) ? -1 : 1; }
    return clause_nlits((clause*)x) > 2 && (clause_nlits((clause*)y) == 2 || ((clause*)x)->act < ((clause*)y)->act) ? -1 : 1; }
 
void sat_solver2_reducedb(sat_solver2* s)
{
/*
    vecp     Vec, * pVec = &Vec;
    double   extra_limD = (double)s->cla_inc / veci_size(&s->learnts); // Remove any clause below this activity
    unsigned extra_lim  = (extra_limD < 1.0) ? 1 : (int)extra_limD;
    int      i, j, * pBeg, * pEnd;

    // move clauses into vector
    vecp_new( pVec );
    pBeg = (int*)veci_begin(&s->learnts);
    pEnd = pBeg + veci_size(&s->learnts);
    while ( pBeg < pEnd )
        vecp_push( pVec, get_clause(s,*pBeg++) );
    sat_solver2_sort( vecp_begin(pVec), vecp_size(pVec), &clause_cmp );
    vecp_delete( pVec );

    // compact clauses
    pBeg = (int*)veci_begin(&s->learnts);
    for (i = j = 0; i < vecp_size(pVec); i++)
    {
        clause * c = ((clause**)vecp_begin(pVec))[i]; 
        int Cid = clause_id(s,c);
//        printf( "%d ", c->act );
        if (clause_nlits(c) > 2 && s->reasons[lit_var(*clause_begin(c))] != Cid && (i < vecp_size(pVec)/2 || c->act < extra_lim) )
            clause_remove(s,c);
        else
            pBeg[j++] = Cid;
    }
printf( "Reduction removed %10d clauses (out of %10d)... Value = %d\n", veci_size(&s->learnts) - j, veci_size(&s->learnts), extra_lim );
    veci_resize(&s->learnts,j);
*/
}

static lbool sat_solver2_search(sat_solver2* s, ABC_INT64_T nof_conflicts, ABC_INT64_T * nof_learnts)
{
    double  var_decay       = 0.95;
    double  clause_decay    = 0.999;
    double  random_var_freq = s->fNotUseRandom ? 0.0 : 0.02;
//    s->var_decay = (float)(1 / var_decay   );
//    s->cla_decay = (float)(1 / clause_decay);

    ABC_INT64_T  conflictC       = 0;
    veci    learnt_clause;

    assert(s->root_level == sat_solver2_dlevel(s));

    s->stats.starts++;
    veci_resize(&s->model,0);
    veci_new(&learnt_clause);

    for (;;){
        clause* confl = sat_solver2_propagate(s);
        if (confl != 0){
            // CONFLICT
            int blevel;

#ifdef VERBOSEDEBUG
            printf(L_IND"**CONFLICT**\n", L_ind);
#endif
            s->stats.conflicts++; conflictC++;
            if (sat_solver2_dlevel(s) == s->root_level){
#ifdef SAT_USE_ANALYZE_FINAL
                sat_solver2_analyze_final(s, confl, 0);
#endif
                veci_delete(&learnt_clause);
                return l_False;
            }

            veci_resize(&learnt_clause,0);
            sat_solver2_analyze(s, confl, &learnt_clause);
            blevel = veci_size(&learnt_clause) > 1 ? var_level(s, lit_var(veci_begin(&learnt_clause)[1])) : s->root_level;
            blevel = s->root_level > blevel ? s->root_level : blevel;
            sat_solver2_canceluntil(s,blevel);
            sat_solver2_record(s,&learnt_clause);
#ifdef SAT_USE_ANALYZE_FINAL
            // if (learnt_clause.size() == 1) level[var(learnt_clause[0])] = 0;    
            // (this is ugly (but needed for 'analyzeFinal()') -- in future versions, we will backtrack past the 'root_level' and redo the assumptions)
            if ( learnt_clause.size == 1 ) 
                var_set_level( s, lit_var(learnt_clause.ptr[0]), 0 );
#endif
            act_var_decay(s);
            act_clause_decay(s);

        }else{
            // NO CONFLICT
            int next;

            if (nof_conflicts >= 0 && conflictC >= nof_conflicts){
                // Reached bound on number of conflicts:
                s->progress_estimate = sat_solver2_progress(s);
                sat_solver2_canceluntil(s,s->root_level);
                veci_delete(&learnt_clause);
                return l_Undef; }

            if ( (s->nConfLimit && s->stats.conflicts > s->nConfLimit) ||
//                 (s->nInsLimit  && s->stats.inspects  > s->nInsLimit) )
                 (s->nInsLimit  && s->stats.propagations > s->nInsLimit) )
            {
                // Reached bound on number of conflicts:
                s->progress_estimate = sat_solver2_progress(s);
                sat_solver2_canceluntil(s,s->root_level);
                veci_delete(&learnt_clause);
                return l_Undef; 
            }

//            if (sat_solver2_dlevel(s) == 0 && !s->fSkipSimplify)
                // Simplify the set of problem clauses:
//                sat_solver2_simplify(s);

            if (*nof_learnts >= 0 && s->stats.learnts - s->qtail >= *nof_learnts)
            {
                // Reduce the set of learnt clauses:
//                sat_solver2_reducedb(s);
//                *nof_learnts = *nof_learnts * 12 / 10; //*= 1.1;
            }

            // New variable decision:
            s->stats.decisions++;
            next = order_select(s,(float)random_var_freq);

            if (next == var_Undef){
                // Model found:
                int i;
                veci_resize(&s->model, 0);
                for (i = 0; i < s->size; i++) 
                    veci_push( &s->model, var_value(s,i)==var1 ? l_True : l_False );
                sat_solver2_canceluntil(s,s->root_level);
                veci_delete(&learnt_clause);

                /*
                veci apa; veci_new(&apa);
                for (i = 0; i < s->size; i++) 
                    veci_push(&apa,(int)(s->model.ptr[i] == l_True ? toLit(i) : lit_neg(toLit(i))));
                printf("model: "); printlits((lit*)apa.ptr, (lit*)apa.ptr + veci_size(&apa)); printf("\n");
                veci_delete(&apa);
                */

                return l_True;
            }

            if ( var_polar(s, next) ) // positive polarity
                assume(s,toLit(next));
            else
                assume(s,lit_neg(toLit(next)));
        }
    }

    return l_Undef; // cannot happen
}

//=================================================================================================
// External solver functions:

sat_solver2* sat_solver2_new(void)
{
    sat_solver2 * s;
    s = (sat_solver2 *)ABC_CALLOC( char, sizeof(sat_solver2) );

    // initialize vectors
    veci_new(&s->order);
    veci_new(&s->trail_lim);
    veci_new(&s->tagged);
    veci_new(&s->stack);
    veci_new(&s->model);
    veci_new(&s->temp_clause);
    veci_new(&s->conf_final);

    // initialize other
    s->iLearnt                = -1; // the first learnt clause 
    s->iLast                  = -1; // the last learnt clause 
    s->cla_inc                = (1 << 11);
    s->var_inc                = (1 << 5);
    s->random_seed            = 91648253;
    return s;
}


void sat_solver2_delete(sat_solver2* s)
{
    ABC_FREE(s->pMemArray);

    // delete vectors
    veci_delete(&s->order);
    veci_delete(&s->trail_lim);
    veci_delete(&s->tagged);
    veci_delete(&s->stack);
    veci_delete(&s->model);
    veci_delete(&s->temp_clause);
    veci_delete(&s->conf_final);

    // delete arrays
    if (s->vi != 0){
        int i;
        if ( s->wlists )
            for (i = 0; i < s->size*2; i++)
                veci_delete(&s->wlists[i]);
        ABC_FREE(s->wlists   );
        ABC_FREE(s->pWatches );
        ABC_FREE(s->vi       );
        ABC_FREE(s->activity );
        ABC_FREE(s->orderpos );
        ABC_FREE(s->reasons  );
        ABC_FREE(s->trail    );
    }
    ABC_FREE(s);
}


int sat_solver2_addclause(sat_solver2* s, lit* begin, lit* end)
{
    int c;
    lit *i,*j;
    int maxvar;
    lit last;

    veci_resize( &s->temp_clause, 0 );
    for ( i = begin; i < end; i++ )
        veci_push( &s->temp_clause, *i );
    begin = veci_begin( &s->temp_clause );
    end = begin + veci_size( &s->temp_clause );

    if (begin == end) 
        return false;

    //printlits(begin,end); printf("\n");
    // insertion sort
    maxvar = lit_var(*begin);
    for (i = begin + 1; i < end; i++){
        lit l = *i;
        maxvar = lit_var(l) > maxvar ? lit_var(l) : maxvar;
        for (j = i; j > begin && *(j-1) > l; j--)
            *j = *(j-1);
        *j = l;
    }
    sat_solver2_setnvars(s,maxvar+1);
//    sat_solver2_setnvars(s, lit_var(*(end-1))+1 );

    //printlits(begin,end); printf("\n");
//    values = s->assigns;

    // delete duplicates
    last = lit_Undef;
    for (i = j = begin; i < end; i++){
        //printf("lit: "L_LIT", value = %d\n", L_lit(*i), (lit_sign(*i) ? -values[lit_var(*i)] : values[lit_var(*i)]));
//        lbool sig = !lit_sign(*i); sig += sig - 1;
//        if (*i == lit_neg(last) || sig == values[lit_var(*i)])
        if (*i == lit_neg(last) || var_value(s, lit_var(*i)) == lit_sign(*i))
            return true;   // tautology
//        else if (*i != last && values[lit_var(*i)] == l_Undef)
        else if (*i != last && var_value(s, lit_var(*i)) == varX)
            last = *j++ = *i;
    }

    //printf("final: "); printlits(begin,j); printf("\n");

    if (j == begin)          // empty clause
        return false;

    if (j - begin == 1) // unit clause
        return enqueue(s,*begin,0);

    // create new clause
    c = clause_new(s,begin,j,0);

    s->stats.clauses++;
    s->stats.clauses_literals += j - begin;
    return true;
}


int sat_solver2_simplify(sat_solver2* s)
{
//    int type;
    int Counter = 0;

    assert(sat_solver2_dlevel(s) == 0);

    if (sat_solver2_propagate(s) != 0)
        return false;

    if (s->qhead == s->simpdb_assigns || s->simpdb_props > 0)
        return true;

/*
    for (type = 0; type < 2; type++){
        veci* cs  = type ? &s->learnts : &s->clauses;
        int*  cls = (int*)veci_begin(cs);

        int i, j;
        for (j = i = 0; i < veci_size(cs); i++){
            clause * c = get_clause(s,cls[i]);
            if (s->reasons[lit_var(*clause_begin(c))] != cls[i] &&
                clause_simplify(s,c) == l_True)
                clause_remove(s,c), Counter++;
            else
                cls[j++] = cls[i];
        }
        veci_resize(cs,j);
    }
*/
//printf( "Simplification removed %d clauses (out of %d)...\n", Counter, s->stats.clauses );

    s->simpdb_assigns = s->qhead;
    // (shouldn't depend on 'stats' really, but it will do for now)
    s->simpdb_props   = (int)(s->stats.clauses_literals + s->stats.learnts_literals);

    return true;
}

double luby2(double y, int x)
{
    int size, seq;
    for (size = 1, seq = 0; size < x+1; seq++, size = 2*size + 1);
    while (size-1 != x){
        size = (size-1) >> 1;
        seq--;
        x = x % size;
    }
    return pow(y, (double)seq);
} 

void luby2_test()
{
    int i;
    for ( i = 0; i < 20; i++ )
        printf( "%d ", (int)luby2(2,i) );
    printf( "\n" );
}

int sat_solver2_solve(sat_solver2* s, lit* begin, lit* end, ABC_INT64_T nConfLimit, ABC_INT64_T nInsLimit, ABC_INT64_T nConfLimitGlobal, ABC_INT64_T nInsLimitGlobal)
{
    int restart_iter = 0;
    ABC_INT64_T  nof_conflicts;
    ABC_INT64_T  nof_learnts   = sat_solver2_nclauses(s) / 3;
    lbool   status        = l_Undef;
//    lbool*  values        = s->assigns;
    lit*    i;

    // set the external limits
//    s->nCalls++;
//    s->nRestarts  = 0;
    s->nConfLimit = 0;
    s->nInsLimit  = 0;
    if ( nConfLimit )
        s->nConfLimit = s->stats.conflicts + nConfLimit;
    if ( nInsLimit )
//        s->nInsLimit = s->stats.inspects + nInsLimit;
        s->nInsLimit = s->stats.propagations + nInsLimit;
    if ( nConfLimitGlobal && (s->nConfLimit == 0 || s->nConfLimit > nConfLimitGlobal) )
        s->nConfLimit = nConfLimitGlobal;
    if ( nInsLimitGlobal && (s->nInsLimit == 0 || s->nInsLimit > nInsLimitGlobal) )
        s->nInsLimit = nInsLimitGlobal;

#ifndef SAT_USE_ANALYZE_FINAL

    //printf("solve: "); printlits(begin, end); printf("\n");
    for (i = begin; i < end; i++){
//        switch (lit_sign(*i) ? -values[lit_var(*i)] : values[lit_var(*i)]){
        switch (var_value(s, *i)) {
        case var1: // l_True: 
            break;
        case varX: // l_Undef
            assume(s, *i);
            if (sat_solver2_propagate(s) == NULL)
                break;
            // fallthrough
        case var0: // l_False 
            sat_solver2_canceluntil(s, 0);
            return l_False;
        }
    }
    s->root_level = sat_solver2_dlevel(s);

#endif

/*
    // Perform assumptions:
    root_level = assumps.size();
    for (int i = 0; i < assumps.size(); i++){
        Lit p = assumps[i];
        assert(var(p) < nVars());
        if (!assume(p)){
            GClause r = reason[var(p)];
            if (r != GClause_NULL){
                Clause* confl;
                if (r.isLit()){
                    confl = propagate_tmpbin;
                    (*confl)[1] = ~p;
                    (*confl)[0] = r.lit();
                }else
                    confl = r.clause();
                analyzeFinal(confl, true);
                conflict.push(~p);
            }else
                conflict.clear(),
                conflict.push(~p);
            cancelUntil(0);
            return false; }
        Clause* confl = propagate();
        if (confl != NULL){
            analyzeFinal(confl), assert(conflict.size() > 0);
            cancelUntil(0);
            return false; }
    }
    assert(root_level == decisionLevel());
*/

#ifdef SAT_USE_ANALYZE_FINAL
    // Perform assumptions:
    s->root_level = end - begin;
    for ( i = begin; i < end; i++ )
    {
        lit p = *i;
        assert(lit_var(p) < s->size);
        veci_push(&s->trail_lim,s->qtail);
        if (!enqueue(s,p,0))
        {
            clause * r = get_clause(s, s->reasons[lit_var(p)]);
            if (r != NULL)
            {
                clause* confl = r;
                sat_solver2_analyze_final(s, confl, 1);
                veci_push(&s->conf_final, lit_neg(p));
            }
            else
            {
                veci_resize(&s->conf_final,0);
                veci_push(&s->conf_final, lit_neg(p));
            }
            sat_solver2_canceluntil(s, 0);
            return l_False; 
        }
        else
        {
            clause* confl = sat_solver2_propagate(s);
            if (confl != NULL){
                sat_solver2_analyze_final(s, confl, 0);
                assert(s->conf_final.size > 0);
                sat_solver2_canceluntil(s, 0);
                return l_False; }
        }
    }
    assert(s->root_level == sat_solver2_dlevel(s));
#endif

//    s->nCalls2++;

    if (s->verbosity >= 1){
        printf("==================================[MINISAT]===================================\n");
        printf("| Conflicts |     ORIGINAL     |              LEARNT              | Progress |\n");
        printf("|           | Clauses Literals |   Limit Clauses Literals  Lit/Cl |          |\n");
        printf("==============================================================================\n");
    }

    while (status == l_Undef){
//        int nConfs = 0;
        double Ratio = (s->stats.learnts == 0)? 0.0 :
            s->stats.learnts_literals / (double)s->stats.learnts;
        if ( s->nRuntimeLimit && time(NULL) > s->nRuntimeLimit )
            break;

        if (s->verbosity >= 1)
        {
            printf("| %9.0f | %7.0f %8.0f | %7.0f %7.0f %8.0f %7.1f | %6.3f %% |\n", 
                (double)s->stats.conflicts,
                (double)s->stats.clauses, 
                (double)s->stats.clauses_literals,
                (double)nof_learnts, 
                (double)s->stats.learnts, 
                (double)s->stats.learnts_literals,
                Ratio,
                s->progress_estimate*100);
            fflush(stdout);
        }
        nof_conflicts = (ABC_INT64_T)( 100 * luby2(2, restart_iter++) );
//printf( "%d ", (int)nof_conflicts );
//        nConfs = s->stats.conflicts;
        status = sat_solver2_search(s, nof_conflicts, &nof_learnts);
//        if ( status == l_True )
//            printf( "%d ", s->stats.conflicts - nConfs );

//        nof_conflicts = nof_conflicts * 3 / 2; //*= 1.5;
//printf( "%d ", s->stats.conflicts  );
        // quit the loop if reached an external limit
        if ( s->nConfLimit && s->stats.conflicts > s->nConfLimit )
        {
//            printf( "Reached the limit on the number of conflicts (%d).\n", s->nConfLimit );
            break;
        }
//        if ( s->nInsLimit  && s->stats.inspects > s->nInsLimit )
        if ( s->nInsLimit  && s->stats.propagations > s->nInsLimit )
        {
//            printf( "Reached the limit on the number of implications (%d).\n", s->nInsLimit );
            break;
        }
        if ( s->nRuntimeLimit && time(NULL) > s->nRuntimeLimit )
            break;
    }
//printf( "\n" );
    if (s->verbosity >= 1)
        printf("==============================================================================\n");

    sat_solver2_canceluntil(s,0);
    return status;
}


int sat_solver2_nvars(sat_solver2* s)
{
    return s->size;
}


int sat_solver2_nclauses(sat_solver2* s)
{
    return (int)s->stats.clauses;
}


int sat_solver2_nconflicts(sat_solver2* s)
{
    return (int)s->stats.conflicts;
}

//=================================================================================================
// Sorting functions (sigh):

static inline void selectionsort(void** array, int size, int(*comp)(const void *, const void *))
{
    int     i, j, best_i;
    void*   tmp;

    for (i = 0; i < size-1; i++){
        best_i = i;
        for (j = i+1; j < size; j++){
            if (comp(array[j], array[best_i]) < 0)
                best_i = j;
        }
        tmp = array[i]; array[i] = array[best_i]; array[best_i] = tmp;
    }
}


static void sortrnd(void** array, int size, int(*comp)(const void *, const void *), double* seed)
{
    if (size <= 15)
        selectionsort(array, size, comp);

    else{
        void*       pivot = array[irand(seed, size)];
        void*       tmp;
        int         i = -1;
        int         j = size;

        for(;;){
            do i++; while(comp(array[i], pivot)<0);
            do j--; while(comp(pivot, array[j])<0);

            if (i >= j) break;

            tmp = array[i]; array[i] = array[j]; array[j] = tmp;
        }

        sortrnd(array    , i     , comp, seed);
        sortrnd(&array[i], size-i, comp, seed);
    }
}

void sat_solver2_sort(void** array, int size, int(*comp)(const void *, const void *))
{
//    int i;
    double seed = 91648253;
    sortrnd(array,size,comp,&seed);
//    for ( i = 1; i < size; i++ )
//        assert(comp(array[i-1], array[i])<0);
}
ABC_NAMESPACE_IMPL_END

