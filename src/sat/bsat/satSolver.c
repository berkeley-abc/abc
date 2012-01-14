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

#include "satSolver.h"
#include "satStore.h"

ABC_NAMESPACE_IMPL_START

#define SAT_USE_ANALYZE_FINAL

//=================================================================================================
// Debug:

//#define VERBOSEDEBUG

// For derivation output (verbosity level 2)
#define L_IND    "%-*d"
#define L_ind    sat_solver_dl(s)*2+2,sat_solver_dl(s)
#define L_LIT    "%sx%d"
#define L_lit(p) lit_sign(p)?"~":"", (lit_var(p))

// Just like 'assert()' but expression will be evaluated in the release version as well.
static inline void check(int expr) { assert(expr); }

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

static void sat_solver_sort(void** array, int size, int(*comp)(const void *, const void *));

//=================================================================================================
// Variable datatype + minor functions:

static const int var0  = 1;
static const int var1  = 0;
static const int varX  = 3;

struct varinfo_t
{
    unsigned val    :  2;  // variable value 
    unsigned pol    :  1;  // last polarity
    unsigned tag    :  1;  // conflict analysis tag
    unsigned lev    : 28;  // variable level
};

static inline int     var_level     (sat_solver* s, int v)            { return s->levels[v]; }
static inline int     var_value     (sat_solver* s, int v)            { return s->assigns[v]; }
static inline int     var_polar     (sat_solver* s, int v)            { return s->polarity[v]; }

static inline void    var_set_level (sat_solver* s, int v, int lev)   { s->levels[v] = lev;  }
static inline void    var_set_value (sat_solver* s, int v, int val)   { s->assigns[v] = val;  }
static inline void    var_set_polar (sat_solver* s, int v, int pol)   { s->polarity[v] = pol;  }

// variable tags
static inline int     var_tag       (sat_solver* s, int v)            { return s->tags[v]; }
static inline void    var_set_tag   (sat_solver* s, int v, int tag)   { 
    assert( tag > 0 && tag < 16 );
    if ( s->tags[v] == 0 )
        veci_push( &s->tagged, v );
    s->tags[v] = tag;                           
}
static inline void    var_add_tag   (sat_solver* s, int v, int tag)   { 
    assert( tag > 0 && tag < 16 );
    if ( s->tags[v] == 0 )
        veci_push( &s->tagged, v );
    s->tags[v] |= tag;                           
}
static inline void    solver2_clear_tags(sat_solver* s, int start)    { 
    int i, * tagged = veci_begin(&s->tagged);
    for (i = start; i < veci_size(&s->tagged); i++)
        s->tags[tagged[i]] = 0;
    veci_resize(&s->tagged,start);
}

int sat_solver_get_var_value(sat_solver* s, int v)
{
    if ( var_value(s, v) == var0 )
        return l_False;
    if ( var_value(s, v) == var1 )
        return l_True;
    if ( var_value(s, v) == varX )
        return l_Undef;
    assert( 0 );
    return 0;
}

//=================================================================================================
// Clause datatype + minor functions:

struct clause_t
{
    int size_learnt;
    lit lits[0];
};

static inline int      clause_nlits        (clause* c)             { return c->size_learnt >> 1;                       }
static inline lit*     clause_begin        (clause* c)             { return c->lits;                                   }
static inline int      clause_learnt       (clause* c)             { return c->size_learnt & 1;                        }
static inline float    clause_activity     (clause* c)             { return *((float*)&c->lits[c->size_learnt>>1]);    }
static inline unsigned clause_activity2    (clause* c)             { return *((unsigned*)&c->lits[c->size_learnt>>1]); }
static inline void     clause_setactivity  (clause* c, float a)    { *((float*)&c->lits[c->size_learnt>>1]) = a;       }
static inline void     clause_setactivity2 (clause* c, unsigned a) { *((unsigned*)&c->lits[c->size_learnt>>1]) = a;    }
static inline void     clause_print        (clause* c)             { 
    int i;
    printf( "{ " );
    for ( i = 0; i < clause_nlits(c); i++ )
        printf( "%d ", (clause_begin(c)[i] & 1)? -(clause_begin(c)[i] >> 1) : clause_begin(c)[i] >> 1 );
    printf( "}\n" );
}

static inline clause* clause_read( sat_solver* s, int h )          { return (clause *)Vec_RecEntryP(&s->Mem, h);       }
static inline int     clause_size( int nLits, int fLearnt )        { int a = nLits + fLearnt + 1; return a + (a & 1);  }

//=================================================================================================
// Encode literals in clause pointers:

static inline int     clause_from_lit (lit l)       { return l + l + 1;                            }
static inline int     clause_is_lit   (int h)       { return (h & 1);                              }
static inline lit     clause_read_lit (int h)       { return (lit)(h >> 1);                        }

//=================================================================================================
// Simple helpers:

static inline int     sat_solver_dl(sat_solver* s)                { return veci_size(&s->trail_lim); }
static inline veci*   sat_solver_read_wlist(sat_solver* s, lit l) { return &s->wlists[l];            }

//=================================================================================================
// Variable order functions:

static inline void order_update(sat_solver* s, int v) // updateorder
{
    int*    orderpos = s->orderpos;
    int*    heap     = veci_begin(&s->order);
    int     i        = orderpos[v];
    int     x        = heap[i];
    int     parent   = (i - 1) / 2;

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

static inline void order_assigned(sat_solver* s, int v) 
{
}

static inline void order_unassigned(sat_solver* s, int v) // undoorder
{
    int* orderpos = s->orderpos;
    if (orderpos[v] == -1){
        orderpos[v] = veci_size(&s->order);
        veci_push(&s->order,v);
        order_update(s,v);
//printf( "+%d ", v );
    }
}

static inline int  order_select(sat_solver* s, float random_var_freq) // selectvar
{
    int*      heap     = veci_begin(&s->order);
    int*      orderpos = s->orderpos;
    // Random decision:
    if (drand(&s->random_seed) < random_var_freq){
        int next = irand(&s->random_seed,s->size);
        assert(next >= 0 && next < s->size);
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
            int    i     = 0;
            int    child = 1;
            while (child < size){
                if (child+1 < size && s->activity[heap[child]] < s->activity[heap[child+1]])
                    child++;
                assert(child < size);
                if (s->activity[x] >= s->activity[heap[child]])
                    break;
                heap[i]           = heap[child];
                orderpos[heap[i]] = i;
                i                 = child;
                child             = 2 * child + 1;
            }
            heap[i]           = x;
            orderpos[heap[i]] = i;
        }
        if (var_value(s, next) == varX)
            return next;
    }
    return var_Undef;
}

//=================================================================================================
// Activity functions:

#ifdef USE_FLOAT_ACTIVITY

static inline void act_var_rescale(sat_solver* s)  {
    double* activity = s->activity;
    int i;
    for (i = 0; i < s->size; i++)
        activity[i] *= 1e-100;
    s->var_inc *= 1e-100;
}
static inline void act_clause_rescale(sat_solver* s) {
    static int Total = 0;
    clause** cs = (clause**)veci_begin(&s->learnts);
    int i, clk = clock();
    for (i = 0; i < veci_size(&s->learnts); i++){
        float a = clause_activity(cs[i]);
        clause_setactivity(cs[i], a * (float)1e-20);
    }
    s->cla_inc *= (float)1e-20;

    Total += clock() - clk;
    printf( "Rescaling...   Cla inc = %10.3f  Conf = %10d   ", s->cla_inc,  s->stats.conflicts );
    Abc_PrintTime( 1, "Time", Total );
}
static inline void act_var_bump(sat_solver* s, int v) {
    s->activity[v] += s->var_inc;
    if (s->activity[v] > 1e100)
        act_var_rescale(s);
    if (s->orderpos[v] != -1)
        order_update(s,v);
}
static inline void act_var_bump_global(sat_solver* s, int v) {
    if ( !s->pGlobalVars )
        return;
    s->activity[v] += (s->var_inc * 3.0 * s->pGlobalVars[v]);
    if (s->activity[v] > 1e100)
        act_var_rescale(s);
    if (s->orderpos[v] != -1)
        order_update(s,v);
}
static inline void act_var_bump_factor(sat_solver* s, int v) {
    if ( !s->factors )
        return;
    s->activity[v] += (s->var_inc * s->factors[v]);
    if (s->activity[v] > 1e100)
        act_var_rescale(s);
    if (s->orderpos[v] != -1)
        order_update(s,v);
}
static inline void act_clause_bump(sat_solver* s, clause *c) {
    float a = clause_activity(c) + s->cla_inc;
    clause_setactivity(c,a);
    if (a > 1e20) act_clause_rescale(s);
}
static inline void act_var_decay(sat_solver* s)    { s->var_inc *= s->var_decay; }
static inline void act_clause_decay(sat_solver* s) { s->cla_inc *= s->cla_decay; }

#else

static inline void act_var_rescale(sat_solver* s) {
    unsigned* activity = s->activity;
    int i;
    for (i = 0; i < s->size; i++)
        activity[i] >>= 19;
    s->var_inc >>= 19;
    s->var_inc = Abc_MaxInt( s->var_inc, (1<<4) );
}
/*
static inline void act_clause_rescale(sat_solver* s) {
    static int Total = 0;
    clause** cs = (clause**)vecp_begin(&s->learnts);
    int i, clk = clock();
    for (i = 0; i < vecp_size(&s->learnts); i++){
        unsigned a = clause_activity2(cs[i]);
        clause_setactivity2(cs[i], a >> 14);
    }
    s->cla_inc >>= 14;
    s->cla_inc = Abc_MaxInt( s->cla_inc, (1<<10) );

//    Total += clock() - clk;
//    printf( "Rescaling...   Cla inc = %5d  Conf = %10d   ", s->cla_inc,  s->stats.conflicts );
//    Abc_PrintTime( 1, "Time", Total );
}
*/
static inline void act_var_bump(sat_solver* s, int v) {
    s->activity[v] += s->var_inc;
    if (s->activity[v] & 0x80000000)
        act_var_rescale(s);
    if (s->orderpos[v] != -1)
        order_update(s,v);
}
static inline void act_var_bump_global(sat_solver* s, int v) {
    if ( !s->pGlobalVars )
        return;
    s->activity[v] += (int)(s->var_inc * 3 * s->pGlobalVars[v]);
    if (s->activity[v] & 0x80000000)
        act_var_rescale(s);
    if (s->orderpos[v] != -1)
        order_update(s,v);
}
static inline void act_var_bump_factor(sat_solver* s, int v) {
    if ( !s->factors )
        return;
    s->activity[v] += (int)(s->var_inc * s->factors[v]);
    if (s->activity[v] & 0x80000000)
        act_var_rescale(s);
    if (s->orderpos[v] != -1)
        order_update(s,v);
}
/*
static inline void act_clause_bump(sat_solver* s, clause*c) {
    unsigned a = clause_activity2(c) + s->cla_inc;
    clause_setactivity2(c,a);
    if (a & 0x80000000) 
        act_clause_rescale(s);
}
*/
static inline void act_var_decay(sat_solver* s)    { s->var_inc += (s->var_inc >>  4); }
//static inline void act_clause_decay(sat_solver* s) { s->cla_inc += (s->cla_inc >> 10); }

#endif


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

void sat_solver_sort(void** array, int size, int(*comp)(const void *, const void *))
{
//    int i;
    double seed = 91648253;
    sortrnd(array,size,comp,&seed);
//    for ( i = 1; i < size; i++ )
//        assert(comp(array[i-1], array[i])<0);
}

//=================================================================================================
// Clause functions:

/* pre: size > 1 && no variable occurs twice
 */
static int clause_create_new(sat_solver* s, lit* begin, lit* end, int learnt)
{
    int size;
    clause* c;
    int h, i;

    assert(end - begin > 1);
    assert(learnt >= 0 && learnt < 2);
    size           = end - begin;

    // do not allocate memory for the two-literal problem clause
    if ( size == 2 && !learnt )
    {
        veci_push(sat_solver_read_wlist(s,lit_neg(begin[0])),(clause_from_lit(begin[1])));
        veci_push(sat_solver_read_wlist(s,lit_neg(begin[1])),(clause_from_lit(begin[0])));
        return 0;
    }

    // create new clause
    h = Vec_RecAppend( &s->Mem, clause_size(size, learnt) );
    c = clause_read( s, h );
    assert( !(h & 1) );
    if ( s->hLearnts == -1 && learnt )
        s->hLearnts = h;
    c->size_learnt = (size << 1) | learnt;
    for (i = 0; i < size; i++)
        c->lits[i] = begin[i];
    if (learnt)
        *((float*)&c->lits[size]) = 0.0;

    assert(begin[0] >= 0);
    assert(begin[0] < s->size*2);
    assert(begin[1] >= 0);
    assert(begin[1] < s->size*2);

    assert(lit_neg(begin[0]) < s->size*2);
    assert(lit_neg(begin[1]) < s->size*2);

    //veci_push(sat_solver_read_wlist(s,lit_neg(begin[0])),c);
    //veci_push(sat_solver_read_wlist(s,lit_neg(begin[1])),c);
    veci_push(sat_solver_read_wlist(s,lit_neg(begin[0])),(size > 2 ? h : clause_from_lit(begin[1])));
    veci_push(sat_solver_read_wlist(s,lit_neg(begin[1])),(size > 2 ? h : clause_from_lit(begin[0])));

    return h;
}


//=================================================================================================
// Minor (solver) functions:

static inline int sat_solver_enqueue(sat_solver* s, lit l, int from)
{
    int v  = lit_var(l);
#ifdef VERBOSEDEBUG
    printf(L_IND"enqueue("L_LIT")\n", L_ind, L_lit(l));
#endif
    if (var_value(s, v) != varX)
        return var_value(s, v) == lit_sign(l);
    else{
        // New fact -- store it.
#ifdef VERBOSEDEBUG
        printf(L_IND"bind("L_LIT")\n", L_ind, L_lit(l));
#endif
        var_set_value(s, v, lit_sign(l));
        var_set_level(s, v, sat_solver_dl(s));
        s->reasons[v] = from;
        s->trail[s->qtail++] = l;
        order_assigned(s, v);
        return true;
    }
}


static inline int sat_solver_assume(sat_solver* s, lit l){
    assert(s->qtail == s->qhead);
    assert(var_value(s, lit_var(l)) == varX);
#ifdef VERBOSEDEBUG
    printf(L_IND"assume("L_LIT")  ", L_ind, L_lit(l));
    printf( "act = %.20f\n", s->activity[lit_var(l)] );
#endif
    veci_push(&s->trail_lim,s->qtail);
    return sat_solver_enqueue(s,l,0);
}


static void sat_solver_canceluntil(sat_solver* s, int level) {
    int      bound;
    int      lastLev;
    int      c;
    
    if (sat_solver_dl(s) <= level)
        return;

    bound   = (veci_begin(&s->trail_lim))[level];
    lastLev = (veci_begin(&s->trail_lim))[veci_size(&s->trail_lim)-1];

    ////////////////////////////////////////
    // added to cancel all assignments
//    if ( level == -1 )
//        bound = 0;
    ////////////////////////////////////////

    for (c = s->qtail-1; c >= bound; c--) {
        int     x  = lit_var(s->trail[c]);
        var_set_value(s, x, varX);
        s->reasons[x] = 0;
        if ( c < lastLev )
            var_set_polar( s, x, !lit_sign(s->trail[c]) );
    }

    for (c = s->qhead-1; c >= bound; c--)
        order_unassigned(s,lit_var(s->trail[c]));

    s->qhead = s->qtail = bound;
    veci_resize(&s->trail_lim,level);
}

static void sat_solver_record(sat_solver* s, veci* cls)
{
    lit*    begin = veci_begin(cls);
    lit*    end   = begin + veci_size(cls);
    int     h     = (veci_size(cls) > 1) ? clause_create_new(s,begin,end,1) : 0;
    sat_solver_enqueue(s,*begin,h);

    ///////////////////////////////////
    // add clause to internal storage
    if ( s->pStore )
    {
        int RetValue = Sto_ManAddClause( (Sto_Man_t *)s->pStore, begin, end );
        assert( RetValue );
    }
    ///////////////////////////////////

    assert(veci_size(cls) > 0);

    if (h != 0) {
//        veci_push(&s->learnts,c);
//        act_clause_bump(s,c);
        s->stats.learnts++;
        s->stats.learnts_literals += veci_size(cls);
    }
}


static double sat_solver_progress(sat_solver* s)
{
    int     i;
    double  progress = 0;
    double  F        = 1.0 / s->size;
    for (i = 0; i < s->size; i++)
        if (var_value(s, i) != varX)
            progress += pow(F, var_level(s, i));
    return progress / s->size;
}

//=================================================================================================
// Major methods:

static int sat_solver_lit_removable(sat_solver* s, int x, int minl)
{
    int      top     = veci_size(&s->tagged);

    assert(s->reasons[x] != 0);
    veci_resize(&s->stack,0);
    veci_push(&s->stack,x);

    while (veci_size(&s->stack)){
        int v = veci_pop(&s->stack);
        assert(s->reasons[v] != 0);
        if (clause_is_lit(s->reasons[v])){
            v = lit_var(clause_read_lit(s->reasons[v]));
            if (!var_tag(s,v) && var_level(s, v)){
                if (s->reasons[v] != 0 && ((1 << (var_level(s, v) & 31)) & minl)){
                    veci_push(&s->stack,v);
                    var_set_tag(s, v, 1);
                }else{
                    solver2_clear_tags(s, top);
                    return 0;
                }
            }
        }else{
            clause* c = clause_read(s, s->reasons[v]);
            lit* lits = clause_begin(c);
            int  i;
            for (i = 1; i < clause_nlits(c); i++){
                int v = lit_var(lits[i]);
                if (!var_tag(s,v) && var_level(s, v)){
                    if (s->reasons[v] != 0 && ((1 << (var_level(s, v) & 31)) & minl)){
                        veci_push(&s->stack,lit_var(lits[i]));
                        var_set_tag(s, v, 1);
                    }else{
                        solver2_clear_tags(s, top);
                        return 0;
                    }
                }
            }
        }
    }
    return 1;
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

static void sat_solver_analyze_final(sat_solver* s, int hConf, int skip_first)
{
    clause* conf = clause_read(s, hConf);
    int i, j, start;
    veci_resize(&s->conf_final,0);
    if ( s->root_level == 0 )
        return;
    assert( veci_size(&s->tagged) == 0 );
//    assert( s->tags[lit_var(p)] == l_Undef );
//    s->tags[lit_var(p)] = l_True;
    for (i = skip_first ? 1 : 0; i < clause_nlits(conf); i++)
    {
        int x = lit_var(clause_begin(conf)[i]);
        if (var_level(s, x) > 0)
            var_set_tag(s, x, 1);
    }

    start = (s->root_level >= veci_size(&s->trail_lim))? s->qtail-1 : (veci_begin(&s->trail_lim))[s->root_level];
    for (i = start; i >= (veci_begin(&s->trail_lim))[0]; i--){
        int x = lit_var(s->trail[i]);
        if (var_tag(s,x)){
            if (s->reasons[x] == 0){
                assert(var_level(s, x) > 0);
                veci_push(&s->conf_final,lit_neg(s->trail[i]));
            }else{
                if (clause_is_lit(s->reasons[x])){
                    lit q = clause_read_lit(s->reasons[x]);
                    assert(lit_var(q) >= 0 && lit_var(q) < s->size);
                    if (var_level(s, lit_var(q)) > 0)
                        var_set_tag(s, lit_var(q), 1);
                }
                else{
                    clause* c = clause_read(s, s->reasons[x]);
                    int* lits = clause_begin(c);
                    for (j = 1; j < clause_nlits(c); j++)
                        if (var_level(s, lit_var(lits[j])) > 0)
                            var_set_tag(s, lit_var(lits[j]), 1);
                }
            }
        }
    }
    solver2_clear_tags(s,0);
}

#endif


static void sat_solver_analyze(sat_solver* s, int h, veci* learnt)
{
    lit*     trail   = s->trail;
    int      cnt     = 0;
    lit      p       = lit_Undef;
    int      ind     = s->qtail-1;
    lit*     lits;
    int      i, j, minl;
    veci_push(learnt,lit_Undef);
    do{
        assert(h != 0);
        if (clause_is_lit(h)){
            int x = lit_var(clause_read_lit(h));
            if (var_tag(s, x) == 0 && var_level(s, x) > 0){
                var_set_tag(s, x, 1);
                act_var_bump(s,x);
                if (var_level(s, x) == sat_solver_dl(s))
                    cnt++;
                else
                    veci_push(learnt,clause_read_lit(h));
            }
        }else{
            clause* c = clause_read(s, h);
//            if (clause_learnt(c))
//                act_clause_bump(s,c);
            lits = clause_begin(c);
            //printlits(lits,lits+clause_nlits(c)); printf("\n");
            for (j = (p == lit_Undef ? 0 : 1); j < clause_nlits(c); j++){
                int x = lit_var(lits[j]);
                if (var_tag(s, x) == 0 && var_level(s, x) > 0){
                    var_set_tag(s, x, 1);
                    act_var_bump(s,x);
                    if (var_level(s,x) == sat_solver_dl(s))
                        cnt++;
                    else
                        veci_push(learnt,lits[j]);
                }
            }
        }

        while ( !var_tag(s, lit_var(trail[ind--])) );

        p = trail[ind+1];
        h = s->reasons[lit_var(p)];
        cnt--;

    }while (cnt > 0);

    *veci_begin(learnt) = lit_neg(p);

    lits = veci_begin(learnt);
    minl = 0;
    for (i = 1; i < veci_size(learnt); i++){
        int lev = var_level(s, lit_var(lits[i]));
        minl    |= 1 << (lev & 31);
    }

    // simplify (full)
    for (i = j = 1; i < veci_size(learnt); i++){
        if (s->reasons[lit_var(lits[i])] == 0 || !sat_solver_lit_removable(s,lit_var(lits[i]),minl))
            lits[j++] = lits[i];
    }

    // update size of learnt + statistics
    veci_resize(learnt,j);
    s->stats.tot_literals += j;

    // clear tags
    solver2_clear_tags(s,0);

#ifdef DEBUG
    for (i = 0; i < s->size; i++)
        assert(!var_tag(s, i));
#endif

#ifdef VERBOSEDEBUG
    printf(L_IND"Learnt {", L_ind);
    for (i = 0; i < veci_size(learnt); i++) printf(" "L_LIT, L_lit(lits[i]));
#endif
    if (veci_size(learnt) > 1){
        int max_i = 1;
        int max   = var_level(s, lit_var(lits[1]));
        lit tmp;

        for (i = 2; i < veci_size(learnt); i++)
            if (var_level(s, lit_var(lits[i])) > max){
                max   = var_level(s, lit_var(lits[i]));
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


int sat_solver_propagate(sat_solver* s)
{
    int     hConfl = 0;
    lit*    lits;
    lit false_lit;

    //printf("sat_solver_propagate\n");
    while (hConfl == 0 && s->qtail - s->qhead > 0){
        lit   p     = s->trail[s->qhead++];
        veci* ws    = sat_solver_read_wlist(s,p);
        int*  begin = veci_begin(ws);
        int*  end   = begin + veci_size(ws);
        int*i, *j;

        s->stats.propagations++;
        s->simpdb_props--;

        //printf("checking lit %d: "L_LIT"\n", veci_size(ws), L_lit(p));
        for (i = j = begin; i < end; ){
            if (clause_is_lit(*i)){

                int Lit = clause_read_lit(*i);
                if (var_value(s, lit_var(Lit)) == lit_sign(Lit)){
                    *j++ = *i++;
                    continue;
                }

                *j++ = *i;
                if (!sat_solver_enqueue(s,clause_read_lit(*i),clause_from_lit(p))){
                    hConfl = s->hBinary;
                    (clause_begin(s->binary))[1] = lit_neg(p);
                    (clause_begin(s->binary))[0] = clause_read_lit(*i++);
                    // Copy the remaining watches:
                    while (i < end)
                        *j++ = *i++;
                }
            }else{

                clause* c = clause_read(s,*i);
                lits = clause_begin(c);

                // Make sure the false literal is data[1]:
                false_lit = lit_neg(p);
                if (lits[0] == false_lit){
                    lits[0] = lits[1];
                    lits[1] = false_lit;
                }
                assert(lits[1] == false_lit);

                // If 0th watch is true, then clause is already satisfied.
                if (var_value(s, lit_var(lits[0])) == lit_sign(lits[0]))
                    *j++ = *i;
                else{
                    // Look for new watch:
                    lit* stop = lits + clause_nlits(c);
                    lit* k;
                    for (k = lits + 2; k < stop; k++){
                        if (var_value(s, lit_var(*k)) != !lit_sign(*k)){
                            lits[1] = *k;
                            *k = false_lit;
                            veci_push(sat_solver_read_wlist(s,lit_neg(lits[1])),*i);
                            goto next; }
                    }

                    *j++ = *i;
                    // Clause is unit under assignment:
                    if (!sat_solver_enqueue(s,lits[0], *i)){
                        hConfl = *i++;
                        // Copy the remaining watches:
                        while (i < end)
                            *j++ = *i++;
                    }
                }
            }
        next:
            i++;
        }

        s->stats.inspects += j - veci_begin(ws);
        veci_resize(ws,j - veci_begin(ws));
    }

    return hConfl;
}

//=================================================================================================
// External solver functions:

sat_solver* sat_solver_new(void)
{
    sat_solver* s = (sat_solver*)ABC_CALLOC( char, sizeof(sat_solver));

    Vec_RecAlloc_(&s->Mem);
    s->hLearnts = -1;
    s->hBinary = Vec_RecAppend( &s->Mem, clause_size(2, 0) );
    s->binary = clause_read( s, s->hBinary );
    s->binary->size_learnt = (2 << 1);

    // initialize vectors
    veci_new(&s->order);
    veci_new(&s->trail_lim);
    veci_new(&s->tagged);
    veci_new(&s->stack);
//    veci_new(&s->model);
    veci_new(&s->act_vars);
    veci_new(&s->temp_clause);
    veci_new(&s->conf_final);

    // initialize arrays
    s->wlists    = 0;
    s->activity  = 0;
    s->orderpos  = 0;
    s->reasons   = 0;
    s->trail     = 0;

    // initialize other vars
    s->size                   = 0;
    s->cap                    = 0;
    s->qhead                  = 0;
    s->qtail                  = 0;
#ifdef USE_FLOAT_ACTIVITY
    s->var_inc                = 1;
    s->cla_inc                = 1;
    s->var_decay              = (float)(1 / 0.95  );
    s->cla_decay              = (float)(1 / 0.999 );
#else
    s->var_inc                = (1 <<  5);
    s->cla_inc                = (1 << 11);
#endif
    s->root_level             = 0;
    s->simpdb_assigns         = 0;
    s->simpdb_props           = 0;
    s->random_seed            = 91648253;
    s->progress_estimate      = 0;
//    s->binary                 = (clause*)ABC_ALLOC( char, sizeof(clause) + sizeof(lit)*2);
//    s->binary->size_learnt    = (2 << 1);
    s->verbosity              = 0;

    s->stats.starts           = 0;
    s->stats.decisions        = 0;
    s->stats.propagations     = 0;
    s->stats.inspects         = 0;
    s->stats.conflicts        = 0;
    s->stats.clauses          = 0;
    s->stats.clauses_literals = 0;
    s->stats.learnts          = 0;
    s->stats.learnts_literals = 0;
    s->stats.tot_literals     = 0;
    return s;
}

void sat_solver_setnvars(sat_solver* s,int n)
{
    int var;

    if (s->cap < n){
        int old_cap = s->cap;
        while (s->cap < n) s->cap = s->cap*2+1;

        s->wlists    = ABC_REALLOC(veci,   s->wlists,   s->cap*2);
//        s->vi        = ABC_REALLOC(varinfo,s->vi,       s->cap);
        s->levels    = ABC_REALLOC(int,    s->levels,   s->cap);
        s->assigns   = ABC_REALLOC(char,   s->assigns,  s->cap);
        s->polarity  = ABC_REALLOC(char,   s->polarity, s->cap);
        s->tags      = ABC_REALLOC(char,   s->tags,     s->cap);
#ifdef USE_FLOAT_ACTIVITY
        s->activity  = ABC_REALLOC(double,   s->activity, s->cap);
#else
        s->activity  = ABC_REALLOC(unsigned, s->activity, s->cap);
#endif
        if ( s->factors )
        s->factors   = ABC_REALLOC(double, s->factors,  s->cap);
        s->orderpos  = ABC_REALLOC(int,    s->orderpos, s->cap);
        s->reasons   = ABC_REALLOC(int,    s->reasons,  s->cap);
        s->trail     = ABC_REALLOC(lit,    s->trail,    s->cap);
        s->model     = ABC_REALLOC(int,    s->model,    s->cap);
        memset( s->wlists + 2*old_cap, 0, 2*(s->cap-old_cap)*sizeof(veci) );
    } 

    for (var = s->size; var < n; var++){
        assert(!s->wlists[2*var].size);
        assert(!s->wlists[2*var+1].size);
        if ( s->wlists[2*var].ptr == NULL )
            veci_new(&s->wlists[2*var]);
        if ( s->wlists[2*var+1].ptr == NULL )
            veci_new(&s->wlists[2*var+1]);
#ifdef USE_FLOAT_ACTIVITY
        s->activity[var] = 0;
#else
        s->activity[var] = (1<<10);
#endif
        if ( s->factors )
        s->factors [var] = 0;
//        *((int*)s->vi + var) = 0; s->vi[var].val = varX;
        s->levels  [var] = 0;
        s->assigns [var] = varX;
        s->polarity[var] = 0;
        s->tags    [var] = 0;
        s->orderpos[var] = veci_size(&s->order);
        s->reasons [var] = 0;
        s->model   [var] = 0; 
        
        /* does not hold because variables enqueued at top level will not be reinserted in the heap
           assert(veci_size(&s->order) == var); 
         */
        veci_push(&s->order,var);
        order_update(s, var);
    }

    s->size = n > s->size ? n : s->size;
}

void sat_solver_delete(sat_solver* s)
{
    Vec_RecFree_( &s->Mem );

    // delete vectors
    veci_delete(&s->order);
    veci_delete(&s->trail_lim);
    veci_delete(&s->tagged);
    veci_delete(&s->stack);
//    veci_delete(&s->model);
    veci_delete(&s->act_vars);
    veci_delete(&s->temp_clause);
    veci_delete(&s->conf_final);

    // delete arrays
    if (s->reasons != 0){
        int i;
        for (i = 0; i < s->cap*2; i++)
            veci_delete(&s->wlists[i]);
        ABC_FREE(s->wlists   );
//        ABC_FREE(s->vi       );
        ABC_FREE(s->levels   );
        ABC_FREE(s->assigns  );
        ABC_FREE(s->polarity );
        ABC_FREE(s->tags     );
        ABC_FREE(s->activity );
        ABC_FREE(s->factors  );
        ABC_FREE(s->orderpos );
        ABC_FREE(s->reasons  );
        ABC_FREE(s->trail    );
        ABC_FREE(s->model    );
    }

    sat_solver_store_free(s);
    ABC_FREE(s);
}

void sat_solver_rollback( sat_solver* s )
{
    int i;
    Vec_RecRestart( &s->Mem );

    s->hLearnts = -1;
    s->hBinary = Vec_RecAppend( &s->Mem, clause_size(2, 0) );
    s->binary = clause_read( s, s->hBinary );
    s->binary->size_learnt = (2 << 1);

    veci_resize(&s->trail_lim, 0);
    veci_resize(&s->order, 0);
    for ( i = 0; i < s->size*2; i++ )
        s->wlists[i].size = 0;

    // initialize other vars
    s->size                   = 0;
//    s->cap                    = 0;
    s->qhead                  = 0;
    s->qtail                  = 0;
#ifdef USE_FLOAT_ACTIVITY
    s->var_inc                = 1;
    s->cla_inc                = 1;
    s->var_decay              = (float)(1 / 0.95  );
    s->cla_decay              = (float)(1 / 0.999 );
#else
    s->var_inc                = (1 <<  5);
    s->cla_inc                = (1 << 11);
#endif
    s->root_level             = 0;
    s->simpdb_assigns         = 0;
    s->simpdb_props           = 0;
    s->random_seed            = 91648253;
    s->progress_estimate      = 0;
    s->verbosity              = 0;

    s->stats.starts           = 0;
    s->stats.decisions        = 0;
    s->stats.propagations     = 0;
    s->stats.inspects         = 0;
    s->stats.conflicts        = 0;
    s->stats.clauses          = 0;
    s->stats.clauses_literals = 0;
    s->stats.learnts          = 0;
    s->stats.learnts_literals = 0;
    s->stats.tot_literals     = 0;
}

/*
static void clause_remove(sat_solver* s, clause* c)
{
    lit* lits = clause_begin(c);
    assert(lit_neg(lits[0]) < s->size*2);
    assert(lit_neg(lits[1]) < s->size*2);

    //veci_remove(sat_solver_read_wlist(s,lit_neg(lits[0])),(void*)c);
    //veci_remove(sat_solver_read_wlist(s,lit_neg(lits[1])),(void*)c);

    assert(lits[0] < s->size*2);
    veci_remove(sat_solver_read_wlist(s,lit_neg(lits[0])),(clause_nlits(c) > 2 ? c : clause_from_lit(lits[1])));
    veci_remove(sat_solver_read_wlist(s,lit_neg(lits[1])),(clause_nlits(c) > 2 ? c : clause_from_lit(lits[0])));

    if (clause_learnt(c)){
        s->stats.learnts--;
        s->stats.learnts_literals -= clause_nlits(c);
    }else{
        s->stats.clauses--;
        s->stats.clauses_literals -= clause_nlits(c);
    }
}

static lbool clause_simplify(sat_solver* s, clause* c)
{
    lit*   lits   = clause_begin(c);
    int i;

    assert(sat_solver_dl(s) == 0);

    for (i = 0; i < clause_nlits(c); i++){
        lbool sig = !lit_sign(lits[i]); sig += sig - 1;
        if (s->assignss[lit_var(lits[i])] == sig)
            return l_True;
    }
    return l_False;
}
*/

int sat_solver_simplify(sat_solver* s)
{
//    clause** reasons;
//    int type;
    assert(sat_solver_dl(s) == 0);

    if (sat_solver_propagate(s) != 0)
        return false;

    if (s->qhead == s->simpdb_assigns || s->simpdb_props > 0)
        return true;
/*
    reasons = s->reasons;
    for (type = 0; type < 2; type++){
        vecp*    cs  = type ? &s->learnts : &s->clauses;
        clause** cls = (clause**)vecp_begin(cs);

        int i, j;
        for (j = i = 0; i < vecp_size(cs); i++){
            if (reasons[lit_var(*clause_begin(cls[i]))] != cls[i] &&
                clause_simplify(s,cls[i]) == l_True)
                clause_remove(s,cls[i]);
            else
                cls[j++] = cls[i];
        }
        vecp_resize(cs,j);
    }
*/
    s->simpdb_assigns = s->qhead;
    // (shouldn't depend on 'stats' really, but it will do for now)
    s->simpdb_props   = (int)(s->stats.clauses_literals + s->stats.learnts_literals);
    return true;
}


/*
static int clause_cmp (const void* x, const void* y) {
    return clause_nlits((clause*)x) > 2 && (clause_nlits((clause*)y) == 2 || clause_activity((clause*)x) < clause_activity((clause*)y)) ? -1 : 1; }
void sat_solver_reducedb(sat_solver* s)
{
    int      i, j;
    double   extra_lim = s->cla_inc / veci_size(&s->learnts); // Remove any clause below this activity
    clause** learnts = (clause**)veci_begin(&s->learnts);
    clause** reasons = s->reasons;

    sat_solver_sort(veci_begin(&s->learnts), veci_size(&s->learnts), &clause_cmp);

    for (i = j = 0; i < veci_size(&s->learnts) / 2; i++){
        if (clause_nlits(learnts[i]) > 2 && reasons[lit_var(*clause_begin(learnts[i]))] != learnts[i])
            clause_remove(s,learnts[i]);
        else
            learnts[j++] = learnts[i];
    }
    for (; i < veci_size(&s->learnts); i++){
        if (clause_nlits(learnts[i]) > 2 && reasons[lit_var(*clause_begin(learnts[i]))] != learnts[i] && clause_activity(learnts[i]) < extra_lim)
            clause_remove(s,learnts[i]);
        else
            learnts[j++] = learnts[i];
    }
    veci_resize(&s->learnts,j);
}
*/

int sat_solver_addclause(sat_solver* s, lit* begin, lit* end)
{
    lit *i,*j;
    int maxvar;
    lit last;
    assert( begin < end );

    veci_resize( &s->temp_clause, 0 );
    for ( i = begin; i < end; i++ )
        veci_push( &s->temp_clause, *i );
    begin = veci_begin( &s->temp_clause );
    end = begin + veci_size( &s->temp_clause );

    // insertion sort
    maxvar = lit_var(*begin);
    for (i = begin + 1; i < end; i++){
        lit l = *i;
        maxvar = lit_var(l) > maxvar ? lit_var(l) : maxvar;
        for (j = i; j > begin && *(j-1) > l; j--)
            *j = *(j-1);
        *j = l;
    }
    sat_solver_setnvars(s,maxvar+1);

    ///////////////////////////////////
    // add clause to internal storage
    if ( s->pStore )
    {
        int RetValue = Sto_ManAddClause( (Sto_Man_t *)s->pStore, begin, end );
        assert( RetValue );
    }
    ///////////////////////////////////

    // delete duplicates
    last = lit_Undef;
    for (i = j = begin; i < end; i++){
        //printf("lit: "L_LIT", value = %d\n", L_lit(*i), (lit_sign(*i) ? -s->assignss[lit_var(*i)] : s->assignss[lit_var(*i)]));
        if (*i == lit_neg(last) || var_value(s, lit_var(*i)) == lit_sign(*i))
            return true;   // tautology
        else if (*i != last && var_value(s, lit_var(*i)) == varX)
            last = *j++ = *i;
    }
//    j = i;

    if (j == begin)          // empty clause
        return false;

    if (j - begin == 1) // unit clause
        return sat_solver_enqueue(s,*begin,0);

    // create new clause
    clause_create_new(s,begin,j,0);

    s->stats.clauses++;
    s->stats.clauses_literals += j - begin;
    return true;
}


double luby(double y, int x)
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

void luby_test()
{
    int i;
    for ( i = 0; i < 20; i++ )
        printf( "%d ", (int)luby(2,i) );
    printf( "\n" );
}

static lbool sat_solver_search(sat_solver* s, ABC_INT64_T nof_conflicts, ABC_INT64_T nof_learnts)
{
    double  var_decay       = 0.95;
    double  clause_decay    = 0.999;
    double  random_var_freq = s->fNotUseRandom ? 0.0 : 0.02;

    ABC_INT64_T  conflictC       = 0;
    veci    learnt_clause;
    int     i;

    assert(s->root_level == sat_solver_dl(s));

    s->nRestarts++;
    s->stats.starts++;
//    s->var_decay = (float)(1 / var_decay   );  // move this to sat_solver_new()
//    s->cla_decay = (float)(1 / clause_decay);  // move this to sat_solver_new()
//    veci_resize(&s->model,0);
    veci_new(&learnt_clause);

    // use activity factors in every even restart
    if ( (s->nRestarts & 1) && veci_size(&s->act_vars) > 0 )
//    if ( veci_size(&s->act_vars) > 0 )
        for ( i = 0; i < s->act_vars.size; i++ )
            act_var_bump_factor(s, s->act_vars.ptr[i]);

    // use activity factors in every restart
    if ( s->pGlobalVars && veci_size(&s->act_vars) > 0 )
        for ( i = 0; i < s->act_vars.size; i++ )
            act_var_bump_global(s, s->act_vars.ptr[i]);

    for (;;){
        int hConfl = sat_solver_propagate(s);
        if (hConfl != 0){
            // CONFLICT
            int blevel;

#ifdef VERBOSEDEBUG
            printf(L_IND"**CONFLICT**\n", L_ind);
#endif
            s->stats.conflicts++; conflictC++;
            if (sat_solver_dl(s) == s->root_level){
#ifdef SAT_USE_ANALYZE_FINAL
                sat_solver_analyze_final(s, hConfl, 0);
#endif
                veci_delete(&learnt_clause);
                return l_False;
            }

            veci_resize(&learnt_clause,0);
            sat_solver_analyze(s, hConfl, &learnt_clause);
            blevel = veci_size(&learnt_clause) > 1 ? var_level(s, lit_var(veci_begin(&learnt_clause)[1])) : s->root_level;
            blevel = s->root_level > blevel ? s->root_level : blevel;
            sat_solver_canceluntil(s,blevel);
            sat_solver_record(s,&learnt_clause);
#ifdef SAT_USE_ANALYZE_FINAL
//            if (learnt_clause.size() == 1) level[var(learnt_clause[0])] = 0;    // (this is ugly (but needed for 'analyzeFinal()') -- in future versions, we will backtrack past the 'root_level' and redo the assumptions)
            if ( learnt_clause.size == 1 ) 
                var_set_level(s, lit_var(learnt_clause.ptr[0]), 0);
#endif
            act_var_decay(s);
//            act_clause_decay(s);

        }else{
            // NO CONFLICT
            int next;
 
            if (nof_conflicts >= 0 && conflictC >= nof_conflicts){
                // Reached bound on number of conflicts:
                s->progress_estimate = sat_solver_progress(s);
                sat_solver_canceluntil(s,s->root_level);
                veci_delete(&learnt_clause);
                return l_Undef; }

            if ( (s->nConfLimit && s->stats.conflicts > s->nConfLimit) ||
                 (s->nInsLimit  && s->stats.propagations > s->nInsLimit) )
            {
                // Reached bound on number of conflicts:
                s->progress_estimate = sat_solver_progress(s);
                sat_solver_canceluntil(s,s->root_level);
                veci_delete(&learnt_clause);
                return l_Undef; 
            }

            if (sat_solver_dl(s) == 0 && !s->fSkipSimplify)
                // Simplify the set of problem clauses:
                sat_solver_simplify(s);

//            if (nof_learnts >= 0 && veci_size(&s->learnts) - s->qtail >= nof_learnts)
                // Reduce the set of learnt clauses:
//                sat_solver_reducedb(s);

            // New variable decision:
            s->stats.decisions++;
            next = order_select(s,(float)random_var_freq);

            if (next == var_Undef){
                // Model found:
                int i;
                for (i = 0; i < s->size; i++)
                    s->model[i] = (var_value(s,i)==var1 ? l_True : l_False);
                sat_solver_canceluntil(s,s->root_level);
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
                sat_solver_assume(s,toLit(next));
            else
                sat_solver_assume(s,lit_neg(toLit(next)));
        }
    }

    return l_Undef; // cannot happen
}

int sat_solver_solve(sat_solver* s, lit* begin, lit* end, ABC_INT64_T nConfLimit, ABC_INT64_T nInsLimit, ABC_INT64_T nConfLimitGlobal, ABC_INT64_T nInsLimitGlobal)
{
    int restart_iter = 0;
    ABC_INT64_T  nof_conflicts;
    ABC_INT64_T  nof_learnts   = sat_solver_nclauses(s) / 3;
    lbool   status        = l_Undef;
    lit*    i;

    ////////////////////////////////////////////////
    if ( s->fSolved )
    {
        if ( s->pStore )
        {
            int RetValue = Sto_ManAddClause( (Sto_Man_t *)s->pStore, NULL, NULL );
            assert( RetValue );
        }
        return l_False;
    }
    ////////////////////////////////////////////////

    // set the external limits
    s->nCalls++;
    s->nRestarts  = 0;
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
//        switch (lit_sign(*i) ? -s->assignss[lit_var(*i)] : s->assignss[lit_var(*i)]){
        switch (var_value(s, *i)) {
        case var1: // l_True: 
            break;
        case varX: // l_Undef
            sat_solver_assume(s, *i);
            if (sat_solver_propagate(s) == 0)
                break;
            // fallthrough
        case var0: // l_False 
            sat_solver_canceluntil(s, 0);
            return l_False;
        }
    }
    s->root_level = sat_solver_dl(s);

#endif

/*
    // Perform assumptions:
    root_level = assumps.size();
    for (int i = 0; i < assumps.size(); i++){
        Lit p = assumps[i];
        assert(var(p) < nVars());
        if (!sat_solver_assume(p)){
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
        if (!sat_solver_enqueue(s,p,0))
        {
            int h = s->reasons[lit_var(p)];
            if (h)
            {
                if (clause_is_lit(h))
                {
                    (clause_begin(s->binary))[1] = lit_neg(p);
                    (clause_begin(s->binary))[0] = clause_read_lit(h);
                    h = s->hBinary;
                }
                sat_solver_analyze_final(s, h, 1);
                veci_push(&s->conf_final, lit_neg(p));
            }
            else
            {
                veci_resize(&s->conf_final,0);
                veci_push(&s->conf_final, lit_neg(p));
                // the two lines below are a bug fix by Siert Wieringa 
                if (var_level(s, lit_var(p)) > 0)
                    veci_push(&s->conf_final, p);
            }
            sat_solver_canceluntil(s, 0);
            return l_False; 
        }
        else
        {
            int fConfl = sat_solver_propagate(s);
            if (fConfl){
                sat_solver_analyze_final(s, fConfl, 0);
                assert(s->conf_final.size > 0);
                sat_solver_canceluntil(s, 0);
                return l_False; }
        }
    }
    assert(s->root_level == sat_solver_dl(s));
#endif

    s->nCalls2++;

    if (s->verbosity >= 1){
        printf("==================================[MINISAT]===================================\n");
        printf("| Conflicts |     ORIGINAL     |              LEARNT              | Progress |\n");
        printf("|           | Clauses Literals |   Limit Clauses Literals  Lit/Cl |          |\n");
        printf("==============================================================================\n");
    }

    while (status == l_Undef){
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
//                (double)nof_learnts, 
                (double)0, 
                (double)s->stats.learnts, 
                (double)s->stats.learnts_literals,
                Ratio,
                s->progress_estimate*100);
            fflush(stdout);
        }
        nof_conflicts = (ABC_INT64_T)( 100 * luby(2, restart_iter++) );
        status = sat_solver_search(s, nof_conflicts, nof_learnts);
        nof_learnts    = nof_learnts * 11 / 10; //*= 1.1;
        // quit the loop if reached an external limit
        if ( s->nConfLimit && s->stats.conflicts > s->nConfLimit )
            break;
        if ( s->nInsLimit  && s->stats.propagations > s->nInsLimit )
            break;
        if ( s->nRuntimeLimit && time(NULL) > s->nRuntimeLimit )
            break;
    }
    if (s->verbosity >= 1)
        printf("==============================================================================\n");

    sat_solver_canceluntil(s,0);

    ////////////////////////////////////////////////
    if ( status == l_False && s->pStore )
    {
        int RetValue = Sto_ManAddClause( (Sto_Man_t *)s->pStore, NULL, NULL );
        assert( RetValue );
    }
    ////////////////////////////////////////////////
    return status;
}


int sat_solver_nvars(sat_solver* s)
{
    return s->size;
}


int sat_solver_nclauses(sat_solver* s)
{
    return s->stats.clauses;
}


int sat_solver_nconflicts(sat_solver* s)
{
    return (int)s->stats.conflicts;
}

//=================================================================================================
// Clause storage functions:

void sat_solver_store_alloc( sat_solver * s )
{
    assert( s->pStore == NULL );
    s->pStore = Sto_ManAlloc();
}

void sat_solver_store_write( sat_solver * s, char * pFileName )
{
    if ( s->pStore ) Sto_ManDumpClauses( (Sto_Man_t *)s->pStore, pFileName );
}

void sat_solver_store_free( sat_solver * s )
{
    if ( s->pStore ) Sto_ManFree( (Sto_Man_t *)s->pStore );
    s->pStore = NULL;
}

int sat_solver_store_change_last( sat_solver * s )
{
    if ( s->pStore ) return Sto_ManChangeLastClause( (Sto_Man_t *)s->pStore );
    return -1;
}
 
void sat_solver_store_mark_roots( sat_solver * s )
{
    if ( s->pStore ) Sto_ManMarkRoots( (Sto_Man_t *)s->pStore );
}

void sat_solver_store_mark_clauses_a( sat_solver * s )
{
    if ( s->pStore ) Sto_ManMarkClausesA( (Sto_Man_t *)s->pStore );
}

void * sat_solver_store_release( sat_solver * s )
{
    void * pTemp;
    if ( s->pStore == NULL )
        return NULL;
    pTemp = s->pStore;
    s->pStore = NULL;
    return pTemp;
}


ABC_NAMESPACE_IMPL_END

